theory Blossom_Algo_working
  imports Graph_Quotient_working_2
begin        

subsection \<open>Misc\<close>
       
lemma set_tl:
  shows "set (tl l) \<subseteq> set l"
  by (induction l) auto

lemma construct_distinct_path:
  assumes
    disj_paths: "set p1 \<inter> set p2 = {}" and
    distinct: "distinct p1" "distinct p2"
  shows "distinct ((rev p1) @ p2)"
  using assms by simp

lemma numeral_4_eq_4:
  "4 = Suc (Suc (Suc (Suc 0)))"
  by auto

lemma Suc_le_length_iff_snoc2:
  "(Suc n \<le> length xs) = (\<exists>x ys. xs = ys @ [x] \<and> n \<le> length ys)"
proof
  assume "Suc n \<le> length xs"
  then have "Suc n \<le> length (rev xs)"
    by simp
  then have "(\<exists>x ys. rev xs = x # ys  \<and> n \<le> length ys)"
    using Suc_le_length_iff
    by metis
  then show "\<exists>x ys. xs = ys @ [x] \<and> n \<le> length ys"
    by auto
next
  assume "\<exists>x ys. xs = ys @ [x] \<and> n \<le> length ys"
  then have "\<exists>x ys. rev xs = x # ys \<and> n \<le> length ys"
    by force
  then have "Suc n \<le> length (rev xs)"
    using Suc_le_length_iff
    by metis
  then show  "Suc n \<le> length xs"
    by auto
qed

lemma set_butlast_tl:
  assumes "l \<noteq> []" "hd l = last l"
  shows "set (butlast l) = set (tl l)"
  using assms
  by (metis append_butlast_last_id butlast.simps(2) last_tl list.exhaust_sel rotate1.simps(2) set_rotate1)

fun dist_neq where
  "dist_neq _ [] = True"
| "dist_neq n (x # xs) \<longleftrightarrow>  (if length xs > n then (x \<noteq> hd (drop n xs)) \<and> dist_neq n xs else True)"

lemma dist_neq_path_eop: "dist_neq 0 (tl p) \<Longrightarrow> dist_neq 1 (tl p) \<Longrightarrow> dist_neq 1 (edges_of_path p)"
proof(induction  p rule: induct_list012)
  case (sucsuc x y zs)
  show ?case
  proof(cases zs)
    case cons1[simp]: (Cons z' zs')
    then show ?thesis
    proof(cases zs')
      case cons2[simp]: (Cons z'' zs'')
      moreover have "dist_neq 0 (tl zs)" "dist_neq 1 (tl zs)"
        using sucsuc
        by (cases zs; auto split: if_splits)+
      then have "dist_neq 1 (edges_of_path zs)"
        apply(intro sucsuc)
        by simp+
      ultimately show ?thesis
        using sucsuc(3,4)
        apply(cases zs'')
        by(simp add: cons1 doubleton_eq_iff)+
    qed simp
  qed simp
qed simp_all

lemma dist_neq_split: "dist_neq 1 (xs1 @ x # y # z # xs2) \<Longrightarrow> x \<noteq> z"
  by(induction xs1; auto)

lemma distinct_dist_neq: "distinct xs \<Longrightarrow> dist_neq n xs"
  by(induction xs; auto simp add: hd_drop_conv_nth)

lemma dist_neq_append: "dist_neq n (xs @ ys) \<Longrightarrow> dist_neq n xs"
  by(induction xs; auto)

lemma dist_neq_append2: "dist_neq n (xs @ ys) \<Longrightarrow> dist_neq n ys"
  apply(induction xs; simp)
  by (metis dist_neq.elims(3) length_Cons less_Suc_eq trans_less_add2)

lemma dist_neq_split_2: "(x \<noteq> z \<and> dist_neq 1 (xs1 @ [x, y]) \<and> dist_neq (Suc 0) (y # z # xs2))
                       \<Longrightarrow> dist_neq (Suc 0) (xs1 @ x # y # z # xs2)"
  apply(induction xs1)
   apply(auto simp add: hd_drop_conv_nth hd_append)
  subgoal for xs1 apply(cases xs1; simp)
    done
  done

lemma dist_neq_split_2': assumes "((last xs1 \<noteq> z) \<or> xs1 = [])" "dist_neq 1 (xs1 @ [y])" "dist_neq 1 (y # z # xs2)"
  shows "dist_neq 1 (xs1 @ y # z # xs2)"
proof(cases "xs1 =[]")
  case True
  then show ?thesis
    using assms
    by auto
next
  case False
  then have *: "xs1 = butlast xs1 @ [last xs1]"
    by simp
  have "last xs1 \<noteq> z"
    using assms(1) False
    by (simp add: append.assoc)
  moreover have "dist_neq 1 (butlast xs1 @ [last xs1, y])"
    using assms(2)
    apply(subst (asm) *)
    by (simp add: append.assoc)
  moreover have "dist_neq (Suc 0) (y # z # xs2)"
    using assms(3)
    by (simp add: append.assoc)
  ultimately show ?thesis
    apply (subst *)
    apply(simp add: append.assoc)
    apply(intro dist_neq_split_2 conjI)
    by simp+
qed

lemma Suc_le_length_iff_snoc: "(Suc n \<le> length xs) = (\<exists>x ys. xs = ys @ [x] \<and> n \<le> length ys)"
  using Suc_le_length_iff[of _ "rev xs", unfolded length_rev]
  by auto

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

subsection\<open>Contracting blossoms and lifting found augmenting paths\<close>

text\<open>We refine the algorithm \<open>aug_path_search\<close>. Here we only handle contracting \<open>match_blossoms\<close> and lifting
     abstract augmenting paths.\<close>

datatype 'a match_blossom_res =
   Path "'a list" 
| Blossom (stem_vs: "'a list") (cycle_vs: "'a list")

locale create_vert = 
  fixes create_vert::"'a set \<Rightarrow> 'a"
  assumes create_vert_works:
    "finite vs \<Longrightarrow> create_vert vs \<notin> vs" (*It has to be finite, otherwise that is a contradiction*)

text \<open>Here we cannot fix the graph nor the matching as they change as the algorithm executes.\<close>

locale find_aug_path = choose sel+
  create_vert create_vert 
  for sel::"'a set \<Rightarrow> 'a" and create_vert::"'a set \<Rightarrow> 'a" +
  fixes blos_search::"'a set set \<Rightarrow> 'a set set \<Rightarrow>  ('a match_blossom_res) option"
  assumes
    bloss_algo_complete: 
    "\<lbrakk>graph_invar G; matching M; M \<subseteq> G;
        (\<exists>p. graph_augmenting_path G M p)\<rbrakk>
     \<Longrightarrow> (\<exists>blos_comp. blos_search G M = Some blos_comp)" and
    bloss_algo_sound:
    "\<lbrakk>graph_invar G; matching M; M \<subseteq> G; blos_search G M = Some (Path p)\<rbrakk> \<Longrightarrow>
     graph_augmenting_path G M p"
    "\<lbrakk>graph_invar G; matching M; M \<subseteq> G; blos_search G M = Some (Blossom stem C)\<rbrakk> \<Longrightarrow>
     blossom G M stem C"
begin

lemma bloss_algo_sound_2:
    "\<lbrakk>graph_invar G; matching M; M \<subseteq> G; blos_search G M = Some (Blossom stem C)\<rbrakk> 
    \<Longrightarrow> (path G (stem @ C) \<and> (matching M \<longrightarrow> match_blossom M stem C))"
  using bloss_algo_sound(2)
  by auto


text\<open>A function to contract vertices\<close>

(*abbreviation "quot_fun s u v \<equiv> (if v \<notin> s then u else v)"*)

text\<open>This function is parameterised on another function that computes an augmenting path or a
     \<open>match_blossom\<close> if either one exists. It returns an optional \<open>match_blossom_comp\<close>, i.e. a \<open>match_blossom\<close> or an
     augmenting path or nothing.\<close>

(*context
  fixes s::"'a set" and u::'a
  assumes "u \<notin> s" "s \<subset> Vs G"
begin
interpretation quot: quot sel G s u
  using \<open>u \<notin> s\<close> \<open>s \<subset> Vs G\<close>
  apply(unfold_locales)
  .

end
*)

term quot.refine


function (domintros) find_aug_path where
  "find_aug_path G M = 
     (case blos_search G M of Some match_blossom_res \<Rightarrow>
        case match_blossom_res of Path p \<Rightarrow> Some p
        | Blossom stem cyc \<Rightarrow>
            let u = create_vert (Vs G);
                s = Vs G - (set cyc);
                quotG = quot.quotG s (create_vert (Vs G));
                refine = quot.refine sel G s (create_vert (Vs G)) cyc M
            in (case find_aug_path (quotG G) (quotG M) of Some p' \<Rightarrow> Some (refine p')
                | _ \<Rightarrow> None)
      | _ \<Rightarrow> None)"
  by pat_completeness auto

definition "find_aug_path_meas G = card (Vs G)"

(*lemma quot_sat:
  assumes "finite vs" "u = (create_vert vs)" "s \<subseteq> vs"
  shows "quot (quot_fun s u) s u"
  using assms
  unfolding quot_def
  using create_vert_works[OF assms(1)] assms by auto
*)

context 
  fixes s::"'a set" and E::"'a set set"
  assumes quot_assms: "s\<subset>Vs E" "graph_invar E"
begin
interpretation quot: quot sel E s "(create_vert (Vs E))"
  apply(unfold_locales)
  using quot_assms create_vert_works 
  by auto


lemma card_Vs_lt:
  assumes "1 < card (Vs E - s)"
  shows "find_aug_path_meas (quot.quotG E) < find_aug_path_meas E"
  unfolding find_aug_path_meas_def
  apply (rule quot.card_Vs_quotG)
  using quot_assms assms
  by auto

lemmas matching_quotM=quot.matching_quotM

lemmas doublton_quot = quot.doubleton_quot

lemmas aug_path_works_in_contraction = quot.aug_path_works_in_contraction

lemmas finite_quot = quot.finite_quot

lemmas doubleton_quot = quot.doubleton_quot

lemmas refine = quot.refine

end

lemma find_aug_path_dom_step:
  assumes "let u = (create_vert (Vs G));
               s = (Vs G - (set (cycle_vs (the (blos_search G M)))));
               quotG = quot.quotG s u
           in find_aug_path_dom (quotG G, quotG M)"
  shows "find_aug_path_dom (G, M)"
  using assms
  by (auto simp add: Let_def intro: find_aug_path.domintros)

lemma blossom_cycle_longer_2:
  assumes \<open>match_blossom M stem cyc\<close> 
  shows "card (set cyc) \<ge> 2"
proof-
  have "distinct (butlast cyc)"
    using match_blossomD(2)[OF \<open>match_blossom M stem cyc\<close>] distinct_append
    by blast
  then have "length (butlast cyc) = card (set (butlast cyc))"
    by (simp add: distinct_card)
  have "length (butlast cyc) = length cyc - 1"
    using length_butlast by blast
  then have "length (butlast cyc) \<ge> 2"
    using odd_cycleD(1)[OF match_blossomD(3)[OF \<open>match_blossom M stem cyc\<close>]] 
    by auto
  then have "card (set (butlast cyc)) \<ge> 2"
    using \<open>length (butlast cyc) = card (set (butlast cyc))\<close>
    by auto
  moreover have "set cyc = insert (last cyc) (set (butlast cyc))"
  proof-
    have "cyc = (butlast cyc) @ [last cyc]"
      by (metis \<open>length (butlast cyc) = card (set (butlast cyc))\<close> append_butlast_last_id butlast.simps(1) calculation le_zero_eq list.size(3) zero_neq_numeral)
    then show ?thesis
      by (metis list.simps(15) rotate1.simps(2) set_rotate1)
  qed
  ultimately show ?thesis
    using card_insert_le order.trans by fastforce
qed

lemma blossom_diff: 
assumes
  "graph_invar E" 
  "match_blossom M stem cyc"
  "path E (stem @ cyc)"
shows "((Vs E) - set cyc) \<subset> (Vs E)" (is "?s \<subset> _")
proof-  
  have "set cyc \<subseteq> Vs E"
    using path_suff subset_path_Vs assms
    by metis
  then have "Vs E - ?s = set cyc"
    by auto
  moreover have "?s \<subseteq> Vs E"
    by auto
  moreover have "card (set cyc) \<ge> 2"
    using blossom_cycle_longer_2[OF \<open>match_blossom M stem cyc\<close>] .
  moreover have "finite (Vs E)"
    by (simp add: assms)
  ultimately show ?thesis
    by auto
qed

lemma find_aug_path_dom:
  assumes "matching M" "M \<subseteq> E" "graph_invar E" 
  shows "find_aug_path_dom (E,M)"
  using assms
proof(induction "find_aug_path_meas E" arbitrary: E M rule: nat_less_induct)
  case 1
  show ?case
  proof(cases "(blos_search E M) = None")
    case T1: True
    then show ?thesis
      by (auto intro: find_aug_path.domintros)
  next
    case F1: False
    then obtain blos_comp where blos_comp: "(blos_search E M) = Some blos_comp"
      by auto
    show ?thesis
    proof(cases "\<exists>p. blos_comp = Path p")
      case T2: True
      then show ?thesis
        using find_aug_path.domintros blos_comp
        by (metis match_blossom_res.distinct(1) option.inject)
    next
      let ?u = "(create_vert (Vs E))"
      case F2: False
      then obtain stem cyc where stem_cyc: "blos_comp = Blossom stem cyc"
        using match_blossom_res.exhaust_sel by blast
      let ?s = "(Vs E - (set cyc))"
      have "match_blossom M stem cyc"
        "path E (stem @ cyc)"
        using bloss_algo_sound(2) blos_comp stem_cyc "1.prems"
        by auto
      then have "set cyc \<subseteq> Vs E"
        using path_suff subset_path_Vs
        by metis
      then have "Vs E - ?s = set cyc"
        by auto
      moreover have "?s \<subseteq> Vs E"
        by auto
      moreover have "card (set cyc) \<ge> 2"
        using blossom_cycle_longer_2[OF \<open>match_blossom M stem cyc\<close>] .
      moreover have "finite (Vs E)"
        by (simp add: "1.prems"(3))
      ultimately have "find_aug_path_meas (quot.quotG ?s ?u E) < find_aug_path_meas E"
        using 1              
        by (fastforce intro!: card_Vs_lt)

      moreover have "finite (quot.quotG ?s ?u E)"
        using "1.prems"
        by (metis (no_types, lifting) Diff_empty Vs_def Vs_quot_graph_finite finite_Diff_insert
                  finite_UnionD)
      moreover have "((Vs E) - set cyc) \<subset> (Vs E)"
        using blossom_diff[OF \<open>graph_invar E\<close> \<open>match_blossom M stem cyc\<close> \<open>path E (stem@cyc)\<close>].  
      hence "dblton_graph (quot.quotG ?s ?u E)"
        apply(intro doublton_quot[where E = E])
        using \<open>graph_invar E\<close> create_vert_works
        by auto


      ultimately have dom_quot: "find_aug_path_dom (quot.quotG ?s ?u E, M')" 
        if "matching M'" "M' \<subseteq> quot.quotG ?s ?u E" for M'
        using 1 that
        by (simp add: finite_dbl_finite_verts)
      moreover have "matching (quot.quotG ?s ?u M)"
        apply (intro matching_quotM[where s = ?s and stem = stem and C=cyc and E=E])
        subgoal using \<open>((Vs E) - set cyc) \<subset> (Vs E)\<close> .
        subgoal using \<open>graph_invar E\<close> .
        subgoal using \<open>match_blossom M stem cyc\<close> .
        subgoal using 1(2) .
        subgoal using "1.prems"(2) by blast
        subgoal ..
        done
      moreover have "(quot.quotG ?s ?u M) \<subseteq> quot.quotG ?s ?u E"
        by (simp add: "1.prems"(2) Diff_mono graph_subset_quot_subset)
      ultimately show ?thesis
        using blos_comp stem_cyc 1(2)
        by (fastforce intro!: find_aug_path_dom_step)
    qed
  qed
qed

lemma find_aug_path_complete:
  assumes aug_path: "graph_augmenting_path G M p" and
    matching: "matching M" "M \<subseteq> G" and
    graph: "graph_invar G"
  shows "\<exists>p'. find_aug_path G M = Some p'"
proof-
  have "find_aug_path_dom (G,M)"
    using find_aug_path_dom[OF matching(1,2) \<open>graph_invar G\<close>]
    by simp
  then show ?thesis
    using assms
  proof (induction arbitrary: p rule: find_aug_path.pinduct)
    case (1 G M)
    show ?case
    proof(cases "(blos_search G M) = None")
      case T1: True
      then show ?thesis
        using 1 bloss_algo_complete
        by (metis (no_types, lifting) option.distinct(1))
    next
      case F1: False
      then obtain blos_comp where blos_comp: "(blos_search G M) = Some blos_comp"
        by auto
      show ?thesis
      proof(cases "\<exists>p. blos_comp = Path p")
        case T2: True
        then show ?thesis
          apply(simp add: find_aug_path.psimps[OF 1(1)])
          using blos_comp bloss_algo_sound
          by force
      next
        let ?u = "(create_vert (Vs G))"
        case F2: False
        then obtain stem cyc where stem_cyc: "blos_comp = Blossom stem cyc"
          using match_blossom_res.exhaust_sel by blast
        define s where "s = (Vs G - (set cyc))"
        have blos: "blossom G M stem cyc"
          using bloss_algo_sound(2) blos_comp stem_cyc 1
          by metis
        then have "set cyc \<subseteq> Vs G"
          using path_suff subset_path_Vs
          by metis
        then have "Vs G - s = set cyc"
          unfolding s_def
          by auto
        have "((Vs G) - set cyc) \<subset> (Vs G)"
          using blossom_diff[OF \<open>graph_invar G\<close> blossomD(2,1)[OF blos]] .
        moreover have "graph_invar G"
          using \<open>graph_invar G\<close> .
        moreover have "?u \<notin> Vs G"
          using create_vert_works \<open>graph_invar G\<close>
          by simp
        moreover have "finite M"
         using graph_invar_finite_Vs[OF \<open>graph_invar G\<close>] graph_invar_dblton[OF\<open>graph_invar G\<close>] \<open>M \<subseteq> G\<close>
          by (simp add: dblton_graph_finite_Vs finite_subset)
        ultimately obtain p' where p': "graph_augmenting_path (quot.quotG s ?u G) (quot.quotG s ?u M) p'"
          using aug_path_works_in_contraction[OF _ _ blos \<open>graph_augmenting_path G M p\<close> \<open>matching M\<close>] 
          using "1.prems"(3) s_def
          by auto
        have "finite (quot.quotG s ?u M)"
          using finite_quot[OF \<open>((Vs G) - set cyc) \<subset> (Vs G)\<close> \<open>graph_invar G\<close> \<open>finite M\<close>]
          by (auto simp add: s_def)
        moreover have "dblton_graph (quot.quotG s ?u G)"
          using doubleton_quot[OF \<open>((Vs G) - set cyc) \<subset> (Vs G)\<close> \<open>graph_invar G\<close>]
          by (auto simp: s_def)
        moreover have "finite (quot.quotG s ?u G)"
          using quot_graph_finite'[OF graph_invar_finite_Vs[OF \<open>graph_invar G\<close>]]
          by auto
        moreover have "(quot.quotG s ?u M) \<subseteq> (quot.quotG s ?u G)"
          using graph_subset_quot_subset[OF \<open>M \<subseteq> G\<close>]
          by auto
        moreover have "matching (quot.quotG s ?u M)"
          using matching_quotM[OF \<open>((Vs G) - set cyc) \<subset> (Vs G)\<close> \<open>graph_invar G\<close> blossomD(2)[OF blos]] 
                1 s_def
          by blast
        ultimately obtain p'' where "find_aug_path (quot.quotG s ?u G) (quot.quotG s ?u M) = Some p''"
          using s_def 1(2)[OF blos_comp stem_cyc _ _ _ _ p'] dblton_graph_finite_Vs
          by fastforce
        then show ?thesis
          apply(intro exI[where x="quot.refine sel G s ?u cyc M p''"])
          by(force simp add: s_def blos_comp stem_cyc find_aug_path.psimps[OF 1(1)] Let_def split: option.splits)
      qed
    qed
  qed
qed

end

lemma match_blossom_distinct_tl:
  assumes "match_blossom M stem cyc"
  shows "distinct (tl cyc)"
proof-
  have "distinct (butlast cyc)" "hd cyc = last cyc"
    using match_blossomD[OF assms] odd_cycleD
    unfolding distinct_append[symmetric] 
    by auto
  then have "distinct (tl (butlast cyc))" "hd cyc \<notin> set (tl (butlast cyc))"
    using distinct_tl
    by (metis \<open>distinct (butlast cyc)\<close> append_butlast_last_id assms distinct.simps(2) empty_iff hd_append2 list.collapse list.sel(2) list.set(1) match_blossomD(3) odd_cycle_nempty)+
  then have "distinct ((tl (butlast cyc)) @ [last cyc])"
    using \<open>hd cyc = last cyc\<close>
    by auto
  moreover have "(tl (butlast cyc)) @ [last cyc] = tl cyc" if "length cyc \<ge> 3" for cyc::"'a list"
    using that
  proof(induction cyc)
    case Nil
    then show ?case by auto
  next
    case (Cons a' cyc')
    then show ?case 
      by auto
  qed
  moreover have "length cyc \<ge> 3"
    using odd_cycleD(1)[OF match_blossomD(3)[OF assms]]
    by auto
  ultimately show ?thesis
    by auto
qed

lemma cycle_set_tl_eq_butlast:
  assumes "match_blossom M stem cyc"
  shows "set (tl cyc) = set (butlast cyc)"
  by (metis append_butlast_last_id assms match_blossomD(3) butlast.simps(2) last_tl list.exhaust_sel odd_cycleD(3) odd_cycle_nempty rotate1.simps(2) set_rotate1)

context find_aug_path
begin

lemma find_aug_path_sound:
  assumes matching: "matching M" "M \<subseteq> G" "finite M" and
    graph: "graph_invar G" and
    find_aug_path: "find_aug_path G M = Some p"
  shows "graph_augmenting_path G M p"
proof-
  have "find_aug_path_dom (G,M)"
    using find_aug_path_dom[OF matching(1,2) graph]
    by simp
  then show ?thesis
    using assms
  proof (induction arbitrary: p rule: find_aug_path.pinduct)
    case (1 G M)
    show ?case
    proof(cases "(blos_search G M) = None")
      case T1: True
      then show ?thesis
        using 1(1,7) 
        by(simp add: find_aug_path.psimps)
    next
      case F1: False
      then obtain blos_comp where blos_comp: "(blos_search G M) = Some blos_comp"
        by auto
      show ?thesis
      proof(cases "\<exists>p. blos_comp = Path p")
        case T2: True
        then show ?thesis
          using 1(1,7)
          apply(simp add: find_aug_path.psimps)
          using blos_comp bloss_algo_sound 1
          by auto
      next
        let ?u = "(create_vert (Vs G))"
        case F2: False
        then obtain stem cyc where stem_cyc: "blos_comp = Blossom stem cyc"
          using match_blossom_res.exhaust_sel by blast
        let ?s = "(Vs G - (set cyc))"
        have blos: "path G (stem @ cyc)" "match_blossom M stem cyc"
          using bloss_algo_sound(2) blos_comp stem_cyc 1
          by auto
        (*then have "set cyc \<subseteq> Vs G"
          using path_suff subset_path_Vs
          by metis
        then have "Vs G - s = set cyc"
          unfolding s_def
          by auto
        have s_subset_VsG: "s \<subseteq> Vs G"
          unfolding s_def
          by auto
        moreover have "finite (Vs G)"
          using dblton_graph_finite_Vs \<open>graph_invar G\<close>
          by auto
        ultimately have "quot s u"
          using 1 u_def quotF_def
          by simp*)
        have "?s \<subset> (Vs G)"
          using blossom_diff[OF \<open>graph_invar G\<close> blos(2,1)] .
        moreover have "graph_invar G"
          using \<open>graph_invar G\<close> .
        moreover have "?u \<notin> Vs G"
          using create_vert_works \<open>graph_invar G\<close>
          by simp
       moreover have "finite M"
         using graph_invar_finite_Vs[OF \<open>graph_invar G\<close>] graph_invar_dblton[OF\<open>graph_invar G\<close>] \<open>M \<subseteq> G\<close>
          by (simp add: dblton_graph_finite_Vs finite_subset)

        ultimately have "finite (quot.quotG ?s ?u M)"
          apply(intro finite_quot)
          by auto

        moreover have "dblton_graph (quot.quotG ?s ?u G)"
          using doubleton_quot[OF \<open>?s \<subset> Vs G\<close>] 1
          by simp
        moreover have "finite (quot.quotG ?s ?u G)"
          using "1.prems"(4) quot_graph_finite'
          by auto
        moreover have "(quot.quotG ?s ?u M) \<subseteq> (quot.quotG ?s ?u G)"
          by (simp add: "1.prems"(2) Diff_mono graph_subset_quot_subset)
        moreover have "matching (quot.quotG ?s ?u M)"
          using matching_quotM[OF \<open>?s \<subset> Vs G\<close> \<open>graph_invar G\<close> blos(2)] 1
          by blast
        moreover obtain p' where p': "find_aug_path (quot.quotG ?s ?u G) (quot.quotG ?s ?u M) = Some p'"
          using 1(7)
          by (simp add: blos_comp stem_cyc find_aug_path.psimps[OF 1(1)] Let_def split: option.splits)
        ultimately have "matching_augmenting_path (quot.quotG ?s ?u M) p' \<and>
                         path (quot.quotG ?s ?u G) p' \<and> distinct p'"
          using 1(2)[OF blos_comp stem_cyc _ _ _ _]
          by (meson dblton_graph_finite_Vs)
        then have "matching_augmenting_path M (quot.refine sel G ?s ?u cyc M p') \<and>
                   path G (quot.refine sel G ?s ?u cyc M p') \<and>
                   distinct (quot.refine sel G ?s ?u cyc M p')"
          using refine[OF \<open>?s \<subset> Vs G\<close>] match_blossomD[OF blos(2)]
            match_blossom_alt_cycle[OF blos(2)] match_blossom_distinct_tl[OF blos(2)]
            path_suff[OF blos(1)] 1
          by(auto simp add: )
        then show ?thesis
          using 1(7) p'
          by(simp add: blos_comp stem_cyc find_aug_path.psimps[OF 1(1)] Let_def split: option.splits)
      qed
    qed
  qed
qed

end

text\<open>the function terminates on a finite graph\<close>

locale find_aug_path_use = find_aug_path sel +
  graph_abs E for sel::"'a set \<Rightarrow> 'a" and E::"'a set set"
begin

interpretation find_max_match_intrp: find_max_match E find_aug_path
  apply unfold_locales
  subgoal using find_aug_path_complete[OF _ _ _ graph] by force
  subgoal using find_aug_path_sound[OF _ _ _ graph] by force
  done
(*
lemma find_max_match_sat:
  assumes "graph_invar G"
  shows "find_max_match G find_aug_path"
  unfolding find_max_match_def
  using find_aug_path_sound[OF _ _ _ assms] find_aug_path_complete[OF _ _ _ assms]
    finite_dbl_finite_verts[]
  by auto

*)
text\<open>The function can be plugged in the main function from above.\<close>

(*TODO: there must be a better way to use conclusions from the interpretation
        other than renaming everyithng*) 

abbreviation "find_max_matching \<equiv> find_max_match_intrp.find_max_matching"

lemmas find_max_matching_works = find_max_match_intrp.find_max_matching_works
(*lemma find_max_matching_2_works:
  shows "find_max_matching {} \<subseteq> G"
    "matching (find_max_matching {})"
    "finite (find_max_matching {})"
    "\<forall>M. matching M \<and> M \<subseteq> G \<and> finite M \<longrightarrow> card M \<le> card (find_max_matching {})"
  using find_max_matching_works
  by auto*)


end

lemma creat_vert_fun:
  "\<And>vs::nat set. finite vs \<Longrightarrow> (\<lambda>vs. Max vs +1) vs \<notin> vs"
  using Max_ge Suc_le_eq by auto

text\<open>This is a naive function to ascend the given blossom. It takes time quadratic in the size of
     the blossom.\<close>

fun longest_disj_pfx where
  "longest_disj_pfx l1 [] = (None,None)"
| "longest_disj_pfx [] l2 = (None,None)"
| "longest_disj_pfx l1 (h#l2) = 
    (let l1_pfx = (find_pfx ((=) h) l1) in
       if (last l1_pfx = h) then
         (Some l1_pfx,Some [h])
       else (let (l1_pfx,l2_pfx) = (longest_disj_pfx l1 l2) in
               case l2_pfx of Some pfx2 \<Rightarrow> (l1_pfx,Some (h#pfx2))
                            | _ \<Rightarrow> (l1_pfx, l2_pfx)))"

text\<open>This is a function to do the same task in linear time in the blossom.\<close>

fun longest_disj_pfx_lin where
  "longest_disj_pfx_lin l1 [] = (None, None)"
| "longest_disj_pfx_lin [] l2 = (None, None)"
| "longest_disj_pfx_lin (x#xs) (y#ys) =
    (if x = y then
       (Some [x], Some [x])
     else
       (let (l1_pfx,l2_pfx) = (longest_disj_pfx_lin xs ys)
        in
          case l1_pfx of Some pfx1 \<Rightarrow>
            (case l2_pfx of Some pfx2 \<Rightarrow> 
              (Some (x#pfx1), Some (y#ys)))
          | _ \<Rightarrow> (None, None)))"

lemma no_first_pfx_then_no_snd_pfx:
  "(None,l2_pfx) = (longest_disj_pfx l1 l2) \<Longrightarrow> \<exists>pfx2. l2_pfx = None"
proof(induction l2 arbitrary: l1 l2_pfx)
  case Nil
  then show ?case by auto
next
  case cons1: (Cons a2 l2)
  show ?case
  proof(cases l1)
    case Nil
    then show ?thesis
      using cons1
      by (auto simp add: Let_def)
  next
    case (Cons a1' l1')
    then show ?thesis
      using cons1
      apply (auto simp add: Let_def split: if_splits prod.splits option.splits)
      by (metis option.simps(3))+
  qed
qed

lemma first_pfx_then_snd_pfx:
  "(Some pfx1,l2_pfx) = (longest_disj_pfx l1 l2) \<Longrightarrow> \<exists>pfx2. l2_pfx = Some pfx2"
proof(induction l2 arbitrary: l1 pfx1 l2_pfx)
  case Nil
  then show ?case by auto
next
  case cons1: (Cons a2 l2)
  show ?case
  proof(cases l1)
    case Nil
    then show ?thesis
      using cons1
      by (auto simp add: Let_def)
  next
    case (Cons a1' l1')
    then show ?thesis
      using cons1
      apply (auto simp add: Let_def split: if_splits prod.splits option.splits)
      by (metis option.simps(3))+
  qed
qed

lemma first_pfx_nempty:
  "(Some pfx1,l2_pfx) = (longest_disj_pfx l1 l2) \<Longrightarrow> pfx1 \<noteq> []"
proof(induction l2 arbitrary: l1 pfx1 l2_pfx)
  case Nil
  then show ?case by auto
next
  case cons1: (Cons a2 l2)
  show ?case
  proof(cases l1)
    case Nil
    then show ?thesis
      using cons1
      by (auto simp add: Let_def)
  next
    case (Cons a1' l1')
    then show ?thesis
      using cons1
      apply (auto simp add: Let_def split: if_splits prod.splits option.splits)
      by metis+
  qed
qed

lemma snd_pfx_nempty:
  "(l1_pfx, Some pfx2) = (longest_disj_pfx l1 l2) \<Longrightarrow> pfx2 \<noteq> []"
proof(induction l2 arbitrary: l1 l1_pfx pfx2)
  case Nil
  then show ?case by auto
next
  case cons1: (Cons a2 l2)
  show ?case
  proof(cases l1)
    case Nil
    then show ?thesis
      using cons1
      by (auto simp add: Let_def)
  next
    case (Cons a1' l1')
    then show ?thesis
      using cons1
      by (auto simp add: Let_def split: if_splits prod.splits option.splits)
  qed
qed

lemma pfx_common_end:
  "(Some pfx1, l2_pfx) = (longest_disj_pfx l1 l2) \<Longrightarrow> last pfx1 = last (the l2_pfx)"
proof(induction l2 arbitrary: l1 pfx1 l2_pfx)
  case Nil
  then show ?case by auto
next
  case cons1: (Cons a2 l2)
  show ?case
  proof(cases l1)
    case Nil
    then show ?thesis
      using cons1
      by (auto simp add: Let_def)
  next
    case (Cons a1' l1')
    then show ?thesis
      using cons1 
      apply (clarsimp simp add: Let_def split: if_splits prod.splits option.splits)
      subgoal by metis
      subgoal by (metis option.sel snd_pfx_nempty)
      subgoal by (metis option.sel)
      subgoal by (metis option.sel snd_pfx_nempty)
      done
  qed
qed

lemma find_pfx_nempty: "l \<noteq> [] \<Longrightarrow> find_pfx Q l \<noteq> []"
  by(induction l; auto)

lemma find_pfx_empty: "find_pfx Q l = [] \<Longrightarrow> l = []"
  using find_pfx_nempty by auto

lemma disj_pref_append1:
  assumes "(Some pfx1, l2_pfx) = (longest_disj_pfx l1 l2)"
  shows "\<exists>l1'. l1 = pfx1@l1'"
  using assms
proof(induction l2 arbitrary: l1 pfx1 l2_pfx)
  case Nil
  then show ?case by auto
next
  case cons1: (Cons a2 l2)
  show ?case
  proof(cases l1)
    case Nil
    then show ?thesis
      using cons1
      by (auto simp add: Let_def)
  next
    case (Cons a1' l1')
    then show ?thesis
      using cons1
      by (auto simp add: find_pfx_append_2 Let_def split: if_splits prod.splits option.splits)
  qed
qed

lemma disj_pref_append2:
  assumes "(l1_pfx, Some pfx2) = (longest_disj_pfx l1 l2)"
  shows "\<exists>l2'. l2 = pfx2@l2'"
  using assms
proof(induction l2 arbitrary: l1 pfx2 l1_pfx)
  case Nil
  then show ?case by auto
next
  case cons1: (Cons a2 l2)
  show ?case
  proof(cases l1)
    case Nil
    then show ?thesis
      using cons1
      by (auto simp add: Let_def)
  next
    case (Cons a1' l1')
    then show ?thesis
      using cons1
      apply (auto simp add: Let_def split: if_splits prod.splits option.splits)
      by metis+
  qed
qed

lemma disj_pfx_are_disj_1:
  assumes "(Some pfx1, l2_pfx) = (longest_disj_pfx l1 l2)"
  shows "set pfx1 \<inter> set (butlast (the l2_pfx)) = {}"
  using assms
proof(induction l2 arbitrary: l1 pfx1 l2_pfx)
  case Nil
  then show ?case by auto
next
  case cons1: (Cons a2 l2)
  show ?case
  proof(cases l1)
    case Nil
    then show ?thesis
      using cons1
      by (auto simp add: Let_def)
  next
    case (Cons a1' l1')
    then show ?thesis
      using cons1(1,2)
      apply (clarsimp simp add: Let_def split: if_splits prod.splits option.splits)
      subgoal using cons1.prems by fastforce
      subgoal by (metis append_eq_Cons_conv append_is_Nil_conv disj_pref_append1 empty_iff empty_set find_pfx_empty option.sel set_ConsD)
      subgoal by metis
      subgoal by (metis (mono_tags, opaque_lifting) Un_iff disj_pref_append1 find_pfx_works_1 option.sel set_ConsD set_append) 
      done
  qed
qed

lemma find_pfx_butlast_2:
  assumes "x \<in> set (butlast (find_pfx Q l))"
  shows "\<not>Q x"
  using assms
proof(induction l)
  case Nil
  then show ?case
    by auto
next
  case (Cons a' l')
  show ?case
  proof(cases "x = a'")
    case True
    then show ?thesis
      using Cons
      by auto
  next
    case False
    then show ?thesis
      using Cons
      by (auto split: if_splits)
  qed
qed

lemma disj_pfx_are_disj_2:
  assumes "(Some pfx1, Some pfx2) = (longest_disj_pfx l1 l2)"
  shows "set (butlast pfx1) \<inter> set pfx2 = {}"
  using assms
proof(induction l2 arbitrary: l1 pfx1 pfx2)
  case Nil
  then show ?case by auto
next
  case cons1: (Cons a2 l2)
  show ?case
  proof(cases l1)
    case Nil
    then show ?thesis
      using cons1
      by (auto simp add: Let_def)
  next
    case (Cons a1' l1')
    then show ?thesis
      using cons1(1,2)
      apply (clarsimp simp add: Let_def split: if_splits prod.splits option.splits)
      subgoal using find_pfx_butlast_2 by fastforce
      subgoal by (metis butlast.simps(2) disj_pref_append1 empty_iff empty_set find_pfx_empty in_set_butlast_appendI)
      subgoal by (metis butlast.simps(2) cons1.prems disj_pfx_are_disj_1 disjoint_iff_not_equal in_set_butlastD list.set_intros(1) option.sel snd_pfx_nempty)
      done
  qed
qed

lemma disj_pfx_are_disj_3:
  assumes "(Some pfx1, l2_pfx) = (longest_disj_pfx l1 l2)"
  shows "set (butlast pfx1) \<inter> set (butlast (the l2_pfx)) = {}"
  using assms disj_pfx_are_disj_1
  by (metis IntI Int_emptyI empty_iff in_set_butlastD)

lemma disj_pfx_is_complete:
  assumes "(None, l2_pfx) = (longest_disj_pfx l1 l2)"
  shows "set l1 \<inter> set l2 = {}"
  using assms
proof(induction l2 arbitrary: l1 l2_pfx)
  case Nil
  then show ?case by auto
next
  case cons1: (Cons a2 l2)
  show ?case
  proof(cases l1)
    case Nil
    then show ?thesis
      using cons1
      by (auto simp add: Let_def)
  next
    case (Cons a1' l1')
    then show ?thesis
      using cons1(1,2)
      apply (clarsimp simp add: Let_def split: if_splits prod.splits option.splits)
      subgoal by (metis IntI Int_commute Int_empty_right distinct.simps(2) distinct_singleton empty_set find_pfx_empty list.set_intros(1))
      subgoal by (metis IntI empty_iff empty_set find_pfx_empty inf_right_idem list.set_intros(1))
      subgoal by (metis (full_types) find_pfx_works_1 insert_disjoint(1) list.simps(15))
      subgoal by (metis (full_types) find_pfx_works_1 insert_disjoint(2) list.simps(15))
      done
  qed
qed

lemma back_subst_2: "(Q a b \<Longrightarrow> P a b) \<Longrightarrow> Q c d \<Longrightarrow> a = c \<Longrightarrow> b = d \<Longrightarrow> P c d"
  by simp

lemma pfxs_alt_path':
  assumes
    pfxs_are_pfxs: "(Some pfx1, Some pfx2) = longest_disj_pfx p1 p2" and
    alt_paths: "alt_path M (hd p2 # p1)" "alt_path M (hd p1 # p2)"
    "last p1 \<notin> Vs M" and
    odd_lens: "odd (length p1)" "odd (length p2)"
  shows "alt_path M (rev (drop (length pfx1) p1) @ rev pfx1 @ pfx2)"
proof-
  have "(rev (drop (length pfx1) p1)) @ rev pfx1 = rev p1"
    using assms(1) disj_pref_append1 by fastforce
  moreover have "alt_path M ((rev p1) @ pfx2)"
  proof(cases pfx2)
    case Nil
    then show ?thesis
      using snd_pfx_nempty pfxs_are_pfxs
      by auto
  next
    have "p1 \<noteq> []"
      using disj_pref_append1 first_pfx_nempty pfxs_are_pfxs by fastforce
    then have eqop_append: "edges_of_path (rev p1 @ pfx2) = edges_of_path (rev p1) @ edges_of_path (hd p1 # pfx2)"
      using edges_of_path_append_2 edges_of_path_rev
      by (metis (no_types, lifting) rev.simps(2) rev_append rev_rev_ident)
    case (Cons a' pfx2')
    then have "hd (edges_of_path p1) \<in> M" if "edges_of_path (rev p1) \<noteq> []"
      using alt_paths(1) that[unfolded edges_of_path_rev[symmetric]] \<open>p1 \<noteq> []\<close>
      by(auto simp add: neq_Nil_conv alt_list_step)
    then have "last (edges_of_path (rev p1)) \<in> M" if "edges_of_path (rev p1) \<noteq> []"
      using that Cons
      by(simp add: edges_of_path_rev[symmetric] last_rev)
    moreover have "alt_path M (rev p1)" if "edges_of_path (rev p1) \<noteq> []"
      apply(intro odd_alt_path_rev)
      subgoal using odd_lens(1) .
      subgoal using that
        by (simp add: edges_of_path_nempty)
      subgoal using alt_paths
        by(intro alt_path_cons_odd[where p = p1 and v = "hd p2"] odd_lens(1); simp)+
      done
    moreover have "alt_path M ((hd p1)#pfx2)"
    proof -
      obtain p2' where "p2 = pfx2 @ p2'"
        using disj_pref_append2[OF pfxs_are_pfxs]
        by rule
      have *:"butlast (hd p1 # pfx2) @ [last (hd p1 # pfx2)] = (hd p1 # pfx2)"
        by simp
      have **:"b # l1 @ a # l2 = b # (l1 @ [a]) @ l2" for l1 l2 a b
        by simp
      have "edges_of_path ((hd p1 # pfx2) @ p2') = edges_of_path (hd p1 # pfx2) @ edges_of_path (last (hd p1 # pfx2) # p2')" (is "?a = ?b")
        using edges_of_path_append_2[where ?p = "butlast (hd p1 # pfx2)" and ?p' = "last (hd p1 # pfx2) # p2'", unfolded *]
        apply (simp add: Cons split: if_splits)
        by (simp add: "**")
      then show ?thesis
        apply(subst conjunct1[OF alt_list_append_1[where ?l2.0 = "edges_of_path (last (hd p1 # pfx2) # p2')"]])
        using alt_paths(2)
        by (simp add: \<open>p2 = pfx2 @ p2'\<close>)+
    qed
    ultimately show ?thesis
      using alternating_list_odd_last odd_pos
      by (fastforce simp: eqop_append alt_list_empty intro!: alt_list_append_3)+
  qed
  ultimately show ?thesis
    by (metis append.assoc)
qed

lemma pfxs_path:
  assumes
    pfxs_are_pfxs: "(Some pfx1, Some pfx2) = longest_disj_pfx p1 p2" and
    paths: "path G p1" "path G p2"
    "{hd p1, hd p2} \<in> G"
  shows "path G (rev (drop (length pfx1) p1) @ rev pfx1 @ pfx2)"
proof-
  have "(rev (drop (length pfx1) p1)) @ rev pfx1 = rev p1"
    using assms(1) disj_pref_append1 by fastforce
  moreover have "path G ((rev p1) @ pfx2)"
  proof(cases pfx2)
    case Nil
    then show ?thesis
      using snd_pfx_nempty pfxs_are_pfxs
      by auto
  next
    case (Cons a' pfx2')
    have "p1 \<noteq> []"
      using disj_pref_append1 first_pfx_nempty pfxs_are_pfxs by fastforce
    moreover have "path G (rev p1)"
      by (simp add: paths(1) rev_path_is_path)
    moreover have "hd pfx2 = hd p2"
      using Cons disj_pref_append2
        pfxs_are_pfxs
      by fastforce
    moreover have "path G pfx2"
      using disj_pref_append2[OF pfxs_are_pfxs] path_pref paths(2)
      by auto
    ultimately show ?thesis
      apply(intro path_append)
      using paths(3)
      by (simp add: last_rev edges_of_path_rev[symmetric])+
  qed
  ultimately show ?thesis
    by (metis append.assoc)
qed

lemma pfxs_distinct:
  assumes
    pfxs_are_pfxs: "(Some pfx1, Some pfx2) = longest_disj_pfx p1 p2" and
    distinct: "distinct p1" "distinct p2"
    "p1 = pfx1 @ p'" "p2 = pfx2 @ p'"
  shows "distinct (rev (drop (length pfx1) p1) @ butlast (rev pfx1 @ pfx2))"
proof-
  have "(rev (drop (length pfx1) p1)) @ rev pfx1 = rev p1"
    using assms(1) disj_pref_append1 by fastforce
  moreover have "butlast (rev pfx1 @ pfx2) = (rev pfx1 @ (butlast pfx2))"
    using assms
    by (metis butlast_append snd_pfx_nempty)
  moreover have "distinct ((rev p1) @ (butlast pfx2))"
    apply(simp add: )
    by (smt Un_iff append_butlast_last_id butlast.simps(1) disj_pfx_are_disj_1 disjoint_iff_not_equal distinct(1) distinct(2) distinct(3) distinct(4) distinct_append option.sel pfxs_are_pfxs set_append)
  ultimately show ?thesis
    by (metis append.assoc)
qed

lemma pfxs_odd_cycle':
  assumes pfxs_are_pfxs: "(Some pfx1, Some pfx2) = longest_disj_pfx p1 p2" and
    from_tree: "p1 = pfx1 @ p" "p2 = pfx2 @ p" and
    alt_paths: "alt_path (-M) p1" "alt_path (-M) p2"
    "{hd p1, hd p2} \<notin> M" and 
    hds_neq: "hd p1 \<noteq> hd p2" and
    even_lens: "odd (length p1)" "odd (length p2)"
  shows "odd_cycle (rev pfx1 @ pfx2)"
proof-
  have "length (rev pfx1 @ pfx2) \<ge> 3"
  proof(rule ccontr)
    assume "\<not> 3 \<le> length (rev pfx1 @ pfx2)"
    moreover have "rev pfx1 \<noteq> []"
      using first_pfx_nempty pfxs_are_pfxs by auto
    moreover have "pfx2 \<noteq> []"
      using snd_pfx_nempty pfxs_are_pfxs by auto
    ultimately have "length (rev pfx1 @ pfx2) = 2"
      apply(cases pfx1; cases pfx2; simp)
      using le_simps(3) by blast+
    then obtain a1 a2 where a1a2: "pfx2 = [a2]" "pfx1 = [a1]"
      using \<open>rev pfx1 \<noteq> []\<close> \<open>pfx2 \<noteq> []\<close>
      by (cases pfx1; cases pfx2; auto)
    then have "a1 = a2"
      using pfx_common_end pfxs_are_pfxs by fastforce
    moreover have "a1 = hd p1"
      using a1a2
      using disj_pref_append1 pfxs_are_pfxs by fastforce
    moreover have "a2 = hd p2"
      using a1a2
      using disj_pref_append2 pfxs_are_pfxs by fastforce
    ultimately show False
      using hds_neq
      by auto
  qed
  moreover have "hd ((rev pfx1) @ pfx2) = last ((rev pfx1) @ pfx2)"
  proof-
    have "rev pfx1 \<noteq> []"
      using first_pfx_nempty pfxs_are_pfxs by auto
    moreover have "pfx2 \<noteq> []"
      using snd_pfx_nempty pfxs_are_pfxs by auto
    moreover have "hd (rev pfx1) = last pfx2" 
      using hd_rev pfx_common_end pfxs_are_pfxs
      by (metis option.sel)
    ultimately show ?thesis
      by auto
  qed
  moreover have "odd (length (edges_of_path ((rev pfx1) @ pfx2)))"
  proof(cases "odd (length pfx1) \<and> odd (length pfx2)")
    case T1: True
    then have "odd (length (rev pfx1))"
      by simp
    then have "even (length ((rev pfx1) @ pfx2))"
      using T1
      by simp
    then show ?thesis
      by (metis Nil_is_append_conv T1 edges_of_path_length' even_add odd_one)
  next
    case F1: False
    moreover{
      assume ass: "even (length pfx1)" "odd (length pfx2)"
      then have False
        using alt_paths(2) from_tree(2)
          even_lens from_tree(1)
        by auto
    }
    moreover{
      assume ass: "odd (length pfx1)" "even (length pfx2)"
      then have False
        using alt_paths(2) from_tree(2)
          even_lens from_tree(1)
        by auto
    }
    ultimately show ?thesis
      by (metis Nil_is_append_conv edges_of_path_length' even_add from_tree(1) from_tree(2) hds_neq
                length_append length_rev odd_one rev_is_Nil_conv)
  qed
  ultimately show ?thesis
    unfolding odd_cycle_def
    by simp
qed

lemma pfxs_even_stem':
  assumes pfxs_are_pfxs: "(Some pfx1, Some pfx2) = longest_disj_pfx p1 p2" and
    from_tree: "p1 = pfx1 @ p" "p2 = pfx2 @ p" and
    alt_paths: "alt_path M (hd p2 # p1)" "alt_path M (hd p1 # p2)"
    "last p1 \<notin> Vs M" and 
    hds_neq: "hd p1 \<noteq> hd p2" and
    odd_lens: "odd (length p1)" "odd (length p2)" and
    distinct: "distinct p1" "distinct p2" and
    matching: "matching M"
  shows "even (length (edges_of_path (rev (drop (length pfx1) p1) @ [hd (rev pfx1 @ pfx2)])))"
proof-
  have "hd (rev pfx1 @ pfx2) = hd (rev pfx1)"
    using first_pfx_nempty hd_append2 pfxs_are_pfxs by blast
  moreover have "(drop (length pfx1) p1) = p"
    by (simp add: from_tree(1))
  have pfx1_nempty: "pfx1 \<noteq> []"
    using pfxs_are_pfxs first_pfx_nempty snd_pfx_nempty
    by auto
  have pfx2_nempty: "pfx2 \<noteq> []"
    using pfxs_are_pfxs snd_pfx_nempty
    by auto

  have last_pfx1_eq: "last pfx1 = last pfx2"
    using pfx_common_end pfxs_are_pfxs by fastforce

  have last_pfxs_neq: "last (butlast pfx2) \<noteq> last (butlast pfx1)"
                      if "length pfx1 \<ge> 2" "length pfx2 \<ge> 2" "set (butlast pfx1) \<inter> set pfx2 = {}"
                      for pfx1 pfx2
    using that
    by (metis Suc_1 diff_is_0_eq disjoint_iff in_set_butlastD last_in_set length_butlast list.size(3)
              not_less_eq_eq)

  {
    fix p1 pfx1 p2 pfx2::"'a list"
    assume "p \<noteq> []"
    assume "length pfx1 \<ge> 2"
    then have pfx1_nempty: "pfx1 \<noteq> []"
      by auto
    assume pfx2_nempty: "pfx2 \<noteq> []"
    assume from_tree: "p1 = pfx1 @ p" "p2 = pfx2 @ p"
    assume odd_lens: "odd (length p1)" "odd (length p2)"
    assume last_pfx1_eq: "last pfx1 = last pfx2"
    assume hds_neq: "hd p1 \<noteq> hd p2"
    assume pfxs_disj: "set (butlast pfx1) \<inter> set pfx2 = {}"
    assume distinct: "distinct p1"
    {
      fix p1 pfx1::"'a list"
      assume from_tree: "p1 = pfx1 @ p"
      assume odd_lens: "odd (length p1)"
      assume alt_paths: "alt_path (-M) p1" "last p1 \<notin> Vs M"
      assume "length pfx1 \<ge> 2"
      then have "pfx1 \<noteq> []"
        by auto
      have "alt_path M ((rev p) @ [last pfx1, last (butlast pfx1)])"
      proof-
        have "last (edges_of_path ((last pfx1) # p)) = last (edges_of_path p1)"
          apply( simp add: from_tree(1) edges_of_path_append_2[OF \<open>p \<noteq> []\<close>])
          using \<open>pfx1 \<noteq> []\<close> \<open>p \<noteq> []\<close>
          by (metis edges_of_path.simps(3) edges_of_path_append_2 edges_of_path_append_3 last_appendR neq_Nil_conv)
        moreover have "last (edges_of_path p1) \<notin> M"
        proof-
          have "(edges_of_path p1) \<noteq> []"
            by (simp add: \<open>2 \<le> length pfx1\<close> \<open>pfx1 \<noteq> []\<close> edges_of_path_append_3 edges_of_path_nempty from_tree)
          then show ?thesis
            using alt_paths(2) edges_of_path_nempty last_edge_in_last_vert_in
            by auto
        qed
        ultimately have "last (edges_of_path ((last pfx1) # p)) \<notin> M"
          by auto
        moreover have "length p1 \<ge> 2"
          using \<open>2 \<le> length pfx1\<close> from_tree
          by simp
        ultimately have revp1_alt: "alt_path M (rev p1)"
          apply(intro odd_alt_path_rev alt_paths odd_lens)
          by simp+
        have "\<exists>pfx1'. rev pfx1 = [last pfx1, last (butlast pfx1)] @ pfx1'"
        proof-
          have "length (rev pfx1) \<ge>  2"
            using \<open>length pfx1 \<ge>  2\<close>
            by simp
          then obtain a b pfx1'' where "rev pfx1 = a # b # pfx1''"
            apply (simp only: numeral_2_eq_2 Suc_le_length_iff)
            by fastforce
          then have pfx1'': "pfx1 = ((rev pfx1'') @ [b]) @ [a]"
            by auto
          then have "a = last pfx1" "b = last (butlast pfx1)"
            by (simp only: butlast_snoc last_snoc)+
          then show ?thesis
            using pfx1''
            by fastforce
        qed
        then obtain pfx1' where "rev pfx1 = ([last pfx1, last (butlast pfx1)]) @ pfx1'"
          by metis
        then have revp1_eq: "rev p1 = (rev p @ [last pfx1, last (butlast pfx1)]) @pfx1'"
          using from_tree(1)
          by auto
        have eop_cat: "edges_of_path ((rev p @ [last pfx1, last (butlast pfx1)]) @ pfx1') = (edges_of_path (rev p @ [last pfx1, last (butlast pfx1)]) @ (edges_of_path ((last (butlast pfx1)) # pfx1')))"
          using edges_of_path_append_2
          by (smt (verit, best) append_is_Nil_conv edges_of_path_append_3 last.simps last_append list.discI)
        show ?thesis
          apply(rule conjunct1[OF alt_list_append_1])
          using revp1_alt
          by (simp only: eop_cat revp1_eq)
      qed
    }note * = this
    assume alt_paths: "alt_path M (hd p2 # p1)" "alt_path M (hd p1 # p2)" "last p1 \<notin> Vs M" 
    then have alt_paths': "alt_path (-M) p1" "alt_path (-M) p2" "{hd p1, hd p2} \<notin> M"
      by(intro alt_path_cons_odd[where p = p1 and v = "hd p2"] alt_path_cons_odd[where p = p2 and v = "hd p1"] odd_lens; simp)+
    have alt_path_pfx1: "alt_path M (rev p @ [last pfx1, last (butlast pfx1)])"
      using *[OF from_tree(1) odd_lens(1) alt_paths'(1) alt_paths(3) \<open>length pfx1 \<ge> 2\<close>]
      by simp
    have "alt_path M (rev p @ [last pfx1])"
      using alt_path_pfx1
      by (metis alt_list_append_1 edges_of_path_append_2 list.sel(1) list.simps(3))
    moreover assume odd_length: "odd (length (edges_of_path ((last pfx1) # p)))"
    ultimately have "last (edges_of_path ((rev p) @ [last pfx1])) \<notin> M"
      using alternating_list_gt_last[OF alternating_gt_odd]
      by (metis One_nat_def edges_of_path_rev even_Suc length_rev list.size(3) odd_one rev.simps(2))
    have "even (length (edges_of_path ((rev p) @ [last pfx1, last (butlast pfx1)])))"
      using odd_length
      by (metis One_nat_def append.assoc append_Cons append_Nil edges_of_path.simps(3) edges_of_path_rev length_rev list.size(4) odd_even_add odd_one rev.simps(2))
    then have "last (edges_of_path ((rev p) @ [last pfx1, last (butlast pfx1)])) \<in> M"
      using alt_path_pfx1
      by (metis Nil_is_append_conv \<open>p \<noteq> []\<close> alternating_list_even_last edges_of_path.simps(3) edges_of_path_append_3 list.simps(3) rev_is_Nil_conv)
    then have last_pfx1_matched: "{last pfx1, last (butlast pfx1)} \<in> M"
      by (metis edges_of_path.simps(2) edges_of_path.simps(3) edges_of_path_append last_snoc)
    have False
    proof(cases "length pfx2 > 1")
      case gt_1: True
      then have "length pfx2 \<ge> 2"
        by auto
      show ?thesis
      proof(cases "{last pfx2, last (butlast pfx2)} \<in> M")
        case last_pfx2_matched: True
        have "last (butlast pfx2) \<noteq> last (butlast pfx1)"
          using last_pfxs_neq[OF \<open>2 \<le> length pfx1\<close> \<open>2 \<le> length pfx2\<close> pfxs_disj]
          by blast
        then have "{last pfx2, last (butlast pfx2)} \<noteq> {last pfx1, last (butlast pfx1)}"
          using last_pfx1_eq
          by (auto simp add: doubleton_eq_iff)
        then show ?thesis 
          using matching last_pfx1_matched last_pfx2_matched \<open>last pfx1 = last pfx2\<close>
          by (metis edges_are_Vs insertI1 matching_def2)
      next
        have "last p2 \<notin> Vs M"
          using from_tree alt_paths(3) 
          by (simp add: \<open>p \<noteq> []\<close>)
        then have alt_path_pfx2: "alt_path M (rev p @ [last pfx2, last (butlast pfx2)])"
          using *[OF from_tree(2) odd_lens(2) alt_paths'(2) _ \<open>length pfx2 \<ge> 2\<close>]
          by simp
        moreover have "even (length (edges_of_path (rev p @ [last pfx2, last (butlast pfx2)])))"
          using odd_length \<open>last pfx1 = last pfx2\<close>
          by (metis One_nat_def append.assoc append_Cons append_Nil edges_of_path.simps(3) edges_of_path_rev length_rev list.size(4) odd_even_add odd_one rev.simps(2))
        moreover have "last (edges_of_path (rev p @ [last pfx2, last (butlast pfx2)])) = {last pfx2, last (butlast pfx2)}"
          by (metis edges_of_path.simps(2) edges_of_path.simps(3) edges_of_path_append last_snoc)
        ultimately have "{last pfx2, last (butlast pfx2)} \<in> M"
          using alternating_list_even_last edges_of_path_nempty by fastforce
        moreover case last_pfx2_unmatched: False
        ultimately show ?thesis
          by auto
      qed
    next
      case False
      then have "length pfx2 \<le> 1"
        by auto
      then have "length pfx2 = 1"
        using pfx2_nempty
        by (simp add: le_less)
      then have "hd pfx2 = last pfx2"
        by (auto simp add: numeral_2_eq_2 length_Suc_conv)
      then have "{hd pfx1, last pfx2} \<notin> M"
        using alt_paths'(3) from_tree(1) from_tree(2) pfx1_nempty pfx2_nempty
        by auto
      moreover have "{last pfx2, hd p} \<notin> M"
        by (metis (no_types, lifting) Nil_is_rev_conv \<open>last (edges_of_path (rev p @ [last pfx1])) \<notin> M\<close> \<open>p \<noteq> []\<close> edges_of_path_snoc insert_commute last_pfx1_eq last_rev snoc_eq_iff_butlast)
      ultimately show ?thesis
        using alt_paths(2) \<open>length pfx1 \<ge> 2\<close> \<open>length pfx2 = 1\<close> \<open>p \<noteq> []\<close>
        by(auto simp add: from_tree numeral_2_eq_2 Suc_le_length_iff length_Suc_conv neq_Nil_conv alt_list_step alt_list_empty)
    qed
  } note p_nempty_even = this

  show ?thesis
  proof(cases "p = []")
    case p_empty: True
    then show ?thesis
      by (simp add: \<open>drop (length pfx1) p1 = p\<close>)
  next
    case p_nempty: False
    show ?thesis
    proof(cases "2 \<le> length pfx1")
      case len_pf1_ge_2: True
      have "set (butlast pfx1) \<inter> set pfx2 = {}"
        by (simp add: disj_pfx_are_disj_2 pfxs_are_pfxs)
      show ?thesis
        using p_nempty_even[OF p_nempty len_pf1_ge_2 pfx2_nempty from_tree odd_lens \<open>last pfx1 = last pfx2\<close> hds_neq \<open>set (butlast pfx1) \<inter> set pfx2 = {}\<close> distinct(1) alt_paths(1,2,3)]
        by (metis \<open>drop (length pfx1) p1 = p\<close> calculation edges_of_path_rev hd_rev length_rev pfx1_nempty rev.simps(2))
    next
      case False
      then have len_pf1_le_1: "length pfx1 \<le> 1"
        by auto
      show ?thesis
      proof(cases "2 \<le> length pfx2")
        case len_pf2_ge_2: True
        have "set (butlast pfx2) \<inter> set pfx1 = {}"
          using disj_pfx_are_disj_1 pfxs_are_pfxs by fastforce
        have "{hd p2, hd p1} \<notin> M"
          by(intro alt_path_cons_odd alt_paths(1) odd_lens)
        have "last p2 \<notin> Vs M"
          using assms(6) from_tree(1) from_tree(2) p_nempty by auto
        have "last pfx2 = last pfx1"
          by (simp add: last_pfx1_eq)
        show ?thesis
          using p_nempty_even[OF p_nempty len_pf2_ge_2 pfx1_nempty from_tree(2,1) odd_lens(2,1) \<open>last pfx2 = last pfx1\<close> hds_neq[symmetric] \<open>set (butlast pfx2) \<inter> set pfx1 = {}\<close> distinct(2) alt_paths(2,1) \<open>last p2 \<notin> Vs M\<close>]
          by (metis \<open>drop (length pfx1) p1 = p\<close> calculation edges_of_path_rev hd_rev last_pfx1_eq length_rev pfx1_nempty rev.simps(2))
      next
        case len_pf2_le_1: False
        then show ?thesis
          by (metis One_nat_def Suc_1 append_Nil drop0 drop_all from_tree(1) from_tree(2) hds_neq
                    impossible_Cons last_pfx1_eq len_pf1_le_1 list.exhaust_sel not_less_eq_eq
                    order_antisym pfx1_nempty pfx2_nempty snoc_eq_iff_butlast)
      qed
    qed
  qed
qed

lemma common_pfxs_form_match_blossom':
  assumes pfxs_are_pfxs: "(Some pfx1, Some pfx2) = longest_disj_pfx p1 p2" and
    from_tree: "p1 = pfx1 @ p" "p2 = pfx2 @ p" and
    alt_paths: "alt_path M (hd p2 # p1)" "alt_path M (hd p1 # p2)"
    "last p1 \<notin> Vs M" and
    hds_neq: "hd p1 \<noteq> hd p2" and
    odd_lens: "odd (length p1)" "odd (length p2)" and
    distinct: "distinct p1" "distinct p2" and
    matching: "matching M"
  shows "match_blossom M (rev (drop (length pfx1) p1)) (rev pfx1 @ pfx2)"
proof-
  have alt_paths': "alt_path (-M) p1" "alt_path (-M) p2" "{hd p1, hd p2} \<notin> M"
    by(intro alt_path_cons_odd[OF odd_lens(1) alt_paths(1)] alt_path_cons_odd[OF odd_lens(2) alt_paths(2)])+
  have "(rev (drop (length pfx1) p1)) @ rev pfx1 = rev p1"
    using assms(1) disj_pref_append1 by fastforce
  then have " (rev (drop (length pfx1) p1) @ rev pfx1 @ pfx2) = rev p1 @ pfx2"
    by auto
  moreover have "p1 \<noteq> []"
    using first_pfx_nempty from_tree(1) pfxs_are_pfxs by auto
  ultimately have "hd (rev (drop (length pfx1) p1) @ rev pfx1 @ pfx2) = last p1"
    by (simp add: \<open>rev (drop (length pfx1) p1) @ rev pfx1 @ pfx2 = rev p1 @ pfx2\<close> hd_rev)
  then show ?thesis
    unfolding match_blossom_def      
    apply(intro conjI pfxs_even_stem'[OF assms(1-5) _ hds_neq odd_lens distinct matching]
        pfxs_odd_cycle'[OF pfxs_are_pfxs from_tree alt_paths'(1,2,3) hds_neq odd_lens]
        pfxs_distinct[OF pfxs_are_pfxs distinct from_tree] 
        pfxs_alt_path'[OF pfxs_are_pfxs alt_paths(1,2) ]
        alt_paths(3))
    subgoal using odd_lens(1) .
    subgoal using odd_lens(2) .
    subgoal by (simp add: assms(6))
    done
qed

lemma construct_aug_path:
  assumes
    disj_paths: "set p1 \<inter> set p2 = {}" and
    nempty: "p1 \<noteq> []" "p2 \<noteq> []" and
    alt_paths: "alt_path M p1" "alt_path M p2"
    "last p1 \<notin> Vs M" "last p2 \<notin> Vs M"
    "{hd p1, hd p2} \<in> M" and 
    even_lens: "even (length p1)" "even (length p2)"
  shows "matching_augmenting_path M ((rev p1) @ p2)"
proof-
  have "length p1 \<ge> 2"
    using alt_paths(3,5) nempty
    apply (auto simp add: Vs_def numeral_2_eq_2 Suc_le_length_iff)
    by (metis edges_of_path.cases insertI1 last.simps list.sel(1))
  then have "last (edges_of_path p1) \<notin> M"
    using alt_paths
    by (meson last_edge_in_last_vert_in)
  then have "alt_path M (rev p1)"
    using alt_paths(1) alt_list_rev
    by (simp add: \<open>2 \<le> length p1\<close> even_alt_path_rev even_lens(1))
  moreover have "last (edges_of_path (rev p1)) \<notin> M"
    apply(simp add: edges_of_path_rev[symmetric])
    by (metis \<open>last (edges_of_path p1) \<notin> M\<close> alt_list_step assms(4) last_rev list.exhaust_sel rev.simps(1))
  moreover have "alt_path (-M) (hd p1 # p2)"
    using alt_paths(2,5)
    by(cases p2; auto simp add: alt_list_step alt_list_empty)
  moreover have "edges_of_path ((rev p1) @ p2) = (edges_of_path (rev p1)) @ (edges_of_path (hd p1 # p2))"
    by (metis (no_types, lifting) edges_of_path_append_2 edges_of_path_rev nempty(1) rev.simps(2) rev_append rev_rev_ident)
  ultimately have "alt_path M ((rev p1) @ p2)"
    apply simp
    apply(intro alt_list_append_2)
    subgoal by auto
    subgoal by auto
    subgoal using  even_lens(1)
      by (simp add: edges_of_path_length'[OF nempty(1)])
    done
  moreover have " 2 \<le> length (rev p1 @ p2)"
    using \<open>2 \<le> length p1\<close> by auto
  moreover have "hd (rev p1 @ p2) \<notin> Vs M"
    by (simp add: assms(6) hd_rev nempty(1))
  moreover have "last (rev p1 @ p2) \<notin> Vs M"
    by (simp add: assms(7) nempty(2))
  ultimately show ?thesis
    unfolding matching_augmenting_path_def
    by simp
qed

lemma construct_aug_path':
  assumes
    disj_paths: "set p1 \<inter> set p2 = {}" and
    nempty: "p1 \<noteq> []" "p2 \<noteq> []" and
    alt_paths: "alt_path M (hd p2 # p1)" "alt_path M (hd p1 # p2)"
    "last p1 \<notin> Vs M" "last p2 \<notin> Vs M" and 
    odd_lens: "odd (length p1)" "odd (length p2)"
  shows "matching_augmenting_path M ((rev p1) @ p2)"
proof(cases "length p1 \<ge> 2")
  case True
  then have "alt_path (-M) p1"
    using alt_paths(1)
    using alt_path_cons_odd(1) odd_lens(1) by fastforce
  have "last (edges_of_path p1) \<notin> M"
    using alt_paths True
    by (meson last_edge_in_last_vert_in)
  moreover have "(edges_of_path p1) \<noteq> []"
    using True
    by (simp add: edges_of_path_nempty)
  ultimately have "last (edges_of_path (rev p1)) \<in> M"
    using \<open>alt_path (-M) p1\<close>
    apply(simp add: edges_of_path_rev[symmetric] last_rev)
    by (metis alt_list_step list.exhaust_sel)  
  moreover have "edges_of_path ((rev p1) @ p2) = (edges_of_path (rev p1)) @ (edges_of_path (hd p1 # p2))"
    by (metis (no_types, lifting) edges_of_path_append_2 edges_of_path_rev nempty(1) rev.simps(2) rev_append rev_rev_ident)
  moreover have "alt_path M (rev p1)"
    using alt_paths(1) alt_list_rev \<open>alt_path (-M) p1\<close>
    by (simp add: True odd_alt_path_rev odd_lens(1))
  ultimately have "alt_path M ((rev p1) @ p2)"
    apply simp
    apply(intro alt_list_append_3)
    subgoal by auto
    subgoal using alt_paths(2) .
    subgoal using alternating_list_odd_last by blast
    done
  moreover have " 2 \<le> length (rev p1 @ p2)"
    using \<open>2 \<le> length p1\<close> by auto
  moreover have "hd (rev p1 @ p2) \<notin> Vs M"
    by (simp add: assms(6) hd_rev nempty(1))
  moreover have "last (rev p1 @ p2) \<notin> Vs M"
    by (simp add: assms(7) nempty(2))
  ultimately show ?thesis
    unfolding matching_augmenting_path_def
    by simp
next
  case False
  then have "p1 = [hd p1]"
    using odd_lens(1)
    by (metis Suc_eq_plus1 edges_of_path_length' edges_of_path_nempty length_0_conv length_Suc_conv
              list.sel(1) nempty(1))
  have "alt_path M ((rev p1) @ p2)"
    using alt_paths(2)
    apply(subst \<open>p1 = [hd p1]\<close>)
    by simp
  moreover have " 2 \<le> length (rev p1 @ p2)"
    using odd_lens(2)
    by (metis False Nil_is_append_conv edges_of_path_length' edges_of_path_nempty even_add
              length_append length_rev nempty(1))
  moreover have "hd (rev p1 @ p2) \<notin> Vs M"
    by (simp add: assms(6) hd_rev nempty(1))
  moreover have "last (rev p1 @ p2) \<notin> Vs M"
    by (simp add: assms(7) nempty(2))
  ultimately show ?thesis
    unfolding matching_augmenting_path_def
    by simp
qed

lemma odd_cycle_length_edges_ge_3:
  assumes "odd_cycle p"
  shows "length (edges_of_path p) \<ge> 3"
  using odd_cycleD[OF assms]
  by (metis One_nat_def Suc_le_eq Suc_pred assms edges_of_path_length gt_zero linorder_neqE_nat
            linorder_not_le odd_cycle_even_verts odd_numeral)

lemma odd_cycle_length_verts_ge_4:
  assumes "odd_cycle p"
  shows "length p \<ge> 4"
  using odd_cycle_length_edges_ge_3[OF assms]
  by (metis Suc_leI assms le_eq_less_or_eq numeral_3_eq_3 numeral_4_eq_4 odd_cycle_def
            odd_cycle_even_verts odd_numeral)

lemma odd_cycle_set_butlast_tl:
  assumes "odd_cycle C"
  shows "set (butlast C) = set (tl C)"
  using odd_cycleD[OF assms] odd_cycle_nempty[OF assms]
  by (simp add: set_butlast_tl)

locale match = graph_abs G for G+ 
  fixes M
  assumes matching: "matching M" "M \<subseteq> G"

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
(*  create_vert::"'a set \<Rightarrow> 'a" and*)
(*  G M::"'a set set"*)

begin

abbreviation "compute_alt_path_spec' \<equiv> compute_alt_path_spec G M compute_alt_path"
  
(*lemma compute_alt_path_spec_works_1:
  assumes "compute_alt_path_spec"
  shows 
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
    "Some(p1, p2) = compute_alt_path \<Longrightarrow> path G p2"
    "compute_alt_path = Some (p1, p2) \<Longrightarrow> {hd p1, hd p2} \<in> G"
  using assms
  unfolding compute_alt_path_spec_def
  by metis+
*)
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

(*
abbreviation 
  "find_max_matching_3 \<equiv> 
       find_aug_path.find_max_matching_2 
       (compute_match_blossom'.compute_match_blossom compute_alt_path) create_vert"

*)


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

subsection \<open>Data Structure of Search Forest\<close>


definition follow_invar::"('a \<Rightarrow> 'a option) \<Rightarrow> bool" where
  "follow_invar par = ((\<forall>v. (\<exists>v'. (v' = v \<or> (v', v) \<in> {(v',v) | v' v. (Some v' = par v)}\<^sup>+) \<and> par v' = None)) \<and>
                      (\<forall>v v'. par v = Some v' \<longrightarrow>  v \<noteq> v') \<and> 
                      finite {(x, y) |x y. (Some x = par y)})"

(*Done: Invar 3*)

definition parent_spec::"('a \<Rightarrow> 'a option) \<Rightarrow> bool" where
  "parent_spec parent = wf {(x, y) |x y. (Some x = parent y)}"


locale parent = 
  fixes parent::"'a \<Rightarrow> 'a option" and
    parent_rel::"'a \<Rightarrow> 'a \<Rightarrow> bool"

  assumes parent_rel:
    "parent_spec parent"
begin

function (domintros) follow where
  "follow v = (case (parent v) of Some v' \<Rightarrow> v # (follow v') | _  \<Rightarrow> [v])"
  by pat_completeness auto


lemma assumes "parent v = None"
  shows "follow_dom v"
  apply(rule follow.domintros)
  using assms
  by auto

lemma assumes "parent v' = Some v" "follow_dom v"
  shows "Wellfounded.accp follow_rel v'"
  apply(rule follow.domintros)
  using assms
  by auto

lemma wfP_follow_rel:
  assumes "wfP follow_rel"
  shows "follow_dom v"
  using accp_wfpD[OF assms]
  by blast

lemma wf_follow_rel:
  assumes "wf {(x,y) | x y. follow_rel x y}"
  shows "follow_dom v"
  using wfP_follow_rel assms
  unfolding wfp_def
  by force

lemma parent_eq_follow_rel: "follow_rel = (\<lambda>v' v. Some v' = parent v)"
  unfolding parent_rel follow_rel.simps
  apply simp
  apply(rule HOL.ext)+
  by auto

lemma wf_found_rel:
  "wf {(x,y) | x y. follow_rel x y}"
  unfolding parent_eq_follow_rel
  using parent_rel[unfolded parent_spec_def]
  by simp

lemma follow_dom:
  "follow_dom v"
  using wf_found_rel wf_follow_rel
  by force

lemma follow_cons:
  "follow u = v # p \<Longrightarrow> v = u"
  by (auto simp: follow.psimps[OF follow_dom] split: option.splits)

lemma follow_cons_2:
  "follow v = v # v' # p \<Longrightarrow> follow v' = v' # p"
  "follow v = v # v' # p \<Longrightarrow> parent v = Some v'"
  by(cases "parent v"; simp add: follow.psimps[OF follow_dom]; clarsimp split: option.splits)+

lemma follow_append:
  "follow v = p @ u # p' \<Longrightarrow> follow u = u # p'"
proof(induction "follow v" arbitrary: v p)
  case nil1: Nil
  then show ?case 
    by auto
next
  case cons1: (Cons v' follow_v')
  then have "v' = v"
    using follow_cons
    by metis
  show ?case
  proof (cases follow_v')
    case nil2: Nil
    then have "v = u" "p = []"
      using cons1 \<open>v' = v\<close>
      by (simp add: Cons_eq_append_conv)+
    then show ?thesis
      using cons1
      by auto
  next
    case cons2: (Cons v'' follow_v'')
    then show ?thesis
      using cons1
      by (metis \<open>v' = v\<close> append_eq_Cons_conv follow_cons_2 list.sel(1))
  qed
qed

lemma from_tree:
  assumes "follow v1 = p1 @ u # p1'" "follow v2 = p2 @ u # p2'"
  shows "p1' = p2'"
  using follow_append follow_append
    assms parent_axioms
  by fastforce

lemma follow_psimps:
  "follow v = (case parent v of None \<Rightarrow> [v] | Some v' \<Rightarrow> v # follow v')"
  using follow.psimps[OF follow_dom] .

end


context parent
begin

lemma follow_nempty: "follow v \<noteq> []"
  apply(subst follow.psimps[OF follow_dom])
  by(auto simp add: option.case_eq_if split: if_splits)

lemma follow_None:
  "follow v = [v'] \<Longrightarrow> parent v = None"
  apply(subst (asm) follow.psimps[OF follow_dom])
  by(auto simp add: follow_nempty option.case_eq_if split: if_splits)


lemma nin_ancestors: "\<forall>v2\<in>set (follow v1). parent v2 \<noteq> Some v3 \<Longrightarrow> v3 \<noteq> v1 \<Longrightarrow>  v3 \<notin> set (follow v1)"
proof(induction rule: follow.pinduct[OF follow_dom[of v1]])
  case (1 v)
  then show ?case
  proof (cases "parent v")
    case None
    then show ?thesis
      using 1
      by (simp add: follow_psimps)
  next
    case (Some a)
    then show ?thesis
      using 1
      using follow_psimps by auto
  qed
qed

end

lemma follow_cong:
  assumes "parent par" "parent.follow_dom par v"
  shows "(\<forall>v'\<in>set(parent.follow par v). par v' = par' v') \<Longrightarrow> parent par' \<Longrightarrow> parent.follow par v = parent.follow par' v"
  using assms(2)
proof(induction rule: parent.follow.pinduct[OF assms])
  case (1 v)
  then show ?case
  proof(cases "par v")
    case None
    then show ?thesis
      apply( simp add: parent.follow_psimps[OF 1(4)])
      by (metis (mono_tags, lifting) "1.hyps" "1.prems"(1) assms(1) list.set_intros(1) option.case_eq_if parent.follow.psimps)
  next
    case (Some a)
    have "\<forall>v\<in>set (parent.follow par a). par v = par' v"
      by (simp add: "1.prems"(1) "1.prems"(3) Some assms(1) parent.follow.psimps)
    moreover have "parent.follow_dom par a"
      by (simp add: assms(1) parent.follow_dom)
    ultimately have "parent.follow par a = parent.follow par' a" 
      using 1
      using Some by blast
    moreover have "par' v = Some a"
      using "1.hyps" "1.prems"(1) Some assms(1) parent.follow.psimps by fastforce
    ultimately show ?thesis
      using 1(4) Some
      by(auto simp add: parent.follow_psimps[OF assms(1)] parent.follow_psimps[OF 1(4)] )
  qed
qed

lemma v2_nin_ancestors:
  assumes
    "parent par" and
    "\<forall>v''. par v'' \<noteq> Some v2" "v2 \<noteq> v"
  shows "\<forall>v'\<in>set(parent.follow par v). v' \<noteq> v2"
  using assms
proof(induction v rule: parent.follow.pinduct[OF assms(1) parent.follow_dom[OF assms(1)]])
  case (1 v)
  show ?case
  proof(cases "par v")
    case None
    then show ?thesis
      using 1(5)
      by(simp add: parent.follow_psimps[OF 1(3)])
  next
    case (Some a)
    have "\<forall>v\<in>set (parent.follow par a). v \<noteq> v2"
      using "1.IH" Some assms(1) assms(2) by blast
    then show ?thesis
      using "1.hyps" "1.prems"(3) Some assms(1) parent.follow.psimps by fastforce
  qed    
qed

lemma ancestors_unaffected_1:
  assumes
    "parent par" and
    "\<forall>v'\<in>set(parent.follow par v). v' \<noteq> v2" and
    f': "f' = (f(v2 \<mapsto> v1))"
  shows "\<forall>v'\<in>set(parent.follow par v). f v' = f' v'"
  using assms
proof(induction v rule: parent.follow.pinduct[OF assms(1) parent.follow_dom[OF assms(1)]])
  case (1 v)
  show ?case
  proof(cases "par v")
    case None
    then show ?thesis
      using 1
      by( simp add: parent.follow_psimps[OF 1(3)])
  next
    case (Some a)
    then have "\<forall>v\<in>set (parent.follow par a). f v = f' v"
      apply(intro 1)
      using 1(4)
      by (simp add: f' parent.follow_psimps[OF 1(3)])+
    then show ?thesis
      by (simp add: "1.prems"(2) "1.prems"(3))
  qed
qed

lemma no_children_not_in_follow:
  assumes
    "parent par" and
    "\<forall>v''. par v'' \<noteq> Some v2" "v2 \<noteq> v" and
    par': "par' = (par(v2 \<mapsto> v1))"
  shows "\<forall>v'\<in>set(parent.follow par v). par v' = par' v'"
  using assms
proof(induction  rule: parent.follow.pinduct[OF assms(1) parent.follow_dom[OF assms(1)]])
  case (1 v)
  show ?case
  proof(cases "par v")
    case None
    then show ?thesis
      using 1
      by( simp add: parent.follow_psimps[OF 1(3)])
  next
    case (Some a)
    have "\<forall>v\<in>set (parent.follow par a). par v = par' v"
      using "1.IH" Some assms(1) assms(2) par' by blast
    then show ?thesis
      using "1.hyps" "1.prems"(3) Some assms(1) par' parent.follow.psimps by fastforce
  qed    
qed


subsection \<open>Main Search Procedure: Finding Alternating Paths\<close>

subsubsection \<open>Modelling the Search Procedure as a Recursive Function\<close> 

datatype label = Odd | Even

locale compute_alt_path = match G M + choose sel 

for G M::"'a set set" and sel::"'a set \<Rightarrow> 'a"

(*fixes M :: "'a set set" and create_vert::"'a set \<Rightarrow> 'a"*)
(*
assumes
  matching: "matching M"" M \<subseteq> G" (*and
        create_vert_works:
        "finite vs \<Longrightarrow> create_vert vs \<notin> vs"*)
*)

begin

text \<open>At this stage we don't want t assume that the vertices have any ordering.\<close>

definition if1_cond where "if1_cond flabel ex = (\<exists>v1 v2. {v1, v2} \<in> G - ex \<and>
                                                         (\<exists>r. flabel v1 = Some (r, Even)) \<and>
                                                         flabel v2 = None \<and> (\<exists>v3. {v2, v3} \<in> M))"

definition if1 where (*I am using this because when the RHS is in the function the function package messes up the pairing.*)
  "if1 flabel ex v1 v2 v3 r = ({v1, v2} \<in> G - ex \<and>
             flabel v1 = Some (r, Even) \<and> flabel v2 = None \<and> {v2, v3} \<in> M)"

find_theorems dblton_graph "(\<subseteq>)"

interpretation matching_graph: graph_abs M
  apply(unfold_locales)
  using graph_invar_subset[OF graph matching(2)] .

definition 
  "sel_if1 flabel ex = 
     (let es = D \<inter> {(v1,v2)| v1 v2. {v1,v2} \<in> (G - ex) \<and> (\<exists>r. flabel v1 = Some (r, Even)) \<and> flabel v2 = None \<and> v2 \<in> Vs M};
         (v1,v2) = sel_pair es;
         v3 = sel (neighbourhood M v2);
         r = fst (the (flabel v1)) 
     in (v1,v2,v3,r))"

definition if2_cond where "if2_cond flabel =
   (\<exists>v1 v2 r r'. {v1, v2} \<in> G \<and> flabel v1 = Some (r, Even) \<and> flabel v2 = Some (r', Even))"

definition if2 where 
  "if2 flabel v1 v2 r r' = ({v1, v2} \<in> G \<and> flabel v1 = Some (r, Even) \<and> flabel v2 = Some (r', Even))"

definition 
  "sel_if2 flabel = 
     (let es = D \<inter> {(v1,v2)| v1 v2. {v1, v2} \<in> G \<and> (\<exists>r1. flabel v1 = Some (r1, Even)) \<and> 
                                   (\<exists>r2. flabel v2 = Some (r2, Even))};
         (v1,v2) = sel_pair es;
         r1 = fst (the (flabel v1)); 
         r2 = fst (the (flabel v2)) 
     in (v1,v2,r1,r2))"

(*definition if1_1_cond where "if1_1_cond flabel v2 \<equiv> flabel v2 = None \<and> (\<exists>v3. {v2, v3} \<in> M)"*)

function (domintros) compute_alt_path:: "'a set set \<Rightarrow>
                                         ('a \<Rightarrow> 'a option) \<Rightarrow>
                                         ('a \<Rightarrow> ('a \<times> label) option) \<Rightarrow>
                                         (('a list \<times> 'a list) option)" where
  "compute_alt_path ex par flabel = 
    (if if1_cond flabel ex then
       let
         (v1,v2,v3,r) = sel_if1 flabel ex;
         ex' = insert {v1, v2} ex;
         ex'' = insert {v2, v3} ex';
         par' = par(v2 := Some v1, v3 := Some v2);
         flabel' = flabel(v2 := Some (r, Odd), v3 := Some (r, Even));
         return = compute_alt_path ex'' par' flabel'
       in
         return
     else if if2_cond flabel then
        let
          (v1,v2,r,r') = sel_if2 flabel; 
          return = Some (parent.follow par v1, parent.follow par v2)
        in
          return
     else
       let
          return = None
       in
         return)"
  by pat_completeness auto

subsubsection \<open>Reasoning Infrastructure\<close>

lemma if1_cond_props:
  "if1_cond flabel ex \<Longrightarrow> (\<exists>v1 v2. {v1, v2} \<in> G - ex \<and> (\<exists>r. flabel v1 = Some (r, Even)) \<and> flabel v2 = None \<and> (\<exists>v3. {v2, v3} \<in> M))"
  unfolding if1_cond_def
  .

lemma if1_cond_props':
  "if1_cond flabel ex \<Longrightarrow> (\<exists>v1 v2 v3 r. if1 flabel ex v1 v2 v3 r)"
  unfolding if1_cond_def if1_def by simp

lemma if2_cond_props:
  "if2_cond flabel \<Longrightarrow> (\<exists>v1 v2 r r'. if2 flabel v1 v2 r r')"
  unfolding if2_cond_def if2_def
  .

lemma if1_props:
  assumes "if1 flabel ex v1 v2 v3 r"
  shows 
    "{v1, v2} \<in> G - ex" "flabel v1 = Some (r, Even)" "flabel v2 = None" "{v2, v3} \<in> M"
  using assms
  unfolding if1_def 
  by auto

lemma if1_cond_props'':
  assumes "if1_cond flabel ex"
  obtains v1 v2 v3 r where "if1 flabel ex v1 v2 v3 r"
  using assms(1)
  unfolding if1_cond_def if1_def
  by (smt surj_pair)


lemma if1_cond_props''':
  assumes "if1_cond flabel ex" "(v1, v2, v3, r) = sel_if1 flabel ex"
  shows "if1 flabel ex v1 v2 v3 r"
proof-

  have "case (sel_if1 flabel ex) of (v1,v2,v3,r) \<Rightarrow> if1 flabel ex v1 v2 v3 r"
  proof-
    let ?es = "D \<inter> {(v1,v2)| v1 v2. {v1,v2} \<in> (G - ex) \<and> (\<exists>r. flabel v1 = Some (r, Even)) \<and> flabel v2 = None \<and> v2 \<in> Vs M}"
    have "?es\<noteq>{}"
      using assms 
      apply (clarsimp elim!: if1_cond_props'' simp: sel_if1_def edge_iff_edge_1 if1_def insert_commute split: prod.split)
      using insert_commute
      by blast
    moreover have "finite ?es"
      using Vs_eq_dVs finite_Vs finite_vertices_iff
      by fastforce
    ultimately have "sel_pair ?es \<in> ?es"
      by force
    moreover obtain v1 v2 where "sel_pair ?es = (v1,v2)"
      by (cases "sel_pair ?es") auto
    ultimately have "(neighbourhood M v2) \<noteq> {}"
      using assms \<open>?es \<noteq> {}\<close> matching_graph.vs_member'
      by (auto elim!: if1_cond_props''
               simp: sel_if1_def edge_iff_edge_1 if1_def neighbourhood_def 
               split: prod.split)
    moreover have "finite (neighbourhood M v2)"
      by (meson matching_graph.graph neighbourhood_subset_Vs rev_finite_subset)
    ultimately have "sel (neighbourhood M v2) \<in> (neighbourhood M v2)"
      by (auto simp add: sel)
    hence "{v2, sel (neighbourhood M v2)} \<in> M"
      by auto

    moreover have "\<exists>r. flabel v1 = Some (r, Even)"
      using \<open>sel_pair ?es \<in> ?es\<close> \<open>sel_pair ?es = (v1, v2)\<close>
      by auto

    ultimately show ?thesis
      using \<open>sel_pair ?es \<in> ?es\<close> \<open>sel_pair ?es = (v1, v2)\<close> \<open>if1_cond flabel ex\<close>
      by(auto simp: sel_if1_def if1_def)
  qed
  thus ?thesis
    using assms(2)
    by auto
qed

lemma if1_cond_props'''':
  assumes "if1_cond flabel ex"
  shows "\<exists>v1 v2 v3 r. (v1, v2, v3, r) = sel_if1 flabel ex \<and> if1 flabel ex v1 v2 v3 r"
proof-
  let ?q = "sel_if1 flabel ex"
  have "(fst ?q, fst (snd ?q), fst (snd (snd ?q)), snd (snd (snd ?q))) = ?q"
    by simp
  then show ?thesis
    using if1_cond_props'''[OF assms]
    by metis
qed

lemma if2_cond_props'':
  assumes "if2_cond flabel"
  obtains v1 v2 r r' where "if2 flabel v1 v2 r r'"
  using assms(1)
  unfolding if2_cond_def if2_def
  by (smt surj_pair)

lemma if2_cond_props''':
  assumes "if2_cond flabel" "(v1, v2, r1, r2) = sel_if2 flabel"
  shows "if2 flabel v1 v2 r1 r2"
proof-

  have "case (sel_if2 flabel) of (v1,v2,r1,r2) \<Rightarrow> if2 flabel v1 v2 r1 r2"
  proof-
    let ?es = "D \<inter> {(v1,v2)| v1 v2. {v1, v2} \<in> G \<and> (\<exists>r1. flabel v1 = Some (r1, Even)) \<and> 
                                   (\<exists>r2. flabel v2 = Some (r2, Even))}"
    have "?es\<noteq>{}"
      using assms 
      by (auto elim!: if2_cond_props'' simp: sel_if2_def edge_iff_edge_1 if2_def insert_commute split: prod.split)
    moreover have "finite ?es"
      using Vs_eq_dVs finite_Vs finite_vertices_iff
      by fastforce
    ultimately have "sel_pair ?es \<in> ?es"
      by force
    moreover obtain v1 v2 where "sel_pair ?es = (v1,v2)"
      by (cases "sel_pair ?es") auto
  

    moreover have "\<exists>r1. flabel v1 = Some (r1, Even)" "\<exists>r2. flabel v2 = Some (r2, Even)"
      using \<open>sel_pair ?es \<in> ?es\<close> \<open>sel_pair ?es = (v1, v2)\<close>
      by auto
    ultimately show ?thesis
      using \<open>sel_pair ?es \<in> ?es\<close> \<open>sel_pair ?es = (v1, v2)\<close> \<open>if2_cond flabel\<close>
      by(auto simp: sel_if2_def if2_def)
  qed

  thus ?thesis
    using assms(2)
    by force
qed

lemma if2_cond_props'''':
  assumes "if2_cond flabel"
  shows "\<exists>v1 v2 r r'. (v1, v2, r, r') = sel_if2 flabel \<and> if2 flabel v1 v2 r r'"
proof-
  let ?q = "sel_if2 flabel"
  have "(fst ?q, fst (snd ?q), fst (snd (snd ?q)), snd (snd (snd ?q))) = ?q"
    by simp
  then show ?thesis
    using if2_cond_props'''[OF assms]
    by metis
qed


lemma compute_alt_path_if1:
  assumes "compute_alt_path_dom (ex,par,flabel)" 
    "if1_cond flabel ex"
    "(v1, v2, v3, r) = sel_if1 flabel ex"
    "ex' = insert {v2, v3} (insert {v1, v2} ex)"
    "par' = par(v2 := Some v1, v3 := Some v2)"
    "flabel' = flabel(v2 := Some (r, Odd), v3 := Some (r, Even))"
  shows "local.compute_alt_path ex par flabel = compute_alt_path ex' par' flabel'"
  using assms
  by (auto simp add:  compute_alt_path.psimps[OF assms(1)] Let_def split: if_splits prod.splits)


lemma compute_alt_path_pinduct_2':
  assumes "compute_alt_path_dom (ex, par, flabel)"
    "(\<And>ex par flabel.
    compute_alt_path_dom (ex, par, flabel) \<Longrightarrow>
    (\<And>v1 v2 v3 r ex' par' flabel'.
        if1_cond flabel ex \<Longrightarrow>
        (v1,v2,v3,r) = sel_if1 flabel ex \<Longrightarrow>
        ex' = insert {v2,v3} (insert {v1, v2} ex) \<Longrightarrow>
        par' = par(v2 \<mapsto> v1, v3 \<mapsto> v2) \<Longrightarrow>
        flabel' = flabel(v2 \<mapsto> (r, Odd), v3 \<mapsto> (r, Even)) \<Longrightarrow> P ex' par' flabel') \<Longrightarrow>
    P ex par flabel)"
  shows "P ex par flabel"
  apply(rule compute_alt_path.pinduct[OF assms(1)])
  using assms(2)
  by metis

lemma compute_alt_path_pinduct_2:
  "compute_alt_path_dom (ex, par, flabel) \<Longrightarrow> 
(\<And>ex par flabel.
    compute_alt_path_dom (ex, par, flabel) \<Longrightarrow>
    (\<And>v1 v2 v3 r ex' par' flabel'.
        if1_cond flabel ex \<Longrightarrow>
        (v1,v2,v3,r) = sel_if1 flabel ex \<Longrightarrow>
        ex' = insert {v2, v3} (insert {v1, v2} ex) \<Longrightarrow>
        par' = par(v2 \<mapsto> v1, v3 \<mapsto> v2) \<Longrightarrow>
        flabel' = flabel(v2 \<mapsto> (r, Odd), v3 \<mapsto> (r, Even)) \<Longrightarrow> P ex' par' flabel') \<Longrightarrow>
    P ex par flabel) \<Longrightarrow> P ex par flabel"
  apply (rule compute_alt_path_pinduct_2')
  by metis+

subsubsection \<open>Termination of the Search Procedure\<close>

definition "compute_alt_path_meas ex = card (G - ex)"

lemma compute_alt_path_dom:
  assumes "finite ex" "ex \<subseteq> G"
  shows "compute_alt_path_dom (ex, par, flabel)"
  using assms
proof(induction "compute_alt_path_meas ex" arbitrary: ex par flabel rule: nat_less_induct)
  case 1
  then have IH: "compute_alt_path_dom (ex', par', flabel')"
    if "compute_alt_path_meas ex' < compute_alt_path_meas ex" "finite ex'" "ex' \<subseteq> G"
    for ex' par' flabel'
    using that
    by simp

  show ?case
  proof (cases "if1_cond flabel ex")
    case True
    {
      fix v1 v2 v3 r
      assume "(v1, v2, v3, r) = sel_if1 flabel ex"
      then have "if1 flabel ex v1 v2 v3 r"
        by(rule if1_cond_props'''[OF True])
      then have  v1v2: "{v1, v2} \<in> G - ex" "{v2, v3} \<in> M"
        by(rule if1_props)+
      then have "{v1, v2} \<in> G" "{v1, v2} \<notin> ex"
        by simp+
      define ex' where "ex' = insert {v1, v2} ex"

      have "compute_alt_path_meas ex' < compute_alt_path_meas ex"
      proof-
        have "card ex < card ex'"
          unfolding ex'_def
          using 1(2) \<open>{v1, v2} \<notin> ex\<close>
          by auto
        moreover have "compute_alt_path_meas ex' = card G - card ex'"
          unfolding compute_alt_path_meas_def ex'_def
          using graph 1(2,3) \<open>{v1,v2} \<in> G\<close>
          by (simp add: card_Diff_subset)
        moreover have "compute_alt_path_meas ex = card G - card ex"
          unfolding compute_alt_path_meas_def
          using graph 1(2,3)
          by (simp add: card_Diff_subset)
        ultimately show ?thesis
          apply simp
          apply(intro diff_less_mono2)
          subgoal .
          subgoal apply(rule psubset_card_mono)
            subgoal using finite_E .
            subgoal apply(rule psubsetI)
              subgoal using 1(3) .
              subgoal using \<open>{v1, v2} \<in> G\<close> \<open>{v1, v2} \<notin> ex\<close>
                by auto
              done
            done
          done
      qed       
      moreover have "finite ex'"
        unfolding ex'_def
        using 1(2)
        by auto
      ultimately have "compute_alt_path_meas (insert e ex') < compute_alt_path_meas ex" for e
        apply(simp add: compute_alt_path_meas_def ex'_def)
        by (metis Diff_insert card_Diff1_le dual_order.strict_trans1 linorder_not_le)
      moreover have "finite (insert e ex')" for e
        by (simp add: \<open>finite ex'\<close>)
      moreover have "{v2, v3} \<in> G"
        using matching(2) \<open>{v2, v3} \<in> M\<close>
        by auto
      then have "(insert {v2, v3} ex') \<subseteq> G"
        unfolding ex'_def
        using \<open>{v1,v2} \<in> G\<close> 1(3)
        by auto
      ultimately have compute_alt_path_dom_ex': "compute_alt_path_dom (insert {v2, v3} ex', par', flabel')" for par' flabel'
        apply(intro IH)
        .
    }
    then show ?thesis
      using compute_alt_path.domintros
      by metis
  next
    case False
    then show ?thesis
      apply(subst compute_alt_path.domintros)
      by blast+
  qed
qed


lemma assumes 
  "compute_alt_path_dom(ex, par, flabel)"
  "Some (p1, p2) = compute_alt_path ex par flabel"
shows "\<exists>v1 par. p1 = parent.follow par v1"
  using assms
  apply(induction rule: compute_alt_path.pinduct)
  by(auto simp add: compute_alt_path.psimps Let_def split: if_splits option.splits prod.splits)

lemma assumes 
  "compute_alt_path_dom(ex, par, flabel)"
  "Some (p1, p2) = compute_alt_path ex par flabel"
shows "\<exists>v2 par. p2 = parent.follow par v2"
  using assms
  apply(induction rule: compute_alt_path.pinduct)
  by(auto simp add: compute_alt_path.psimps Let_def split: if_splits option.splits prod.splits)

subsubsection \<open>Algorithm is Partially Correct: Any Computed Alternating Paths Satisfy the Correctness Props\<close>

lemma wf_par':
  assumes wf: "parent_spec par" and
    par': "par' = par(v2 := Some v1, v3 := Some v2)" and
    neq: "v1 \<noteq> v2" "v2 \<noteq> v3" "v1 \<noteq> v3" and
    no_ances: "\<forall>v. par v \<noteq> Some v2" "\<forall>v. par v \<noteq> Some v3" and
    no_par: "par v2 = None" "par v3 = None"
  shows "parent_spec par'" (is ?g1) "parent_spec (par(v2 := Some v1))" (is ?g2)
proof-
  have "(v2, v1) \<notin> {(x,y) | x y. (Some x = par y)}\<^sup>*"
    using neq(1) no_ances(1)
    apply clarsimp
    by (metis (mono_tags, lifting) converse_rtranclE mem_Collect_eq old.prod.case)
  then have wf_v2_v1: "wf (insert (v1, v2) {(x,y) | x y. (Some x = par y)})"
    using wf[unfolded parent_spec_def] by blast
  moreover have "{(x, y) |x y. Some x = (par(v2 \<mapsto> v1)) y} = (insert (v1, v2) {(x, y) |x y. Some x = par y})"
    using neq(1) no_par
    by auto
  ultimately show ?g2
    unfolding parent_spec_def
    by simp

  have "(v3, v2) \<notin> {(x,y) | x y. (Some x = par y)}\<^sup>*"
    using neq(2) no_ances(2)
    apply clarsimp
    by (metis (mono_tags, lifting) converse_rtranclE mem_Collect_eq old.prod.case)
  moreover have "(v3, v2) \<notin>  {(x, y). (x, v1) \<in> {(x,y) | x y. (Some x = par y)}\<^sup>* \<and> (v2, y) \<in> {(x,y) | x y. (Some x = par y)}\<^sup>*}"
    using neq(3) no_ances(2)
    apply clarsimp
    by (metis (mono_tags, lifting) converse_rtranclE mem_Collect_eq old.prod.case)
  ultimately have "(v3, v2) \<notin> (insert (v1, v2) {(x,y) | x y. (Some x = par y)})\<^sup>*"
    unfolding rtrancl_insert
    by simp
  then have "wf (insert (v2, v3) (insert (v1, v2) {(x,y) | x y. (Some x = par y)}))"
    apply(subst wf_insert)
    using wf_v2_v1
    by simp
  moreover have "{(x,y) | x y. (Some x = par' y)} = insert (v2, v3) (insert (v1, v2) {(x,y) | x y. (Some x = par y)})"
    using neq(1,2) no_par
    by(auto simp add: par')
  ultimately show ?g1
    unfolding parent_spec_def
    by simp
qed

(*Done: Invar 4*)

definition flabel_invar where "flabel_invar flabel = (\<forall>v1 v2. {v1, v2} \<in> M \<longrightarrow> ((flabel v1 = None) \<longleftrightarrow> (flabel v2 = None)))"

(*Done: Invar 10 *)

definition flabel_invar_2 where
  "flabel_invar_2 flabel =
     (\<forall>v1 v2. {v1, v2} \<in> M \<longrightarrow> ((\<exists>r. flabel v1 = Some (r, Even))
                     \<longleftrightarrow> (\<exists>r. flabel v2 = Some (r, Odd))))"

(*Done: Invar 5*)

definition flabel_par_invar where "flabel_par_invar par flabel = (\<forall>v. (flabel v = None) \<longrightarrow> (par v = None \<and> (\<forall>v'. par v' \<noteq> Some v)))"

lemma 
  assumes "(\<forall>v. par v = None)"
  shows "wf {(x,y). par y = Some x}"
  using assms wf_empty
  by simp

lemma flabel_invar_2_props:
  "flabel_invar_2 flabel \<Longrightarrow> flabel v1 = Some (r, Even) \<Longrightarrow> flabel v2 = Some (s, Even) \<Longrightarrow> {v1, v2} \<notin> M"
  unfolding flabel_invar_2_def
  by force

lemma flabel_invar_pres:
  assumes invars: "flabel_invar flabel" and
    ass: "if1 flabel ex v1 v2 v3 r"
  shows "flabel_invar (flabel(v2 := Some (r, lab), v3 := Some (r2, lab2)))"
proof-
  have "{v1,v2} \<in> G - ex" "flabel v1 = Some (r, Even)" "{v2, v3} \<in> M" "flabel v2 = None"
    by (intro if1_props[OF ass])+
  have "flabel v3 = None"
    using invars \<open>{v2, v3} \<in> M\<close> \<open>flabel v2 = None\<close>
    unfolding flabel_invar_def
    by auto

  have "v = v2" if "{v, v3} \<in> M" for v
    using matching that \<open>{v2,v3} \<in> M\<close>
    unfolding matching_def2
    apply (clarsimp simp add: doubleton_eq_iff Vs_def)
    by (smt doubleton_eq_iff insertI1)
  moreover have "v = v3" if "{v, v2} \<in> M" for v
    using matching that \<open>{v2,v3} \<in> M\<close>
    unfolding matching_def2
    apply (clarsimp simp add: doubleton_eq_iff Vs_def)
    by (smt doubleton_eq_iff insertI1)
  ultimately show ?thesis
    using invars
    unfolding flabel_invar_def
    apply safe
    subgoal by (smt \<open>\<And>va. {va, v2} \<in> M \<Longrightarrow> va = v3\<close> \<open>\<And>va. {va, v3} \<in> M \<Longrightarrow> va = v2\<close> fun_upd_idem_iff fun_upd_other fun_upd_upd option.distinct(1))
    subgoal by (metis \<open>\<And>v2a v1a. \<lbrakk>\<And>v. {v, v3} \<in> M \<Longrightarrow> v = v2; \<And>v. {v, v2} \<in> M \<Longrightarrow> v = v3; \<forall>v1 v2. {v1, v2} \<in> M \<longrightarrow> (flabel v1 = None) = (flabel v2 = None); {v1a, v2a} \<in> M; (flabel(v2 \<mapsto> (r, lab), v3 \<mapsto> (r2, lab2))) v1a = None\<rbrakk> \<Longrightarrow> (flabel(v2 \<mapsto> (r, lab), v3 \<mapsto> (r2, lab2))) v2a = None\<close> \<open>\<And>va. {va, v2} \<in> M \<Longrightarrow> va = v3\<close> \<open>\<And>va. {va, v3} \<in> M \<Longrightarrow> va = v2\<close> doubleton_eq_iff)
    done
qed

lemma flabel_invar_2_pres:
  assumes invars: "flabel_invar_2 flabel" and
    ass: "if1 flabel ex v1 v2 v3 r"
  shows "flabel_invar_2 (flabel(v2 := Some (r, Odd), v3 := Some (r, Even)))"
proof-
  have "{v1,v2} \<in> G - ex" "flabel v1 = Some (r, Even)" "{v2, v3} \<in> M" "flabel v2 = None"
    by (intro if1_props[OF ass])+

  have "v = v2" if "{v, v3} \<in> M" for v
    using matching that \<open>{v2,v3} \<in> M\<close>
    unfolding matching_def2
    apply (clarsimp simp add: doubleton_eq_iff Vs_def)
    by (smt doubleton_eq_iff insertI1)
  moreover have "v = v3" if "{v, v2} \<in> M" for v
    using matching that \<open>{v2,v3} \<in> M\<close>
    unfolding matching_def2
    apply (clarsimp simp add: doubleton_eq_iff Vs_def)
    by (smt doubleton_eq_iff insertI1)
  ultimately show ?thesis
    using invars
    unfolding flabel_invar_2_def
    apply safe
    subgoal 
      by (smt dblton_graph_def Pair_inject doubleton_eq_iff graph in_mono map_upd_Some_unfold 
              matching(2))
    subgoal 
      by (smt Pair_inject insert_commute map_upd_Some_unfold)
    done
qed


lemma flabel_par_invar_pres:
  assumes invars:"flabel_par_invar par flabel" and
    ass: "if1 flabel ex v1 v2 v3 r"
  shows "flabel_par_invar (par(v2 \<mapsto> v1, v3 \<mapsto> v2)) (flabel(v2 := Some (r, lab), v3 := Some (r, lab2)))" (is ?g1)
    "flabel_par_invar (par(v2 \<mapsto> v1)) (flabel(v2 := Some (r, lab)))" (is ?g2)
proof-

  have "{v1,v2} \<in> G - ex" "flabel v1 = Some (r, Even)" "{v2, v3} \<in> M" "flabel v2 = None"
    by (intro if1_props[OF ass])+

  show ?g1 ?g2
    using  invars
    unfolding flabel_par_invar_def
    by (auto simp add: \<open>flabel v1 = Some (r, Even)\<close>)
qed

lemma parent_spec_pres:
  assumes invars: "parent_spec par"
    "flabel_invar flabel"
    "flabel_par_invar par flabel" and
    ass: "if1 flabel ex v1 v2 v3 r"
  shows "parent_spec (par(v2 \<mapsto> v1, v3 \<mapsto> v2))" (is ?g1) "parent_spec (par(v2 := Some v1))" (is ?g2)
proof-
  have "{v1,v2} \<in> G - ex" "flabel v1 = Some (r, Even)" "{v2, v3} \<in> M" "flabel v2 = None"
    by (intro if1_props[OF ass])+
  have "flabel v3 = None"
    using invars(2) \<open>{v2, v3} \<in> M\<close> \<open>flabel v2 = None\<close>
    unfolding flabel_invar_def
    by auto

  have "par v2 = None" (is ?p1) "par v3 = None" (is ?p2)
    "\<forall>v. par v \<noteq> Some v2" (is ?p3) "\<forall>v. par v \<noteq> Some v3" (is ?p4)
  proof-
    show ?p1 ?p3
      using \<open>flabel v2 = None\<close> invars(3)
      unfolding flabel_par_invar_def
      by simp+
    show ?p2 ?p4
      using \<open>flabel v3 = None\<close> invars(3)
      unfolding flabel_par_invar_def
      by simp+
  qed
  moreover have "v1 \<noteq> v2" 
    using graph \<open>{v1,v2} \<in> G -ex\<close>
    by (fastforce elim: dblton_graphE)
  moreover have "v2 \<noteq> v3"
    using graph \<open>{v2,v3} \<in> M\<close> matching(2)
    by (fastforce elim: dblton_graphE)
  moreover have "v1 \<noteq> v3"
  proof-
    show ?thesis
      using \<open>flabel v1 = Some (r, Even)\<close> \<open>flabel v3 = None\<close>
      by auto
  qed
  ultimately show ?g1 ?g2
    by(auto intro: wf_par'[OF invars(1), of _ v2 v1 v3])
qed

lemma compute_alt_path_dom_if1:
  assumes "if1 flabel ex v1 v2 v3 r"
    "finite ex" "ex \<subseteq> G"
    "ex' = insert {v2, v3} (insert {v1, v2} ex)"
  shows "compute_alt_path_dom (ex', par', flabel')"
  unfolding assms(4)
  apply(rule compute_alt_path_dom)
  using if1_props[OF assms(1)] assms(2,3) matching(2)
  by auto

(*Done: Invar 1 and 2*)

fun alt_labels_invar where
  "alt_labels_invar flabel r [] = True"
| "alt_labels_invar flabel r [v] = (flabel v = Some (r, Even))"
| "alt_labels_invar flabel r (v1 # v2 # vs) = ((if (flabel v1 = Some (r, Even) \<and> flabel v2 = Some (r, Odd)) then
                                                {v1,v2} \<in> M
                                              else if (flabel v1 = Some (r, Odd) \<and> flabel v2 = Some (r, Even)) then
                                                {v1, v2} \<notin> M
                                              else undefined)
                                             \<and> alt_labels_invar flabel r (v2 #vs))"


(*Proof of Invar 1 and 2 from paper*)

lemma alt_invars_then_alt_path:
  assumes 
    "parent_spec par"
    "alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd)) (parent.follow par v)"
    "alt_labels_invar flabel r (parent.follow par v)"
  shows "alt_path (-M) (parent.follow par v)"
  using assms
proof(induction "(parent.follow par v)" arbitrary: v rule: induct_list012)
  case nil
  then show ?case
    by (simp add: alt_list_empty)
next
  case (single x)
  then have "x = v"
    using parent.follow_cons[OF parent.intro[OF assms(1)], where p = "[]" ]
    by simp
  then show ?case
    by (simp add: single(1)[symmetric] Nil alt_list_empty)
next
  case (sucsuc x y zs)
  then have "x = v"
    apply(intro parent.follow_cons[OF parent.intro[OF assms(1)], where p = "y # zs"])
    by simp
  then have "parent.follow par y = y # zs"
    apply(subst parent.follow_cons_2[OF parent.intro[OF assms(1)], of v y zs])
    using sucsuc(3)
    by simp+
  show ?case
  proof(cases zs)
    case Nil
    then show ?thesis
      using sucsuc(5,6)
      by (simp add: sucsuc(3)[symmetric] Nil alt_list_empty alt_list_step)
  next
    case (Cons z' zs')
    then have "parent.follow par z' = zs"
      using \<open>parent.follow par y = y # zs\<close> parent.follow_cons_2[OF parent.intro[OF assms(1)]]
      by blast
    moreover have "alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd)) (parent.follow par z')"
      "alt_labels_invar flabel r (parent.follow par z')"
      using sucsuc(5,6)
      by (simp add: alt_list_step sucsuc(3)[symmetric] \<open>parent.follow par y = y # zs\<close> Cons \<open>parent.follow par z' = zs\<close>)+
    ultimately have "alt_path (- M) (parent.follow par z')"
      apply(intro sucsuc(1) assms(1))
      by simp+
    moreover have "{x, y} \<in> M" "{y, z'} \<notin> M"
      using sucsuc(5,6) 
      by(simp add: sucsuc(3)[symmetric] alt_list_step Cons)+
    ultimately show ?thesis
      using \<open>parent.follow par z' = zs\<close>
      by(simp add: sucsuc(3)[symmetric] alt_list_step Cons)
  qed
qed

lemma alt_labels_invar_cong:
  "(\<forall>v\<in> set vs. flabel v = flabel2 v) \<Longrightarrow> alt_labels_invar flabel r vs = alt_labels_invar flabel2 r vs"
proof(induction vs)
  case Nil
  then show ?case
    by auto
next
  case (Cons a vs)
  then show ?case
    by(cases vs; auto)
qed

lemma v1_neq_v3:
  assumes "if1 flabel ex v1 v2 v3 r" "flabel_invar flabel" 
  shows "v1 \<noteq> v3"
proof-  
  have "flabel v3 = None"
    using assms(2) if1_props[OF assms(1)]
    unfolding flabel_invar_def
    by auto
  moreover have "flabel v1 \<noteq> None"
    using if1_props[OF assms(1)]
    by auto
  ultimately show ?thesis
    by metis
qed

end

context compute_alt_path
begin

lemma flabel_par_invar_props: 
  assumes "flabel_par_invar par flabel" "flabel v = None"
  shows "par v = None" "(\<forall>v'. par v' \<noteq> Some v)"
  using assms
  by(auto simp add: flabel_par_invar_def)

lemma ancestors_unaffected:
  assumes
    ass: "if1 flabel ex v1 v2 v3 r" and
    invars: "flabel_par_invar par flabel"
    "parent_spec par"
    "flabel_invar flabel" and
    neq: "v2 \<noteq> v" "v3 \<noteq> v"
  shows "par' = (par(v2 \<mapsto> v1, v3 \<mapsto> v2)) \<Longrightarrow> \<forall>v'\<in>set(parent.follow par v). par v' = par' v'" (is "?par' \<Longrightarrow> ?g1")
    "flabel' = (flabel(v2 \<mapsto> a, v3 \<mapsto> b)) \<Longrightarrow> \<forall>v'\<in>set(parent.follow par v). flabel v' = flabel' v'" (is "?flabel' \<Longrightarrow> ?g2")
proof-
  have "parent par"
    using invars(2)
    by (simp add: parent_def)
  moreover have "\<forall>v''. par v'' \<noteq> Some v2"
    by(intro flabel_par_invar_props[OF invars(1)] if1_props[OF ass])
  ultimately have "\<forall>v'\<in>set (parent.follow par v). v' \<noteq> v2"
    apply(intro v2_nin_ancestors neq) .
  then have *: "\<forall>v'\<in>set (parent.follow par v). par v' = (par(v2 \<mapsto> v1)) v'"
    apply(intro ancestors_unaffected_1[where ?v1.0 = v1 and ?v2.0 = v2] neq \<open>parent par\<close>)
    by blast+
  have "parent (par(v2 \<mapsto> v1))"
    unfolding parent_def
    by(intro parent_spec_pres(2)[OF invars(2,3,1) ass] \<open>parent par\<close>[unfolded parent_def])
  moreover  have "\<forall>v''. (par(v2 \<mapsto> v1)) v'' \<noteq> Some v3"
    using flabel_par_invar_props[OF invars(1)] if1_props[OF ass]
    by (metis flabel_invar_def invars(3) map_upd_Some_unfold option.distinct(1))
  ultimately have "\<forall>v'\<in>set (parent.follow (par(v2 \<mapsto> v1)) v). v' \<noteq> v3"
    apply(intro v2_nin_ancestors neq) .
  then have "\<forall>v'\<in>set (parent.follow (par(v2 \<mapsto> v1)) v). (par(v2 \<mapsto> v1)) v' = (par(v2 \<mapsto> v1, v3 \<mapsto> v2)) v'"
    apply(intro ancestors_unaffected_1[where ?par = "(par(v2 \<mapsto> v1))" and ?v1.0 = v2 and ?v2.0 = v3] neq \<open>parent (par(v2 \<mapsto> v1))\<close>)
    by blast+
  moreover have "v3 \<notin> set (parent.follow par v)"
    using parent.nin_ancestors
    by (metis "*" \<open>\<forall>v''. (par(v2 \<mapsto> v1)) v'' \<noteq> Some v3\<close> \<open>parent par\<close> neq(2))
  ultimately show "?par' \<Longrightarrow> ?g1"
    by (simp add: "*")
  have *: "\<forall>v'\<in>set (parent.follow par v). flabel v' = (flabel(v2 \<mapsto> a)) v'"
    apply(intro ancestors_unaffected_1[where ?v1.0 = a and ?v2.0 = v2] neq \<open>parent par\<close> \<open>\<forall>v'\<in>set (parent.follow par v). v' \<noteq> v2\<close>)
    by blast+
  moreover have "\<forall>v'\<in>set (parent.follow (par(v2 \<mapsto> v1)) v). (flabel(v2 \<mapsto> a)) v' = (flabel(v2 \<mapsto> a, v3 \<mapsto> b)) v'"
    apply(intro ancestors_unaffected_1[where ?par = "(par(v2 \<mapsto> v1))" and ?v1.0 = b and ?v2.0 = v3] neq \<open>parent (par(v2 \<mapsto> v1))\<close>
        \<open>\<forall>v'\<in>set (parent.follow (par(v2 \<mapsto> v1)) v). v' \<noteq> v3\<close>)
    by blast+
  ultimately show "?flabel' \<Longrightarrow> ?g2"
    using \<open>v3 \<notin> set (parent.follow par v)\<close>
    by (simp add: "*")
qed

lemma v1_neq_v2_neq_v3: assumes "if1 flabel ex v1 v2 v3 r" shows "v1 \<noteq> v2" "v2 \<noteq> v3"
  using if1_props[OF assms]
  using \<open>{v2, v3} \<in> M\<close> graph matching(2)
  by (fastforce elim: dblton_graphE)+

lemma alt_labels_invar_pres:
  assumes  ass: "if1 flabel ex v1 v2 v3 r" and
    invars: "\<And>v r lab. flabel v = Some (r, lab) \<Longrightarrow> alt_labels_invar flabel r (parent.follow par v)"
    "\<And>v r. flabel v = Some (r, Even) \<Longrightarrow> alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd)) (parent.follow par v)"
    "parent_spec par"
    "flabel_invar flabel" 
    "flabel_par_invar par flabel" and
    inG: "\<exists>lab. flabel' v = Some (r', lab)" and
    flabel': "flabel' = (flabel(v2 \<mapsto> (r, Odd), v3 \<mapsto> (r, Even)))" and
    par': "par' = (par(v2 \<mapsto> v1, v3 \<mapsto> v2))"
  shows "alt_labels_invar flabel' r' (parent.follow par' v)"
  using assms
proof(induction flabel' r' "parent.follow par' v" arbitrary: v rule: alt_labels_invar.induct)
  case (1 flabel' r')
  then show ?case
    by auto
next
  case (2 flabel' r' v')
  have **:"parent par" "parent par'"
    unfolding parent_def par'
    by(intro invars(3) parent_spec_pres[OF invars(3-5) 2(2)])+
  have "v1 \<noteq> v2"  "v2 \<noteq> v3"
    by(rule v1_neq_v2_neq_v3[OF 2(2)])+
  have "v1 \<noteq> v3"
    using v1_neq_v3[OF 2(2,6)]
    .
  have "v' = v"
    using 2(1)[symmetric]
    apply(intro parent.follow_cons[OF **(2), where p = "[]"])
    by simp
  have "par' v = None"
    using parent.follow_None[OF **(2) 2(1)[symmetric]]
    by simp
  then have "par v = None"
    by (auto simp add: par' split: if_splits)
  moreover have "alt_labels_invar flabel r' (parent.follow par v)"
  proof(cases "v = v1")
    case True
    then show ?thesis
      using 2(3,8,9) \<open>v1 \<noteq> v2\<close> \<open>v1 \<noteq> v3\<close>
      by auto
  next
    case F1: False
    show ?thesis
    proof(cases "v = v2")
      have "par' v2 = Some v1"
        using \<open>v2 \<noteq> v3\<close>
        by(simp add: 2(10))
      moreover case True
      ultimately have False        
        using \<open>par' v = None\<close>
        by simp
      then show ?thesis
        by simp
    next
      case F2: False
      then show ?thesis
      proof(cases "v = v3")
        have "par' v3 = Some v2"
          using \<open>v2 \<noteq> v3\<close>
          by(simp add: 2(10))
        moreover case True
        ultimately have False        
          using \<open>par' v = None\<close>
          by simp
        then show ?thesis
          by simp
      next
        case False
        then have "flabel v \<noteq> None"
          using F1 F2 2(8,9)
          by (auto split: if_splits)
        then show ?thesis
          using "2.prems"(8) "2.prems"(2) "2.prems"(7) F2 False by auto
      qed
    qed
  qed
  ultimately have "flabel v = Some (r', Even)"
    by (auto simp add: parent.follow_psimps[OF **(1)] 2(1)[symmetric] split: option.splits)
  moreover have "v \<noteq> v2"
    using if1_props[OF 2(2)] \<open>flabel v = Some (r', Even)\<close>
    by auto
  moreover have "v \<noteq> v3"
    using \<open>par' v = None\<close> 
    by(auto simp add: par')
  ultimately have "flabel' v \<noteq> None"
    unfolding 2(9)
    by (auto split: if_splits)
  then show ?case
    using \<open>par' v = None\<close>
    by (auto simp add: parent.follow_psimps[OF **(2)] 2(1)[symmetric] "2.prems"(8)
                       \<open>flabel v = Some (r', Even)\<close> \<open>v \<noteq> v2\<close> \<open>v \<noteq> v3\<close>)
next
  case (3 flabel' r' v1' v2' vs)
  have **:"parent par" "parent par'"
    unfolding parent_def par'
    using 3(3-10)
    by (intro invars(3) parent_spec_pres)+
  have "v1' = v"
    using 3(2)[symmetric] parent.follow_cons[OF **(2)]
    by simp
  have "{v2,v3} \<in> M"
    using if1_props(4)[OF 3(3)]
    .
  have "{v} \<notin> M" for v
    using matching(2) graph
    by (blast elim: dblton_graphE)
  have "par' v3 = Some v2"
    by (simp add: par')
  moreover have "par' v1' = Some v2'"
    using 3(2)[symmetric] parent.follow_cons_2(2)[OF **(2)] parent.follow_cons[OF **(2)]
    by metis
  ultimately have "v1' = v3 \<longrightarrow> v2' = v2"
    by auto
  moreover  have "v1' = v2 \<Longrightarrow> v2' \<noteq> v3"
    by (metis (no_types, lifting) "**"(2) "3.hyps"(2) \<open>v1' = v\<close> assms(1) invars(4) map_upd_Some_unfold not_Cons_self2 par' parent.follow_cons_2(1) parent.follow_cons_2(2) v1_neq_v3)
  ultimately have "v2' \<noteq> v3"
    by (metis \<open>par' v1' = Some v2'\<close> \<open>{v2, v3} \<in> M\<close> ass flabel_invar_def flabel_par_invar_props(2) fun_upd_apply if1_props(3) invars(4) invars(5) par')
  moreover have "v3 \<noteq> v2"
    using \<open>\<And>v. {v} \<notin> M\<close> \<open>{v2, v3} \<in> M\<close> by auto
  moreover have "\<forall>v'. par v' \<noteq> Some v2"
    using flabel_par_invar_props(2)[OF invars(5) if1_props(3)[OF assms(1)]].
  ultimately consider (c1) "v1' = v3 \<and> v2' = v2" | (c2) "v1' = v2 \<and> v2' = v1" | (c3) "{v1', v2'} \<inter> {v2, v3} = {}"
    using \<open>par' v1' = Some v2'\<close> 
    apply (cases "v1' = v2"; clarsimp)
    by (fastforce simp: par')+
  then show ?case
  proof(cases )
    case c1
    then show ?thesis
      apply(simp add: par' \<open> flabel' = flabel(v2 \<mapsto> (r, Odd), v3 \<mapsto> (r, Even))\<close>)
      by (smt "**"(2) "3.hyps"(1) "3.hyps"(2) "3.prems"(7) "3.prems"(8) Pair_inject \<open>v1' = v\<close>
              \<open>{v2, v3} \<in> M\<close> alt_labels_invar.simps(3) ass insert_commute invars(1) invars(2)
              invars(3) invars(4) invars(5) map_upd_Some_unfold par' parent.follow_cons_2(1))
  next
    have aa: "{v2, vx} \<in> M \<Longrightarrow> vx = v3" for vx
      using doubleton_in_matching[OF matching(1)] \<open>{v2, v3} \<in> M\<close>
      by blast
    case c2
    then show ?thesis
      by (smt "**"(2) "3.hyps"(1) "3.hyps"(2) "3.prems"(7) "3.prems"(8) Pair_inject
              \<open>v1' = v\<close> \<open>v2' \<noteq> v3\<close> \<open>v3 \<noteq> v2\<close> aa alt_labels_invar.simps(3) ass
              compute_alt_path.if1_props(2) compute_alt_path_axioms invars(1) invars(2) invars(3)
              invars(4) invars(5) label.distinct(1) map_upd_Some_unfold par' parent.follow_cons_2(1))
  next
    case c3
    then have " parent.follow par v1' = parent.follow par' v1'"
      apply(intro  ancestors_unaffected(1)[OF 3(3,8,6,7) _ _ par'] follow_cong[OF \<open>parent par\<close> _ _ \<open>parent par'\<close>])
      by (auto simp add: "**"(1) parent.follow_dom)
    then have follow_eq_follow': " parent.follow par v = parent.follow par' v"
      unfolding \<open>v1' = v\<close>
      .
    have "alt_labels_invar flabel r' (parent.follow par v1') = alt_labels_invar flabel' r' (parent.follow par v1')"
      apply(intro alt_labels_invar_cong[OF] ancestors_unaffected(2)[OF 3(3,8,6,7) _ _ 3(10)])
      using c3
      by (auto simp add: "**"(1) parent.follow_dom)
    then have "alt_labels_invar flabel r' (parent.follow par v) = alt_labels_invar flabel' r' (parent.follow par v)"
      unfolding \<open>v1' = v\<close>
      .
    moreover have "alt_labels_invar flabel r' (parent.follow par v1')"
    proof-
      obtain lab where "flabel' v = Some (r', lab)"
        using 3
        by auto
      then have "flabel v = Some (r', lab)"
        using c3 \<open>v1' = v\<close>
        by (auto simp add: 3(10) split: if_splits)
      then show ?thesis
        apply(intro 3(4))
        using \<open>v1' = v\<close>
        by simp
    qed
    ultimately show ?thesis
      unfolding \<open>v1' = v\<close>
      by (simp add: follow_eq_follow')
  qed
qed

lemma alt_list_pres:
  assumes  ass: "if1 flabel ex v1 v2 v3 r" and
    invars: "\<And>v r. flabel v = Some (r, Even) \<Longrightarrow> alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd)) (parent.follow par v)"
    "parent_spec par"
    "flabel_invar flabel" 
    "flabel_par_invar par flabel" and
    inG: "flabel' v = Some (r', Even)" and
    flabel': "flabel' = (flabel(v2 \<mapsto> (r, Odd), v3 \<mapsto> (r, Even)))" and
    par': "par' = (par(v2 \<mapsto> v1, v3 \<mapsto> v2))"
  shows "alt_list (\<lambda>v. flabel' v = Some (r', Even)) (\<lambda>v. flabel' v = Some (r', Odd)) (parent.follow par' v)"
  using assms
proof(induction "(parent.follow par' v)" arbitrary: v rule: induct_list012)
  case nil
  then show ?case
    by (simp add: alt_list_empty)
next
  case (single x)
  then show ?case
    by (metis (mono_tags, lifting) alt_list.simps compute_alt_path.parent_spec_pres(1) compute_alt_path_axioms par' parent.follow_cons parent.intro)
next
  case (sucsuc x y zs)
  have **:"parent par" "parent par'"
    unfolding parent_def par'
    using sucsuc
    by (intro invars parent_spec_pres)+
  have "x = v"
    using sucsuc(3)[symmetric] parent.follow_cons[OF **(2)]
    by simp
  have "{v2,v3} \<in> M"
    using if1_props(4)[OF sucsuc(4)]
    .
  have "{v} \<notin> M" for v
    using matching(2) graph
    by (blast elim: dblton_graphE)
  have "par' v3 = Some v2"
    by (simp add: par')
  moreover have "par' x = Some y"
    using sucsuc(3)[symmetric] parent.follow_cons_2(2)[OF **(2)] parent.follow_cons[OF **(2)]
    by metis
  ultimately have "x = v3 \<longrightarrow> y = v2"
    by auto
  moreover  have "x = v2 \<Longrightarrow> y \<noteq> v3"
    by (metis (no_types, lifting) "**"(2) "sucsuc.hyps"(3) \<open>x = v\<close> assms(1) assms(2) invars(3) map_upd_Some_unfold not_Cons_self2 par' parent.follow_cons_2(1) parent.follow_cons_2(2) v1_neq_v3)
  ultimately have "y \<noteq> v3"
    by (metis \<open>par' x = Some y\<close> \<open>{v2, v3} \<in> M\<close> ass flabel_invar_def flabel_par_invar_props(2) fun_upd_other if1_props(3) invars(3) invars(4) par')
  moreover have "v3 \<noteq> v2"
    using \<open>\<And>v. {v} \<notin> M\<close> \<open>{v2, v3} \<in> M\<close> by auto
  moreover have "\<forall>v'. par v' \<noteq> Some v2"
    using flabel_par_invar_props(2)[OF invars(4) if1_props(3)[OF assms(1)]] .
  ultimately consider (c1) "x = v3 \<and> y = v2" | (c2) "x = v2 \<and> y = v1" | (c3) "{x, y} \<inter> {v2, v3} = {}"
    using \<open>par' x = Some y\<close> 
    apply (cases "x = v2"; clarsimp)
    by (fastforce simp: par')+
  then show ?case
  proof cases
    case c1
    then show ?thesis
      apply(cases zs)
      subgoal by (metis "**"(2) "sucsuc.hyps"(3) \<open>x = v\<close> fun_upd_def option.simps(3) par' parent.follow_None parent.follow_cons_2(1))
      subgoal by (smt (z3) "**"(2) Pair_inject \<open>x = v\<close> alt_list_step ass compute_alt_path.if1_props(2) compute_alt_path_axioms flabel' map_upd_Some_unfold not_Cons_self2 par' parent.follow_cons_2(1) parent.follow_cons_2(2) sucsuc.hyps(1) sucsuc.hyps(3) sucsuc.prems(2) sucsuc.prems(3) sucsuc.prems(4) sucsuc.prems(5) sucsuc.prems(6))
      done
  next
    case c2
    then show ?thesis
      using "sucsuc.prems"(6) \<open>v3 \<noteq> v2\<close> \<open>x = v\<close> flabel' by auto
  next
    case c3
    case c3
    then have " parent.follow par x = parent.follow par' x"
      apply(intro  ancestors_unaffected(1)[OF sucsuc(4,8,6,7) _ _ par'] follow_cong[OF \<open>parent par\<close> _ _ \<open>parent par'\<close>])
      by (auto simp add: "**"(1) parent.follow_dom)
    then have follow_eq_follow': " parent.follow par v = parent.follow par' v"
      unfolding \<open>x = v\<close>
      .
    have "\<forall>v'\<in>set (parent.follow par x). flabel v' = flabel' v'"
      apply(rule ancestors_unaffected(2)[OF sucsuc(4,8,6,7) _ _ flabel'])
      using c3 
      by (auto simp add: "**"(1) parent.follow_dom)
    then have "\<forall>v'\<in>set (parent.follow par v). flabel v' = flabel' v'"
      unfolding \<open>x = v\<close> .
    then have "alt_list (\<lambda>v. flabel' v = Some (r', Even)) (\<lambda>v. flabel' v = Some (r', Odd)) (parent.follow par v) =
           alt_list (\<lambda>v. flabel v = Some (r', Even)) (\<lambda>v. flabel v = Some (r', Odd)) (parent.follow par v)"
      apply(intro alt_list_cong_eq[OF] )
      by simp+
    moreover have "alt_list (\<lambda>v. flabel v = Some (r', Even)) (\<lambda>v. flabel v = Some (r', Odd)) (parent.follow par x)"
    proof-
      have "flabel' v = Some (r', Even)"
        using sucsuc
        by auto
      then have "flabel v = Some (r', Even)"
        using c3 \<open>x = v\<close>
        by (auto simp add: sucsuc(10) split: if_splits)
      then show ?thesis
        apply(intro sucsuc(5))
        using \<open>x = v\<close>
        by simp
    qed
    ultimately show ?thesis
      unfolding \<open>x = v\<close>
      by (simp add: follow_eq_follow')
  qed
qed

(*Done: Invar 6*)

definition "last_not_matched_invar par flabel =
   (\<forall>v. (flabel v \<noteq> None \<longrightarrow> (last (parent.follow par v) \<notin> Vs M)))"

end

context parent
begin

lemma follow_cons_3: "\<exists>l. follow v = v # l"
  by (metis follow_cons follow_nempty list.exhaust)

lemma follow_cons_3': obtains l where "follow v = v # l"
  by (metis follow_cons follow_nempty list.exhaust)

lemma follow_cons_4: "parent v = Some v' \<Longrightarrow> follow v = v # (follow v')"
  using follow_psimps
  by auto

lemma follow_pinduct:
  "(\<And>v. (\<And>x2. parent v = Some x2 \<Longrightarrow> P x2) \<Longrightarrow> P v) \<Longrightarrow> P a"
  by (metis follow.pinduct[OF follow_dom])

end

lemma last_follow_eq:
  assumes invar: "parent_spec par" "parent_spec (par (v \<mapsto> v''))"  and 
    neq: "\<forall>v'. par v' \<noteq> Some v" "v'' \<noteq> v" "v' \<noteq> v"
  shows "last (parent.follow (par (v \<mapsto> v'')) v') = last (parent.follow par v')"
  using assms 
proof(induction v' rule: parent.follow_pinduct[OF parent.intro[OF invar(1)]])
  case (1 v')
  then have "parent par" "parent (par (v \<mapsto> v''))"
    unfolding parent_def
    by(intro 1)+
  then have "parent.follow_dom (par (v \<mapsto> v'')) v'"
    by (simp add: parent.follow_dom)
  note follow_simps [simp] = parent.follow.psimps[OF \<open>parent (par(v \<mapsto> v''))\<close> parent.follow_dom[OF \<open>parent (par(v \<mapsto> v''))\<close>], of v']
    parent.follow.psimps[OF \<open>parent par\<close> parent.follow_dom[OF \<open>parent par\<close>], of v']
  have *: "(par (v \<mapsto> v'')) v' = par v'"
    using 1
    by (auto split: if_splits)
  show ?case
  proof(cases "par v'")
    case None
    then show ?thesis
      apply (simp only: follow_simps * split: if_splits option.splits)
      by simp
  next
    case (Some a)
    then have "(par(v \<mapsto> v'')) v' = Some a"
      unfolding "*"
      .
    have "last (parent.follow (par(v \<mapsto> v'')) a) = last (parent.follow par a)"
      apply(intro 1)
      using Some 1(4)
      by (auto simp add: \<open>parent par\<close> parent.follow_dom)
    moreover have "last (parent.follow (par(v \<mapsto> v'')) v') = last (parent.follow (par(v \<mapsto> v'')) a)"
      unfolding parent.follow_cons_4[OF \<open>parent (par(v \<mapsto> v''))\<close> \<open>(par(v \<mapsto> v'')) v' = Some a\<close>]
      using last_ConsR[OF parent.follow_nempty[OF \<open>parent (par(v \<mapsto> v''))\<close>]]
      .
    moreover have "last (parent.follow par v') = last (parent.follow par a)"
      unfolding parent.follow_cons_4[OF \<open>parent par\<close> Some]
      using last_ConsR[OF parent.follow_nempty[OF \<open>parent par\<close>]]
      .
    ultimately show ?thesis
      by metis
  qed
qed

lemma follow_eq:
  assumes invar: "parent_spec par" "parent_spec (par (v \<mapsto> v''))" and
    neq: "\<forall>v'. par v' \<noteq> Some v" "v'' \<noteq> v"
  shows "parent.follow par v'' = parent.follow (par(v \<mapsto> v'')) v''"
  apply(rule follow_cong )
  subgoal using parent.intro[OF invar(1)].
  subgoal using parent.follow_dom[OF parent.intro[OF invar(1)]]. 
  subgoal apply(rule no_children_not_in_follow[where ?v2.0 = v and ?v1.0 = v''])
    subgoal using parent.intro[OF invar(1)] .
    subgoal using neq by auto
    subgoal using neq(2) by simp
    subgoal by blast
    done
  subgoal using parent.intro[OF invar(2)] .
  done

context compute_alt_path
begin

lemma compute_alt_path_follow_eq:
  assumes ass: "if1 flabel ex v1 v2 v3 r" and
    invars: "parent_spec par"
    "flabel_invar flabel"
    "flabel_par_invar par flabel" and
    neq: "v2 \<noteq> v" "v3 \<noteq> v"
  shows "parent.follow par v = parent.follow (par(v2 \<mapsto> v1, v3 \<mapsto> v2)) v"
    (*Can use follow_eq to prove it?*)
  apply(intro follow_cong)
  subgoal using parent.intro[OF invars(1)] .
  subgoal using parent.follow_dom[OF parent.intro[OF invars(1)]] .
  subgoal apply(intro ancestors_unaffected(1)[OF ass invars(3,1,2)])
    using neq by auto
  subgoal using parent.intro[OF parent_spec_pres(1)[OF invars ass]] .
  done

end

lemma last_follow_eq_2:
  assumes invar: "parent_spec par" "parent_spec (par (v \<mapsto> v''))" and
    neq: "\<forall>v'. par v' \<noteq> Some v" "v'' \<noteq> v"
  shows "last (parent.follow (par (v \<mapsto> v'')) v) = last (parent.follow par v'')"
proof(cases "par v''")
  note follow_simps [simp] = parent.follow_psimps[OF parent.intro[OF invar(1)]]
    parent.follow_psimps[OF parent.intro[OF invar(2)]]
  case None
  then show ?thesis
    using neq
    by auto
next
  note follow_simps [simp] = parent.follow_psimps[OF parent.intro[OF invar(1)], of v]
    parent.follow_psimps[OF parent.intro[OF invar(2)], of v]
  case (Some a)
  then show ?thesis
    using parent.follow_nempty[OF parent.intro[OF invar(2)], where v = v'']
    using follow_eq[OF invar neq]
    by simp
qed

context compute_alt_path
begin

lemma flabel_invar_props: "flabel_invar flabel \<Longrightarrow> {v1, v2} \<in> M \<Longrightarrow> (flabel v1 = None) \<Longrightarrow> (flabel v2 = None)"
  "flabel_invar flabel \<Longrightarrow> {v1, v2} \<in> M \<Longrightarrow> (flabel v1 \<noteq> None) \<Longrightarrow> (flabel v2 \<noteq> None)"
  unfolding flabel_invar_def
  by simp+

lemma compute_alt_path_last_eq:
  assumes ass: "if1 flabel ex v1 v2 v3 r" and
    invars: "parent_spec par"
    "flabel_invar flabel"
    "flabel_par_invar par flabel"
  shows  "last (parent.follow (par(v2 \<mapsto> v1)) v2) = last (parent.follow par v1)" (is ?g1)
    "\<And>v. v \<noteq> v2 \<Longrightarrow> last (parent.follow (par(v2 \<mapsto> v1)) v) = last (parent.follow par v)" (is "\<And>v. ?p v \<Longrightarrow> ?g2 v") 
    "last (parent.follow (par(v2 \<mapsto> v1, v3 \<mapsto> v2)) v3) = last (parent.follow (par(v2 \<mapsto> v1)) v2)" (is ?g3)
    "\<And>v. v \<noteq> v3 \<Longrightarrow> last (parent.follow (par(v2 \<mapsto> v1, v3 \<mapsto> v2)) v) = last (parent.follow (par(v2 \<mapsto> v1)) v)" (is "\<And>v. ?p2 v \<Longrightarrow> ?g4 v")
proof-
  have parent_spec: "parent_spec (par(v2 \<mapsto> v1))"
    using parent_spec_pres(2)[OF invars(1-3) ass]
    .
  moreover have "\<forall>v'. par v' \<noteq> Some v2"
    by(intro if1_props[OF ass] flabel_par_invar_props(2)[OF invars(3)])
  moreover have "v1 \<noteq> v2"
    by(intro v1_neq_v2_neq_v3[OF ass])
  ultimately show ?g1 "\<And>v. ?p v \<Longrightarrow> ?g2 v"
    by(intro last_follow_eq[OF invars(1) parent_spec] last_follow_eq_2[OF invars(1) parent_spec]; simp)+
  have "parent_spec (par(v2 \<mapsto> v1))" "parent_spec (par(v2 \<mapsto> v1, v3 \<mapsto> v2))"
    by (intro parent_spec_pres[OF invars(1-3) ass])+
  moreover have "v2 \<noteq> v3"
    by(intro v1_neq_v2_neq_v3[OF ass])
  moreover have  "\<forall>v'. (par(v2 \<mapsto> v1)) v' \<noteq> Some v3"
    using \<open>v2 \<noteq> v3\<close>
    by (metis ass compute_alt_path.if1_props(3) compute_alt_path.if1_props(4) compute_alt_path_axioms flabel_invar_def flabel_par_invar_props(2) fun_upd_apply invars(2) invars(3) option.inject v1_neq_v3)
  ultimately
  show ?g3 "\<And>v. ?p2 v \<Longrightarrow> ?g4 v"
    by(intro last_follow_eq[OF _ ] last_follow_eq_2[OF _ ]; simp)+
qed

lemma last_not_matched_invar_pres:
  assumes 
    ass: "if1 flabel ex v1 v2 v3 r" and
    invars: 
    "parent_spec par"
    "flabel_invar flabel"
    "flabel_par_invar par flabel"
    "last_not_matched_invar par flabel"                
  shows "last_not_matched_invar (par(v2 \<mapsto> v1)) (flabel(v2 \<mapsto> (r, lab)))" (is ?g1)
    "last_not_matched_invar (par(v2 \<mapsto> v1, v3 \<mapsto> v2)) (flabel(v2 \<mapsto> (r, lab), v3 \<mapsto> (r2, lab2)))" (is ?g2)
proof-
  {
    fix v2 v1 v3 r lab and par :: "'a \<Rightarrow> 'a option" and flabel::"'a \<Rightarrow> ('b \<times> label) option"
    assume *: "last (parent.follow (par(v2 \<mapsto> v1)) v2) = last (parent.follow par v1)"
      "last (parent.follow (par(v2 \<mapsto> v1)) v) = last (parent.follow par v)" if  "v \<noteq> v2" for v
    assume invar: "last_not_matched_invar par flabel" "flabel_par_invar par flabel"  and
      ass: "flabel v1 \<noteq> None"
    have "last (parent.follow (par(v2 \<mapsto> v1)) v) \<notin> Vs M" if "(flabel(v2 \<mapsto> (r, lab))) v \<noteq> None" for v
    proof(cases "v = v2")
      case True
      have "last (parent.follow par v1) \<notin> Vs M"
        using invar(1) ass
        by (auto simp: last_not_matched_invar_def)
      then have "last (parent.follow (par(v2 \<mapsto> v1)) v1) \<notin> Vs M"
        by (metis "*"(1) "*"(2))
      then have "last (parent.follow (par(v2 \<mapsto> v1)) v2) \<notin> Vs M"
        by (metis "*"(1) "*"(2))
      then show ?thesis
        using True by simp
    next
      case False
      then show ?thesis
        using *(2)
        using invar that
        by (fastforce simp: last_not_matched_invar_def flabel_par_invar_def)
    qed
    then have "last_not_matched_invar (par(v2 \<mapsto> v1)) (flabel(v2 := Some (r, lab)))"
      unfolding last_not_matched_invar_def
      by(intro conjI allI impI)
        (*moreover have " v \<notin> Vs M" if "(par(v2 \<mapsto> v1)) v = None" for v
      using invar(1)
      unfolding last_not_matched_invar_def
      using that
      by (clarsimp split: if_splits)
    ultimately have "last_not_matched_invar (par(v2 \<mapsto> v1)) (flabel(v2 := Some (r, lab)))"
      unfolding last_not_matched_invar_def
      by(intro conjI allI impI)*)
  } note gen = this
  have "flabel v1 \<noteq> None" using if1_props(2)[OF ass]
    by auto
  then show g1: ?g1
    by(intro gen[OF compute_alt_path_last_eq(1,2)[OF ass invars(1-3)] invars(4,3)])
  have "(flabel(v2 \<mapsto> (r, lab))) v2 \<noteq> None"
    by auto
  moreover have "flabel_par_invar (par(v2 \<mapsto> v1)) (flabel(v2 \<mapsto> (r, lab)))"
    using flabel_par_invar_pres(2)[OF invars(3) ass] .
  ultimately show ?g2
    apply(intro gen[OF compute_alt_path_last_eq(3,4)[OF ass invars(1-3)] g1]) 
    by auto
qed

lemma last_not_matched_invar_props: 
  assumes "last_not_matched_invar par flabel"
  shows  "(flabel v = Some a \<Longrightarrow> last (parent.follow par v) \<notin> Vs M)"
  using assms
  unfolding last_not_matched_invar_def
  by simp+

(*Done: Invar 8*)

definition "matching_examined_invar flabel ex = (\<forall>v1 v2. {v1, v2} \<in> M \<longrightarrow> flabel v1 \<noteq> None \<longrightarrow> {v1, v2} \<in> ex)"

lemma matching_examined_invar_props: 
  "matching_examined_invar flabel ex \<Longrightarrow> {v1, v2} \<in> M \<Longrightarrow> flabel v1 = Some (r, lab) \<Longrightarrow> {v1, v2} \<in> ex"
  unfolding matching_examined_invar_def
  by simp

lemma matching_examined_invar_pres:
  assumes 
    invars: 
    "flabel_invar flabel"
    "matching_examined_invar flabel ex" and
    ass: "if1 flabel ex v1 v2 v3 r"
  shows "matching_examined_invar (flabel(v2 \<mapsto> (r, lab), v3 \<mapsto> (r', lab'))) (insert {v2, v3} (insert {v1, v2} ex))" (is ?g1)
proof-
  {
    fix v1' v2'
    have "flabel_invar (flabel(v2 \<mapsto> (r, lab), v3 \<mapsto> (r', lab')))"
      using flabel_invar_pres[OF invars(1) ass]
      .
    assume ass2: "{v1', v2'} \<in> M" "(flabel(v2 \<mapsto> (r, lab), v3 \<mapsto> (r', lab'))) v1' \<noteq> None"
    moreover have "(flabel(v2 \<mapsto> (r, lab), v3 \<mapsto> (r', lab'))) v2' \<noteq> None"
      apply(rule flabel_invar_props[OF flabel_invar_pres[OF invars(1) ass], of v1'])
      using ass2
      by auto
    moreover have "{v1, v2} \<notin> M"
      using matching_examined_invar_props[OF invars(2)]
        if1_props[OF ass]
      by fastforce
    moreover have "v1' \<noteq> v2'"
      using matching(2) graph \<open>{v1', v2'} \<in> M\<close>
      apply clarsimp
      by (blast elim: dblton_graphE)
    moreover have "v1 \<noteq> v2"
      using graph if1_props(1)[OF ass(1)]
      apply clarsimp
      by  (blast elim: dblton_graphE)
    moreover have "v1 \<noteq> v3"
      using v1_neq_v3[OF ass invars(1)].
    ultimately have "{v1', v2'} \<in> insert {v2, v3} (insert {v1, v2} ex)"
      apply (clarsimp split: if_splits simp add: matching_examined_invar_props[OF invars(2)] insert_commute doubleton_eq_iff)
      subgoal using matching_examined_invar_props[OF invars(2)] insert_commute by metis
      done
  }
  then show ?thesis
    unfolding matching_examined_invar_def
    by simp
qed

lemma matching_examined_invar_imp:
  assumes ass: "if1 flabel ex v1 v2 v3 r" and
    invar: "matching_examined_invar flabel ex"
  shows "{v1, v2} \<notin> M"
  using if1_props[OF ass] matching_examined_invar_props[OF invar]
  by blast

end

lemma alt_list_length_odd:
  assumes invar: "alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd)) vs" and 
    "flabel (hd vs) = Some (r, Even)"
    "flabel (last vs) = Some (r, Even)"
    "vs \<noteq> []"
  shows "odd (length vs)"
  using assms
proof(induction vs rule: induct_list012)
  case nil
  then show ?case
    by auto
next
  case (single x)
  then show ?case
    by auto
next
  case (sucsuc x y zs)
  then show ?case
  proof(cases zs)
    case Nil
    then show ?thesis
      using sucsuc
      by (auto simp add: alt_list_step)
  next
    case (Cons z zs')
    moreover have "alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd)) zs" "flabel (hd zs) = Some (r, Even)"
      using sucsuc(3)
      by (auto simp add: alt_list_step Cons)
    moreover have "flabel (last zs) = Some (r, Even)"
    proof-
      have "last zs = last (x # y # zs)"
        using Cons
        by auto
      then show ?thesis
        using sucsuc(5)
        by simp
    qed
    ultimately have "odd (length zs)"
      apply(intro sucsuc(1))
      by simp+
    then show ?thesis
      by simp
  qed
qed

context compute_alt_path
begin

(*Done: Invar 7*)

definition "last_even_invar par flabel = (\<forall>v r lab. flabel v = Some(r, lab) \<longrightarrow> flabel (last (parent.follow par v)) = Some (r, Even))"

lemma last_even_invar_props:
  "last_even_invar par flabel \<Longrightarrow> flabel v = Some (r, lab) \<Longrightarrow> flabel (last (parent.follow par v)) = Some (r, Even)"
  unfolding last_even_invar_def
  by auto

lemma last_even_invar_pres:
  assumes  invars: 
    "parent_spec par"
    "flabel_invar flabel"
    "flabel_par_invar par flabel"
    "last_even_invar par flabel" and
    ass: "if1 flabel ex v1 v2 v3 r"
  shows "last_even_invar (par(v2 \<mapsto> v1, v3 \<mapsto> v2)) (flabel(v2 \<mapsto> (r, lab), v3 \<mapsto> (r, lab')))"
proof-
  define par' where "par' = (par(v2 \<mapsto> v1, v3 \<mapsto> v2))"
  define flabel' where "flabel' = (flabel(v2 \<mapsto> (r, lab), v3 \<mapsto> (r, lab')))"
  have "parent par'"
    unfolding par'_def
    using parent.intro[OF parent_spec_pres(1)[OF invars(1-3) ass]]
    .
  note follow_simps [simp] = parent.follow.psimps[OF \<open>parent par'\<close> parent.follow_dom[OF \<open>parent par'\<close>]]
  {
    fix v r lab
    assume "v2 \<noteq> v" "v3 \<noteq> v"
      "flabel' v = Some (r, lab)" 
    then have "flabel v = Some (r, lab)"
      by (auto simp: flabel'_def)
    then have i: "flabel (last (parent.follow par v)) = Some (r, Even)"
      apply (intro last_even_invar_props[OF invars(4), of _ r lab])
      .
    have "flabel (last (parent.follow par v)) = Some (r, Even)"
      using i
      by simp
    moreover have "\<forall>v'\<in>set (parent.follow par v). v' \<noteq> v2"
      by(intro v2_nin_ancestors[OF parent.intro[OF invars(1)] flabel_par_invar_props(2)[OF invars(3)]] if1_props[OF ass] \<open>v2 \<noteq> v\<close>)
    moreover have "\<forall>v'\<in>set (parent.follow par v). v' \<noteq> v3"
      by(intro v2_nin_ancestors[OF parent.intro[OF invars(1)] flabel_par_invar_props(2)[OF invars(3)]] flabel_invar_props(1)[OF invars(2) if1_props(4,3)[OF ass]] \<open>v3 \<noteq> v\<close> )
    moreover have "(last (parent.follow par v)) \<in> set (parent.follow par v)"
      using parent.follow_nempty[OF parent.intro[OF invars(1)]]
      by simp
    ultimately have "flabel' (last (parent.follow par v)) = Some (r, Even)"
      unfolding flabel'_def
      by simp
    moreover have "parent.follow par v =  parent.follow par' v"
      unfolding par'_def
      using compute_alt_path_follow_eq[OF ass invars(1,2,3) \<open>v2 \<noteq> v\<close> \<open>v3 \<noteq> v\<close>]
      .
    ultimately have "flabel' (last (parent.follow par' v)) = Some (r, Even)"
      by simp
  }
  moreover have *: "(last (parent.follow par' v2)) = (last (parent.follow par' v1))"
  proof-
    have "par' v2 = Some v1"
      unfolding par'_def
      using v1_neq_v2_neq_v3(2)[OF ass]
      by simp
    then show ?thesis
      using parent.follow_nempty[OF \<open>parent par'\<close>]
      by (simp split: if_splits)
  qed
  moreover have "(last (parent.follow par' v3)) = (last (parent.follow par' v1))"
  proof-
    have "par' v3 = Some v2"
      unfolding par'_def
      using if1_props[OF ass]
      by simp
    then show ?thesis
      apply (subst *[symmetric])
      using \<open>parent par'\<close> parent.follow_nempty by fastforce
  qed
  moreover have "v1 \<noteq> v2" "v1 \<noteq> v3"
    by(rule v1_neq_v2_neq_v3[OF ass] v1_neq_v3[OF ass invars(2)])+
  ultimately have "flabel' (last (parent.follow par' v)) = Some (r, Even)" if "flabel' v = Some (r, lab)" for v r lab
    using that
    by (smt ass flabel'_def if1_props(2) map_upd_Some_unfold prod.inject)
  then show ?thesis
    unfolding flabel'_def par'_def last_even_invar_def
    by simp
qed

lemma last_even_invar_imp:
  assumes invars: 
    "parent_spec par"
    "alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd)) (parent.follow par v)"
    "last_even_invar par flabel" and
    "flabel v = Some (r, Even)"
  shows "odd (length (parent.follow par v))"
proof-
  have "flabel (last (parent.follow par v)) = Some (r, Even)"
    using assms
    unfolding last_even_invar_def
    by simp
  moreover have "parent.follow par v \<noteq> []"
    by (metis (mono_tags, lifting) invars(1)  parent.follow_nempty parent.intro)
  moreover have "flabel (hd (parent.follow par v)) = Some (r, Even)"
    by (metis (mono_tags, lifting) alt_list.simps invars(2) list.sel(1) calculation(2))
  ultimately show ?thesis
    by (intro alt_list_length_odd[OF invars(2)])
qed

(*Done: Invar 9*)

definition "distinct_invar par = (\<forall>v. distinct (parent.follow par v))"

lemma distinct_invar_props: "distinct_invar par \<Longrightarrow> distinct (parent.follow par v)"
  unfolding distinct_invar_def
  by simp

lemma distinct_invar_pres:
  assumes invars: 
    "parent_spec par"
    "flabel_invar flabel"
    "flabel_par_invar par flabel"
    "\<And>v r. flabel v = Some (r, Even) \<Longrightarrow> alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd)) (parent.follow par v)"
    "distinct_invar par"
    and
    ass: "if1 flabel ex v1 v2 v3 r"
  shows "distinct_invar (par(v2 \<mapsto> v1, v3 \<mapsto> v2))"
proof-

  define par' where "par' = (par(v2 \<mapsto> v1, v3 \<mapsto> v2))"
  have invar': "parent_spec par'"
    unfolding par'_def
    by (meson assms(6) assms(5) parent_spec_pres(1) invars(1) invars(2) invars(3))
  note follow_simps [simp] = parent.follow.psimps[OF parent.intro[OF invar'] parent.follow_dom[OF parent.intro[OF invar']], of v2]
    parent.follow.psimps[OF parent.intro[OF invar'] parent.follow_dom[OF parent.intro[OF invar']], of v3]

  have "v2 \<noteq> v3"
    using v1_neq_v2_neq_v3(2)[OF ass].
  then have pars: "par' v2 = Some v1" "par' v3 = Some v2"
    unfolding par'_def
    by simp+
  then have rw: "(parent.follow par' v3) = v3 # v2 # (parent.follow par' v1)"
    by simp

  have "flabel v1 = Some (r, Even)"
    using if1_props(2)[OF ass(1)].
  then have *: "alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd)) (parent.follow par v1)"
    using invars(4)
    by blast
  have "flabel v = Some (r, Even) \<or> flabel v = Some (r, Odd)" if "v \<in> set (parent.follow par v1)" for v
    by(intro alt_list_or[OF *] that)
  then have ances_some: "flabel v \<noteq> None" if "v \<in> set (parent.follow par v1)" for v
    using that
    by fastforce
  moreover have "flabel v2 = None"
    using if1_props(3)[OF ass]
    by simp
  moreover have "flabel v3 = None"
    by (intro flabel_invar_props[OF invars(2) if1_props(4)[OF ass]] \<open>flabel v2 = None\<close>)
  ultimately have "v3 \<notin> set (parent.follow par v1)" "v2 \<notin> set (parent.follow par v1)"
    by fastforce+


  have rw_v: "(parent.follow par v) = (parent.follow par' v)" if "v3 \<noteq> v" "v2 \<noteq> v" for v
    unfolding par'_def
    by(intro compute_alt_path_follow_eq[OF ass invars(1-3)] if1_props(3)[OF ass(1)] that)
  then have rw_v1: "(parent.follow par v1) = (parent.follow par' v1)"
    using \<open>flabel v1 = Some (r, Even)\<close> \<open>flabel v2 = None\<close> \<open>flabel v3 = None\<close> by force
  {
    fix v
    consider (c1) "v = v2" | (c2) "v = v3" | (c3) "v \<notin> {v2, v3}"
      by auto
    then have "distinct (parent.follow par' v)"
    proof(cases)
      case c1
      moreover have "distinct (parent.follow par' v1)"
        using distinct_invar_props[OF invars(5), of v1] rw_v1
        by simp
      ultimately show ?thesis
        using c1 \<open>v2 \<notin> set (parent.follow par v1)\<close>
        by(simp add: pars rw_v1)
    next
      case c2
      moreover have "flabel v3 = None"
        by(intro flabel_invar_props[OF invars(2) if1_props(4)[OF ass]] if1_props(3)[OF ass])
      ultimately have "flabel v = None"
        by simp
      then have "v \<notin> set (parent.follow par v1)"
        using ances_some
        by fastforce
      moreover have "distinct (parent.follow par' v1)"
        using distinct_invar_props[OF invars(5), of v1] rw_v1
        by simp
      ultimately show ?thesis
        using c2 \<open>v2 \<notin> set (parent.follow par v1)\<close> \<open>v3 \<notin> set (parent.follow par v1)\<close>
          \<open>v2 \<noteq> v3\<close>
        by(simp add: pars rw_v1)
    next
      case c3
      then have *: "(parent.follow par v) = (parent.follow par' v)"
        using rw_v
        by auto
      show ?thesis
        using distinct_invar_props[OF invars(5), of v]
        unfolding *[symmetric] .
    qed
  }
  then show ?thesis
    unfolding distinct_invar_def par'_def
    by(intro allI)
qed

(*Done: Invar 9*)

definition "path_invar par = (\<forall>v \<in> Vs G. path G (parent.follow par v))"

lemma path_invar_props: "path_invar par \<Longrightarrow> v \<in> Vs G \<Longrightarrow> path G (parent.follow par v)"
  unfolding path_invar_def
  by simp

lemma path_invar_pres:
  assumes invars: 
    "parent_spec par"
    "flabel_invar flabel"
    "flabel_par_invar par flabel"
    "path_invar par"
    and
    ass: "if1 flabel ex v1 v2 v3 r"
  shows "path_invar (par(v2 \<mapsto> v1, v3 \<mapsto> v2))"
proof-
  define par' where "par' = (par(v2 \<mapsto> v1, v3 \<mapsto> v2))"
  have invar': "parent_spec par'"
    unfolding par'_def
    by (meson ass parent_spec_pres(1) invars(1) invars(2) invars(3))
  note follow_simps [simp] = parent.follow.psimps[OF parent.intro[OF invar'] parent.follow_dom[OF parent.intro[OF invar']]]

  have "v2 \<noteq> v3"
    using v1_neq_v2_neq_v3(2)[OF ass].
  then have pars: "par' v2 = Some v1" "par' v3 = Some v2"
    unfolding par'_def
    by simp+
  then have rw: "(parent.follow par' v3) = v3 # v2 # (parent.follow par' v1)"
    by simp

  have "{v3, v2} \<in> G"
    by (metis ass compute_alt_path.if1_def matching(2) compute_alt_path_axioms in_mono insert_commute)
  have "{v2, v1} \<in> G"
    by (metis Diff_iff ass if1_def insert_commute)
  then have "v1 \<in> Vs G"
    unfolding Vs_def
    by auto

  have rw_v: "(parent.follow par v) = (parent.follow par' v)" if "v3 \<noteq> v" "v2 \<noteq> v" for v
    unfolding par'_def
    by(intro compute_alt_path_follow_eq[OF ass invars(1-3)] if1_props(3)[OF ass(1)] if1_props(1)[OF ass] that)
  then have rw_v1: "(parent.follow par v1) = (parent.follow par' v1)"
    using ass invars(2) v1_neq_v2_neq_v3(1) v1_neq_v3 by fastforce
  {
    fix v
    assume "v \<in> Vs G"
    consider (c1) "v = v2" | (c2) "v = v3" | (c3) "v \<notin> {v2, v3}"
      by auto
    then have "path G (parent.follow par' v)"
    proof(cases)
      case c1
      moreover have "path G (parent.follow par' v1)"
        using path_invar_props[OF invars(4), of v1] rw_v1 \<open>v1 \<in> Vs G\<close>
        by simp
      ultimately show ?thesis
        using c1 \<open>{v2, v1} \<in> G\<close>
        apply(simp add: pars rw_v1)
        apply(split option.splits)+
        by simp+
    next
      case c2
      moreover have "path G (parent.follow par' v1)"
        using path_invar_props[OF invars(4), of v1] rw_v1 \<open>v1 \<in> Vs G\<close>
        by simp
      ultimately show ?thesis
        using c2 \<open>{v2, v1} \<in> G\<close> \<open>{v3, v2} \<in> G\<close>
        apply(simp add: pars rw_v1)
        apply(split option.splits)+
        by simp+
    next
      case c3
      then have *: "(parent.follow par v) = (parent.follow par' v)"
        using rw_v
        by auto
      show ?thesis
        using path_invar_props[OF invars(4), of v] \<open>v \<in> Vs G\<close>
        unfolding *[symmetric] .
    qed
  }
  then show ?thesis
    unfolding path_invar_def par'_def
    by(intro ballI)
qed

lemma compute_alt_path_from_tree_1:
  assumes invars: 
    "\<And>v r lab. flabel v = Some (r, lab) \<Longrightarrow> alt_labels_invar flabel r (parent.follow par v)"
    (*Done *)
    "\<And>v r. flabel v = Some (r, Even) \<Longrightarrow> alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd)) (parent.follow par v)"
    "parent_spec par"
    "flabel_invar flabel"
    "flabel_par_invar par flabel"
    "last_not_matched_invar par flabel"
    "matching_examined_invar flabel ex"
    "last_even_invar par flabel"
    "distinct_invar par"
    "path_invar par"
    "flabel_invar_2 flabel" and
    ret:    
    "compute_alt_path ex par flabel = Some (p1, p2)" and
    init:       
    "finite ex" "ex \<subseteq> G"
  shows "last p1 \<notin> Vs M \<and>
       last p2 \<notin> Vs M \<and>
       hd p1 \<noteq> hd p2 \<and>
       odd (length p1) \<and>
       odd (length p2) \<and>
       distinct p1 \<and>
       distinct p2 \<and>
       path G p1 \<and>
       path G p2 \<and>
       {hd p1, hd p2} \<in> G \<and>
       (\<forall>x pref1 post1 pref2 post2. p1 = pref1 @ x # post1 \<and> p2 = pref2 @ x # post2 \<longrightarrow> post1 = post2) \<and>
       alt_path M (hd p1 # p2) \<and> 
       alt_path M (hd p2 # p1)" 
  using assms
proof(induction ex par flabel arbitrary: p1 p2 rule: compute_alt_path_pinduct_2)
  case 1
  then show ?case
    by(intro compute_alt_path_dom init)
next
  case (2 ex par flabel)
  show ?case
  proof(cases "if1_cond flabel ex")
    case True
    obtain v1 v2 v3 r where sel: "(v1,v2,v3,r) = sel_if1 flabel ex" "if1 flabel ex v1 v2 v3 r"
      using if1_cond_props''''[OF True] by metis
    let ?par' = "par(v2 \<mapsto> v1, v3 \<mapsto> v2)"
    let ?flabel' = "flabel(v2 \<mapsto> (r, Odd), v3 \<mapsto> (r, Even))"
    let ?ex' = "insert {v2, v3} (insert {v1, v2} ex)"
    have "compute_alt_path ex par flabel = compute_alt_path ?ex' ?par' ?flabel'"
      by(auto intro: compute_alt_path_if1[OF 2(1) True sel(1)])
    then have "compute_alt_path ?ex' ?par' ?flabel' = Some (p1, p2)"
      using 2
      by simp
    moreover have "parent_spec ?par'"
      using parent_spec_pres(1)[OF 2(5-7) sel(2)].
    moreover have "flabel_invar (?flabel')"
      using flabel_invar_pres[OF 2(6) sel(2), of Odd _ Even].
    moreover have "flabel_par_invar (?par') (?flabel')"
      using flabel_par_invar_pres(1)[OF 2(7) sel(2)].
    moreover have "compute_alt_path_dom (?ex', ?par', ?flabel')"
      apply(intro compute_alt_path_dom_if1[OF sel(2)])
      using 2(16,15)
      by auto
    moreover have "finite (insert {v1, v2} ex)"
      using 2(15)
      by auto
    moreover have "?ex' \<subseteq> G"
      by (meson "2.prems"(14) DiffD1 compute_alt_path.if1_props(1) compute_alt_path_axioms if1_props(4) insert_subsetI matching(2) sel(2) subsetD)
    moreover have "alt_labels_invar ?flabel' r' (parent.follow ?par' v)" if "?flabel' v = Some (r', lab)" for v r' lab
      apply(intro alt_labels_invar_pres[OF sel(2) 2(3,4,5,6,7)])
      using that
      by auto
    moreover have "alt_list (\<lambda>v. ?flabel' v = Some (r', Even)) (\<lambda>v. ?flabel' v = Some (r', Odd)) (parent.follow ?par' v)" if "?flabel' v = Some (r', Even)" for v r'
      using alt_list_pres[OF sel(2) 2(4,5,6,7)] 2(5,6,7) that
      by auto
    moreover have "finite ?ex'"
      using 2(15)
      by auto
    moreover have "last_not_matched_invar ?par' ?flabel'"
      by(intro last_not_matched_invar_pres(2)[OF sel(2) 2(5,6,7,8)])
    moreover have "matching_examined_invar ?flabel' ?ex'"
      using matching_examined_invar_pres[OF 2(6,9) sel(2)]
      .
    moreover have "last_even_invar ?par' ?flabel'"
      using last_even_invar_pres[OF 2(5,6,7,10) sel(2)]
      .
    moreover have "distinct_invar ?par' "
      using distinct_invar_pres[OF 2(5,6,7,4,11) sel(2)]
      .
    moreover have "path_invar ?par'"
      using path_invar_pres[OF 2(5,6,7,12) sel(2)]
      .
    moreover have "flabel_invar_2 ?flabel'"
      by(intro flabel_invar_2_pres[OF _ sel(2)] 2)
    ultimately show ?thesis
      using sel
      apply(intro 2(2)[OF True, of v1 v2 v3 r])
      by (simp; blast)+
  next
    case False
    then have if2_holds: "if2_cond flabel"
      using 2(14)
      by(auto simp add: compute_alt_path.psimps[OF 2(1)] split: if_splits prod.splits)
    then obtain v1 v2 r s where v1v2r: "(v1,v2,r,s) = sel_if2 flabel" "if2 flabel v1 v2 r s"
      using if2_cond_props''''
      by force
    then have s: "flabel v2 = Some (s, Even)" "p1 = parent.follow par v1" "p2 = parent.follow par v2"
                 "flabel v1 = Some (r, Even)" "{v1, v2} \<in> G"
      unfolding if2_def
      using False 2(14) v1v2r(1)
      by (auto simp add: compute_alt_path.psimps[OF 2(1)] Let_def split: if_splits prod.splits)
    moreover have "v1 = hd p1" "v2 = hd p2"
      by (metis "2.prems"(3,4) calculation(3,2) list.sel(1) parent.follow_cons_3 parent.intro)+
    moreover have "\<forall>x pref1 post1 pref2 post2. p1 = pref1 @ x # post1 \<and> p2 = pref2 @ x # post2 \<longrightarrow> post1 = post2"
      using "2.prems"(3) parent.from_tree parent.intro s(2) s(3) by fastforce
    moreover have "(\<forall>v. flabel v \<noteq> None \<longrightarrow> last (parent.follow par v) \<notin> Vs M)"
      using 2(8)
      unfolding last_not_matched_invar_def .
    then have "last (parent.follow par v1) \<notin> Vs M" "last (parent.follow par v2) \<notin> Vs M"
      using s by auto
    moreover have "{v1, v2} \<notin> M"
      by(intro flabel_invar_2_props[OF 2(13), where ?r = r and ?s = s] s)
    then have "alt_path M (v1 # parent.follow par v2)"
      apply(intro nin_M_alt_path)
      subgoal apply(subst \<open>p2 = parent.follow par v2\<close>[symmetric])
        by(simp add: \<open>v1 = hd p1\<close> \<open>v2 = hd p2\<close>)
      subgoal using alt_invars_then_alt_path[where ?r = s, OF 2(5,4) 2(3)[OF \<open>flabel v2 = Some (s, Even)\<close>] ]
        subgoal using \<open>flabel v2 = Some (s, Even)\<close> .
        done
      done
    moreover have "alt_path M (v2 # parent.follow par v1)"
      apply(intro nin_M_alt_path)
      subgoal using \<open>{v1, v2} \<notin> M\<close>
        apply(subst \<open>p1 = parent.follow par v1\<close>[symmetric])
        by(simp add: \<open>v1 = hd p1\<close> \<open>v2 = hd p2\<close> insert_commute)
      subgoal using alt_invars_then_alt_path[where ?r = r, OF 2(5,4) 2(3)[OF \<open>flabel v1 = Some (r, Even)\<close>] ]
        subgoal using \<open>flabel v1 = Some (r, Even)\<close> .
        done
      done
    moreover have "v1 \<noteq> v2"
      using graph s(5)
      by (auto elim: dblton_graphE)
    moreover have "odd (length (parent.follow par v1))"
      using last_even_invar_imp[OF 2(5,4,10) \<open>flabel v1 = Some (r, Even)\<close> ] \<open>flabel v1 = Some (r, Even)\<close>
      by simp
    moreover have "odd (length (parent.follow par v2))"
      using last_even_invar_imp[OF 2(5,4,10) ] \<open>flabel v2 = Some (s, Even)\<close> 
      by blast
    moreover have "distinct (parent.follow par v1)" "distinct (parent.follow par v2)"
      by(intro distinct_invar_props[OF 2(11)])+
    moreover have "v1 \<in> Vs G"
      using s(5) by(auto simp: Vs_def)
    then have "path G (parent.follow par v1)"
      by(intro path_invar_props[OF 2(12)])
    moreover have "v2 \<in> Vs G"
      using s(5) by(auto simp: Vs_def)
    then have "path G (parent.follow par v2)"
      by(intro path_invar_props[OF 2(12)])
    ultimately show ?thesis
      using 2(5)
      by metis
  qed
qed

subsubsection \<open>Algorithm is Totally Correct: it does not miss Alternating Paths\<close>

(*Done: Invar 11*)

definition "examined_have_odd_verts_invar ex flabel = (\<forall>e\<in>ex. \<exists>v\<in>e.\<exists>r. flabel v = Some (r, Odd))"

lemma examined_have_odd_verts_invar_pres:
  assumes invars: 
    "flabel_invar flabel"
    "examined_have_odd_verts_invar ex flabel"
    and
    ass: "if1 flabel ex v1 v2 v3 r"
  shows "examined_have_odd_verts_invar (insert {v2, v3} (insert {v1, v2} ex)) (flabel(v2 \<mapsto> (r, Odd), v3 \<mapsto> (r', Even)))"
proof-
  have "flabel v2 = None"
    using if1_props(3)[OF ass].
  moreover have "flabel v3 = None"
    by(rule if1_props[OF ass] flabel_invar_props(1)[OF invars(1)])+
  ultimately show ?thesis
    using invars(2) v1_neq_v2_neq_v3(2)[OF ass]
    apply (clarsimp simp: examined_have_odd_verts_invar_def)
    using option.distinct(1)
    by metis
qed

lemma examined_have_odd_verts_invar_props:
  "examined_have_odd_verts_invar ex flabel \<Longrightarrow> \<forall>v\<in>e. flabel v = None \<Longrightarrow> e \<notin> ex"
  unfolding examined_have_odd_verts_invar_def
  by auto

(*Done: Invar 12*)

definition "unexamined_matched_unlabelled_invar ex flabel = (\<forall>e\<in>M - ex. \<forall>v\<in>e. flabel v = None)"

lemma unexamined_matched_unlabelled_invar_props:
  "unexamined_matched_unlabelled_invar ex flabel \<Longrightarrow> e \<in> M \<Longrightarrow> e \<notin> ex \<Longrightarrow> v \<in> e \<Longrightarrow> flabel v = None"
  unfolding unexamined_matched_unlabelled_invar_def
  by auto

lemma unexamined_matched_unlabelled_invar_pres:
  assumes invars: 
    "flabel_invar flabel"
    "unexamined_matched_unlabelled_invar ex flabel"
    and
    ass: "if1 flabel ex v1 v2 v3 r"
  shows "unexamined_matched_unlabelled_invar (insert {v2, v3} (insert {v1, v2} ex)) (flabel(v2 \<mapsto> (r, Odd), v3 \<mapsto> (r', Even)))"
proof-
  have "flabel v2 = None"
    by(rule if1_props[OF ass])
  moreover have "flabel v3 = None"
    by(rule if1_props[OF ass] flabel_invar_props(1)[OF invars(1)])+
  ultimately show ?thesis
    using unexamined_matched_unlabelled_invar_props[OF invars(2)]
      if1_props[OF ass]
      matching_unique_match[OF matching(1)]
    apply (simp add: unexamined_matched_unlabelled_invar_def)
    by blast
qed

(*Done: Invar 13*)

definition "finite_odds_invar flabel = finite {v. \<exists>r. flabel v = Some (r, Odd)}"

lemma finite_odds_invar_pres:
  assumes invars: 
    "flabel_invar flabel"
    "finite_odds_invar flabel"
    and
    ass: "if1 flabel ex v1 v2 v3 r"
  shows "finite_odds_invar(flabel(v2 \<mapsto> (r, Odd), v3 \<mapsto> (r', Even)))"
proof-
  define flabel' where "flabel' = (flabel(v2 \<mapsto> (r, Odd), v3 \<mapsto> (r', Even)))"
  have "flabel v2 = None"
    by(rule if1_props[OF ass])
  moreover have "flabel v3 = None"
    by(intro calculation flabel_invar_props(1)[OF invars(1) if1_props(4)[OF ass]])
  moreover have "v2 \<noteq> v3"
    by(rule v1_neq_v2_neq_v3[OF ass])
  ultimately have "{v. \<exists>r. flabel' v = Some (r, Odd)} = insert v2 {v. \<exists>r. flabel v = Some (r, Odd)}"
    unfolding flabel'_def
    by auto
  then show ?thesis
    using invars(2)
    unfolding finite_odds_invar_def flabel'_def
    by simp
qed

(*Done: Invar 14*)

definition "odd_labelled_verts_num_invar ex flabel = 
              (card {v. \<exists>r. flabel v = Some (r, Odd)} = card (M \<inter> ex))"

lemma odd_labelled_verts_num_invar_pres:
  assumes invars: 
    "flabel_invar flabel"
    "odd_labelled_verts_num_invar ex flabel"
    "finite_odds_invar flabel"
    "examined_have_odd_verts_invar ex flabel"
    and
    ass: "if1 flabel ex v1 v2 v3 r"
  shows "odd_labelled_verts_num_invar (insert {v2, v3} (insert {v1, v2} ex)) (flabel(v2 \<mapsto> (r, Odd), v3 \<mapsto> (r', Even)))"
proof-
  define flabel' where "flabel' = (flabel(v2 \<mapsto> (r, Odd), v3 \<mapsto> (r', Even)))"
  have "v2 \<noteq> v3"
    by(rule v1_neq_v2_neq_v3[OF ass])
  moreover have "flabel v2 = None"
    by(rule if1_props[OF ass])
  moreover have "flabel v3 = None"
    by(rule if1_props[OF ass] flabel_invar_props(1)[OF invars(1)])+
  ultimately have "{v. \<exists>r. flabel' v = Some (r, Odd)} = insert v2 {v. \<exists>r. flabel v = Some (r, Odd)}" "v2 \<notin> {v. \<exists>r. flabel v = Some (r, Odd)}"
    unfolding flabel'_def
    by auto
  moreover have "finite {v. \<exists>r. flabel v = Some (r, Odd)}"
    using invars(3)
    unfolding finite_odds_invar_def
    by simp
  ultimately have i: "card {v. \<exists>r. flabel' v = Some (r, Odd)} = card {v. \<exists>r. flabel v = Some (r, Odd)} + 1"
    by simp
  define ex' where "ex' = (insert {v2, v3} (insert {v1, v2} ex))"
  have "flabel v3 = None"
    by (simp add: \<open>flabel v3 = None\<close>)
  then have "{v2, v3} \<notin> ex"
    apply(intro examined_have_odd_verts_invar_props[where flabel = flabel] invars)
    using \<open>flabel v2 = None\<close>
    by simp
  moreover have "{v1, v2} \<notin> M"
    using \<open>flabel v2 = None\<close> ass compute_alt_path.if1_props(2) compute_alt_path_axioms flabel_invar_props(2) invars(1) by fastforce
  moreover have "{v2, v3} \<in> M"
    by(rule if1_props[OF ass])
  moreover have "finite M"
    using infinite_super matching(2) finite_E
    by auto
  ultimately have ii: "card (M \<inter> ex') = card (M \<inter> ex) + 1"
    unfolding ex'_def
    by simp
  show ?thesis
    using i ii invars(2)
    by (auto simp: odd_labelled_verts_num_invar_def ex'_def flabel'_def)  
qed

(*Done: Invar 15*)

definition
  "ulabelled_verts_matched_invar ex flabel = (\<forall>v \<in> (Vs G). flabel v = None \<longrightarrow> (\<exists>e\<in>(M - ex). v \<in> e))"

lemma ulabelled_verts_matched_invar_pres:
  assumes invars: 
    "ulabelled_verts_matched_invar ex flabel"
    and
    ass: "if1 flabel ex v1 v2 v3 r"
  shows "ulabelled_verts_matched_invar (insert {v2, v3} (insert {v1, v2} ex)) (flabel(v2 \<mapsto> (r, Odd), v3 \<mapsto> (r', Even)))"
  using invars
  using if1_props(2)[OF ass]
  by (fastforce simp add: ulabelled_verts_matched_invar_def Vs_def)

(*Done: Invar 16*)

definition 
  "odd_then_matched_examined_invar ex flabel =
     (\<forall>v \<in> (Vs G). \<exists>r. flabel v = Some(r, Odd) \<longrightarrow> (\<exists>e\<in>(M \<inter> ex). v \<in> e))"

lemma odd_then_matched_examined_invar_pres:
  assumes invars: 
    "flabel_invar flabel"
    "odd_then_matched_examined_invar ex flabel"
    and
    ass: "if1 flabel ex v1 v2 v3 r"
  shows "odd_then_matched_examined_invar (insert {v2, v3} (insert {v1, v2} ex)) (flabel(v2 \<mapsto> (r, Odd), v3 \<mapsto> (r', Even)))"
  using assms
  unfolding odd_then_matched_examined_invar_def Vs_def
  by (fastforce simp add: if1_props)+

end

definition odd_set_cover where
  "odd_set_cover OSC G = (finite OSC \<and> (\<forall>s\<in>OSC. odd (card s) \<and> finite s) \<and>
                         (\<forall>e\<in>G.\<exists>s\<in>OSC. (if card s = 1 then s \<inter> e \<noteq> empty else e \<subseteq> s)))"

definition capacity1 where
  "capacity1 s = (if card s = 1 then 1 else (card s) div 2)"

lemma cap11[simp]: "capacity1 {x} = 1"
  unfolding capacity1_def
  by simp

definition capacity2 where
  "capacity2 OSC = (\<Sum>s\<in>OSC. capacity1 s)"

lemma cap21[simp]: "capacity2 {{x}} = 1"
  unfolding capacity2_def
  by simp

definition es where
  "es s = {e. card e = 2 \<and> e \<subseteq> s}"

lemma es_minus: "es (s - e) = (es s) - {e'. e' \<inter> e \<noteq> empty}"
  unfolding es_def
  by auto

lemma es_minus_matched: "matching M \<Longrightarrow> e \<in> M \<Longrightarrow> (M \<inter> (es s - {e})) = (M \<inter> es (s - e))"
  apply(auto simp add: es_minus matching_def)
  by (simp add: es_def)

lemma es_sing: "es {v} = {}"
  unfolding es_def
  by (auto simp: subset_iff card_Suc_eq numeral_2_eq_2)

lemma odd_set_coverI: 
  assumes "finite OSC" "(\<And>s. s\<in>OSC \<Longrightarrow> odd (card s) \<and> finite s)"
          "(\<And>e. e\<in>G \<Longrightarrow> \<exists>s\<in>OSC. (if card s = 1 then s \<inter> e \<noteq> empty else e \<subseteq> s))"
  shows "odd_set_cover OSC G"
  using assms 
  by (auto simp: odd_set_cover_def)

lemma capacity_bounds_common_edges:
  assumes 
    "finite G"
    "finite s"
    "matching M"
    "M \<subseteq> G"
    "odd (card s)"
    "dblton_graph G"
  shows "card (M \<inter> es s) \<le> capacity1 s"
proof-
  have "finite M"
    using assms(1,4)
    using infinite_super by auto
  then show ?thesis
    using assms
  proof(induction M arbitrary: s)
    case empty
    then show ?case
      by simp
  next
    case (insert e M')
    obtain v1 v2 where e: "e = {v1, v2}" "v1 \<noteq> v2"
      using insert.prems(4) insert.prems(6)
      by (auto elim: dblton_graphE)
    define es' where "es' = es s - {e}"
    define s' where "s' = s - e"
    consider (one) "card s = 1" | (three) "card s = 3" | (ge_five)"card s \<ge> 5"
      using insert(8)
      by (metis (no_types, lifting) One_nat_def Suc_leI antisym_conv card_gt_0_iff eval_nat_numeral(3) even_numeral insert.prems(2) not_less_eq_eq numeral_3_eq_3 numeral_4_eq_4 odd_card_imp_not_empty)
    then show ?case
    proof cases
      case one
      then obtain v where "s = {v}"
        by (erule card_1_singletonE)
      then have "card (insert e M' \<inter> es s) \<le> 1"
        by(simp add: es_sing)
      then show ?thesis
        using one
        by(simp add: capacity1_def)
    next
      define M where "M = insert e M'"
      then have "matching M"
        using insert(6)
        by simp
      case three
      then obtain u1 u2 u3 where u1u2u3: "s = {u1, u2, u3}" "u1 \<noteq> u2" "u1 \<noteq> u3"  "u2 \<noteq> u3"
        by (auto simp: card_Suc_eq numeral_3_eq_3 numeral_2_eq_2)
      then have "es s = {{u1,u2}, {u2,u3}, {u1,u3}}" "{u1,u2} \<noteq> {u2,u3}" "{u1,u2} \<noteq> {u1,u3}" "{u2,u3} \<noteq> {u1,u3}"
        unfolding es_def
        by (auto simp: card_Suc_eq numeral_2_eq_2 subset_iff)
      then have "\<exists>e1 e2. e1 \<noteq> e2 \<and> e1 \<in> M \<and> e2 \<in> M \<and> e1 \<inter> e2 \<noteq> empty" if "2 \<le> card (M \<inter> es s)"
        using that u1u2u3(2-4)
        apply(simp add: card_le_Suc_iff numeral_2_eq_2 Int_def ex_in_conv)
        by (smt insert_compr mem_Collect_eq)
      then have "card (M \<inter> es s) \<le> 1"
        using \<open>matching M\<close>
        by(fastforce simp add: matching_def)
      then show ?thesis
        using three
        by(simp add: capacity1_def M_def)
    next
      case ge_five
      show ?thesis
      proof(cases "e\<subseteq>s")
        have "(insert e M' \<inter> es s) \<subseteq> insert e (M' \<inter> es s')"
          using insert(2) matching_unique_match[OF insert.prems(3)]
          by(auto simp add: es_minus es_def s'_def subset_iff)
        then have "card (insert e M' \<inter> es s) \<le> card (insert e (M' \<inter> es s'))"
          apply(intro card_mono)
          using insert(5)
          by (auto simp add: s'_def es_def)
        also have "... \<le> card (M' \<inter> es s') + 1"
          by (simp add: insert.hyps(1) insert.hyps(2))
        finally have "card (insert e M' \<inter> es s) \<le> card (M' \<inter> es s') + 1".
        moreover case True
        then have "card (s - {v1, v2}) = card s - 2"
          by (simp add: e insert.prems(2))
        then have "capacity1 s' + 1 \<le> capacity1 s"
          unfolding capacity1_def s'_def e
          using ge_five
          by auto
        moreover have "odd (card s')"
          using insert(8) \<open>card (s - {v1, v2}) = card s - 2\<close> ge_five
          by(simp add: s'_def e(1))
        then have "card (M' \<inter> es s') \<le> capacity1 s'"
          using insert
          by(auto simp: s'_def matching_def)
        ultimately show ?thesis
          by linarith
      next
        case False
        then have "(M' \<inter> es s) = (insert e M' \<inter> es s)"
          using insert(2) matching_unique_match[OF insert.prems(3)]
          by(auto simp add: es_minus es_def s'_def subset_iff)
        moreover have "card (M' \<inter> es s) \<le> capacity1 s"
          apply(rule insert)+
          using insert
          by(auto simp: s'_def matching_def)
        ultimately show ?thesis
          by simp
      qed
    qed 
  qed
qed

lemma OSC_empty: "odd_set_cover {} G \<Longrightarrow> G = {}"
  unfolding odd_set_cover_def
  by auto

lemma OSC_insert:
  assumes "card s \<ge> 3" "odd_set_cover (insert s OSC) G" "dblton_graph G"
  shows "odd_set_cover OSC (G - es s)"
proof-
  {
    fix e
    assume "e\<in>G - es s"
    then have "e \<in> G"
      by simp
    then obtain s' where s': "s'\<in>(insert s OSC)"  "if card s' = 1 then s' \<inter> e \<noteq> {} else e \<subseteq> s'"
      using assms(2)
      by (auto simp add: odd_set_cover_def)
    moreover have "card e = 2"
      using assms(3) \<open>e \<in> G\<close>
      by (fastforce elim: dblton_graphE)
    ultimately have "\<exists>s\<in>OSC. if card s = 1 then s \<inter> e \<noteq> {} else e \<subseteq> s"
      using assms(1) s' \<open>e \<in> G - es s\<close>
      by (fastforce simp add: es_def)
  }
  then show ?thesis
    using assms(2)
    unfolding odd_set_cover_def
    by auto
qed

lemma odd_set_cover_bounds_matching_size:
  assumes 
    "finite G"
    "matching M"
    "M \<subseteq> G"
    "odd_set_cover OSC G"
    "dblton_graph G"
  shows "card M \<le> capacity2 OSC"
proof-
  have "finite OSC"
    using assms(4) odd_set_cover_def by blast
  then show ?thesis
    using assms
  proof(induction OSC arbitrary: M G)
    case empty
    then have "M = {}"
      using OSC_empty
      by auto
    then show ?case
      by (simp add: capacity2_def)
  next
    case (insert s OSC)
    then show ?case
    proof(cases "card s = 1")
      case True
      then obtain v where v: "s = {v}"
        by(elim card_1_singletonE)
      define ev where "ev = {e. v \<in> e}"
      have "odd_set_cover OSC (G - ev)"
        using insert(1,7)
        unfolding odd_set_cover_def ev_def
        by (fastforce simp: card_Suc_eq v)
      moreover have "matching (M - ev)" "(M - ev) \<subseteq> (G - ev)"
        using insert(5,6)
        by (auto simp add: matching_def)
      ultimately have "card (M - ev) \<le> capacity2 OSC"
        apply(intro insert(3)[where G = "G - ev"])
        using insert
        by (auto simp add: dblton_graph_def)
      moreover have "\<exists>e1 e2. e1 \<noteq> e2 \<and> e1 \<in> M \<and> e2 \<in> M \<and> e1 \<inter> e2 \<noteq> empty" if "2 \<le> card (M \<inter> ev)"
        using that 
        apply(simp add: card_le_Suc_iff numeral_2_eq_2 Int_def ex_in_conv ev_def)
        by (metis (mono_tags, lifting) insert_iff mem_Collect_eq)
      then have "card (M \<inter> ev) \<le> 1"
        using \<open>matching M\<close>
        by(fastforce simp add: matching_def)      
      then have "card M \<le> card (M - ev) + 1"
        by (metis card_Diff_subset_Int diff_le_mono2 finite_Int insert.prems(1) insert.prems(3) le_diff_conv rev_finite_subset)
      moreover have "capacity2 (insert s OSC) = capacity2 OSC + 1"
        using insert(1,2)
        by (simp add: True capacity1_def capacity2_def)
      ultimately show ?thesis
        by linarith
    next
      case False
      moreover have "odd (card s)"
        using insert(7)
        unfolding odd_set_cover_def
        by auto
      ultimately have "card s \<ge> 3"
        by presburger
      then have "odd_set_cover OSC (G - es s)"
        apply(intro OSC_insert insert) .
      moreover have "matching (M - es s)" "M - es s \<subseteq> G -  es s"
        using insert
        by (auto simp add: Diff_mono matching_def)
      ultimately have "card (M - es s) \<le> capacity2 OSC"
        apply(intro insert(3)[where G = "G - es s"])
        using insert
        by (auto simp: dblton_graph_def)
      moreover have "card (M \<inter> es s) \<le> capacity1 s"
        apply(intro capacity_bounds_common_edges[OF insert(4)] insert)
        using \<open>odd (card s)\<close> odd_card_imp_not_empty
        by (force elim: )+
      moreover have "finite (M \<inter> es s)"
        using insert.prems(1,3) infinite_super
        by blast
      then have "card (M - es s) = card M - card (M \<inter> es s)"
        using card_Diff_subset_Int
        by auto
      ultimately have "card M \<le> capacity2 OSC + capacity1 s"
        by simp
      then show ?thesis
        by (simp add: capacity2_def insert(1,2))
    qed
  qed
qed

lemma OSC_union: "odd_set_cover OSC1 G1 \<Longrightarrow> odd_set_cover OSC2 G2 \<Longrightarrow> odd_set_cover (OSC1 \<union> OSC2) (G1 \<union> G2)"
  unfolding odd_set_cover_def
  by (auto; metis Un_iff)

lemma OSC_inter: "odd_set_cover OSC G1 \<Longrightarrow> odd_set_cover OSC (G1 \<inter> G2)"
  unfolding odd_set_cover_def
  by auto

lemma card_sing_image: "card {{x} | x . P x} = card {x . P x}"
proof-
  have "card ((\<lambda>x. {x}) ` {x . P x}) =  card {x . P x}"
    apply(intro card_image)
    by simp
  then show ?thesis
    by (simp add: setcompr_eq_image)
qed

lemma card_UNION_const:
  assumes "finite S"
    "(\<And>s. s \<in> S \<Longrightarrow> card s = k)"
    "\<And>s s'. s \<noteq> s' \<Longrightarrow> s \<in> S \<Longrightarrow> s' \<in> S \<Longrightarrow> s \<inter> s' = {}"
  shows "card (\<Union> S) = k * card S"
  using assms
proof(induction S)
  case empty
  then show ?case by simp
next
  case (insert s S')
  then show ?case
    apply simp
    by (metis add_diff_cancel_left' card_Un_disjoint card_eq_0_iff diff_zero finite_Un finite_Union
              insert.prems(2) insert_partition mult.commute mult_0_right)
qed

lemma capacity1_gt1: "0 < k \<Longrightarrow> card s = Suc (2 * k) \<Longrightarrow> capacity1 s = k"
  unfolding capacity1_def
  by auto

lemma capacity2_sings:
  assumes "finite {{v} | v . P v}" shows "capacity2 {{v} | v . P v} = card {{v} | v . P v}"
proof-
  have "sum capacity1 {{v} |v. P v} = (\<Sum>s\<in>{{v} |v. P v}. 1)"
    using assms
    by(fastforce simp:capacity2_def intro: sum.mono_neutral_cong_right)
  then show ?thesis
    unfolding capacity2_def
    by simp
qed


lemma capacity2_Un_disjoint: "S \<inter> U = {} \<Longrightarrow> finite S \<Longrightarrow> finite U \<Longrightarrow> capacity2 (S \<union> U) = capacity2 S + capacity2 U"
  by (simp add: capacity2_def sum.union_disjoint)

context compute_alt_path
begin

lemma finiteM: "finite M"
  using finite_E matching(2) finite_subset
  by blast

lemma compute_alt_path_from_tree_2':
  assumes invars: 
    "flabel_invar flabel"
    "examined_have_odd_verts_invar ex flabel"
    "unexamined_matched_unlabelled_invar ex flabel"
    "finite_odds_invar flabel"
    "odd_labelled_verts_num_invar ex flabel"
    "ulabelled_verts_matched_invar ex flabel"
    "odd_then_matched_examined_invar ex flabel" and
    ret:
    "compute_alt_path ex par flabel = None" and
    init:       
    "finite ex" "ex \<subseteq> G"
  shows "\<nexists>p. matching_augmenting_path M p \<and> path G p \<and> distinct p"
proof-
  have "\<exists>OSC. odd_set_cover OSC G \<and> capacity2 OSC = card M"
    using assms
  proof(induction ex par flabel rule: compute_alt_path_pinduct_2)
    case 1
    then show ?case
      by(intro compute_alt_path_dom init)
  next
    case (2 ex par flabel)
    show ?case
    proof(cases "if1_cond flabel ex")
      case True
      obtain v1 v2 v3 r where sel: "(v1, v2, v3, r) = sel_if1 flabel ex" "if1 flabel ex v1 v2 v3 r"
        using if1_cond_props''''[OF True] by metis
      let ?par' = "par(v2 \<mapsto> v1, v3 \<mapsto> v2)"
      let ?flabel' = "flabel(v2 \<mapsto> (r, Odd), v3 \<mapsto> (r, Even))"
      let ?ex' = "insert {v2, v3} (insert {v1, v2} ex)"
      have "compute_alt_path ex par flabel = compute_alt_path ?ex' ?par' ?flabel'"
        by(auto intro: compute_alt_path_if1[OF 2(1) True sel(1)])
      then have "compute_alt_path ?ex' ?par' ?flabel' = None"
        using 2
        by simp
      moreover have "flabel_invar ?flabel'"
        using flabel_invar_pres[OF 2(3) sel(2), of Odd _ Even].
      moreover have "examined_have_odd_verts_invar ?ex' ?flabel'"
        using examined_have_odd_verts_invar_pres(1)[OF 2(3,4) sel(2)].
      moreover have "?ex' \<subseteq> G"
        by (meson "2.prems"(10) DiffD1 compute_alt_path.if1_props(1) compute_alt_path_axioms if1_props(4) insert_subsetI matching(2) sel(2) subsetD)
      moreover have "finite ?ex'"
        using 2
        by auto
      moreover have "unexamined_matched_unlabelled_invar ?ex' ?flabel'"
        using unexamined_matched_unlabelled_invar_pres(1)[OF 2(3,5) sel(2)].
      moreover have "finite_odds_invar ?flabel'"
        by(intro finite_odds_invar_pres[where ex = ex and ?v1.0 = v1] 2 sel)
      moreover have "odd_labelled_verts_num_invar ?ex' ?flabel'"
        by(intro odd_labelled_verts_num_invar_pres[where ex = ex and ?v1.0 = v1] 2 sel)
      moreover have "ulabelled_verts_matched_invar ?ex' ?flabel'"
        by(intro ulabelled_verts_matched_invar_pres[where ex = ex and ?v1.0 = v1] 2 sel)
      moreover have "odd_then_matched_examined_invar ?ex' ?flabel'"
        by(intro odd_then_matched_examined_invar_pres[where ex = ex and ?v1.0 = v1] 2 sel)
      ultimately show ?thesis
        using sel
        apply(intro 2(2)[OF True, of v1 v2 v3 r])
        by (simp; blast)+
    next
      case noL1: False
      then have if2_nholds: "\<not>if2_cond flabel"
        using 2
        by(auto simp add: compute_alt_path.psimps[OF 2(1)] split: prod.splits)
      define lab_osc where "lab_osc = {{v} | v . \<exists>r. flabel v = Some (r, Odd)}"
      {
        fix es
        assume "\<And>e. e \<in> es \<Longrightarrow> \<exists>v \<in> e. \<exists>r. flabel v = Some (r, Odd)"
        then have "\<exists>s\<in>lab_osc. e \<inter> s \<noteq> {}" if "e \<in> es" for e 
          using \<open>examined_have_odd_verts_invar ex flabel\<close> that
          unfolding examined_have_odd_verts_invar_def lab_osc_def
          apply auto
          by (metis disjoint_insert(2))
        moreover have "finite lab_osc"
          unfolding lab_osc_def
          using \<open>finite_odds_invar flabel\<close> finite_odds_invar_def
          by force
        moreover have "odd (card s) \<and> finite s" if "s\<in>lab_osc" for s
          using that
          unfolding lab_osc_def
          by auto
        moreover have "card s = 1" if "s \<in> lab_osc" for s
          using that
          unfolding lab_osc_def
          by auto
        ultimately have "odd_set_cover lab_osc es"
          unfolding odd_set_cover_def
          by (simp add: inf_commute)
        then have "odd_set_cover lab_osc (es \<inter> G)"
          by(rule OSC_inter)
      } note * = this
      have "odd_set_cover lab_osc (ex \<inter> G)"
        apply(intro *)
        using \<open>examined_have_odd_verts_invar ex flabel\<close>
        using examined_have_odd_verts_invar_def
        by blast
      have "finite lab_osc"
        unfolding lab_osc_def
        using \<open>finite_odds_invar flabel\<close> finite_odds_invar_def
        by force
      have all_verts_labelled: "\<exists>v. v \<in> e \<and> (flabel v = None \<or> (\<exists>r. flabel v = Some (r, Odd)))"
        if "e \<in> G" for e
      proof-
        obtain v1 v2 where "e = {v1, v2}" "v1 \<noteq> v2"
          using \<open>e \<in> G\<close> graph_invar_dblton[OF graph]
          apply -
          by(erule dblton_graphE)
        then have "flabel v1 = None \<or> (\<exists>r. flabel v1 = Some (r, Odd)) \<or>
                   flabel v2 = None \<or> (\<exists>r. flabel v2 = Some (r, Odd))"
          using if2_nholds
          unfolding if2_cond_def
          by (smt label.exhaust option.exhaust surj_pair that)
        moreover have "v1 \<in> e" "v2 \<in> e"
          using \<open>e = {v1, v2}\<close>
          by auto
        ultimately show ?thesis
          by auto
      qed
      have lab_osc_covers: "\<exists>s\<in>lab_osc. s \<inter> e \<noteq> {} \<and>  card s = 1"
        if "v \<in> e" "\<exists>r. flabel v = Some (r, Odd)" for e v
      proof-
        have "{v} \<in> lab_osc"
          using that
          unfolding lab_osc_def
          by auto
        moreover have "card {v} = 1"
          by simp
        ultimately show ?thesis
          using that
          by auto
      qed
      consider (all_match_ex) "card (M - ex) = 0" | (one_match_unex) "card (M - ex) = 1" | (mult_match_unex) "2 \<le> card (M - ex)"
        by linarith
      then show ?thesis
      proof cases
        case all_match_ex
        then have "flabel v \<noteq> None" if "v \<in> e" "e \<in> G" for v e
          using \<open>ulabelled_verts_matched_invar ex flabel\<close> that finiteM 
          by (force simp: ulabelled_verts_matched_invar_def)
        then have "\<exists>v \<in> e. \<exists>r. flabel v = Some (r, Odd)" if "e \<in> G" for e
          using all_verts_labelled that
          by blast
        then have "odd_set_cover lab_osc (G \<inter> G)"
          apply(intro *)
          by simp
        then have "odd_set_cover lab_osc G"
          by simp
        moreover have "M \<inter> ex = M"
          using all_match_ex finite_subset[OF matching(2) finite_E]
          by fastforce
        then have "card (M \<inter> ex) = card M"
          by simp
        then have "card M = card lab_osc"
          using \<open>odd_labelled_verts_num_invar ex flabel\<close> 
          unfolding odd_labelled_verts_num_invar_def lab_osc_def card_sing_image
          by simp
        moreover have "... = capacity2 lab_osc"
          using \<open>finite lab_osc\<close>
          unfolding lab_osc_def
          apply(intro capacity2_sings[symmetric])
          by auto
        ultimately show ?thesis
          by auto
      next
        case one_match_unex
        then obtain e where "(M - ex) = {e}" 
          by(auto simp: card_Suc_eq)
        then obtain v1 v2 where "e = {v1, v2}" "v1 \<noteq> v2"
          using matching(2) graph
          by (auto elim!: dblton_graphE)
        then have "flabel v1 = None" "flabel v2 = None"
          using \<open>unexamined_matched_unlabelled_invar ex flabel\<close> \<open>M - ex = {e}\<close>
          by(auto simp: unexamined_matched_unlabelled_invar_def)
        define unlab_osc where "unlab_osc = {{v1}}"
        define osc where "osc = lab_osc \<union> unlab_osc"
        have "\<exists>s\<in>osc. s \<inter> e' \<noteq> {} \<and> card s = 1" if "e' \<in> G - ex" for e'
        proof(cases "e' \<in> M")
          case True
          then have "e = e'"
            using \<open>M - ex = {e}\<close> that
            by auto
          then show ?thesis
            by(auto simp add: unlab_osc_def \<open>e = {v1, v2}\<close> osc_def)
        next
          case False
          obtain va where "va \<in> e'" "flabel va = None \<or> (\<exists>r. flabel va = Some (r, Odd))"
            using all_verts_labelled \<open>e' \<in> G - ex\<close>
            by force      
          then consider "(\<exists>r. flabel va = Some (r, Odd))" | "flabel va = None"
            by auto
          then show ?thesis
          proof cases
            case 1
            then have "{va} \<in> osc"
              unfolding osc_def lab_osc_def
              by auto
            then show ?thesis
              using \<open>va \<in> e'\<close>
              by auto
          next
            case 2
            then have "va = v1 \<or> va = v2"
              by (metis "2.prems"(6) DiffD1 \<open>M - ex = {e}\<close> \<open>e = {v1, v2}\<close> \<open>va \<in> e'\<close>
                        ulabelled_verts_matched_invar_def insertE singletonD that vs_member_intro)
            then consider (v1) "va = v1" | (v2) "va = v2"
              by auto
            then show ?thesis
            proof cases
              case v1
              then show ?thesis
                using \<open>va \<in> e'\<close>
                by (auto simp: osc_def unlab_osc_def)
            next
              case v2
              obtain vb where "e' = {va, vb}" "va \<noteq> vb"
                using \<open>va \<in> e'\<close> \<open>e' \<in> G - ex\<close> graph
                by auto
              consider (none) "flabel vb = None" | (odd) "\<exists>r. flabel vb = Some (r, Odd)" | (even) "\<exists>r. flabel vb = Some (r, Even)"
                by (cases "flabel vb"; auto intro: label.exhaust)
              then show ?thesis
              proof cases
                case none
                then show ?thesis
                  using "2.prems"(6)
                  by (smt  DiffD1 Diff_insert_absorb False \<open>M - ex = {e}\<close> \<open>e = {v1, v2}\<close>
                          \<open>e' = {va, vb}\<close> \<open>va \<noteq> vb\<close> edges_are_Vs insert_absorb insert_commute v2
                          singletonD singleton_insert_inj_eq' that ulabelled_verts_matched_invar_def)
              next
                case odd
                then have "\<exists>s\<in>lab_osc. s \<inter> e' \<noteq> {} \<and> card s = 1"
                  using \<open>e' = {va, vb}\<close> lab_osc_covers
                  by auto
                then show ?thesis
                  unfolding osc_def
                  by blast
              next
                case even
                moreover have "{v2, v1} \<in> M"
                  using \<open>M - ex = {e}\<close> \<open>e = {v1, v2}\<close>
                  by auto
                moreover have "{vb, va} \<in> G - ex"
                  using \<open>e' \<in> G - ex\<close> \<open>e' = {va, vb}\<close>
                  by (simp add: insert_commute)
                ultimately have "if1_cond flabel ex"
                  unfolding if1_cond_def
                  using v2 \<open>flabel v2 = None\<close>
                  by metis
                then show ?thesis
                  using noL1
                  by simp
              qed 
            qed
          qed
        qed
        moreover have "finite osc"
          unfolding osc_def lab_osc_def unlab_osc_def
          using \<open>finite_odds_invar flabel\<close> finite_odds_invar_def
          by force
        moreover have "odd (card s) \<and> finite s" if "s\<in>osc" for s
          using that
          unfolding lab_osc_def osc_def unlab_osc_def
          by auto
        moreover have "card s = 1" if "s \<in> osc" for s
          using that
          unfolding osc_def lab_osc_def unlab_osc_def
          by auto
        ultimately have "odd_set_cover osc (G - ex)"
          unfolding odd_set_cover_def
          by simp
        hence "odd_set_cover (osc \<union> lab_osc) ((G - ex) \<union> (ex \<inter> G))"
          apply(intro OSC_union)
          using \<open>odd_set_cover lab_osc (ex \<inter> G)\<close>
          by simp+
        hence i: "odd_set_cover osc G"
          unfolding osc_def
          by (simp add: Un_Diff_Int Un_commute inf_commute)
        have "lab_osc \<inter> unlab_osc = {}"
          using \<open>flabel v1 = None\<close>
          unfolding lab_osc_def unlab_osc_def
          by auto
        moreover have "finite unlab_osc"
          by (simp add: unlab_osc_def)
        ultimately have "card osc = card lab_osc + card unlab_osc"
          unfolding osc_def
          apply(intro card_Un_disjoint)
          using \<open>finite lab_osc\<close>
          by auto
        also have "... = card (M - ex) + card (M \<inter> ex)"
          unfolding unlab_osc_def
          using \<open>card (M - ex) = 1\<close> \<open>odd_labelled_verts_num_invar ex flabel\<close> 
          unfolding odd_labelled_verts_num_invar_def lab_osc_def card_sing_image
          by simp
        also have "... = card ((M - ex) \<union> (M \<inter> ex))"
          apply(intro card_Un_disjoint[symmetric])
          using finiteM
          by auto
        finally have "card osc = card ((M - ex) \<union> (M \<inter> ex))".
        moreover have "M = ((M - ex) \<union> (M \<inter> ex))"
          by auto
        ultimately have "card M = card osc"
          by simp
        moreover have *: "osc = {{v} | v. v = v1 \<or> (\<exists>r. flabel v = Some (r, Odd))}"
          unfolding osc_def lab_osc_def unlab_osc_def
          by auto
        moreover have "finite ..."
          using * \<open>finite osc\<close> by simp
        then have "capacity2 ... = card ..."
          apply(intro capacity2_sings)
          using \<open>finite lab_osc\<close>
          by (auto simp: lab_osc_def)
        ultimately have "capacity2 osc = card M"
          by simp
        then show ?thesis
          using i
          by metis
      next
        case mult_match_unex
        then obtain e M' where M': "e \<in> M - ex" "M - ex = insert e M'" "e \<notin> M'"
          by(auto simp: card_le_Suc_iff numeral_2_eq_2)
        then obtain v1 v2 where v1v2: "e = {v1, v2}" "v1 \<noteq> v2"
          using matching(2) graph
          by (force elim: dblton_graphE)
        have "v1 \<notin> \<Union> M'" (*as, e is disjoint will edges in M', as M is a matching*)
          by (metis DiffD1 Diff_insert_absorb M'(2) M'(3) Union_iff matching(1) insertI1 matching_unique_match v1v2(1))
        have "e = {v2, v1}"
          using \<open>e = {v1, v2}\<close> by auto
        then have "v2 \<notin> \<Union> M'"
          by (metis DiffD1 Diff_insert_absorb M'(2) M'(3) Union_iff matching(1) insertI1 matching_unique_match)
        define unlab_osc1 where "unlab_osc1  = {{v1}}"
        define unlab_osc2 where "unlab_osc2  = {{v2} \<union> \<Union>M'}"
        define osc where "osc = lab_osc \<union> unlab_osc1 \<union> unlab_osc2"
        have card_unlab_osc2: "card ({v2} \<union> \<Union> M') = Suc (2 * card M')"
        proof-
          have "finite M'"
            by (metis M'(2) finiteM finite_Diff finite_insert)
          moreover have "card e = 2" if "e \<in> M'" for e
            using graph matching(2)
            by (metis dblton_graph_def Diff_subset M'(2) card_2_iff insert_subset subset_iff that)
          moreover have "e \<inter> e' = {}" if "e \<in> M'" "e' \<in> M'" "e \<noteq> e'" for e e'
            using matching(1) that
            unfolding matching_def2
            by (metis Diff_subset Int_emptyI M'(2) in_mono matching(1) matching_unique_match subset_insertI)
          ultimately have "card (\<Union>M') = (2 * card M')"
            apply(intro card_UNION_const).
          have "{v2} \<inter> \<Union>M' = {}"
            using \<open>v2 \<notin> \<Union>M'\<close> by auto
          moreover have "finite (\<Union>M')"
            using matching(2) graph(1) M'(2)
            by (metis dblton_graph_def Un_Diff_Int Union_Un_distrib Union_insert
                      finite.simps finite_Un finite_Union finite_insert finite_E
                      inf.orderE inf_commute)
          ultimately have "card ({v2} \<union> \<Union> M') = card {v2} + card (\<Union>M')"
            unfolding unlab_osc2_def
            apply(intro card_Un_disjoint)
            by auto
          then show ?thesis
            using \<open>card (\<Union>M') = (2 * card M')\<close>
            by simp
        qed

        have "finite unlab_osc1"
          unfolding unlab_osc1_def
          by auto
        moreover have "finite unlab_osc2"
          unfolding unlab_osc2_def
          by auto
        moreover have "unlab_osc1 \<inter> unlab_osc2 = {}"
          using \<open>v1 \<noteq> v2\<close> \<open>v1 \<notin> \<Union>M'\<close>
          by (auto simp: unlab_osc1_def unlab_osc2_def)
        ultimately have "capacity2 (unlab_osc1 \<union> unlab_osc2) = capacity2 unlab_osc1 + capacity2 unlab_osc2"
          apply(intro capacity2_Un_disjoint) .
        moreover have "capacity2 unlab_osc1 = 1"
          by (auto simp: unlab_osc1_def)
        moreover have "capacity2 unlab_osc2 = card M'"
        proof-
          have "finite M'"
            by (metis M'(2) finiteM finite_Diff finite_insert)
          then have "0 < card M'"
            using mult_match_unex M' card_unlab_osc2
            by simp
          hence "capacity1 ({v2} \<union> \<Union> M') = card M'"
            using card_unlab_osc2
            apply(intro capacity1_gt1) .
          then show ?thesis
            unfolding unlab_osc2_def
            by (auto simp add: capacity2_def)
        qed
        ultimately have "capacity2 (unlab_osc1 \<union> unlab_osc2) = Suc (card M')"
          by simp
        moreover have "card (M - ex) = Suc (card M')"
          using M' finiteM
          by (metis card_insert_disjoint finite_Diff finite_insert)
        ultimately have "capacity2 (unlab_osc1 \<union> unlab_osc2) = card (M -ex)"
          by auto
        moreover have "capacity2 (lab_osc \<union> (unlab_osc1 \<union> unlab_osc2)) = capacity2 lab_osc + capacity2 (unlab_osc1 \<union> unlab_osc2)"
        proof-
          have "flabel v = None" if "v \<in> \<Union>M'" for v
            using that
            apply auto
            by (metis "2.prems"(3) M'(2) subset_eq  subset_insertI unexamined_matched_unlabelled_invar_def)
          moreover have "flabel v2 = None"
            using "2.prems"(3) M'(1) unexamined_matched_unlabelled_invar_props v1v2(1) by fastforce
          ultimately have "lab_osc \<inter> unlab_osc2 = {}"
            unfolding lab_osc_def unlab_osc2_def
            by auto
          moreover have "flabel v1 = None"
            using "2.prems"(3) M'(1) unexamined_matched_unlabelled_invar_props v1v2(1) by fastforce
          then have "lab_osc \<inter> unlab_osc1 = {}"
            using \<open>flabel v1 = None\<close>
            unfolding lab_osc_def unlab_osc1_def
            by auto
          ultimately have "lab_osc \<inter> (unlab_osc1 \<union> unlab_osc2) = {}" by auto
          moreover have "finite (unlab_osc1 \<union> unlab_osc2)"
            using \<open>finite unlab_osc1\<close> \<open>finite unlab_osc2\<close>
            by simp
          moreover have "finite lab_osc"
            unfolding lab_osc_def
            using \<open>finite_odds_invar flabel\<close> finite_odds_invar_def
            by force
          ultimately show ?thesis
            apply(intro capacity2_Un_disjoint) .
        qed
        moreover have "capacity2 lab_osc = card lab_osc"
          using \<open>finite lab_osc\<close>
          unfolding lab_osc_def
          apply(intro capacity2_sings)
          by auto
        then have "card lab_osc = card (M \<inter> ex)"
          using \<open>odd_labelled_verts_num_invar ex flabel\<close> 
          unfolding odd_labelled_verts_num_invar_def lab_osc_def card_sing_image
          by simp
        moreover have "card ((M - ex) \<union> (M \<inter> ex)) = card (M - ex) + card (M \<inter> ex)"
          apply(intro card_Un_disjoint)
          using finiteM
          by auto
        ultimately have "capacity2 osc = card M"
          by (simp add: Un_Diff_Int \<open>capacity2 lab_osc = card lab_osc\<close> Un_assoc osc_def)
        moreover have "odd_set_cover osc G"
        proof-
          have "\<exists>s\<in>osc. (s \<inter> e' \<noteq> {} \<and> card s = 1) \<or> e' \<subseteq> s" if "e' \<in> G - ex" for e'
          proof-
            have "e' = e \<or> e' \<in> M' \<or> e' \<notin> M"
              using M' v1v2 that
              by auto
            then consider (e) "e' = e" | (M') "e' \<in> M'" | (unmatched) "e' \<notin> M"
              by metis
            then show ?thesis
            proof cases
              case e
              then show ?thesis
                by (simp add: osc_def unlab_osc1_def v1v2(1))
            next
              case M'
              then have "\<exists>s\<in>unlab_osc2. e' \<subseteq> s"
                unfolding unlab_osc2_def
                by auto
              then show ?thesis
                unfolding osc_def
                by auto
            next
              case unmatched
              have "e' \<in> G"
                using that by simp
              then obtain va vb where "e' = {va, vb}" "va \<noteq> vb"
                using graph
                by (blast elim: dblton_graphE)
              have "(\<forall>v\<in>{va,vb}.\<exists>r. flabel v = Some (r, Even)) \<or>
                  ((\<exists>v\<in>{va,vb}.\<exists>r. flabel v = Some (r, Odd))) \<or>
                  ((\<exists>v\<in>{va,vb}.\<exists>r. flabel v = Some (r, Even)) \<and> (\<exists>v\<in>{va,vb}. flabel v = None)) \<or>
                  (\<forall>v\<in>{va,vb}. flabel v = None)"
                apply (cases "flabel va"; cases "flabel vb")
                using label.exhaust label.distinct
                by auto
              then consider
                (evens) "(\<forall>v\<in>{va,vb}.\<exists>r. flabel v = Some (r, Even))" |
                (odd) "((\<exists>v\<in>{va,vb}.\<exists>r. flabel v = Some (r, Odd)))" |
                (even_unlab) "((\<exists>v\<in>{va,vb}.\<exists>r. flabel v = Some (r, Even)) \<and> (\<exists>v\<in>{va,vb}. flabel v = None))"|
                (nones) "(\<forall>v\<in>{va,vb}. flabel v = None)"
                by presburger
              then show ?thesis
              proof cases
                case evens
                then have "if2_cond flabel"
                  unfolding if2_cond_def
                  using \<open>e' = {va, vb}\<close> \<open>e' \<in> G\<close>
                  by blast
                hence False
                  using \<open>\<not> if2_cond flabel\<close>
                  by simp
                then show ?thesis
                  by simp
              next
                case odd
                then have "\<exists>s\<in>lab_osc. s \<inter> e' \<noteq> {} \<and> card s = 1"
                  using \<open>e' = {va, vb}\<close> lab_osc_covers
                  by auto
                then show ?thesis
                  unfolding osc_def
                  by blast
              next
                case even_unlab
                then obtain e where "e \<in> M" "(flabel va = None \<and> va \<in> e) \<or> (flabel vb = None \<and> vb \<in> e)"
                  using \<open>ulabelled_verts_matched_invar ex flabel\<close>
                    \<open>e' \<in> G - ex\<close> \<open>e' = {va, vb}\<close>
                  unfolding ulabelled_verts_matched_invar_def Vs_def
                  by fastforce
                then obtain v where "(flabel va = None \<and> e = {v, va}) \<or> (flabel vb = None \<and> e = {v, vb})"
                  using graph matching(2)
                  by (auto elim: dblton_graphE)
                then have "flabel v = None"
                  using \<open>e \<in> M\<close> \<open>flabel_invar flabel\<close>
                  unfolding flabel_invar_def
                  by auto
                then have "if1_cond flabel ex"
                  unfolding if1_cond_def
                  by (smt \<open>e \<in> M\<close> \<open>e' = {va, vb}\<close> \<open>flabel va = None \<and> e = {v, va} \<or> flabel vb = None \<and> e = {v, vb}\<close> empty_iff even_unlab insertE insert_commute option.distinct(1) that)
                hence False
                  using \<open>\<not> if1_cond flabel ex\<close>
                  by simp
                then show ?thesis
                  by simp
              next
                case nones
                then show ?thesis
                proof(cases "va = v1 \<or> vb = v1")
                  case True
                  then have "\<exists>s\<in>unlab_osc1. s \<inter> e' \<noteq> {} \<and> card s = 1"
                    using \<open>e' = {va, vb}\<close>
                    unfolding unlab_osc1_def
                    by auto
                  then show ?thesis
                    unfolding osc_def
                    by auto
                next
                  case False
                  then have "va \<noteq> v1" "vb \<noteq> v1"
                    by simp+
                  have "\<Union>(M - ex) = {v1, v2} \<union> \<Union> M'"
                    using unlab_osc2_def \<open>M - ex = insert e M'\<close> \<open>e = {v1, v2}\<close>
                    by auto
                  also have  "... - {v1} = {v2} \<union> \<Union> M'"
                    using \<open>v1 \<noteq> v2\<close> \<open>v1 \<notin> \<Union> M'\<close>
                    by auto
                  finally have "\<Union>(M - ex) - {v1} = {v2} \<union> \<Union> M'".
                  moreover have "va \<in> \<Union>(M - ex)" "vb \<in> \<Union>(M - ex)"
                    using nones
                    by (metis "2.prems"(6) Union_iff \<open>e' = {va, vb}\<close> \<open>e' \<in> G\<close> edges_are_Vs insertI1 
                              ulabelled_verts_matched_invar_def insert_commute)+
                  then have "{va, vb} \<subseteq> \<Union>(M - ex) - {v1}"
                    using \<open>va \<noteq> v1\<close> \<open>vb \<noteq> v1\<close>
                    by auto
                  ultimately have "\<exists>s\<in>unlab_osc2. e' \<subseteq> s"
                    using \<open>e' = {va, vb}\<close> by (simp add: unlab_osc2_def)
                  then show ?thesis
                    unfolding osc_def
                    by auto
                qed
              qed
            qed
          qed
          moreover have "finite osc"
            by (simp add: \<open>finite lab_osc\<close> osc_def unlab_osc1_def unlab_osc2_def)
          moreover have "odd (card s) \<and> finite s" if "s \<in> osc" for s
            using that card_unlab_osc2
            unfolding lab_osc_def osc_def unlab_osc1_def unlab_osc2_def
            apply auto
            by (metis card.infinite finite_insert nat.simps(3))
          ultimately have i: "odd_set_cover osc (G - ex)"
            using graph
            apply(intro odd_set_coverI)
            apply simp_all
            by (metis inf.absorb_iff2 insert_not_empty dblton_graphE)
          hence "odd_set_cover (osc \<union> lab_osc) ((G - ex) \<union> (ex \<inter> G))"
            apply(intro OSC_union)
            using \<open>odd_set_cover lab_osc (ex \<inter> G)\<close>
            by simp+
          then show ?thesis
            unfolding osc_def
            by (metis Un_Diff_Int inf_commute le_sup_iff sup.absorb1 sup_ge1)
        qed
        ultimately show ?thesis
          by metis
      qed
    qed
  qed
  then have "card M' \<le> card M" if "matching M'" "M' \<subseteq> G" for M'
    using odd_set_cover_bounds_matching_size graph finite_E that
    by metis
  then show ?thesis
    by (meson Berge_2(1) Berge_2(2) Berge_2(3) finiteM leD matching(1) matching(2))
qed

lemma compute_alt_path_from_tree_2:
  assumes invars: 
    "flabel_invar flabel"
    "examined_have_odd_verts_invar ex flabel"
    "unexamined_matched_unlabelled_invar ex flabel"
    "finite_odds_invar flabel"
    "odd_labelled_verts_num_invar ex flabel"
    "ulabelled_verts_matched_invar ex flabel"
    "odd_then_matched_examined_invar ex flabel" and
    aug_path:
    "\<exists>p. matching_augmenting_path M p \<and> path G p \<and> distinct p"
    and
    init:       
    "finite ex" "ex \<subseteq> G"
  shows "\<exists>match_blossom_comp. compute_alt_path ex par flabel = Some match_blossom_comp"
  using compute_alt_path_from_tree_2'[OF invars _ init, where par = par] option.distinct aug_path
  by blast

subsubsection \<open>Bringing it All Together: Final Correctness Theorems\<close>

lemma invar_init:
  fixes flabel::"('a \<Rightarrow> ('a \<times> label) option)" and
    ex::"'a set set" and 
    par::"'a \<Rightarrow> 'a option" 
  assumes initialisation:
    "\<And>v. flabel v = (if v \<in> Vs G \<and> v \<notin> Vs M then Some (v, Even) else None)" "ex = empty"
    "\<And>v. par v = None"
  shows
    "\<And>v r lab. flabel v = Some (r, lab) \<Longrightarrow> alt_labels_invar flabel r (parent.follow par v)"
    "\<And>v r. flabel v = Some (r, Even) \<Longrightarrow> alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd)) (parent.follow par v)"
    "parent_spec par"
    "flabel_invar flabel"
    "flabel_par_invar par flabel"
    "last_not_matched_invar par flabel"
    "matching_examined_invar flabel ex"
    "last_even_invar par flabel"
    "distinct_invar par"
    "path_invar par"
    "flabel_invar_2 flabel"
    "examined_have_odd_verts_invar ex flabel"
    "unexamined_matched_unlabelled_invar ex flabel"
    "finite_odds_invar flabel"
    "odd_labelled_verts_num_invar ex flabel"
    "ulabelled_verts_matched_invar ex flabel"
    "odd_then_matched_examined_invar ex flabel"
proof-
  show "flabel_invar flabel"
    using assms  
    unfolding flabel_invar_def
    by (auto simp: edges_are_Vs)
  show "examined_have_odd_verts_invar ex flabel"
    using assms  
    unfolding examined_have_odd_verts_invar_def
    by auto
  show "unexamined_matched_unlabelled_invar ex flabel"
    using assms  
    unfolding unexamined_matched_unlabelled_invar_def
    by (auto simp: Vs_def)
  show "finite_odds_invar flabel"
    using assms  
    unfolding finite_odds_invar_def Vs_def
    apply simp
    using not_finite_existsD
    by blast
  show "odd_labelled_verts_num_invar ex flabel"
    using assms  
    unfolding odd_labelled_verts_num_invar_def
    using card_eq_0_iff by fastforce
  show "ulabelled_verts_matched_invar ex flabel"
    using assms  
    unfolding ulabelled_verts_matched_invar_def Vs_def
    by auto
  show "odd_then_matched_examined_invar ex flabel" 
    using assms  
    unfolding odd_then_matched_examined_invar_def
    by auto
  show "parent_spec par"
    using assms  
    unfolding parent_spec_def
    by auto
  then have "parent par"
    by (simp add: parent_def)
  then have par[simp]: "(parent.follow par v) = [v]" if "par v = None" for v
    using parent.follow_psimps[OF \<open>parent par\<close>] that
    by auto
  then show "\<And>v r lab. flabel v = Some (r, lab) \<Longrightarrow> alt_labels_invar flabel r (parent.follow par v)"
    using assms  
    apply auto
    by (metis Pair_inject option.inject option.simps(3))
  show "\<And>v r. flabel v = Some (r, Even) \<Longrightarrow> alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd)) (parent.follow par v)"
    using assms  
    by (auto simp: alt_list_step alt_list_empty)
  show "flabel_par_invar par flabel"
    using assms  
    unfolding flabel_par_invar_def
    by auto
  show "last_not_matched_invar par flabel"
    using assms  
    unfolding last_not_matched_invar_def Vs_def
    by auto
  show "matching_examined_invar flabel ex"
    using assms  
    unfolding matching_examined_invar_def Vs_def
    by auto
  show "last_even_invar par flabel"
    using assms  
    unfolding last_even_invar_def
    by auto
  show "distinct_invar par"
    using assms  
    unfolding distinct_invar_def
    by auto
  show "path_invar par"
    using assms  
    unfolding path_invar_def
    by (auto simp: Vs_def)
  show "flabel_invar_2 flabel"
    using assms  
    unfolding flabel_invar_2_def
    by (simp add: edges_are_Vs)
qed

abbreviation "ex_init \<equiv> {}"
abbreviation "par_init \<equiv> Map.empty"
abbreviation "flabel_init \<equiv> (\<lambda>v. if v \<in> Vs G \<and> v \<notin> Vs M then Some (v, Even) else None)"

lemma compute_alt_path_from_tree_sound:
  fixes flabel::"'a \<Rightarrow> ('a \<times> label) option" and
    ex::"'a set set" and
    par::"'a \<Rightarrow> 'a option"
  assumes  initialisation:
    "\<And>v. flabel v = (if v \<in> Vs G \<and> v \<notin> Vs M then Some (v, Even) else None)" "ex = empty"
    "\<And>v. par v = None"
    and
    ret:
    "compute_alt_path ex par flabel = Some (p1, p2)"
  shows "last p1 \<notin> Vs M \<and>
       last p2 \<notin> Vs M \<and>
       hd p1 \<noteq> hd p2 \<and>
       odd (length p1) \<and>
       odd (length p2) \<and>
       distinct p1 \<and>
       distinct p2 \<and>
       path G p1 \<and>
       path G p2 \<and>
       {hd p1, hd p2} \<in> G \<and>
       (\<forall>x pref1 post1 pref2 post2. p1 = pref1 @ x # post1 \<and> p2 = pref2 @ x # post2 \<longrightarrow> post1 = post2) \<and>
       alt_path M (hd p1 # p2) \<and> 
       alt_path M (hd p2 # p1)"
  apply(intro compute_alt_path_from_tree_1[OF invar_init(1-11)[OF initialisation] ret])
  using initialisation
  by auto

lemma compute_alt_path_from_tree_sound':
  fixes flabel::"'a set set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> ('a \<times> label) option" and
    ex::"'a set set" and
    par::"'a \<Rightarrow> 'a option"
  assumes  initialisation:
    "\<And>v G M. flabel G M v = (if v \<in> Vs G \<and> v \<notin> Vs M then Some (v, Even) else None)" "ex = empty"
    "\<And>v. par v = None"
  shows "compute_alt_path_spec G M (compute_alt_path ex par (flabel G M))"
  using compute_alt_path_from_tree_sound[where par = par, OF initialisation]
  unfolding compute_alt_path_spec_def
  apply(intro conjI)
  by metis+

lemma compute_alt_path_from_tree_complete:
  fixes flabel::"'a set set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> ('a \<times> label) option" and
    ex::"'a set set" and
    par::"'a \<Rightarrow> 'a option"
  assumes  initialisation:
    "\<And>G M v. flabel G M v = (if v \<in> Vs G \<and> v \<notin> Vs M then Some (v, Even) else None)" "ex = empty"
    "\<And>v. par v = None"
    and
    aug_path:
    "\<exists>p. matching_augmenting_path M p \<and> path G p \<and> distinct p"
  shows "\<exists>match_blossom_comp. compute_alt_path ex par (flabel G M) = Some match_blossom_comp"
  apply(intro compute_alt_path_from_tree_2 invar_init[OF initialisation] aug_path)
  using initialisation
  by auto

end 

locale compute_alt_path_use =
  g: graph_abs E +
  choose sel +
  create_vert create_vert 
  for sel create_vert:: "'a set \<Rightarrow> 'a" and E::"'a set set "
begin

abbreviation "flabel \<equiv> (\<lambda>G M v. if v \<in> Vs G \<and> v \<notin> Vs M then Some (v, Even) else None)"
abbreviation "ex \<equiv> empty"
abbreviation "par \<equiv> (\<lambda>v. None)"

interpretation compute_match_blossom'_use E sel create_vert "(\<lambda>G M. compute_alt_path.compute_alt_path G M sel ex par (flabel G M))"
proof(unfold_locales,goal_cases)
  case (2 G M)
  then interpret compute_alt_path  G M
    apply unfold_locales
    by auto
  show ?case
    apply(rule compute_alt_path_from_tree_complete)
    using 2
    by auto
next
  case (1 G M)
  then interpret compute_alt_path G M
    apply unfold_locales
    by auto
   show ?case
     apply(rule compute_alt_path_from_tree_sound')
     by auto
qed

lemmas find_max_matching_works = find_max_matching_works 
end

end