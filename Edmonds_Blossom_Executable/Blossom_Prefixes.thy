(*
  Author: Mohammad Abdulaziz
*)

theory Blossom_Prefixes
  imports Graph_Quotient Blossom_Misc
begin

provenance human

datatype 'a match_blossom_res =
   Path "'a list" 
| Blossom (stem_vs: "'a list") (cycle_vs: "'a list")

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
  then show ?case
    by auto
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
      using \<^marker>\<open>provenance ai\<close> cons1
      by \<^marker>\<open>provenance ai\<close> (auto simp: Let_def split: if_splits prod.splits option.splits
                               dest: cons1(1)[OF sym])
  qed
qed

lemma first_pfx_then_snd_pfx:
  "(Some pfx1,l2_pfx) = (longest_disj_pfx l1 l2) \<Longrightarrow> \<exists>pfx2. l2_pfx = Some pfx2"
proof(induction l2 arbitrary: l1 pfx1 l2_pfx)
  case Nil
  then show ?case
    by auto
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
      using \<^marker>\<open>provenance ai\<close> cons1
      by \<^marker>\<open>provenance ai\<close> (auto simp: Let_def split: if_splits prod.splits option.splits
                               dest: cons1(1)[OF sym])
  qed
qed

lemma first_pfx_nempty:
  "(Some pfx1,l2_pfx) = (longest_disj_pfx l1 l2) \<Longrightarrow> pfx1 \<noteq> []"
proof(induction l2 arbitrary: l1 pfx1 l2_pfx)
  case Nil
  then show ?case
    by auto
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
      using \<^marker>\<open>provenance ai\<close> cons1
      by \<^marker>\<open>provenance ai\<close> (auto simp: Let_def split: if_splits prod.splits option.splits
                               dest: cons1(1)[OF sym])
  qed
qed

lemma snd_pfx_nempty:
  "(l1_pfx, Some pfx2) = (longest_disj_pfx l1 l2) \<Longrightarrow> pfx2 \<noteq> []"
proof(induction l2 arbitrary: l1 l1_pfx pfx2)
  case Nil
  then show ?case
    by auto
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
  then show ?case
    by auto
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
      using \<^marker>\<open>provenance ai\<close> cons1 
      by \<^marker>\<open>provenance ai\<close> (auto simp: Let_def split: if_splits prod.splits option.splits
                               dest: cons1(1)[OF sym] snd_pfx_nempty[OF sym])
  qed
qed

lemma find_pfx_nempty: "l \<noteq> [] \<Longrightarrow> find_pfx Q l \<noteq> []"
  by(induction l; auto)

lemma find_pfx_empty: "find_pfx Q l = [] \<Longrightarrow> l = []"
  using find_pfx_nempty
  by auto

lemma disj_pref_append1:
  assumes "(Some pfx1, l2_pfx) = (longest_disj_pfx l1 l2)"
  shows "\<exists>l1'. l1 = pfx1@l1'"
  using assms
proof(induction l2 arbitrary: l1 pfx1 l2_pfx)
  case Nil
  then show ?case
    by auto
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
  then show ?case
    by auto
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
      using \<^marker>\<open>provenance ai\<close> cons1
      by \<^marker>\<open>provenance ai\<close> (auto simp: Let_def split: if_splits prod.splits option.splits
                               dest: cons1(1)[OF sym])
  qed
qed

lemma disj_pfx_are_disj_1:
  assumes "(Some pfx1, l2_pfx) = (longest_disj_pfx l1 l2)"
  shows "set pfx1 \<inter> set (butlast (the l2_pfx)) = {}"
  using assms
proof(induction l2 arbitrary: l1 pfx1 l2_pfx)
  case Nil
  then show ?case
    by auto
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
    proof (clarsimp simp add: Let_def split: if_splits prod.splits option.splits, goal_cases)
      case 1
      then show ?case
        by (auto dest: cons1(1)[OF sym])
    next
      case 2
      then show ?case
        using \<^marker>\<open>provenance ai\<close> 2(2)[OF sym[OF 2(5)]] disj_pref_append1[OF sym[OF 2(5)]]
              first_pfx_nempty[OF sym[OF 2(5)]] find_pfx_empty[OF 2(3)]
        by \<^marker>\<open>provenance ai\<close> (auto simp: Cons_eq_append_conv)
    next
      case 3
      then show ?case
        by \<^marker>\<open>provenance ai\<close> (auto dest: cons1(1)[OF sym])
    next
      case 4
      then show ?case
        using \<^marker>\<open>provenance ai\<close> 4(2)[OF sym[OF 4(6)]] disj_pref_append1[OF sym[OF 4(6)]]
              first_pfx_nempty[OF sym[OF 4(6)]] find_pfx_works_1[of a2 l1' "(=) a2"]
        by \<^marker>\<open>provenance ai\<close> (auto simp: Cons_eq_append_conv)
    qed
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
  then show ?case
    by auto
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
    proof (clarsimp simp add: Let_def split: if_splits prod.splits option.splits, goal_cases)
      case 1
      then show ?case
        by (auto dest: find_pfx_butlast_2)
    next
      case 2
      then show ?case
        using \<^marker>\<open>provenance ai\<close> 2(2)[OF sym[OF 2(5)]] disj_pref_append1[OF sym[OF 2(5)]]
              first_pfx_nempty[OF sym[OF 2(5)]] find_pfx_empty[OF 2(3)]
        by \<^marker>\<open>provenance ai\<close> (auto simp: Cons_eq_append_conv)
    next
      case 3
      then show ?case
        using \<^marker>\<open>provenance ai\<close> 3(2)[OF sym[OF 3(6)]] disj_pref_append1[OF sym[OF 3(6)]]
              first_pfx_nempty[OF sym[OF 3(6)]] find_pfx_works_1[of a2 l1' "(=) a2"]
        by \<^marker>\<open>provenance ai\<close> (auto simp: Cons_eq_append_conv dest: in_set_butlastD)
    qed
  qed
qed

lemma disj_pfx_are_disj_3:
  assumes "(Some pfx1, l2_pfx) = (longest_disj_pfx l1 l2)"
  shows "set (butlast pfx1) \<inter> set (butlast (the l2_pfx)) = {}"
  using \<^marker>\<open>provenance ai\<close> disj_pfx_are_disj_1[OF assms]
  by \<^marker>\<open>provenance ai\<close> (auto dest: in_set_butlastD)

lemma disj_pfx_is_complete:
  assumes "(None, l2_pfx) = (longest_disj_pfx l1 l2)"
  shows "set l1 \<inter> set l2 = {}"
  using assms
proof(induction l2 arbitrary: l1 l2_pfx)
  case Nil
  then show ?case
    by auto
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
    proof (clarsimp simp add: Let_def split: if_splits prod.splits option.splits, goal_cases)
      case 1
      then show ?case
        using \<^marker>\<open>provenance ai\<close> 1(2)[OF sym[OF 1(5)]] find_pfx_empty[OF 1(3)]
        by \<^marker>\<open>provenance ai\<close> auto
    next
      case 2
      then show ?case
        using \<^marker>\<open>provenance ai\<close> 2(2)[OF sym[OF 2(5)]] find_pfx_empty[OF 2(3)]
        by \<^marker>\<open>provenance ai\<close> auto
    next
      case 3
      then show ?case
        using \<^marker>\<open>provenance ai\<close> 3(2)[OF sym[OF 3(6)]] find_pfx_works_1[of a2 l1' "(=) a2"]
        by \<^marker>\<open>provenance ai\<close> auto
    next
      case 4
      then show ?case
        using \<^marker>\<open>provenance ai\<close> 4(2)[OF sym[OF 4(6)]] find_pfx_works_1[of a2 l1' "(=) a2"]
        by \<^marker>\<open>provenance ai\<close> auto
    qed
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
    using assms(1) disj_pref_append1
    by fastforce
  moreover have "alt_path M ((rev p1) @ pfx2)"
  proof(cases pfx2)
    case Nil
    then show ?thesis
      using snd_pfx_nempty pfxs_are_pfxs
      by auto
  next
    have "p1 \<noteq> []"
      using disj_pref_append1 first_pfx_nempty pfxs_are_pfxs
      by fastforce
    then have eqop_append: "edges_of_path (rev p1 @ pfx2) = edges_of_path (rev p1) @ edges_of_path (hd p1 # pfx2)"
      using \<^marker>\<open>provenance ai\<close> edges_of_path_append_3[of "rev p1" pfx2]
      by \<^marker>\<open>provenance ai\<close> (simp add: last_rev)
    case (Cons a' pfx2')
    then have "hd (edges_of_path p1) \<in> M" if "edges_of_path (rev p1) \<noteq> []"
      using alt_paths(1) that[unfolded edges_of_path_rev[symmetric]] \<open>p1 \<noteq> []\<close>
      by(auto simp add: neq_Nil_conv alt_list_step)
    then have "last (edges_of_path (rev p1)) \<in> M" if "edges_of_path (rev p1) \<noteq> []"
      using that Cons
      by(simp add: edges_of_path_rev[symmetric] last_rev)
    moreover have "alt_path M (rev p1)" if "edges_of_path (rev p1) \<noteq> []"
      using that odd_lens(1) alt_path_cons_odd(1)[OF odd_lens(1) alt_paths(1)]
      by (intro odd_alt_path_rev; simp add: edges_of_path_nempty)
    moreover have "alt_path M ((hd p1)#pfx2)"
    proof-
      obtain p2' where "p2 = pfx2 @ p2'"
        using disj_pref_append2[OF pfxs_are_pfxs]
        by rule
      have *:"butlast (hd p1 # pfx2) @ [last (hd p1 # pfx2)] = (hd p1 # pfx2)"
        by simp
      have **:"b # l1 @ a # l2 = b # (l1 @ [a]) @ l2" for l1 l2 a b
        by simp
      have "edges_of_path ((hd p1 # pfx2) @ p2') = edges_of_path (hd p1 # pfx2) @ edges_of_path (last (hd p1 # pfx2) # p2')" (is "?a = ?b")
        using edges_of_path_append_2[where ?p = "butlast (hd p1 # pfx2)" and ?p' = "last (hd p1 # pfx2) # p2'", unfolded *]
        by (simp add: Cons split: if_splits; simp add: **)
      then show ?thesis
        using alt_paths(2)
        by (subst conjunct1[OF alt_list_append_1[where ?l2.0 = "edges_of_path (last (hd p1 # pfx2) # p2')"]];
                                simp add: \<open>p2 = pfx2 @ p2'\<close>)
    qed
    ultimately show ?thesis
      using alternating_list_odd_last odd_pos
      by (fastforce simp: eqop_append alt_list_empty intro!: alt_list_append_3)+
  qed
  ultimately show ?thesis
    by \<^marker>\<open>provenance ai\<close> (simp flip: append_assoc)
qed

lemma pfxs_path:
  assumes
    pfxs_are_pfxs: "(Some pfx1, Some pfx2) = longest_disj_pfx p1 p2" and
    paths: "path G p1" "path G p2"
    "{hd p1, hd p2} \<in> G"
  shows "path G (rev (drop (length pfx1) p1) @ rev pfx1 @ pfx2)"
proof-
  have "(rev (drop (length pfx1) p1)) @ rev pfx1 = rev p1"
    using assms(1) disj_pref_append1
    by fastforce
  moreover have "path G ((rev p1) @ pfx2)"
  proof(cases pfx2)
    case Nil
    then show ?thesis
      using snd_pfx_nempty pfxs_are_pfxs
      by auto
  next
    case (Cons a' pfx2')
    have "p1 \<noteq> []"
      using disj_pref_append1 first_pfx_nempty pfxs_are_pfxs
      by fastforce
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
      using paths(3)
      by (intro path_append; simp add: last_rev edges_of_path_rev[symmetric])
  qed
  ultimately show ?thesis
    by \<^marker>\<open>provenance ai\<close> (simp flip: append_assoc)
qed

lemma pfxs_distinct:
  assumes
    pfxs_are_pfxs: "(Some pfx1, Some pfx2) = longest_disj_pfx p1 p2" and
    distinct: "distinct p1" "distinct p2"
    "p1 = pfx1 @ p'" "p2 = pfx2 @ p'"
  shows "distinct (rev (drop (length pfx1) p1) @ butlast (rev pfx1 @ pfx2))"
proof-
  have "(rev (drop (length pfx1) p1)) @ rev pfx1 = rev p1"
    using assms(1) disj_pref_append1
    by fastforce
  moreover have "butlast (rev pfx1 @ pfx2) = (rev pfx1 @ (butlast pfx2))"
    using \<^marker>\<open>provenance ai\<close> assms
    by \<^marker>\<open>provenance ai\<close> (simp add: butlast_append snd_pfx_nempty[OF pfxs_are_pfxs])
  moreover have "distinct ((rev p1) @ (butlast pfx2))"
    using \<^marker>\<open>provenance ai\<close> disj_pfx_are_disj_1[OF pfxs_are_pfxs] distinct
    by \<^marker>\<open>provenance ai\<close> (auto simp: distinct_append inter_distr_append
                         dest: in_set_butlastD distinct_butlast)
  ultimately show ?thesis
    by \<^marker>\<open>provenance ai\<close> (simp flip: append_assoc)
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
      using first_pfx_nempty pfxs_are_pfxs
      by auto
    moreover have "pfx2 \<noteq> []"
      using snd_pfx_nempty pfxs_are_pfxs
      by auto
    ultimately have "length (rev pfx1 @ pfx2) = 2"
      by (cases pfx1; cases pfx2; auto simp: le_simps(3))
    then obtain a1 a2 where a1a2: "pfx2 = [a2]" "pfx1 = [a1]"
      using \<open>rev pfx1 \<noteq> []\<close> \<open>pfx2 \<noteq> []\<close>
      by (cases pfx1; cases pfx2; auto)
    then have "a1 = a2"
      using pfx_common_end pfxs_are_pfxs
      by fastforce
    moreover have "a1 = hd p1"
      using a1a2 disj_pref_append1 pfxs_are_pfxs
      by fastforce
    moreover have "a2 = hd p2"
      using a1a2 disj_pref_append2 pfxs_are_pfxs
      by fastforce
    ultimately show False
      using hds_neq
      by auto
  qed
  moreover have "hd ((rev pfx1) @ pfx2) = last ((rev pfx1) @ pfx2)"
  proof-
    have "rev pfx1 \<noteq> []"
      using first_pfx_nempty pfxs_are_pfxs
      by auto
    moreover have "pfx2 \<noteq> []"
      using snd_pfx_nempty pfxs_are_pfxs
      by auto
    moreover have "hd (rev pfx1) = last pfx2" 
      using \<^marker>\<open>provenance ai\<close> hd_rev pfx_common_end pfxs_are_pfxs
      by \<^marker>\<open>provenance ai\<close> (simp add: hd_rev pfx_common_end[OF pfxs_are_pfxs])
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
      using \<^marker>\<open>provenance ai\<close> T1
      by \<^marker>\<open>provenance ai\<close> (auto simp: edges_of_path_length)
  next
    case F1: False
    then have "even (length pfx1)" "even (length pfx2)"
      using even_lens from_tree
      by auto
    then show ?thesis
      using \<^marker>\<open>provenance ai\<close> hds_neq from_tree
      by \<^marker>\<open>provenance ai\<close> (cases pfx1; cases pfx2; auto simp: edges_of_path_length)
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
    using first_pfx_nempty hd_append2 pfxs_are_pfxs
    by blast
  moreover have "(drop (length pfx1) p1) = p"
    by (simp add: from_tree(1))
  have pfx1_nempty: "pfx1 \<noteq> []"
    using pfxs_are_pfxs first_pfx_nempty snd_pfx_nempty
    by auto
  have pfx2_nempty: "pfx2 \<noteq> []"
    using pfxs_are_pfxs snd_pfx_nempty
    by auto

  have last_pfx1_eq: "last pfx1 = last pfx2"
    using pfx_common_end pfxs_are_pfxs
    by fastforce

  have last_pfxs_neq: "last (butlast pfx2) \<noteq> last (butlast pfx1)"
                      if "length pfx1 \<ge> 2" "length pfx2 \<ge> 2" "set (butlast pfx1) \<inter> set pfx2 = {}"
                      for pfx1 pfx2
    using \<^marker>\<open>provenance ai\<close> that last_in_set[of "butlast pfx1"] last_in_set[of "butlast pfx2"]
          in_set_butlastD[of "last (butlast pfx2)" pfx2]
    by \<^marker>\<open>provenance ai\<close> (auto simp: disjoint_iff length_greater_0_conv[symmetric] length_butlast)

  have p_nempty_even: False
    if "p \<noteq> []"
      and "length pfx1 \<ge> 2"
      and pfx2_nempty: "pfx2 \<noteq> []"
      and from_tree: "p1 = pfx1 @ p" "p2 = pfx2 @ p"
      and odd_lens: "odd (length p1)" "odd (length p2)"
      and last_pfx1_eq: "last pfx1 = last pfx2"
      and hds_neq: "hd p1 \<noteq> hd p2"
      and pfxs_disj: "set (butlast pfx1) \<inter> set pfx2 = {}"
      and distinct: "distinct p1"
      and alt_paths: "alt_path M (hd p2 # p1)" "alt_path M (hd p1 # p2)" "last p1 \<notin> Vs M"
      and odd_length: "odd (length (edges_of_path ((last pfx1) # p)))"
    for p1 pfx1 p2 pfx2::"'a list"
  proof-
    from \<open>length pfx1 \<ge> 2\<close> have pfx1_nempty: "pfx1 \<noteq> []"
      by auto
    have *: "alt_path M ((rev p) @ [last pfx1, last (butlast pfx1)])"
      if from_tree: "p1 = pfx1 @ p"
        and odd_lens: "odd (length p1)"
        and alt_paths: "alt_path (-M) p1" "last p1 \<notin> Vs M"
        and "length pfx1 \<ge> 2"
      for p1 pfx1::"'a list"
    proof-
      from \<open>length pfx1 \<ge> 2\<close> have "pfx1 \<noteq> []"
        by auto
      show ?thesis
      proof-
        have "last (edges_of_path ((last pfx1) # p)) = last (edges_of_path p1)"
          using \<^marker>\<open>provenance ai\<close> \<open>pfx1 \<noteq> []\<close> \<open>p \<noteq> []\<close>
          by \<^marker>\<open>provenance ai\<close> (cases p; simp add: from_tree(1) edges_of_path_append_3)
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
          by (intro odd_alt_path_rev alt_paths odd_lens; simp)
        have "\<exists>pfx1'. rev pfx1 = [last pfx1, last (butlast pfx1)] @ pfx1'"
        proof-
          have "length (rev pfx1) \<ge>  2"
            using \<open>length pfx1 \<ge>  2\<close>
            by simp
          then obtain a b pfx1'' where "rev pfx1 = a # b # pfx1''"
            by (simp only: numeral_2_eq_2 Suc_le_length_iff; fastforce)
          then have pfx1'': "pfx1 = ((rev pfx1'') @ [b]) @ [a]"
            by auto
          then have "a = last pfx1" "b = last (butlast pfx1)"
            by (simp only: butlast_snoc last_snoc)+
          then show ?thesis
            using pfx1''
            by fastforce
        qed
        then obtain pfx1' where "rev pfx1 = ([last pfx1, last (butlast pfx1)]) @ pfx1'"
          by \<^marker>\<open>provenance ai\<close> blast
        then have revp1_eq: "rev p1 = (rev p @ [last pfx1, last (butlast pfx1)]) @pfx1'"
          using from_tree(1)
          by auto
        have eop_cat: "edges_of_path ((rev p @ [last pfx1, last (butlast pfx1)]) @ pfx1') = (edges_of_path (rev p @ [last pfx1, last (butlast pfx1)]) @ (edges_of_path ((last (butlast pfx1)) # pfx1')))"
          using \<^marker>\<open>provenance ai\<close> edges_of_path_append_3[of "rev p @ [last pfx1, last (butlast pfx1)]" pfx1']
          by \<^marker>\<open>provenance ai\<close> simp
        show ?thesis
          using revp1_alt[unfolded revp1_eq eop_cat]
          by (rule conjunct1[OF alt_list_append_1])
      qed
    qed
    from alt_paths have alt_paths': "alt_path (-M) p1" "alt_path (-M) p2" "{hd p1, hd p2} \<notin> M"
      by(intro alt_path_cons_odd[where p = p1 and v = "hd p2"] alt_path_cons_odd[where p = p2 and v = "hd p1"] odd_lens; simp)+
    have alt_path_pfx1: "alt_path M (rev p @ [last pfx1, last (butlast pfx1)])"
      using *[OF from_tree(1) odd_lens(1) alt_paths'(1) alt_paths(3) \<open>length pfx1 \<ge> 2\<close>]
      by simp
    have "alt_path M (rev p @ [last pfx1])"
      using \<^marker>\<open>provenance ai\<close> alt_path_pfx1
      by \<^marker>\<open>provenance ai\<close> (auto dest: alt_list_append_1 simp: edges_of_path_snoc_2)
    moreover note odd_length
    ultimately have "last (edges_of_path ((rev p) @ [last pfx1])) \<notin> M"
      by \<^marker>\<open>provenance ai\<close> (auto dest: alternating_list_odd_last
                simp: odd_length length_edges_of_path_rev[of "(last pfx1) # p", simplified])
    have "even (length (edges_of_path ((rev p) @ [last pfx1, last (butlast pfx1)])))"
      using \<^marker>\<open>provenance ai\<close> odd_length
      by \<^marker>\<open>provenance ai\<close> (simp add: edges_of_path_snoc_2 length_edges_of_path_rev[of "(last pfx1) # p", simplified])
    then have "last (edges_of_path ((rev p) @ [last pfx1, last (butlast pfx1)])) \<in> M"
      using \<^marker>\<open>provenance ai\<close> alt_path_pfx1
      by \<^marker>\<open>provenance ai\<close> (auto dest: alternating_list_even_last simp: edges_of_path_snoc_2)
    then have last_pfx1_matched: "{last pfx1, last (butlast pfx1)} \<in> M"
      by \<^marker>\<open>provenance ai\<close> (simp add: edges_of_path_snoc_2)
    show ?thesis
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
          using \<^marker>\<open>provenance ai\<close> matching_unique_match[OF matching _ _ last_pfx2_matched last_pfx1_matched, of "last pfx1"]
                \<open>last pfx1 = last pfx2\<close>
          by \<^marker>\<open>provenance ai\<close> simp
      next
        have "last p2 \<notin> Vs M"
          using from_tree alt_paths(3) 
          by (simp add: \<open>p \<noteq> []\<close>)
        then have alt_path_pfx2: "alt_path M (rev p @ [last pfx2, last (butlast pfx2)])"
          using *[OF from_tree(2) odd_lens(2) alt_paths'(2) _ \<open>length pfx2 \<ge> 2\<close>]
          by simp
        moreover have "even (length (edges_of_path (rev p @ [last pfx2, last (butlast pfx2)])))"
          using \<^marker>\<open>provenance ai\<close> odd_length \<open>last pfx1 = last pfx2\<close>
          by \<^marker>\<open>provenance ai\<close> (simp add: edges_of_path_snoc_2
                                           length_edges_of_path_rev[of "(last pfx2) # p", simplified])
        moreover have "last (edges_of_path (rev p @ [last pfx2, last (butlast pfx2)])) = {last pfx2, last (butlast pfx2)}"
          by \<^marker>\<open>provenance ai\<close> (simp add: edges_of_path_snoc_2)
        ultimately have "{last pfx2, last (butlast pfx2)} \<in> M"
          using alternating_list_even_last edges_of_path_nempty
          by fastforce
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
        using \<^marker>\<open>provenance ai\<close> \<open>last (edges_of_path (rev p @ [last pfx1])) \<notin> M\<close> \<open>p \<noteq> []\<close> last_pfx1_eq
        by \<^marker>\<open>provenance ai\<close> (simp add: edges_of_path_snoc[symmetric] last_rev insert_commute)
      ultimately show ?thesis
        using alt_paths(2) \<open>length pfx1 \<ge> 2\<close> \<open>length pfx2 = 1\<close> \<open>p \<noteq> []\<close>
        by(auto simp add: from_tree numeral_2_eq_2 Suc_le_length_iff length_Suc_conv neq_Nil_conv alt_list_step alt_list_empty)
    qed
  qed

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
        using \<^marker>\<open>provenance ai\<close> p_nempty_even[OF p_nempty len_pf1_ge_2 pfx2_nempty from_tree odd_lens \<open>last pfx1 = last pfx2\<close> hds_neq \<open>set (butlast pfx1) \<inter> set pfx2 = {}\<close> distinct(1) alt_paths(1,2,3)]
        by \<^marker>\<open>provenance ai\<close> (auto simp: calculation \<open>drop (length pfx1) p1 = p\<close> hd_rev pfx1_nempty
                                       length_edges_of_path_rev[of "last pfx1 # p", simplified])
    next
      case False
      then have len_pf1_le_1: "length pfx1 \<le> 1"
        by auto
      show ?thesis
      proof(cases "2 \<le> length pfx2")
        case len_pf2_ge_2: True
        have "set (butlast pfx2) \<inter> set pfx1 = {}"
          using disj_pfx_are_disj_1 pfxs_are_pfxs
          by fastforce
        have "{hd p2, hd p1} \<notin> M"
          by(intro alt_path_cons_odd alt_paths(1) odd_lens)
        have "last p2 \<notin> Vs M"
          using assms(6) from_tree(1) from_tree(2) p_nempty
          by auto
        have "last pfx2 = last pfx1"
          by (simp add: last_pfx1_eq)
        show ?thesis
          using \<^marker>\<open>provenance ai\<close> p_nempty_even[OF p_nempty len_pf2_ge_2 pfx1_nempty from_tree(2,1) odd_lens(2,1) \<open>last pfx2 = last pfx1\<close> hds_neq[symmetric] \<open>set (butlast pfx2) \<inter> set pfx1 = {}\<close> distinct(2) alt_paths(2,1) \<open>last p2 \<notin> Vs M\<close>]
          by \<^marker>\<open>provenance ai\<close> (auto simp: calculation \<open>drop (length pfx1) p1 = p\<close> hd_rev pfx1_nempty last_pfx1_eq
                                         length_edges_of_path_rev[of "last pfx2 # p", simplified])
      next
        case len_pf2_le_1: False
        then show ?thesis
          using \<^marker>\<open>provenance ai\<close> from_tree hds_neq last_pfx1_eq len_pf1_le_1 pfx1_nempty pfx2_nempty
          by \<^marker>\<open>provenance ai\<close> (cases pfx1; cases pfx2; auto simp: Suc_le_eq length_greater_0_conv)
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
    using assms(1) disj_pref_append1
    by fastforce
  then have " (rev (drop (length pfx1) p1) @ rev pfx1 @ pfx2) = rev p1 @ pfx2"
    by auto
  moreover have "p1 \<noteq> []"
    using first_pfx_nempty from_tree(1) pfxs_are_pfxs
    by auto
  ultimately have "hd (rev (drop (length pfx1) p1) @ rev pfx1 @ pfx2) = last p1"
    by (simp add: \<open>rev (drop (length pfx1) p1) @ rev pfx1 @ pfx2 = rev p1 @ pfx2\<close> hd_rev)
  then show ?thesis
    unfolding match_blossom_def
    by
       (intro conjI pfxs_even_stem'[OF assms(1-5) _ hds_neq odd_lens distinct matching]
              pfxs_odd_cycle'[OF pfxs_are_pfxs from_tree alt_paths'(1,2,3) hds_neq odd_lens]
              pfxs_distinct[OF pfxs_are_pfxs distinct from_tree]
              pfxs_alt_path'[OF pfxs_are_pfxs alt_paths(1,2)]
              alt_paths(3) odd_lens;
              simp add: assms(6))
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
    using \<^marker>\<open>provenance ai\<close> alt_paths(3,5) nempty
    by \<^marker>\<open>provenance ai\<close> (cases p1; cases "tl p1"; auto dest: edges_are_Vs)
  then have "last (edges_of_path p1) \<notin> M"
    using \<^marker>\<open>provenance ai\<close> alt_paths
    by \<^marker>\<open>provenance ai\<close> (auto dest: last_edge_in_last_vert_in)
  then have "alt_path M (rev p1)"
    using alt_paths(1) alt_list_rev
    by (simp add: \<open>2 \<le> length p1\<close> even_alt_path_rev even_lens(1))
  moreover have "last (edges_of_path (rev p1)) \<notin> M"
    using \<^marker>\<open>provenance ai\<close> alt_paths(1) \<open>2 \<le> length p1\<close> edges_of_path_nempty[of p1]
    by \<^marker>\<open>provenance ai\<close> (cases "edges_of_path p1"; simp add: edges_of_path_rev[symmetric] alt_list_step)
  moreover have "alt_path (-M) (hd p1 # p2)"
    using alt_paths(2,5)
    by(cases p2; auto simp add: alt_list_step alt_list_empty)
  moreover have "edges_of_path ((rev p1) @ p2) = (edges_of_path (rev p1)) @ (edges_of_path (hd p1 # p2))"
    using \<^marker>\<open>provenance ai\<close> nempty(1) edges_of_path_append_3[of "rev p1" p2]
    by \<^marker>\<open>provenance ai\<close> (simp add: last_rev)
  ultimately have "alt_path M ((rev p1) @ p2)"
    using even_lens(1) edges_of_path_length'[OF nempty(1)]
    by (simp, intro alt_list_append_2; auto)
  moreover have " 2 \<le> length (rev p1 @ p2)"
    using \<open>2 \<le> length p1\<close>
    by auto
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
    using alt_paths(1) alt_path_cons_odd(1) odd_lens(1)
    by fastforce
  have "last (edges_of_path p1) \<notin> M"
    using \<^marker>\<open>provenance ai\<close> alt_paths True
    by \<^marker>\<open>provenance ai\<close> (auto dest: last_edge_in_last_vert_in)
  moreover have "(edges_of_path p1) \<noteq> []"
    using True
    by (simp add: edges_of_path_nempty)
  ultimately have "last (edges_of_path (rev p1)) \<in> M"
    using \<^marker>\<open>provenance ai\<close> \<open>alt_path (-M) p1\<close>
    by \<^marker>\<open>provenance ai\<close> (cases "edges_of_path p1"; simp add: edges_of_path_rev[symmetric] alt_list_step)
  moreover have "edges_of_path ((rev p1) @ p2) = (edges_of_path (rev p1)) @ (edges_of_path (hd p1 # p2))"
    using \<^marker>\<open>provenance ai\<close> nempty(1) edges_of_path_append_3[of "rev p1" p2]
    by \<^marker>\<open>provenance ai\<close> (simp add: last_rev)
  moreover have "alt_path M (rev p1)"
    using alt_paths(1) alt_list_rev \<open>alt_path (-M) p1\<close>
    by (simp add: True odd_alt_path_rev odd_lens(1))
  ultimately have "alt_path M ((rev p1) @ p2)"
    using alt_paths(2)
    by (simp, intro alt_list_append_3; auto dest: alternating_list_odd_last)
  moreover have " 2 \<le> length (rev p1 @ p2)"
    using \<open>2 \<le> length p1\<close>
    by auto
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
    using \<^marker>\<open>provenance ai\<close> odd_lens(1) nempty(1) edges_of_path_length' edges_of_path_nempty
    by \<^marker>\<open>provenance ai\<close> (cases p1; cases "tl p1"; auto)
  have "alt_path M ((rev p1) @ p2)"
    using alt_paths(2)
    by (subst \<open>p1 = [hd p1]\<close>; simp)
  moreover have " 2 \<le> length (rev p1 @ p2)"
    using \<^marker>\<open>provenance ai\<close> odd_lens(2) False nempty
    by \<^marker>\<open>provenance ai\<close> (cases p1; cases p2; auto simp: edges_of_path_length' dest: odd_pos)
  moreover have "hd (rev p1 @ p2) \<notin> Vs M"
    by (simp add: assms(6) hd_rev nempty(1))
  moreover have "last (rev p1 @ p2) \<notin> Vs M"
    by (simp add: assms(7) nempty(2))
  ultimately show ?thesis
    unfolding matching_augmenting_path_def
    by simp
qed

locale match = graph_abs G for G+ 
  fixes M
  assumes matching: "matching M" "M \<subseteq> G"

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

end

