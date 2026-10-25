(*
  Author: Mohammad Abdulaziz
*)

theory Blossom_Misc
  imports Undirected_Set_Graphs.Paths
begin

provenance human

subsection \<open>Misc\<close>
       
lemma set_tl:
  shows "set (tl l) \<subseteq> set l"
  by (induction l) auto

lemma construct_distinct_path:
  assumes
    disj_paths: "set p1 \<inter> set p2 = {}" and
    distinct: "distinct p1" "distinct p2"
  shows "distinct ((rev p1) @ p2)"
  using assms
  by simp

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
    by \<^marker>\<open>provenance ai\<close> (rule Suc_le_length_iff[THEN iffD1])
  then show "\<exists>x ys. xs = ys @ [x] \<and> n \<le> length ys"
    by auto
next
  assume "\<exists>x ys. xs = ys @ [x] \<and> n \<le> length ys"
  then have "\<exists>x ys. rev xs = x # ys \<and> n \<le> length ys"
    by force
  then have "Suc n \<le> length (rev xs)"
    by \<^marker>\<open>provenance ai\<close> (rule Suc_le_length_iff[THEN iffD2])
  then show  "Suc n \<le> length xs"
    by auto
qed

lemma set_butlast_tl:
  assumes "l \<noteq> []" "hd l = last l"
  shows "set (butlast l) = set (tl l)"
proof \<^marker>\<open>provenance ai\<close>(cases l)
  case Nil
  then show ?thesis
    using assms
    by simp
next
  case (Cons x xs)
  then show ?thesis
    using assms
    by (cases xs rule: rev_cases; auto)
qed

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
        by (intro sucsuc; simp)
      ultimately show ?thesis
        using sucsuc(3,4)
        by (cases zs''; simp add: cons1 doubleton_eq_iff)
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
proof(induction xs)
  case (Cons x xs)
  then show ?case
    by \<^marker>\<open>provenance ai\<close> (cases "n < length (xs @ ys)"; cases ys; auto)
qed simp

lemma dist_neq_split_2: "(x \<noteq> z \<and> dist_neq 1 (xs1 @ [x, y]) \<and> dist_neq (Suc 0) (y # z # xs2))
                       \<Longrightarrow> dist_neq (Suc 0) (xs1 @ x # y # z # xs2)"
proof(induction xs1)
  case (Cons a xs1)
  then show ?case
    by (cases xs1; auto simp add: hd_drop_conv_nth hd_append)
qed auto

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
    by (subst (asm) *; simp add: append.assoc)
  moreover have "dist_neq (Suc 0) (y # z # xs2)"
    using assms(3)
    by (simp add: append.assoc)
  ultimately show ?thesis
    by (subst *; simp add: append.assoc; intro dist_neq_split_2 conjI; simp)
qed

lemma Suc_le_length_iff_snoc: "(Suc n \<le> length xs) = (\<exists>x ys. xs = ys @ [x] \<and> n \<le> length ys)"
  using Suc_le_length_iff[of _ "rev xs", unfolded length_rev]
  by auto

end