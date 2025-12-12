theory Misc
  imports "Undirected_Set_Graphs.Undirected_Set_Graphs"
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

end