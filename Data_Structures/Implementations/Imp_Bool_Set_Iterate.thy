theory Imp_Bool_Set_Iterate
  imports
    Imp_Bool_Set
    Fixed_Univ_Set_Iterate_Imp
begin

section \<open>Iterating over Boolean Arrays\<close>

text \<open>The iterator carries the array, its length and the next member. Advancing scans the array
      for the next member. The elements are visited in increasing order. Nothing is allocated.\<close>

partial_function (heap) xset_scan :: "bool array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "xset_scan a l i =
     (if i < l then do { b \<leftarrow> Array.nth a i; if b then return i else xset_scan a l (Suc i) }
      else return i)"

definition "xset_it_init a = do { l \<leftarrow> Array.len a; i \<leftarrow> xset_scan a l 0; return (a, l, i) }"

definition "xset_it_has_next it = (case it of (a, l, i) \<Rightarrow> return (i < l))"

definition "xset_it_next it = (case it of (a, l, i) \<Rightarrow>
   do { j \<leftarrow> xset_scan a l (Suc i); return (i, (a, l, j)) })"

definition "xset_is_it n X p xs it = (case it of (a, l, i) \<Rightarrow>
   xset_assn n X p *
   \<up>(a = p \<and> l = n \<and> i \<le> n \<and> (i < n \<longrightarrow> i \<in> X) \<and> xs = filter (\<lambda>j. j \<in> X) [i..<n]))"

lemma xset_scan_rule:
  "i \<le> n \<Longrightarrow>
   <xset_assn n X p> xset_scan p n i
   <\<lambda>j. xset_assn n X p * \<up>(i \<le> j \<and> j \<le> n \<and> (j < n \<longrightarrow> j \<in> X) \<and>
                         filter (\<lambda>k. k \<in> X) [i..<n] = filter (\<lambda>k. k \<in> X) [j..<n])>"
proof(induction "n - i" arbitrary: i)
  case 0
  hence "i = n" by simp
  thus ?case by (subst xset_scan.simps) sep_auto
next
  case (Suc d)
  hence i: "i < n" by simp
  have split: "[i..<n] = i # [Suc i..<n]" using i by (simp add: upt_conv_Cons)
  have d: "d = n - Suc i" using Suc(2) by simp
  note IH = Suc(1)[OF d Suc_leI[OF i]]
  show ?case
    using i
    by (cases "i \<in> X")
       (subst xset_scan.simps, sep_auto heap: IH xset_memb_rule simp: split)+
qed

lemma sorted_list_of_xset:
  assumes "X \<subseteq> {..<n}"
  shows "sorted_list_of_set X = filter (\<lambda>k. k \<in> X) [0..<n]"
proof-
  have "finite X" using assms finite_subset by blast
  thus ?thesis
    using assms by (intro sorted_distinct_set_unique) (auto simp: sorted_wrt_filter)
qed

lemma xset_len_rule: "<xset_assn n X p> Array.len p <\<lambda>r. xset_assn n X p * \<up>(r = n)>"
  unfolding xset_assn_def by sep_auto

lemma xset_it_init_rule:
  "X \<subseteq> {..<n} \<Longrightarrow>
   <xset_assn n X p> xset_it_init p <xset_is_it n X p (sorted_list_of_set (id X))>"
  unfolding xset_it_init_def xset_is_it_def
  by (sep_auto heap: xset_len_rule xset_scan_rule simp: sorted_list_of_xset)

lemma xset_it_next_rule:
  "<xset_is_it n X p (x # xs) it> xset_it_next it <\<lambda>(y, it'). xset_is_it n X p xs it' * \<up>(y = x)>"
proof-
  obtain a l i where it: "it = (a, l, i)" by (cases it) auto
  show ?thesis
    unfolding it xset_it_next_def xset_is_it_def prod.case
  proof(rule ht_extract_pre_pure(1), elim conjE)
    assume a: "a = p" "l = n" "i \<le> n" "i < n \<longrightarrow> i \<in> X" "x # xs = filter (\<lambda>j. j \<in> X) [i..<n]"
    hence i: "i < n" by (cases "i < n") auto
    hence split: "[i..<n] = i # [Suc i..<n]" by (simp add: upt_conv_Cons)
    have x: "x = i" and xs: "xs = filter (\<lambda>j. j \<in> X) [Suc i..<n]"
      using a(4,5) i by (simp_all add: split)
    show "<xset_assn n X p> xset_scan a l (Suc i) \<bind> (\<lambda>j. return (i, a, l, j))
          <\<lambda>(y, it'). (case it' of (a, l, i) \<Rightarrow>
             xset_assn n X p * \<up>(a = p \<and> l = n \<and> i \<le> n \<and> (i < n \<longrightarrow> i \<in> X) \<and>
                                   xs = filter (\<lambda>j. j \<in> X) [i..<n])) * \<up>(y = x)>"
      using i by (sep_auto heap: xset_scan_rule simp: a(1,2) x xs)
  qed
qed

lemma xset_it_has_next_rule:
  "<xset_is_it n X p xs it> xset_it_has_next it <\<lambda>r. xset_is_it n X p xs it * \<up>(r \<longleftrightarrow> xs \<noteq> [])>"
proof-
  obtain a l i where it: "it = (a, l, i)" by (cases it) auto
  have "\<lbrakk>i \<le> n; i < n \<longrightarrow> i \<in> X\<rbrakk> \<Longrightarrow> (i < n) = (filter (\<lambda>j. j \<in> X) [i..<n] \<noteq> [])"
    by (cases "i < n") (auto simp: upt_conv_Cons filter_empty_conv)
  thus ?thesis
    unfolding it xset_it_has_next_def xset_is_it_def
    by sep_auto
qed

lemma xset_quit_iteration: "xset_is_it n X p xs it \<Longrightarrow>\<^sub>A xset_assn n X p"
  unfolding xset_is_it_def by (cases it) sep_auto

lemma xset_fixed_univ_set_iterate_imp:
  "fixed_univ_set_iterate_imp {..<n} (\<lambda> X. X \<subseteq> {..<n}) id {} insert (\<lambda> x X. X - {x})
     (\<lambda> X x. x \<in> X) (xset_assn n) (Array.new n False) xset_insert_imp xset_delete_imp
     xset_isin_imp sorted_list_of_set (xset_is_it n) xset_it_init xset_it_has_next xset_it_next"
  by (intro fixed_univ_set_iterate_imp.intro fixed_univ_set_iterate_imp_axioms.intro
            xset_fixed_univ_set_imp sorted_list_of_set_order xset_it_init_rule xset_it_next_rule
            xset_it_has_next_rule xset_quit_iteration)

end
