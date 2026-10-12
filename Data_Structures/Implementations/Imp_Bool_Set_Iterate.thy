theory Imp_Bool_Set_Iterate
  imports
    Imp_Bool_Set
    Fixed_Univ_Set_Iterate_Imp
begin

section \<open>Iterating over Boolean Arrays\<close>

text \<open>The iterator carries the array, its length and the next member. Advancing scans the array
      for the next member. The elements are visited in increasing order. Nothing is allocated.\<close>

partial_function (heap) bool_array_set_scan :: "bool array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "bool_array_set_scan a l i =
     (if i < l then do { b \<leftarrow> Array.nth a i; if b then return i else bool_array_set_scan a l (Suc i) }
      else return i)"

definition "bool_array_set_it_init a = do { l \<leftarrow> Array.len a; i \<leftarrow> bool_array_set_scan a l 0; return (a, l, i) }"

definition "bool_array_set_it_has_next it = (case it of (a, l, i) \<Rightarrow> return (i < l))"

definition "bool_array_set_it_next it = (case it of (a, l, i) \<Rightarrow>
   do { j \<leftarrow> bool_array_set_scan a l (Suc i); return (i, (a, l, j)) })"

definition "bool_array_set_is_it n X p xs it = (case it of (a, l, i) \<Rightarrow>
   bool_array_set_assn n X p *
   \<up>(a = p \<and> l = n \<and> i \<le> n \<and> (i < n \<longrightarrow> i \<in> X) \<and> xs = filter (\<lambda>j. j \<in> X) [i..<n]))"

lemma bool_array_set_scan_rule:
  "i \<le> n \<Longrightarrow>
   <bool_array_set_assn n X p> bool_array_set_scan p n i
   <\<lambda>j. bool_array_set_assn n X p * \<up>(i \<le> j \<and> j \<le> n \<and> (j < n \<longrightarrow> j \<in> X) \<and>
                         filter (\<lambda>k. k \<in> X) [i..<n] = filter (\<lambda>k. k \<in> X) [j..<n])>"
proof(induction "n - i" arbitrary: i)
  case 0
  hence "i = n" by simp
  thus ?case by (subst bool_array_set_scan.simps) sep_auto
next
  case (Suc d)
  hence i: "i < n" by simp
  have split: "[i..<n] = i # [Suc i..<n]" using i by (simp add: upt_conv_Cons)
  have d: "d = n - Suc i" using Suc(2) by simp
  note IH = Suc(1)[OF d Suc_leI[OF i]]
  show ?case
    using i
    by (cases "i \<in> X")
       (subst bool_array_set_scan.simps, sep_auto heap: IH bool_array_set_memb_rule simp: split)+
qed

lemma sorted_list_of_xset:
  assumes "X \<subseteq> {..<n}"
  shows "sorted_list_of_set X = filter (\<lambda>k. k \<in> X) [0..<n]"
proof-
  have "finite X" using assms finite_subset by blast
  thus ?thesis
    using assms by (intro sorted_distinct_set_unique) (auto simp: sorted_wrt_filter)
qed

lemma bool_array_set_len_rule: "<bool_array_set_assn n X p> Array.len p <\<lambda>r. bool_array_set_assn n X p * \<up>(r = n)>"
  unfolding bool_array_set_assn_def by sep_auto

lemma bool_array_set_it_init_rule:
  "X \<subseteq> {..<n} \<Longrightarrow>
   <bool_array_set_assn n X p> bool_array_set_it_init p <bool_array_set_is_it n X p (sorted_list_of_set (id X))>"
  unfolding bool_array_set_it_init_def bool_array_set_is_it_def
  by (sep_auto heap: bool_array_set_len_rule bool_array_set_scan_rule simp: sorted_list_of_xset)

lemma bool_array_set_it_next_rule:
  "<bool_array_set_is_it n X p (x # xs) it> bool_array_set_it_next it <\<lambda>(y, it'). bool_array_set_is_it n X p xs it' * \<up>(y = x)>"
proof-
  obtain a l i where it: "it = (a, l, i)" by (cases it) auto
  show ?thesis
    unfolding it bool_array_set_it_next_def bool_array_set_is_it_def prod.case
  proof(rule ht_extract_pre_pure(1), elim conjE)
    assume a: "a = p" "l = n" "i \<le> n" "i < n \<longrightarrow> i \<in> X" "x # xs = filter (\<lambda>j. j \<in> X) [i..<n]"
    hence i: "i < n" by (cases "i < n") auto
    hence split: "[i..<n] = i # [Suc i..<n]" by (simp add: upt_conv_Cons)
    have x: "x = i" and xs: "xs = filter (\<lambda>j. j \<in> X) [Suc i..<n]"
      using a(4,5) i by (simp_all add: split)
    show "<bool_array_set_assn n X p> bool_array_set_scan a l (Suc i) \<bind> (\<lambda>j. return (i, a, l, j))
          <\<lambda>(y, it'). (case it' of (a, l, i) \<Rightarrow>
             bool_array_set_assn n X p * \<up>(a = p \<and> l = n \<and> i \<le> n \<and> (i < n \<longrightarrow> i \<in> X) \<and>
                                   xs = filter (\<lambda>j. j \<in> X) [i..<n])) * \<up>(y = x)>"
      using i by (sep_auto heap: bool_array_set_scan_rule simp: a(1,2) x xs)
  qed
qed

lemma bool_array_set_it_has_next_rule:
  "<bool_array_set_is_it n X p xs it> bool_array_set_it_has_next it <\<lambda>r. bool_array_set_is_it n X p xs it * \<up>(r \<longleftrightarrow> xs \<noteq> [])>"
proof-
  obtain a l i where it: "it = (a, l, i)" by (cases it) auto
  have "\<lbrakk>i \<le> n; i < n \<longrightarrow> i \<in> X\<rbrakk> \<Longrightarrow> (i < n) = (filter (\<lambda>j. j \<in> X) [i..<n] \<noteq> [])"
    by (cases "i < n") (auto simp: upt_conv_Cons filter_empty_conv)
  thus ?thesis
    unfolding it bool_array_set_it_has_next_def bool_array_set_is_it_def
    by sep_auto
qed

lemma bool_array_set_quit_iteration: "bool_array_set_is_it n X p xs it \<Longrightarrow>\<^sub>A bool_array_set_assn n X p"
  unfolding bool_array_set_is_it_def by (cases it) sep_auto

lemma bool_array_set_fixed_univ_set_iterate_imp:
  "fixed_univ_set_iterate_imp {..<n} (\<lambda> X. X \<subseteq> {..<n}) id {} insert (\<lambda> x X. X - {x})
     (\<lambda> X x. x \<in> X) (bool_array_set_assn n) (Array.new n False) bool_array_set_insert_imp bool_array_set_delete_imp
     bool_array_set_isin_imp sorted_list_of_set (bool_array_set_is_it n) bool_array_set_it_init bool_array_set_it_has_next bool_array_set_it_next"
  by (intro fixed_univ_set_iterate_imp.intro fixed_univ_set_iterate_imp_axioms.intro
            bool_array_set_fixed_univ_set_imp sorted_list_of_set_order bool_array_set_it_init_rule bool_array_set_it_next_rule
            bool_array_set_it_has_next_rule bool_array_set_quit_iteration)

end
