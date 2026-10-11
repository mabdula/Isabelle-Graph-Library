theory Imp_Array_Move_To_Front_List
  imports
    Array_Linked_Lists
    Imp_Array_Map
    Fixed_Univ_List_Specs_Imp
begin

section \<open>Distinct Lists with Move-to-Front as Doubly-Linked Lists in Arrays\<close>

text \<open>A distinct list over the elements \<open>{..<n}\<close>, stored in a successor and a predecessor array
      over the elements and a reference to the first element, all allocated once. Pushing to the
      front, moving to the front, and reading the first element and a successor take a constant
      number of array accesses. The functional model is the reference and the two arrays as
      functions.\<close>

type_synonym amtf = "nat option \<times> (nat \<Rightarrow> nat option) \<times> (nat \<Rightarrow> nat option)"

definition amtf_empty :: amtf where
  "amtf_empty = (None, (\<lambda> _. None), (\<lambda> _. None))"

definition amtf_push_front :: "amtf \<Rightarrow> nat \<Rightarrow> amtf" where
  "amtf_push_front = (\<lambda> (F, NX, PV) x.
     (Some x, NX(x := F), (case F of None \<Rightarrow> PV(x := None) | Some y \<Rightarrow> (PV(x := None))(y := Some x))))"

definition amtf_remove :: "amtf \<Rightarrow> nat \<Rightarrow> amtf" where
  "amtf_remove = (\<lambda> (F, NX, PV) x.
     ((case PV x of None \<Rightarrow> NX x | Some _ \<Rightarrow> F), remove_nx NX PV x, remove_pv NX PV x))"

definition amtf_move_to_front :: "amtf \<Rightarrow> nat \<Rightarrow> amtf" where
  "amtf_move_to_front L x = amtf_push_front (amtf_remove L x) x"

definition amtf_first :: "amtf \<Rightarrow> nat option" where
  "amtf_first = (\<lambda> (F, NX, PV). F)"

definition amtf_next :: "amtf \<Rightarrow> nat \<Rightarrow> nat option" where
  "amtf_next = (\<lambda> (F, NX, PV) x. NX x)"

subsection \<open>Abstraction\<close>

definition amtf_good :: "nat \<Rightarrow> amtf \<Rightarrow> nat list \<Rightarrow> bool" where
  "amtf_good n L xs = (case L of (F, NX, PV) \<Rightarrow>
     seg NX PV None xs None \<and> F = first_opt xs \<and> distinct xs \<and> set xs \<subseteq> {..<n})"

definition "amtf_invar n L = (\<exists> xs. amtf_good n L xs)"

definition "amtf_abstract n L = (SOME xs. amtf_good n L xs)"

lemma amtf_good_unique: "\<lbrakk>amtf_good n L xs; amtf_good n L ys\<rbrakk> \<Longrightarrow> xs = ys"
  by (cases L) (auto simp add: amtf_good_def intro: seg_unique)

lemma amtf_abstract_good: "amtf_good n L xs \<Longrightarrow> amtf_abstract n L = xs"
  unfolding amtf_abstract_def using amtf_good_unique by blast

lemma amtf_good_set: "amtf_good n L xs \<Longrightarrow> distinct xs \<and> set xs \<subseteq> {..<n}"
  by (cases L) (simp add: amtf_good_def)

lemma amtf_push_front_good:
  assumes "amtf_good n L xs" "x < n" "x \<notin> set xs"
  shows "amtf_good n (amtf_push_front L x) (x # xs)"
proof-
  obtain F NX PV where L: "L = (F, NX, PV)"
    by (cases L) auto
  have I: "seg NX PV None xs None" "F = first_opt xs" "distinct xs" "set xs \<subseteq> {..<n}"
    using assms(1) by (simp_all add: amtf_good_def L)
  have "amtf_push_front L x = (Some x, push_nx NX x xs, push_pv PV x xs)"
    using I(2) by (cases xs) (simp_all add: amtf_push_front_def L push_nx_def push_pv_def)
  thus ?thesis
    using seg_push_front[OF I(1,3) assms(3)] I(3,4) assms(2,3) by (simp add: amtf_good_def)
qed

lemma amtf_remove_good:
  assumes "amtf_good n L xs" "x \<in> set xs"
  shows "amtf_good n (amtf_remove L x) (remove1 x xs)"
proof-
  obtain F NX PV where L: "L = (F, NX, PV)"
    by (cases L) auto
  have I: "seg NX PV None xs None" "F = first_opt xs" "distinct xs" "set xs \<subseteq> {..<n}"
    using assms(1) by (simp_all add: amtf_good_def L)
  obtain as bs where xs: "xs = as @ x # bs"
    using split_list[OF assms(2)] by blast
  have rm: "remove1 x xs = as @ bs"
    using I(3) xs by (simp add: remove1_append)
  note m = seg_mid[OF I(1)[unfolded xs]]
  have F': "(case PV x of None \<Rightarrow> NX x | Some _ \<Rightarrow> F) = first_opt (as @ bs)"
    using m(1,2) I(2) xs by (cases as rule: rev_cases) (auto simp add: first_opt_append last_opt_def)
  show ?thesis
    using seg_remove[OF I(1)[unfolded xs] I(3)[unfolded xs]] F' I(3,4) rm xs
    by (auto simp add: amtf_good_def amtf_remove_def L)
qed

lemma amtf_fixed_univ_list:
  "fixed_univ_list {..<n} (amtf_invar n) (amtf_abstract n) amtf_empty amtf_push_front
     amtf_move_to_front amtf_first amtf_next"
proof(unfold_locales, goal_cases)
  case (1 L)
  then obtain xs where "amtf_good n L xs"
    by (auto simp add: amtf_invar_def)
  thus ?case
    using amtf_abstract_good by (cases L) (auto simp add: amtf_good_def)
next
  case 2
  have "amtf_good n amtf_empty []"
    by (simp add: amtf_good_def amtf_empty_def)
  thus ?case
    by (auto simp add: amtf_invar_def)
next
  case 3
  have "amtf_good n amtf_empty []"
    by (simp add: amtf_good_def amtf_empty_def)
  thus ?case
    by (rule amtf_abstract_good)
next
  case (4 L x)
  then obtain xs where xs: "amtf_good n L xs"
    by (auto simp add: amtf_invar_def)
  have x: "x < n" "x \<notin> set xs"
    using 4(2,3) amtf_abstract_good[OF xs] by simp_all
  show ?case
    unfolding amtf_invar_def using amtf_push_front_good[OF xs x] by blast
next
  case (5 L x)
  then obtain xs where xs: "amtf_good n L xs"
    by (auto simp add: amtf_invar_def)
  have x: "x < n" "x \<notin> set xs"
    using 5(2,3) amtf_abstract_good[OF xs] by simp_all
  show ?case
    using amtf_abstract_good[OF amtf_push_front_good[OF xs x]] amtf_abstract_good[OF xs] by simp
next
  case (6 L x)
  then obtain xs where xs: "amtf_good n L xs"
    by (auto simp add: amtf_invar_def)
  have x: "x \<in> set xs"
    using 6(2) amtf_abstract_good[OF xs] by simp
  note R = amtf_remove_good[OF xs x]
  have "x < n" "x \<notin> set (remove1 x xs)"
    using x amtf_good_set[OF xs] by auto
  note P = amtf_push_front_good[OF R this]
  show ?case
    unfolding amtf_invar_def amtf_move_to_front_def using P by blast
next
  case (7 L x)
  then obtain xs where xs: "amtf_good n L xs"
    by (auto simp add: amtf_invar_def)
  have x: "x \<in> set xs"
    using 7(2) amtf_abstract_good[OF xs] by simp
  note R = amtf_remove_good[OF xs x]
  have "x < n" "x \<notin> set (remove1 x xs)"
    using x amtf_good_set[OF xs] by auto
  note P = amtf_push_front_good[OF R this]
  show ?case
    using amtf_abstract_good[OF xs] amtf_abstract_good[OF P] by (simp add: amtf_move_to_front_def)
next
  case (8 L)
  then obtain xs where xs: "amtf_good n L xs"
    by (auto simp add: amtf_invar_def)
  thus ?case
    using amtf_abstract_good[OF xs] by (cases L; cases xs) (auto simp add: amtf_good_def amtf_first_def)
next
  case (9 L xs x ys)
  then obtain zs where zs: "amtf_good n L zs"
    by (auto simp add: amtf_invar_def)
  obtain F NX PV where L: "L = (F, NX, PV)"
    by (cases L) auto
  have "seg NX PV None (xs @ x # ys) None"
    using zs 9(2) amtf_abstract_good[OF zs] by (simp add: amtf_good_def L)
  thus ?case
    using seg_mid(2) by (cases ys) (fastforce simp add: amtf_next_def L)+
qed

section \<open>The Arrays\<close>

type_synonym amtfi = "nat option ref \<times> nat option array \<times> nat option array"

fun amtf_assn :: "nat \<Rightarrow> amtf \<Rightarrow> amtfi \<Rightarrow> assn" where
  "amtf_assn n (F, NX, PV) (Fr, NXa, PVa) = Fr \<mapsto>\<^sub>r F * xmap_assn n NX NXa * xmap_assn n PV PVa"

definition amtf_empty_imp :: "nat \<Rightarrow> amtfi Heap" where
  "amtf_empty_imp n = do {
     Fr \<leftarrow> ref None; NXa \<leftarrow> Array.new n None; PVa \<leftarrow> Array.new n None;
     return (Fr, NXa, PVa) }"

definition amtf_push_front_imp :: "amtfi \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "amtf_push_front_imp = (\<lambda> (Fr, NXa, PVa) x. do {
     f \<leftarrow> !Fr;
     _ \<leftarrow> Array.upd x f NXa;
     _ \<leftarrow> Array.upd x None PVa;
     _ \<leftarrow> (case f of None \<Rightarrow> return PVa | Some y \<Rightarrow> Array.upd y (Some x) PVa);
     Fr := Some x })"

definition amtf_remove_imp :: "amtfi \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "amtf_remove_imp = (\<lambda> (Fr, NXa, PVa) x. do {
     p \<leftarrow> Array.nth PVa x;
     q \<leftarrow> Array.nth NXa x;
     _ \<leftarrow> (case p of None \<Rightarrow> Fr := q | Some a \<Rightarrow> do { _ \<leftarrow> Array.upd a q NXa; return () });
     _ \<leftarrow> (case q of None \<Rightarrow> return PVa | Some b \<Rightarrow> Array.upd b p PVa);
     return () })"

definition amtf_move_to_front_imp :: "amtfi \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "amtf_move_to_front_imp Li x = do { amtf_remove_imp Li x; amtf_push_front_imp Li x }"

definition amtf_first_imp :: "amtfi \<Rightarrow> nat option Heap" where
  "amtf_first_imp = (\<lambda> (Fr, NXa, PVa). !Fr)"

definition amtf_next_imp :: "amtfi \<Rightarrow> nat \<Rightarrow> nat option Heap" where
  "amtf_next_imp = (\<lambda> (Fr, NXa, PVa) x. Array.nth NXa x)"

text \<open>The pointers stored in the arrays point into the universe.\<close>

lemma amtf_pointers:
  assumes "amtf_good n (F, NX, PV) xs"
  shows "F = Some y \<Longrightarrow> y < n"
        "\<lbrakk>x \<in> set xs; NX x = Some y\<rbrakk> \<Longrightarrow> y < n"
        "\<lbrakk>x \<in> set xs; PV x = Some y\<rbrakk> \<Longrightarrow> y < n"
proof-
  have I: "seg NX PV None xs None" "F = first_opt xs" "set xs \<subseteq> {..<n}"
    using assms by (simp_all add: amtf_good_def)
  show "F = Some y \<Longrightarrow> y < n"
    using I(2,3) by (cases xs) auto
  show "NX x = Some y \<Longrightarrow> y < n" "PV x = Some y \<Longrightarrow> y < n" if x: "x \<in> set xs"
  proof-
    obtain as bs where xs: "xs = as @ x # bs"
      using split_list[OF x] by blast
    note m = seg_mid[OF I(1)[unfolded xs]]
    show "NX x = Some y \<Longrightarrow> y < n"
      using m(2) I(3) xs by (cases bs) auto
    show "PV x = Some y \<Longrightarrow> y < n"
      using m(1) I(3) xs last_in_set[of as] by (cases "as = []") (auto simp add: last_opt_def)
  qed
qed

lemma amtf_empty_rule: "<emp> amtf_empty_imp n <\<lambda> Li. amtf_assn n amtf_empty Li>"
  unfolding amtf_empty_imp_def amtf_empty_def
  by (sep_auto heap: xmap_assn_new)

lemma amtf_push_front_rule:
  assumes "amtf_good n L xs" "x < n"
  shows "<amtf_assn n L Li> amtf_push_front_imp Li x <\<lambda> _. amtf_assn n (amtf_push_front L x) Li>"
proof-
  obtain F NX PV where L: "L = (F, NX, PV)"
    by (cases L) auto
  obtain Fr NXa PVa where Li: "Li = (Fr, NXa, PVa)"
    by (cases Li) auto
  have y: "\<And> y. F = Some y \<Longrightarrow> y < n"
    using amtf_pointers(1)[OF assms(1)[unfolded L]] .
  show ?thesis
    unfolding L Li amtf_push_front_imp_def amtf_push_front_def
    using assms(2) y
    by (cases F) (sep_auto heap: xmap_upd_rule)+
qed

lemma amtf_remove_rule:
  assumes "amtf_good n L xs" "x \<in> set xs"
  shows "<amtf_assn n L Li> amtf_remove_imp Li x <\<lambda> _. amtf_assn n (amtf_remove L x) Li>"
proof-
  obtain F NX PV where L: "L = (F, NX, PV)"
    by (cases L) auto
  obtain Fr NXa PVa where Li: "Li = (Fr, NXa, PVa)"
    by (cases Li) auto
  have x: "x < n"
    using assms by (auto simp add: amtf_good_def L)
  have a: "\<And> a. PV x = Some a \<Longrightarrow> a < n" and b: "\<And> b. NX x = Some b \<Longrightarrow> b < n"
    using amtf_pointers(2,3)[OF assms(1)[unfolded L] assms(2)] by auto
  show ?thesis
    unfolding L Li amtf_remove_imp_def amtf_remove_def
    using x a b
    by (cases "PV x"; cases "NX x")
       (sep_auto simp: remove_nx_def remove_pv_def heap: xmap_lookup_rule xmap_upd_rule)+
qed

lemma amtf_move_to_front_rule:
  assumes "amtf_invar n L" "x \<in> set (amtf_abstract n L)"
  shows "<amtf_assn n L Li> amtf_move_to_front_imp Li x
         <\<lambda> _. amtf_assn n (amtf_move_to_front L x) Li>"
proof-
  obtain xs where xs: "amtf_good n L xs"
    using assms(1) by (auto simp add: amtf_invar_def)
  have x: "x \<in> set xs"
    using assms(2) amtf_abstract_good[OF xs] by simp
  have xn: "x < n"
    using x xs by (cases L) (auto simp add: amtf_good_def)
  note R = amtf_remove_good[OF xs x]
  show ?thesis
    unfolding amtf_move_to_front_imp_def amtf_move_to_front_def
    by (sep_auto heap: amtf_remove_rule[OF xs x] amtf_push_front_rule[OF R xn])
qed

lemma amtf_first_rule:
  "<amtf_assn n L Li> amtf_first_imp Li <\<lambda> r. amtf_assn n L Li * \<up>(r = amtf_first L)>"
  unfolding amtf_first_imp_def amtf_first_def
  by (cases L; cases Li) sep_auto

lemma amtf_next_rule:
  assumes "amtf_invar n L" "x \<in> set (amtf_abstract n L)"
  shows "<amtf_assn n L Li> amtf_next_imp Li x <\<lambda> r. amtf_assn n L Li * \<up>(r = amtf_next L x)>"
proof-
  obtain xs where xs: "amtf_good n L xs"
    using assms(1) by (auto simp add: amtf_invar_def)
  have "x < n"
    using assms(2) amtf_abstract_good[OF xs] xs by (cases L) (auto simp add: amtf_good_def)
  thus ?thesis
    unfolding amtf_next_imp_def amtf_next_def
    by (cases L; cases Li) (sep_auto heap: xmap_lookup_rule)
qed

lemma amtf_fixed_univ_list_imp:
  "fixed_univ_list_imp {..<n} (amtf_invar n) (amtf_abstract n) amtf_empty amtf_push_front
     amtf_move_to_front amtf_first amtf_next (amtf_assn n) (amtf_empty_imp n) amtf_push_front_imp
     amtf_move_to_front_imp amtf_first_imp amtf_next_imp"
proof-
  interpret fixed_univ_list "{..<n}" "amtf_invar n" "amtf_abstract n" amtf_empty amtf_push_front
    amtf_move_to_front amtf_first amtf_next
    by (rule amtf_fixed_univ_list)
  show ?thesis
  proof(unfold_locales, goal_cases)
    case 1
    show ?case
      by (rule amtf_empty_rule)
  next
    case (2 L x Li)
    then obtain xs where "amtf_good n L xs"
      by (auto simp add: amtf_invar_def)
    thus ?case
      using amtf_push_front_rule 2(2) by simp
  next
    case (3 L x Li)
    thus ?case
      by (rule amtf_move_to_front_rule)
  next
    case (4 L Li)
    show ?case
      by (rule amtf_first_rule)
  next
    case (5 L x Li)
    thus ?case
      by (rule amtf_next_rule)
  qed
qed

end
