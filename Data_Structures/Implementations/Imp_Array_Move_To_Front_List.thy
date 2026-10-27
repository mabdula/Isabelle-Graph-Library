theory Imp_Array_Move_To_Front_List
  imports
    Array_Linked_Lists
    Imp_Array_Fun
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

lemma amtf_good_unique:
  "\<lbrakk>amtf_good n L xs; amtf_good n L ys\<rbrakk> \<Longrightarrow> xs = ys"
  by (cases L) (auto simp add: amtf_good_def intro: seg_unique)

lemma amtf_abstract_good: "amtf_good n L xs \<Longrightarrow> amtf_abstract n L = xs"
  by (auto simp add: amtf_abstract_def intro: amtf_good_unique)

lemma amtf_good_set:
  "amtf_good n L xs \<Longrightarrow> distinct xs \<and> set xs \<subseteq> {..<n}"
  by (cases L) (simp add: amtf_good_def)

lemma amtf_good_empty: "amtf_good n amtf_empty []"
  by (simp add: amtf_good_def amtf_empty_def)

lemma amtf_invarI: "amtf_good n L xs \<Longrightarrow> amtf_invar n L"
  by (auto simp add: amtf_invar_def)

lemma amtf_invarE:
  assumes "amtf_invar n L"
  obtains xs where "amtf_good n L xs" "amtf_abstract n L = xs"
  using assms
  by (auto simp add: amtf_invar_def amtf_abstract_good)

lemma amtf_push_front_good:
  assumes "amtf_good n L xs" "x < n" "x \<notin> set xs"
  shows "amtf_good n (amtf_push_front L x) (x # xs)"
proof(cases L)
  case (fields F NX PV)
  thus ?thesis
    using assms seg_push_front[of NX PV xs x]
    by (cases xs; auto simp add: amtf_good_def amtf_push_front_def push_nx_def push_pv_def)
qed

lemma amtf_remove_good:
  assumes "amtf_good n L xs" "x \<in> set xs"
  shows "amtf_good n (amtf_remove L x) (remove1 x xs)"
proof(cases L)
  case (fields F NX PV)
  obtain as bs where "xs = as @ x # bs"
    using assms(2)
    by (blast dest: split_list)
  moreover have "seg NX PV None xs None" "F = first_opt xs"
    "distinct xs" "set xs \<subseteq> {..<n}"
    using assms(1) fields
    by (simp_all add: amtf_good_def)
  ultimately have "PV x = last_opt as" "NX x = first_opt bs" "F = first_opt (as @ x # bs)"
    "seg (remove_nx NX PV x) (remove_pv NX PV x) None (as @ bs) None"
    "distinct (as @ x # bs)" "set (as @ x # bs) \<subseteq> {..<n}"
    by (simp_all add: seg_mid seg_remove)
  thus ?thesis
    using fields \<open>xs = as @ x # bs\<close>
    by (cases as rule: rev_cases;
        auto simp add: amtf_good_def amtf_remove_def remove1_append first_opt_append last_opt_def)
qed

lemma amtf_move_to_front_good:
  "\<lbrakk>amtf_good n L xs; x \<in> set xs\<rbrakk> \<Longrightarrow>
    amtf_good n (amtf_move_to_front L x) (x # remove1 x xs)"
  unfolding amtf_move_to_front_def
  by (rule amtf_push_front_good[OF amtf_remove_good]) (auto dest: amtf_good_set)

lemma amtf_fixed_univ_list:
  "fixed_univ_list {..<n} (amtf_invar n) (amtf_abstract n) amtf_empty amtf_push_front
     amtf_move_to_front amtf_first amtf_next"
proof(unfold_locales, goal_cases)
  case (1 L)
  thus ?case
    by (auto elim!: amtf_invarE dest: amtf_good_set)
next
  case 2
  show ?case
    using amtf_good_empty
    by (rule amtf_invarI)
next
  case 3
  show ?case
    using amtf_good_empty
    by (rule amtf_abstract_good)
next
  case (4 L x)
  thus ?case
    by (auto elim!: amtf_invarE intro: amtf_invarI amtf_push_front_good)
next
  case (5 L x)
  thus ?case
    by (auto elim!: amtf_invarE intro: amtf_abstract_good amtf_push_front_good)
next
  case (6 L x)
  thus ?case
    by (auto elim!: amtf_invarE intro: amtf_invarI amtf_move_to_front_good)
next
  case (7 L x)
  thus ?case
    by (auto elim!: amtf_invarE intro: amtf_abstract_good amtf_move_to_front_good)
next
  case (8 L)
  thus ?case
    by (cases L) (auto elim!: amtf_invarE simp add: amtf_good_def amtf_first_def first_opt_def)
next
  case (9 L xs x ys)
  thus ?case
    by (cases L)
       (auto elim!: amtf_invarE simp add: amtf_good_def amtf_next_def first_opt_def
         dest!: seg_mid(2))
qed

section \<open>The Arrays\<close>

type_synonym amtfi = "nat option ref \<times> nat option array \<times> nat option array"

fun amtf_assn :: "nat \<Rightarrow> amtf \<Rightarrow> amtfi \<Rightarrow> assn" where
  "amtf_assn n (F, NX, PV) (Fr, NXa, PVa) = Fr \<mapsto>\<^sub>r F * array_fun_assn n NX NXa * array_fun_assn n PV PVa"

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
  show "F = Some y \<Longrightarrow> y < n"
    using assms
    by (cases xs; auto simp add: amtf_good_def)
  show "NX x = Some y \<Longrightarrow> y < n" "PV x = Some y \<Longrightarrow> y < n"
    if "x \<in> set xs"
  proof-
    obtain as bs where "xs = as @ x # bs"
      using \<open>x \<in> set xs\<close>
      by (blast dest: split_list)
    moreover have "seg NX PV None xs None" "set xs \<subseteq> {..<n}"
      using assms
      by (simp_all add: amtf_good_def)
    ultimately have "PV x = last_opt as" "NX x = first_opt bs"
      "set (as @ x # bs) \<subseteq> {..<n}"
      by (simp_all add: seg_mid)
    thus "NX x = Some y \<Longrightarrow> y < n" "PV x = Some y \<Longrightarrow> y < n"
      by (cases bs; cases as rule: rev_cases; auto simp add: last_opt_def)+
  qed
qed

lemma amtf_empty_rule: "<emp> amtf_empty_imp n <\<lambda> Li. amtf_assn n amtf_empty Li>"
  unfolding amtf_empty_imp_def amtf_empty_def
  by (sep_auto heap: array_fun_assn_new)

lemma amtf_push_front_rule:
  assumes "amtf_good n L xs" "x < n"
  shows "<amtf_assn n L Li> amtf_push_front_imp Li x <\<lambda> _. amtf_assn n (amtf_push_front L x) Li>"
proof-
  obtain F NX PV Fr NXa PVa where "L = (F, NX, PV)" "Li = (Fr, NXa, PVa)"
    by (cases L, cases Li) auto
  thus ?thesis
    using assms amtf_pointers(1)[of n F NX PV xs]
    unfolding amtf_push_front_imp_def amtf_push_front_def
      \<open>L = (F, NX, PV)\<close> \<open>Li = (Fr, NXa, PVa)\<close>
    by (cases F) (sep_auto heap: array_fun_upd_rule)+
qed

lemma amtf_remove_rule:
  assumes "amtf_good n L xs" "x \<in> set xs"
  shows "<amtf_assn n L Li> amtf_remove_imp Li x <\<lambda> _. amtf_assn n (amtf_remove L x) Li>"
proof-
  obtain F NX PV Fr NXa PVa where "L = (F, NX, PV)" "Li = (Fr, NXa, PVa)"
    by (cases L, cases Li) auto
  thus ?thesis
    using assms amtf_good_set[OF assms(1)] amtf_pointers(2,3)[of n F NX PV xs x]
    unfolding amtf_remove_imp_def amtf_remove_def
      \<open>L = (F, NX, PV)\<close> \<open>Li = (Fr, NXa, PVa)\<close>
    by (cases "PV x"; cases "NX x")
       (sep_auto simp: remove_nx_def remove_pv_def heap: array_fun_lookup_rule array_fun_upd_rule)+
qed

lemma amtf_move_to_front_rule:
  "\<lbrakk>amtf_invar n L; x \<in> set (amtf_abstract n L)\<rbrakk> \<Longrightarrow>
    <amtf_assn n L Li> amtf_move_to_front_imp Li x
    <\<lambda> _. amtf_assn n (amtf_move_to_front L x) Li>"
  by (elim amtf_invarE)
     (sep_auto simp: amtf_move_to_front_imp_def amtf_move_to_front_def
       heap: amtf_remove_rule amtf_push_front_rule intro: amtf_remove_good dest: amtf_good_set)

lemma amtf_first_rule:
  "<amtf_assn n L Li> amtf_first_imp Li <\<lambda> r. amtf_assn n L Li * \<up>(r = amtf_first L)>"
  unfolding amtf_first_imp_def amtf_first_def
  by (cases L; cases Li) sep_auto

lemma amtf_next_rule:
  "\<lbrakk>amtf_invar n L; x \<in> set (amtf_abstract n L)\<rbrakk> \<Longrightarrow>
    <amtf_assn n L Li> amtf_next_imp Li x <\<lambda> r. amtf_assn n L Li * \<up>(r = amtf_next L x)>"
  by (elim amtf_invarE, cases L, cases Li)
     (sep_auto heap: array_fun_lookup_rule simp: amtf_good_def amtf_next_imp_def amtf_next_def)

lemma amtf_fixed_univ_list_imp:
  "fixed_univ_list_imp {..<n} (amtf_invar n) (amtf_abstract n) amtf_empty amtf_push_front
     amtf_move_to_front amtf_first amtf_next (amtf_assn n) (amtf_empty_imp n) amtf_push_front_imp
     amtf_move_to_front_imp amtf_first_imp amtf_next_imp"
  by (intro fixed_univ_list_imp.intro amtf_fixed_univ_list fixed_univ_list_imp_axioms.intro)
     (auto elim!: amtf_invarE intro: amtf_invarI amtf_empty_rule amtf_push_front_rule
        amtf_move_to_front_rule amtf_first_rule amtf_next_rule)

end
