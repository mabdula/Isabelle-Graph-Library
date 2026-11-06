theory Imp_Array_Buckets
  imports
    Array_Linked_Lists
    Imp_Array_Fun
    Fixed_Univ_Buckets_Specs_Imp
begin

section \<open>Buckets as Doubly-Linked Lists in Arrays\<close>

text \<open>Buckets with keys \<open>{..<nb}\<close> over the elements \<open>{..<n}\<close>: one doubly-linked list per bucket,
      stored in a head and a tail array over the keys and a successor and a predecessor array
      over the elements, all allocated once. Every operation takes a constant number of array
      accesses; moving a bucket into another one splices the first list in front of the second
      one. The functional model is the four arrays as functions.\<close>

type_synonym abk = "(nat \<Rightarrow> nat option) \<times> (nat \<Rightarrow> nat option) \<times> (nat \<Rightarrow> nat option) \<times> (nat \<Rightarrow> nat option)"

definition abk_empty :: abk where
  "abk_empty = ((\<lambda> _. None), (\<lambda> _. None), (\<lambda> _. None), (\<lambda> _. None))"

definition abk_insert :: "abk \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> abk" where
  "abk_insert = (\<lambda> (H, T, NX, PV) x k.
     (let f = H k
      in (H(k := Some x), (case f of None \<Rightarrow> T(k := Some x) | Some _ \<Rightarrow> T), NX(x := f),
          (case f of None \<Rightarrow> PV(x := None) | Some y \<Rightarrow> (PV(x := None))(y := Some x)))))"

definition abk_remove :: "abk \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> abk" where
  "abk_remove = (\<lambda> (H, T, NX, PV) x k.
     ((case PV x of None \<Rightarrow> H(k := NX x) | Some _ \<Rightarrow> H),
      (case NX x of None \<Rightarrow> T(k := PV x) | Some _ \<Rightarrow> T),
      remove_nx NX PV x, remove_pv NX PV x))"

definition abk_pick :: "abk \<Rightarrow> nat \<Rightarrow> nat option" where
  "abk_pick = (\<lambda> (H, T, NX, PV) k. H k)"

definition abk_move :: "abk \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> abk" where
  "abk_move = (\<lambda> (H, T, NX, PV) j j'.
     (case H j of None \<Rightarrow> (H, T, NX, PV)
      | Some a \<Rightarrow>
          (let f = H j'; z = T j
           in ((H(j := None))(j' := Some a), (case f of None \<Rightarrow> (T(j := None))(j' := z) | Some _ \<Rightarrow> T(j := None)),
               NX(the z := f), (case f of None \<Rightarrow> PV | Some y \<Rightarrow> PV(y := z))))))"

subsection \<open>Abstraction\<close>

definition "disjoint_lists L =
  (\<forall> k k'. k \<noteq> k' \<longrightarrow> set (L k) \<inter> set (L k') = {})"

definition "lists_abs L x =
  (if \<exists> k. x \<in> set (L k) then Some (THE k. x \<in> set (L k)) else None)"

lemma lists_abs_Some:
  "disjoint_lists L \<Longrightarrow> lists_abs L x = Some k \<longleftrightarrow> x \<in> set (L k)"
  by (auto simp add: lists_abs_def disjoint_lists_def; rule the_equality theI; blast)

lemma lists_abs_None:
  "lists_abs L x = None \<longleftrightarrow> (\<forall> k. x \<notin> set (L k))"
  by (simp add: lists_abs_def)

lemma lists_abs_eqI:
  assumes "disjoint_lists L" "\<And> y k. y \<in> set (L k) \<longleftrightarrow> f y = Some k"
  shows "lists_abs L = f"
proof
  fix y
  show "lists_abs L y = f y"
    using assms
    by (cases "f y") (simp_all add: lists_abs_None lists_abs_Some)
qed

lemma disjoint_listsD:
  "\<lbrakk>disjoint_lists L; k \<noteq> k'; x \<in> set (L k)\<rbrakk> \<Longrightarrow> x \<notin> set (L k')"
  by (auto simp add: disjoint_lists_def)

lemma disjoint_lists_upd:
  "\<lbrakk>disjoint_lists L; set xs \<subseteq> set (L k)\<rbrakk> \<Longrightarrow> disjoint_lists (L(k := xs))"
  by (auto simp add: disjoint_lists_def)

text \<open>The lists of the buckets, as they are linked in the arrays.\<close>

definition abk_good :: "nat \<Rightarrow> nat \<Rightarrow> abk \<Rightarrow> (nat \<Rightarrow> nat list) \<Rightarrow> bool"
  where
  "abk_good n nb B L = (case B of (H, T, NX, PV) \<Rightarrow>
  (\<forall> k. nb \<le> k \<longrightarrow> L k = []) \<and>
  (\<forall> k < nb. seg NX PV None (L k) None \<and> H k = first_opt (L k) \<and>
    T k = last_opt (L k)) \<and>
  (\<forall> k. distinct (L k) \<and> set (L k) \<subseteq> {..<n}) \<and> disjoint_lists L)"

definition "abk_invar n nb B = (\<exists> L. abk_good n nb B L)"

definition "abk_abstract n nb B = lists_abs (SOME L. abk_good n nb B L)"

lemma abk_good_unique:
  assumes "abk_good n nb B L" "abk_good n nb B L'"
  shows "L = L'"
proof
  fix k
  show "L k = L' k"
    using assms
    by (cases B; cases "k < nb") (auto simp add: abk_good_def intro: seg_unique)
qed

lemma abk_abstract_good: "abk_good n nb B L \<Longrightarrow> abk_abstract n nb B = lists_abs L"
  unfolding abk_abstract_def
  by (rule someI2[where Q = "\<lambda> L'. lists_abs L' = lists_abs L"])
     (auto dest: abk_good_unique)

lemma abk_goodD:
  assumes "abk_good n nb (H, T, NX, PV) L"
  shows "\<And> k. nb \<le> k \<Longrightarrow> L k = []"
        "\<And> k. k < nb \<Longrightarrow> seg NX PV None (L k) None"
        "\<And> k. k < nb \<Longrightarrow> H k = first_opt (L k)"
        "\<And> k. k < nb \<Longrightarrow> T k = last_opt (L k)"
        "\<And> k. distinct (L k)" "\<And> k. set (L k) \<subseteq> {..<n}" "disjoint_lists L"
  using assms
  by (simp_all add: abk_good_def)

lemma abk_good_disjoint: "abk_good n nb B L \<Longrightarrow> disjoint_lists L"
  by (cases B) (simp add: abk_good_def)

lemma abk_good_lists:
  "abk_good n nb B L \<Longrightarrow> disjoint_lists L \<and> (\<forall> k. distinct (L k))"
  by (cases B) (simp add: abk_good_def)

lemma abk_good_in:
  "\<lbrakk>abk_good n nb B L; x \<in> set (L k)\<rbrakk> \<Longrightarrow> x < n \<and> k < nb"
  by (cases B, cases "k < nb") (auto simp add: abk_good_def)

lemma abk_good_empty: "abk_good n nb abk_empty (\<lambda> _. [])"
  by (simp add: abk_good_def abk_empty_def disjoint_lists_def)

lemma abk_invarI: "abk_good n nb B L \<Longrightarrow> abk_invar n nb B"
  by (auto simp add: abk_invar_def)

lemma abk_invarE:
  assumes "abk_invar n nb B"
  obtains L where "abk_good n nb B L" "abk_abstract n nb B = lists_abs L" "disjoint_lists L"
  using assms
  by (auto simp add: abk_invar_def abk_abstract_good abk_good_disjoint)

lemma abk_abstract_eqI:
  "\<lbrakk>abk_good n nb B L; \<And> y k. y \<in> set (L k) \<longleftrightarrow> f y = Some k\<rbrakk> \<Longrightarrow>
    abk_abstract n nb B = f"
  by (simp add: abk_abstract_good lists_abs_eqI abk_good_disjoint)

subsection \<open>The Operations on the Lists\<close>

lemma abk_insert_good:
  assumes "abk_good n nb (H, T, NX, PV) L" "x < n" "k < nb" "\<forall> k. x \<notin> set (L k)"
  shows "abk_good n nb (abk_insert (H, T, NX, PV) x k) (L(k := x # L k))"
proof-
  have "abk_insert (H, T, NX, PV) x k =
        (H(k := Some x), (if L k = [] then T(k := Some x) else T),
         push_nx NX x (L k), push_pv PV x (L k))"
    using assms(1,3)
    by (cases "L k") (simp_all add: abk_good_def abk_insert_def push_nx_def push_pv_def)
  moreover have "seg (push_nx NX x (L k)) (push_pv PV x (L k)) None (L k') None"
    if "k' \<noteq> k" "k' < nb" for k'
    using assms(1,4) that disjoint_listsD[of L k k' "hd (L k)"]
    by (cases "L k"; simp_all add: abk_good_def push_nx_def push_pv_def)
  ultimately show ?thesis
    using assms seg_push_front[of NX PV "L k" x]
    by (auto simp add: abk_good_def disjoint_lists_def)
qed

lemma abk_remove_good:
  assumes "abk_good n nb (H, T, NX, PV) L" "x \<in> set (L k)"
  shows "abk_good n nb (abk_remove (H, T, NX, PV) x k) (L(k := remove1 x (L k)))"
proof-
  obtain as bs where "L k = as @ x # bs"
    using assms(2)
    by (blast dest: split_list)
  moreover have "k < nb"
    using abk_good_in[OF assms]
    by simp
  ultimately have "distinct (as @ x # bs)" "seg NX PV None (as @ x # bs) None"
    "set (as @ x # bs) \<subseteq> {..<n}"
    using abk_goodD(2,5,6)[OF assms(1), of k]
    by simp_all
  hence "PV x = last_opt as" "NX x = first_opt bs"
    "seg (remove_nx NX PV x) (remove_pv NX PV x) None (as @ bs) None"
    by (simp_all add: seg_mid seg_remove)
  moreover have "seg (remove_nx NX PV x) (remove_pv NX PV x) None (L k') None"
    if "k' \<noteq> k" "k' < nb" for k'
    using assms(1) that \<open>L k = as @ x # bs\<close> \<open>PV x = last_opt as\<close>
      \<open>NX x = first_opt bs\<close> disjoint_listsD[of L k k']
    by (cases as rule: rev_cases; cases bs;
        simp_all add: abk_good_def remove_nx_def remove_pv_def last_opt_def)
  ultimately show ?thesis
    using assms(1) \<open>L k = as @ x # bs\<close> \<open>k < nb\<close> \<open>distinct (as @ x # bs)\<close>
      \<open>set (as @ x # bs) \<subseteq> {..<n}\<close> disjoint_lists_upd[of L "as @ bs" k]
    by (auto simp add: abk_good_def abk_remove_def remove1_append first_opt_append last_opt_append
        subset_insertI split: option.split)
qed

lemma abk_move_good:
  assumes "abk_good n nb (H, T, NX, PV) L" "j < nb" "j' < nb" "j \<noteq> j'"
  shows "abk_good n nb (abk_move (H, T, NX, PV) j j') (L(j := [], j' := L j @ L j'))"
proof(cases "L j = []")
  case True
  hence "L(j := [], j' := L j @ L j') = L"
    by auto
  thus ?thesis
    using assms True
    by (simp add: abk_good_def abk_move_def)
next
  case False
  have "distinct (L j @ L j')"
    using assms
    by (auto simp add: abk_good_def disjoint_lists_def)
  moreover have
    "seg (concat_nx NX (last (L j)) (L j')) (concat_pv PV (last (L j)) (L j')) None (L k) None"
    if "k \<noteq> j" "k \<noteq> j'" "k < nb" for k
    using assms(1) that False disjoint_listsD[of L j k] disjoint_listsD[of L j' k]
    by (cases "L j'"; simp_all add: abk_good_def concat_nx_def concat_pv_def last_in_set)
  moreover have "abk_move (H, T, NX, PV) j j' =
    ((H(j := None))(j' := H j), (T(j := None))(j' := last_opt (L j @ L j')),
     concat_nx NX (last (L j)) (L j'), concat_pv PV (last (L j)) (L j'))"
    using assms False
    by (cases "L j'";
        auto simp add: abk_good_def abk_move_def concat_nx_def concat_pv_def last_opt_def
          split: option.split)
  moreover have "disjoint_lists (L(j := [], j' := L j @ L j'))"
    using abk_goodD(7)[OF assms(1)]
    by (auto simp add: disjoint_lists_def)
  ultimately show ?thesis
    using assms False seg_concat[of NX PV "L j" "L j'"]
    by (auto simp add: abk_good_def first_opt_append)
qed

lemma abk_insert_abstract:
  "\<lbrakk>abk_good n nb (H, T, NX, PV) L; x < n; k < nb; \<forall> k. x \<notin> set (L k)\<rbrakk>
    \<Longrightarrow>
    abk_abstract n nb (abk_insert (H, T, NX, PV) x k) = (lists_abs L)(x := Some k)"
  by (rule abk_abstract_eqI[OF abk_insert_good])
     (auto simp add: lists_abs_Some dest: abk_good_disjoint)

lemma abk_remove_abstract:
  "\<lbrakk>abk_good n nb (H, T, NX, PV) L; x \<in> set (L k)\<rbrakk> \<Longrightarrow>
    abk_abstract n nb (abk_remove (H, T, NX, PV) x k) = (lists_abs L)(x := None)"
  by (rule abk_abstract_eqI[OF abk_remove_good])
     (auto simp add: lists_abs_Some dest!: abk_good_lists dest: disjoint_listsD)

lemma abk_move_abstract:
  "\<lbrakk>abk_good n nb (H, T, NX, PV) L; j < nb; j' < nb; j \<noteq> j'\<rbrakk>
    \<Longrightarrow>
    abk_abstract n nb (abk_move (H, T, NX, PV) j j') =
    (\<lambda> x. if lists_abs L x = Some j then Some j' else lists_abs L x)"
  by (rule abk_abstract_eqI[OF abk_move_good])
     (auto simp add: lists_abs_Some dest!: abk_good_lists dest: disjoint_listsD)

subsection \<open>The Functional Model Satisfies the Specification\<close>

lemma abk_fixed_univ_buckets:
  "fixed_univ_buckets {..<n} {..<nb} (abk_invar n nb) (abk_abstract n nb) abk_empty abk_insert
     abk_remove abk_pick abk_move"
proof(unfold_locales, goal_cases)
  case (1 B x k)
  thus ?case
    by (auto elim!: abk_invarE dest: abk_good_in simp add: lists_abs_Some)
next
  case 2
  show ?case
    using abk_good_empty
    by (rule abk_invarI)
next
  case 3
  show ?case
    by (rule abk_abstract_eqI[OF abk_good_empty]) simp
next
  case (4 B x k)
  thus ?case
    by (cases B)
       (auto elim!: abk_invarE simp add: lists_abs_None intro!: abk_invarI[OF abk_insert_good])
next
  case (5 B x k)
  thus ?case
    by (cases B) (auto elim!: abk_invarE simp add: lists_abs_None intro!: abk_insert_abstract)
next
  case (6 B x k)
  thus ?case
    by (cases B)
       (auto elim!: abk_invarE simp add: lists_abs_Some intro!: abk_invarI[OF abk_remove_good])
next
  case (7 B x k)
  thus ?case
    by (cases B) (auto elim!: abk_invarE simp add: lists_abs_Some intro!: abk_remove_abstract)
next
  case (8 B k)
  thus ?case
    by (cases B) (auto elim!: abk_invarE simp add: abk_pick_def lists_abs_Some dest: abk_goodD(3))
next
  case (9 B k x)
  thus ?case
    by (cases B)
       (auto elim!: abk_invarE simp add: abk_pick_def lists_abs_Some first_opt_def
         split: list.splits dest: abk_goodD(3))
next
  case (10 B j j')
  thus ?case
    by (cases B) (auto elim!: abk_invarE intro: abk_invarI abk_move_good)
next
  case (11 B j j')
  thus ?case
    by (cases B) (auto elim!: abk_invarE cong: if_cong intro!: abk_move_abstract)
qed

section \<open>The Arrays\<close>

type_synonym abki = "nat option array \<times> nat option array \<times> nat option array \<times> nat option array"

fun abk_assn :: "nat \<Rightarrow> nat \<Rightarrow> abk \<Rightarrow> abki \<Rightarrow> assn" where
  "abk_assn n nb (H, T, NX, PV) (Ha, Ta, NXa, PVa) =
   array_fun_assn nb H Ha * array_fun_assn nb T Ta * array_fun_assn n NX NXa * array_fun_assn n PV PVa"

definition abk_empty_imp :: "nat \<Rightarrow> nat \<Rightarrow> abki Heap" where
  "abk_empty_imp n nb = do {
     Ha \<leftarrow> Array.new nb None; Ta \<leftarrow> Array.new nb None;
     NXa \<leftarrow> Array.new n None; PVa \<leftarrow> Array.new n None;
     return (Ha, Ta, NXa, PVa) }"

definition abk_insert_imp :: "abki \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "abk_insert_imp = (\<lambda> (Ha, Ta, NXa, PVa) x k. do {
     f \<leftarrow> Array.nth Ha k;
     _ \<leftarrow> Array.upd k (Some x) Ha;
     _ \<leftarrow> (case f of None \<Rightarrow> Array.upd k (Some x) Ta | Some _ \<Rightarrow> return Ta);
     _ \<leftarrow> Array.upd x f NXa;
     _ \<leftarrow> Array.upd x None PVa;
     _ \<leftarrow> (case f of None \<Rightarrow> return PVa | Some y \<Rightarrow> Array.upd y (Some x) PVa);
     return () })"

definition abk_remove_imp :: "abki \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "abk_remove_imp = (\<lambda> (Ha, Ta, NXa, PVa) x k. do {
     p \<leftarrow> Array.nth PVa x;
     q \<leftarrow> Array.nth NXa x;
     _ \<leftarrow> (case p of None \<Rightarrow> Array.upd k q Ha | Some a \<Rightarrow> return Ha);
     _ \<leftarrow> (case q of None \<Rightarrow> Array.upd k p Ta | Some b \<Rightarrow> return Ta);
     _ \<leftarrow> (case p of None \<Rightarrow> return NXa | Some a \<Rightarrow> Array.upd a q NXa);
     _ \<leftarrow> (case q of None \<Rightarrow> return PVa | Some b \<Rightarrow> Array.upd b p PVa);
     return () })"

definition abk_pick_imp :: "abki \<Rightarrow> nat \<Rightarrow> nat option Heap" where
  "abk_pick_imp = (\<lambda> (Ha, Ta, NXa, PVa) k. Array.nth Ha k)"

definition abk_move_imp :: "abki \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "abk_move_imp = (\<lambda> (Ha, Ta, NXa, PVa) j j'. do {
     h \<leftarrow> Array.nth Ha j;
     (case h of None \<Rightarrow> return ()
      | Some a \<Rightarrow> do {
          z \<leftarrow> Array.nth Ta j;
          f \<leftarrow> Array.nth Ha j';
          _ \<leftarrow> Array.upd j None Ha;
          _ \<leftarrow> Array.upd j' (Some a) Ha;
          _ \<leftarrow> Array.upd j None Ta;
          _ \<leftarrow> (case f of None \<Rightarrow> Array.upd j' z Ta | Some _ \<Rightarrow> return Ta);
          _ \<leftarrow> Array.upd (the z) f NXa;
          _ \<leftarrow> (case f of None \<Rightarrow> return PVa | Some y \<Rightarrow> Array.upd y z PVa);
          return () }) })"

text \<open>The pointers stored in the arrays point into the universes.\<close>

lemma abk_pointers:
  assumes "abk_good n nb (H, T, NX, PV) L"
  shows "\<lbrakk>k < nb; H k = Some y\<rbrakk> \<Longrightarrow> y < n"
        "\<lbrakk>k < nb; T k = Some y\<rbrakk> \<Longrightarrow> y < n"
        "\<lbrakk>x \<in> set (L k); NX x = Some y\<rbrakk> \<Longrightarrow> y < n"
        "\<lbrakk>x \<in> set (L k); PV x = Some y\<rbrakk> \<Longrightarrow> y < n"
proof-
  show "\<lbrakk>k < nb; H k = Some y\<rbrakk> \<Longrightarrow> y < n"
    "\<lbrakk>k < nb; T k = Some y\<rbrakk> \<Longrightarrow> y < n"
    using abk_goodD(3,4,6)[OF assms, of k] last_in_set[of "L k"]
    by (auto simp add: first_opt_def last_opt_def split: list.splits if_splits)
  show "NX x = Some y \<Longrightarrow> y < n" "PV x = Some y \<Longrightarrow> y < n"
    if "x \<in> set (L k)"
  proof-
    obtain as bs where "L k = as @ x # bs"
      using \<open>x \<in> set (L k)\<close>
      by (blast dest: split_list)
    moreover have "set (L k) \<subseteq> {..<n}" "seg NX PV None (L k) None"
      using abk_good_in[OF assms that] abk_goodD(2,6)[OF assms, of k]
      by simp_all
    ultimately have "PV x = last_opt as" "NX x = first_opt bs"
      "set (as @ x # bs) \<subseteq> {..<n}"
      by (simp_all add: seg_mid)
    thus "NX x = Some y \<Longrightarrow> y < n" "PV x = Some y \<Longrightarrow> y < n"
      by (cases bs; cases as rule: rev_cases; auto simp add: last_opt_def)+
  qed
qed

lemma abk_empty_rule: "<emp> abk_empty_imp n nb <\<lambda> Bi. abk_assn n nb abk_empty Bi>"
  unfolding abk_empty_imp_def abk_empty_def
  by (sep_auto heap: array_fun_assn_new)

lemma abk_insert_rule:
  assumes "abk_invar n nb B" "x < n" "k < nb"
  shows "<abk_assn n nb B Bi> abk_insert_imp Bi x k <\<lambda> _. abk_assn n nb (abk_insert B x k) Bi>"
proof-
  obtain H T NX PV Ha Ta NXa PVa L where
    "B = (H, T, NX, PV)" "Bi = (Ha, Ta, NXa, PVa)" "abk_good n nb (H, T, NX, PV) L"
    using assms(1)
    by (cases B, cases Bi) (auto simp add: abk_invar_def)
  thus ?thesis
    using assms(2,3) abk_pointers(1)[of n nb H T NX PV L k]
    unfolding abk_insert_imp_def abk_insert_def
      \<open>B = (H, T, NX, PV)\<close> \<open>Bi = (Ha, Ta, NXa, PVa)\<close>
    by (cases "H k") (sep_auto heap: array_fun_lookup_rule array_fun_upd_rule)+
qed

lemma abk_remove_rule:
  assumes "abk_invar n nb B" "abk_abstract n nb B x = Some k"
  shows "<abk_assn n nb B Bi> abk_remove_imp Bi x k <\<lambda> _. abk_assn n nb (abk_remove B x k) Bi>"
proof-
  obtain H T NX PV Ha Ta NXa PVa L where
    "B = (H, T, NX, PV)" "Bi = (Ha, Ta, NXa, PVa)" "abk_good n nb (H, T, NX, PV) L"
    "x \<in> set (L k)"
    using assms
    by (cases B, cases Bi) (auto elim!: abk_invarE simp add: lists_abs_Some)
  hence "x < n" "k < nb" "PV x = Some a \<Longrightarrow> a < n" "NX x = Some b \<Longrightarrow> b < n" for a b
    using abk_good_in[of n nb "(H, T, NX, PV)" L x k] abk_pointers(3,4)[of n nb H T NX PV L x k]
    by auto
  thus ?thesis
    unfolding abk_remove_imp_def abk_remove_def
      \<open>B = (H, T, NX, PV)\<close> \<open>Bi = (Ha, Ta, NXa, PVa)\<close>
    by (cases "PV x") (cases "NX x"; sep_auto simp: remove_nx_def remove_pv_def
      heap: array_fun_lookup_rule array_fun_upd_rule)+
qed

lemma abk_pick_rule:
  assumes "k < nb"
  shows "<abk_assn n nb B Bi> abk_pick_imp Bi k <\<lambda> r. abk_assn n nb B Bi * \<up>(r = abk_pick B k)>"
  unfolding abk_pick_imp_def abk_pick_def
  using assms
  by (cases B; cases Bi) (sep_auto heap: array_fun_lookup_rule)

lemma abk_move_rule:
  assumes "abk_invar n nb B" "j < nb" "j' < nb"
  shows "<abk_assn n nb B Bi> abk_move_imp Bi j j' <\<lambda> _. abk_assn n nb (abk_move B j j') Bi>"
proof-
  obtain H T NX PV Ha Ta NXa PVa L where
    "B = (H, T, NX, PV)" "Bi = (Ha, Ta, NXa, PVa)" "abk_good n nb (H, T, NX, PV) L"
    using assms(1)
    by (cases B, cases Bi) (auto simp add: abk_invar_def)
  hence "H j \<noteq> None \<Longrightarrow> \<exists> z. T j = Some z \<and> z < n"
    "\<forall> y. H j' = Some y \<longrightarrow> y < n"
    using assms(2,3) abk_goodD(3,4)[of n nb H T NX PV L j] abk_pointers(1,2)[of n nb H T NX PV L]
    by (auto simp add: last_opt_def)
  thus ?thesis
    unfolding abk_move_imp_def abk_move_def
      \<open>B = (H, T, NX, PV)\<close> \<open>Bi = (Ha, Ta, NXa, PVa)\<close>
    using assms(2,3)
    by (cases "H j") (cases "H j'"; sep_auto heap: array_fun_lookup_rule array_fun_upd_rule)+
qed

lemma abk_fixed_univ_buckets_imp:
  "fixed_univ_buckets_imp {..<n} {..<nb} (abk_invar n nb) (abk_abstract n nb) abk_empty abk_insert
     abk_remove abk_pick abk_move (abk_assn n nb) (abk_empty_imp n nb) abk_insert_imp
     abk_remove_imp abk_pick_imp abk_move_imp"
  by (intro fixed_univ_buckets_imp.intro abk_fixed_univ_buckets fixed_univ_buckets_imp_axioms.intro)
     (auto intro: abk_empty_rule abk_insert_rule abk_remove_rule abk_pick_rule abk_move_rule)


end
