theory Imp_Array_Buckets
  imports
    Array_Linked_Lists
    Imp_Array_Map
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

definition "disjoint_lists L = (\<forall> k k'. k \<noteq> k' \<longrightarrow> set (L k) \<inter> set (L k') = {})"

definition "lists_abs L x = (if \<exists> k. x \<in> set (L k) then Some (THE k. x \<in> set (L k)) else None)"

lemma lists_abs_Some:
  assumes "disjoint_lists L"
  shows "lists_abs L x = Some k \<longleftrightarrow> x \<in> set (L k)"
proof(cases "\<exists> k'. x \<in> set (L k')")
  case True
  then obtain k' where k': "x \<in> set (L k')"
    by blast
  have "(THE k. x \<in> set (L k)) = k'"
    using k' assms by (auto simp add: disjoint_lists_def intro!: the_equality)
  thus ?thesis
    using True k' assms by (auto simp add: lists_abs_def disjoint_lists_def)
qed (simp add: lists_abs_def)

lemma lists_abs_None: "lists_abs L x = None \<longleftrightarrow> (\<forall> k. x \<notin> set (L k))"
  by (simp add: lists_abs_def)

lemma lists_abs_eqI:
  assumes "disjoint_lists L" "\<And> y k. y \<in> set (L k) \<longleftrightarrow> f y = Some k"
  shows "lists_abs L = f"
proof
  fix y
  show "lists_abs L y = f y"
  proof(cases "f y")
    case None
    thus ?thesis
      using assms(2) by (simp add: lists_abs_None)
  next
    case (Some k)
    thus ?thesis
      using assms(2) lists_abs_Some[OF assms(1)] by simp
  qed
qed

text \<open>The lists of the buckets, as they are linked in the arrays.\<close>

definition abk_good :: "nat \<Rightarrow> nat \<Rightarrow> abk \<Rightarrow> (nat \<Rightarrow> nat list) \<Rightarrow> bool" where
  "abk_good n nb B L = (case B of (H, T, NX, PV) \<Rightarrow>
  (\<forall> k. nb \<le> k \<longrightarrow> L k = []) \<and>
  (\<forall> k < nb. seg NX PV None (L k) None \<and> H k = first_opt (L k) \<and> T k = last_opt (L k)) \<and>
  (\<forall> k. distinct (L k) \<and> set (L k) \<subseteq> {..<n}) \<and> disjoint_lists L)"

definition "abk_invar n nb B = (\<exists> L. abk_good n nb B L)"

definition "abk_abstract n nb B = lists_abs (SOME L. abk_good n nb B L)"

lemma abk_good_unique:
  assumes "abk_good n nb B L" "abk_good n nb B L'"
  shows "L = L'"
proof
  fix k
  obtain H T NX PV where B: "B = (H, T, NX, PV)"
    by (cases B) auto
  show "L k = L' k"
  proof(cases "k < nb")
    case True
    have "seg NX PV None (L k) None" "seg NX PV None (L' k) None" "first_opt (L k) = first_opt (L' k)"
      using assms True by (auto simp add: abk_good_def B)
    thus ?thesis
      by (rule seg_unique)
  next
    case False
    hence "nb \<le> k"
      by simp
    hence "L k = []" "L' k = []"
      using assms by (simp_all add: abk_good_def B)
    thus ?thesis
      by simp
  qed
qed

lemma abk_abstract_good: "abk_good n nb B L \<Longrightarrow> abk_abstract n nb B = lists_abs L"
  unfolding abk_abstract_def using abk_good_unique by (metis (mono_tags, lifting) someI_ex)

lemma abk_goodD:
  assumes "abk_good n nb (H, T, NX, PV) L"
  shows "\<And> k. nb \<le> k \<Longrightarrow> L k = []"
        "\<And> k. k < nb \<Longrightarrow> seg NX PV None (L k) None"
        "\<And> k. k < nb \<Longrightarrow> H k = first_opt (L k)"
        "\<And> k. k < nb \<Longrightarrow> T k = last_opt (L k)"
        "\<And> k. distinct (L k)" "\<And> k. set (L k) \<subseteq> {..<n}" "disjoint_lists L"
  using assms by (simp_all add: abk_good_def)

lemma abk_goodI:
  assumes "\<And> k. nb \<le> k \<Longrightarrow> L k = []"
          "\<And> k. k < nb \<Longrightarrow> seg NX PV None (L k) None"
          "\<And> k. k < nb \<Longrightarrow> H k = first_opt (L k)"
          "\<And> k. k < nb \<Longrightarrow> T k = last_opt (L k)"
          "\<And> k. distinct (L k)" "\<And> k. set (L k) \<subseteq> {..<n}" "disjoint_lists L"
  shows "abk_good n nb (H, T, NX, PV) L"
  using assms by (simp add: abk_good_def)

lemma abk_good_disjoint: "abk_good n nb B L \<Longrightarrow> disjoint_lists L"
  by (cases B) (simp add: abk_good_def)

lemma abk_good_key:
  assumes "abk_good n nb B L" "x \<in> set (L k)"
  shows "k < nb"
proof(rule ccontr)
  assume "\<not> k < nb"
  hence "L k = []"
    using assms(1) by (cases B) (simp add: abk_good_def)
  thus False
    using assms(2) by simp
qed

lemma disjoint_listsD: "\<lbrakk>disjoint_lists L; k \<noteq> k'; x \<in> set (L k)\<rbrakk> \<Longrightarrow> x \<notin> set (L k')"
  by (auto simp add: disjoint_lists_def)

subsection \<open>The Operations on the Lists\<close>

lemma abk_insert_good:
  assumes "abk_good n nb (H, T, NX, PV) L" "x < n" "k < nb" "\<forall> k. x \<notin> set (L k)"
  shows "abk_good n nb (abk_insert (H, T, NX, PV) x k) (L(k := x # L k))"
proof-
  note I = abk_goodD[OF assms(1)]
  define NX' where "NX' = push_nx NX x (L k)"
  define PV' where "PV' = push_pv PV x (L k)"
  define T' where "T' = (if L k = [] then T(k := Some x) else T)"
  have ins: "abk_insert (H, T, NX, PV) x k = (H(k := Some x), T', NX', PV')"
    using I(3)[OF assms(3)]
    by (cases "L k") (simp_all add: abk_insert_def NX'_def PV'_def T'_def push_nx_def push_pv_def)
  have xk: "x \<notin> set (L k)"
    using assms(4) by simp
  have other: "seg NX' PV' None (L k') None" if "k' \<noteq> k" "k' < nb" for k'
  proof-
    have "x \<notin> set (L k')"
      using assms(4) by simp
    moreover have "hd (L k) \<notin> set (L k')" if "L k \<noteq> []"
      using disjoint_listsD[OF I(7) \<open>k' \<noteq> k\<close>[symmetric] hd_in_set[OF that]] .
    ultimately show ?thesis
      using I(2)[OF \<open>k' < nb\<close>] by (cases "L k") (simp_all add: NX'_def PV'_def push_nx_def push_pv_def)
  qed
  show ?thesis
    unfolding ins
  proof(rule abk_goodI)
    fix k'
    assume k': "k' < nb"
    show "seg NX' PV' None ((L(k := x # L k)) k') None"
      using seg_push_front[OF I(2)[OF assms(3)] I(5) xk] other[OF _ k']
      by (cases "k' = k") (simp_all add: NX'_def PV'_def)
    show "(H(k := Some x)) k' = first_opt ((L(k := x # L k)) k')"
      using I(3)[OF k'] by simp
    show "T' k' = last_opt ((L(k := x # L k)) k')"
      using I(4)[OF k'] by (auto simp add: T'_def)
  next
    show "disjoint_lists (L(k := x # L k))"
      using I(7) assms(4) by (auto simp add: disjoint_lists_def)
  qed (use I assms(2,3) xk in auto)
qed

lemma abk_remove_good:
  assumes "abk_good n nb (H, T, NX, PV) L" "x \<in> set (L k)"
  shows "abk_good n nb (abk_remove (H, T, NX, PV) x k) (L(k := remove1 x (L k)))"
proof-
  note I = abk_goodD[OF assms(1)]
  have k: "k < nb"
    using abk_good_key[OF assms(1,2)] .
  obtain as bs where Lk: "L k = as @ x # bs"
    using split_list[OF assms(2)] by blast
  have dis: "distinct (as @ x # bs)"
    using I(5)[of k] Lk by simp
  have rm: "remove1 x (L k) = as @ bs"
    using dis Lk by (simp add: remove1_append)
  note m = seg_mid[OF I(2)[OF k, unfolded Lk]]
  have ab: "set as \<subseteq> set (L k)" "set bs \<subseteq> set (L k)"
    using Lk by auto
  have other: "seg (remove_nx NX PV x) (remove_pv NX PV x) None (L k') None" if "k' \<noteq> k" "k' < nb" for k'
  proof-
    have "last as \<notin> set (L k')" if "as \<noteq> []"
      using disjoint_listsD[OF I(7) \<open>k' \<noteq> k\<close>[symmetric]] ab(1) last_in_set[OF that] by blast
    moreover have "hd bs \<notin> set (L k')" if "bs \<noteq> []"
      using disjoint_listsD[OF I(7) \<open>k' \<noteq> k\<close>[symmetric]] ab(2) hd_in_set[OF that] by blast
    ultimately show ?thesis
      using I(2)[OF \<open>k' < nb\<close>] m(1,2)
      by (cases as rule: rev_cases; cases bs) (simp_all add: remove_nx_def remove_pv_def last_opt_def)
  qed
  show ?thesis
    unfolding abk_remove_def prod.case
  proof(rule abk_goodI)
    fix k'
    assume k': "k' < nb"
    show "seg (remove_nx NX PV x) (remove_pv NX PV x) None ((L(k := remove1 x (L k))) k') None"
      using seg_remove[OF I(2)[OF k, unfolded Lk] dis] other[OF _ k'] rm
      by (cases "k' = k") simp_all
    show "(case PV x of None \<Rightarrow> H(k := NX x) | Some _ \<Rightarrow> H) k' = first_opt ((L(k := remove1 x (L k))) k')"
      using I(3)[OF k'] m(1,2) rm Lk
      by (cases "k' = k"; cases as rule: rev_cases)
         (auto simp add: first_opt_append last_opt_def split: option.split)
    show "(case NX x of None \<Rightarrow> T(k := PV x) | Some _ \<Rightarrow> T) k' = last_opt ((L(k := remove1 x (L k))) k')"
      using I(4)[OF k'] m(1,2) rm Lk
      by (cases "k' = k"; cases bs) (auto simp add: last_opt_append split: option.split)
  next
    show "disjoint_lists (L(k := remove1 x (L k)))"
      using I(7) by (auto simp add: disjoint_lists_def dest!: subsetD[OF set_remove1_subset])
  next
    fix k'
    show "set ((L(k := remove1 x (L k))) k') \<subseteq> {..<n}"
      using I(6)[of k] I(6)[of k'] set_remove1_subset[of x "L k"] by auto
  qed (use I k in auto)
qed

lemma abk_move_good:
  assumes "abk_good n nb (H, T, NX, PV) L" "j < nb" "j' < nb" "j \<noteq> j'"
  shows "abk_good n nb (abk_move (H, T, NX, PV) j j') (L(j := [], j' := L j @ L j'))"
proof(cases "L j")
  case Nil
  have "H j = None"
    using abk_goodD(3)[OF assms(1,2)] Nil by simp
  moreover have "L(j := [], j' := L j @ L j') = L"
    using Nil by auto
  ultimately show ?thesis
    using assms(1) by (simp add: abk_move_def)
next
  case (Cons a as)
  note I = abk_goodD[OF assms(1)]
  have Ha: "H j = Some a" "T j = Some (last (L j))"
    using I(3,4)[OF assms(2)] Cons by (simp_all add: last_opt_def)
  define z where "z = last (L j)"
  have dis: "distinct (L j @ L j')"
    using I(5)[of j] I(5)[of j'] I(7) assms(4) by (auto simp add: disjoint_lists_def)
  have cc: "seg (concat_nx NX z (L j')) (concat_pv PV z (L j')) None (L j @ L j') None"
    using seg_concat[OF I(2)[OF assms(2)] I(2)[OF assms(3)] dis] Cons by (simp add: z_def)
  have mv: "abk_move (H, T, NX, PV) j j' =
            ((H(j := None))(j' := Some a), (T(j := None))(j' := last_opt (L j @ L j')),
             concat_nx NX z (L j'), concat_pv PV z (L j'))"
    using Ha I(3,4)[OF assms(3)] Cons assms(4)
    by (cases "L j'")
       (auto simp add: abk_move_def concat_nx_def concat_pv_def z_def last_opt_def fun_eq_iff)
  have other: "seg (concat_nx NX z (L j')) (concat_pv PV z (L j')) None (L k) None"
    if "k \<noteq> j" "k \<noteq> j'" "k < nb" for k
  proof-
    have "z \<notin> set (L k)"
      using disjoint_listsD[OF I(7) \<open>k \<noteq> j\<close>[symmetric]] Cons by (simp add: z_def)
    moreover have "hd (L j') \<notin> set (L k)" if "L j' \<noteq> []"
      using disjoint_listsD[OF I(7) \<open>k \<noteq> j'\<close>[symmetric] hd_in_set[OF that]] .
    ultimately show ?thesis
      using I(2)[OF \<open>k < nb\<close>] by (cases "L j'") (simp_all add: concat_nx_def concat_pv_def)
  qed
  show ?thesis
    unfolding mv
  proof(rule abk_goodI)
    fix k
    assume k: "k < nb"
    show "seg (concat_nx NX z (L j')) (concat_pv PV z (L j')) None ((L(j := [], j' := L j @ L j')) k) None"
      using cc other[OF _ _ k] by (cases "k = j'"; cases "k = j") simp_all
    show "((H(j := None))(j' := Some a)) k = first_opt ((L(j := [], j' := L j @ L j')) k)"
      using I(3)[OF k] Cons assms(4) by (simp add: first_opt_append)
    show "((T(j := None))(j' := last_opt (L j @ L j'))) k = last_opt ((L(j := [], j' := L j @ L j')) k)"
      using I(4)[OF k] assms(4) by simp
  next
    show "disjoint_lists (L(j := [], j' := L j @ L j'))"
      using I(7) by (auto simp add: disjoint_lists_def)
  next
    fix k
    show "distinct ((L(j := [], j' := L j @ L j')) k)"
      using I(5) dis by simp
  qed (use I assms in auto)
qed

subsection \<open>The Functional Model Satisfies the Specification\<close>

lemma abk_fixed_univ_buckets:
  "fixed_univ_buckets {..<n} {..<nb} (abk_invar n nb) (abk_abstract n nb) abk_empty abk_insert
     abk_remove abk_pick abk_move"
proof(unfold_locales, goal_cases)
  case (1 B x k)
  then obtain L where L: "abk_good n nb B L"
    by (auto simp add: abk_invar_def)
  obtain H T NX PV where B: "B = (H, T, NX, PV)"
    by (cases B) auto
  note I = abk_goodD[OF L[unfolded B]]
  have "x \<in> set (L k)"
    using 1(2) lists_abs_Some[OF I(7)] abk_abstract_good[OF L] by simp
  moreover hence "k < nb"
    using abk_good_key[OF L] by simp
  ultimately show ?case
    using I(6) by auto
next
  case 2
  have "abk_good n nb abk_empty (\<lambda> _. [])"
    by (simp add: abk_good_def abk_empty_def disjoint_lists_def)
  thus ?case
    by (auto simp add: abk_invar_def)
next
  case 3
  have "abk_good n nb abk_empty (\<lambda> _. [])"
    by (simp add: abk_good_def abk_empty_def disjoint_lists_def)
  thus ?case
    by (simp add: abk_abstract_good lists_abs_def fun_eq_iff)
next
  case (4 B x k)
  then obtain L where L: "abk_good n nb B L"
    by (auto simp add: abk_invar_def)
  obtain H T NX PV where B: "B = (H, T, NX, PV)"
    by (cases B) auto
  have "\<forall> k. x \<notin> set (L k)"
    using 4(4) abk_abstract_good[OF L] by (simp add: lists_abs_None)
  thus ?case
    using abk_insert_good[OF L[unfolded B]] 4(2,3) by (auto simp add: abk_invar_def B)
next
  case (5 B x k)
  then obtain L where L: "abk_good n nb B L"
    by (auto simp add: abk_invar_def)
  obtain H T NX PV where B: "B = (H, T, NX, PV)"
    by (cases B) auto
  note I = abk_goodD[OF L[unfolded B]]
  have x: "\<forall> k. x \<notin> set (L k)"
    using 5(4) abk_abstract_good[OF L] by (simp add: lists_abs_None)  have xk: "x < n" "k < nb"
    using 5(2,3) by simp_all
  note G = abk_insert_good[OF L[unfolded B] xk x]have "disjoint_lists (L(k := x # L k))"
    using abk_good_disjoint[OF G] .
  hence "lists_abs (L(k := x # L k)) = (lists_abs L)(x := Some k)"
    by (rule lists_abs_eqI) (use lists_abs_Some[OF I(7)] x in auto)
  thus ?case
    using abk_abstract_good[OF G] abk_abstract_good[OF L] 5(2,3) by (simp add: B)
next
  case (6 B x k)
  then obtain L where L: "abk_good n nb B L"
    by (auto simp add: abk_invar_def)
  obtain H T NX PV where B: "B = (H, T, NX, PV)"
    by (cases B) auto
  note I = abk_goodD[OF L[unfolded B]]
  have "x \<in> set (L k)"
    using 6(2) lists_abs_Some[OF I(7)] abk_abstract_good[OF L] by simp
  thus ?case
    using abk_remove_good[OF L[unfolded B]] by (auto simp add: abk_invar_def B)
next
  case (7 B x k)
  then obtain L where L: "abk_good n nb B L"
    by (auto simp add: abk_invar_def)
  obtain H T NX PV where B: "B = (H, T, NX, PV)"
    by (cases B) auto
  note I = abk_goodD[OF L[unfolded B]]
  have xk: "x \<in> set (L k)"
    using 7(2) lists_abs_Some[OF I(7)] abk_abstract_good[OF L] by simp
  note G = abk_remove_good[OF L[unfolded B] xk]
  have "lists_abs (L(k := remove1 x (L k))) = (lists_abs L)(x := None)"
  proof(rule lists_abs_eqI[OF abk_good_disjoint[OF G]])
    fix y k'
    show "y \<in> set ((L(k := remove1 x (L k))) k') \<longleftrightarrow> ((lists_abs L)(x := None)) y = Some k'"
      using lists_abs_Some[OF I(7)] disjoint_listsD[OF I(7) _ xk] I(5)[of k]
      by (cases "k' = k") auto
  qed
  thus ?case
    using abk_abstract_good[OF G] abk_abstract_good[OF L] by (simp add: B)
next
  case (8 B k)
  then obtain L where L: "abk_good n nb B L"
    by (auto simp add: abk_invar_def)
  obtain H T NX PV where B: "B = (H, T, NX, PV)"
    by (cases B) auto
  note I = abk_goodD[OF L[unfolded B]]
  have "abk_pick B k = first_opt (L k)"
    using I(3) 8(2) by (simp add: abk_pick_def B)
  thus ?case
    using lists_abs_Some[OF I(7)] abk_abstract_good[OF L] by (cases "L k") auto
next
  case (9 B k x)
  then obtain L where L: "abk_good n nb B L"
    by (auto simp add: abk_invar_def)
  obtain H T NX PV where B: "B = (H, T, NX, PV)"
    by (cases B) auto
  note I = abk_goodD[OF L[unfolded B]]
  have "abk_pick B k = first_opt (L k)"
    using I(3) 9(2) by (simp add: abk_pick_def B)
  hence "x \<in> set (L k)"
    using 9(3) by (cases "L k") auto
  thus ?case
    using lists_abs_Some[OF I(7)] abk_abstract_good[OF L] by simp
next
  case (10 B j j')
  then obtain L where L: "abk_good n nb B L"
    by (auto simp add: abk_invar_def)
  obtain H T NX PV where B: "B = (H, T, NX, PV)"
    by (cases B) auto
  thus ?case
    using abk_move_good[OF L[unfolded B]] 10(2-4) by (auto simp add: abk_invar_def)
next
  case (11 B j j')
  then obtain L where L: "abk_good n nb B L"
    by (auto simp add: abk_invar_def)
  obtain H T NX PV where B: "B = (H, T, NX, PV)"
    by (cases B) auto
  note I = abk_goodD[OF L[unfolded B]]
  have jj: "j < nb" "j' < nb" "j \<noteq> j'"
    using 11(2-4) by simp_all
  note G = abk_move_good[OF L[unfolded B] jj]
  have "lists_abs (L(j := [], j' := L j @ L j')) =
        (\<lambda> x. if lists_abs L x = Some j then Some j' else lists_abs L x)"
  proof(rule lists_abs_eqI[OF abk_good_disjoint[OF G]])
    fix y k
    show "y \<in> set ((L(j := [], j' := L j @ L j')) k) \<longleftrightarrow>
          (if lists_abs L y = Some j then Some j' else lists_abs L y) = Some k"
      using lists_abs_Some[OF I(7)] disjoint_listsD[OF I(7)] jj(3)
      by (cases "k = j"; cases "k = j'") auto
  qed
  moreover have "abk_abstract n nb (abk_move B j j') = lists_abs (L(j := [], j' := L j @ L j'))"
    using abk_abstract_good[OF G] by (simp add: B)
  ultimately show ?case
    unfolding abk_abstract_good[OF L] by simp
qed

section \<open>The Arrays\<close>

type_synonym abki = "nat option array \<times> nat option array \<times> nat option array \<times> nat option array"

fun abk_assn :: "nat \<Rightarrow> nat \<Rightarrow> abk \<Rightarrow> abki \<Rightarrow> assn" where
  "abk_assn n nb (H, T, NX, PV) (Ha, Ta, NXa, PVa) =
   xmap_assn nb H Ha * xmap_assn nb T Ta * xmap_assn n NX NXa * xmap_assn n PV PVa"

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
  note I = abk_goodD[OF assms]
  show "\<lbrakk>k < nb; H k = Some y\<rbrakk> \<Longrightarrow> y < n"
    using I(3)[of k] I(6)[of k] by (cases "L k") auto
  show "\<lbrakk>k < nb; T k = Some y\<rbrakk> \<Longrightarrow> y < n"
    using I(4)[of k] I(6)[of k] last_in_set[of "L k"] by (cases "L k = []") (auto simp add: last_opt_def)
  show "NX x = Some y \<Longrightarrow> y < n" "PV x = Some y \<Longrightarrow> y < n" if x: "x \<in> set (L k)"
  proof-
    have k: "k < nb"
      using abk_good_key[OF assms x] .
    obtain as bs where Lk: "L k = as @ x # bs"
      using split_list[OF x] by blast
    note m = seg_mid[OF I(2)[OF k, unfolded Lk]]
    show "NX x = Some y \<Longrightarrow> y < n"
      using m(2) I(6)[of k] Lk by (cases bs) auto
    show "PV x = Some y \<Longrightarrow> y < n"
      using m(1) I(6)[of k] Lk last_in_set[of as] by (cases "as = []") (auto simp add: last_opt_def)
  qed
qed

lemma abk_empty_rule: "<emp> abk_empty_imp n nb <\<lambda> Bi. abk_assn n nb abk_empty Bi>"
  unfolding abk_empty_imp_def abk_empty_def
  by (sep_auto heap: xmap_assn_new)

lemma abk_insert_rule:
  assumes "abk_invar n nb B" "x < n" "k < nb"
  shows "<abk_assn n nb B Bi> abk_insert_imp Bi x k <\<lambda> _. abk_assn n nb (abk_insert B x k) Bi>"
proof-
  obtain H T NX PV where B: "B = (H, T, NX, PV)"
    by (cases B) auto
  obtain Ha Ta NXa PVa where Bi: "Bi = (Ha, Ta, NXa, PVa)"
    by (cases Bi) auto
  obtain L where L: "abk_good n nb B L"
    using assms(1) by (auto simp add: abk_invar_def)
  have y: "\<And> y. H k = Some y \<Longrightarrow> y < n"
    using abk_pointers(1)[OF L[unfolded B] assms(3)] .
  show ?thesis
    unfolding B Bi abk_insert_imp_def abk_insert_def
    using assms(2,3) y
    by (cases "H k") (sep_auto heap: xmap_lookup_rule xmap_upd_rule)+
qed

lemma abk_remove_rule:
  assumes "abk_invar n nb B" "abk_abstract n nb B x = Some k"
  shows "<abk_assn n nb B Bi> abk_remove_imp Bi x k <\<lambda> _. abk_assn n nb (abk_remove B x k) Bi>"
proof-
  obtain H T NX PV where B: "B = (H, T, NX, PV)"
    by (cases B) auto
  obtain Ha Ta NXa PVa where Bi: "Bi = (Ha, Ta, NXa, PVa)"
    by (cases Bi) auto
  obtain L where L: "abk_good n nb B L"
    using assms(1) by (auto simp add: abk_invar_def)
  note I = abk_goodD[OF L[unfolded B]]
  have xk: "x \<in> set (L k)"
    using assms(2) lists_abs_Some[OF I(7)] abk_abstract_good[OF L] by simp
  have k: "k < nb"
    using abk_good_key[OF L[unfolded B] xk] .
  have x: "x < n"
    using I(6)[of k] xk by auto
  have a: "\<And> a. PV x = Some a \<Longrightarrow> a < n" and b: "\<And> b. NX x = Some b \<Longrightarrow> b < n"
    using abk_pointers(3,4)[OF L[unfolded B] xk] by auto
  show ?thesis
    unfolding B Bi abk_remove_imp_def abk_remove_def
    using k x a b
    by (cases "PV x"; cases "NX x")
       (sep_auto simp: remove_nx_def remove_pv_def heap: xmap_lookup_rule xmap_upd_rule)+
qed

lemma abk_pick_rule:
  assumes "k < nb"
  shows "<abk_assn n nb B Bi> abk_pick_imp Bi k <\<lambda> r. abk_assn n nb B Bi * \<up>(r = abk_pick B k)>"
  unfolding abk_pick_imp_def abk_pick_def using assms
  by (cases B; cases Bi) (sep_auto heap: xmap_lookup_rule)

lemma abk_move_rule:
  assumes "abk_invar n nb B" "j < nb" "j' < nb"
  shows "<abk_assn n nb B Bi> abk_move_imp Bi j j' <\<lambda> _. abk_assn n nb (abk_move B j j') Bi>"
proof-
  obtain H T NX PV where B: "B = (H, T, NX, PV)"
    by (cases B) auto
  obtain Ha Ta NXa PVa where Bi: "Bi = (Ha, Ta, NXa, PVa)"
    by (cases Bi) auto
  obtain L where L: "abk_good n nb B L"
    using assms(1) by (auto simp add: abk_invar_def)
  have z: "\<And> z. T j = Some z \<Longrightarrow> z < n"
    using abk_pointers(2)[OF L[unfolded B] assms(2)] .
  have y: "\<And> y. H j' = Some y \<Longrightarrow> y < n"
    using abk_pointers(1)[OF L[unfolded B] assms(3)] .
  have Tj: "H j \<noteq> None \<Longrightarrow> T j \<noteq> None"
    using abk_goodD(3,4)[OF L[unfolded B] assms(2)] by simp
  show ?thesis
  proof(cases "H j")
    case None
    thus ?thesis
      unfolding B Bi abk_move_imp_def abk_move_def
      using assms(2) by (sep_auto heap: xmap_lookup_rule)
  next
    case (Some a)
    then obtain zz where Tz: "T j = Some zz"
      using Tj by auto
    have zn: "zz < n"
      using z[OF Tz] .
    show ?thesis
    proof(cases "H j'")
      case None
      thus ?thesis
        unfolding B Bi abk_move_imp_def abk_move_def
        using assms(2,3) Some Tz zn by (sep_auto heap: xmap_lookup_rule xmap_upd_rule)
    next
      case (Some b)
      have "b < n"
        using y[OF Some] .
      thus ?thesis
        unfolding B Bi abk_move_imp_def abk_move_def
        using assms(2,3) \<open>H j = Some a\<close> Tz zn Some by (sep_auto heap: xmap_lookup_rule xmap_upd_rule)
    qed
  qed
qed

lemma abk_fixed_univ_buckets_imp:
  "fixed_univ_buckets_imp {..<n} {..<nb} (abk_invar n nb) (abk_abstract n nb) abk_empty abk_insert
     abk_remove abk_pick abk_move (abk_assn n nb) (abk_empty_imp n nb) abk_insert_imp
     abk_remove_imp abk_pick_imp abk_move_imp"
proof-
  interpret fixed_univ_buckets "{..<n}" "{..<nb}" "abk_invar n nb" "abk_abstract n nb" abk_empty
    abk_insert abk_remove abk_pick abk_move
    by (rule abk_fixed_univ_buckets)
  show ?thesis
    by unfold_locales
       (auto intro: abk_empty_rule abk_insert_rule abk_remove_rule abk_pick_rule abk_move_rule)
qed

end
