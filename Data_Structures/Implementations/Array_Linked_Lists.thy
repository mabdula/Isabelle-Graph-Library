theory Array_Linked_Lists
  imports
    Main
begin

section \<open>Doubly-Linked Lists in Successor and Predecessor Maps\<close>

text \<open>A list \<open>xs\<close> is stored in a successor map \<open>nx\<close> and a predecessor map \<open>pv\<close>, as in two
      arrays over the elements. @{term "seg nx pv p xs q"} says that the elements of \<open>xs\<close> are
      linked in this order, that the predecessor of the first element is \<open>p\<close> and that the
      successor of the last one is \<open>q\<close>. A whole list has \<open>p = q = None\<close>. Several disjoint lists
      may share the two maps. The lemmas below are the list surgery behind pushing an element to
      the front, removing an element and concatenating two lists, each with a constant number of
      map updates.\<close>

definition "first_opt xs = (case xs of [] \<Rightarrow> None | x # _ \<Rightarrow> Some x)"
definition "last_opt xs = (if xs = [] then None else Some (last xs))"

fun seg :: "('a \<Rightarrow> 'a option) \<Rightarrow> ('a \<Rightarrow> 'a option) \<Rightarrow> 'a option \<Rightarrow> 'a list \<Rightarrow> 'a option \<Rightarrow> bool" where
  "seg nx pv p [] q = True"
| "seg nx pv p (x # xs) q =
     (pv x = p \<and> nx x = (case xs of [] \<Rightarrow> q | y # _ \<Rightarrow> Some y) \<and> seg nx pv (Some x) xs q)"

lemma first_opt_simps[simp]: "first_opt [] = None" "first_opt (x # xs) = Some x"
  by (simp_all add: first_opt_def)

lemma last_opt_simps[simp]: "last_opt [] = None" "last_opt [x] = Some x"
  by (simp_all add: last_opt_def)

lemma first_opt_None_iff[simp]: "first_opt xs = None \<longleftrightarrow> xs = []"
  by (cases xs) simp_all

lemma last_opt_None_iff[simp]: "last_opt xs = None \<longleftrightarrow> xs = []"
  by (simp add: last_opt_def)

lemma last_opt_Cons[simp]: "last_opt (x # xs) = (if xs = [] then Some x else last_opt xs)"
  by (simp add: last_opt_def)

lemma first_opt_append: "first_opt (xs @ ys) = (if xs = [] then first_opt ys else first_opt xs)"
  by (cases xs) simp_all

lemma last_opt_append: "last_opt (xs @ ys) = (if ys = [] then last_opt xs else last_opt ys)"
  by (simp add: last_opt_def)

lemma seg_append:
  "seg nx pv p (xs @ ys) q \<longleftrightarrow>
   seg nx pv p xs (first_opt ys) \<and> seg nx pv (if xs = [] then p else Some (last xs)) ys q"
  if "ys \<noteq> []"
  using that
  by (induction xs arbitrary: p; auto split: list.split)

lemma seg_upd_nx[simp]:
  "x \<notin> set xs \<Longrightarrow> seg (nx(x := a)) pv p xs q = seg nx pv p xs q"
  by (induction xs arbitrary: p) auto

lemma seg_upd_pv[simp]:
  "x \<notin> set xs \<Longrightarrow> seg nx (pv(x := a)) p xs q = seg nx pv p xs q"
  by (induction xs arbitrary: p) auto

lemma seg_unique:
  "\<lbrakk>seg nx pv p xs None; seg nx pv p' ys None; first_opt xs = first_opt ys\<rbrakk>
    \<Longrightarrow> xs = ys"
proof(induction xs arbitrary: p p' ys)
  case Nil
  thus ?case
    by (cases ys) simp_all
next
  case (Cons x xs)
  then obtain ys' where "ys = x # ys'"
    by (cases ys) auto
  moreover hence "first_opt xs = first_opt ys'"
    using Cons.prems(1,2)
    by (cases xs; cases ys') auto
  ultimately show ?case
    using Cons.IH[of "Some x" "Some x" ys'] Cons.prems(1,2)
    by simp
qed

text \<open>Redirecting the successor of the last element, or the predecessor of the first one.\<close>

lemma seg_last_nx:
  assumes "seg nx pv p xs r" "distinct xs" "xs \<noteq> []"
  shows "seg (nx(last xs := r')) pv p xs r'"
  using assms
proof(induction xs arbitrary: p)
  case (Cons x xs)
  thus ?case
    using last_in_set[of xs]
    by (cases xs; auto)
qed simp

lemma seg_first_pv:
  assumes "seg nx pv p xs r" "distinct xs" "xs \<noteq> []"
  shows "seg nx (pv(hd xs := p')) p' xs r"
  using assms
  by (cases xs) auto

text \<open>Pushing a fresh element to the front of a whole list.\<close>

definition "push_nx nx x xs = nx(x := first_opt xs)"
definition "push_pv pv x xs =
  (case xs of [] \<Rightarrow> pv(x := None) | y # _ \<Rightarrow> (pv(x := None))(y := Some x))"

lemma seg_push_front:
  assumes "seg nx pv None xs None" "distinct xs" "x \<notin> set xs"
  shows "seg (push_nx nx x xs) (push_pv pv x xs) None (x # xs) None"
  using assms
  by (cases xs; auto simp add: push_nx_def push_pv_def)

text \<open>Removing an element from a whole list: its neighbours are linked to each other.\<close>

definition "remove_nx nx pv x =
  (case pv x of None \<Rightarrow> nx | Some a \<Rightarrow> nx(a := nx x))"
definition "remove_pv nx pv x =
  (case nx x of None \<Rightarrow> pv | Some b \<Rightarrow> pv(b := pv x))"

lemma seg_mid:
  assumes "seg nx pv None (as @ x # bs) None"
  shows "pv x = last_opt as" "nx x = first_opt bs" "seg nx pv None as (Some x)"
        "seg nx pv (Some x) bs None"
  using assms seg_append[of "x # bs" nx pv None as None]
  by (cases bs; simp add: last_opt_def)+

lemma seg_remove:
  assumes "seg nx pv None (as @ x # bs) None" "distinct (as @ x # bs)"
  shows "seg (remove_nx nx pv x) (remove_pv nx pv x) None (as @ bs) None"
proof-
  have "seg nx pv None as (Some x)" "seg nx pv (Some x) bs None" "pv x = last_opt as"
    "nx x = first_opt bs" "distinct as" "distinct bs" "as \<noteq> [] \<Longrightarrow> last as \<notin> set bs"
    "bs \<noteq> [] \<Longrightarrow> hd bs \<notin> set as"
    using assms seg_mid[of nx pv as x bs] last_in_set[of as] hd_in_set[of bs]
    by (auto simp: disjoint_iff)
  moreover have "seg (remove_nx nx pv x) (remove_pv nx pv x) None as (first_opt bs)"
    using \<open>pv x = last_opt as\<close> \<open>nx x = first_opt bs\<close>
      \<open>bs \<noteq> [] \<Longrightarrow> hd bs \<notin> set as\<close> \<open>seg nx pv None as (Some x)\<close> \<open>distinct as\<close>
      seg_last_nx[of nx pv None as "Some x" "first_opt bs"]
    by (cases "as = []")
       (cases bs; auto simp: remove_nx_def remove_pv_def last_opt_def)+
  moreover have "seg (remove_nx nx pv x) (remove_pv nx pv x) (last_opt as) bs None"
    using \<open>pv x = last_opt as\<close> \<open>nx x = first_opt bs\<close>
      \<open>as \<noteq> [] \<Longrightarrow> last as \<notin> set bs\<close> \<open>seg nx pv (Some x) bs None\<close> \<open>distinct bs\<close>
      seg_first_pv[of nx pv "Some x" bs None "last_opt as"]
    by (cases bs) (auto simp: remove_nx_def remove_pv_def last_opt_def)+
  ultimately show ?thesis
    using seg_append[of bs "remove_nx nx pv x" "remove_pv nx pv x" None as None]
    by (cases "bs = []") (auto simp: last_opt_def)+
qed

text \<open>Concatenating two disjoint whole lists, given the last element of the first one.\<close>

definition "concat_nx nx z ys = nx(z := first_opt ys)"
definition "concat_pv pv z ys =
  (case ys of [] \<Rightarrow> pv | y # _ \<Rightarrow> pv(y := Some z))"

lemma seg_concat:
  assumes "seg nx pv None xs None" "seg nx pv None ys None" "distinct (xs @ ys)" "xs \<noteq> []"
  shows "seg (concat_nx nx (last xs) ys) (concat_pv pv (last xs) ys) None (xs @ ys) None"
  using assms
  by (cases xs rule: rev_cases; cases ys; auto simp add: seg_append concat_nx_def concat_pv_def)

text \<open>The maps are only read and written at elements of the list.\<close>

lemma seg_cong:
  "\<lbrakk>\<forall> y \<in> set xs. nx y = nx' y \<and> pv y = pv' y\<rbrakk> \<Longrightarrow>
    seg nx pv p xs q = seg nx' pv' p xs q"
  by (induction xs arbitrary: p) auto

end

