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
proof(induction xs arbitrary: p)
  case (Cons x xs)
  show ?case
    using Cons.IH[OF Cons.prems, of "Some x"] Cons.prems
    by (cases xs; cases ys) simp_all
qed simp

lemma seg_upd_nx[simp]: "x \<notin> set xs \<Longrightarrow> seg (nx(x := a)) pv p xs q = seg nx pv p xs q"
  by (induction xs arbitrary: p) auto

lemma seg_upd_pv[simp]: "x \<notin> set xs \<Longrightarrow> seg nx (pv(x := a)) p xs q = seg nx pv p xs q"
  by (induction xs arbitrary: p) auto

lemma seg_unique:
  "\<lbrakk>seg nx pv p xs None; seg nx pv p' ys None; first_opt xs = first_opt ys\<rbrakk> \<Longrightarrow> xs = ys"
proof(induction xs arbitrary: p p' ys)
  case Nil
  thus ?case
    by (cases ys) simp_all
next
  case (Cons x xs)
  then obtain ys' where ys: "ys = x # ys'"
    by (cases ys) auto
  have "first_opt xs = first_opt ys'"
    using Cons.prems(1,2) ys by (cases xs; cases ys') auto
  thus ?case
    using Cons.IH[of "Some x" "Some x" ys'] Cons.prems(1,2) ys by simp
qed

text \<open>Redirecting the successor of the last element, or the predecessor of the first one.\<close>

lemma seg_last_nx:
  assumes "seg nx pv p xs r" "distinct xs" "xs \<noteq> []"
  shows "seg (nx(last xs := r')) pv p xs r'"
  using assms
proof(induction xs arbitrary: p)
  case (Cons x xs)
  show ?case
  proof(cases xs)
    case (Cons y ys)
    have "last (x # xs) \<noteq> x"
      using Cons.prems(2) \<open>xs = y # ys\<close> by (metis distinct.simps(2) last.simps last_in_set list.discI)
    thus ?thesis
      using Cons.IH[of "Some x"] Cons.prems \<open>xs = y # ys\<close> by auto
  qed (use Cons.prems in simp)
qed simp

lemma seg_first_pv:
  assumes "seg nx pv p xs r" "distinct xs" "xs \<noteq> []"
  shows "seg nx (pv(hd xs := p')) p' xs r"
  using assms by (cases xs) auto

text \<open>Pushing a fresh element to the front of a whole list.\<close>

definition "push_nx nx x xs = nx(x := first_opt xs)"
definition "push_pv pv x xs = (case xs of [] \<Rightarrow> pv(x := None) | y # _ \<Rightarrow> (pv(x := None))(y := Some x))"

lemma seg_push_front:
  assumes "seg nx pv None xs None" "distinct xs" "x \<notin> set xs"
  shows "seg (push_nx nx x xs) (push_pv pv x xs) None (x # xs) None"
proof(cases xs)
  case (Cons y ys)
  have "x \<notin> set ys" "y \<notin> set ys" "x \<noteq> y"
    using assms(2,3) Cons by auto
  thus ?thesis
    using assms(1) Cons by (simp add: push_nx_def push_pv_def)
qed (simp add: push_nx_def push_pv_def)

text \<open>Removing an element from a whole list: its neighbours are linked to each other.\<close>

definition "remove_nx nx pv x = (case pv x of None \<Rightarrow> nx | Some a \<Rightarrow> nx(a := nx x))"
definition "remove_pv nx pv x = (case nx x of None \<Rightarrow> pv | Some b \<Rightarrow> pv(b := pv x))"

lemma seg_mid:
  assumes "seg nx pv None (as @ x # bs) None"
  shows "pv x = last_opt as" "nx x = first_opt bs" "seg nx pv None as (Some x)"
        "seg nx pv (Some x) bs None"
proof-
  have "seg nx pv None as (Some x) \<and> seg nx pv (last_opt as) (x # bs) None"
    using seg_append[of "x # bs" nx pv None as None] assms by (simp add: last_opt_def)
  thus "pv x = last_opt as" "nx x = first_opt bs" "seg nx pv None as (Some x)"
       "seg nx pv (Some x) bs None"
    by (cases bs; simp)+
qed

lemma seg_remove:
  assumes "seg nx pv None (as @ x # bs) None" "distinct (as @ x # bs)"
  shows "seg (remove_nx nx pv x) (remove_pv nx pv x) None (as @ bs) None"
proof-
  note m = seg_mid[OF assms(1)]
  have dis: "distinct as" "distinct bs" "set as \<inter> set bs = {}" "x \<notin> set as" "x \<notin> set bs"
    using assms(2) by auto
  have A: "seg (remove_nx nx pv x) (remove_pv nx pv x) None as (first_opt bs)"
  proof(cases "as = []")
    case False
    have l: "last as \<notin> set bs"
      using dis(3) last_in_set[OF False] by blast
    have s: "seg (nx(last as := first_opt bs)) pv None as (first_opt bs)"
      using seg_last_nx[OF m(3) dis(1) False] .
    have h: "hd bs \<notin> set as" if "bs \<noteq> []"
      using dis(3) hd_in_set[OF that] by blast
    show ?thesis
      using m(1,2) False l s h
      by (cases bs) (auto simp add: remove_nx_def remove_pv_def last_opt_def)
  qed simp
  have B: "seg (remove_nx nx pv x) (remove_pv nx pv x) (last_opt as) bs None"
  proof(cases "bs = []")
    case False
    note bs = this
    have s: "seg nx (pv(hd bs := last_opt as)) (last_opt as) bs None"
      using seg_first_pv[OF m(4) dis(2) False] .
    show ?thesis
    proof(cases "as = []")
      case True
      thus ?thesis
        using s m(1,2) bs by (cases bs) (auto simp add: remove_nx_def remove_pv_def)
    next
      case False
      have l: "last as \<notin> set bs"
        using dis(3) last_in_set[OF False] by blast
      thus ?thesis
        using s m(1,2) bs False by (cases bs) (auto simp add: remove_nx_def remove_pv_def last_opt_def)
    qed
  qed simp
  show ?thesis
  proof(cases "bs = []")
    case True
    thus ?thesis
      using A by simp
  next
    case False
    thus ?thesis
      using A B seg_append[OF False] by (simp add: last_opt_def)
  qed
qed

text \<open>Concatenating two disjoint whole lists, given the last element of the first one.\<close>

definition "concat_nx nx z ys = nx(z := first_opt ys)"
definition "concat_pv pv z ys = (case ys of [] \<Rightarrow> pv | y # _ \<Rightarrow> pv(y := Some z))"

lemma seg_concat:
  assumes "seg nx pv None xs None" "seg nx pv None ys None" "distinct (xs @ ys)" "xs \<noteq> []"
  shows "seg (concat_nx nx (last xs) ys) (concat_pv pv (last xs) ys) None (xs @ ys) None"
proof(cases "ys = []")
  case True
  have "distinct xs"
    using assms(3) by simp
  thus ?thesis
    using seg_last_nx[OF assms(1) _ assms(4), of None] True
    by (simp add: concat_nx_def concat_pv_def)
next
  case False
  have dis: "distinct xs" "distinct ys" "last xs \<notin> set ys" "hd ys \<notin> set xs"
    using assms(3) last_in_set[OF assms(4)] hd_in_set[OF False] by auto
  have "seg (nx(last xs := first_opt ys)) pv None xs (first_opt ys)"
    using seg_last_nx[OF assms(1) dis(1) assms(4)] .
  hence A: "seg (concat_nx nx (last xs) ys) (concat_pv pv (last xs) ys) None xs (first_opt ys)"
    using dis(4) False by (cases ys) (simp_all add: concat_nx_def concat_pv_def)
  have "seg nx (pv(hd ys := Some (last xs))) (Some (last xs)) ys None"
    using seg_first_pv[OF assms(2) dis(2) False] .
  hence B: "seg (concat_nx nx (last xs) ys) (concat_pv pv (last xs) ys) (Some (last xs)) ys None"
    using dis(3) False by (cases ys) (auto simp add: concat_nx_def concat_pv_def)
  show ?thesis
    using A B seg_append[OF False] assms(4) by simp
qed

text \<open>The maps are only read and written at elements of the list.\<close>

lemma seg_cong:
  "\<lbrakk>\<forall> y \<in> set xs. nx y = nx' y \<and> pv y = pv' y\<rbrakk> \<Longrightarrow> seg nx pv p xs q = seg nx' pv' p xs q"
  by (induction xs arbitrary: p) auto

end
