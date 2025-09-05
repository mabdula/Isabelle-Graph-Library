theory Insertion_Sort_Desc
  imports "HOL-Library.Multiset"
begin

section \<open>Insertion Sort\<close>

text \<open>The Best-In.Greedy Algorithm uses sorting as a preprocessing step.
Nota bene: The quadratic running time of insertion sort is asymptotically irrelevant.\<close>


fun insort1_key_desc :: "('a \<Rightarrow> 'k::linorder) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "insort1_key_desc f x [] = [x]" |
  "insort1_key_desc f x (y # ys) = (if f x \<ge> f y then x # y # ys else y # insort1_key_desc f x ys)"

fun insort_key_desc :: "('a \<Rightarrow> 'k::linorder) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "insort_key_desc f [] = []" |
  "insort_key_desc f (x # xs) = insort1_key_desc f x (insort_key_desc f xs)"


lemma mset_insort1_key_desc: "mset (insort1_key_desc f x xs) = {#x#} + mset xs"
  by (induction xs) simp_all

lemma mset_insort_key_desc: "mset (insort_key_desc f xs) = mset xs"
  by (induction xs) (simp_all add: mset_insort1_key_desc)

lemma set_insort_key_desc: "set (insort_key_desc c xs) = set xs"
  by (meson mset_eq_setD mset_insort_key_desc)

lemma length_insort_key_desc: "length (insort_key_desc c xs) = length xs"
  using mset_eq_length mset_insort_key_desc by blast


lemma set_insort1_key_desc: "set (insort1_key_desc f x xs) = {x} \<union> set xs"
  by (induction xs) auto

lemma sorted_desc_insort1_key_desc: "sorted_wrt (\<ge>) (map f (insort1_key_desc f a xs)) = sorted_wrt (\<ge>) (map f xs)"
  by(induction xs)(auto simp: set_insort1_key_desc)

lemma sorted_desc_insort_key_desc: "sorted_wrt (\<ge>) (map f (insort_key_desc f xs))"
  by(induction xs) (simp_all add: sorted_desc_insort1_key_desc)

lemma sorted_desc_f_insort_key_desc: "sorted_wrt (\<lambda>x1 x2. f x1 \<ge> f x2) (insort_key_desc f xs)"
  using sorted_desc_insort_key_desc sorted_wrt_map by force


lemma insort1_key_desc_is_Cons: "\<forall>x\<in>set xs. f a \<ge> f x \<Longrightarrow> insort1_key_desc f a xs = a # xs"
  by (cases xs) auto

lemma filter_insort1_desc_key_neg:
  "\<not> P x \<Longrightarrow> filter P (insort1_key_desc f x xs) = filter P xs"
  by (induction xs) simp_all

lemma filter_insort1_desc_key_pos:
  "sorted_wrt (\<ge>) (map f xs) \<Longrightarrow> P x \<Longrightarrow> filter P (insort1_key_desc f x xs) = insort1_key_desc f x (filter P xs)"
  by (induction xs) (auto, subst insort1_key_desc_is_Cons, auto)

lemma insort_key_desc_stable: "filter (\<lambda>y. f y = k) (insort_key_desc f xs) = filter (\<lambda>y. f y = k) xs"
proof (induction xs)
  case Nil thus ?case by simp
next
  case (Cons a xs)
  thus ?case
  proof (cases "f a = k")
    case False thus ?thesis  by (simp add: Cons.IH filter_insort1_desc_key_neg)
  next
    case True
    have "filter (\<lambda>y. f y = k) (insort_key_desc f (a # xs))
      = filter (\<lambda>y. f y = k) (insort1_key_desc f a (insort_key_desc f xs))"  by simp
    also have "\<dots> = insort1_key_desc f a (filter (\<lambda>y. f y = k) (insort_key_desc f xs))"
      by (simp add: True filter_insort1_desc_key_pos sorted_desc_insort_key_desc)
    also have "\<dots> = insort1_key_desc f a (filter (\<lambda>y. f y = k) xs)"  by (simp add: Cons.IH)
    also have "\<dots> = a # (filter (\<lambda>y. f y = k) xs)"  by(simp add: True insort1_key_desc_is_Cons)
    also have "\<dots> = filter (\<lambda>y. f y = k) (a # xs)" by (simp add: True)
    finally show ?thesis .
  qed
qed

end