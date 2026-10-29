theory Imp_Range_Iteration
  imports Separation_Logic_Imperative_HOL_Partial.Imperative_HOL_Addons
    More_Lists
begin

section \<open>Imperative Iteration over Ranges of Indices and over Lists\<close>

text \<open>Folds of a heap function over the indices \<open>[0..<i]\<close> (downwards, as a @{const foldr}) and
  \<open>[i..<n]\<close> (upwards, as a @{const foldl}), an early-exit search over \<open>[i..<n]\<close> mirroring
  @{const find}, and a fold over a HOL list. The accumulator is described by an arbitrary
  assertion, as in \<open>iterate_range_rule\<close>.\<close>

partial_function (heap) foldr_range_imp :: "(nat \<Rightarrow> 'b \<Rightarrow> 'b Heap) \<Rightarrow> nat \<Rightarrow> 'b \<Rightarrow> 'b Heap" where
  "foldr_range_imp f i a =
     (if i = 0 then return a
      else do { a' \<leftarrow> f (i - 1) a; foldr_range_imp f (i - 1) a' })"

lemma foldr_range_imp_rule:
  assumes "\<And> j a ai. j < i \<Longrightarrow> <A a ai * F> f j ai <\<lambda> r. A (g j a) r * F>"
  shows "<A a ai * F> foldr_range_imp f i ai <\<lambda> r. A (foldr g [0..<i] a) r * F>"
  using assms
proof(induction i arbitrary: a ai)
  case (Suc i)
  have [sep_heap_rules]: "<A b bi * F> foldr_range_imp f i bi <\<lambda> r. A (foldr g [0..<i] b) r * F>"
    for b bi
    by (rule Suc.IH) (rule Suc.prems, simp)
  show ?case
    by (subst foldr_range_imp.simps) (sep_auto heap: Suc.prems)
qed (subst foldr_range_imp.simps, sep_auto)

partial_function (heap) foldl_range_imp ::
  "(nat \<Rightarrow> 'b \<Rightarrow> 'b Heap) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'b \<Rightarrow> 'b Heap" where
  "foldl_range_imp f i n a =
     (if i < n then do { a' \<leftarrow> f i a; foldl_range_imp f (Suc i) n a' }
      else return a)"

lemma foldl_range_imp_rule:
  assumes "\<And> j a ai. \<lbrakk>i \<le> j; j < n\<rbrakk> \<Longrightarrow> <A a ai * F> f j ai <\<lambda> r. A (g j a) r * F>"
  shows "<A a ai * F> foldl_range_imp f i n ai <\<lambda> r. A (foldl (\<lambda> a j. g j a) a [i..<n]) r * F>"
  using assms
proof(induction "n - i" arbitrary: i a ai)
  case (Suc m)
  have "i < n"
    using Suc.hyps(2)
    by simp
  have [sep_heap_rules]: "<A b bi * F> foldl_range_imp f (Suc i) n bi
      <\<lambda> r. A (foldl (\<lambda> a j. g j a) b [Suc i..<n]) r * F>" for b bi
    by (rule Suc.hyps(1)) (use Suc.hyps(2) in simp, rule Suc.prems, simp_all)
  show ?case
    using \<open>i < n\<close>
    by (subst foldl_range_imp.simps) (sep_auto heap: Suc.prems simp: upt_conv_Cons)
qed (subst foldl_range_imp.simps, sep_auto)

partial_function (heap) find_range_imp :: "(nat \<Rightarrow> bool Heap) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat option Heap" where
  "find_range_imp P i n =
     (if i < n then do { b \<leftarrow> P i; if b then return (Some i) else find_range_imp P (Suc i) n }
      else return None)"

lemma find_range_imp_rule:
  assumes "\<And> j. \<lbrakk>i \<le> j; j < n\<rbrakk> \<Longrightarrow> <F> P j <\<lambda> r. F * \<up>(r = p j)>"
  shows "<F> find_range_imp P i n <\<lambda> r. F * \<up>(r = find p [i..<n])>"
  using assms
proof(induction "n - i" arbitrary: i)
  case (Suc m)
  have "i < n"
    using Suc.hyps(2)
    by simp
  have [sep_heap_rules]: "<F> find_range_imp P (Suc i) n <\<lambda> r. F * \<up>(r = find p [Suc i..<n])>"
    by (rule Suc.hyps(1)) (use Suc.hyps(2) in simp, rule Suc.prems, simp_all)
  show ?case
    using \<open>i < n\<close>
    by (subst find_range_imp.simps) (sep_auto heap: Suc.prems simp: upt_conv_Cons)
qed (subst find_range_imp.simps, sep_auto)

primrec foldl_list_imp :: "('a \<Rightarrow> 'b \<Rightarrow> 'b Heap) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b Heap" where
  "foldl_list_imp f [] a = return a"
| "foldl_list_imp f (x # xs) a = do { a' \<leftarrow> f x a; foldl_list_imp f xs a' }"

lemma foldl_list_imp_rule:
  assumes "\<And> x a ai. x \<in> set xs \<Longrightarrow> <A a ai * F> f x ai <\<lambda> r. A (g x a) r * F>"
  shows "<A a ai * F> foldl_list_imp f xs ai <\<lambda> r. A (foldl (\<lambda> a x. g x a) a xs) r * F>"
  using assms
proof(induction xs arbitrary: a ai)
  case (Cons x xs)
  have [sep_heap_rules]: "<A b bi * F> foldl_list_imp f xs bi
      <\<lambda> r. A (foldl (\<lambda> a x. g x a) b xs) r * F>" for b bi
    by (rule Cons.IH) (rule Cons.prems, simp)
  show ?case
    by (sep_auto heap: Cons.prems)
qed sep_auto

subsection \<open>Filtering a Range and Lists of Pairs\<close>

definition "filter_range_imp P n =
  foldr_range_imp (\<lambda> y acc. do { b \<leftarrow> P y; return (if b then y # acc else acc) }) n []"

lemma filter_range_imp_rule:
  assumes "\<And> y. y < n \<Longrightarrow> <F> P y <\<lambda> r. F * \<up>(r = p y)>"
  shows "<F> filter_range_imp P n <\<lambda> r. F * \<up>(r = filter p [0..<n])>"
  unfolding filter_range_imp_def
  by (rule ht_cons[rotated 2, OF foldr_range_imp_rule[where A = "\<lambda> a ai. \<up>(ai = a)"
        and g = "\<lambda> y acc. if p y then y # acc else acc"]])
     (sep_auto heap: assms simp: foldr_cons_filter)+

definition "map_range_imp P n =
  foldr_range_imp (\<lambda> y acc. do { b \<leftarrow> P y; return (b # acc) }) n []"

lemma map_range_imp_rule:
  assumes "\<And> y. y < n \<Longrightarrow> <F> P y <\<lambda> r. F * \<up>(r = p y)>"
  shows "<F> map_range_imp P n <\<lambda> r. F * \<up>(r = map p [0..<n])>"
  unfolding map_range_imp_def
  by (rule ht_cons[rotated 2, OF foldr_range_imp_rule[where A = "\<lambda> a ai. \<up>(ai = a)"
        and g = "\<lambda> y acc. p y # acc"]])
     (sep_auto heap: assms simp: foldr_cons_map)+

definition "pairs_range_imp P Q n a =
  foldr_range_imp (\<lambda> x acc. do {
     b \<leftarrow> P x;
     if b then foldr_range_imp (\<lambda> y acc. do { c \<leftarrow> Q x y;
                                              return (if c then (x, y) # acc else acc) }) n acc
     else return acc }) n a"

lemma pairs_range_imp_rule:
  assumes "\<And> x. x < n \<Longrightarrow> <F> P x <\<lambda> r. F * \<up>(r = p x)>"
    "\<And> x y. \<lbrakk>x < n; y < n\<rbrakk> \<Longrightarrow> <F> Q x y <\<lambda> r. F * \<up>(r = q x y)>"
  shows "<F> pairs_range_imp P Q n a
         <\<lambda> r. F * \<up>(r = concat (map (\<lambda> x. map (Pair x) (filter (q x) [0..<n])) (filter p [0..<n])) @ a)>"
proof-
  have [sep_heap_rules]: "<\<up>(ai = b) * F>
      foldr_range_imp (\<lambda> y acc. do { c \<leftarrow> Q x y; return (if c then (x, y) # acc else acc) }) n ai
      <\<lambda> r. \<up>(r = foldr (\<lambda> y acc. if q x y then (x, y) # acc else acc) [0..<n] b) * F>"
    if "x < n" for x b ai
    by (rule foldr_range_imp_rule[where A = "\<lambda> a ai. \<up>(ai = a)"])
       (use that in \<open>sep_auto heap: assms(2)\<close>)
  have "<\<up>(ai = b) * F>
     do { c \<leftarrow> P x;
          if c then foldr_range_imp (\<lambda> y acc. do { c \<leftarrow> Q x y;
                                              return (if c then (x, y) # acc else acc) }) n ai
          else return ai }
     <\<lambda> r. \<up>(r = (if p x then foldr (\<lambda> y acc. if q x y then (x, y) # acc else acc) [0..<n] b
                   else b)) * F>" if "x < n" for x b ai
    using that
    by (sep_auto heap: assms(1))
  hence "<\<up>(a = a) * F> pairs_range_imp P Q n a
        <\<lambda> r. \<up>(r = foldr (\<lambda> x acc. if p x then
                    foldr (\<lambda> y acc. if q x y then (x, y) # acc else acc) [0..<n] acc else acc)
                  [0..<n] a) * F>"
    unfolding pairs_range_imp_def
    by (rule foldr_range_imp_rule[where A = "\<lambda> a ai. \<up>(ai = a)"])
  thus ?thesis
    by (rule ht_cons[rotated 2]) (sep_auto simp: foldr_pairs)+
qed

text \<open>The upward fold with an accumulator assertion that also sees the current index.\<close>

lemma foldl_range_imp_idx_rule:
  assumes "\<And> j a ai. \<lbrakk>i \<le> j; j < n\<rbrakk> \<Longrightarrow> <A j a ai * F> f j ai <\<lambda> r. A (Suc j) (g j a) r * F>"
    and "i \<le> n"
  shows "<A i a ai * F> foldl_range_imp f i n ai <\<lambda> r. A n (foldl (\<lambda> a j. g j a) a [i..<n]) r * F>"
  using assms
proof(induction "n - i" arbitrary: i a ai)
  case 0
  hence "i = n"
    by simp
  thus ?case
    by (subst foldl_range_imp.simps) sep_auto
next
  case (Suc m)
  have "i < n"
    using Suc.hyps(2)
    by simp
  have [sep_heap_rules]: "<A (Suc i) b bi * F> foldl_range_imp f (Suc i) n bi
      <\<lambda> r. A n (foldl (\<lambda> a j. g j a) b [Suc i..<n]) r * F>" for b bi
    by (rule Suc.hyps(1))
       (use Suc.hyps(2) \<open>i < n\<close> in simp, rule Suc.prems, simp_all add: \<open>i < n\<close> Suc_leI)
  show ?case
    using \<open>i < n\<close>
    by (subst foldl_range_imp.simps) (sep_auto heap: Suc.prems simp: upt_conv_Cons)
qed

subsection \<open>Writing into Existing Arrays\<close>

text \<open>Overwriting an array of length \<open>n\<close> with the values of a function.\<close>

definition "fill_range_imp f n a = foldl_range_imp (\<lambda> i a. Array.upd i (f i) a) 0 n a"

lemma fill_range_imp_rule:
  "<a \<mapsto>\<^sub>a l * \<up>(length l = n)> fill_range_imp f n a <\<lambda> r. a \<mapsto>\<^sub>a map f [0..<n] * \<up>(r = a)>"
  unfolding fill_range_imp_def
  by (rule ht_cons[rotated 2, OF foldl_range_imp_idx_rule[where
        A = "\<lambda> j l' r. a \<mapsto>\<^sub>a l' * \<up>(r = a \<and> length l' = n \<and> take j l' = map f [0..<j])"
        and g = "\<lambda> j l'. list_update l' j (f j)" and F = emp and a = l]])
     (sep_auto simp: take_Suc_upd)+

text \<open>Overwriting an array of length \<open>n\<close> with the results of a computation that keeps \<open>F\<close>.\<close>

definition "copy_range_imp P n a = foldr_range_imp (\<lambda> i _. do { x \<leftarrow> P i; Array.upd i x a; return () }) n ()"

lemma copy_range_imp_rule:
  assumes "\<And> i. i < n \<Longrightarrow> <F> P i <\<lambda> r. F * \<up>(r = p i)>"
  shows "<a \<mapsto>\<^sub>a l * F * \<up>(length l = n)> copy_range_imp P n a <\<lambda> _. a \<mapsto>\<^sub>a map p [0..<n] * F>"
  unfolding copy_range_imp_def
  by (rule ht_pure_pre, rule ht_cons[rotated 2, OF foldr_range_imp_rule[where
        A = "\<lambda> l _. a \<mapsto>\<^sub>a l * \<up>(length l = n)" and g = "\<lambda> j l. list_update l j (p j)"]])
     (sep_auto heap: assms simp: foldr_upd_range)+

text \<open>Writing the indices below \<open>n\<close> satisfying a predicate, in increasing order, into the
  first cells of an array of length at least \<open>n\<close>; the result is their number.\<close>

definition "collect_range_imp P n Fa =
  foldl_range_imp (\<lambda> y k. do { b \<leftarrow> P y;
                              if b then do { Array.upd k y Fa; return (Suc k) } else return k })
    0 n 0"

lemma collect_range_imp_rule:
  assumes "\<And> y. y < n \<Longrightarrow> <F> P y <\<lambda> r. F * \<up>(r = p y)>" "n \<le> length fl"
  shows "<Fa \<mapsto>\<^sub>a fl * F> collect_range_imp P n Fa
         <\<lambda> k. \<exists>\<^sub>A fl'. Fa \<mapsto>\<^sub>a fl' * F *
               \<up>(length fl' = length fl \<and> k = length (filter p [0..<n]) \<and>
                 take k fl' = filter p [0..<n])>"
  unfolding collect_range_imp_def
  by (rule ht_cons[rotated 2, OF foldl_range_imp_idx_rule[where
        A = "\<lambda> j (fk :: nat list \<times> nat) k. Fa \<mapsto>\<^sub>a fst fk *
          \<up>(k = snd fk \<and> length (fst fk) = length fl \<and> k = length (filter p [0..<j]) \<and>
            take k (fst fk) = filter p [0..<j])"
        and g = "\<lambda> j fk. if p j then (list_update (fst fk) (snd fk) j, Suc (snd fk)) else fk"
        and a = "(fl, 0)"]])
     (use assms(2) length_filter_le[of p "[0..<j]" for j] in
       \<open>sep_auto heap: assms(1) simp: take_upd_Suc take_Suc_upd\<close>)+

declare foldr_range_imp.simps[code] foldl_range_imp.simps[code] find_range_imp.simps[code]

end
