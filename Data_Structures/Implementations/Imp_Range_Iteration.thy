theory Imp_Range_Iteration
  imports Separation_Logic_Imperative_HOL_Partial.Sep_Main
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
  case 0
  show ?case
    by (subst foldr_range_imp.simps) sep_auto
next
  case (Suc i)
  have IH: "<A b bi * F> foldr_range_imp f i bi <\<lambda> r. A (foldr g [0..<i] b) r * F>" for b bi
    by (rule Suc.IH) (rule Suc.prems, simp)
  have f: "<A a ai * F> f i ai <\<lambda> r. A (g i a) r * F>"
    by (rule Suc.prems) simp
  show ?case
    by (subst foldr_range_imp.simps) (sep_auto heap: f IH)
qed

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
  case 0
  have "\<not> i < n"
    using 0(1) by simp
  then show ?case
    by (subst foldl_range_imp.simps) sep_auto
next
  case (Suc m)
  have i: "i < n"
    using Suc.hyps(2) by simp
  have IH: "<A b bi * F> foldl_range_imp f (Suc i) n bi
              <\<lambda> r. A (foldl (\<lambda> a j. g j a) b [Suc i..<n]) r * F>" for b bi
    by (rule Suc.hyps(1)) (use Suc.hyps(2) in simp, rule Suc.prems, simp_all)
  have f: "<A a ai * F> f i ai <\<lambda> r. A (g i a) r * F>"
    by (rule Suc.prems) (simp_all add: i)
  show ?case
    by (subst foldl_range_imp.simps) (sep_auto heap: f IH simp: i upt_conv_Cons)
qed

partial_function (heap) find_range_imp :: "(nat \<Rightarrow> bool Heap) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat option Heap" where
  "find_range_imp P i n =
     (if i < n then do { b \<leftarrow> P i; if b then return (Some i) else find_range_imp P (Suc i) n }
      else return None)"

lemma find_range_imp_rule:
  assumes "\<And> j. \<lbrakk>i \<le> j; j < n\<rbrakk> \<Longrightarrow> <F> P j <\<lambda> r. F * \<up>(r = p j)>"
  shows "<F> find_range_imp P i n <\<lambda> r. F * \<up>(r = find p [i..<n])>"
  using assms
proof(induction "n - i" arbitrary: i)
  case 0
  have "\<not> i < n"
    using 0(1) by simp
  then show ?case
    by (subst find_range_imp.simps) sep_auto
next
  case (Suc m)
  have i: "i < n"
    using Suc.hyps(2) by simp
  have IH: "<F> find_range_imp P (Suc i) n <\<lambda> r. F * \<up>(r = find p [Suc i..<n])>"
    by (rule Suc.hyps(1)) (use Suc.hyps(2) in simp, rule Suc.prems, simp_all)
  have P: "<F> P i <\<lambda> r. F * \<up>(r = p i)>"
    by (rule Suc.prems) (simp_all add: i)
  show ?case
    by (subst find_range_imp.simps) (sep_auto heap: P IH simp: i upt_conv_Cons)
qed

primrec foldl_list_imp :: "('a \<Rightarrow> 'b \<Rightarrow> 'b Heap) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b Heap" where
  "foldl_list_imp f [] a = return a"
| "foldl_list_imp f (x # xs) a = do { a' \<leftarrow> f x a; foldl_list_imp f xs a' }"

lemma foldl_list_imp_rule:
  assumes "\<And> x a ai. x \<in> set xs \<Longrightarrow> <A a ai * F> f x ai <\<lambda> r. A (g x a) r * F>"
  shows "<A a ai * F> foldl_list_imp f xs ai <\<lambda> r. A (foldl (\<lambda> a x. g x a) a xs) r * F>"
  using assms
proof(induction xs arbitrary: a ai)
  case Nil
  show ?case
    by sep_auto
next
  case (Cons x xs)
  have IH: "<A b bi * F> foldl_list_imp f xs bi <\<lambda> r. A (foldl (\<lambda> a x. g x a) b xs) r * F>"
    for b bi
    by (rule Cons.IH) (rule Cons.prems, simp)
  have f: "<A a ai * F> f x ai <\<lambda> r. A (g x a) r * F>"
    by (rule Cons.prems) simp
  show ?case
    by (sep_auto heap: f IH)
qed

lemma ht_ex_pre: "(\<And> x. <P x> c <Q>) \<Longrightarrow> <\<exists>\<^sub>A x. P x> c <Q>"
  unfolding hoare_triple_wlp by (auto simp: mod_ex_dist)

lemma ht_pure_pre: "(b \<Longrightarrow> <P> c <Q>) \<Longrightarrow> <P * \<up>b> c <Q>"
  unfolding hoare_triple_wlp by (auto simp: mod_pure_star_dist)

text \<open>Framing a triple, with the pre- and postconditions rearranged by entailments.\<close>

lemma ht_frame_ac:
  assumes "<P> c <Q>" "P' \<Longrightarrow>\<^sub>A P * R" "\<And> x. Q x * R \<Longrightarrow>\<^sub>A Q' x"
  shows "<P'> c <Q'>"
proof-
  have "<P * R> c <\<lambda> x. Q x * R>"
    by (rule ht_frame[OF assms(1)])
  then show ?thesis
    by (rule ht_cons_pre[OF assms(2) ht_cons_post]) (rule ent_true_drop(2)[OF assms(3)])
qed

subsection \<open>Filtering a Range and Lists of Pairs\<close>

lemma foldr_cons_filter:
  "foldr (\<lambda> y acc. if p y then f y # acc else acc) xs a = map f (filter p xs) @ a"
  by (induction xs) simp_all

lemma foldr_pairs:
  "foldr (\<lambda> x acc. if p x then foldr (\<lambda> y acc. if q x y then (x, y) # acc else acc) ys acc 
                   else acc) xs a = 
   concat (map (\<lambda> x. map (Pair x) (filter (q x) ys)) (filter p xs)) @ a"
  by (induction xs) (simp_all add: foldr_cons_filter)

lemma find_filter: "find p (filter q xs) = find (\<lambda> x. q x \<and> p x) xs"
  by (induction xs) simp_all

lemma list_ex_filter: "list_ex p (filter q xs) = list_ex (\<lambda> x. q x \<and> p x) xs"
  by (induction xs) simp_all

lemma list_ex_find: "list_ex p xs = (find p xs \<noteq> None)"
  by (induction xs) simp_all

lemma find_SomeD: "find p xs = Some x \<Longrightarrow> p x \<and> x \<in> set xs"
  by (induction xs) (simp_all split: if_splits)

definition "filter_range_imp P n = 
  foldr_range_imp (\<lambda> y acc. do { b \<leftarrow> P y; return (if b then y # acc else acc) }) n []"

lemma filter_range_imp_rule:
  assumes "\<And> y. y < n \<Longrightarrow> <F> P y <\<lambda> r. F * \<up>(r = p y)>"
  shows "<F> filter_range_imp P n <\<lambda> r. F * \<up>(r = filter p [0..<n])>"
proof-
  have step: "<\<up>(ai = a) * F> do { b \<leftarrow> P j; return (if b then j # ai else ai) } 
                <\<lambda> r. \<up>(r = (if p j then j # a else a)) * F>" if "j < n" for j a ai
    by (sep_auto heap: assms[OF that])
  have run: "<\<up>(([] :: nat list) = []) * F> 
          foldr_range_imp (\<lambda> y acc. do { b \<leftarrow> P y; return (if b then y # acc else acc) }) n [] 
        <\<lambda> r. \<up>(r = foldr (\<lambda> y acc. if p y then y # acc else acc) [0..<n] []) * F>"
    by (rule foldr_range_imp_rule[where A = "\<lambda> a ai. \<up>(ai = a)"]) (rule step)
  show ?thesis 
    unfolding filter_range_imp_def
    by (rule ht_cons_post[OF ht_cons_pre[OF _ run]]) (sep_auto simp: foldr_cons_filter)+
qed

definition "map_range_imp P n = 
  foldr_range_imp (\<lambda> y acc. do { b \<leftarrow> P y; return (b # acc) }) n []"

lemma map_range_imp_rule:
  assumes "\<And> y. y < n \<Longrightarrow> <F> P y <\<lambda> r. F * \<up>(r = p y)>"
  shows "<F> map_range_imp P n <\<lambda> r. F * \<up>(r = map p [0..<n])>"
proof-
  have step: "<\<up>(ai = a) * F> do { b \<leftarrow> P j; return (b # ai) } 
                <\<lambda> r. \<up>(r = p j # a) * F>" if "j < n" for j a ai
    by (sep_auto heap: assms[OF that])
  have run: "<\<up>(([] :: 'a list) = []) * F> 
          foldr_range_imp (\<lambda> y acc. do { b \<leftarrow> P y; return (b # acc) }) n [] 
        <\<lambda> r. \<up>(r = foldr (\<lambda> y acc. p y # acc) [0..<n] []) * F>"
    by (rule foldr_range_imp_rule[where A = "\<lambda> a ai. \<up>(ai = a)"]) (rule step)
  have "foldr (\<lambda> y acc. p y # acc) xs [] = map p xs" for xs
    by (induction xs) simp_all
  then show ?thesis 
    unfolding map_range_imp_def
    by (intro ht_cons_post[OF ht_cons_pre[OF _ run]]) sep_auto+
qed

definition "pairs_range_imp P Q n a = 
  foldr_range_imp (\<lambda> x acc. do { 
     b \<leftarrow> P x; 
     if b then foldr_range_imp (\<lambda> y acc. do { c \<leftarrow> Q x y; 
                                              return (if c then (x, y) # acc else acc) }) n acc 
     else return acc }) n a"

lemma pairs_range_imp_rule:
  assumes P: "\<And> x. x < n \<Longrightarrow> <F> P x <\<lambda> r. F * \<up>(r = p x)>"
    and Q: "\<And> x y. \<lbrakk>x < n; y < n\<rbrakk> \<Longrightarrow> <F> Q x y <\<lambda> r. F * \<up>(r = q x y)>"
  shows "<F> pairs_range_imp P Q n a 
         <\<lambda> r. F * \<up>(r = concat (map (\<lambda> x. map (Pair x) (filter (q x) [0..<n])) (filter p [0..<n])) @ a)>"
proof-
  have inner: "<\<up>(ai = b) * F> 
          foldr_range_imp (\<lambda> y acc. do { c \<leftarrow> Q x y; return (if c then (x, y) # acc else acc) }) n ai
        <\<lambda> r. \<up>(r = foldr (\<lambda> y acc. if q x y then (x, y) # acc else acc) [0..<n] b) * F>" 
    if "x < n" for x b ai
  proof(rule foldr_range_imp_rule[where A = "\<lambda> a ai. \<up>(ai = a)"])
    fix j a ai
    assume "j < n"
    show "<\<up>(ai = a) * F> do { c \<leftarrow> Q x j; return (if c then (x, j) # ai else ai) } 
            <\<lambda> r. \<up>(r = (if q x j then (x, j) # a else a)) * F>"
      by (sep_auto heap: Q[OF that \<open>j < n\<close>])
  qed
  have step: "<\<up>(ai = b) * F> 
     do { c \<leftarrow> P x; 
          if c then foldr_range_imp (\<lambda> y acc. do { c \<leftarrow> Q x y; 
                                              return (if c then (x, y) # acc else acc) }) n ai 
          else return ai }
     <\<lambda> r. \<up>(r = (if p x then foldr (\<lambda> y acc. if q x y then (x, y) # acc else acc) [0..<n] b 
                   else b)) * F>" if "x < n" for x b ai
    by (sep_auto heap: P[OF that] inner[OF that])
  have run: "<\<up>(a = a) * F> pairs_range_imp P Q n a 
        <\<lambda> r. \<up>(r = foldr (\<lambda> x acc. if p x then 
                    foldr (\<lambda> y acc. if q x y then (x, y) # acc else acc) [0..<n] acc else acc) 
                  [0..<n] a) * F>"
    unfolding pairs_range_imp_def
    by (rule foldr_range_imp_rule[where A = "\<lambda> a ai. \<up>(ai = a)"]) (rule step)
  show ?thesis 
    by (rule ht_cons_post[OF ht_cons_pre[OF _ run]]) (sep_auto simp: foldr_pairs)+
qed

text \<open>The upward fold with an accumulator assertion that also sees the current index.\<close>

lemma foldl_range_imp_idx_rule:
  assumes "\<And> j a ai. \<lbrakk>i \<le> j; j < n\<rbrakk> \<Longrightarrow> <A j a ai * F> f j ai <\<lambda> r. A (Suc j) (g j a) r * F>"
    and "i \<le> n"
  shows "<A i a ai * F> foldl_range_imp f i n ai <\<lambda> r. A n (foldl (\<lambda> a j. g j a) a [i..<n]) r * F>"
  using assms
proof(induction "n - i" arbitrary: i a ai)
  case 0
  have i: "i = n"
    using 0(1) 0(3) by simp
  show ?case
    unfolding i by (subst foldl_range_imp.simps) sep_auto
next
  case (Suc m)
  have i: "i < n"
    using Suc.hyps(2) by simp
  have IH: "<A (Suc i) b bi * F> foldl_range_imp f (Suc i) n bi
              <\<lambda> r. A n (foldl (\<lambda> a j. g j a) b [Suc i..<n]) r * F>" for b bi
    by (rule Suc.hyps(1)) (use Suc.hyps(2) i in simp, rule Suc.prems, simp_all add: i Suc_leI)
  have f: "<A i a ai * F> f i ai <\<lambda> r. A (Suc i) (g i a) r * F>"
    by (rule Suc.prems) (simp_all add: i)
  show ?case
    by (subst foldl_range_imp.simps) (sep_auto heap: f IH simp: i upt_conv_Cons)
qed

subsection \<open>Writing into Existing Arrays\<close>

lemma take_upd_Suc: "k < length l \<Longrightarrow> take (Suc k) (list_update l k x) = take k l @ [x]"
  by (subst take_Suc_conv_app_nth) (simp_all add: list_update_beyond)

lemma take_Suc_upd: "k < length l \<Longrightarrow> list_update (take (Suc k) l) k x = take k l @ [x]"
  using take_upd_Suc[of k l x] by (simp add: take_update_swap)

text \<open>Updating a list at the positions @{term "g j"} for the elements @{term j} of a list, with
      @{term g} injective.\<close>

lemma length_foldl_upd [simp]: "length (foldl (\<lambda>W j. list_update W (g j) (f j)) W xs) = length W"
  by (induction xs arbitrary: W) auto

lemma foldl_upd_nth_miss:
  "x \<notin> g ` set xs \<Longrightarrow> foldl (\<lambda>W j. list_update W (g j) (f j)) W xs ! x = W ! x"
  by (induction xs arbitrary: W) auto

lemma foldl_upd_nth_hit:
  assumes "inj_on g (set xs)" "i \<in> set xs" "\<And>j. j \<in> set xs \<Longrightarrow> g j < length W"
  shows "foldl (\<lambda>W j. list_update W (g j) (f j)) W xs ! g i = f i"
  using assms
proof (induction xs arbitrary: W)
  case Nil thus ?case by simp
next
  case (Cons a xs)
  show ?case
  proof (cases "i \<in> set xs")
    case True
    have "inj_on g (set xs)" using Cons.prems(1) by simp
    thus ?thesis using True Cons.prems(3) Cons.IH[of "list_update W (g a) (f a)"] by simp
  next
    case False
    hence i: "i = a" using Cons.prems(2) by simp
    have "g a \<notin> g ` set xs" using Cons.prems(1) False i by (auto simp: inj_on_def)
    thus ?thesis using i Cons.prems(3)[of a] by (simp add: foldl_upd_nth_miss)
  qed
qed

text \<open>Overwriting an array of length \<open>n\<close> with the values of a function.\<close>

definition "fill_range_imp f n a = foldl_range_imp (\<lambda> i a. Array.upd i (f i) a) 0 n a"

lemma fill_range_imp_rule:
  "<a \<mapsto>\<^sub>a l * \<up>(length l = n)> fill_range_imp f n a <\<lambda> r. a \<mapsto>\<^sub>a map f [0..<n] * \<up>(r = a)>"
proof-
  let ?A = "\<lambda> j l' r. a \<mapsto>\<^sub>a l' * \<up>(r = a \<and> length l' = n \<and> take j l' = map f [0..<j])"
  have step: "<?A j l' ai * emp> Array.upd j (f j) ai <\<lambda> r. ?A (Suc j) (list_update l' j (f j)) r * emp>" 
    if "j < n" for j l' ai
    using that by (sep_auto simp: take_Suc_upd)
  have run: "<?A 0 l a * emp> fill_range_imp f n a 
             <\<lambda> r. ?A n (foldl (\<lambda> l' j. list_update l' j (f j)) l [0..<n]) r * emp>"
    unfolding fill_range_imp_def by (rule foldl_range_imp_idx_rule) (rule step, simp_all)
  have fin: "\<lbrakk>length l' = n; take n l' = map f [0..<n]\<rbrakk> \<Longrightarrow> l' = map f [0..<n]" for l'
    by simp
  show ?thesis
    by (rule ht_cons_post[OF ht_cons_pre[OF _ run]]) (sep_auto dest: fin)+
qed

text \<open>Overwriting an array of length \<open>n\<close> with the results of a computation that keeps \<open>F\<close>.\<close>

definition "copy_range_imp P n a = foldr_range_imp (\<lambda> i _. do { x \<leftarrow> P i; Array.upd i x a; return () }) n ()"

lemma foldr_upd_range:
  "k \<le> length l \<Longrightarrow> foldr (\<lambda> j l. list_update l j (p j)) [0..<k] l = map p [0..<k] @ drop k l"
proof(induction k arbitrary: l)
  case (Suc k)
  have "drop k (list_update l k (p k)) = p k # drop (Suc k) l"
    using Suc.prems
    by (simp only: drop_update_swap[of k k] order_refl, subst Cons_nth_drop_Suc[symmetric]) simp_all
  thus ?case
    using Suc by simp
qed simp

lemma copy_range_imp_rule:
  assumes P: "\<And> i. i < n \<Longrightarrow> <F> P i <\<lambda> r. F * \<up>(r = p i)>"
  shows "<a \<mapsto>\<^sub>a l * F * \<up>(length l = n)> copy_range_imp P n a <\<lambda> _. a \<mapsto>\<^sub>a map p [0..<n] * F>"
proof(rule ht_pure_pre)
  assume l: "length l = n"
  have step: "<a \<mapsto>\<^sub>a l' * \<up>(length l' = n) * F> do { x \<leftarrow> P j; Array.upd j x a; return () }
              <\<lambda> _. a \<mapsto>\<^sub>a list_update l' j (p j) * \<up>(length (list_update l' j (p j)) = n) * F>"
    if "j < n" for j l'
    using that by (sep_auto heap: P[OF that])
  have r: "<a \<mapsto>\<^sub>a l * \<up>(length l = n) * F> copy_range_imp P n a
           <\<lambda> _. a \<mapsto>\<^sub>a foldr (\<lambda> j l. list_update l j (p j)) [0..<n] l *
                 \<up>(length (foldr (\<lambda> j l. list_update l j (p j)) [0..<n] l) = n) * F>"
    unfolding copy_range_imp_def
    by (rule foldr_range_imp_rule[where A = "\<lambda> l _. a \<mapsto>\<^sub>a l * \<up>(length l = n)"], rule step)
  show "<a \<mapsto>\<^sub>a l * F> copy_range_imp P n a <\<lambda> _. a \<mapsto>\<^sub>a map p [0..<n] * F>"
    by (rule ht_cons_pre[OF _ ht_cons_post[OF r]]) (use l in \<open>sep_auto simp: foldr_upd_range\<close>)+
qed

text \<open>Writing the indices below \<open>n\<close> satisfying a predicate, in increasing order, into the
  first cells of an array of length at least \<open>n\<close>; the result is their number.\<close>

definition "collect_range_imp P n Fa = 
  foldl_range_imp (\<lambda> y k. do { b \<leftarrow> P y; 
                              if b then do { Array.upd k y Fa; return (Suc k) } else return k }) 
    0 n 0"

lemma collect_range_imp_rule:
  assumes P: "\<And> y. y < n \<Longrightarrow> <F> P y <\<lambda> r. F * \<up>(r = p y)>"
    and len: "n \<le> length fl"
  shows "<Fa \<mapsto>\<^sub>a fl * F> collect_range_imp P n Fa
         <\<lambda> k. \<exists>\<^sub>A fl'. Fa \<mapsto>\<^sub>a fl' * F * 
               \<up>(length fl' = length fl \<and> k = length (filter p [0..<n]) \<and> 
                 take k fl' = filter p [0..<n])>"
proof-
  let ?A = "\<lambda> j (fk :: nat list \<times> nat) k. Fa \<mapsto>\<^sub>a fst fk * 
                \<up>(k = snd fk \<and> length (fst fk) = length fl \<and> k = length (filter p [0..<j]) \<and> 
                  take k (fst fk) = filter p [0..<j])"
  let ?g = "\<lambda> j (fk :: nat list \<times> nat). 
              if p j then (list_update (fst fk) (snd fk) j, Suc (snd fk)) else fk"
  have step: "<?A j fk k * F> 
                do { b \<leftarrow> P j; if b then do { Array.upd k j Fa; return (Suc k) } else return k }
              <\<lambda> r. ?A (Suc j) (?g j fk) r * F>" if "j < n" for j fk k
  proof-
    have k: "length (filter p [0..<j]) < length fl"
      using length_filter_le[of p "[0..<j]"] that len by simp
    show ?thesis
      using that k by (sep_auto heap: P simp: take_upd_Suc take_Suc_upd)
  qed
  have run: "<?A 0 (fl, 0) 0 * F> collect_range_imp P n Fa 
             <\<lambda> r. ?A n (foldl (\<lambda> a j. ?g j a) (fl, 0) [0..<n]) r * F>"
    unfolding collect_range_imp_def by (rule foldl_range_imp_idx_rule) (rule step, simp_all)
  show ?thesis
    by (rule ht_cons_post[OF ht_cons_pre[OF _ run]]) sep_auto+
qed

declare foldr_range_imp.simps[code] foldl_range_imp.simps[code] find_range_imp.simps[code]

end