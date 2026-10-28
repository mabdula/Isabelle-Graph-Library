theory Array_Folds
  imports Separation_Logic_Imperative_HOL_Partial.Sep_Main
begin

section \<open>Folds over an Array\<close>

text \<open>Left and right folds of a heap function over a prefix of an array, which refine
      @{const foldl} and @{const foldr} over the list stored in the array. In contrast to
      the iterations of @{text Array_Range_Iteration}, the range may be empty. The step of the
      right fold may depend on the position, e.g.\ to bound the size of the accumulator.\<close>

partial_function (heap) array_foldl ::
  "'a::heap array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b Heap) \<Rightarrow> 'b \<Rightarrow> 'b Heap" where
  "array_foldl arr i n fi acc =
     (if i < n then do { x \<leftarrow> Array.nth arr i;
                         acc' \<leftarrow> fi x acc;
                         array_foldl arr (Suc i) n fi acc' }
      else return acc)"

lemma array_foldl_rule:
  assumes "n \<le> length xs"
    and "\<And>acc acci x. x \<in> set xs \<Longrightarrow>
           <acc_assn acc acci * F> fi x acci <\<lambda>r. acc_assn (f acc x) r * F>"
  shows "<arr \<mapsto>\<^sub>a xs * acc_assn acc acci * F> array_foldl arr i n fi acci
         <\<lambda>r. arr \<mapsto>\<^sub>a xs * acc_assn (foldl f acc (drop i (take n xs))) r * F>"
proof(induction "n - i" arbitrary: i acc acci)
  case 0
  thus ?case
    by (subst array_foldl.simps) sep_auto
next
  case (Suc k)
  hence i: "i < n" "i < length xs"
    using assms(1) by auto
  have "drop i (take n xs) = xs ! i # drop (Suc i) (take n xs)"
    using i Cons_nth_drop_Suc[of i "take n xs"] by simp
  thus ?case
    using i Suc(1)[of "Suc i"] Suc(2)
    by (subst array_foldl.simps) (sep_auto heap: assms(2))
qed

corollary array_foldl_all_rule:
  assumes "\<And>acc acci x. x \<in> set xs \<Longrightarrow>
             <acc_assn acc acci * F> fi x acci <\<lambda>r. acc_assn (f acc x) r * F>"
  shows "<arr \<mapsto>\<^sub>a xs * acc_assn acc acci * F> array_foldl arr 0 (length xs) fi acci
         <\<lambda>r. arr \<mapsto>\<^sub>a xs * acc_assn (foldl f acc xs) r * F>"
  using array_foldl_rule[of "length xs" xs acc_assn F fi f arr acc acci 0] assms
  by simp

partial_function (heap) array_foldr ::
  "'a::heap array \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b Heap) \<Rightarrow> 'b \<Rightarrow> 'b Heap" where
  "array_foldr arr i fi acc =
     (if 0 < i then do { x \<leftarrow> Array.nth arr (i - 1);
                         acc' \<leftarrow> fi x acc;
                         array_foldr arr (i - 1) fi acc' }
      else return acc)"

text \<open>The step at position @{term j} receives the fold of the entries after @{term j}.\<close>

lemma array_foldr_rule:
  assumes "n \<le> length xs"
    and "\<And>j acci. j < n \<Longrightarrow>
           <acc_assn (foldr f (drop (Suc j) (take n xs)) acc) acci * F> fi (xs ! j) acci
           <\<lambda>r. acc_assn (f (xs ! j) (foldr f (drop (Suc j) (take n xs)) acc)) r * F>"
  shows "<arr \<mapsto>\<^sub>a xs * acc_assn acc acci * F> array_foldr arr n fi acci
         <\<lambda>r. arr \<mapsto>\<^sub>a xs * acc_assn (foldr f (take n xs) acc) r * F>"
proof-
  have "<arr \<mapsto>\<^sub>a xs * acc_assn (foldr f (drop k (take n xs)) acc) acci * F> array_foldr arr k fi acci
        <\<lambda>r. arr \<mapsto>\<^sub>a xs * acc_assn (foldr f (take n xs) acc) r * F>" if "k \<le> n" for k acci
    using that
  proof(induction k arbitrary: acci)
    case 0
    thus ?case
      by (subst array_foldr.simps) sep_auto
  next
    case (Suc k)
    have k: "k < n" "k < length xs"
      using Suc(2) assms(1) by auto
    have "drop k (take n xs) = xs ! k # drop (Suc k) (take n xs)"
      using k Cons_nth_drop_Suc[of k "take n xs"] by simp
    thus ?case
      using k Suc(1)[of _] Suc(2)
      by (subst array_foldr.simps) (sep_auto heap: assms(2)[OF k(1)])
  qed
  from this[of n acci]
  show ?thesis
    by simp
qed

corollary array_foldr_all_rule:
  assumes "\<And>acc acci x. x \<in> set xs \<Longrightarrow>
             <acc_assn acc acci * F> fi x acci <\<lambda>r. acc_assn (f x acc) r * F>"
  shows "<arr \<mapsto>\<^sub>a xs * acc_assn acc acci * F> array_foldr arr (length xs) fi acci
         <\<lambda>r. arr \<mapsto>\<^sub>a xs * acc_assn (foldr f xs acc) r * F>"
  using array_foldr_rule[of "length xs" xs acc_assn f acc F fi arr acci] assms
  by simp

end
