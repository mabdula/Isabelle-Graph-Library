(*
  Author: Thomas Ammer
*)

theory More_Lists
<<<<<<< HEAD:Data_Structures/More_Lists.thy
  imports Main "HOL-Library.Extended_Real" AI_Provenance.Provenance
    Data_Structures.Fixed_Univ_Map_Specs
    More_Arith
=======
  imports Main "HOL-Library.Extended_Real" "HOL-Eisbach.Eisbach"
>>>>>>> weighted_blossom:Set_Graphs/Directed_Graphs/More_Lists.thy
begin

lemma drop_take_Cons_Cons:
  "\<lbrakk>i + 1 < k; k \<le> length xs\<rbrakk> \<Longrightarrow>
   drop i (take k xs) = xs ! i # xs ! (i + 1) # drop (i + 2) (take k xs)"
  using Cons_nth_drop_Suc[of i "take k xs"] Cons_nth_drop_Suc[of "Suc i" "take k xs"]
  by simp

lemma nth_below: "\<lbrakk>set xs \<subseteq> {..<n}; j < length xs\<rbrakk> \<Longrightarrow> xs ! j < (n::nat)"
  by (simp add: subset_eq)

lemma distinct_length_le: "\<lbrakk>distinct xs; set xs \<subseteq> {..<m}\<rbrakk> \<Longrightarrow> length xs \<le> m"
  using card_mono[of "{..<m}" "set xs"]
  by (simp add: distinct_card)

lemma Max_insert_fold: "Max (insert a (set xs)) = fold max xs (a::'a::linorder)"
  using Max.set_eq_fold[of a xs]
  by simp

text \<open>The maximum weight of a non-empty list.\<close>

definition "list_max f xs = fold max (map f (tl xs)) (f (hd xs))"

lemma list_max:
  fixes f :: "'a \<Rightarrow> 'b :: linorder"
  shows "xs \<noteq> [] \<Longrightarrow> list_max f xs = Max (f ` set xs)"
  by (cases xs) (simp_all add: list_max_def Max.set_eq_fold[symmetric])

lemmas [code] = list_max_def

lemma take_drop_upd:
  "\<lbrakk>a < length ys; length xs = length ys; y = ys ! a\<rbrakk> \<Longrightarrow>
   list_update (take a ys @ drop a xs) a y = take (Suc a) ys @ drop (Suc a) xs"
  by (simp add: list_update_append take_Suc_conv_app_nth Cons_nth_drop_Suc[symmetric])

lemma take_upd_Suc: "k < length l \<Longrightarrow> take (Suc k) (list_update l k x) = take k l @ [x]"
  by (subst take_Suc_conv_app_nth) (simp_all add: list_update_beyond)

lemma take_Suc_upd: "k < length l \<Longrightarrow> list_update (take (Suc k) l) k x = take k l @ [x]"
  using take_upd_Suc[of k l x]
  by (simp add: take_update_swap)

lemma take_drop_upd_insert:
  assumes "p < length g"
  shows "take (Suc p) (g[p := x]) @ M @ drop (Suc p + length M) (g[p := x]) =
         take p g @ (x # M) @ drop (p + length (x # M)) g"
  by (simp only: take_upd_Suc[OF assms]) simp

lemma extract_list:
  assumes "distinct hs" "butlast hs \<noteq> []"
  shows "distinct ((butlast hs)[0 := last hs])"
        "set ((butlast hs)[0 := last hs]) = set hs - {hs ! 0}"
        "length ((butlast hs)[0 := last hs]) = length hs - 1"
        "\<And>j. \<lbrakk>0 < j; j < length hs - 1\<rbrakk> \<Longrightarrow>
          (butlast hs)[0 := last hs] ! j = hs ! j"
proof-
  obtain a ys z where "hs = a # ys @ [z]"
    using assms(2)
    by (cases hs; cases "tl hs" rule: rev_cases; auto split: if_splits)
  thus "distinct ((butlast hs)[0 := last hs])"
      "set ((butlast hs)[0 := last hs]) = set hs - {hs ! 0}"
      "length ((butlast hs)[0 := last hs]) = length hs - 1"
      "\<And>j. \<lbrakk>0 < j; j < length hs - 1\<rbrakk> \<Longrightarrow>
        (butlast hs)[0 := last hs] ! j = hs ! j"
    using assms(1)
    by (auto simp add: nth_Cons' nth_append butlast_append)
qed

lemma perm_step_lists:
  assumes "i < length es" "length xs = length es"
  shows "list_update (take (Suc i) xs) i (vs ! (es ! i)) = take i xs @ [vs ! (es ! i)]"
        "drop i (map ((!) vs) es) = vs ! (es ! i) # drop (Suc i) (map ((!) vs) es)"
        "(map ((!) us) (take i es) @ drop i es) ! i = es ! i"
        "list_update (map ((!) us) (take i es) @ drop i es) i (us ! (es ! i)) =
         map ((!) us) (take (Suc i) es) @ drop (Suc i) es"
  using assms Cons_nth_drop_Suc[of i "map ((!) vs) es", symmetric] Cons_nth_drop_Suc[of i es, symmetric]
  by (simp_all add: take_Suc_conv_app_nth list_update_append nth_append)

lemma Cons_eq_upt_conv: "(x # xs = [i..<j]) = (i < j \<and> x = i \<and> xs = [Suc i..<j])"
  by (subst eq_commute) (auto simp: upt_eq_Cons_conv)

lemma replicate_diff_Suc: "i < n \<Longrightarrow> replicate (n - i) x = x # replicate (n - Suc i) x"
  by (simp add: Suc_diff_Suc flip: replicate_Suc)

text \<open>The even and the odd positions of a list with two leading elements.\<close>

lemma evens_odds_Cons2:
  "{(x # y # zs) ! i | i. i < length (x # y # zs) \<and> even i}
     = insert x {zs ! i | i. i < length zs \<and> even i}"
  "{(x # y # zs) ! i | i. i < length (x # y # zs) \<and> odd i}
     = insert y {zs ! i | i. i < length zs \<and> odd i}"
  by (auto simp: less_Suc_eq_0_disj intro: exI[of _ "Suc (Suc i)" for i])
     (rule exI[of _ 0], simp, rule exI[of _ 1], simp)

lemma nth_set_subset: "{zs ! i | i. i < length zs \<and> P i} \<subseteq> set zs"
  by auto

text \<open>The pairs of a walk of odd length \<open>p\<close> that the augmentation exchanges: \<open>(p ! (2i+1), p
! (2i+2))\<close> for the first and \<open>(p ! (2i+1), p ! (2i))\<close> for the second matroid.\<close>

lemma odd_pairs_fst1:
  "odd (length p) \<Longrightarrow>
     set (map fst [(p ! (2*i+1), p ! (2*i+2)). i <- [0..<(length p - 1) div 2]])
       = {p ! i | i. i < length p \<and> odd i}"
  by (presburger |
      auto intro!: image_eqI[of "_ i" _ "(i - 1) div 2" for i] image_eqI[of "p ! i" fst for i]
      intro: less_mult_imp_div_less)+

lemma odd_pairs_snd1:
  "odd (length p) \<Longrightarrow>
     set (map snd [(p ! (2*i+1), p ! (2*i+2)). i <- [0..<(length p - 1) div 2]]) \<union> {p ! 0}
       = {p ! i | i. i < length p \<and> even i}"
  using not_less_eq_eq
  by (auto intro!: less_mult_imp_div_less diff_less_mono cong[OF refl, of _ _ "\<lambda> i. p ! i"]
                   image_eqI[of "_ i" _ "(i - 1) div 2" for i]
                   image_eqI[of "p ! i" snd
                   "(p ! Suc (2 * ((i-1) div 2)), p ! Suc (Suc (2 * ((i-1) div 2))))" for i])+

lemma odd_pairs_fst2:
  "odd (length p) \<Longrightarrow>
     set (map fst [(p ! (2*i+1), p ! (2*i)). i <- [0..<(length p - 1) div 2]])
       = {p ! i | i. i < length p \<and> odd i}"
  by (presburger |
      auto intro!: image_eqI[of "_ i" _ "(i - 1) div 2" for i] image_eqI[of "p ! i" fst for i]
      intro: less_mult_imp_div_less)+

lemma odd_pairs_snd2:
  "odd (length p) \<Longrightarrow>
     set (map snd [(p ! (2*i+1), p ! (2*i)). i <- [0..<(length p - 1) div 2]]) \<union> {p ! (length p - 1)}
       = {p ! i | i. i < length p \<and> even i}"
  by (cases p)
     (auto intro!: less_mult_imp_div_less diff_less_mono cong[OF refl, of _ _ "\<lambda> i. p ! i"]
                   image_eqI[of "_ i" _ "(i) div 2" for i]
                   image_eqI[of "p ! i" snd "(p ! Suc (2 * ((i) div 2)), p ! (2 * ((i) div 2)))" for i]
        simp: less_Suc_eq)

text \<open>On a walk without repeated vertices the exchanged pairs are injective in both components, and no
even-position or start vertex is removed.\<close>

lemma odd_pairs_distinct1:
  "distinct p \<Longrightarrow> distinct (map fst [(p ! (2*i+1), p ! (2*i+2)). i <- [0..<(length p - 1) div 2]])"
  "distinct p \<Longrightarrow> distinct (map snd [(p ! (2*i+1), p ! (2*i+2)). i <- [0..<(length p - 1) div 2]])"
  by (auto simp: distinct_conv_nth nth_eq_iff_index_eq)

lemma odd_pairs_distinct2:
  "distinct p \<Longrightarrow> distinct (map fst [(p ! (2*i+1), p ! (2*i)). i <- [0..<(length p - 1) div 2]])"
  "distinct p \<Longrightarrow> distinct (map snd [(p ! (2*i+1), p ! (2*i)). i <- [0..<(length p - 1) div 2]])"
  by (auto simp: distinct_conv_nth nth_eq_iff_index_eq)

lemma odd_pairs_snd_notin1:
  "\<lbrakk>distinct p; odd (length p); i < length p; odd i \<or> i = 0\<rbrakk> \<Longrightarrow>
     (a, p ! i) \<notin> set [(p ! (2*i+1), p ! (2*i+2)). i <- [0..<(length p - 1) div 2]]"
  by (auto simp: nth_eq_iff_index_eq)

lemma odd_pairs_snd_notin2:
  "\<lbrakk>distinct p; odd (length p); i < length p; odd i \<or> i = length p - 1\<rbrakk> \<Longrightarrow>
     (a, p ! i) \<notin> set [(p ! (2*i+1), p ! (2*i)). i <- [0..<(length p - 1) div 2]]"
  by (auto simp: nth_eq_iff_index_eq)

lemma concat_if_dist:
  "distinct xs \<Longrightarrow> concat (map (\<lambda> x. if x = u then L x else []) xs) = (if u \<in> set xs then L
    u else [])"
  by (induction xs) auto

lemma foldr_cons_map: "foldr (\<lambda> y acc. f y # acc) xs a = map f xs @ a"
  by (induction xs) simp_all

lemma foldr_cons_filter:
  "foldr (\<lambda> y acc. if p y then f y # acc else acc) xs a = map f (filter p xs) @ a"
  by (induction xs) simp_all

lemma foldr_pairs:
  "foldr (\<lambda> x acc. if p x then foldr (\<lambda> y acc. if q x y then (x, y) # acc else acc) ys acc
                   else acc) xs a =
   concat (map (\<lambda> x. map (Pair x) (filter (q x) ys)) (filter p xs)) @ a"
  by (induction xs) (simp_all add: foldr_cons_filter)

lemma foldl_filter_if:
  "foldl (\<lambda> a x. if p x then f a x else a) a xs = foldl f a (filter p xs)"
  by (induction xs arbitrary: a) simp_all

lemma zip_foldl_map:
     "ys = map y xs \<Longrightarrow> foldl (\<lambda>acc a. case a of (x, y) \<Rightarrow> f x y acc) acc (zip xs ys)
      = foldl (\<lambda>acc x. f x (y x) acc) acc xs"
  by(induction xs arbitrary: acc ys) auto

lemma foldl_fixed: "(\<And>x. f s x = s) \<Longrightarrow> foldl f s xs = s"
  by (induction xs) simp_all

lemma foldl_True: "foldl (\<lambda> a x. True) b xs = (b \<or> xs \<noteq> [])"
  by (induction xs arbitrary: b) simp_all

lemma nth_in_take: "\<lbrakk>j < k; k \<le> length ps\<rbrakk> \<Longrightarrow> ps ! j \<in> set (take k ps)"
  using nth_mem[of j "take k ps"]
  by simp

lemma rev_take_Suc_Suc:
  "Suc (Suc j) \<le> length ps \<Longrightarrow> rev (take (Suc (Suc j)) ps) = ps ! Suc j # ps ! j # rev (take j ps)"
  by (simp add: take_Suc_conv_app_nth)

lemma map_bcount_upd:
  assumes "k < nb" "\<And> b. b < nb \<Longrightarrow> g b = (if b = k then v else f b)"
  shows "(map f [0..<nb])[k := v] = map g [0..<nb]"
  by (rule nth_equalityI; insert assms; auto simp: nth_list_update)

lemma map_fun_update:
  "i < n \<Longrightarrow> (map f [0..<n])[i := x] = map (f(i := x)) [0..<n]"
  by (rule nth_equalityI) (auto simp: nth_list_update)

lemma map_mem_update:
  "i < n \<Longrightarrow>
   (map (\<lambda> j. j \<in> X) [0..<n])[i := b] = map (\<lambda> j. j \<in> (if b then insert i X else X - {i})) [0..<n]"
  by (rule nth_equalityI) (auto simp: nth_list_update)

lemma sum_list_map_zero:
  "(\<And> u. \<lbrakk>v \<le> u; u < w\<rbrakk> \<Longrightarrow> L ! u = 0)
     \<Longrightarrow> sum_list (map ((!) L) [v..<w]) = (0 :: 'a :: comm_monoid_add)"
  by(induction w) auto

lemma bal_zero_iff:
  "((\<forall> u. Suc 0 \<le> u \<and> u < nn \<longrightarrow> bl ! u \<le> 0)
    \<and> (\<forall> u. Suc 0 \<le> u \<and> u < nn \<longrightarrow> 0 \<le> bl ! u)
    \<and> sum_list (map ((!) (list_update bl 0 0)) [Suc 0..<nn]) = (0 :: int))
   = (\<forall> v. Suc 0 \<le> v \<and> v < nn \<longrightarrow> bl ! v = 0)"
  by(auto intro: order_antisym sum_list_map_zero)

lemma takeWhile_holds: "x \<in> set (takeWhile P xs) \<Longrightarrow> P x"
  by (induction xs) (auto split: if_splits)

lemma set_takeWhile_closed:
  assumes "\<And>us w ws u. \<lbrakk>xs = us @ w # ws; P w; u \<in> set us\<rbrakk> \<Longrightarrow> P u"
  shows "set (takeWhile P xs) = {x \<in> set xs. P x}"
proof(intro equalityI subsetI)
  fix x
  assume "x \<in> {x \<in> set xs. P x}"
  then obtain us ws where "xs = us @ x # ws" "P x"
    by (auto dest: split_list)
  thus "x \<in> set (takeWhile P xs)"
    using assms[of us x ws]
    by simp
qed (auto dest: set_takeWhileD)

lemma in_dropWhile_neq: "x \<in> set xs \<Longrightarrow> x \<in> set (dropWhile (\<lambda>y. y \<noteq> x) xs)"
  by (induction xs) auto

lemma notin_takeWhile_dropWhile: "\<lbrakk>x \<in> set xs; x \<notin> set (takeWhile P xs)\<rbrakk> \<Longrightarrow> x
  \<in> set (dropWhile P xs)"
  by (induction xs) auto

lemma takeWhile_block_aux:
  "\<lbrakk>distinct xs; xs = pre @ rest; pre \<noteq> []; last pre = L\<rbrakk> \<Longrightarrow> takeWhile
    (\<lambda>x. x \<noteq> L) xs @ [L] = pre"
  by (induction pre arbitrary: xs) (auto split: if_splits)

lemma prefix_mono_set:
  assumes "distinct ys" "as @ as' = ys" "bs @ bs' = ys" "set as \<subseteq> set bs"
  shows "\<exists>cs. bs = as @ cs"
proof(cases "length as \<le> length bs")
  case True
  thus ?thesis
    using arg_cong[OF trans[OF assms(2) assms(3)[symmetric]], of "take (length as)"]
          append_take_drop_id[of "length as" bs]
    by (auto intro!: exI[of _ "drop (length as) bs"])
next
  case False
  then obtain x d where "as = bs @ x # d"
    using arg_cong[OF trans[OF assms(2) assms(3)[symmetric]], of "take (length bs)"]
          append_take_drop_id[of "length bs" as]
    by (cases "drop (length bs) as") auto
  thus ?thesis
    using assms(1,2,4)
    by auto
qed

lemma fold_upd_commute:
  "x \<notin> g ` set xs \<Longrightarrow>
     (fold (\<lambda>a T. T(g a := h a)) xs Y)(x := v) = fold (\<lambda>a T. T(g a := h a)) xs (Y(x := v))"
  by (induction xs arbitrary: Y) (auto simp: fun_upd_twist)

lemma fold_upd_other:
  "z \<notin> (g ` set xs) \<Longrightarrow> (fold (\<lambda>a T. T(g a := h a)) xs Y) z = Y z"
  by (induction xs arbitrary: Y) auto

lemma length_foldl_upd [simp]: "length (foldl (\<lambda>W j. list_update W (g j) (f j)) W xs) = length W"
  by (induction xs arbitrary: W) auto

lemma foldl_upd_nth_miss:
  "x \<notin> g ` set xs \<Longrightarrow> foldl (\<lambda>W j. list_update W (g j) (f j)) W xs ! x = W ! x"
  by (induction xs arbitrary: W) auto

text \<open>Updating a list at the positions @{term "g j"} for the elements @{term j} of a list, with
      @{term g} injective.\<close>

lemma foldl_upd_nth_hit:
  assumes "inj_on g (set xs)" "i \<in> set xs" "\<And>j. j \<in> set xs \<Longrightarrow> g j < length W"
  shows "foldl (\<lambda>W j. list_update W (g j) (f j)) W xs ! g i = f i"
  using assms
proof(induction xs arbitrary: W)
  case (Cons a xs)
  thus ?case
    by (cases "i \<in> set xs") (auto simp: foldl_upd_nth_miss)+
qed simp

lemma foldr_upd_range:
  "k \<le> length l \<Longrightarrow> foldr (\<lambda> j l. list_update l j (p j)) [0..<k] l = map p [0..<k] @ drop k l"
  by (induction k arbitrary: l) (simp_all add: Cons_nth_drop_Suc[symmetric] drop_update_swap)

lemma foldl_upd_eval:
  "(foldl (\<lambda>R u. case f u of None \<Rightarrow> R | Some w \<Rightarrow> R(w \<mapsto> u)) R0 ds) x =
   (if (\<exists>u\<in>set ds. f u = Some x) then Some (last (filter (\<lambda>u. f u = Some x) ds)) else R0 x)"
  by (induction ds rule: rev_induct) (auto split: option.splits)

lemma filter_eq_self_single: "\<lbrakk>distinct xs; u \<in> set xs\<rbrakk> \<Longrightarrow> filter (\<lambda>x. x = u)
  xs = [u]"
  by (induction xs) (auto simp: filter_empty_conv)

lemma find_filter: "find p (filter q xs) = find (\<lambda> x. q x \<and> p x) xs"
  by (induction xs) simp_all

lemma find_SomeD: "find p xs = Some x \<Longrightarrow> p x \<and> x \<in> set xs"
  by (induction xs) (simp_all split: if_splits)

lemma list_ex_filter: "list_ex p (filter q xs) = list_ex (\<lambda> x. q x \<and> p x) xs"
  by (induction xs) simp_all

lemma list_ex_find: "list_ex p xs = (find p xs \<noteq> None)"
  by (induction xs) simp_all

lemma take_nth_eq: "\<lbrakk>take n xs = ys; k < n\<rbrakk> \<Longrightarrow> xs ! k = ys ! k"
  by (clarsimp simp: nth_take)

lemma concat_eqI:
  assumes "length xs = sum_list (map length Ls)"
      and "\<And>k i. \<lbrakk>k < length Ls; i < length (Ls ! k)\<rbrakk>
                \<Longrightarrow> xs ! (sum_list (map length (take k Ls)) + i) = Ls ! k ! i"
  shows "xs = concat Ls"
  using assms
proof(induction Ls arbitrary: xs)
  case (Cons L Ls)
  have "take (length L) xs = L"
    using Cons.prems(1) Cons.prems(2)[of 0]
    by (intro nth_equalityI) auto
  moreover have "drop (length L) xs = concat Ls"
    using Cons.prems Cons.prems(2)[of "Suc k" for k]
    by (intro Cons.IH) (auto simp: add.assoc)
  ultimately show ?case
    using append_take_drop_id[of "length L" xs]
    by simp
qed simp

lemma map_nth_upt_take_drop:
  "b \<le> length xs \<Longrightarrow> map ((!) xs) [a..<b] = take (b - a) (drop a xs)"
  by (rule nth_equalityI) auto

lemma nths_intervall_as_drop_and_take:
  "nths list {start..ed} = drop (start) (take (Suc ed) list)"
  apply(induction list arbitrary: start ed)
  subgoal
    by simp
  subgoal for a list start ed
    apply(cases start)
     apply(all \<open>cases ed\<close>)
       apply (auto simp add: nths_Cons)
    subgoal
      by(auto simp add: intervall_rw2)
    by(auto simp add: nths_def)
  done

lemma nths_intervall_strict_as_drop_and_take:
  "nths list {start..<ed} = drop (start) (take ed list)"
  by(cases ed)
    (simp_all add: atLeastLessThanSuc_atLeastAtMost nths_intervall_as_drop_and_take)

lemma nths_intervall_split_off_first:
  assumes "start \<le> end" "end < length list"
  shows "(nths list {start..end}) =  (list ! start # nths list {Suc start..end})"
  unfolding nths_intervall_as_drop_and_take
  apply(subst Cons_nth_drop_Suc[of start, symmetric])
  using assms(1,2)
  by (auto intro!: arg_cong2[where f = Cons] simp add: assms(1) le_imp_less_Suc)

lemma nths_intervall_strict_split_off_first:
  assumes "start < end" "end < length list"
  shows "(nths list {start..<end}) =  (list ! start # nths list {Suc start..<end})"
  unfolding nths_intervall_strict_as_drop_and_take
  apply(subst Cons_nth_drop_Suc[of start, symmetric])
  using assms(1,2)
  by (auto intro!: arg_cong2[where f = Cons] simp add: assms(1) le_imp_less_Suc)

lemma nths_strict_split_off_first_le:
  assumes "start < end" "end \<le> length list"
  shows "nths list {start..<end} = list ! start # nths list {Suc start..<end}"
  using assms Cons_nth_drop_Suc[of start "take end list"]
  by (simp add: nths_intervall_strict_as_drop_and_take)

lemma nth_shifted_by_lower_bound_of_nths_intervall:
  assumes "u < length xs" "i \<ge> l" "i \<le> u"
  shows "nths xs {l..u} ! (i -l) = xs ! i"
  unfolding nths_intervall_as_drop_and_take
  using assms
  by (subst nth_drop)(auto simp add: le_imp_less_Suc)

lemma nth_of_nths_intervall_shifted_by_lower_bound:
  assumes "u < length xs" "l + i \<le> u"
  shows "nths xs {l..u} ! (i) = xs ! (i + l)"
  unfolding nths_intervall_as_drop_and_take
  using assms
  by (subst nth_drop)(auto simp add: le_imp_less_Suc algebra_simps)

lemma length_nths_of_intervall:
  assumes  "u < length xs"
  shows "length (nths xs {l..u})  = (u + 1) - l"
  using assms
  by(auto simp add: nths_intervall_as_drop_and_take)

lemma foldl_upt_nth: "foldl (\<lambda> a j. g a (xs ! j)) a [0..<length xs] = foldl g a xs"
  by (subst (2) map_nth[symmetric]) (simp add: foldl_map)

lemma sorted_wrt_rank_distinct: "sorted_wrt (\<lambda> a b. (r::nat \<Rightarrow> nat) b < r a) p \<Longrightarrow> distinct p"
  by (induction p) auto

lemma foldl_insert_set: "foldl (\<lambda> A x. Set.insert x A) B ys = set ys \<union> B"
  by (induction ys arbitrary: B) auto

lemma sum_length_filter_key:
  fixes f :: "'a \<Rightarrow> nat"
  shows "(\<And>x. x \<in> set xs \<Longrightarrow> f x < n)
         \<Longrightarrow> (\<Sum>k\<in>{0..<n}. length (filter (\<lambda>x. f x = k) xs)) = length xs"
proof(induction xs)
  case (Cons x xs)
  have "(\<Sum>k\<in>{0..<n}. length (filter (\<lambda>y. f y = k) (x # xs)))
        = (\<Sum>k\<in>{0..<n}. length (filter (\<lambda>y. f y = k) xs) + (if f x = k then 1 else 0))"
    by (auto intro: sum.cong)
  thus ?case
    using Cons
    by (simp add: sum.distrib)
qed simp

lemma foldr_max_some:
  "xs \<noteq> [] \<Longrightarrow>
   foldr (\<lambda> x acc. Some (case acc of None \<Rightarrow> f x | Some m \<Rightarrow> max m (f x))) xs None
     = Some (Max (f ` set xs))"
proof(induction xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  show ?case
  proof(cases "xs = []")
    case True
    then show ?thesis
      by simp
  next
    case False
    then show ?thesis
      using Cons.IH[OF False]
      by (simp add: Max_insert image_insert max.commute)
  qed
qed

provenance human

lemma list_2_preds_aux:
  "\<lbrakk>x' \<in> set xs; P1 x'; \<And>xs1 x xs2. \<lbrakk>xs = xs1 @ [x] @ xs2; P1 x\<rbrakk> \<Longrightarrow>
      \<exists>ys1 y ys2. x # xs2 = ys1 @ [y] @ ys2 \<and> P2 y\<rbrakk> \<Longrightarrow> 
     \<exists> xs1 x xs2. xs = xs1 @ [x] @ xs2 \<and> P2 x \<and> (\<forall>y\<in>set xs2. \<not> P1 y)"
proof(goal_cases)
  case assms: 1
  define property 
       where "property xs =
                (\<forall>xs2 xs1 x. (xs = xs1 @ [x] @ xs2 \<and> P1 x) \<longrightarrow>
                   (\<exists>ys1 y ys2. x#xs2 = ys1 @ [y] @ ys2 \<and> P2 y))"
       for xs
  have propE: "\<lbrakk>property xs;
               (\<And>xs1 x xs2. \<lbrakk>xs = xs1 @ [x] @ xs2; P1 x\<rbrakk> \<Longrightarrow>
                  \<exists>ys1 y ys2. x#xs2 = ys1 @ [y] @ ys2 \<and> P2 y) \<Longrightarrow> P\<rbrakk>
              \<Longrightarrow> P" for xs P
    by(auto simp add: property_def)
  have property_append: "property (xs @ ys) \<Longrightarrow> property ys" for xs ys
    by(auto simp: property_def)
  have "property xs"
    using assms(3)
    by (force simp: property_def)
  thus  ?thesis
    using assms(1,2)
  proof(induction xs arbitrary: x')
    case Nil
    then show ?case 
      by auto
  next
    case (Cons a xs)
    hence "property xs" 
      by(auto intro: property_append[where xs = "[a]"])
    show ?case
    proof(cases "x' = a")
      case x_eq_a: True
      then obtain ys1 y ys2 where "x'#xs = ys1 @ [y] @ ys2" "P2 y"
        using \<open>property (a # xs)\<close> \<open>P1 x'\<close>
        apply(elim propE)
        by (auto 10 10)
      show ?thesis
      proof(cases "ys1 = []")
        case ys1_empty: True
        hence "xs = ys2"
          using \<open>x'#xs = ys1 @ [y] @ ys2\<close>
          by auto
        then show ?thesis
        proof(cases "\<exists>x\<in>set ys2. P1 x")
          case x_in_ys2: True
          then obtain x where "x \<in> set ys2" "P1 x"
            by auto
          hence "\<exists>xs1 x xs2. xs = xs1 @ [x] @ xs2 \<and> P2 x \<and> (\<forall>y\<in>set xs2. \<not> P1 y)"
            using \<open>property xs\<close> \<open>xs = ys2\<close> \<open>P2 y\<close>
            apply(intro Cons(1))
            by auto
          then obtain xs1 x xs2 where "(a # xs) = (a #xs1) @ [x] @ xs2 \<and> P2 x \<and> (\<forall>y\<in>set xs2. \<not> P1 y)"
            by auto
          then show ?thesis
            by metis
        next
          case x_notin_ys2: False
          hence "a # xs = a#ys2 \<and> P2 y \<and> (\<forall>y\<in>set ys2. \<not> P1 y)"
            using \<open>xs = ys2\<close> \<open>P2 y\<close>
            by auto
          then show ?thesis
            using \<open>x' # xs = ys1 @ [y] @ ys2\<close> x_eq_a
            by blast
        qed
      next
        case ys2_nempty: False
        then obtain ys1' where "xs = ys1' @ [y] @ ys2"
          using \<open>x'#xs = ys1 @ [y] @ ys2\<close>
          by (auto simp: neq_Nil_conv)
        show ?thesis
        proof(cases "\<exists>x\<in>set ys2. P1 x")
          case x_in_ys2: True
          then obtain x where "x \<in> set ys2" "P1 x"
            by auto
          hence "\<exists>xs1 x xs2. xs = xs1 @ [x] @ xs2 \<and> P2 x \<and> (\<forall>y\<in>set xs2. \<not> P1 y)"
            using \<open>property xs\<close> \<open>xs = ys1' @ [y] @ ys2\<close> \<open>P2 y\<close>
            apply(intro Cons(1))
            by auto
          then obtain xs1 x xs2 where "(a # xs) = (a #xs1) @ [x] @ xs2 \<and> P2 x \<and> (\<forall>y\<in>set xs2. \<not> P1 y)"
            by auto
          then show ?thesis
            by metis
        next
          case x_notin_ys2: False
          hence "a # xs = (a# ys1') @ [y] @ ys2 \<and> P2 y \<and> (\<forall>y\<in>set ys2. \<not> P1 y)"
            using \<open>xs = ys1' @ [y] @ ys2\<close> \<open>P2 y\<close>
            by auto
          then show ?thesis
            by metis
        qed
      qed
    next
      case x_neq_a: False
      hence "x' \<in> set xs"
        using Cons
        by auto
      then obtain xs1 x xs2 where "xs = xs1 @ [x] @ xs2" "P2 x" "(\<forall>y\<in>set xs2. \<not> P1 y)"
        using Cons \<open>property xs\<close>
        by blast
      hence "a # xs = (a # xs1) @ [x] @ xs2 \<and> P2 x \<and> (\<forall>y\<in>set xs2. \<not> P1 y)"
        by auto
      thus ?thesis
        by metis
    qed
  qed
qed

lemma list_2_preds:
  "\<lbrakk> x\<in>set xs; P1 x; 
     \<And>xs1 x xs2. \<lbrakk>xs = xs1 @ [x] @ xs2; P1 x\<rbrakk> \<Longrightarrow> \<exists>ys1 y ys2. x#xs2 = ys1 @ [y] @ ys2 \<and> P2 y\<rbrakk> 
   \<Longrightarrow>  \<exists> xs1 x xs2. xs = xs1 @ [x] @ xs2 \<and> P2 x \<and> (\<forall>y\<in>set xs2. \<not> P1 y \<and> \<not> P2 y)"
proof(goal_cases)
  case assms: 1
  hence "\<exists>xs1 x xs2. xs = xs1 @ [x] @ xs2 \<and> P2 x \<and> (\<forall>y\<in>set xs2. \<not> P1 y)"
    by (fastforce intro!: list_2_preds_aux)
  then obtain xs1 x xs2 where "xs = xs1 @ [x] @ xs2" "P2 x" "(\<forall>y\<in>set xs2. \<not> P1 y)"
    by auto
  hence "\<exists>ys1 y ys2. x # xs2 = ys1 @ [y] @ ys2 \<and> P2 y \<and> (\<forall>z\<in>set ys2. \<not> P2 z)"
    by (auto intro!: split_list_last_prop)
  then obtain ys1 y ys2 where "x # xs2 = ys1 @ [y] @ ys2" "P2 y" "(\<forall>z\<in>set ys2. \<not> P2 z)"
    by auto
  hence "(\<forall>z\<in>set ys2. \<not>P1 z \<and> \<not> P2 z)"
    using \<open>(\<forall>y\<in>set xs2. \<not> P1 y)\<close> \<open>P2 x\<close>
    by (metis Un_iff insert_iff list.simps(15) set_append)
  moreover have "xs = (xs1 @ ys1) @ [y] @ ys2"
    using \<open>xs = xs1 @ [x] @ xs2\<close> \<open>x # xs2 = ys1 @ [y] @ ys2\<close>
    by auto
  ultimately show ?case
    using \<open>P2 y\<close>
    by fastforce
qed

lemma list_inter_mem_iff: "set xs \<inter> s \<noteq> {} \<longleftrightarrow> (\<exists>xs1 x xs2. xs = xs1 @ [x] @ xs2 \<and> x \<in> s)"
  by (metis append.left_neutral append_Cons disjoint_iff in_set_conv_decomp)

lemma list_P_switch: 
  "\<lbrakk>x \<in> set xs; P x; y \<in> set xs; \<not> P y\<rbrakk>
   \<Longrightarrow> \<exists> p1 p2 x' y'. xs =p1@[x',y']@p2 \<and> ((P x' \<and> \<not> P y') \<or> (P y' \<and> \<not> P x'))"
proof(induction xs arbitrary: x y)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  note IH = this
  then show ?case 
  proof(cases xs)
    case Nil
    then show ?thesis 
      using Cons by simp
  next
    case (Cons b ys)
    then show ?thesis 
    proof(cases "((P a \<and> \<not> P b) \<or> (P b \<and> \<not> P a))")
      case True
      then show ?thesis 
        using Cons True by(auto intro: exI[of "\<lambda> p1. \<exists>p2 x' y'.  _ y' x' p2 p1" Nil] exI[of _ ys])
    next
      case False
      hence alt:"(P a \<and> P b) \<or> (\<not> P a \<and> \<not> P b)" by auto
      have "\<exists>p1 p2 x' y'. xs = p1 @ [x', y'] @ p2 \<and> (P x' \<and> \<not> P y' \<or> P y' \<and> \<not> P x')"   
        using IH Cons by (cases rule: disjE[OF alt]) force+
      then obtain p1 x' y' p2 where "xs = p1 @ [x', y'] @ p2 \<and> (P x' \<and> \<not> P y' \<or> P y' \<and> \<not> P x')"
        by auto
      then show ?thesis
        by(auto intro!: exI[of "\<lambda> p1. \<exists> p2 x' y'. _ p2 x' y' p1" "a#p1"])
    qed
  qed
qed

lemma sum_list_map_filter_split: 
"sum_list (map (f::'s\<Rightarrow> real) xs) = sum_list (map f (filter P xs)) +
 sum_list (map f (filter (\<lambda> x. \<not> P x) xs))"
  by(induction xs)(auto simp add: algebra_simps)

lemma takeWhile_everything: "(\<And> x. x \<in> set xs \<Longrightarrow> P x) \<Longrightarrow> takeWhile P xs = xs"
  by(induction xs) auto

lemma dropWhile_nothing: "(\<And> x. x \<in> set xs \<Longrightarrow> \<not> P x) \<Longrightarrow> dropWhile P xs = xs"
  by(induction xs) auto

lemma foldr_plus_add_right:
  "(c::real)+ foldr (\<lambda>e. (+) (f e)) xs b = foldr (\<lambda>e. (+) (f e)) (xs) (c + b)"
  by(induction xs arbitrary: c b)
  (auto simp add: algebra_simps)

lemma bulast_subset: "set (butlast xs) \<subseteq> set xs" for xs 
  using in_set_butlastD by fastforce

lemma singleton_hd_last: "\<lbrakk>q \<noteq> []; tl q = []\<rbrakk> \<Longrightarrow> hd q = last q"
  by (cases q) auto

lemma hd_last_same: "length xs = 1 \<Longrightarrow> hd xs = last xs" for xs 
  using singleton_hd_last[of xs] 
  by(cases xs) auto
       
lemma last_simp : "last (a#b#cs) = last (b#cs)" by simp

lemma list_triple_split_mid_distinct:
  "\<lbrakk>length xs = n; \<not> distinct xs\<rbrakk>
   \<Longrightarrow> (\<exists> as bs cs x. xs = as@[x]@bs@[x]@cs \<and> distinct bs \<and> x \<notin> set bs)"
proof(induction arbitrary: xs rule: less_induct)
  case (less n)  
  then show ?case 
  proof(cases xs)
    case Nil
    then show ?thesis using less by auto
  next
    case (Cons x ys)
    then show ?thesis 
    proof(cases "x \<in> set ys")
      case True
      obtain gs fs where gf_def: "ys = gs@[x]@fs \<and> x \<notin> set gs" 
        using True  in_set_conv_decomp_first[of x ys] by auto
      then show ?thesis 
      proof(cases "distinct gs")
        case True
        hence "xs = []@[x]@gs@[x]@fs \<and> distinct gs"
          using  \<open>ys = gs @ [x] @ fs \<and> x \<notin> set gs\<close> local.Cons by auto
        then show ?thesis 
          using gf_def by blast
      next
        case False
        have "length gs < n" using less(2) Cons  gf_def by auto
        then obtain as bs cs s where "gs = as@[s]@bs@[s]@cs \<and> distinct bs \<and> s \<notin> set bs"
          using less(1)[of "length gs" gs] False by auto
        hence "xs = []@[x]@as@[s]@bs@[s]@cs@[x]@fs \<and> distinct bs \<and> s \<notin> set bs"
          using local.Cons  gf_def  by force
        then show ?thesis  
          by (metis append.assoc)
      qed
    next
      case False 
      hence "length ys < n "  "length ys = length ys \<and> \<not> distinct ys "
        using less.prems local.Cons False  by auto
      then obtain as bs cs s where "ys = as @ [s] @ bs @ [s] @ cs \<and> distinct bs \<and> s \<notin> set bs"
        using less(1)[of "length ys" ys] by auto
      then show ?thesis using Cons 
        by (metis append_Cons)
    qed
  qed
qed

lemma double_occur_non_dist: 
  "\<lbrakk>set (xs) \<subseteq> X; card X < length xs; finite X; xs \<noteq> []\<rbrakk> \<Longrightarrow> \<not> distinct xs"
  by(induction "card X" arbitrary: X xs, auto)
    (metis card_mono distinct_card linorder_not_less)

lemma subset_big_union_diff:
assumes "set C = (set D) - A " "A = set D - set C" "D \<in> CCC" "C \<notin> CCC" "C \<noteq> D"
        "(\<And> B E. \<lbrakk>B \<in> CCC; E \<in> CCC; B \<noteq> E\<rbrakk> \<Longrightarrow> set E \<inter> set B = {})"
  shows "(\<Union> {set B| B. B \<in> CCC}) - A = \<Union> {set B| B. B \<in> ((CCC - {D}) \<union> {C})}"
proof
  show "\<Union> {set B |B. B \<in> CCC} - A \<subseteq> \<Union> {set B |B. B \<in> CCC - {D} \<union> {C}}"
  proof
    fix x 
    assume "x \<in> \<Union> {set B |B. B \<in> CCC} - A"
    then obtain E where "x \<in> set E \<and> E \<in> CCC" by auto
    then show " x \<in> \<Union> {set B |B. B \<in> CCC - {D} \<union> {C}}"
      using \<open>x \<in> \<Union> {set B |B. B \<in> CCC} - A\<close> assms(1) by auto
  qed
  show "\<Union> {set B |B. B \<in> CCC - {D} \<union> {C}} \<subseteq> \<Union> {set B |B. B \<in> CCC} - A" 
  proof
    fix x
    assume " x \<in> \<Union> {set B |B. B \<in> CCC - {D} \<union> {C}}"
    then obtain E where E_def: "x \<in> set E \<and> E \<in> CCC - {D} \<union> {C}" by auto
    have "\<lbrakk>x \<in> set E; x \<in> A\<rbrakk> \<Longrightarrow> set E \<inter> set D \<noteq> {}"
    using assms
    by blast 
    from E_def show "x \<in> \<Union> {set B |B. B \<in> CCC} - A"
      using \<open>x \<in> set E \<and> E \<in> CCC - {D} \<union> {C}\<close> assms(1,3,6)
            \<open>x \<in> set E \<Longrightarrow> x \<in> A \<Longrightarrow> set E \<inter> set D \<noteq> {}\<close> 
      by (cases "E = C")force+
  qed
qed

lemma bing_union_split:
  assumes "set A = set BB \<union> set C"
  shows   "(\<Union> {set C'|C'. C' \<in> CCC \<union>{A}}) = (\<Union> {set C'|C'. C' \<in> CCC \<union>{BB, C}})"
proof
  show "\<Union> {set C' |C'. C' \<in> CCC \<union> {A}} \<subseteq> \<Union> {set C' |C'. C' \<in> CCC \<union> {BB, C}}"
  proof
    fix x
    assume "x \<in> \<Union> {set C' |C'. C' \<in> CCC \<union> {A}}"
    then obtain E where "E \<in> CCC  \<union> {A} \<and> x \<in> set E" by auto
    then show " x \<in> \<Union> {set C' |C'. C' \<in> CCC \<union> {BB, C}}"
    proof(cases "E = A")
      case True
      hence "x \<in> set BB \<or> x \<in> set C" 
        using \<open>E \<in> CCC \<union> {A} \<and> x \<in> set E\<close> assms by auto
      then show ?thesis by(cases "x \<in> set BB", auto)
    next
      case False
      hence "E \<in> CCC"
        using \<open>E \<in> CCC \<union> {A} \<and> x \<in> set E\<close> by fastforce
      then show ?thesis 
        using \<open>E \<in> CCC \<union> {A} \<and> x \<in> set E\<close> by blast
    qed
  qed
  show "\<Union> {set C' |C'. C' \<in> CCC \<union> {BB, C}} \<subseteq> \<Union> {set C' |C'. C' \<in> CCC \<union> {A}}"
  proof
    fix x
    assume " x \<in> \<Union> {set C' |C'. C' \<in> CCC \<union> {BB, C}}"
    then obtain E where "E \<in> CCC  \<union> {BB, C} \<and> x \<in> set E" by auto
    then show " x \<in> \<Union> {set C' |C'. C' \<in> CCC \<union> {A}}"
    proof(cases "E = BB \<or> E = C")
      case True
      then show ?thesis 
        using \<open>E \<in> CCC \<union> {BB, C} \<and> x \<in> set E\<close> assms by fastforce
    next
      case False
      then show ?thesis 
        using \<open>E \<in> CCC \<union> {BB, C} \<and> x \<in> set E\<close> by blast
    qed
  qed
qed

lemma distinct_hd: "distinct (x#xs) \<Longrightarrow> distinct xs" 
  by auto

lemma distinct_last: "distinct (xs@[x]) \<Longrightarrow> distinct xs" 
  by force

lemma distinct_split1: "distinct (xs@ys) \<Longrightarrow> distinct xs "  
  by auto

lemma distinct_split2: "distinct (xs@ys) \<Longrightarrow> distinct ys "   
  by auto

lemma distinct_inter: "distinct (xs@ys@zs) \<Longrightarrow> distinct (xs@zs)"
  by auto

lemma distinct_swap: "distinct (xs@ys@zs) \<Longrightarrow> distinct (xs@zs@ys)"
  by auto

lemma disjoint_lists_sublists:
  assumes "\<And> X Y. \<lbrakk>X \<in> XX; Y \<in> XX; X \<noteq> Y\<rbrakk> \<Longrightarrow> set X \<inter> set Y = {}"
          "A \<in> XX"
          "setA \<supseteq> set E \<union> set G"
          "setA = set A"
          "set E \<inter> set G = {}"
          "distinct A"
    shows "\<And> X Y. \<lbrakk>X \<in> XX-{A} \<union>{E,G}; Y \<in> XX-{A} \<union>{E,G}; X \<noteq> Y\<rbrakk> \<Longrightarrow> set X \<inter> set Y = {}"
proof-
  fix X Y
  assume "X \<in> XX - {A} \<union> {E, G} " " Y \<in> XX - {A} \<union> {E, G} " "X \<noteq> Y "
  then show "set X \<inter> set Y = {}"
  proof(cases "X = E")
    case True
    hence "X = E" by simp
    then show ?thesis 
    proof(cases "Y = G")
      case True
      then show ?thesis using assms 
        using \<open>X = E\<close> by force
    next
      case False
      hence "Y \<in> XX" 
        using True \<open>X \<noteq> Y\<close> \<open>Y \<in> XX - {A} \<union> {E, G}\<close> by blast 
      moreover have "set X \<subseteq> set A" 
        using True assms by auto
      ultimately show ?thesis using assms(1)[of Y A] 
        using True \<open>X \<noteq> Y\<close> \<open>Y \<in> XX - {A} \<union> {E, G}\<close> assms(2) assms by auto
    qed
  next
    case False
    hence "X \<noteq> E" by simp
    then show ?thesis
    proof(cases "X = G")
      case True
      hence "X = G" by simp
      then show ?thesis 
      proof(cases "Y = E")
      case True
       then show ?thesis using assms 
        using \<open>X = G\<close> by blast
      next
      case False
        hence "Y \<in> XX" 
        using True \<open>X \<noteq> Y\<close> \<open>Y \<in> XX - {A} \<union> {E, G}\<close> by blast 
      moreover have "set X \<subseteq> set A" 
        using True assms  by auto
      ultimately show ?thesis using assms(1)[of Y A] 
        using True \<open>X \<noteq> Y\<close> \<open>Y \<in> XX - {A} \<union> {E, G}\<close> assms(2) assms by auto
      qed
    next
      case False
      hence a: "X \<in> XX" 
        using \<open>X \<in> XX - {A} \<union> {E, G}\<close> \<open>X \<noteq> E\<close> by blast
      moreover have b: "X \<noteq> A" 
        using False \<open>X \<in> XX - {A} \<union> {E, G}\<close> \<open>X \<noteq> E\<close> by fastforce
      ultimately  show ?thesis 
      proof(cases "Y = E", goal_cases)
        case 1
        thus ?case
          using  assms(1)[of X A] a b assms(2) assms by fast
      next
        case 2
        thus ?case
        using  assms(1)[of X A] a b  assms  \<open>Y \<in> XX - {A} \<union> {E, G}\<close>
               \<open>X \<noteq> Y\<close> \<open>Y \<in> XX - {A} \<union> {E, G}\<close> \<open>\<lbrakk>X \<in> XX; A \<in> XX; X \<noteq> A\<rbrakk> \<Longrightarrow> set X \<inter> set A = {}\<close> 
              assms(1)[of X Y ] 
        by (cases "Y = G") fastforce+
     qed
    qed
  qed
qed

lemma disjoint_lists_sublists':
  assumes "\<And> X Y. \<lbrakk>X \<in> XX; Y \<in> XX; X \<noteq> Y\<rbrakk> \<Longrightarrow> set X \<inter> set Y = {}"
          "A \<subseteq> XX"
          "setA \<supseteq> set E \<union> set G"
          "setA = (\<Union> {set H| H. H \<in> A})"
          "set E \<inter> set G = {}"
          "\<And> H. H \<in> A \<Longrightarrow> distinct H"
  shows   "\<And> X Y. 
           \<lbrakk>X \<in> XX-A \<union>{E,G}; Y \<in> XX-A \<union>{E,G}; X \<noteq> Y\<rbrakk> \<Longrightarrow> set X \<inter> set Y = {}"
proof-
  fix X Y
  assume "X \<in> XX - A \<union> {E, G} " " Y \<in> XX - A \<union> {E, G} " "X \<noteq> Y "
  then show "set X \<inter> set Y = {}"
  proof(cases "X = E")
    case True
    hence "X = E" by simp
    then show ?thesis 
    proof(cases "Y = G")
      case True
      then show ?thesis using assms 
        using \<open>X = E\<close> by force
    next
      case False
      hence "Y \<in> XX" 
        using True \<open>X \<noteq> Y\<close> \<open>Y \<in> XX - A \<union> {E, G}\<close> by blast 
      moreover have "set X \<subseteq> (\<Union> {set H| H. H \<in> A})" 
        using True assms by auto
      ultimately show ?thesis using assms(1)
        using True \<open>X \<noteq> Y\<close> \<open>Y \<in> XX - A \<union> {E, G}\<close> assms(2) assms by auto
    qed
  next
    case False
    hence "X \<noteq> E" by simp
    then show ?thesis
    proof(cases "X = G")
      case True
      hence "X = G" by simp
      then show ?thesis 
      proof(cases "Y = E")
      case True
       then show ?thesis using assms 
        using \<open>X = G\<close> by blast
      next
      case False
        hence "Y \<in> XX" 
        using True \<open>X \<noteq> Y\<close> \<open>Y \<in> XX - A \<union> {E, G}\<close> by blast 
      moreover have "set X \<subseteq> (\<Union> {set H| H. H \<in> A})" 
        using True assms  by auto
      ultimately show ?thesis using assms(1)
        using True \<open>X \<noteq> Y\<close> \<open>Y \<in> XX - A \<union> {E, G}\<close> assms(2) assms by auto
      qed
    next
      case False
      hence a: "X \<in> XX" 
        using \<open>X \<in> XX - A \<union> {E, G}\<close> \<open>X \<noteq> E\<close> by blast
      moreover have b: "X \<notin> A" 
        using False \<open>X \<in> XX - A \<union> {E, G}\<close> \<open>X \<noteq> E\<close> by fastforce
      ultimately  show ?thesis 
      proof(cases "Y = E", goal_cases)
        case 1
        note yassm = this
        hence "set Y \<subseteq> setA" 
          using assms(3) by auto
        show "set X \<inter> set Y = {}"        
        proof(rule ccontr)
          assume "set X \<inter> set Y \<noteq> {}"
          then obtain y where "y \<in> set X \<inter> set Y " by auto
          hence "y \<in> \<Union> {set H |H. H \<in> A}" 
            using \<open>set Y \<subseteq> setA\<close> assms(4) by blast
          then obtain  Z where "Z \<in> A \<and> y \<in> set Z " by auto
          have "Z \<noteq> X" 
            using \<open>Z \<in> A \<and> y \<in> set Z\<close> b by blast
          moreover have "Z \<in> XX \<and> X \<in> XX" 
            using \<open>Z \<in> A \<and> y \<in> set Z\<close> a assms(2) by blast
          ultimately show False 
            using \<open>Z \<in> A \<and> y \<in> set Z\<close> \<open>y \<in> set X \<inter> set Y\<close> assms(1) by auto
        qed 
      next 
        case 2
        thus ?case
        proof(cases "Y = G", goal_cases)
          case 1
          note yassm = this
        hence "set Y \<subseteq> setA" 
          using assms(3) by auto
        show "set X \<inter> set Y = {}"        
        proof(rule ccontr)
          assume "set X \<inter> set Y \<noteq> {}"
          then obtain y where "y \<in> set X \<inter> set Y " by auto
          hence "y \<in> \<Union> {set H |H. H \<in> A}" 
            using \<open>set Y \<subseteq> setA\<close> assms(4) by blast
          then obtain  Z where "Z \<in> A \<and> y \<in> set Z " by auto
          have "Z \<noteq> X" 
            using \<open>Z \<in> A \<and> y \<in> set Z\<close> b by blast
          moreover have "Z \<in> XX \<and> X \<in> XX" 
            using \<open>Z \<in> A \<and> y \<in> set Z\<close> a assms(2) by blast
          ultimately show False 
            using \<open>Z \<in> A \<and> y \<in> set Z\<close> \<open>y \<in> set X \<inter> set Y\<close> assms(1) by auto
        qed 
      next
        case 2
        thus ?case
          using \<open>X \<noteq> Y\<close> \<open>Y \<in> XX - A \<union> {E, G}\<close> assms(1) by force
      qed
    qed
   qed
 qed
qed

lemma distinct_single_extract:
  assumes "distinct (xs@[x]@ys)" 
  shows   "set (xs@ys) = set (xs@[x]@ys) - {x}"
proof
  show "set (xs @ ys) \<subseteq> set (xs @ [x] @ ys) - {x}"
  proof
    fix y
    assume " y \<in> set (xs @ ys) "
    hence "y \<in> set xs \<or> y \<in> set ys" by simp
    have "y \<noteq> x" 
      using \<open>y \<in> set xs \<or> y \<in> set ys\<close> assms by auto
    then show "y \<in> set (xs @ [x] @ ys) - {x}" 
      using \<open>y \<in> set xs \<or> y \<in> set ys\<close> by auto
  qed
  show "set (xs @ [x] @ ys) - {x} \<subseteq> set (xs @ ys)" 
  proof
   fix y
   assume " y \<in> set (xs @ [x] @ ys) - {x}"
   hence "y \<noteq> x" by auto
   thus " y \<in> set (xs @ ys) " 
     using \<open>y \<in> set (xs @ [x] @ ys) - {x}\<close> by auto
 qed
qed

lemma set_append_swap: "set (xs@ys) = set (ys@xs)" by auto

lemma in_union_of_sets_append:
 "\<Union> {set xs| xs. xs \<in> xss \<union> {ys,zs}} = \<Union> {set xs| xs. xs \<in> xss \<union> {ys@zs}}"
  by fastforce

lemma extract_first_x:
  "\<lbrakk>x \<in> set xs; P x\<rbrakk> \<Longrightarrow> \<exists> y ys zs. xs = ys@[y]@zs \<and> P y \<and>( \<nexists> z. z \<in> set ys \<and>  P z)"
  apply(induction xs, simp)
  subgoal for a xs
    apply(cases "P a") 
    apply fastforce
    by (metis append_Cons set_ConsD)
  done

lemma extract_last_x:
  "\<lbrakk>x \<in> set xs; P x\<rbrakk> \<Longrightarrow> \<exists> y ys zs. xs = ys@[y]@zs \<and> P y \<and>( \<nexists> z. z \<in> set zs \<and>  P z)"
proof(induction xs arbitrary: x)
  case (Cons xx xs)
  then show ?case 
  proof(cases xs)
    case Nil
    then show ?thesis 
      using Cons.prems(1) Cons.prems(2) by fastforce
  next
    case (Cons a list)
    then show ?thesis 
    proof(cases "\<exists> z. z \<in> set list \<and> P z")
      case True
      then obtain y ys zs where "xs = ys@[y]@zs \<and> P y \<and>( \<nexists> z. z \<in> set zs \<and>  P z)" 
        by (metis Cons.IH list.set_intros(2) local.Cons)
      then show ?thesis 
        by (metis append_Cons)
    next
      case False
      hence "P a \<or> P x"
        using Cons.prems(2) by blast 
      then show ?thesis 
      proof(cases "P a", goal_cases)
        case 1
        thus ?case
          using False Cons
          by (auto intro!: exI[of _ a] intro: exI[of _ "[xx]"])
      next
        case 2
        thus ?case
          using Cons.prems(1) False local.Cons
          by(auto intro!: exI[of _ xx] intro: exI[of _  Nil])
      qed
    qed
  qed
qed simp

text \<open>This lemma is a little bit more interesting: If there are list elements with a certain property,
then there are also a first and a last element satisfying that condition. 
Quite intuitive, but requires a formal proof.\<close>

lemma extract_first_and_last:
  assumes "x \<in> set xs" "y \<in> set xs" "P x" "P y" "x \<noteq> y"
    shows "\<exists> a b as bs cs. 
             xs = as @[a]@bs@[b]@cs \<and> P a \<and> P b 
             \<and> (\<nexists> z. z \<in> set as \<and> P z)
             \<and> (\<nexists> z. z \<in> set cs \<and> P z)"
proof-
  obtain as a rest where asarest:"xs = as@[a]@rest \<and> P a \<and> (\<nexists> z. z \<in> set as \<and> P z)" 
    by (metis assms(2) assms(4) extract_first_x)
  hence "\<exists> z. z \<in> set rest \<and> P z"
    using assms by auto
  then obtain bs b cs where bsdcs:"rest = bs@[b]@cs \<and> P b \<and> (\<nexists>z. z \<in> set cs \<and> P z)" 
    by (metis extract_last_x)
  thus ?thesis using asarest by force
qed

lemma map_hd: "xs \<noteq> [] \<Longrightarrow> hd (map f xs) = f (hd (xs))" 
  using list.map_sel(1) by auto

lemma map_last': "\<lbrakk>xs \<noteq> []; \<And> x. g (f x) = h x\<rbrakk> \<Longrightarrow>g (last (map f xs)) = h (last xs)"
  by (metis last_map)

lemma in_set_map: "y \<in> set (map f xs) \<Longrightarrow> \<exists> x. y = f x \<and> x \<in> set xs" by auto

lemma map_in_set: "x\<in> set xs \<Longrightarrow> f x \<in> set (map f xs)"
  by(induction xs) (auto simp add: list.set_intros(2) set_ConsD)

lemma single_in_append: "([a]@xs) = a#xs"
  by simp

lemma map_split_exists:
  "map f xs = ys@zs \<Longrightarrow> \<exists> ys' zs'. ys'@zs' = xs \<and> map f ys' = ys \<and> map f zs' = zs"
  by (metis append_eq_map_conv)

lemma map_sum_split: 
  "foldr (\<lambda> x acc. f x + acc) (xs@ys) (0::real) = 
   foldr (\<lambda> x acc. f x + acc) xs 0 + foldr (\<lambda> x acc. f x + acc) ys 0"
  by(induction xs) simp+

lemma fold_sum_neg_neg_element:
  "foldr (\<lambda> x acc. f x + acc) xs (0::real) < 0 \<Longrightarrow> \<exists> x \<in> set xs. f x < 0"
  by(induction xs) force+

lemma butlast_tail: 
  "xs \<noteq> [] \<Longrightarrow> butlast (x#xs) = x#butlast xs"
  by simp

lemma inter_distr_append: 
  "(set (xs@ys) \<inter> set zs= {}) = 
   (set (xs) \<inter> set zs= {} \<and> set (ys) \<inter> set zs= {})"
  by auto

lemma in_append_split: "(z \<in> set (xs @ ys)) = (z \<in> set xs \<or> z \<in> set ys)" 
  by simp  

lemma non_empt_elim:
  "\<lbrakk>xs \<noteq> []; \<And> a list. xs = a#list \<Longrightarrow> P xs\<rbrakk> \<Longrightarrow> P xs"
  by(cases xs, auto)

lemma non_empt_elim_triple:
 "\<lbrakk>\<And> x. xs = [x] \<Longrightarrow> P xs; \<And> x y ys. x#y#ys = xs \<Longrightarrow> P xs; xs \<noteq> []\<rbrakk> \<Longrightarrow> P xs"
  apply(cases xs, force)
  subgoal for a list
    by(cases list, auto)
  done

lemma nth_append':
  "\<lbrakk>(xs@ys) ! i = (xs@ys) ! j; i < length xs; j < length xs\<rbrakk> \<Longrightarrow> xs ! i =xs ! j"
  by (metis nth_append)

lemma list_cases4:
  "\<lbrakk>xs = [] \<Longrightarrow> P; \<And> x. xs = [x] \<Longrightarrow> P ;
    \<And> x y. xs = x#y#[] \<Longrightarrow> P; \<And> x y z zs. xs = x#y#z#zs \<Longrightarrow> P\<rbrakk>
    \<Longrightarrow> P"
  by(cases xs, force, metis neq_Nil_conv)

lemma  set_singleton_list: "set [ x] = {x}" for x by simp

lemmas list_cases3 = remdups_adj.cases

lemma append_two: "[a]@[b] = [a,b]" 
  by simp

lemma list_induct3: "\<lbrakk>P Nil; \<And> x. P [x]; \<And> x y xs. P (y#xs) \<Longrightarrow> P (x#y#xs)\<rbrakk> \<Longrightarrow> P xs"
  by (metis list_nonempty_induct neq_Nil_conv)

lemma list_induct3_len_geq_2: "length xs \<ge> 2 \<Longrightarrow> (\<And> x y. P [x,y]) \<Longrightarrow> (\<And> x y xs. P (y#xs) \<Longrightarrow> P (x#y#xs)) \<Longrightarrow> P xs" for xs P
  apply(induction rule: list_induct3)
  using not_less_eq_eq by fastforce+

lemma list_induct2_len_geq_1: 
  "\<lbrakk>length xs \<ge> 1; \<And> x. P [x]; \<And> x y xs. P (y#xs) \<Longrightarrow> P (x#y#xs)\<rbrakk> \<Longrightarrow> P xs" 
  by (metis One_nat_def length_greater_0_conv less_eq_Suc_le list.exhaust_sel list_nonempty_induct)

lemma snoc_eq_iff_butlast': "ys = xs @ [x] \<longleftrightarrow> (ys \<noteq> [] \<and> butlast ys = xs \<and> last ys = x)"
  by fastforce

lemma neq_Nil_conv_snoc: "xs \<noteq> [] \<longleftrightarrow> (\<exists>x ys. xs = ys @ [x])"
  by (meson snoc_eq_iff_butlast')

lemma list_cases_both_sides: 
"\<lbrakk>xs = [] \<Longrightarrow> P; \<And> x. xs =[x] \<Longrightarrow> P; \<And> x y ys. xs =[x]@ys@[y] \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P "
  by (metis neq_Nil_conv neq_Nil_conv_snoc single_in_append)

lemma append_butlast_last_cancel: "p \<noteq> [] \<Longrightarrow> butlast p @ last p # p' = p @ p'"
  by simp

lemma induct_list_length2: 
"\<lbrakk>length xs \<ge> 2; \<And> x y. P [x,y]; \<And> xs x y z. P (xs@[x,y]) \<Longrightarrow> P(xs@[x,y,z])\<rbrakk> \<Longrightarrow> P xs"
proof(induction xs rule: rev_induct)
  case (snoc z xs)
  note IH = this
  show ?case 
  proof(cases xs)
    case (Cons b list)
    note cons = this
    show ?thesis 
    proof(cases list)
      case (Cons b llist)
      then obtain ys x y where axs_subst:"xs = ys@[x,y]"
        by (metis append_Cons append_butlast_last_cancel cons list.distinct(1) neq_Nil_conv_snoc)
      show ?thesis
        using axs_subst IH(3,4) snoc.IH 
        by (fastforce intro: IH(4))
    next
      case Nil
      then show ?thesis
        using cons snoc.prems(2) by fastforce
    qed
    next
      case Nil
      then show ?thesis 
        using snoc.prems(1) by force
    qed
  qed simp

lemma list_cases_betw: 
"\<lbrakk>length xs \<ge> 2; \<And> x y. xs = [x,y] \<Longrightarrow> P; \<And> ys x y. xs = [x]@ys@[y] \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto intro: list_cases_both_sides[of xs]) 

lemma list_cases2_both_sides:
  "\<lbrakk>length xs \<ge> 2; \<And> x y zs. xs = x#zs@[y] \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" for P
  by(cases xs rule: list_cases_betw) auto

lemma get_longest_common_tail:
assumes "length p \<ge> 1" "length q \<ge> 1" "last p = last q"
obtains ys p' q' where "p = p'@ys" "q =q'@ys" 
                        "\<And> ys' p'' q''. \<lbrakk>p=p''@ys'; q = q''@ys'\<rbrakk> \<Longrightarrow> length ys' \<le> length ys"
  using assms 
proof(induction "length p" arbitrary: p q thesis rule: less_induct)
  case less
  then obtain pa a where p_last:"p = pa@[a]"
    by (metis append_butlast_last_id list.size(3) not_one_le_zero)
  from less obtain qb b where q_last:"q = qb@[b]"
    by (metis append_butlast_last_id list.size(3) not_one_le_zero)
  have butlasts: "butlast p = pa" "butlast q = qb"
    by (auto simp add: p_last q_last)
  have last_q: "last q = a"
    using less.prems(4) p_last by auto
  show ?case
  proof(cases pa)
    case Nil
    then have "p = []@[a]" "q =qb@[a]" 
                        "\<And> ys' p'' q''. pa=p''@ys' \<Longrightarrow> qb = q''@ys' \<Longrightarrow> length ys' \<le> length [a]"
      using less.prems(4) p_last q_last  local.Nil by force+
    then show ?thesis 
      using less.prems(1) by fastforce
  next
    case (Cons x list)
    note cons = this
    show ?thesis
  proof(cases qb)
    case Nil
      then have "p = pa@[a]" "q =[]@[a]" 
        using less.prems(4) local.Nil p_last q_last by fastforce+
      moreover from this Nil
      have  "\<lbrakk>p=p''@ys'; q= q''@ys'\<rbrakk> \<Longrightarrow> length ys' \<le> length [a]" for ys' p'' q''
        using  local.Nil q_last by(cases ys') (auto simp add: Cons_eq_append_conv)
      ultimately show ?thesis     
        using less.prems(1) by force 
    next
      case (Cons y kist)
      show ?thesis
      proof(cases "last pa = last qb")
        case True
      obtain  p' q' ys  where IH_applied:"pa = p'@ys" "qb =q'@ys" 
                        "\<And> ys' p'' q''. \<lbrakk>pa=p''@ys'; qb = q''@ys'\<rbrakk> \<Longrightarrow> length ys' \<le> length ys"
        using butlasts p_last cons Cons True 
        by (auto intro: less(1)[of "butlast p" qb, simplified butlasts(1)])
      hence "p = p'@ys@[a]" "q=q'@ys@[a]" 
        using IH_applied(2) last_q q_last by(auto simp add: p_last)
      moreover have  "\<lbrakk>p=p''@ys'; q = q''@ys'\<rbrakk> \<Longrightarrow> length ys' \<le> length (ys@[a])" for ys' p'' q''
          using last_q q_last  p_last IH_applied(3)[of p'' "butlast ys'" q''] butlasts(2)
          by(cases ys' rule: rev_cases) (auto simp add: butlast_append)
      ultimately show ?thesis 
        using less.prems(1) by force
    next
      case False
      hence "p = pa@[a]" "q =qb@[a]" 
        using last_q q_last p_last by auto
      moreover have  "\<lbrakk>p=p''@ys'; q = q''@ys'\<rbrakk> \<Longrightarrow> length ys' \<le> length [a]" for ys' p'' q''
          using False butlasts last_q p_last
          by(cases ys' rule: rev_cases, simp)
            (auto simp add: butlast_snoc[of "_ @ _", simplified] 
                            last_append if_split[of _ "_ = Nil"])
      ultimately show ?thesis
        using less.prems(1) by force
    qed
  qed
qed
qed

lemma inter_Big_union_distr_empt_list:
  "(\<And> C. C \<in> B \<Longrightarrow> A \<inter> set C = {}) \<Longrightarrow> (A \<inter> \<Union> { set C| C. C \<in> B}) = {}" for A B by auto

lemma foldl_invar: 
 "\<lbrakk>inv x; \<And> y z. inv y \<Longrightarrow> inv (f y z)\<rbrakk> \<Longrightarrow> inv (foldl f x xs)" for inv
  by(induction xs arbitrary: x) auto

lemma foldr_invar: 
  "\<lbrakk>inv x; \<And> y z. inv y \<Longrightarrow> inv (f z y)\<rbrakk> \<Longrightarrow> inv (foldr f xs x)" for inv
  by(induction xs arbitrary: x) auto

lemma list_in_image_map: "set ys \<subseteq> f ` X \<Longrightarrow> \<exists> xs. map f xs = ys \<and> set xs \<subseteq> X"
proof(induction ys)
  case (Cons y ys)
  then obtain x where "x \<in> X" "f x = y"  by auto
  moreover obtain xs where "map f xs = ys" "set xs \<subseteq> X"
    using Cons by auto
  ultimately show ?case 
    by(auto intro!: exI[of _ "x#xs"])
qed simp

lemma rev_cases3: 
  "\<lbrakk>xs = Nil \<Longrightarrow> P; \<And> x. xs = [x] \<Longrightarrow> P; \<And> ys y x. xs=ys@[y,x] \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" 
  by (metis More_Lists.append_butlast_last_cancel append_Nil neq_Nil_conv_snoc)


lemma list_split_off_last_two:
  assumes "length xs \<ge> 2"
  obtains ys x y where "xs = ys@[x,y]"
  using assms by(cases xs rule: rev_cases3) auto

fun itrev_aux :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"itrev_aux  [] ys = ys" |
"itrev_aux  (x #xs) ys = itrev_aux  xs (x #ys)"
definition "itrev xs = itrev_aux  xs Nil"

lemma itrev_rev_gen:"itrev_aux xs ys = rev xs @ ys"
  by(induction xs ys arbitrary: rule: itrev_aux.induct) auto

lemma itrev_is_rev[simp]: "itrev = rev"
  by(auto simp add: itrev_rev_gen[of _ Nil, simplified] itrev_def)

<<<<<<< HEAD:Data_Structures/More_Lists.thy
=======
lemma distinct_indexE:
   "\<lbrakk>distinct xs; (\<And> i j. \<lbrakk>i < length xs; j < length xs; xs! i = xs ! j\<rbrakk> \<Longrightarrow> i = j) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  and distinct_indexD:
   "\<lbrakk>distinct xs; i < length xs; j < length xs; xs! i = xs ! j\<rbrakk> \<Longrightarrow> i = j"
  by (simp add: nth_eq_iff_index_eq)+

lemma list_cases_hd_and_last:
  "\<lbrakk>xs = Nil \<Longrightarrow> P; \<And> x. xs = [x] \<Longrightarrow> P; \<And> x y xs'. xs = x#xs'@[y] \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(cases xs, all \<open>cases xs rule: rev_cases\<close>) (auto elim!: rev_exhaust)

fun foldl2 :: "('b \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b" where
foldl2_Nil:  "foldl2 f a [] = a" |
foldl2_Sing:  "foldl2 f a [x] = a" |
foldl2_Cons: "foldl2 f a (x # y#xs) = foldl2 f (f a x y) (y#xs)"

fun foldr2 :: "('a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b" where
foldr2_Nil:  "foldr2 f [] = id" |
foldr2_Sing: "foldr2 f [_] = id"|
foldr2_Cons: "foldr2 f (x # y# xs) = f x y \<circ> foldr2 f (y#xs)"

lemma list_nempty_induct:
  "\<lbrakk>xs \<noteq> []; \<And> x. P [x]; \<And> x y xs. P (y#xs) \<Longrightarrow> P (x#y#xs)\<rbrakk> \<Longrightarrow> P xs"
  by (metis list.exhaust list_nonempty_induct)

lemma foldr2_append_one:
  assumes "xs \<noteq> []"
  shows "foldr2 (\<lambda>x1 x2 y. f y x2 x1) (xs @ [v']) (f a v v') =
       foldr2 (\<lambda>x1 x2 y. f y x2 x1) (xs @ [v', v]) a"
  by(induction rule: list_nempty_induct[OF assms]) simp+

lemma foldl2_conv_foldr2:
  "foldl2 f a xs = foldr2 (\<lambda>x1 x2 y. f y x2 x1) (rev xs) a"
proof(induction xs arbitrary: a f rule: list_induct3)
  case 1
  then show ?case by simp
next
  case (2 v)
  then show ?case by simp
next
  case (3 v v' l)
  have "foldr2 (\<lambda>x1 x2 y. f y x2 x1) (rev l @ [v']) (f a v v') =
    foldr2 (\<lambda>x1 x2 y. f y x2 x1) (rev l @ [v', v]) a"
  proof(cases l)
    case (Cons a list)
    then show ?thesis 
      using foldr2_append_one by fast
  qed simp
  thus ?case 
    by(simp add: 3)
qed

lemma list_induct_longer_2:
  "\<lbrakk>length xs \<ge> 2; \<And> x y. P [x, y]; \<And> x y z xs. P (y#z#xs) \<Longrightarrow> P (x#y#z#xs)\<rbrakk> \<Longrightarrow> P xs"
  by (metis list_induct3_len_geq_2 list_cases3)
>>>>>>> weighted_blossom:Set_Graphs/Directed_Graphs/More_Lists.thy

end