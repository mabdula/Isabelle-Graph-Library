theory More_Arith
  imports Main Complex_Main "HOL-Library.Extended_Real" More_Logic
begin

subsection \<open>Sums\<close>

lemma sum_cong_extensive: "\<lbrakk>A = B; \<And> x. \<lbrakk>x \<in> A; x \<in> B\<rbrakk> \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> sum f A = sum g B"
  by simp

lemma add_0_cong_left: "(a::int) = b \<Longrightarrow> c = 0 \<Longrightarrow> c + a = b"
  by simp

lemma add_assoc2: "(a::nat) + (b + c) = a + b + c"
  by simp
lemma add_assoc3: "(a::nat) + (b + c + d ) = a + b + c + d" 
  by simp

lemma sum_if_P: 
  "(\<And> x. x \<in> X \<Longrightarrow> P x) \<Longrightarrow> sum (\<lambda> x. i x (if P x then g x else h x)) X = sum (\<lambda> x. i x (g x)) X" 
  by simp

lemma sum_if_not_P:
  "(\<And> x. x \<in> X \<Longrightarrow> \<not> P x) \<Longrightarrow> sum (\<lambda> x. i x (if P x then g x else h x)) X = sum (\<lambda> x. i x (h x)) X" 
  by simp

lemma sum_if_not_P_not_Q_but_R:
  "\<lbrakk>(\<And> x. x \<in> X \<Longrightarrow> \<not> P x); (\<And> x. x \<in> X \<Longrightarrow> \<not> Q x);(\<And> x. x \<in> X \<Longrightarrow> R x)\<rbrakk> \<Longrightarrow> 
     sum (\<lambda> x. i x (if P x then g x else if Q x then h x else if R x then h1 x else h2 x)) X 
   = sum (\<lambda> x. i x (h1 x)) X" 
  by simp

lemma sum_if_not_P_not_Q_not_R:
  "\<lbrakk>(\<And> x. x \<in> X \<Longrightarrow> \<not> P x); (\<And> x. x \<in> X \<Longrightarrow> \<not> Q x);(\<And> x. x \<in> X \<Longrightarrow> R x)\<rbrakk> \<Longrightarrow> 
     sum (\<lambda> x. i x (if P x then g x else if Q x then h x else if R x then h1 x else h2 x)) X 
   = sum (\<lambda> x. i x (h1 x)) X" 
  by simp

lemma two_sum_remove: "(\<Sum>e'\<in>{x, y}. g e') = (if x \<noteq> y then g x + g y else g x)"
  by simp

lemma disjoint_multiple_sum:
  assumes "finite X"
  shows  "\<lbrakk>\<And> x y. \<lbrakk>x \<in> X; y \<in> X; x\<noteq>y\<rbrakk> \<Longrightarrow> f x \<inter> f y = {};
           \<And> x. x \<in> X \<Longrightarrow> finite (f x)\<rbrakk>
          \<Longrightarrow> (\<Sum> x \<in> X. (\<Sum> y \<in> f x. (g y))) = (\<Sum> y \<in> (\<Union> x \<in> X. f x) . g y)"
  using assms(1)
proof(induction )
  case (insert xx X)
  have " (\<Sum>x\<in>insert xx X. sum g (f x)) = sum g (f xx) + (\<Sum>x\<in> X. sum g (f x))" 
    by (meson insert.hyps(1) insert.hyps(2) sum.insert_if)
  moreover have "(\<Sum>x\<in>X. sum g (f x)) = sum g  (\<Union> x \<in> X. f x)" 
    by (simp add: insert.IH insert.prems)
  moreover have " (\<Union> x \<in> X. f x) \<inter> f xx = {}" 
  proof(rule ccontr)
    assume " (\<Union> x \<in> X. f x) \<inter> f xx \<noteq> {}"
    then obtain y where "f y \<inter> f xx \<noteq> {} \<and> y \<in> X" by blast
    then show False 
      using insert.hyps(2) insert.prems by blast
  qed
  moreover have " (\<Union> x \<in> insert xx X. f x) = f xx \<union> (\<Union> x \<in> X. f x)" 
    by auto
  moreover have "finite ((\<Union> x \<in> X. f x))" 
    by (simp add: insert.hyps(1) insert.prems(2))
  ultimately show ?case using sum.union_disjoint[of "f xx" "(\<Union> x \<in> X. f x)" g]
    by (metis inf_commute insert.prems(2) insertCI)
qed simp

lemma sum_inj: "inj f \<Longrightarrow> sum g (f ` X) = sum (g \<circ> f) X"
  by (simp add: inj_def inj_onI sum.reindex)

lemma sum_inj_on: "inj_on f X \<Longrightarrow> sum g (f ` X) = sum (g \<circ> f) X"
  by (simp add: inj_def inj_onI sum.reindex)

lemma sum_eq_split: "\<lbrakk>a = b; c = d\<rbrakk> \<Longrightarrow> a + c = b + d"
  by auto

lemma diff_eq_split: "\<lbrakk>a = b; c = d\<rbrakk> \<Longrightarrow> a - c = b - d"
  by auto

lemma sum_singleton: "(\<Sum> i \<in> {x}. f i) = f x"
  by(rule  trans[OF sum.insert_remove[of "{}" f x]], simp+)

lemma union_disjoint_triple: 
  "\<lbrakk>finite A; finite B; finite C; A \<inter> B = {}; A \<inter> C = {}; B \<inter> C = {} \<rbrakk>
   \<Longrightarrow> sum f (A \<union> B \<union> C) = sum f A + sum f B + sum f C" 
  by (simp add: boolean_algebra.conj_disj_distrib2 sum_Un_eq)

lemma sum_index_shift: "finite X \<Longrightarrow> sum f {x+(k::nat)|x. x \<in> X} = sum (\<lambda>x. f (x+k)) X"
  proof(induction rule: finite.induct)
    case (insertI X x)
    then show ?case
    proof(cases "x \<in> X")
      case False
      thus ?thesis 
      proof(subst insert_is_Un)
        assume assm: " x \<notin> X"
       have "{xa + k |xa. xa \<in> {x} \<union> X} = 
           ({x+ k} \<union> {xa + k |xa. xa \<in>  X})" 
        by(rule, blast, auto )
       hence "sum f {xa + k |xa. xa \<in> {x} \<union> X} = 
           sum f ({x+ k} \<union> {xa + k |xa. xa \<in>  X})" by simp
       also have "... = sum f {x+ k} + sum f {xa + k |xa. xa \<in>  X}"
         using  finite_image_iff[of "(+) k" X] assm insertI
         by (auto intro: sum.union_disjoint)
       also have "... = (\<Sum>x\<in>{x}.f (x+k)) + (\<Sum>x\<in>X. f (x + k))"
         by (simp add: insertI)
       also have "... = (\<Sum>x\<in>{x} \<union>X. f (x + k))"
         using assm insertI by(auto intro: sum.union_disjoint)
       finally show "sum f {xa + k |xa. xa \<in> {x} \<union> X} = (\<Sum>x\<in>insert x X. f (x + k))" by simp
     qed
   qed (smt (verit, best) Collect_cong insert_absorb)
 qed simp

lemma distinct_sum: "distinct xs \<Longrightarrow> sum f (set xs)  = foldr (\<lambda> x acc. acc + f x) xs 0"
  by(induction xs) (simp add: add.commute)+

lemma distinct_sum2: "distinct xs \<Longrightarrow> sum f (set xs)  = foldr (\<lambda> x acc.  f x + acc) xs 0"
  by(induction xs) (simp add: add.commute)+

lemma sum_zero_not_all_zero: 
  assumes "finite X" "sum (f::'b \<Rightarrow> real) X = 0"  "\<exists> x \<in> X. f x \<noteq> 0"
  shows   "\<exists> x \<in> X. f x > 0"
proof(rule ccontr)
  assume a:"\<not> (\<exists>x\<in>X. 0 < f x)"
  hence b:"\<And> x. x \<in> X \<Longrightarrow> f x \<le> 0" by auto
  hence c:"\<exists> x \<in> X. f x < 0" using assms(3) by force
  have "sum f X < sum (\<lambda> x. 0) X"
    using assms(1) b c 
    by (intro sum_strict_mono_ex1, auto)
  thus False using assms(2) by simp
qed

lemma sum_except_two: 
  "\<lbrakk>finite X; a \<noteq> b; a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> sum f X = sum f (X- {a,b}) +  f a + f b"
  by (metis DiffI Diff_insert add.commute finite_Diff insert_absorb singletonD sum.insert_remove)

lemma sum_split_off: "\<lbrakk>A \<subseteq> B; finite B; \<And> x. x \<in> B - A \<Longrightarrow> f x = 0\<rbrakk> \<Longrightarrow> sum f A = sum f B" 
  by (simp add: sum.mono_neutral_cong_right)

lemma sum_filter_zero: "finite X \<Longrightarrow> sum f X = sum f {x|x.   x \<in> X \<and> f x \<noteq>0 }"
  by (metis (mono_tags, lifting) DiffD1 DiffD2 mem_Collect_eq subsetI sum.mono_neutral_cong_left)

lemma sum_up_leq:
  "\<lbrakk>\<And> j. \<lbrakk>(a::nat) \<le> j; j < i\<rbrakk> \<Longrightarrow>((f j)::nat) \<le> g j; a < i; n = i - a\<rbrakk>
  \<Longrightarrow> (\<Sum>j = a..<i. f j) \<le> (\<Sum>j = a..<i. g j)"
proof(induction n arbitrary: a)
  case (Suc n)
  have " sum f {a..<i} =  f a + sum f {Suc a..<i}" 
    using Suc.prems(2) sum.atLeast_Suc_lessThan by blast
  also have "... \<le> g a + sum f {Suc a..<i}"
    using Suc(2)[of a] Suc(3) by simp
  also have "... \<le> g a + sum g {Suc a..<i}"
    using Suc(1)[of "Suc a"] Suc(3,4) Suc(2) by force
  also have "... =  sum g {a..<i}" 
    by (simp add: Suc.prems(2) sum.atLeast_Suc_lessThan)
  finally show ?case by simp
qed simp

lemma sum_up_same_cong:
  "\<lbrakk>\<And> j. \<lbrakk>(a::nat) \<le> j; j < i\<rbrakk> \<Longrightarrow> ((f j)::nat) = g j; a \<le> i; n = i - a\<rbrakk>
   \<Longrightarrow> (\<Sum>j = a..<i. f j) = (\<Sum>j = a..<i. g j)"
proof(induction n arbitrary: a)
  case (Suc n) 
    have a_less_i:"a < i" using Suc by auto
  have " sum f {a..<i} =  f a + sum f {Suc a..<i}" 
    using Suc.prems(2) sum.atLeast_Suc_lessThan a_less_i  by blast
  also have "... = g a + sum f {Suc a..<i}"
    using Suc(2)[of a] Suc(3) a_less_i by simp
  also have "... = g a + sum g {Suc a..<i}"
    using Suc(1)[of "Suc a"] Suc(3,4) Suc(2) by force
  also have "... =  sum g {a..<i}" 
    by (simp add: Suc.prems(2) a_less_i  sum.atLeast_Suc_lessThan)
  finally show ?case by simp
qed simp

lemma sum_up_assoc: "(\<Sum>j = a..<(i::nat). f j)  + (\<Sum>j = a..<i. g j) = (\<Sum>j = a..<i. f j +  g j)"
  by (simp add: sum.distrib)

lemma sum_ones_interval: "\<lbrakk>a \<le>(b::nat); n = b - a\<rbrakk> \<Longrightarrow> (\<Sum> j = a..<b. 1) = b-a"
proof(induction n arbitrary: a)
  case (Suc n)
  hence a_less_i: "a < b"by simp
  have " sum (\<lambda> x. 1) {a..<b} =  1 + sum (\<lambda> x. 1)  {Suc a..<b}" 
    using Suc.prems sum.atLeast_Suc_lessThan a_less_i by blast
  also have "... \<le> 1 + b - Suc a"
    using Suc(1)[of "Suc a"] Suc(3) Suc(2) by force
  also have "... =  b - a" 
    by (simp add: Suc.prems(2) sum.atLeast_Suc_lessThan)
  finally show ?case by simp
qed simp

lemma sum_indes_less_suc_conv: "(\<Sum> j \<in> {a..<Suc b}. f j) = (\<Sum> j \<in> {a.. b}. f j)" 
  using atLeastLessThanSuc_atLeastAtMost by presburger

lemma sum_cong: "(\<And> x. x \<in> X \<Longrightarrow> f x = g x) \<Longrightarrow> sum f X  = sum g X"
  by force

lemma binary_sum: 
  "\<lbrakk>finite S; \<And> x. x \<in> S \<Longrightarrow> f x = 1 \<or> f x = 0\<rbrakk> \<Longrightarrow> sum f S = int (card {x . x \<in> S \<and> f x = 1})"
  apply(induction rule: finite_induct) apply simp
  subgoal for x F
    apply(cases "f x = 1", subst sum.insert_remove, simp)
    apply(rule trans[of _ " (int (card {x \<in> F. f x = 1})) + 1"], simp)
    apply(subst arg_cong[OF sym[OF card_insert_disjoint[of "{x \<in> F. f x = 1}" x]], of int, simplified int_Suc])
    by(fastforce  intro!:  arg_cong[of _ _ int] arg_cong[of _ _ card] add_0_cong_left)+
  done

(*Needs to be here because of next lemma*)

lemma get_least: 
  assumes "P (n::nat)"
  obtains n_min where "P n_min" "\<not> (\<exists> m < n_min. P m)"
  by (metis assms bot_nat_0.extremum_strict ex_least_nat_le)

lemma sum_cards_with_life_time:
  assumes "finite \<S>"
          "(\<Union> j . S j) \<subseteq> \<S>"
          "\<And> i j x. \<lbrakk>j > i + life_time; x \<in> S i\<rbrakk> \<Longrightarrow> x \<notin> S j"
          "\<And> j. j > i \<Longrightarrow> S j = {}"
    shows "(\<Sum>  j \<in> {0..< Suc i}. card (S j)) \<le> (life_time +1 )* card \<S>"
  using assms(2-) 
proof(induction arbitrary: S rule: finite_induct[OF assms(1)] )
  case (2 x \<S>)
  have finite_Ss: "finite (S j)" for j
    using 2(1,4) finite_subset[OF 2(4)] finite_subset[of "S j" "\<Union> (range S)"] by auto
  show ?case 
  proof(cases "\<exists> j < Suc i. x \<in> S j")
    case True
    then obtain j_min where j_min_prop:"j_min < Suc i" "x \<in> S j_min" 
                                       "\<not> (\<exists> j < Suc i. x \<in> S j \<and> j < j_min)"
      using get_least[of "\<lambda> j. j < Suc i \<and> x \<in> S j"] by metis
    hence x_never_after: "j > j_min + life_time \<Longrightarrow> x \<notin> S j" for j
      using 2(5)[of j_min j x] by simp
   have "(\<Sum>j = 0..<Suc i. card (S j)) = (\<Sum>j = 0..< j_min. card (S j)) +
                   (\<Sum>j = j_min..<Suc i. card (S j))" 
    by (metis j_min_prop(1) le_eq_less_or_eq sum.atLeastLessThan_concat zero_le)
  also have "... = (\<Sum>j = 0..<j_min. card (S j)) +
                   ((\<Sum>j = j_min..< Suc (min (j_min + life_time) i). card (S j))+
                   (\<Sum>j = Suc (min (j_min + life_time) i)..< Suc i. card (S j)))"
    apply(rule sum_eq_split, simp)
    by (metis j_min_prop(1) less_add_Suc1 linorder_not_le min.commute min_absorb1 not_less_eq
            order_less_imp_le sum.atLeastLessThan_concat)
  also have "... = (\<Sum>j = 0..<j_min. card (S j - {x})) +
                   ((\<Sum>j = j_min..< Suc (min (j_min + life_time) i). card (S j))+
                   (\<Sum>j = Suc (min (j_min + life_time) i)..< Suc i. card (S j - {x})))"
    apply(rule sum_eq_split)
    subgoal
      apply(rule sum.ivl_cong, simp, simp)
      subgoal for j
        using j_min_prop(1,3) not_in_card_del[of x "S j"] 
        by fastforce
      done
        using j_min_prop(2) 2(5)[of j_min _ x] 2(6)[of _] 
        by (auto intro: sum.ivl_cong)
    also have "... \<le> (\<Sum>j = 0..<j_min. card (S j - {x})) +
                   ((\<Sum>j = j_min..< Suc (min (j_min + life_time) i). card (S j - {x}) + 1)+
                   (\<Sum>j = Suc (min (j_min + life_time) i)..< Suc i. card (S j - {x})))"
        apply(rule add_mono_thms_linordered_semiring(2), rule, simp)
      apply(rule add_mono_thms_linordered_semiring(3), rule)
      subgoal
        apply(rule sum_up_leq[OF _ _ refl])
      subgoal for j
       using  card.insert_remove[OF finite_Ss[of j], of x] card_insert_le[of "S j" x] 
       by auto
     using j_min_prop(1) by simp
   by simp
  also have "... = (\<Sum>j = 0..<j_min. card (S j - {x})) +
                   (((\<Sum>j = j_min..< Suc (min (j_min + life_time) i). card (S j - {x}))+
                   (\<Sum>j = j_min..< Suc (min (j_min + life_time) i). 1)) +
                   (\<Sum>j = Suc (min (j_min + life_time) i)..< Suc i. card (S j - {x})))"
    by(rule sum_eq_split, simp)
      (rule sum_eq_split, rule sym[OF sum_up_assoc], simp)
  also have "... = (\<Sum>j = 0..<j_min. card (S j - {x})) +
                   (((\<Sum>j = j_min..< Suc (min (j_min + life_time) i). card (S j - {x}))+
                   (Suc (min (j_min + life_time) i) - j_min)) +
                   (\<Sum>j = Suc (min (j_min + life_time) i)..< Suc i. card (S j - {x})))"
    apply(rule sum_eq_split, simp)
    apply(rule sum_eq_split, rule sum_eq_split, simp)
    subgoal
      apply(rule sum_ones_interval[OF _ refl])
      using min.boundedI[of "j_min" "j_min + life_time" i] j_min_prop(1)
      by simp
    by simp
  also have "... \<le>
            (\<Sum>j = 0..<j_min. card (S j - {x})) +
  (\<Sum>j = j_min..<Suc (min (j_min + life_time) i). card (S j - {x}))  +
   (\<Sum>j = Suc (min (j_min + life_time) i)..<Suc i. card (S j - {x})) + (life_time + 1)"
    by simp
  also have "... = (\<Sum>j = 0..<j_min. card (S j - {x})) +
  (\<Sum>j = j_min..<Suc i. card (S j - {x})) + (life_time + 1)"
    by (smt (z3) add.commute group_cancel.add2 j_min_prop(1) le_Suc_eq less_add_Suc1 min.commute 
            min_def order_less_imp_le sum.atLeastLessThan_concat)
  also have "... = (\<Sum>j = 0..<Suc i. card (S j - {x})) + (life_time + 1)"
    by (metis j_min_prop(1) le_eq_less_or_eq sum.atLeastLessThan_concat zero_le)
  also have "... \<le> (life_time + 1) * card \<S> + (life_time + 1)"
    apply(rule add_right_mono)
    using 2(4) 2(2)  2(5) 2(6) 
    by (intro 2(3)) fastforce+
  also have "... = (life_time + 1) * card (insert x \<S>)"
    by (simp add: "2.hyps"(1) "2.hyps"(2))
  finally show ?thesis by simp
next
  case False
  have "(\<Sum>j = 0..<Suc i. card (S j)) = 
        (\<Sum>j = 0..<Suc i. card (S j - {x}))"
    by (metis "2.prems"(3) False empty_Diff not_less_eq single_diff_remove)
  also have "... \<le> (life_time + 1) * (card \<S>) "
    using 2(4) 2(2)  2(5) 2(6) 
    by (intro 2(3)) fastforce+
  also have "... \<le> (life_time + 1) * (card (insert x \<S>))" 
    by (meson card_insert_le mult_le_mono2)
  finally show ?thesis by simp
 qed 
qed simp

subsection \<open>Reals and Ereals\<close>

lemma ereal_add_homo: "ereal (a + b) = ereal a + ereal b"
  by auto

lemma minus_distr: "- ((a::real) + b) = -a - b"
  by simp

lemma less_PInfty_sum: "\<lbrakk>a < PInfty; b < PInfty\<rbrakk> \<Longrightarrow> a +b < PInfty"
  by simp

lemma real_strict_mono:"a > b \<Longrightarrow> real a > real b"
  by auto

lemma pos_subs_ineq: "a \<le> b \<Longrightarrow> c \<ge> 0 \<Longrightarrow> a - c \<le> (b::real)" 
  by simp

lemma minus_leq_flip:"- (a::ereal) \<le> b \<Longrightarrow> - b \<le> a" 
  by (simp add: ereal_uminus_le_reorder)

lemma mul_zero_cancel: "(a::real) > 0 \<Longrightarrow> a * b < 0 \<Longrightarrow> b < 0"  
  by (simp add: mult_less_0_iff)

lemma real_mono: "(x::nat) \<le> y \<Longrightarrow> real x \<le> real y" 
  by simp

lemma ereal_umst:"y \<ge> 0 \<Longrightarrow> ereal \<gamma> \<le> y - ereal x \<longleftrightarrow> ereal (\<gamma> +  x)  \<le> y" 
  by(cases y) auto

lemma real_mul_assoc:"(a::real) * (b * c) = (a * b) * c"
  by simp

lemma leq_mul_swap: "a*b *d \<le> c*d \<Longrightarrow> (d::real) > 0 \<Longrightarrow> a * b \<le> c"
  by simp

lemma cancel_power_denominator:"b > 0 \<Longrightarrow> (1/(b::real))^(a::nat) * b ^a = 1" 
  by (simp add: power_one_over)

lemma ceil_is_int_iff_range:"(\<lceil> x::real \<rceil> = i) \<longleftrightarrow> (of_int i \<ge> x \<and> x > of_int i - 1)"
  by (auto simp add: algebra_simps) linarith+

lemma enat_less_plus_1_leq:"(x::enat) < (y::enat) + 1 \<Longrightarrow> x \<le> y" 
  by(cases y, all \<open>cases x\<close>)
    (auto simp add: plus_1_eSuc(2))

lemma gt_zero:"x < (y::nat) \<Longrightarrow> 0 < y"
  by auto

lemma ereal_of_real_of_ereal_leq: "x \<ge> 0 \<Longrightarrow> ereal (real_of_ereal x) \<le> x"
  by (simp add: ereal_real)

lemma is_multiple_multiple: "(\<exists> n::nat.  y = (real n) * x) \<Longrightarrow> (\<exists> n::nat. y*2 = (real n) * x )"
  by (metis distrib_left mult.commute mult_2_right of_nat_add)

lemma real_of_plus_distrib: "real (a + b) = real a + real b"
 and real_of_minus_distrib: "a \<ge> b \<Longrightarrow> real (a - b) = real a - real b"
  by auto

lemma finite_sum_less_PInfty: "\<lbrakk>finite A; \<And> x. x \<in> A \<Longrightarrow> f x < PInfty\<rbrakk> \<Longrightarrow> sum f A < PInfty "
  apply(induction A rule: finite_induct, simp)
  apply(subst comm_monoid_add_class.sum.insert_remove) 
  by auto

subsection \<open>Minimum and Maximum\<close>

lemma min_PInfty_cong: 
  "\<lbrakk>x = PInfty; y = z\<rbrakk> \<Longrightarrow> min z x = y"  
  by simp

lemma miny: 
  "(a::real) \<le> min b c \<Longrightarrow> a \<le> b" 
  "(a'::ereal) \<le> min b' c' \<Longrightarrow> a' \<le> b'" 
  by auto

lemma min_PInfty: "min x PInfty = x" 
  by simp

lemma min_same: "\<lbrakk>finite A; A \<noteq> {}; \<And> x. x \<in> A \<Longrightarrow> x = y\<rbrakk> \<Longrightarrow> Min A = y"
  by auto

lemma insert_gtr_Min_insert: "finite A \<Longrightarrow> Min (insert (x::'s::linorder) A) \<le> x"
  by simp

lemma add_inifinites: 
  "\<lbrakk>finite A; A \<noteq> {}; finite B; \<And> x. x \<in> B \<Longrightarrow> x = PInfty\<rbrakk> \<Longrightarrow> Min (A \<union> B) = Min A"
  by (cases "B = {}")(auto simp add: linorder_class.Min_Un min_PInfty_cong)

lemma x_in_xs_Min: "\<lbrakk>x \<in> (set xs); a \<le> Min {y . \<exists> x. x \<in> set xs \<and> y = f x}\<rbrakk> \<Longrightarrow> a \<le> f x"
  proof(induction xs arbitrary: x)
    case Nil
    then show ?case by simp
  next
    case (Cons z xs)
    note cons = this
    have "finite (set xs)" by simp
    hence "finite {y. \<exists>x. x \<in> set xs \<and> y = f x}" 
      using finite_imageI[of "set xs" f] by simp
    then show ?case 
    proof(cases xs)
      case Nil
      hence "{y. \<exists>x. x \<in> set (z # xs) \<and> y = f x} = {f z}" by force
      hence " Min {y. \<exists>x. x \<in> set (z # xs) \<and> y = f x}  = f z" using Min_singleton by simp
      then show ?thesis
        using Cons.prems(1) Cons.prems(2) local.Nil by auto
    next
      case (Cons b list)
      hence "Min ({y. \<exists>x. x \<in> set xs \<and> y = f x} \<union> {f z}) =
                     min (Min {y. \<exists>x. x \<in> set xs \<and> y = f x}) (f z)"
      using  Min_Un[of " {y. \<exists>x. x \<in> set xs \<and> y = f x}" "{f z}"]
      by (metis (mono_tags, lifting) List.finite_set Min_singleton equals0I list.discI list.simps(15)
           \<open>finite {y. \<exists>x. x \<in> set xs \<and> y = f x}\<close> empty_Collect_eq  set_empty)
    have " Min ({y. \<exists>x. x \<in> set (z#xs) \<and> y = f x}) = min (Min {y. \<exists>x. x \<in> set xs \<and> y = f x}) (f z)"
      using set_img_extract[of xs f z]  
           \<open>Min ({y. \<exists>x. x \<in> set xs \<and> y = f x} \<union> {f z}) =
               min (Min {y. \<exists>x. x \<in> set xs \<and> y = f x}) (f z)\<close> by presburger
    hence "a \<le> min (Min {y. \<exists>x. x \<in> set xs \<and> y = f x}) (f z)"
         using cons by presburger
    then show ?thesis
      using cons by auto
  qed 
qed

lemma img_subset_min: "\<lbrakk>finite A; finite C; A\<noteq> {}; A \<subseteq> C\<rbrakk> \<Longrightarrow> Min (f ` A) \<ge> Min (f ` C)"
  by(induction rule: finite.induct) auto 

lemma ereal_Min:
  assumes "A \<noteq> {}" "finite A"
  shows "ereal (Min A) = Min (ereal ` A)"
proof-
  obtain x where x_prop:"x = Min A" "x \<in> A" 
     using assms Min_in[of A] by auto
  obtain y where y_prop:"y = Min (ereal ` A)" "y \<in> (ereal ` A)"
    using assms Min_in[of A] by auto
  have "y \<le> x"
  proof(rule ccontr)
    assume "\<not> y \<le> ereal x "
    hence yx:"y > ereal x" by simp
    have "ereal x \<in> (ereal ` A)" using x_prop by simp
    hence "Min (ereal ` A) \<le> ereal x" 
      by (simp add: assms(2))
    thus False using yx y_prop by simp
  qed
  moreover have "x \<le> y"
    using x_prop y_prop(2) assms(2) by auto
  ultimately show ?thesis using x_prop y_prop by simp
qed

lemma real_of_ereal_of_Min_or_ereal:
  "\<lbrakk>finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow> real_of_ereal (Min (ereal ` A)) = Min A"
  by(auto simp add: ereal_Min[symmetric])
 
lemma  obtain_min:
  assumes "finite A" "A \<noteq> {}"
  obtains m where "m = Min A" "m \<in> A"
  using Min_in assms(1) assms(2) by blast

lemma Min_bigger: 
  "\<lbrakk>finite X; finite Y; X \<noteq> {}; \<And> a b. \<lbrakk>a \<in> X; b \<in> Y\<rbrakk> \<Longrightarrow> b \<ge> a\<rbrakk> \<Longrightarrow> Min X = Min (X \<union> Y)"
  by (metis Min_Un Min_in min_def sup_bot_right)

lemma obtain_Max: "\<lbrakk>finite X; X \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists> x . f x = Max { f x| x. x \<in> X} \<and> x \<in> X"
  apply(induction X rule: finite_induct, simp)
  subgoal for x F
    apply(cases "F = {}")
    apply simp  
    apply(rule exE[of "\<lambda> x. f x = Max {f x |x. x \<in> F}\<and> x \<in> F"])
     apply simp
    subgoal for y 
    apply(subst collapse_to_img)
    apply(subst image_insert)
      apply(subst Max_insert, simp, simp)
      apply(subst (asm) collapse_to_img, simp)+
      apply(cases "(f x) < (Max (f ` F))")
       apply(rule exI[of _ y]) 
       apply simp
      apply(rule exI[of _ "x"])
      by simp
    done
  done

lemma Max_lower_bound: "\<lbrakk>finite X; X \<noteq> {}; x \<in> X; f x > t\<rbrakk> \<Longrightarrow> Max {f x | x. x \<in> X} > t"
  by(subst Max_gr_iff, auto) 

lemma obtain_Max': "\<lbrakk>finite X; X \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists> x \<in> X. f x = Max{f x | x. x \<in> X}"
  using obtain_Max by auto

lemma min_integral: 
  "\<lbrakk>\<exists> n::nat. x = real n; \<exists> n::nat. y = real n\<rbrakk> \<Longrightarrow>  \<exists> n::nat. min x y = real n" 
  by (simp add: min_def)

lemma minE: "\<lbrakk>(a::real) \<le> b \<Longrightarrow> P a; b \<le> a \<Longrightarrow> P b\<rbrakk> \<Longrightarrow> P (min a b)"
  by linarith

lemma P_of_minI: "\<lbrakk>((a::real) \<le> b \<Longrightarrow> P a); (b \<le> a \<Longrightarrow> P b)\<rbrakk> \<Longrightarrow> P (min a b)"
and P_of_minE: 
  "\<lbrakk>P (min a b); \<lbrakk>(a::real) \<le> b; P a\<rbrakk> \<Longrightarrow> Q; \<lbrakk>b \<le> a; P b\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
and P_of_minI_strict1: "\<lbrakk>(a::real) < b \<Longrightarrow> P a; b \<le> a \<Longrightarrow> P b\<rbrakk> \<Longrightarrow> P (min a b)"
and P_of_minE_strict2: 
  "\<lbrakk>P (min a b);\<lbrakk>(a::real) \<le> b; P a\<rbrakk> \<Longrightarrow> Q; \<lbrakk>b < a; P b\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
  by(linarith+)
    (smt (verit, best))+

lemma add_non_min_element_Min:
  "\<lbrakk>finite A; A \<noteq> {}; y \<le> x; y \<in> A; B = insert x A\<rbrakk> \<Longrightarrow> Min B = Min A"
  by (metis Min.boundedE Min.insert_not_elem insert_absorb min_def order_antisym)

subsection \<open>Integrality\<close>

definition "is_integral (x::real) = (\<exists> n::int. x = n)"

lemma is_integralI: "(x::real) = (n::int) \<Longrightarrow> is_integral x"
and is_integralE: "\<lbrakk>is_integral x; \<And> n. (x::real) = (n::int) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp add: is_integral_def)

lemma integral_min: "is_integral x \<Longrightarrow> is_integral y \<Longrightarrow> is_integral (min x y)"
  unfolding is_integral_def
  by (simp add: min_def)

lemma integral_Min: "\<lbrakk>finite M; M \<noteq> {}; \<And> x. x \<in> M \<Longrightarrow> is_integral x\<rbrakk> \<Longrightarrow> is_integral (Min M)"
  by(induction rule: finite.induct)(meson Min_in finite.insertI)+

lemma is_integral_neg: "is_integral x \<Longrightarrow> is_integral (- x)"
  unfolding is_integral_def 
  by (metis of_int_minus)

lemma integral_add: "\<lbrakk>is_integral a; is_integral b\<rbrakk> \<Longrightarrow> is_integral (a+b)"
  unfolding is_integral_def 
  by (metis of_int_add)

lemma integral_sub: "\<lbrakk>is_integral a; is_integral b\<rbrakk> \<Longrightarrow> is_integral (a-b)"
  unfolding is_integral_def 
  by (metis of_int_diff)

lemma is_integral_ceiling: "is_integral x \<Longrightarrow> \<lceil> x \<rceil> = x"
  unfolding is_integral_def by simp

lemma sum_integer_multiple:
  "\<lbrakk>finite E; \<And> e. e\<in> E \<Longrightarrow> \<exists> (n::int). n * (\<gamma>::real) = f e\<rbrakk> \<Longrightarrow> \<exists> (n::int). n *\<gamma> = sum f E"
  apply(induction rule: finite_induct)
   apply(rule exI[of _ 0], simp)
  subgoal for x F
  apply(subst sum.insert, simp, simp)
    apply(rule exE[of "\<lambda> n. real_of_int n * \<gamma> = f x"], fast) 
    subgoal for xn
      apply(rule exE[of "\<lambda> n. real_of_int n * \<gamma> = sum f F"], fast)
      subgoal for En
        apply(rule exI[of _ "xn + En"]) 
        by(auto simp add: algebra_simps)
      done
    done
  done

lemma integer_multiple_add: 
  "\<lbrakk>\<exists> (n::int). x = n*(c::real); \<exists> (n::int). y = n*c\<rbrakk>  \<Longrightarrow> \<exists> (n::int). x +y = n*c" 
  apply(rule exE[of  "\<lambda> n. x = real_of_int n*c"], simp)
  apply(rule exE[of  "\<lambda> n. y = real_of_int n*c"], simp)
  subgoal for xn yn
  by(rule exI[of _ "xn+yn"], auto simp add: algebra_simps)
  done

lemma integer_multiple_sub: 
  "\<lbrakk>\<exists> (n::int). x = n*(c::real); \<exists> (n::int). y = n*c\<rbrakk> \<Longrightarrow> \<exists> (n::int). x - y = n*c" 
  apply(rule exE[of  "\<lambda> n. x = real_of_int n*c"], simp)
  apply(rule exE[of  "\<lambda> n. y = real_of_int n*c"], simp)
  subgoal for xn yn
  by(rule exI[of _ "xn-yn"], auto simp add: algebra_simps)
  done

lemma sum_integral: "\<lbrakk>finite A; \<And> x . x\<in> A \<Longrightarrow> is_integral (f x)\<rbrakk> \<Longrightarrow> is_integral (sum f A)"
  by(induction rule: finite.induct, simp add: is_integral_def) 
    (metis insert_absorb insert_iff is_integral_def of_int_add sum.insert)

subsection \<open>Multiples\<close>

definition "multiples_of (\<epsilon>::real) f X = (\<forall> x \<in> X. \<exists> n::nat. f x = n * \<epsilon>)"

lemma multiples_ofI:
  "(\<And> x. x \<in> X \<Longrightarrow> \<exists> n::nat. f x = n * (\<epsilon>::real)) \<Longrightarrow> multiples_of \<epsilon> f X"
  and multiples_ofE:
  "\<lbrakk>multiples_of (\<epsilon>::real) f X; (\<And> x. x \<in> X \<Longrightarrow> \<exists> n::nat. f x = n * \<epsilon>) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  and multiples_ofD:
  "\<lbrakk>multiples_of (\<epsilon>::real) f X; x \<in> X\<rbrakk> \<Longrightarrow> \<exists> n::nat. f x = n * \<epsilon>"
  by(auto simp add: multiples_of_def)

lemma multiples_of_sum: 
 "\<lbrakk>finite X; multiples_of \<epsilon> f X\<rbrakk> \<Longrightarrow> multiples_of \<epsilon> id {sum f X}"
proof(induction X rule: finite_induct)
  case empty
  then show ?case 
    by(auto simp add: multiples_of_def)
next
  case (insert x X)
  obtain n where "(n::nat)*\<epsilon> = sum f X"
    using insert(3,4)
    by(force simp add: multiples_of_def)
  moreover obtain n' where "(n'::nat) * \<epsilon> = f x"
    using insert (4)
    by(force simp add: multiples_of_def)
  ultimately have "(n+n') *\<epsilon> = sum f (insert x X)"
    using insert(2,1)
    by(auto simp add: comm_monoid_add_class.sum.insert[simplified] algebra_simps)
  thus ?case 
    by(auto simp add: multiples_of_def intro!: exI[of _ "n + n'"])
qed

subsection \<open>Calculations\<close>

lemma nat_int_exchg:
 "int (nat \<lceil>log 2 (max 1 (5 / 10 * X))\<rceil>) = \<lceil>log 2 (max 1 (5 / 10 * X))\<rceil>"
  apply(rule nat_0_le)
  apply(subst zero_le_ceiling)
  apply(subst max_def)
  apply(cases "1 \<le> (5 / 10 * X)")
  apply(subst if_P, simp)
  using zero_le_log_cancel_iff[of  2 "5 / 10 * X"] apply argo
  apply simp
  done

lemma same8_2:"(8::real) = 2*2*2" and  same4_2:"(4::real) = 2*2" 
  by simp+

lemma log283: "log 2 8 =3"
 by(subst same8_2, subst log_mult, simp+)
   (subst same4_2, subst log_mult, simp+)

subsection \<open>Abstraction of Real Maps\<close>

definition "abstract_real_map mp x = (case mp x of None \<Rightarrow> 0 | Some y \<Rightarrow> y)"

lemma abstract_real_map_empty: "abstract_real_map (\<lambda> _ . None) = (\<lambda> _ . 0)"
  by(auto simp add: abstract_real_map_def)

lemma abstract_real_map_some: "mp x = Some y \<Longrightarrow> abstract_real_map mp x = y"
  by(auto simp add: abstract_real_map_def)

lemma abstract_real_map_cong: "mp x = mp' x \<Longrightarrow> abstract_real_map mp x = abstract_real_map mp' x"
  by(auto simp add: abstract_real_map_def)

lemma abstract_real_map_none: "mp x = None \<Longrightarrow> abstract_real_map mp x = 0"
  by(auto simp add: abstract_real_map_def)

lemma abstract_real_map_not_zeroE: 
  "\<lbrakk>abstract_real_map mp x \<noteq> 0; \<And> y. \<lbrakk>mp x = Some y; y \<noteq> 0\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(cases "mp x")(auto simp add: abstract_real_map_def)

lemma abstract_real_map_outside_dom: "x \<notin> dom mp \<Longrightarrow> abstract_real_map mp x = 0"
  by(cases "mp x")(auto simp add: abstract_real_map_def dom_if)

lemma abstract_real_map_in_dom_the: "x \<in> dom mp \<Longrightarrow> abstract_real_map mp x = the (mp x)"
  by(cases "mp x")(auto simp add: abstract_real_map_def dom_if)

lemma abstract_real_map_fun_upd:
  "abstract_real_map (fun_upd f x (Some y)) = (\<lambda> z. if z = x then y else abstract_real_map f z)"
  by(auto simp add: abstract_real_map_def)

definition "abstract_bool_map mp = (\<lambda> opt. (case mp opt of None \<Rightarrow> False
                                | Some x \<Rightarrow> x))"

lemma abstract_bool_map_None: "mp x = None \<Longrightarrow> abstract_bool_map mp x = False"
and abstract_bool_map_Some: "mp x = Some b \<Longrightarrow> abstract_bool_map mp x = b"
and abstract_bool_map_upd: "abstract_bool_map (mp(x:=Some bb)) = 
                        (\<lambda> y. if x = y then bb else abstract_bool_map mp y)" 
  by(auto simp add: abstract_bool_map_def)
end