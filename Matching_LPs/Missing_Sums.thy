theory Missing_Sums
  imports  Linear_Inequalities.Integer_Hull
    Jordan_Normal_Form.Missing_VectorSpace
begin

context gram_schmidt
begin

lemma nonneg_each_smaller_than_sum:
  fixes c :: "'b \<Rightarrow> 'a :: trivial_conjugatable_linordered_field" 
  assumes "finite S" 
  assumes "\<forall>i \<in> S. c i \<ge> 0" 
  shows "\<forall>i \<in> S. c i \<le> sum c S" 
  using member_le_sum[of _ S c]  assms by auto

lemma nonneg_sum_range_each_le:
  fixes f :: "nat \<Rightarrow> 'a"
  assumes "\<forall>i < m. f i \<ge> 0"
  shows "\<forall>i < m. f i \<le> sum f {0..<m}"
  using nonneg_each_smaller_than_sum[of "{0..<m}" f] 
  by (meson assms atLeastLessThan_iff finite_atLeastLessThan zero_le)

lemma sum_range_divided_at_zero:
  fixes f :: "nat \<Rightarrow> 'a :: trivial_conjugatable_linordered_field"
  shows "f 0 + sum f {1..<k +1} = sum f {0..<k+1}" 
  by (auto simp: sum.atLeast_Suc_lessThan)

lemma sumlist_map_carr:
  assumes "f : set A \<rightarrow> carrier_vec n"
  shows "sumlist (map f A) \<in> carrier_vec n" 
proof -
  have "set (map f A) \<subseteq> carrier_vec  n"
    using  Pi_mem 
    using assms by auto
  then show ?thesis 
    using M.sumlist_carrier by blast
qed

lemma sumlist_map_mult:
  assumes "f : set xs \<rightarrow> carrier_vec n"
  assumes "k \<noteq> 0"
  shows "sumlist (map f xs) =  k \<cdot>\<^sub>v sumlist (map (\<lambda>i. (1/k)\<cdot>\<^sub>v(f i)) xs)"
  using assms(1-2)
proof(induct xs)
  case (Cons a xs)
  have f_carr: "f \<in> set xs \<rightarrow> carrier_vec n" 
    using Cons.prems(1) by auto
  have " k \<cdot>\<^sub>v ((\<lambda>i. 1 / k \<cdot>\<^sub>v f i) a + sumlist (map (\<lambda>i. 1 / k \<cdot>\<^sub>v f i) xs)) =
     k \<cdot>\<^sub>v ((\<lambda>i. 1 / k \<cdot>\<^sub>v f i) a) + k \<cdot>\<^sub>v (sumlist (map (\<lambda>i. 1 / k \<cdot>\<^sub>v f i) xs))" 
    apply(rule smult_add_distrib_vec[of _ n])
     apply(auto) 
    using Cons.prems(1)
     apply(auto simp: Pi_mem)
    apply (rule sumlist_map_carr) 
    using f_carr by blast
  then show ?case 
    by (simp add: Cons.hyps assms(2) f_carr smult_smult_assoc)
qed simp

lemma lincomb_in_integer_set:
  assumes "set xs \<subseteq> carrier_vec n"
  assumes "set xs \<subseteq> P \<inter> \<int>\<^sub>v"
  assumes "P = integer_hull P"
  assumes "sum c {0..<length xs} = 1"
  assumes "(\<forall>i<length xs. 0 \<le> c i) " 
  shows "lincomb_list c xs \<in> P" 
proof -
  have "convex_lincomb_list c xs (lincomb_list c xs)" 
    unfolding convex_lincomb_list_def nonneg_lincomb_list_def 
    using assms(5) assms(4) by blast
  have "convex_hull (set xs) = convex_hull_list xs" 
    using assms(1) finite_convex_hull_iff_convex_hull_list by auto
  then have "lincomb_list c xs \<in> convex_hull (set xs)" 
    unfolding convex_hull_list_def 
    using \<open>convex_lincomb_list c xs (lincomb_list c xs)\<close> by blast
  have "convex_hull (set xs) \<subseteq> convex_hull (P \<inter> \<int>\<^sub>v)" 
    using assms(2) convex_hull_mono by presburger
  then show "lincomb_list c xs \<in> P" 
    using \<open>lincomb_list c xs \<in> convex_hull (set xs)\<close> assms(3) integer_hull_def by blast
qed

lemma sumlist_swap_upd_same:
  assumes "set xs \<subseteq> carrier_vec n"
  assumes "i < length xs"
  assumes "j < length xs"
  shows "sumlist (xs[i:= xs ! j, j:= xs ! i]) = sumlist xs" 
  by (auto simp: sumlist_as_summset assms perm_swap)

lemma sumlist_swap_upd_same':
  assumes "set xs \<subseteq> carrier_vec n"
  assumes "i < length xs"
  assumes "j < length xs"
  shows " sumlist xs = sumlist (xs[i:= xs ! j, j:= xs ! i])" 
  by (auto simp: sumlist_as_summset assms perm_swap)

lemma add_zero_to_range_list:
  assumes "m > 0" 
  shows "0 # [1..< m] = [0..<m]"
  using upt_eq_Cons_conv[of 0 m 0 "[1..< m]"]
  by (auto simp: assms)

lemma map_swap_fun_same:
  fixes xs :: "'a vec list" 
  assumes "i < length xs"
  assumes "j < length xs"
  shows "(map (f(i:=f j, j := f i))[0..<length (xs[i := xs ! j, j := xs ! i])]) =
      (map f [0..<length xs])[i := (map f [0..<length xs]) ! j, j := (map f [0..<length xs]) ! i]"
  by (simp add: assms  map_nth_eq_conv)

lemma swap_fun_nonneg:
  assumes "i < length xs"
  assumes "j < length xs"
  assumes "\<forall>ia < length xs. 0 \<le> f ia" 
  shows "\<forall>ia < length xs. 0 \<le> (f(i := f j, j := f i)) ia"
  using assms by auto

lemma swap_zero_fun_nonneg:
  assumes "j < length xs"
  assumes "\<forall>ia < length xs. 0 \<le> f ia" 
  shows "\<forall>ia < length xs. 0 \<le> (f(0 := f j, j := f 0)) ia"
  using assms swap_fun_nonneg 
  by (metis bot_nat_0.not_eq_extremum less_nat_zero_code)

lemma sum_of_swap_fun_eq:
  assumes "finite A"
  assumes "i \<in> A"
  assumes "j \<in> A"
  shows "sum (f(i := f j, j := f i)) A = sum f A"
proof -
  let ?g = "(f(i := f j, j := f i))" 
  have "{i, j} \<subseteq> A" 
    using assms(2) assms(3) by blast
  have sum_union_f: "sum f A = sum f (A - {i, j}) + sum f {i, j}"
    by (intro sum.subset_diff[of "{i, j}" A f] assms(1) `{i, j} \<subseteq> A` )
  have sum_union_g: "sum ?g A = sum ?g (A - {i, j}) + sum ?g {i, j}"
    by (intro sum.subset_diff[of "{i, j}" A ?g] assms(1) `{i, j} \<subseteq> A` )
  show "sum (f(i := f j, j := f i)) A = sum f A"
    apply(simp only:sum_union_f sum_union_g)
    by (cases "i = j"; auto simp: add.commute)
qed   

lemma zero_vec_is_int:
  shows "0\<^sub>v n \<in>  \<int>\<^sub>v" 
  unfolding Ints_vec_def zero_vec_def 
  by fastforce

lemma sum_int_is_int:
  assumes "a \<in> carrier_vec n"
  assumes "b \<in> carrier_vec n"
  assumes "a \<in> \<int>\<^sub>v"
  assumes "b \<in> \<int>\<^sub>v"
  shows "a + b \<in> \<int>\<^sub>v" 
  using assms unfolding Ints_vec_def by force

lemma diff_int_is_int:
  assumes "a \<in> carrier_vec n"
  assumes "b \<in> carrier_vec n"
  assumes "a \<in> \<int>\<^sub>v"
  assumes "b \<in> \<int>\<^sub>v"
  shows "a - b \<in> \<int>\<^sub>v" 
  using assms unfolding Ints_vec_def by force

lemma sumlist_map_append:
  assumes "f : {0..<Suc m} \<rightarrow> carrier_vec n"
  shows "sumlist (map f [0..<Suc m]) = sumlist (map f [0..<m]) + f m"
  using sumlist_snoc[of "(map f [0..<m])" "f m"] assms 
  by force

lemma sumlist_of_ints_is_int:
  assumes "f : {0..<m} \<rightarrow> carrier_vec n"
  assumes "\<forall>j < m. f  j \<in> \<int>\<^sub>v"
  shows "sumlist (map f [0..<m]) \<in> \<int>\<^sub>v"
  using assms 
proof(induct m)
  case (Suc m)
  have f_carr:"f \<in> {0..<m} \<rightarrow> carrier_vec n" 
    using Suc.prems(1) by auto
  have sum_carr:"sumlist (map f [0..<m]) \<in> carrier_vec n" 
    by  (auto simp: sumlist_map_carr f_carr)
  show ?case
    apply (simp only: sumlist_map_append[of f m] Suc.prems(1))
    apply(intro sum_int_is_int)
    using sum_carr  apply blast
    using Suc.prems(1) apply auto
    using Suc.hyps f_carr  Suc.prems(2) less_Suc_eq apply presburger
    by (simp add: Suc.prems(2))
qed (simp add: zero_vec_is_int)

lemma sum_mono_nonneg:
  fixes f :: "'b \<Rightarrow> 'a"
  assumes "finite S"
  assumes "\<forall>i \<in> S. f i \<ge> 0" 
  assumes "F \<subseteq> S"
  shows "sum f F \<le> sum f S" 
  using sum_mono2[of S F f] assms DiffD1 
  by blast

lemma sum_eq_one_elem_other_zero:
  fixes f :: "'b \<Rightarrow> 'a"
  assumes "finite S" 
  assumes "\<forall>i \<in> S. f i \<ge> 0" 
  assumes "i \<in> S"
  assumes "f i = sum f S"
  assumes "j \<in> S \<and> j \<noteq> i"
  shows "f j = 0"
proof(rule ccontr)
  assume "f j \<noteq> 0" 
  then have "f j > 0" 
    using assms(2) assms(5) dual_order.order_iff_strict by blast
  have "sum f {i, j} \<le> sum f S" using sum_mono_nonneg[of S f "{i, j}"] 
    using assms(1) assms(2) assms(3) assms(5) by fastforce
  then show False using assms `f j > 0`
    by force
qed

lemma int_mult_int_vec:
  assumes "a \<in> \<int>\<^sub>v" 
  assumes "k \<in> \<int>"
  shows "k \<cdot>\<^sub>v a \<in> \<int>\<^sub>v" 
  using assms(1) assms(2) indexed_Ints_vec_UNIV smult_indexed_Ints_vec by blast

lemma convex_lincom_int:
  assumes "convex_lincomb_list c L x"
  assumes "set L \<subseteq> \<int>\<^sub>v"  
  assumes "set L \<subseteq> carrier_vec n"
  assumes "\<forall>i < length L. c i \<in> \<int>"
  shows "x \<in> \<int>\<^sub>v"
proof -
  have "\<forall>j < length L. (\<lambda>i. c i \<cdot>\<^sub>v L ! i)  j \<in> \<int>\<^sub>v" 
    using assms(2) assms(4) nth_mem int_mult_int_vec by blast
  then have "sumlist (map (\<lambda>i. c i \<cdot>\<^sub>v L ! i) [0..<length L]) \<in>  \<int>\<^sub>v" 
    using sumlist_of_ints_is_int[of "(\<lambda>i. c i \<cdot>\<^sub>v L ! i)" "length L"] assms(3) by fastforce
  then show "x \<in> \<int>\<^sub>v" 
    using assms(1) 
    unfolding convex_lincomb_list_def lincomb_list_def nonneg_lincomb_list_def
    by blast
qed

lemma convex_lincomb_less_1_coeff:
  assumes "convex_lincomb_list c L x"
  assumes "x \<notin> \<int>\<^sub>v"
  assumes "set L \<subseteq> \<int>\<^sub>v"  
  assumes "set L \<subseteq> carrier_vec n" 
  assumes "i < length L" 
  shows "c i < 1" 
proof -
  have fin:"finite (set L)" 
    by simp
  have nonneg_sum_1: "(\<forall> i < length L. c i \<ge> 0) \<and> sum c {0..<length L} = 1" 
    using assms(1) convex_lincomb_list_def nonneg_lincomb_list_def by blast
  show "c i < 1" 
  proof(rule ccontr)
    assume " \<not> c i < 1" 
    then have "c i = 1"
      using  nonneg_sum_range_each_le[of "length L" c] 
        assms(5) nonneg_sum_1 order_le_imp_less_or_eq 
      by metis
    have "\<forall>j < length L. i \<noteq> j \<longrightarrow> c j = 0" 
      using sum_eq_one_elem_other_zero[of "{0..<length L}" c i] 
      by (auto simp: \<open>c i = 1\<close> assms(5) nonneg_sum_1) 
    then have "x \<in> \<int>\<^sub>v" using convex_lincom_int[of c L x] 
      by (metis Ints_0 Ints_1 \<open>c i = 1\<close> assms(1) assms(3) assms(4))
    then show False 
      by (simp add: assms(2))
  qed
qed

lemma map_shift_by_one: 
  "(map (\<lambda>i. f i \<cdot>\<^sub>v (a # ax) ! i) [1..<length (a # ax)]) = 
    (map (\<lambda> i. (f (i+1)) \<cdot>\<^sub>v ax ! i) [0..<length ax])"
proof -
  have append_shift:"\<forall> i < length ax. ([Suc 0..<length ax] @ [length ax]) ! i = i + 1" 
    using nth_upt[of 1 _ "length ax + 1"] by auto
  have "(map (\<lambda> i. (f (i+1) \<cdot>\<^sub>v (a # ax) ! (i+1))) [0..<length ax]) = 
    (map (\<lambda> i. (f i \<cdot>\<^sub>v (a # ax) ! i)) [1..<length ax + 1])"
    apply (auto simp: map_eq_conv' append_shift) 
    by (metis Suc_leI length_greater_0_conv)
  then show ?thesis
    by auto
qed

lemma length_upt_same:
  shows "length (xs[0 := xs ! i, i := xs ! 0]) = length xs"
  by auto

lemma lincomb_map_set_carrier:
  assumes "set Wsl \<subseteq> carrier_vec n"
  shows "set (map (\<lambda>ia. c ia \<cdot>\<^sub>v Wsl ! ia) [0..<length Wsl]) \<subseteq> carrier_vec n"
proof
  fix z
  assume "z \<in> set (map (\<lambda>ia. c ia \<cdot>\<^sub>v Wsl ! ia) [0..<length Wsl])"
  then obtain j where "j <length Wsl \<and> z = c j \<cdot>\<^sub>v Wsl ! j" 
    by auto
  then show "z \<in> carrier_vec n" 
    using assms(1) nth_mem 
    using smult_carrier_vec by blast
qed

lemma sumlist_upt_same:
  assumes "set Wsl \<subseteq> carrier_vec n"
  assumes "i < length Wsl"
  shows "(M.sumlist (map (\<lambda>ia. (c(0 := c i, i := c 0)) ia \<cdot>\<^sub>v Wsl[0 := Wsl ! i, i := Wsl ! 0] ! ia)
         [0..<length (Wsl[0 := Wsl ! i, i := Wsl ! 0])])) = 
          (M.sumlist (map (\<lambda>ia. c ia \<cdot>\<^sub>v Wsl ! ia) [0..<length Wsl]))"
proof -
  have 0: "0 < length Wsl" 
    using assms(2) by linarith
  have 1: "(\<lambda>ia. c ia \<cdot>\<^sub>v Wsl ! ia)(0 := c i \<cdot>\<^sub>v Wsl ! i, i := c 0 \<cdot>\<^sub>v Wsl ! 0) = 
            (\<lambda>ia. (c(0 := c i, i := c 0)) ia \<cdot>\<^sub>v Wsl[0 := Wsl ! i, i := Wsl ! 0] ! ia)" 
    using \<open>i < length Wsl\<close>  nth_mem 0 length_pos_if_in_set  by fastforce
  show ?thesis 
    apply (insert sumlist_swap_upd_same[of "(map (\<lambda>ia. c ia \<cdot>\<^sub>v Wsl ! ia) [0..<length Wsl])" 0 i]) 
    apply (insert map_swap_fun_same[of 0 Wsl i "(\<lambda>ia. c ia \<cdot>\<^sub>v Wsl ! ia)"] )
    apply (simp only: assms lincomb_map_set_carrier[of Wsl c] 1 0 length_map less_nat_zero_code) 
    using assms(2) by fastforce
qed

lemma convex_lincomb_list_swap:
  assumes "convex_lincomb_list c Wsl x"
  assumes "set Wsl \<subseteq> carrier_vec n"
  assumes "i < length Wsl"
  shows "convex_lincomb_list (c(0 := c i, i := c 0)) (Wsl[0 := Wsl ! i, i := Wsl ! 0]) x" 
proof -
  have cll:"(lincomb_list c Wsl = x \<and> (\<forall>i<length Wsl. 0 \<le> c i)) \<and> sum c {0..<length Wsl} = 1" 
    using assms unfolding convex_lincomb_list_def nonneg_lincomb_list_def by auto
  have x_sumlist: "sumlist (map (\<lambda>ia. c ia \<cdot>\<^sub>v Wsl ! ia) [0..<length Wsl]) = x" 
    using cll unfolding lincomb_list_def by auto
  show ?thesis
    unfolding convex_lincomb_list_def  nonneg_lincomb_list_def lincomb_list_def
    apply(simp only: length_upt_same)
    apply(intro conjI)  
    using sumlist_upt_same[of Wsl i c] apply (simp add: x_sumlist assms(2) assms(3))
    using swap_zero_fun_nonneg[of i Wsl c] assms(3) cll  apply presburger
    using sum_of_swap_fun_eq[of "{0..<length Wsl}" 0 i c] 
    by (metis assms(3) atLeastLessThan_iff cll linorder_le_less_linear 
        not_less_zero sum.infinite zero_less_iff_neq_zero)
qed

lemma convex_lincomb_in_convex_hull_list:
  assumes "set L \<subseteq> carrier_vec n"
  assumes "convex_lincomb c' (set L) x"
  shows "x \<in> convex_hull_list L"
proof -
  have "convex_hull_list L = convex_hull (set L)" 
    by (simp add: assms(1) finite_convex_hull_iff_convex_hull_list)
  then show "x \<in> convex_hull_list L"  
    using assms(2) convex_hull_def 
    by blast
qed

lemma obt_convect_lincomb_list:
  assumes "set L \<subseteq> carrier_vec n"
  assumes "convex_lincomb c' (set L) x"
  obtains c where "convex_lincomb_list c L x" 
  using gram_schmidt.convex_hull_list_def 
  using that convex_lincomb_in_convex_hull_list assms 
  by blast

lemma sum_except_one:
  fixes f :: "nat \<Rightarrow> 'a"
  assumes "sum f {0..<length (a#ax)} = 1"
  assumes "f 0 \<noteq> 1" 
  shows "(\<Sum>i = 0..<length ax. f (i + 1) / (1 - f 0)) = 1"
proof -
  let ?g = "(\<lambda>i. f (i + 1) / (1 - f 0))" 
  have "length (a # ax) = 1 + length ax" 
    by simp
  then have 0:"sum (\<lambda>i. f (i + 1)) {0..<length ax} = sum (\<lambda>i. f i) {1..<length (a # ax)}"
    by (metis Nat.add_0_right  add.commute sum.shift_bounds_nat_ivl)
  then have "(1/(1 - f 0)) * sum (\<lambda>i. f (i + 1)) {0..<length ax} =
              (1/(1 - f 0)) * sum (\<lambda>i. f i) {1..<length (a # ax)}" by simp
  have 1:"sum ?g {0..<length ax} = (1/(1 - f 0)) * sum (\<lambda>i. f (i + 1)) {0..<length ax}"  
    using mult_hom.hom_sum[of "(1/(1 - f 0))" "(\<lambda>i. f (i + 1))" "{0..<length ax}"]
    by simp
  then have "f 0 + sum f {1..<length (a#ax)} = sum f {0..<length (a#ax)}" 
    by (metis \<open>length (a # ax) = 1 + length ax\<close> add.commute sum_range_divided_at_zero)
  then have "f 0 + sum f {1..<length (a#ax)} = 1" 
    by (metis  \<open>sum f {0..<length (a#ax)} = 1\<close>)
  then have 2:"sum (\<lambda>i. f (i + 1)) {0..<length ax} = 1 - f 0" 
    using 0 by linarith 
  then have "(1/(1 - f 0)) * (1 - f 0) =  1" using `f 0 \<noteq> 1` 
    by (metis nonzero_eq_divide_eq r_right_minus_eq)
  then show ?thesis 
    using 1 2 by presburger
qed

lemma sumlist_distr_zero:
  assumes "m > 0"
  shows "sumlist (map f [0..<m]) = f 0 + sumlist (map f [1..<m])" 
  by (metis M.sumlist_Cons add_zero_to_range_list assms list.simps(9))

lemma sumlist_as_lincomb_two_elems:
  assumes "c 0 \<noteq> 1"
  assumes "set (a#ax) \<subseteq> carrier_vec n" 
  shows " sumlist (map (\<lambda>i. c i \<cdot>\<^sub>v (a # ax) ! i) [0..<length (a#ax)]) =
    c 0 \<cdot>\<^sub>v a + (1 - c 0) \<cdot>\<^sub>v sumlist ( map (\<lambda>i. (c (i + 1) / (1 - c 0)) \<cdot>\<^sub>v ax ! i) [0..<length ax])"
proof -
  let ?f = "(\<lambda>i. c i \<cdot>\<^sub>v (a # ax) ! i)"  
  have "?f \<in> set [1..<length (a # ax)] \<rightarrow> carrier_vec n" 
    using lincomb_map_set_carrier[of "a#ax" c] assms set_upt smult_closed subsetD by fastforce
  then have " M.sumlist (map ?f [1..<length (a # ax)]) =
    (1 - c 0) \<cdot>\<^sub>v M.sumlist (map (\<lambda>i. 1 / (1 - c 0) \<cdot>\<^sub>v ?f i) [1..<length (a # ax)])"
    using sumlist_map_mult[of ?f " [1..<length (a # ax)]" "(1 - c 0)"] `c 0 \<noteq> 1` 
    by linarith
  moreover have "(\<lambda>i. 1 / (1 - c 0) \<cdot>\<^sub>v ?f i) =  (\<lambda>i. (c i / (1 - c 0)) \<cdot>\<^sub>v (a # ax) ! i)"
    using `c 0 \<noteq> 1` 
    by fastforce  
  moreover have "sumlist ( map ?f [1..<length (a # ax)]) = 
    (1 - c 0) \<cdot>\<^sub>v sumlist ( map (\<lambda>i. (c i / (1 - c 0)) \<cdot>\<^sub>v (a # ax) ! i) [1..<length (a # ax)])" 
    using `c 0 \<noteq> 1` 
    using calculation(1) calculation(2) by presburger
  moreover have "sumlist ( map (\<lambda>i. (c i / (1 - c 0)) \<cdot>\<^sub>v (a # ax) ! i) [1..<length (a # ax)]) = 
      sumlist ( map (\<lambda>i. (c (i + 1) / (1 - c 0)) \<cdot>\<^sub>v ax ! i) [0..<length ax])" 
    using map_shift_by_one[of "\<lambda>i. (c i / (1 - c 0))" a ax]
    by argo
  ultimately show ?thesis 
    using  sumlist_distr_zero[of "length (a#ax)" ?f] 
    by simp
qed

lemma elem_int_hull_lincomb_list:
  fixes x :: "'a :: trivial_conjugatable_linordered_field vec"
  assumes "P \<subseteq> carrier_vec n"
  assumes "P = integer_hull P"
  assumes"x \<in> P" 
  assumes "x \<notin> \<int>\<^sub>v"
  obtains Wsl c where "convex_lincomb_list c Wsl x \<and> c 0 \<noteq> 0 \<and> (set Wsl) \<subseteq> P \<inter> \<int>\<^sub>v \<and> Wsl \<noteq> []"
proof -
obtain Ws c' where Ws_c':"finite Ws" "Ws \<subseteq> P \<inter> \<int>\<^sub>v" "convex_lincomb c' Ws x"
  using assms(2) unfolding integer_hull_def
        by (smt (verit, ccfv_SIG) IntD1 \<open>x \<in> P\<close> gram_schmidt.convex_hull_def mem_Collect_eq)
  have Ws_subs: "Ws \<subseteq> carrier_vec n" 
    by (meson Int_subset_iff Ws_c'(2) assms(1) dual_order.trans)
  have "x \<in> convex_hull Ws" 
    using Ws_c' convex_hull_def by blast
  obtain Wsl where Wsl:"set Wsl =  Ws "
    by (meson Ws_c'(1) finite_list)
  then obtain c where c: "convex_lincomb_list c Wsl x" 
    using Ws_subs Ws_c' obt_convect_lincomb_list by blast
  then obtain i where i: "i < length Wsl \<and> c i \<noteq> 0" 
    by (metis Ints_0 Ws_c'(2) Ws_subs Wsl assms(4) convex_lincom_int inf.boundedE)
  have Ws_swap: "Ws = set (Wsl[0:= Wsl ! i, i:=Wsl ! 0])"
    by (metis i Wsl length_pos_if_in_set nth_mem set_swap)
 have "Ws \<noteq> {}" 
    using \<open>x \<in> convex_hull Ws\<close> convex_hull_empty(2) by blast
 then have "Wsl \<noteq> []" 
    using \<open>Ws \<noteq> {}\<close> Wsl by fastforce
  then show ?thesis
    using convex_lincomb_list_swap[of c Wsl x i] Ws_c'
    by (metis Ws_swap Ws_subs Wsl c fun_upd_other fun_upd_same i list_update_nonempty that)
qed

lemma elem_of_P_is_lin_comb:
  fixes x :: "'a :: trivial_conjugatable_linordered_field vec"
  assumes "P \<subseteq> carrier_vec n"
  assumes "P = integer_hull P"
  assumes"x \<in> P" 
  assumes "x \<notin> \<int>\<^sub>v"
  obtains y z l where "y \<in> P \<inter> \<int>\<^sub>v" "z \<in> P" "x = l \<cdot>\<^sub>v y + (1 - l) \<cdot>\<^sub>v z" "l > 0 \<and> l < 1"
proof -
  obtain Wsl c where Wc: "convex_lincomb_list c Wsl x \<and> c 0 \<noteq> 0 \<and> (set Wsl) \<subseteq> P \<inter> \<int>\<^sub>v \<and> Wsl \<noteq> []"
    using elem_int_hull_lincomb_list 
    by (metis assms)
  then have lin_comb_x: 
    "lincomb_list c Wsl = x \<and> (\<forall> i < length Wsl. c i \<ge> 0) \<and> sum c {0..<length Wsl} = 1"
    using convex_lincomb_list_def nonneg_lincomb_list_def Wc by blast
  have "sum c {0..<length Wsl} = 1" 
    using lin_comb_x by blast
  obtain a ax where "Wsl = a # ax" 
    by (meson Wc neq_Nil_conv)
  then have " \<forall>i<length Wsl. c i < 1"
    using convex_lincomb_less_1_coeff[of c Wsl x] using Wc assms(1) 
    using assms(4) by blast
  then have "c 0 \<noteq> 1" 
    by (metis Wc length_greater_0_conv less_numeral_extra(4))
  let ?f = "(\<lambda>i. c (i + 1) / (1 - c 0))" 
  have "sum ?f {0..<length ax} = 1" using sum_except_one 
    by (metis \<open>Wsl = a # ax\<close> \<open>c 0 \<noteq> 1\<close> \<open>sum c {0..<length Wsl} = 1\<close>)
  have "set ax \<subseteq> set Wsl" 
    using \<open>Wsl = a # ax\<close> by auto
  then have "set ax \<subseteq> carrier_vec n" using assms(1) Wc
    by blast
  have " set ax \<subseteq> P \<inter> \<int>\<^sub>v" 
    using Wc \<open>set ax \<subseteq> set Wsl\<close>   by blast
  have "(\<forall> i < length Wsl. c i \<ge> 0)" 
    using lin_comb_x by presburger
  have "(1 - c 0) > 0" using nonneg_sum_range_each_le[of "length Wsl" c] 
    by (meson Wc \<open>\<forall>i<length Wsl. c i < 1\<close> diff_gt_0_iff_gt gr_zeroI length_0_conv)
  then have " \<forall>i<length ax. 0 \<le> ?f i"  
    by (simp add: \<open>Wsl = a # ax\<close> \<open>\<forall>i<length Wsl. 0 \<le> c i\<close>)
  have 1:"sumlist (map (\<lambda>i. ?f i \<cdot>\<^sub>v ax ! i) [0..<length ax]) \<in> P" 
    using lincomb_in_integer_set[of ax P ?f] `sum ?f {0..<length ax} = 1`  
    using \<open>\<forall>i<length ax. 0 \<le> ?f i\<close> \<open>set ax \<subseteq> P \<inter> \<int>\<^sub>v\<close> \<open>set ax \<subseteq> carrier_vec n\<close> assms(2)
    unfolding lincomb_list_def 
    by blast
  have 2:"x = c 0 \<cdot>\<^sub>v a + (1 - c 0) \<cdot>\<^sub>v sumlist ( map (\<lambda>i. ?f i \<cdot>\<^sub>v ax ! i) [0..<length ax])"
    using sumlist_as_lincomb_two_elems[of c a ax]  \<open>Wsl = a # ax\<close> \<open>c 0 \<noteq> 1\<close>
      lin_comb_x assms(1) Wc by (auto simp: lincomb_list_def)
  have 3:"a \<in> P \<inter> \<int>\<^sub>v" 
    using \<open>Wsl = a # ax\<close> Wc  by force
  have 4:"c 0 > 0" 
    by (metis Wc \<open>\<forall>i<length Wsl. 0 \<le> c i\<close> length_greater_0_conv order_le_imp_less_or_eq)
  have 5:"c 0 \<le> 1" using member_le_sum[of 0 "{0..<length Wsl}" c] 
    using \<open>Wsl = a # ax\<close> lin_comb_x by force
  then show ?thesis using 1 2 3 4 5
    using that 
    using \<open>c 0 \<noteq> 1\<close> by force
qed

lemma lincomb_then_lincomb_list:
  assumes "set L \<subseteq> carrier_vec n"
  assumes "x = lincomb c' (set L)"
  obtains c where "x = lincomb_list c L" 
  using assms(1) assms(2) lincomb_as_lincomb_list by blast

end
end