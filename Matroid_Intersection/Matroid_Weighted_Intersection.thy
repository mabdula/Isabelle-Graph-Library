theory Matroid_Weighted_Intersection
  imports Matroid_Intersection
begin

section \<open>Theory for Weighted Matroid Intersection\<close>

text \<open>This file contains theory for weighted matroid intersection (Korte\&Vygen, Section 13.7).
It formalises the fact that splitting the weight into two functions, each optimal in one of the
two matroids for a fixed cardinality, yields an optimum common independent set of that cardinality
(the implication (13.5) $\Rightarrow$ (13.4)), together with Frank's augmentation lemma
(Lemma 13.35), the weighted analogue of Lemma 13.27.\<close>

locale weighted_double_matroid = double_matroid carrier indep1 indep2
  for carrier :: "'a set" and indep1 indep2 +
  fixes c :: "'a \<Rightarrow> 'b :: linordered_ab_group_add"
begin

text \<open>A set is optimum in the intersection if it is common independent and has maximum weight
among all common independent sets. This is the object the weighted matroid intersection algorithm
ultimately computes.\<close>

definition "is_opt X \<longleftrightarrow> indep1 X \<and> indep2 X \<and> (\<forall> Y. indep1 Y \<and> indep2 Y \<longrightarrow> sum c Y \<le> sum c X)"

text \<open>The implication (13.5) $\Rightarrow$ (13.4): if the weight splits as \<open>c = c1 + c2\<close> and \<open>X\<close> is a
common independent set that is simultaneously \<open>c1\<close>-maximum in the first and \<open>c2\<close>-maximum in the
second matroid among the sets of its own cardinality, then \<open>X\<close> is \<open>c\<close>-maximum among all common
independent sets of that cardinality.\<close>

lemma opt_in_matroids_imp_opt_in_intersection:
  fixes c1 c2 :: "'a \<Rightarrow> 'b"
  assumes "\<And> e. e \<in> carrier \<Longrightarrow> c e = c1 e + c2 e"
    "indep1 X" "indep2 X" "k = card X"
    "\<And> Y. \<lbrakk>indep1 Y; card Y = k\<rbrakk> \<Longrightarrow> sum c1 Y \<le> sum c1 X"
    "\<And> Y. \<lbrakk>indep2 Y; card Y = k\<rbrakk> \<Longrightarrow> sum c2 Y \<le> sum c2 X"
    "indep1 Z" "indep2 Z" "card Z = k"
  shows "sum c Z \<le> sum c X"
proof-
  have Z_carrier: "Z \<subseteq> carrier" using assms(7) matroid1.indep_subset_carrier by simp
  have X_carrier: "X \<subseteq> carrier" using assms(2) matroid1.indep_subset_carrier by simp
  have splitZ: "sum c Z = sum c1 Z + sum c2 Z"
    using assms(1) Z_carrier by (subst sum.distrib[symmetric]) (auto intro: sum.cong)
  have splitX: "sum c X = sum c1 X + sum c2 X"
    using assms(1) X_carrier by (subst sum.distrib[symmetric]) (auto intro: sum.cong)
  have "sum c1 Z \<le> sum c1 X" using assms(5)[OF assms(7) assms(9)] .
  moreover have "sum c2 Z \<le> sum c2 X" using assms(6)[OF assms(8) assms(9)] .
  ultimately show ?thesis using splitZ splitX by (simp add: add_mono)
qed

end

text \<open>Three list utilities for deleting the element at a fixed index, needed for the induction in
Lemma 13.35.\<close>

lemma del_index_nth:
  assumes "h < length zs" "p < length zs - 1"
  shows "(take h zs @ drop (Suc h) zs) ! p = zs ! (if p < h then p else Suc p)"
proof(cases "p < h")
  case True
  thus ?thesis using assms by (simp add: nth_append)
next
  case False
  thus ?thesis using assms by (simp add: nth_append)
qed

lemma del_index_set:
  assumes "distinct zs" "h < length zs"
  shows "set (take h zs @ drop (Suc h) zs) = set zs - {zs ! h}"
proof-
  have decomp: "zs = take h zs @ zs ! h # drop (Suc h) zs"
    using id_take_nth_drop[OF assms(2)] by simp
  have dd: "distinct (take h zs @ zs ! h # drop (Suc h) zs)"
    by (subst decomp[symmetric]) (rule assms(1))
  have notin: "zs ! h \<notin> set (take h zs @ drop (Suc h) zs)"
    using dd by auto
  have setzs: "set zs = insert (zs ! h) (set (take h zs @ drop (Suc h) zs))"
    by (subst decomp) auto
  from setzs notin show ?thesis by auto
qed

lemma del_index_distinct:
  assumes "distinct zs" "h < length zs"
  shows "distinct (take h zs @ drop (Suc h) zs)"
proof-
  have decomp: "zs = take h zs @ zs ! h # drop (Suc h) zs"
    using id_take_nth_drop[OF assms(2)] by simp
  have dd: "distinct (take h zs @ zs ! h # drop (Suc h) zs)"
    by (subst decomp[symmetric]) (rule assms(1))
  thus ?thesis by auto
qed

text \<open>Weight telescoping across a tight alternating path. If \<open>n\<close> is odd and successive elements
across every odd-indexed edge carry equal weight, the total over even indices exceeds that over odd
indices by exactly \<open>g 0\<close> (the source endpoint).\<close>
lemma sum_evens_odds_tight:
  fixes g :: "nat \<Rightarrow> 'b :: linordered_ab_group_add"
  assumes "odd n" "\<And>i. i < n \<Longrightarrow> odd i \<Longrightarrow> g i = g (Suc i)"
  shows "sum g {i. i < n \<and> even i} = sum g {i. i < n \<and> odd i} + g 0"
proof-
  have finE: "finite {i. i < n \<and> even i}" by simp
  have zero_in: "(0::nat) \<in> {i. i < n \<and> even i}" using assms(1) odd_pos by auto
  have img: "Suc ` {i. i < n \<and> odd i} = {i. i < n \<and> even i} - {0}"
  proof(intro equalityI subsetI)
    fix x assume "x \<in> Suc ` {i. i < n \<and> odd i}"
    then obtain i where i: "i < n" "odd i" "x = Suc i" by auto
    have "Suc i < n" using i assms(1) by presburger
    thus "x \<in> {i. i < n \<and> even i} - {0}" using i by auto
  next
    fix x assume x: "x \<in> {i. i < n \<and> even i} - {0}"
    have "x < n" "even x" "x \<noteq> 0" using x by auto
    hence "x - 1 < n \<and> odd (x - 1) \<and> x = Suc (x - 1)" by presburger
    thus "x \<in> Suc ` {i. i < n \<and> odd i}" by (auto simp add: image_iff)
  qed
  have inj: "inj_on Suc {i. i < n \<and> odd i}" by simp
  have reix: "sum g ({i. i < n \<and> even i} - {0}) = (\<Sum>i\<in>{i. i < n \<and> odd i}. g (Suc i))"
    using sum.reindex[OF inj, of g] img by (simp add: o_def)
  have tighteq: "(\<Sum>i\<in>{i. i < n \<and> odd i}. g (Suc i)) = sum g {i. i < n \<and> odd i}"
  proof(rule sum.cong[OF refl])
    fix i assume "i \<in> {i. i < n \<and> odd i}"
    hence "i < n" "odd i" by auto
    thus "g (Suc i) = g i" using assms(2) by simp
  qed
  have "sum g {i. i < n \<and> even i} = g 0 + sum g ({i. i < n \<and> even i} - {0})"
    by (rule sum.remove[OF finE zero_in])
  also have "... = g 0 + sum g {i. i < n \<and> odd i}" using reix tighteq by simp
  finally show ?thesis by (simp add: add.commute)
qed

text \<open>The symmetric telescoping across the even-indexed edges: the even-index total exceeds the
odd-index total by \<open>g (n - 1)\<close> (the sink endpoint).\<close>
lemma sum_evens_odds_tight2:
  fixes g :: "nat \<Rightarrow> 'b :: linordered_ab_group_add"
  assumes "odd n" "\<And>i. Suc i < n \<Longrightarrow> even i \<Longrightarrow> g i = g (Suc i)"
  shows "sum g {i. i < n \<and> even i} = sum g {i. i < n \<and> odd i} + g (n - 1)"
proof-
  have en1: "even (n - 1)" using assms(1) by presburger
  have n1: "n - 1 < n" using assms(1) odd_pos by fastforce
  have last_in: "(n - 1) \<in> {i. i < n \<and> even i}" using en1 n1 by simp
  have nn: "(n - 1) \<notin> {i. i < n \<and> even i \<and> i \<noteq> n - 1}" by auto
  have fin2: "finite {i. i < n \<and> even i \<and> i \<noteq> n - 1}" by simp
  have img: "Suc ` {i. i < n \<and> even i \<and> i \<noteq> n - 1} = {i. i < n \<and> odd i}"
  proof(intro equalityI subsetI)
    fix x assume "x \<in> Suc ` {i. i < n \<and> even i \<and> i \<noteq> n - 1}"
    then obtain i where i: "i < n" "even i" "i \<noteq> n - 1" "x = Suc i" by auto
    have "Suc i < n" using i assms(1) by presburger
    thus "x \<in> {i. i < n \<and> odd i}" using i by auto
  next
    fix x assume x: "x \<in> {i. i < n \<and> odd i}"
    have "x < n" "odd x" using x by auto
    hence "x - 1 < n \<and> even (x - 1) \<and> x - 1 \<noteq> n - 1 \<and> x = Suc (x - 1)" using assms(1) by presburger
    thus "x \<in> Suc ` {i. i < n \<and> even i \<and> i \<noteq> n - 1}" by (auto simp add: image_iff)
  qed
  have inj: "inj_on Suc {i. i < n \<and> even i \<and> i \<noteq> n - 1}" by simp
  have reix: "sum g {i. i < n \<and> odd i} = (\<Sum>i\<in>{i. i < n \<and> even i \<and> i \<noteq> n - 1}. g (Suc i))"
    using sum.reindex[OF inj, of g] img by (simp add: o_def)
  have tighteq: "(\<Sum>i\<in>{i. i < n \<and> even i \<and> i \<noteq> n - 1}. g (Suc i))
                   = sum g {i. i < n \<and> even i \<and> i \<noteq> n - 1}"
  proof(rule sum.cong[OF refl])
    fix i assume i: "i \<in> {i. i < n \<and> even i \<and> i \<noteq> n - 1}"
    hence "i < n" "even i" "i \<noteq> n - 1" by auto
    hence "Suc i < n" using assms(1) by presburger
    thus "g (Suc i) = g i" using \<open>even i\<close> assms(2) by simp
  qed
  have split: "{i. i < n \<and> even i} = insert (n - 1) {i. i < n \<and> even i \<and> i \<noteq> n - 1}"
    using last_in by auto
  have "sum g {i. i < n \<and> even i} = g (n - 1) + sum g {i. i < n \<and> even i \<and> i \<noteq> n - 1}"
    by (subst split) (rule sum.insert[OF fin2 nn])
  also have "... = g (n - 1) + sum g {i. i < n \<and> odd i}" using reix tighteq by simp
  finally show ?thesis by (simp add: add.commute)
qed

context matroid
begin

text \<open>Basic circuit exchange: if \<open>x\<close> lies in the fundamental circuit \<open>C(X, y)\<close>, then swapping \<open>x\<close>
for \<open>y\<close> keeps the set independent.\<close>

lemma circuit_exchange_indep:
  assumes "indep X" "y \<in> carrier - X" "x \<in> the_circuit (insert y X)"
  shows "indep (insert y X - {x})"
proof-
  have inserty_carrier: "insert y X \<subseteq> carrier"
    using assms(1,2) indep_subset_carrier by auto
  have not_indep: "\<not> indep (insert y X)"
    using assms(3) the_circuit_non_empty_dependent by auto
  have C_circuit: "circuit (the_circuit (insert y X))"
    using the_circuit_is_circuit(1)[OF assms(1) not_indep inserty_carrier] by simp
  have sub_carrier: "insert y X - {x} \<subseteq> carrier"
    using inserty_carrier by auto
  show ?thesis
  proof(rule ccontr)
    assume "\<not> indep (insert y X - {x})"
    then obtain C2 where C2: "circuit C2" "C2 \<subseteq> insert y X - {x}"
      using dep_iff_supset_circuit[OF sub_carrier] by auto
    hence "C2 = the_circuit (insert y X)"
      using circuit_is_the_circuit[OF assms(1) not_indep C2(1)] by auto
    thus False using assms(3) C2(2) by auto
  qed
qed

text \<open>The fundamental circuit of \<open>y\<close> is unaffected by replacing \<open>X\<close> by an independent \<open>X'\<close> that
still contains that circuit (apart from \<open>y\<close>).\<close>

lemma the_circuit_swap_invariant:
  assumes "indep X" "indep X'" "y \<in> carrier" "y \<notin> X'"
    "\<not> indep (insert y X)"
    "the_circuit (insert y X) \<subseteq> insert y X'"
  shows "the_circuit (insert y X') = the_circuit (insert y X)"
proof-
  have inserty_carrier: "insert y X \<subseteq> carrier"
    using assms(1,3) indep_subset_carrier by auto
  have C_circuit: "circuit (the_circuit (insert y X))"
    using the_circuit_is_circuit(1)[OF assms(1) assms(5) inserty_carrier] by simp
  have not_indep': "\<not> indep (insert y X')"
    using supset_circuit_imp_dep[OF conjI[OF C_circuit assms(6)]] by simp
  show ?thesis
    using circuit_is_the_circuit[OF assms(2) not_indep' C_circuit assms(6)] by simp
qed

text \<open>Frank's augmentation lemma (Lemma 13.35), the weighted analogue of
@{thm [source] single_matroid_augment}. Given a weight \<open>c\<close>, a matching sequence of removed
elements \<open>fst (xys ! i)\<close> and inserted elements \<open>snd (xys ! i)\<close> where each removed element sits on
the fundamental circuit of the inserted one with equal weight, and the two cross conditions on
circuit membership versus weight hold, the resulting swap keeps the set independent.\<close>

lemma weighted_single_matroid_augment:
  fixes c :: "'a \<Rightarrow> 'b :: linorder"
  assumes "indep X"
    "set (map fst xys) \<subseteq> X"
    "set (map snd xys) \<subseteq> carrier - X"
    "s = length xys"
    "distinct (map fst xys)"
    "distinct (map snd xys)"
    "\<And> i. i < s \<Longrightarrow>
       fst (xys ! i) \<in> the_circuit (insert (snd (xys ! i)) X) \<and> c (fst (xys ! i)) = c (snd (xys ! i))"
    "\<And> i j. i < s \<Longrightarrow> j < s \<Longrightarrow> j < i \<Longrightarrow>
       fst (xys ! j) \<notin> the_circuit (insert (snd (xys ! i)) X) \<or> c (fst (xys ! j)) > c (snd (xys ! i))"
    "\<And> i j. i < s \<Longrightarrow> j < s \<Longrightarrow> j < i \<Longrightarrow>
       fst (xys ! i) \<notin> the_circuit (insert (snd (xys ! j)) X) \<or> c (fst (xys ! i)) \<ge> c (snd (xys ! j))"
    "XR = X - set (map fst xys) \<union> set (map snd xys)"
  shows "indep XR"
  using assms
proof(induction "length xys" arbitrary: xys X XR s rule: less_induct)
  case less
  show ?case
  proof(cases "xys = []")
    case True
    then show ?thesis using less.prems(1,10) by simp
  next
    case False
    hence lpos: "0 < length xys" by simp
    \<comment> \<open>pick \<open>h\<close>, the smallest index realising the minimum weight among the removed elements\<close>
    define P where "P = (\<lambda> i. i < length xys \<and> (\<forall> j < length xys. c (fst (xys ! i)) \<le> c (fst (xys ! j))))"
    have exP: "\<exists> i. P i"
    proof-
      have fin: "finite ((\<lambda>i. c (fst (xys!i))) ` {0..<length xys})" by simp
      have ne: "(\<lambda>i. c (fst (xys!i))) ` {0..<length xys} \<noteq> {}" using lpos by simp
      obtain i0 where i0: "i0 < length xys" "c (fst (xys!i0)) = Min ((\<lambda>i. c (fst (xys!i))) ` {0..<length xys})"
        using Min_in[OF fin ne] by auto
      have "\<And> j. j < length xys \<Longrightarrow> c (fst (xys!i0)) \<le> c (fst (xys!j))"
        using Min_le[OF fin] i0(2) by auto
      thus ?thesis using i0(1) P_def by blast
    qed
    define h where "h = (LEAST i. P i)"
    have Ph: "P h" unfolding h_def using exP by (rule LeastI_ex)
    have h_less: "h < length xys" using Ph P_def by simp
    have h_min: "\<And> j. j < length xys \<Longrightarrow> c (fst (xys!h)) \<le> c (fst (xys!j))" using Ph P_def by simp
    have h_smallest: "\<And> i. i < h \<Longrightarrow> c (fst (xys!h)) < c (fst (xys!i))"
    proof-
      fix i assume ih: "i < h"
      hence notPi: "\<not> P i" using not_less_Least[of i P] by (simp add: h_def)
      have ilen: "i < length xys" using ih h_less by simp
      then obtain j where j: "j < length xys" "c (fst (xys!j)) < c (fst (xys!i))"
        using notPi P_def not_le by auto
      show "c (fst (xys!h)) < c (fst (xys!i))" using h_min[OF j(1)] j(2) by (rule le_less_trans)
    qed
    \<comment> \<open>length-indexed reformulation of the three hypotheses\<close>
    have acond: "\<And> i. i < length xys \<Longrightarrow>
        fst (xys!i) \<in> the_circuit (insert (snd (xys!i)) X) \<and> c (fst (xys!i)) = c (snd (xys!i))"
      using less.prems(7)[unfolded less.prems(4)] .
    have bcond: "\<And> i j. i < length xys \<Longrightarrow> j < length xys \<Longrightarrow> j < i \<Longrightarrow>
        fst (xys!j) \<notin> the_circuit (insert (snd (xys!i)) X) \<or> c (fst (xys!j)) > c (snd (xys!i))"
      using less.prems(8)[unfolded less.prems(4)] .
    have ccond: "\<And> i j. i < length xys \<Longrightarrow> j < length xys \<Longrightarrow> j < i \<Longrightarrow>
        fst (xys!i) \<notin> the_circuit (insert (snd (xys!j)) X) \<or> c (fst (xys!i)) \<ge> c (snd (xys!j))"
      using less.prems(9)[unfolded less.prems(4)] .
    have hs: "h < s" using h_less less.prems(4) by simp
    have xh_in_X: "fst (xys!h) \<in> X"
      using less.prems(2) h_less by (metis length_map nth_map nth_mem subsetD)
    have yh_in: "snd (xys!h) \<in> carrier - X"
      using less.prems(3) h_less by (metis length_map nth_map nth_mem subsetD)
    have xh_circ: "fst (xys!h) \<in> the_circuit (insert (snd (xys!h)) X)"
      using less.prems(7)[OF hs] by simp
    define X' where "X' = insert (snd (xys!h)) X - {fst (xys!h)}"
    have indepX': "indep X'"
      using circuit_exchange_indep[OF less.prems(1) yh_in xh_circ] X'_def by simp
    \<comment> \<open>the minimum-weight removed element lies on none of the other fundamental circuits\<close>
    have h_notin_circ: "\<And> j. j < length xys \<Longrightarrow> j \<noteq> h \<Longrightarrow>
        fst (xys!h) \<notin> the_circuit (insert (snd (xys!j)) X)"
    proof-
      fix j assume j: "j < length xys" "j \<noteq> h"
      show "fst (xys!h) \<notin> the_circuit (insert (snd (xys!j)) X)"
      proof(cases "h < j")
        case True
        have disj: "fst (xys!h) \<notin> the_circuit (insert (snd (xys!j)) X) \<or> c (fst (xys!h)) > c (snd (xys!j))"
          using bcond[OF j(1) h_less True] .
        have "c (fst (xys!h)) \<le> c (fst (xys!j))" using h_min[OF j(1)] .
        moreover have "c (fst (xys!j)) = c (snd (xys!j))" using acond[OF j(1)] by simp
        ultimately show ?thesis using disj by auto
      next
        case False
        hence jh: "j < h" using j(2) by simp
        have disj: "fst (xys!h) \<notin> the_circuit (insert (snd (xys!j)) X) \<or> c (fst (xys!h)) \<ge> c (snd (xys!j))"
          using ccond[OF h_less j(1) jh] .
        have "c (fst (xys!h)) < c (fst (xys!j))" using h_smallest[OF jh] .
        moreover have "c (fst (xys!j)) = c (snd (xys!j))" using acond[OF j(1)] by simp
        ultimately show ?thesis using disj by auto
      qed
    qed
    \<comment> \<open>hence every remaining fundamental circuit is preserved by the swap\<close>
    have circ_inv: "\<And> j. j < length xys \<Longrightarrow> j \<noteq> h \<Longrightarrow>
        the_circuit (insert (snd (xys!j)) X') = the_circuit (insert (snd (xys!j)) X)"
    proof-
      fix j assume j: "j < length xys" "j \<noteq> h"
      have yj_in: "snd (xys!j) \<in> carrier - X"
        using less.prems(3) j(1) by (metis length_map nth_map nth_mem subsetD)
      have yj_carrier: "snd (xys!j) \<in> carrier" using yj_in by simp
      have yj_neq_yh: "snd (xys!j) \<noteq> snd (xys!h)"
        using less.prems(6) j h_less by (metis distinct_conv_nth length_map nth_map)
      have yj_notin_X': "snd (xys!j) \<notin> X'"
        using yj_in yj_neq_yh X'_def by simp
      have dep_j: "\<not> indep (insert (snd (xys!j)) X)"
        using acond[OF j(1)] the_circuit_non_empty_dependent by auto
      have insertj_carrier: "insert (snd (xys!j)) X \<subseteq> carrier"
        using less.prems(1) yj_in indep_subset_carrier by auto
      have C_sub: "the_circuit (insert (snd (xys!j)) X) \<subseteq> insert (snd (xys!j)) X"
        using the_circuit_is_circuit(2)[OF less.prems(1) dep_j insertj_carrier] .
      have C_sub_X': "the_circuit (insert (snd (xys!j)) X) \<subseteq> insert (snd (xys!j)) X'"
        using C_sub h_notin_circ[OF j] X'_def by auto
      show "the_circuit (insert (snd (xys!j)) X') = the_circuit (insert (snd (xys!j)) X)"
        using the_circuit_swap_invariant[OF less.prems(1) indepX' yj_carrier yj_notin_X' dep_j C_sub_X'] .
    qed
    \<comment> \<open>delete pair \<open>h\<close> and apply the induction hypothesis to the shorter list\<close>
    define ys' where "ys' = take h xys @ drop (Suc h) xys"
    have len': "length ys' = length xys - 1" using h_less by (simp add: ys'_def)
    have len_lt: "length ys' < length xys" using len' lpos by simp
    have nth': "\<And> p. p < length xys - 1 \<Longrightarrow> ys' ! p = xys ! (if p < h then p else Suc p)"
      using del_index_nth[OF h_less] by (simp add: ys'_def)
    have mapfst': "map fst ys' = take h (map fst xys) @ drop (Suc h) (map fst xys)"
      by (simp add: ys'_def take_map drop_map)
    have mapsnd': "map snd ys' = take h (map snd xys) @ drop (Suc h) (map snd xys)"
      by (simp add: ys'_def take_map drop_map)
    have nthfst: "map fst xys ! h = fst (xys!h)" using h_less by simp
    have nthsnd: "map snd xys ! h = snd (xys!h)" using h_less by simp
    have hlenf: "h < length (map fst xys)" using h_less by simp
    have hlens: "h < length (map snd xys)" using h_less by simp
    have setfst': "set (map fst ys') = set (map fst xys) - {fst (xys!h)}"
      using del_index_set[OF less.prems(5) hlenf] mapfst' nthfst by simp
    have setsnd': "set (map snd ys') = set (map snd xys) - {snd (xys!h)}"
      using del_index_set[OF less.prems(6) hlens] mapsnd' nthsnd by simp
    have distfst': "distinct (map fst ys')"
      using del_index_distinct[OF less.prems(5), of h] h_less mapfst' by simp
    have distsnd': "distinct (map snd ys')"
      using del_index_distinct[OF less.prems(6), of h] h_less mapsnd' by simp
    have fstsub: "set (map fst ys') \<subseteq> X'"
      unfolding setfst' X'_def using less.prems(2) by auto
    have sndsub: "set (map snd ys') \<subseteq> carrier - X'"
      unfolding setsnd' X'_def using less.prems(3) by auto
    have acond': "\<And> i. i < length ys' \<Longrightarrow>
        fst (ys'!i) \<in> the_circuit (insert (snd (ys'!i)) X') \<and> c (fst (ys'!i)) = c (snd (ys'!i))"
    proof-
      fix i assume i: "i < length ys'"
      define gi where "gi = (if i < h then i else Suc i)"
      have gi_lt: "gi < length xys" using i len' h_less by (auto simp add: gi_def)
      have gi_ne: "gi \<noteq> h" by (auto simp add: gi_def)
      have yi: "ys'!i = xys!gi" using nth'[of i] i len' by (simp add: gi_def)
      have "fst (xys!gi) \<in> the_circuit (insert (snd (xys!gi)) X)" using acond[OF gi_lt] by simp
      hence "fst (ys'!i) \<in> the_circuit (insert (snd (ys'!i)) X')"
        using circ_inv[OF gi_lt gi_ne] yi by simp
      moreover have "c (fst (ys'!i)) = c (snd (ys'!i))" using acond[OF gi_lt] yi by simp
      ultimately show "fst (ys'!i) \<in> the_circuit (insert (snd (ys'!i)) X') \<and> c (fst (ys'!i)) = c (snd (ys'!i))"
        by simp
    qed
    have bcond': "\<And> i j. i < length ys' \<Longrightarrow> j < length ys' \<Longrightarrow> j < i \<Longrightarrow>
        fst (ys'!j) \<notin> the_circuit (insert (snd (ys'!i)) X') \<or> c (fst (ys'!j)) > c (snd (ys'!i))"
    proof-
      fix i j assume ij: "i < length ys'" "j < length ys'" "j < i"
      define gi where "gi = (if i < h then i else Suc i)"
      define gj where "gj = (if j < h then j else Suc j)"
      have gi_lt: "gi < length xys" using ij(1) len' h_less by (auto simp add: gi_def)
      have gj_lt: "gj < length xys" using ij(2) len' h_less by (auto simp add: gj_def)
      have gi_ne: "gi \<noteq> h" by (auto simp add: gi_def)
      have gji: "gj < gi" using ij(3) by (auto simp add: gi_def gj_def)
      have yi: "ys'!i = xys!gi" using nth'[of i] ij(1) len' by (simp add: gi_def)
      have yj: "ys'!j = xys!gj" using nth'[of j] ij(2) len' by (simp add: gj_def)
      have "fst (xys!gj) \<notin> the_circuit (insert (snd (xys!gi)) X) \<or> c (fst (xys!gj)) > c (snd (xys!gi))"
        using bcond[OF gi_lt gj_lt gji] .
      thus "fst (ys'!j) \<notin> the_circuit (insert (snd (ys'!i)) X') \<or> c (fst (ys'!j)) > c (snd (ys'!i))"
        using circ_inv[OF gi_lt gi_ne] yi yj by simp
    qed
    have ccond': "\<And> i j. i < length ys' \<Longrightarrow> j < length ys' \<Longrightarrow> j < i \<Longrightarrow>
        fst (ys'!i) \<notin> the_circuit (insert (snd (ys'!j)) X') \<or> c (fst (ys'!i)) \<ge> c (snd (ys'!j))"
    proof-
      fix i j assume ij: "i < length ys'" "j < length ys'" "j < i"
      define gi where "gi = (if i < h then i else Suc i)"
      define gj where "gj = (if j < h then j else Suc j)"
      have gi_lt: "gi < length xys" using ij(1) len' h_less by (auto simp add: gi_def)
      have gj_lt: "gj < length xys" using ij(2) len' h_less by (auto simp add: gj_def)
      have gj_ne: "gj \<noteq> h" by (auto simp add: gj_def)
      have gji: "gj < gi" using ij(3) by (auto simp add: gi_def gj_def)
      have yi: "ys'!i = xys!gi" using nth'[of i] ij(1) len' by (simp add: gi_def)
      have yj: "ys'!j = xys!gj" using nth'[of j] ij(2) len' by (simp add: gj_def)
      have "fst (xys!gi) \<notin> the_circuit (insert (snd (xys!gj)) X) \<or> c (fst (xys!gi)) \<ge> c (snd (xys!gj))"
        using ccond[OF gi_lt gj_lt gji] .
      thus "fst (ys'!i) \<notin> the_circuit (insert (snd (ys'!j)) X') \<or> c (fst (ys'!i)) \<ge> c (snd (ys'!j))"
        using circ_inv[OF gj_lt gj_ne] yi yj by simp
    qed
    have XR'': "X' - set (map fst ys') \<union> set (map snd ys') = XR"
    proof-
      have fh_in_F: "fst (xys!h) \<in> set (map fst xys)" using h_less by (metis length_map nth_map nth_mem)
      have yh_in_snd: "snd (xys!h) \<in> set (map snd xys)" using h_less by (metis length_map nth_map nth_mem)
      have "X' - set (map fst ys') \<union> set (map snd ys')
          = (insert (snd (xys!h)) X - {fst (xys!h)}) - (set (map fst xys) - {fst (xys!h)})
              \<union> (set (map snd xys) - {snd (xys!h)})"
        using setfst' setsnd' by (simp add: X'_def)
      also have "... = X - set (map fst xys) \<union> set (map snd xys)"
        using xh_in_X yh_in yh_in_snd fh_in_F less.prems(2,3) by auto
      finally show ?thesis using less.prems(10) by simp
    qed
    have "indep (X' - set (map fst ys') \<union> set (map snd ys'))"
      using less.hyps[OF len_lt indepX' fstsub sndsub refl distfst' distsnd' acond' bcond' ccond' refl] .
    thus ?thesis using XR'' by simp
  qed
qed

end

section \<open>Algorithm-independent candidate lemmas for the weighted algorithm\<close>

text \<open>The snapshot lemmas behind Korte\&Vygen Theorem 13.36; see
\<open>Weighted_Intersection_Lemma_Candidates.md\<close>. They speak about a fixed common independent set,
never about the iteration.\<close>

context matroid
begin

text \<open>\<open>max_weight_card c X\<close>: \<open>X\<close> has maximum \<open>c\<close>-weight among the independent sets of its cardinality.\<close>
definition max_weight_card :: "('a \<Rightarrow> 'b :: linordered_ab_group_add) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "max_weight_card c X \<longleftrightarrow> (\<forall> Y. indep Y \<and> card Y = card X \<longrightarrow> sum c Y \<le> sum c X)"

text \<open>\<open>local_opt c X\<close>: the two conditions of the greedy optimality criterion (Theorem 13.23) --
(a) no profitable circuit swap, (b) no profitable single addition.\<close>
definition local_opt :: "('a \<Rightarrow> 'b :: linordered_ab_group_add) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "local_opt c X \<longleftrightarrow>
     (\<forall> y \<in> carrier - X. \<forall> x \<in> the_circuit (insert y X) - {y}. c y \<le> c x)
   \<and> (\<forall> x \<in> X. \<forall> y \<in> carrier - X. indep (insert y X) \<longrightarrow> c y \<le> c x)"

text \<open>Single-element symmetric exchange (Brualdi) -- the key sublemma for the hard direction of the
greedy optimality criterion; proved from the \<open>augment\<close> axiom (absent from the library).\<close>
lemma symmetric_exchange:
  assumes "indep X" "indep Y" "card X = card Y" "x \<in> X - Y"
  shows "\<exists> y \<in> Y - X. indep (insert y (X - {x})) \<and> indep (insert x (Y - {y}))"
proof-
  have xX: "x \<in> X" and xnY: "x \<notin> Y" using assms(4) by auto
  have Xc: "X \<subseteq> carrier" using assms(1) indep_subset_carrier by simp
  have Yc: "Y \<subseteq> carrier" using assms(2) indep_subset_carrier by simp
  have xc: "x \<in> carrier" using xX Xc by auto
  have indepA: "indep (X - {x})" using assms(1) indep_subset by auto
  have Ac: "X - {x} \<subseteq> carrier" using Xc by auto
  have cardA: "card (X - {x}) < card Y"
    using card_Diff1_less[OF indep_finite[OF assms(1)] xX] assms(3) by simp
  \<comment> \<open>Fact C: an element of an independent set is not spanned by the rest\<close>
  have factC: "x \<notin> cl (X - {x})"
  proof
    assume "x \<in> cl (X - {x})"
    hence "rank_of (insert x (X - {x})) = rank_of (X - {x})" by (rule cl_rank_of)
    hence "rank_of X = rank_of (X - {x})"
      using xX by (simp add: insert_absorb)
    moreover have "rank_of X = card X" 
      using indep_iff_rank_of[OF Xc] assms(1) by blast
    moreover have "rank_of (X - {x}) = card (X - {x})" 
      using indep_iff_rank_of[OF Ac] indepA by blast
    ultimately have "card X = card (X - {x})" by linarith
    thus False using card_Diff1_less[OF indep_finite[OF assms(1)] xX] by linarith
  qed
  show ?thesis
  proof(cases "indep (insert x Y)")
    case True
    \<comment> \<open>x can be added to Y freely; augment \<open>X - {x}\<close> from Y to get the first swap\<close>
    obtain z where z: "z \<in> Y - (X - {x})" "indep (insert z (X - {x}))"
      using augment[OF assms(2) indepA cardA] by auto
    have zYX: "z \<in> Y - X" using z(1) xnY by auto
    have "insert x (Y - {z}) \<subseteq> insert x Y" by auto
    hence "indep (insert x (Y - {z}))" using True indep_subset by auto
    thus ?thesis using z(2) zYX by blast
  next
    case False
    \<comment> \<open>otherwise x lies on the fundamental circuit C of x in Y\<close>
    define C where "C = the_circuit (insert x Y)"
    have insxY_c: "insert x Y \<subseteq> carrier" using Yc xc by auto
    have Ccirc: "circuit C" and Csub: "C \<subseteq> insert x Y"
      using the_circuit_is_circuit[OF assms(2) False insxY_c] C_def by auto
    have xC: "x \<in> C"
      using circuit_extensional[OF assms(2) xc] False assms(2) xnY C_def by auto
    \<comment> \<open>some circuit element lies outside X and extends \<open>X - {x}\<close>\<close>
    have "\<exists> y \<in> C - X. indep (insert y (X - {x}))"
    proof(rule ccontr)
      assume noext: "\<not> (\<exists> y \<in> C - X. indep (insert y (X - {x})))"
      have CsubclA: "C - {x} \<subseteq> cl (X - {x})"
      proof
        fix z assume zC: "z \<in> C - {x}"
        show "z \<in> cl (X - {x})"
        proof(cases "z \<in> X")
          case True
          thus ?thesis using zC cl_subset[OF Ac] by auto
        next
          case False
          have "z \<in> carrier" using zC Ccirc circuit_subset_carrier by auto
          moreover have "\<not> indep (insert z (X - {x}))" using noext zC False by auto
          ultimately show ?thesis using clI_insert[OF _ indepA] by auto
        qed
      qed
      have "cl (C - {x}) \<subseteq> cl (cl (X - {x}))"
        using cl_mono[OF CsubclA cl_subset_carrier] .
      hence sub: "cl (C - {x}) \<subseteq> cl (X - {x})" by (simp add: cl_cl_absorb[OF Ac])
      have "indep (C - {x})" using circuit_min_dep[OF Ccirc xC] .
      moreover have "\<not> indep (insert x (C - {x}))"
        using circuit_dep[OF Ccirc] xC by (simp add: insert_absorb)
      ultimately have "x \<in> cl (C - {x})" by (rule clI_insert[OF xc])
      thus False using sub factC by auto
    qed
    then obtain y where y: "y \<in> C - X" "indep (insert y (X - {x}))" by auto
    have yY: "y \<in> Y" using y(1) Csub xX by auto
    have "indep (insert x (Y - {y}))"
    proof-
      have yneqx: "y \<noteq> x" using y(1) xX by auto
      have "indep (insert x Y - {y})"
        using circuit_extensional[OF assms(2) xc] False C_def y(1) by auto
      moreover have "insert x (Y - {y}) = insert x Y - {y}" using yneqx by auto
      ultimately show ?thesis by simp
    qed
    thus ?thesis using y(1) y(2) yY by blast
  qed
qed

text \<open>C1 -- Theorem 13.23: local optimality characterises maximum weight at fixed cardinality.\<close>
lemma greedy_optimality:
  fixes c :: "'a \<Rightarrow> 'b :: linordered_ab_group_add"
  assumes "indep X"
  shows "max_weight_card c X \<longleftrightarrow> local_opt c X"
proof-
  have finX: "finite X" using assms indep_finite by simp
  have Xc: "X \<subseteq> carrier" using assms indep_subset_carrier by simp
  have sumswap: "sum c (insert v (Z - {u})) = sum c Z - c u + c v"
    if Z: "finite Z" "u \<in> Z" "v \<notin> Z" for u v Z
  proof-
    have "v \<notin> Z - {u}" using Z(3) by simp
    hence "sum c (insert v (Z - {u})) = c v + sum c (Z - {u})"
      by (rule sum.insert[OF finite_Diff[OF Z(1)]])
    moreover have "sum c Z = c u + sum c (Z - {u})" by (rule sum.remove[OF Z(1) Z(2)])
    ultimately show ?thesis by (simp add: algebra_simps)
  qed
  have cardswap: "card (insert v (Z - {u})) = card Z"
    if Z: "finite Z" "u \<in> Z" "v \<notin> Z" for u v Z
  proof-
    have "v \<notin> Z - {u}" using Z(3) by simp
    hence "card (insert v (Z - {u})) = Suc (card (Z - {u}))"
      by (rule card_insert_disjoint[OF finite_Diff[OF Z(1)]])
    moreover have "card (Z - {u}) = card Z - 1" using Z(1,2) by (simp add: card_Diff_singleton)
    moreover have "0 < card Z" using Z(1,2) card_gt_0_iff by auto
    ultimately show ?thesis by simp
  qed
  have gt_of_swap: "Z < Z - a + b" if "a < b" for Z a b :: 'b
  proof-
    have "Z = (Z - a) + a" by simp
    also have "\<dots> < (Z - a) + b" using that by (rule add_strict_left_mono)
    finally show ?thesis by (simp add: algebra_simps)
  qed
  have le_of_swap: "Z \<le> Z - a + b" if "a \<le> b" for Z a b :: 'b
  proof-
    have "Z = (Z - a) + a" by simp
    also have "\<dots> \<le> (Z - a) + b" using that by (rule add_left_mono)
    finally show ?thesis by (simp add: algebra_simps)
  qed
  show ?thesis
  proof(rule iffI)
    \<comment> \<open>forward: an optimum set admits no improving circuit swap or addition\<close>
    assume maxw: "max_weight_card c X"
    have maxw': "\<And> Y. indep Y \<Longrightarrow> card Y = card X \<Longrightarrow> sum c Y \<le> sum c X"
      using maxw unfolding max_weight_card_def by blast
    have condA: "c y \<le> c x"
      if yA: "y \<in> carrier - X" and xA: "x \<in> the_circuit (insert y X) - {y}" for x y
    proof(rule ccontr)
      assume "\<not> c y \<le> c x"
      hence lt: "c x < c y" by simp
      have ynotX: "y \<notin> X" and yc: "y \<in> carrier" using yA by auto
      have xcirc: "x \<in> the_circuit (insert y X)" and xny: "x \<noteq> y" using xA by auto
      have ndep: "\<not> indep (insert y X)" using xcirc the_circuit_non_empty_dependent by auto
      have insyX_c: "insert y X \<subseteq> carrier" using Xc yc by auto
      have xX: "x \<in> X"
        using xcirc the_circuit_is_circuit(2)[OF assms ndep insyX_c] xny by auto
      have eqset: "insert y X - {x} = insert y (X - {x})" using xny by auto
      have "indep (insert y X - {x})" using circuit_exchange_indep[OF assms yA xcirc] .
      hence indeps: "indep (insert y (X - {x}))" using eqset by simp
      have cards: "card (insert y (X - {x})) = card X" using cardswap[OF finX xX ynotX] .
      show False
        using sumswap[OF finX xX ynotX] gt_of_swap[OF lt, of "sum c X"] maxw'[OF indeps cards] by simp
    qed
    have condB: "c y \<le> c x"
      if xB: "x \<in> X" and yB: "y \<in> carrier - X" and dep: "indep (insert y X)" for x y
    proof(rule ccontr)
      assume "\<not> c y \<le> c x"
      hence lt: "c x < c y" by simp
      have ynotX: "y \<notin> X" using yB by simp
      have xny: "x \<noteq> y" using xB ynotX by auto
      have eqset: "insert y X - {x} = insert y (X - {x})" using xny by auto
      have "insert y X - {x} \<subseteq> insert y X" by auto
      hence "indep (insert y X - {x})" using dep indep_subset by auto
      hence indeps: "indep (insert y (X - {x}))" using eqset by simp
      have cards: "card (insert y (X - {x})) = card X" using cardswap[OF finX xB ynotX] .
      show False
        using sumswap[OF finX xB ynotX] gt_of_swap[OF lt, of "sum c X"] maxw'[OF indeps cards] by simp
    qed
    show "local_opt c X" using condA condB by (simp add: local_opt_def)
  next
    \<comment> \<open>backward: local optimality is global, by induction on \<open>card (X - Y)\<close> via symmetric exchange\<close>
    assume lopt: "local_opt c X"
    have loA: "\<And> y x. y \<in> carrier - X \<Longrightarrow> x \<in> the_circuit (insert y X) - {y} \<Longrightarrow> c y \<le> c x"
      using conjunct1[OF lopt[unfolded local_opt_def], rule_format] .
    have loB: "\<And> x y. x \<in> X \<Longrightarrow> y \<in> carrier - X \<Longrightarrow> indep (insert y X) \<Longrightarrow> c y \<le> c x"
      using conjunct2[OF lopt[unfolded local_opt_def], rule_format] .
    have main: "sum c Y \<le> sum c X"
      if "indep Y" "card Y = card X" "n = card (X - Y)" for Y n
      using that
    proof(induct n arbitrary: Y rule: less_induct)
      case (less n)
      have finY: "finite Y" using less.prems(1) indep_finite by simp
      show ?case
      proof(cases "X \<subseteq> Y")
        case True
        have "X = Y" using card_subset_eq[OF finY True less.prems(2)[symmetric]] .
        thus ?thesis by simp
      next
        case False
        then obtain x where x: "x \<in> X - Y" by auto
        have xX: "x \<in> X" and xnY: "x \<notin> Y" using x by auto
        obtain y where y: "y \<in> Y - X" "indep (insert y (X - {x}))" "indep (insert x (Y - {y}))"
          using symmetric_exchange[OF assms less.prems(1) less.prems(2)[symmetric] x] by auto
        have yY: "y \<in> Y" and ynX: "y \<notin> X" using y(1) by auto
        have ycarr: "y \<in> carrier" using yY less.prems(1) indep_subset_carrier by auto
        have yc: "y \<in> carrier - X" using ycarr ynX by simp
        have xny: "x \<noteq> y" using xX ynX by auto
        \<comment> \<open>the exchanged pair does not decrease the weight\<close>
        have cyx: "c y \<le> c x"
        proof(cases "indep (insert y X)")
          case True
          show ?thesis using loB[OF xX yc True] .
        next
          case False
          have eqset: "insert y X - {x} = insert y (X - {x})" using xny by auto
          hence "indep (insert y X - {x})" using y(2) by simp
          hence "x \<in> the_circuit (insert y X)"
            using circuit_extensional[OF assms ycarr] False xX by auto
          hence "x \<in> the_circuit (insert y X) - {y}" using xny by simp
          thus ?thesis by (rule loA[OF yc])
        qed
        \<comment> \<open>move Y one step towards X and recurse\<close>
        define Y' where "Y' = insert x (Y - {y})"
        have indepY': "indep Y'" using y(3) Y'_def by simp
        have cardY': "card Y' = card X"
          using cardswap[OF finY yY xnY] less.prems(2) Y'_def by simp
        have "X - Y' = (X - Y) - {x}" using ynX by (auto simp add: Y'_def)
        hence "card (X - Y') < n"
          using card_Diff1_less[OF finite_Diff[OF finX] x] less.prems(3) by simp
        hence hyp: "sum c Y' \<le> sum c X"
          by (rule less.hyps[OF _ indepY' cardY' refl])
        have "sum c Y' = sum c Y - c y + c x"
          unfolding Y'_def by (rule sumswap[OF finY yY xnY])
        hence "sum c Y \<le> sum c Y'" using le_of_swap[OF cyx, of "sum c Y"] by simp
        also have "\<dots> \<le> sum c X" using hyp .
        finally show ?thesis .
      qed
    qed
    show "max_weight_card c X"
      unfolding max_weight_card_def using main[OF _ _ refl] by blast
  qed
qed

text \<open>C2: adding the heaviest addable element preserves local optimality (hence optimality at card+1).\<close>
lemma greedy_extension:
  fixes c :: "'a \<Rightarrow> 'b :: linordered_ab_group_add"
  assumes "indep X" "local_opt c X" "y0 \<in> carrier - X" "indep (insert y0 X)"
    "c y0 = Max (c ` {y \<in> carrier - X. indep (insert y X)})"
  shows "local_opt c (insert y0 X)"
proof-
  define X' where "X' = insert y0 X"
  define S where "S = {y \<in> carrier - X. indep (insert y X)}"
  have finX: "finite X" using assms(1) indep_finite by simp
  have y0nX: "y0 \<notin> X" using assms(3) by simp
  have Ssub: "S \<subseteq> carrier" by (auto simp add: S_def)
  have finS: "finite S" using Ssub carrier_finite finite_subset by auto
  have cy0S: "c y0 = Max (c ` S)" using assms(5) by (simp add: S_def)
  \<comment> \<open>every element addable to X is no heavier than the chosen \<open>y0\<close>\<close>
  have maxadd: "c w \<le> c y0" if "w \<in> S" for w
  proof-
    have "c w \<in> c ` S" using that by simp
    hence "c w \<le> Max (c ` S)" by (rule Max_ge[OF finite_imageI[OF finS]])
    thus ?thesis using cy0S by simp
  qed
  have maxwX: "max_weight_card c X"
    using greedy_optimality[OF assms(1)] assms(2) by blast
  have cardX': "card X' = card X + 1" using y0nX finX by (simp add: X'_def)
  have eqX': "sum c X' = sum c X + c y0"
    using sum.insert[OF finX y0nX] by (simp add: X'_def add.commute)
  \<comment> \<open>hence \<open>X'\<close> is c-maximum at cardinality \<open>card X + 1\<close>\<close>
  have maxwX': "max_weight_card c X'"
    unfolding max_weight_card_def
  proof(intro allI impI)
    fix Z assume "indep Z \<and> card Z = card X'"
    hence Zi: "indep Z" and Zc: "card Z = card X'" by auto
    have finZ: "finite Z" using Zi indep_finite by simp
    have cardlt: "card X < card Z" using Zc cardX' by simp
    obtain w where w: "w \<in> Z - X" "indep (insert w X)"
      using augment[OF Zi assms(1) cardlt] by auto
    have wZ: "w \<in> Z" using w(1) by simp
    have "w \<in> carrier - X" using w(1) Zi indep_subset_carrier by auto
    hence wS: "w \<in> S" using w(2) by (simp add: S_def)
    have indepZw: "indep (Z - {w})" using indep_subset[OF Zi Diff_subset] .
    have cardZw: "card (Z - {w}) = card X"
      using wZ finZ Zc cardX' by (simp add: card_Diff_singleton)
    have le1: "sum c (Z - {w}) \<le> sum c X"
      using maxwX[unfolded max_weight_card_def, rule_format, OF conjI[OF indepZw cardZw]] .
    have eqZ: "sum c Z = sum c (Z - {w}) + c w"
      using sum.remove[OF finZ wZ] by (simp add: add.commute)
    have "sum c Z \<le> sum c X + c y0"
      unfolding eqZ using le1 maxadd[OF wS] by (rule add_mono)
    thus "sum c Z \<le> sum c X'" using eqX' by simp
  qed
  show ?thesis
    using greedy_optimality[OF assms(4)] maxwX'[unfolded X'_def] by blast
qed

text \<open>A locally optimal \<open>X\<close> bounds the weight of every larger independent set: each further
element weighs at most the bound \<open>d\<close> on the elements addable to \<open>X\<close>.\<close>
lemma local_opt_larger_bound:
  fixes c :: "'a \<Rightarrow> 'b :: linordered_ab_group_add"
  assumes "indep X" "local_opt c X" "indep Y" "card Y = card X + k"
    "\<And> y. \<lbrakk>y \<in> carrier - X; indep (insert y X)\<rbrakk> \<Longrightarrow> c y \<le> d"
  shows "sum c Y \<le> sum c X + sum (\<lambda> _. d) {..<k}"
  using assms
proof(induction k arbitrary: X)
  case 0
  have "max_weight_card c X"
    using greedy_optimality[OF 0(1)] 0(2) by blast
  thus ?case
    using 0(3,4) by (simp add: max_weight_card_def)
next
  case (Suc k)
  define S where "S = {y \<in> carrier - X. indep (insert y X)}"
  have finS: "finite S"
    using carrier_finite by (auto simp add: S_def)
  obtain w where "w \<in> Y - X" "indep (insert w X)"
    using augment[OF Suc(4,2)] Suc(5) by auto
  hence "w \<in> S"
    using indep_subset_carrier[OF Suc(4)] by (auto simp add: S_def)
  hence "Max (c ` S) \<in> c ` S"
    using finS by (intro Max_in) auto
  then obtain y0 where y0: "y0 \<in> S" "c y0 = Max (c ` S)"
    by auto
  have y0X: "y0 \<in> carrier - X" "indep (insert y0 X)"
    using y0(1) by (simp_all add: S_def)
  have finX: "finite X"
    using Suc(2) indep_finite by simp
  have lo: "local_opt c (insert y0 X)"
    by (rule greedy_extension[OF Suc(2,3) y0X y0(2)[unfolded S_def]])
  have IH: "sum c Y \<le> sum c (insert y0 X) + sum (\<lambda> _. d) {..<k}"
  proof(rule Suc.IH[OF y0X(2) lo Suc(4)])
    show "card Y = card (insert y0 X) + k"
      using Suc(5) y0X(1) finX by simp
    fix y assume "y \<in> carrier - insert y0 X" "indep (insert y (insert y0 X))"
    thus "c y \<le> d"
      using Suc(6) indep_subset[of "insert y (insert y0 X)" "insert y X"] by auto
  qed
  have "sum c Y \<le> c y0 + (sum c X + sum (\<lambda> _. d) {..<k})"
    using IH y0X(1) by (simp add: finX algebra_simps)
  also have "\<dots> \<le> d + (sum c X + sum (\<lambda> _. d) {..<k})"
    by (rule add_right_mono[OF Suc(6)[OF y0X]])
  finally show ?case
    by (simp add: algebra_simps)
qed

text \<open>C3: shifting the weight down by \<open>\<epsilon>\<close> on a set \<open>R\<close> preserves local optimality, provided \<open>\<epsilon>\<close> does
not exceed any weight gap across the boundary of \<open>R\<close>. This is the dual (reweighting) step.\<close>
lemma reweight_preserves_local_opt:
  fixes c :: "'a \<Rightarrow> 'b :: linordered_ab_group_add"
  assumes "indep X" "local_opt c X" "R \<subseteq> carrier" "0 < \<epsilon>"
    "\<And> y x. y \<in> carrier - X \<Longrightarrow> x \<in> the_circuit (insert y X) - {y} \<Longrightarrow> x \<in> R \<Longrightarrow> y \<notin> R
              \<Longrightarrow> \<epsilon> \<le> c x - c y"
    "\<And> x y. x \<in> X \<Longrightarrow> y \<in> carrier - X \<Longrightarrow> indep (insert y X) \<Longrightarrow> x \<in> R \<Longrightarrow> y \<notin> R
              \<Longrightarrow> \<epsilon> \<le> c x - c y"
  shows "local_opt (\<lambda> e. if e \<in> R then c e - \<epsilon> else c e) X"
proof-
  define c' where "c' = (\<lambda> e. if e \<in> R then c e - \<epsilon> else c e)"
  have loA: "\<And> y x. y \<in> carrier - X \<Longrightarrow> x \<in> the_circuit (insert y X) - {y} \<Longrightarrow> c y \<le> c x"
    using conjunct1[OF assms(2)[unfolded local_opt_def], rule_format] .
  have loB: "\<And> x y. x \<in> X \<Longrightarrow> y \<in> carrier - X \<Longrightarrow> indep (insert y X) \<Longrightarrow> c y \<le> c x"
    using conjunct2[OF assms(2)[unfolded local_opt_def], rule_format] .
  \<comment> \<open>reweighting keeps the order of any pair whose boundary gap is at least \<open>\<epsilon>\<close>\<close>
  have shift: "c' u \<le> c' v" if uv: "c u \<le> c v" "v \<in> R \<Longrightarrow> u \<notin> R \<Longrightarrow> \<epsilon> \<le> c v - c u" for u v
  proof(cases "u \<in> R")
    case uR: True
    show ?thesis
    proof(cases "v \<in> R")
      case True
      thus ?thesis using diff_right_mono[OF uv(1), of \<epsilon>] uR by (simp add: c'_def)
    next
      case False
      have "c u - \<epsilon> \<le> c u" using less_imp_le[OF assms(4)] by (simp add: diff_le_eq)
      also have "\<dots> \<le> c v" using uv(1) .
      finally show ?thesis using uR False by (simp add: c'_def)
    qed
  next
    case unR: False
    show ?thesis
    proof(cases "v \<in> R")
      case True
      have "c u \<le> c v - \<epsilon>" using uv(2)[OF True unR] by (simp add: le_diff_eq add.commute)
      thus ?thesis using unR True by (simp add: c'_def)
    next
      case False
      thus ?thesis using uv(1) unR by (simp add: c'_def)
    qed
  qed
  have condA': "c' y \<le> c' x"
    if yx: "y \<in> carrier - X" "x \<in> the_circuit (insert y X) - {y}" for x y
  proof(rule shift)
    show "c y \<le> c x" using loA[OF yx] .
    show "x \<in> R \<Longrightarrow> y \<notin> R \<Longrightarrow> \<epsilon> \<le> c x - c y" using assms(5)[OF yx] .
  qed
  have condB': "c' y \<le> c' x"
    if xy: "x \<in> X" "y \<in> carrier - X" "indep (insert y X)" for x y
  proof(rule shift)
    show "c y \<le> c x" using loB[OF xy] .
    show "x \<in> R \<Longrightarrow> y \<notin> R \<Longrightarrow> \<epsilon> \<le> c x - c y" using assms(6)[OF xy] .
  qed
  show ?thesis
    unfolding local_opt_def using condA'[unfolded c'_def] condB'[unfolded c'_def] by blast
qed

end

text \<open>The two-matroid graph lemmas fix both split weights and the fixed common independent set \<open>X\<close>,
so they live in an extension of \<open>double_matroid\<close> that also fixes \<open>c1 c2\<close>. The weight-induced
subgraph objects are defined as subsets of the (weight-agnostic) auxiliary graph \<open>A1 A2 S T\<close>.\<close>

locale weighted_intersection_graph = double_matroid carrier indep1 indep2
  for carrier :: "'a set" and indep1 indep2 +
  fixes c1 c2 :: "'a \<Rightarrow> 'b :: linordered_ab_group_add"
begin

context fixes X :: "'a set"
begin

definition "Sbar = {y \<in> S X. c1 y = Max (c1 ` S X)}"
definition "Tbar = {y \<in> T X. c2 y = Max (c2 ` T X)}"
definition "Abar1 = {e \<in> A1 X. c1 (fst e) = c1 (snd e)}"
definition "Abar2 = {e \<in> A2 X. c2 (fst e) = c2 (snd e)}"
definition "Gbar = Abar1 \<union> Abar2"

end

text \<open>The tight subgraph and restricted endpoints are subsets of the (weight-agnostic) auxiliary
graph; hence any tight path is a path in the full graph.\<close>
lemma Gbar_subset: "Gbar X \<subseteq> A1 X \<union> A2 X"
  by (auto simp add: Gbar_def Abar1_def Abar2_def)

lemma Sbar_subset: "Sbar X \<subseteq> S X"
  by (auto simp add: Sbar_def)

lemma Tbar_subset: "Tbar X \<subseteq> T X"
  by (auto simp add: Tbar_def)

text \<open>C4 -- facts (i)/(ii): every non-tight arc of the auxiliary graph has a strict weight drop.\<close>
lemma tight_gap1:
  assumes "indep1 X" "indep2 X" "matroid1.local_opt c1 X" "(x, y) \<in> A1 X" "c1 x \<noteq> c1 y"
  shows "c1 y < c1 x"
proof-
  have "y \<in> carrier - X" "x \<in> matroid1.the_circuit (insert y X) - {y}"
    using assms(4) by(auto simp add: A1_def)
  hence "c1 y \<le> c1 x"
    using assms(3) by(auto simp add: matroid1.local_opt_def)
  thus ?thesis using assms(5) by simp
qed

lemma tight_gap2:
  assumes "indep1 X" "indep2 X" "matroid2.local_opt c2 X" "(y, x) \<in> A2 X" "c2 x \<noteq> c2 y"
  shows "c2 y < c2 x"
proof-
  have "y \<in> carrier - X" "x \<in> matroid2.the_circuit (insert y X) - {y}"
    using assms(4) by(auto simp add: A2_def)
  hence "c2 y \<le> c2 x"
    using assms(3) by(auto simp add: matroid2.local_opt_def)
  thus ?thesis using assms(5) by simp
qed

text \<open>Weighted analogue of @{thm [source] augment_in_matroid1}: a shortest tight path augments while
keeping the first matroid independent, via Frank's Lemma 13.35. Condition (a)'s cost equality comes
from the tightness of the \<open>Abar1\<close>-arcs, (b)'s strict gap from a \<open>Gbar\<close>-shortcut argument, and (c)
directly from local optimality of \<open>X\<close> in matroid 1.\<close>
lemma weighted_augment_in_matroid1:
  assumes "indep1 X" "indep2 X" "matroid1.local_opt c1 X"
    "vwalk_bet (Gbar X) x p y" "x \<in> Sbar X" "y \<in> Tbar X"
    "\<nexists> q. vwalk_bet (Gbar X) x q y \<and> length q < length p"
  shows "indep1 ((X \<union> {p ! i | i. i < length p \<and> even i}) - {p ! i | i. i < length p \<and> odd i})"
proof-
  have xS: "x \<in> S X" using assms(5) Sbar_subset by blast
  have yT: "y \<in> T X" using assms(6) Tbar_subset by blast
  have vwalk_full: "vwalk_bet (A1 X \<union> A2 X) x p y"
    using assms(4) Gbar_subset by (meson vwalk_bet_subset)
  have p_non_empt: "p \<noteq> []" using assms(4) by auto
  have p_init: "p ! 0 = x" using assms(4) hd_conv_nth[OF p_non_empt] by(auto simp add: vwalk_bet_def)
  have X0: "indep1 (insert (p ! 0) X)" using xS by(auto simp add: S_def p_init)
  have odd_p: "odd (length p)"
    using xS yT by(intro walk_is_odd[OF assms(1,2) vwalk_full])(auto simp add: S_def T_def)
  have distinct_p: "distinct p" using shortest_vwalk_bet_distinct[OF assms(4,7)] .
  define s where "s = (length p - 1) div 2"
  define list where "list = [(p ! (2*i+1), p ! (2*i+2)). i <- [0..<s]]"
  have odds_are: "set (map fst list) = {p ! i | i. i < length p \<and> odd i}"
    using odd_p
    by (presburger |
        auto intro!: image_eqI[of "_ i" _ "(i - 1) div 2" for i] image_eqI[of "p ! i" fst for i]
        intro: less_mult_imp_div_less
        simp add: dvd_div_mult_self list_def s_def)+
  have evens_are: "set (map snd list) \<union> {p ! 0} = {p ! i | i. i < length p \<and> even i}"
    using odd_p not_less_eq_eq
    by (auto intro!: less_mult_imp_div_less diff_less_mono cong[OF refl, of _ _ "\<lambda> i. p ! i"]
                     image_eqI[of "_ i" _ "(i - 1) div 2" for i]
                     image_eqI[of "p ! i" snd
                     "(p ! Suc (2 * ((i-1) div 2)), p ! Suc (Suc (2 * ((i-1) div 2))))" for i]
          simp add: dvd_div_mult_self list_def s_def)+
  have helper1: "i < length p \<Longrightarrow> odd i \<Longrightarrow> (a, p ! i) \<in> set list \<Longrightarrow> False" for i a
    using distinct_p by (auto simp add: list_def nth_eq_iff_index_eq s_def)
  have thm_precond1: "(X \<union> {p ! i | i. i < length p \<and> even i}) - {p ! i | i. i < length p \<and> odd i} =
            insert (p ! 0) X - set (map fst list) \<union> set (map snd list)"
    using odds_are evens_are helper1 by auto
  have awalk_p: "awalk (A1 X \<union> A2 X) x (edges_of_vwalk p) y"
    by (simp add: vwalk_full vwalk_imp_awalk)
  have x_not_inX: "x \<in> carrier - X" using S_def xS by blast
  have y_not_inX: "y \<in> carrier - X" using T_def yT by blast
  have list_in_A1: "set list \<subseteq> A1 X"
    using walk_is_alternating[OF assms(1,2) awalk_p x_not_inX y_not_inX]
    by (force intro: alternating_list_odd_index
           simp add: edges_of_vwalk_length edges_of_vwalk_index[symmetric] list_def s_def)
  have edges_in_Gbar: "set (edges_of_vwalk p) \<subseteq> Gbar X"
    using assms(4) by (simp add: vwalk_bet_edges_in_edges)
  have list_edges: "\<And> i. i < length list \<Longrightarrow> list ! i = edges_of_vwalk p ! (2*i+1)"
    using odd_p by (simp add: edges_of_vwalk_index list_def s_def)
  have list_in_Gbar: "set list \<subseteq> Gbar X"
  proof
    fix e assume "e \<in> set list"
    then obtain i where i: "i < length list" "e = list ! i" by (metis in_set_conv_nth)
    have "2*i+1 < length (edges_of_vwalk p)"
      using i(1) odd_p by (simp add: edges_of_vwalk_length list_def s_def)
    thus "e \<in> Gbar X" using i list_edges edges_in_Gbar by (metis nth_mem subsetD)
  qed
  have A1A2_disj: "A1 X \<inter> A2 X = {}"
    using A1_edges(1)[OF assms(1,2)] A2_edges(2)[OF assms(1,2)] by fastforce
  have list_in_Abar1: "set list \<subseteq> Abar1 X"
    using list_in_A1 list_in_Gbar A1A2_disj by (auto simp add: Gbar_def Abar2_def Abar1_def)
  have tight1: "\<And> e. e \<in> set list \<Longrightarrow> c1 (fst e) = c1 (snd e)"
    using list_in_Abar1 by (auto simp add: Abar1_def)
  have fst_list_in_X: "set (map fst list) \<subseteq> X"
    using A1_edges(1)[OF assms(1,2)] list_in_A1 by auto
  have snd_list_not_in_X: "set (map snd list) \<subseteq> carrier - X"
    using A1_edges(2)[OF assms(1,2)] list_in_A1 by auto
  have thm_precond2: "set (map fst list) \<subseteq> insert (p ! 0) X" using fst_list_in_X by blast
  have helper3: "snd ` set list \<subseteq> carrier - X \<Longrightarrow> (a, p ! 0) \<in> set list \<Longrightarrow> False" for a
    using distinct_p nth_eq_iff_index_eq odd_p by (fastforce simp add: list_def s_def)
  have thm_precond3: "set (map snd list) \<subseteq> carrier - insert (p ! 0) X"
    using snd_list_not_in_X by (auto intro: helper3)
  have distinct_fst: "distinct (map fst list)"
    using distinct_p by (auto simp add: list_def s_def distinct_conv_nth nth_eq_iff_index_eq)
  have distinct_snd: "distinct (map snd list)"
    using distinct_p by (auto simp add: list_def s_def distinct_conv_nth nth_eq_iff_index_eq)
  have loA1: "\<And> b a. b \<in> carrier - X \<Longrightarrow> a \<in> matroid1.the_circuit (insert b X) - {b} \<Longrightarrow> c1 b \<le> c1 a"
    using conjunct1[OF assms(3)[unfolded matroid1.local_opt_def], rule_format] .
  have thm_precond4: "i < length list \<Longrightarrow>
      fst (list ! i) \<in> matroid1.the_circuit (insert (snd (list ! i)) (insert (p ! 0) X))
      \<and> c1 (fst (list ! i)) = c1 (snd (list ! i))" for i
  proof-
    assume i: "i < length list"
    have "fst (list ! i) \<in> matroid1.the_circuit (insert (snd (list ! i)) (insert (p ! 0) X))"
      using nth_mem[OF i] list_in_A1
      by(subst matroid1.same_cicuit_indep_part_extended[of "snd (list ! i)" X, OF _ X0])
        (force intro!: matroid1.the_circuit_non_empty_dependent simp add: A1_def)+
    moreover have "c1 (fst (list ! i)) = c1 (snd (list ! i))"
      using tight1[OF nth_mem[OF i]] .
    ultimately show "fst (list ! i) \<in> matroid1.the_circuit (insert (snd (list ! i)) (insert (p ! 0) X))
        \<and> c1 (fst (list ! i)) = c1 (snd (list ! i))" by simp
  qed
  have thm_precond5: "i < length list \<Longrightarrow> j < length list \<Longrightarrow> j < i \<Longrightarrow>
        fst (list ! j) \<notin> matroid1.the_circuit (insert (snd (list ! i)) (insert (p ! 0) X))
        \<or> c1 (fst (list ! j)) > c1 (snd (list ! i))" for i j
  proof(rule ccontr, simp only: de_Morgan_disj not_not not_less, goal_cases)
    case 1
    hence circ: "fst (list ! j) \<in> matroid1.the_circuit (insert (snd (list ! i)) (insert (p ! 0) X))"
      and cle: "c1 (fst (list ! j)) \<le> c1 (snd (list ! i))" by auto
    have fst_in_list: "fst (list ! j) \<in> set (map fst list)" using 1 by simp
    have j_length_p: "2 * j + 2 < length p" using 1 by(simp add: list_def s_def)
    have i_length_p: "2 * i + 2 < length p" using 1 by(simp add: list_def s_def)
    have list_j_is: "list ! j = (p ! (2*j+1), p ! (2*j + 2))" using 1 by(simp add: list_def s_def)
    have list_i_is: "list ! i = (p ! (2*i+1), p ! (2*i + 2))" using 1 by(simp add: list_def s_def)
    have non_indep_snd: "\<not> indep1 (insert (snd (list ! i)) X)"
      using list_in_A1 1(1) nth_mem
      by (force intro!: matroid1.the_circuit_non_empty_dependent simp add: A1_def)
    have snd_j_in_carrier: "snd (list ! i) \<in> carrier - X"
      using "1"(1) nth_mem thm_precond3 by fastforce
    have circuit_is: "matroid1.the_circuit (insert (snd (list ! i)) (insert (p ! 0) X)) =
              matroid1.the_circuit (insert (snd (list ! i)) X)"
      using snd_j_in_carrier
      by(auto intro!: matroid1.same_cicuit_indep_part_extended[OF non_indep_snd X0 _])
    have fst_not_snd: "snd (list ! i) \<noteq> fst (list ! j)"
      using fst_in_list fst_list_in_X snd_j_in_carrier by fastforce
    have found_edge_in: "(fst (list ! j), snd (list ! i)) \<in> A1 X"
      using circ snd_j_in_carrier fst_not_snd by (auto simp add: A1_def circuit_is)
    have cge: "c1 (snd (list ! i)) \<le> c1 (fst (list ! j))"
      using loA1[OF snd_j_in_carrier] circ fst_not_snd by (simp add: circuit_is)
    have ceq: "c1 (fst (list ! j)) = c1 (snd (list ! i))" using cle cge by simp
    have edge_Gbar: "(fst (list ! j), snd (list ! i)) \<in> Gbar X"
      using found_edge_in ceq by (simp add: Gbar_def Abar1_def)
    have "last (take (2*j + 2) p) = p ! (2*j+1)"
      using take_last[OF assms(1,2), of "2*j+1" p] j_length_p by simp
    hence walk_x_inter: "vwalk_bet (Gbar X) x (take (2*j + 2) p) (fst (list ! j))"
      using vwalk_bet_prefix_is_vwalk_bet[of "(take (2*j + 2) p)" "Gbar X" x "drop (2*j + 2) p" y]
        i_length_p assms(4) by (simp add: list_j_is)
    have "hd (drop (2 * i + 2) p) = snd (list ! i)"
      by(subst hd_drop_conv_nth[OF i_length_p])(simp add: list_i_is)
    hence vwalk_further: "vwalk_bet (Gbar X) (snd (list ! i)) (drop (2*i+2) p) y"
      using vwalk_bet_suffix_is_vwalk_bet[of "(drop (2*i + 2) p)" "Gbar X" x "take (2*i + 2) p" y]
            i_length_p assms(4) by auto
    have better_walk: "vwalk_bet (Gbar X) x (take (2*j + 2) p @ drop (2*i+2) p) y"
      using walk_x_inter edge_Gbar vwalk_further
      by (auto intro: vwalk_append_intermediate_edge)
    moreover have "length (take (2*j + 2) p @ drop (2*i+2) p) < length p"
      using j_length_p "1"(3) i_length_p by auto
    ultimately show ?case using assms(7) by auto
  qed
  have thm_precond6: "fst (list ! i) \<notin> matroid1.the_circuit (insert (snd (list ! j)) (insert (p ! 0) X))
        \<or> c1 (fst (list ! i)) \<ge> c1 (snd (list ! j))"
    if ij: "i < length list" "j < length list" "j < i" for i j
  proof(cases "fst (list ! i) \<in> matroid1.the_circuit (insert (snd (list ! j)) (insert (p ! 0) X))")
    case True
    have snd_in_carrier: "snd (list ! j) \<in> carrier - X"
      using ij(2) nth_mem thm_precond3 by fastforce
    have non_indep: "\<not> indep1 (insert (snd (list ! j)) X)"
      using list_in_A1 ij(2) nth_mem
      by (force intro!: matroid1.the_circuit_non_empty_dependent simp add: A1_def)
    have circuit_is: "matroid1.the_circuit (insert (snd (list ! j)) (insert (p ! 0) X)) =
              matroid1.the_circuit (insert (snd (list ! j)) X)"
      using snd_in_carrier
      by(auto intro!: matroid1.same_cicuit_indep_part_extended[OF non_indep X0 _])
    have fst_not_snd: "snd (list ! j) \<noteq> fst (list ! i)"
      using ij(1) nth_mem fst_list_in_X snd_in_carrier by fastforce
    have "c1 (snd (list ! j)) \<le> c1 (fst (list ! i))"
      using loA1[OF snd_in_carrier] True fst_not_snd by (simp add: circuit_is)
    thus ?thesis by simp
  qed simp
  show ?thesis
    using matroid1.weighted_single_matroid_augment[OF X0 thm_precond2 thm_precond3 refl
        distinct_fst distinct_snd thm_precond4 thm_precond5 thm_precond6 thm_precond1]
    by simp
qed

text \<open>Weighted analogue of @{thm [source] augment_in_matroid2}. The conditions of Lemma 13.35 are
established for the natural \<open>list\<close> and transferred to \<open>rev list\<close> by explicit \<open>rev_nth\<close> rewriting.\<close>
lemma weighted_augment_in_matroid2:
  assumes "indep1 X" "indep2 X" "matroid2.local_opt c2 X"
    "vwalk_bet (Gbar X) x p y" "x \<in> Sbar X" "y \<in> Tbar X"
    "\<nexists> q. vwalk_bet (Gbar X) x q y \<and> length q < length p"
  shows "indep2 ((X \<union> {p ! i | i. i < length p \<and> even i}) - {p ! i | i. i < length p \<and> odd i})"
proof-
  have xS: "x \<in> S X" using assms(5) Sbar_subset by blast
  have yT: "y \<in> T X" using assms(6) Tbar_subset by blast
  have vwalk_full: "vwalk_bet (A1 X \<union> A2 X) x p y"
    using assms(4) Gbar_subset by (meson vwalk_bet_subset)
  have p_non_empt: "p \<noteq> []" using assms(4) by auto
  have p_init: "p ! (length p - 1) = y"
    using assms(4) last_conv_nth[OF p_non_empt] by(auto simp add: vwalk_bet_def)
  have X0: "indep2 (insert (p ! (length p - 1)) X)" using yT p_init by(auto simp add: T_def)
  have odd_p: "odd (length p)"
    using xS yT by(intro walk_is_odd[OF assms(1,2) vwalk_full])(auto simp add: S_def T_def)
  have distinct_p: "distinct p" using shortest_vwalk_bet_distinct[OF assms(4,7)] .
  define s where "s = (length p - 1) div 2"
  define list where "list = [(p ! (2*i+1), p ! (2*i)). i <- [0..<s]]"
  have odds_are: "set (map fst list) = {p ! i | i. i < length p \<and> odd i}"
    using odd_p
    by (presburger |
        auto intro!: image_eqI[of "_ i" _ "(i - 1) div 2" for i] image_eqI[of "p ! i" fst for i]
        intro: less_mult_imp_div_less
        simp add: list_def s_def)+
  have evens_are: "set (map snd list) \<union> {p ! (length p - 1)} = {p ! i | i. i < length p \<and> even i}"
    using odd_p p_non_empt
    by (auto intro!: less_mult_imp_div_less diff_less_mono cong[OF refl, of _ _ "\<lambda> i. p ! i"]
                     image_eqI[of "_ i" _ "(i) div 2" for i]
                     image_eqI[of "p ! i" snd
                     "(p ! Suc (2 * ((i) div 2)), p ! (2 * ((i) div 2)))" for i]
          simp add: list_def s_def)
  have helper1: "i < length p \<Longrightarrow> odd i \<Longrightarrow> (a, p ! i) \<in> set list \<Longrightarrow> False" for i a
    using distinct_p by (auto simp add: list_def nth_eq_iff_index_eq s_def)
  have thm_precond1: "X \<union> {p ! i |i. i < length p \<and> even i} - {p ! i |i. i < length p \<and> odd i} =
    insert (p ! (length p - 1)) X - set (map fst (rev list)) \<union> set (map snd (rev list))"
    using odds_are evens_are helper1 by auto
  have awalk_p: "awalk (A1 X \<union> A2 X) x (edges_of_vwalk p) y"
    by (simp add: vwalk_full vwalk_imp_awalk)
  have x_not_inX: "x \<in> carrier - X" using S_def xS by blast
  have y_not_inX: "y \<in> carrier - X" using T_def yT by blast
  have list_in_A2: "set list \<subseteq> prod.swap ` A2 X" "set (map prod.swap list) \<subseteq> A2 X"
    using walk_is_alternating[OF assms(1,2) awalk_p x_not_inX y_not_inX]
    by (force intro: alternating_list_even_index
           simp add: edges_of_vwalk_length edges_of_vwalk_index[symmetric] list_def s_def)+
  have edges_in_Gbar: "set (edges_of_vwalk p) \<subseteq> Gbar X"
    using assms(4) by (simp add: vwalk_bet_edges_in_edges)
  have swap_list_edges: "\<And> i. i < length list \<Longrightarrow> prod.swap (list ! i) = edges_of_vwalk p ! (2*i)"
    using odd_p by (simp add: edges_of_vwalk_index list_def s_def)
  have swap_list_in_Gbar: "set (map prod.swap list) \<subseteq> Gbar X"
  proof
    fix e assume "e \<in> set (map prod.swap list)"
    then obtain i where i: "i < length list" "e = prod.swap (list ! i)"
      by (auto simp add: in_set_conv_nth)
    have "2*i < length (edges_of_vwalk p)"
      using i(1) odd_p by (simp add: edges_of_vwalk_length list_def s_def)
    thus "e \<in> Gbar X" using i swap_list_edges edges_in_Gbar by (metis nth_mem subsetD)
  qed
  have A1A2_disj: "A1 X \<inter> A2 X = {}"
    using A1_edges(1)[OF assms(1,2)] A2_edges(2)[OF assms(1,2)] by fastforce
  have swap_list_in_Abar2: "set (map prod.swap list) \<subseteq> Abar2 X"
    using list_in_A2(2) swap_list_in_Gbar A1A2_disj by (auto simp add: Gbar_def Abar1_def Abar2_def)
  have tight2: "\<And> i. i < length list \<Longrightarrow> c2 (fst (list ! i)) = c2 (snd (list ! i))"
    using swap_list_in_Abar2 by (fastforce simp add: Abar2_def in_set_conv_nth)
  have list_and_p: "set (map fst list) \<subseteq> set p" "set (map snd list) \<subseteq> set p"
    by(auto simp add: list_def s_def)
  have fst_list_in_X: "set (map fst list) \<subseteq> X"
    using list_in_A2 by(force intro: A2_single_edge_endpoints_X_carrier(1)[OF assms(1,2)])
  have snd_list_not_in_X: "set (map snd list) \<subseteq> carrier - X"
    using list_in_A2 by(force dest: A2_single_edge_endpoints_X_carrier(2)[OF assms(1,2)])
  have set_rev_fst: "set (map fst (rev list)) = set (map fst list)" by simp
  have set_rev_snd: "set (map snd (rev list)) = set (map snd list)" by simp
  have thm_precond2: "set (map fst (rev list)) \<subseteq> insert (p ! (length p - 1)) X"
    using fst_list_in_X set_rev_fst by blast
  have helper3: "snd ` set list \<subseteq> carrier - X \<Longrightarrow> (a, p ! (length p - 1)) \<in> set list \<Longrightarrow> False" for a
    using distinct_p nth_eq_iff_index_eq odd_p by (fastforce simp add: list_def s_def)
  have thm_precond3: "set (map snd (rev list)) \<subseteq> carrier - insert (p ! (length p - 1)) X"
    using snd_list_not_in_X set_rev_snd by (auto intro: helper3)
  have distinct_fst_list: "distinct (map fst list)"
    using distinct_p by (auto simp add: list_def s_def distinct_conv_nth nth_eq_iff_index_eq)
  have distinct_snd_list: "distinct (map snd list)"
    using distinct_p by (auto simp add: list_def s_def distinct_conv_nth nth_eq_iff_index_eq)
  have distinct_fst: "distinct (map fst (rev list))"
    using distinct_fst_list by (simp add: rev_map[symmetric])
  have distinct_snd: "distinct (map snd (rev list))"
    using distinct_snd_list by (simp add: rev_map[symmetric])
  have loA2: "\<And> b a. b \<in> carrier - X \<Longrightarrow> a \<in> matroid2.the_circuit (insert b X) - {b} \<Longrightarrow> c2 b \<le> c2 a"
    using conjunct1[OF assms(3)[unfolded matroid2.local_opt_def], rule_format] .
  have circ4: "fst (list ! i) \<in> matroid2.the_circuit (insert (snd (list ! i)) (insert (p ! (length p - 1)) X))"
    if i: "i < length list" for i
  proof-
    have "list ! i \<in> prod.swap ` A2 X" using i list_in_A2(1) by (simp add: nth_mem subsetD)
    then obtain xx yy where lxy: "list ! i = (xx, yy)" "yy \<in> carrier - X"
        "xx \<in> matroid2.the_circuit (insert yy X) - {yy}"
      by (auto simp add: A2_def)
    hence circX: "fst (list ! i) \<in> matroid2.the_circuit (insert (snd (list ! i)) X)" by simp
    have ndep: "\<not> indep2 (insert (snd (list ! i)) X)"
      using circX matroid2.the_circuit_non_empty_dependent by auto
    have "matroid2.the_circuit (insert (snd (list ! i)) (insert (p ! (length p - 1)) X)) =
          matroid2.the_circuit (insert (snd (list ! i)) X)"
      using lxy by (intro matroid2.same_cicuit_indep_part_extended[OF ndep X0]) auto
    thus ?thesis using circX by simp
  qed
  \<comment> \<open>transfer condition (a) to the reversed list\<close>
  have thm_precond4: "fst (rev list ! i) \<in> matroid2.the_circuit (insert (snd (rev list ! i)) (insert (p ! (length p - 1)) X))
      \<and> c2 (fst (rev list ! i)) = c2 (snd (rev list ! i))"
    if i: "i < length (rev list)" for i
  proof-
    have il: "i < length list" using i by simp
    have ei: "rev list ! i = list ! (length list - 1 - i)" using il by (simp add: rev_nth)
    have ai: "length list - 1 - i < length list" using il by auto
    show ?thesis using circ4[OF ai] tight2[OF ai] ei by simp
  qed 
  \<comment> \<open>condition (b) for the natural list, from a \<open>Gbar\<close>-shortcut\<close>
  have precond5_list: "fst (list ! j) \<notin> matroid2.the_circuit (insert (snd (list ! i)) (insert (p ! (length p - 1)) X))
        \<or> c2 (fst (list ! j)) > c2 (snd (list ! i))"
    if ij: "i < length list" "j < length list" "i < j" for i j
  proof(cases "fst (list ! j) \<in> matroid2.the_circuit (insert (snd (list ! i)) (insert (p ! (length p - 1)) X))")
    case False thus ?thesis by simp
  next
    case True
    have j_length_p: "2 * j + 1 < length p" using ij by(simp add: list_def s_def)
    have i_length_p: "2 * i < length p" using ij by(simp add: list_def s_def)
    have list_j_is: "list ! j = (p ! (2*j+1), p ! (2*j))" using ij by(simp add: list_def s_def)
    have list_i_is: "list ! i = (p ! (2*i+1), p ! (2*i))" using ij by(simp add: list_def s_def)
    have snd_i_in_carrier: "snd (list ! i) \<in> carrier - X"
      using ij(1) snd_list_not_in_X by (metis length_map nth_map nth_mem subsetD)
    have fst_j_in_X: "fst (list ! j) \<in> X"
      using ij(2) fst_list_in_X by (metis length_map nth_map nth_mem subsetD)
    have non_indep_snd: "\<not> indep2 (insert (snd (list ! i)) X)"
      using list_in_A2(1) ij(1) nth_mem
      by (force intro!: matroid2.the_circuit_non_empty_dependent simp add: A2_def)
    have circuit_is: "matroid2.the_circuit (insert (snd (list ! i)) (insert (p ! (length p - 1)) X)) =
              matroid2.the_circuit (insert (snd (list ! i)) X)"
      using snd_i_in_carrier matroid2.same_cicuit_indep_part_extended[OF non_indep_snd X0 _] by auto
    have fst_not_snd: "snd (list ! i) \<noteq> fst (list ! j)"
      using fst_j_in_X snd_i_in_carrier by auto
    have found_edge_in: "(snd (list ! i), fst (list ! j)) \<in> A2 X"
      using True snd_i_in_carrier fst_not_snd unfolding A2_def circuit_is by auto
    have cge: "c2 (snd (list ! i)) \<le> c2 (fst (list ! j))"
    proof-
      have "fst (list ! j) \<in> matroid2.the_circuit (insert (snd (list ! i)) X) - {snd (list ! i)}"
        using True[unfolded circuit_is] fst_not_snd by simp
      thus ?thesis by (rule loA2[OF snd_i_in_carrier])
    qed
    have "c2 (fst (list ! j)) \<noteq> c2 (snd (list ! i))"
    proof
      assume ceq: "c2 (fst (list ! j)) = c2 (snd (list ! i))"
      have edge_Gbar: "(snd (list ! i), fst (list ! j)) \<in> Gbar X"
        using found_edge_in ceq by (simp add: Gbar_def Abar2_def)
      have "last (take (2*i + 1) p) = p ! (2*i)"
        using take_last[OF assms(1,2), of "2*i" p] i_length_p by simp
      hence walk_x_inter: "vwalk_bet (Gbar X) x (take (2*i + 1) p) (snd (list ! i))"
        using vwalk_bet_prefix_is_vwalk_bet[of "(take (2*i + 1) p)" "Gbar X" x "drop (2*i + 1) p" y]
          i_length_p assms(4) by (simp add: list_i_is)
      have "hd (drop (2 * j + 1) p) = fst (list ! j)"
        using hd_drop_conv_nth[OF j_length_p] by(auto simp add: list_j_is)
      hence vwalk_further: "vwalk_bet (Gbar X) (fst (list ! j)) (drop (2*j+1) p) y"
        using vwalk_bet_suffix_is_vwalk_bet[of "(drop (2*j + 1) p)" "Gbar X" x "take (2*j + 1) p" y]
          j_length_p assms(4) by auto
      have "vwalk_bet (Gbar X) x (take (2*i + 1) p @ drop (2*j+1) p) y"
        using walk_x_inter edge_Gbar vwalk_further by (auto intro: vwalk_append_intermediate_edge)
      moreover have "length (take (2*i + 1) p @ drop (2*j+1) p) < length p"
        using j_length_p ij(3) i_length_p by auto
      ultimately show False using assms(7) by auto
    qed
    hence "c2 (fst (list ! j)) > c2 (snd (list ! i))" using cge by simp
    thus ?thesis by simp
  qed
  \<comment> \<open>transfer condition (b) to the reversed list\<close>
  have thm_precond5: "fst (rev list ! j) \<notin> matroid2.the_circuit (insert (snd (rev list ! i)) (insert (p ! (length p - 1)) X))
        \<or> c2 (fst (rev list ! j)) > c2 (snd (rev list ! i))"
    if ij: "i < length (rev list)" "j < length (rev list)" "j < i" for i j
  proof-
    have il: "i < length list" and jl: "j < length list" using ij by simp+
    have ei: "rev list ! i = list ! (length list - 1 - i)" using il by (simp add: rev_nth)
    have ej: "rev list ! j = list ! (length list - 1 - j)" using jl by (simp add: rev_nth)
    have ai: "length list - 1 - i < length list" using il by auto
    have bj: "length list - 1 - j < length list" using jl by auto
    have ab: "length list - 1 - i < length list - 1 - j" using ij(3) il by auto
    show ?thesis using precond5_list[OF ai bj ab] ei ej by simp
  qed
  \<comment> \<open>condition (c) is immediate from local optimality of X in matroid 2\<close>
  have thm_precond6: "fst (rev list ! i) \<notin> matroid2.the_circuit (insert (snd (rev list ! j)) (insert (p ! (length p - 1)) X))
        \<or> c2 (fst (rev list ! i)) \<ge> c2 (snd (rev list ! j))"
    if ij: "i < length (rev list)" "j < length (rev list)" "j < i" for i j
  proof(cases "fst (rev list ! i) \<in> matroid2.the_circuit (insert (snd (rev list ! j)) (insert (p ! (length p - 1)) X))")
    case False thus ?thesis by simp
  next
    case True
    have "rev list ! j \<in> prod.swap ` A2 X"
      using ij(2) list_in_A2(1) by (metis nth_mem set_rev subsetD)
    then obtain xx yy where lxy: "rev list ! j = (xx, yy)" "yy \<in> carrier - X"
        "xx \<in> matroid2.the_circuit (insert yy X) - {yy}"
      by (auto simp add: A2_def)
    have snd_in_carrier: "snd (rev list ! j) \<in> carrier - X" using lxy by simp
    have ndep: "\<not> indep2 (insert (snd (rev list ! j)) X)"
      using lxy matroid2.the_circuit_non_empty_dependent by auto
    have circuit_is: "matroid2.the_circuit (insert (snd (rev list ! j)) (insert (p ! (length p - 1)) X)) =
              matroid2.the_circuit (insert (snd (rev list ! j)) X)"
      using snd_in_carrier by (intro matroid2.same_cicuit_indep_part_extended[OF ndep X0]) auto
    have fst_in_X: "fst (rev list ! i) \<in> X"
      using ij(1) fst_list_in_X set_rev_fst by (metis length_map nth_map nth_mem subsetD)
    have fst_not_snd: "snd (rev list ! j) \<noteq> fst (rev list ! i)"
      using fst_in_X snd_in_carrier by auto
    have "c2 (snd (rev list ! j)) \<le> c2 (fst (rev list ! i))"
    proof-
      have "fst (rev list ! i) \<in> matroid2.the_circuit (insert (snd (rev list ! j)) X) - {snd (rev list ! j)}"
        using True[unfolded circuit_is] fst_not_snd by simp
      thus ?thesis by (rule loA2[OF snd_in_carrier])
    qed
    thus ?thesis by simp
  qed
  have "indep2 (insert (p ! (length p - 1)) X - set (map fst (rev list)) \<union> set (map snd (rev list)))"
    using matroid2.weighted_single_matroid_augment[OF X0 thm_precond2 thm_precond3 refl
        distinct_fst distinct_snd thm_precond4 thm_precond5 thm_precond6 refl] .
  thus ?thesis using thm_precond1 by simp
qed

text \<open>C5: a shortest tight \<open>Sbar\<close>-\<open>Tbar\<close> path preserves common independence and the per-matroid local
optimality while raising the cardinality by one (weighted analogue of
@{thm [source] augment_in_both_matroids}).\<close>
lemma augment_tight_path:
  assumes "indep1 X" "indep2 X" "matroid1.local_opt c1 X" "matroid2.local_opt c2 X"
    "vwalk_bet (Gbar X) u p v" "u \<in> Sbar X" "v \<in> Tbar X"
    "\<nexists> q. vwalk_bet (Gbar X) u q v \<and> length q < length p"
    "X' = (X \<union> {p ! i | i. i < length p \<and> even i}) - {p ! i | i. i < length p \<and> odd i}"
  shows "indep1 X'" "indep2 X'" "card X' = card X + 1"
    "matroid1.local_opt c1 X'" "matroid2.local_opt c2 X'"
    "sum c1 X' = sum c1 X + c1 u" "sum c2 X' = sum c2 X + c2 v"
proof-
  have xS: "u \<in> S X" using assms(6) Sbar_subset by blast
  have yT: "v \<in> T X" using assms(7) Tbar_subset by blast
  have vwalk_full: "vwalk_bet (A1 X \<union> A2 X) u p v"
    using assms(5) Gbar_subset by (meson vwalk_bet_subset)
  have awalk: "awalk (A1 X \<union> A2 X) u (edges_of_vwalk p) v"
    using vwalk_full by(auto intro!: vwalk_imp_awalk)
  have x_in_carrier: "u \<in> carrier - X" using S_def xS by blast
  have y_in_carrier: "v \<in> carrier - X" using T_def yT by blast
  have alternation: "even (length (edges_of_vwalk p))"
    "(\<And> i. i<length (edges_of_vwalk p) \<Longrightarrow> even i \<Longrightarrow> edges_of_vwalk p ! i \<in> A2 X)"
    "\<And> i. i<length (edges_of_vwalk p) \<Longrightarrow> odd i \<Longrightarrow> edges_of_vwalk p ! i \<in> A1 X"
    by(auto intro: alternating_list_even_index[OF
           walk_is_alternating[OF assms(1,2) awalk x_in_carrier y_in_carrier]]
                      alternating_list_odd_index[OF
           walk_is_alternating[OF assms(1,2) awalk x_in_carrier y_in_carrier]]
            simp add: walk_is_even[OF assms(1,2) awalk x_in_carrier y_in_carrier])
  have odd_in_X: "{p ! i | i. i < length p \<and> odd i} \<subseteq> X"
      using alternation(1)[simplified edges_of_vwalk_length]
      by(intro  forw_subst[ of "p!i" "fst (p ! i, p ! Suc i)" "\<lambda> x. x \<in> X" for i,
                              OF fst_conv[symmetric]]|
         subst edges_of_vwalk_index[of _ p, symmetric]|
         presburger |
         auto intro!: A1_edges(1)[OF assms(1,2) alternating_list_odd_index[OF
                          walk_is_alternating[OF assms(1,2) awalk x_in_carrier y_in_carrier],
                                simplified edges_of_vwalk_length]]
         simp add: edges_of_vwalk_index[of _ p, symmetric])+
  have even_not_in_X: "a \<in> {p ! i | i. i < length p \<and> even i} \<Longrightarrow> a \<notin> X" for a
  proof( goal_cases)
    case 1
    then obtain i where i_prop:"i < length p" "even i" "p ! i = a" by auto
    show ?case
    proof(cases "i = length p -1")
      case True
      hence "a = v" using vwalk_full i_prop(3) last_conv_nth
        by(force simp add: vwalk_bet_def)
      then show ?thesis
        using yT by(simp add: T_def)
    next
      case False
      have p_edge_is: " (p ! i, p ! (i+1)) = edges_of_vwalk p ! i"
        using edges_of_vwalk_index[of "i" p] i_prop  False by auto
      have "(p ! i, p ! (i+1)) \<in> A2 X"
        using False
        by(subst  p_edge_is)
          (auto intro!: alternation(2)[simplified edges_of_vwalk_length]
            simp add: i_prop(1) i_prop(2) less_diff_conv Suc_lessI)
      then show ?thesis
        using i_prop(3) A2_edges(1)[OF assms(1,2)] by (auto simp add: A2_def)
    qed
  qed
  have distinct_p: "distinct p"
    by (rule shortest_vwalk_bet_distinct[OF assms(5) assms(8)])
  have p_non_empt:"p \<noteq> []"
    using vwalk_full by auto
  have odd_p: "odd (length p )"
    using  alternation(1) p_non_empt by (simp add: edges_of_vwalk_length)
  have card_even:"card {p ! i |i. i < length p \<and> even i} = length p div 2 + 1"
    by(subst setcompr_eq_image, subst card_image)
      (auto intro: inj_on_nth[OF distinct_p] simp add: card_of_evens_under_odd[OF assms(1,2) odd_p])
  have card_odd:"card {p ! i |i. i < length p \<and> odd i} = length p div 2"
    by(subst setcompr_eq_image, subst card_image)
      (auto intro: inj_on_nth[OF distinct_p] simp add: card_of_odds_under_odd[OF assms(1,2) odd_p])
  have disjnt: "disjnt X {p ! i |i. i < length p \<and> even i}"
    using even_not_in_X by(fastforce simp add: disjnt_def)
  have edges_in_Gbar: "set (edges_of_vwalk p) \<subseteq> Gbar X"
    using assms(5) by (simp add: vwalk_bet_edges_in_edges)
  have A1A2_disj: "A1 X \<inter> A2 X = {}"
    using A1_edges(1)[OF assms(1,2)] A2_edges(2)[OF assms(1,2)] by fastforce
  have tight_c1: "\<And>i. i < length p \<Longrightarrow> odd i \<Longrightarrow> c1 (p ! i) = c1 (p ! Suc i)"
  proof-
    fix i assume i: "i < length p" "odd i"
    have suc_lt: "Suc i < length p" using i odd_p by presburger
    have ilen: "i < length (edges_of_vwalk p)" using suc_lt by (simp add: edges_of_vwalk_length)
    have e_Gbar: "edges_of_vwalk p ! i \<in> Gbar X" using edges_in_Gbar nth_mem[OF ilen] by blast
    have e_A1: "edges_of_vwalk p ! i \<in> A1 X" using alternation(3)[OF ilen i(2)] .
    have "edges_of_vwalk p ! i \<in> Abar1 X"
      using e_A1 e_Gbar A1A2_disj by (auto simp add: Gbar_def Abar1_def Abar2_def)
    hence "c1 (fst (edges_of_vwalk p ! i)) = c1 (snd (edges_of_vwalk p ! i))" by (simp add: Abar1_def)
    thus "c1 (p ! i) = c1 (p ! Suc i)" using edges_of_vwalk_index[OF suc_lt] by simp
  qed
  have tight_c2: "\<And>i. Suc i < length p \<Longrightarrow> even i \<Longrightarrow> c2 (p ! i) = c2 (p ! Suc i)"
  proof-
    fix i assume i: "Suc i < length p" "even i"
    have ilen: "i < length (edges_of_vwalk p)" using i(1) by (simp add: edges_of_vwalk_length)
    have e_Gbar: "edges_of_vwalk p ! i \<in> Gbar X" using edges_in_Gbar nth_mem[OF ilen] by blast
    have e_A2: "edges_of_vwalk p ! i \<in> A2 X" using alternation(2)[OF ilen i(2)] .
    have "edges_of_vwalk p ! i \<in> Abar2 X"
      using e_A2 e_Gbar A1A2_disj by (auto simp add: Gbar_def Abar1_def Abar2_def)
    hence "c2 (fst (edges_of_vwalk p ! i)) = c2 (snd (edges_of_vwalk p ! i))" by (simp add: Abar2_def)
    thus "c2 (p ! i) = c2 (p ! Suc i)" using edges_of_vwalk_index[OF i(1)] by simp
  qed
  have finX: "finite X" using assms(1) matroid1.indep_finite by simp
  have finE1: "finite {p ! i | i. i < length p \<and> even i}"
    by (rule finite_subset[of _ "set p"]) (auto intro: nth_mem)
  have finO1: "finite {p ! i | i. i < length p \<and> odd i}"
    by (rule finite_subset[of _ "set p"]) (auto intro: nth_mem)
  have evens_disjX: "X \<inter> {p ! i | i. i < length p \<and> even i} = {}"
    using even_not_in_X by auto
  have inj_even: "inj_on (\<lambda>i. p ! i) {i. i < length p \<and> even i}"
    by (rule inj_on_nth[OF distinct_p]) auto
  have inj_odd: "inj_on (\<lambda>i. p ! i) {i. i < length p \<and> odd i}"
    by (rule inj_on_nth[OF distinct_p]) auto
  have re_even1: "sum c1 {p ! i | i. i < length p \<and> even i}
                    = sum (\<lambda>i. c1 (p ! i)) {i. i < length p \<and> even i}"
    using sum.reindex[OF inj_even, of c1] by (simp add: setcompr_eq_image o_def)
  have re_odd1: "sum c1 {p ! i | i. i < length p \<and> odd i}
                   = sum (\<lambda>i. c1 (p ! i)) {i. i < length p \<and> odd i}"
    using sum.reindex[OF inj_odd, of c1] by (simp add: setcompr_eq_image o_def)
  have re_even2: "sum c2 {p ! i | i. i < length p \<and> even i}
                    = sum (\<lambda>i. c2 (p ! i)) {i. i < length p \<and> even i}"
    using sum.reindex[OF inj_even, of c2] by (simp add: setcompr_eq_image o_def)
  have re_odd2: "sum c2 {p ! i | i. i < length p \<and> odd i}
                   = sum (\<lambda>i. c2 (p ! i)) {i. i < length p \<and> odd i}"
    using sum.reindex[OF inj_odd, of c2] by (simp add: setcompr_eq_image o_def)
  have telescope_c1: "sum c1 {p ! i | i. i < length p \<and> even i}
                       = sum c1 {p ! i | i. i < length p \<and> odd i} + c1 (p ! 0)"
    using sum_evens_odds_tight[where g="\<lambda>i. c1 (p ! i)", OF odd_p tight_c1] re_even1 re_odd1 by simp
  have telescope_c2: "sum c2 {p ! i | i. i < length p \<and> even i}
                       = sum c2 {p ! i | i. i < length p \<and> odd i} + c2 (p ! (length p - 1))"
    using sum_evens_odds_tight2[where g="\<lambda>i. c2 (p ! i)", OF odd_p tight_c2] re_even2 re_odd2 by simp
  have sub1: "{p ! i | i. i < length p \<and> odd i} \<subseteq> X \<union> {p ! i | i. i < length p \<and> even i}"
    using odd_in_X by auto
  have fin_un1: "finite (X \<union> {p ! i | i. i < length p \<and> even i})" using finX finE1 by simp
  have sumX'_c1: "sum c1 X' = sum c1 X + c1 (p ! 0)"
  proof-
    have e1: "sum c1 (X \<union> {p ! i | i. i < length p \<and> even i})
                = sum c1 X' + sum c1 {p ! i | i. i < length p \<and> odd i}"
      using sum.subset_diff[OF sub1 fin_un1] by (simp add: assms(9))
    have e2: "sum c1 (X \<union> {p ! i | i. i < length p \<and> even i})
                = sum c1 X + sum c1 {p ! i | i. i < length p \<and> even i}"
      using sum.union_disjoint[OF finX finE1 evens_disjX] .
    from e1 e2 have "sum c1 X' + sum c1 {p ! i | i. i < length p \<and> odd i}
                       = sum c1 X + sum c1 {p ! i | i. i < length p \<and> even i}" by simp
    thus ?thesis using telescope_c1 by (simp add: algebra_simps)
  qed
  have sumX'_c2: "sum c2 X' = sum c2 X + c2 (p ! (length p - 1))"
  proof-
    have e1: "sum c2 (X \<union> {p ! i | i. i < length p \<and> even i})
                = sum c2 X' + sum c2 {p ! i | i. i < length p \<and> odd i}"
      using sum.subset_diff[OF sub1 fin_un1] by (simp add: assms(9))
    have e2: "sum c2 (X \<union> {p ! i | i. i < length p \<and> even i})
                = sum c2 X + sum c2 {p ! i | i. i < length p \<and> even i}"
      using sum.union_disjoint[OF finX finE1 evens_disjX] .
    from e1 e2 have "sum c2 X' + sum c2 {p ! i | i. i < length p \<and> odd i}
                       = sum c2 X + sum c2 {p ! i | i. i < length p \<and> even i}" by simp
    thus ?thesis using telescope_c2 by (simp add: algebra_simps)
  qed
  have indep1X': "indep1 X'"
    using weighted_augment_in_matroid1[OF assms(1,2,3,5,6,7,8)] by (simp add: assms(9))
  have indep2X': "indep2 X'"
    using weighted_augment_in_matroid2[OF assms(1,2,4,5,6,7,8)] by (simp add: assms(9))
  have cardX': "card X' = card X + 1"
    using odd_in_X disjnt card_even card_odd
    by (subst assms(9), subst card_Diff_subset)
      (auto simp add:  card_Un_disjnt diff_add_assoc assms(1) matroid1.indep_finite[OF assms(1)])
  have loc1: "matroid1.local_opt c1 X'"
  proof-
    have p_init: "p ! 0 = u"
    proof-
      have "hd p = u" using assms(5) by (simp add: vwalk_bet_def)
      thus ?thesis using hd_conv_nth[OF p_non_empt] by simp
    qed
    have indep1_u: "indep1 (insert u X)" using xS by (simp add: S_def)
    have cmax: "c1 u = Max (c1 ` {y \<in> carrier - X. indep1 (insert y X)})"
      using assms(6) by (simp add: Sbar_def S_def)
    have lo_insert: "matroid1.local_opt c1 (insert u X)"
      using matroid1.greedy_extension[OF assms(1,3) x_in_carrier indep1_u cmax] .
    have maxw_insert: "matroid1.max_weight_card c1 (insert u X)"
      using matroid1.greedy_optimality[OF indep1_u] lo_insert by blast
    have unX: "u \<notin> X" using x_in_carrier by simp
    have card_insert: "card (insert u X) = card X + 1" using unX finX by simp
    have sum_insert: "sum c1 (insert u X) = sum c1 X + c1 u"
      using sum.insert[OF finX unX] by (simp add: add.commute)
    have sumX'_eq: "sum c1 X' = sum c1 (insert u X)"
      using sumX'_c1 sum_insert p_init by simp
    have "matroid1.max_weight_card c1 X'"
      unfolding matroid1.max_weight_card_def
    proof(intro allI impI)
      fix Z assume "indep1 Z \<and> card Z = card X'"
      hence Zi: "indep1 Z" and Zc: "card Z = card X'" by auto
      have "card Z = card (insert u X)" using Zc cardX' card_insert by simp
      hence "sum c1 Z \<le> sum c1 (insert u X)"
        using maxw_insert[unfolded matroid1.max_weight_card_def] Zi by blast
      thus "sum c1 Z \<le> sum c1 X'" using sumX'_eq by simp
    qed
    thus ?thesis using matroid1.greedy_optimality[OF indep1X'] by blast
  qed
  have loc2: "matroid2.local_opt c2 X'"
  proof-
    have p_last: "p ! (length p - 1) = v"
    proof-
      have "last p = v" using assms(5) by (simp add: vwalk_bet_def)
      thus ?thesis using last_conv_nth[OF p_non_empt] by simp
    qed
    have indep2_v: "indep2 (insert v X)" using yT by (simp add: T_def)
    have cmax2: "c2 v = Max (c2 ` {y \<in> carrier - X. indep2 (insert y X)})"
      using assms(7) by (simp add: Tbar_def T_def)
    have lo_insert2: "matroid2.local_opt c2 (insert v X)"
      using matroid2.greedy_extension[OF assms(2,4) y_in_carrier indep2_v cmax2] .
    have maxw_insert2: "matroid2.max_weight_card c2 (insert v X)"
      using matroid2.greedy_optimality[OF indep2_v] lo_insert2 by blast
    have vnX: "v \<notin> X" using y_in_carrier by simp
    have card_insert2: "card (insert v X) = card X + 1" using vnX finX by simp
    have sum_insert2: "sum c2 (insert v X) = sum c2 X + c2 v"
      using sum.insert[OF finX vnX] by (simp add: add.commute)
    have sumX'_eq2: "sum c2 X' = sum c2 (insert v X)"
      using sumX'_c2 sum_insert2 p_last by simp
    have "matroid2.max_weight_card c2 X'"
      unfolding matroid2.max_weight_card_def
    proof(intro allI impI)
      fix Z assume "indep2 Z \<and> card Z = card X'"
      hence Zi: "indep2 Z" and Zc: "card Z = card X'" by auto
      have "card Z = card (insert v X)" using Zc cardX' card_insert2 by simp
      hence "sum c2 Z \<le> sum c2 (insert v X)"
        using maxw_insert2[unfolded matroid2.max_weight_card_def] Zi by blast
      thus "sum c2 Z \<le> sum c2 X'" using sumX'_eq2 by simp
    qed
    thus ?thesis using matroid2.greedy_optimality[OF indep2X'] by blast
  qed
  show "indep1 X'" using indep1X' .
  show "indep2 X'" using indep2X' .
  show "card X' = card X + 1" using cardX' .
  show "matroid1.local_opt c1 X'" using loc1 .
  show "matroid2.local_opt c2 X'" using loc2 .
  show "sum c1 X' = sum c1 X + c1 u"
    using sumX'_c1 hd_conv_nth[OF p_non_empt] assms(5) by (simp add: vwalk_bet_def)
  show "sum c2 X' = sum c2 X + c2 v"
    using sumX'_c2 last_conv_nth[OF p_non_empt] assms(5) by (simp add: vwalk_bet_def)
qed

end

text \<open>Two purely mathematical facts feeding the termination argument of the weighted algorithm. Both
concern the reweighting step \<open>c \<mapsto> (\<lambda>z. if z \<in> R then c z - \<epsilon> else c z)\<close>. They are stated at the
function level here (rather than at the executable data-structure level) so that the plain and the
circuit variant of the algorithm can share them.\<close>

text \<open>Shifting the weight down by \<open>\<epsilon>\<close> on \<open>R\<close> lowers the maximum by exactly \<open>\<epsilon>\<close>, provided every element
outside \<open>R\<close> is at least \<open>\<epsilon>\<close> below the maximum and the argmax lies in \<open>R\<close>: the old argmax drops to
\<open>Max - \<epsilon>\<close> and everything else stays \<open>\<le> Max - \<epsilon>\<close>.\<close>
lemma argmax_reweight_newmax:
  fixes c :: "'a \<Rightarrow> 'b :: linordered_ab_group_add"
  assumes "finite V" "V \<noteq> {}" "0 < e"
    and gap: "\<And>y. y \<in> V \<Longrightarrow> y \<notin> R \<Longrightarrow> c y \<le> Max (c ` V) - e"
    and argR: "\<And>y. y \<in> V \<Longrightarrow> c y = Max (c ` V) \<Longrightarrow> y \<in> R"
  shows "Max ((\<lambda>z. if z \<in> R then c z - e else c z) ` V) = Max (c ` V) - e"
proof -
  let ?m = "Max (c ` V)"
  let ?c' = "\<lambda>z. if z \<in> R then c z - e else c z"
  have fin: "finite (c ` V)" using assms(1) by simp
  have ne: "c ` V \<noteq> {}" using assms(2) by simp
  have le_all: "\<And>y. y \<in> V \<Longrightarrow> ?c' y \<le> ?m - e"
  proof -
    fix y assume yV: "y \<in> V"
    have "c y \<in> c ` V" by (rule imageI[OF yV])
    hence "c y \<le> ?m" using Max_ge[OF fin] by simp
    thus "?c' y \<le> ?m - e" using gap[OF yV] by auto
  qed
  obtain z where z: "z \<in> V" "c z = ?m" using Max_in[OF fin ne] by auto
  have zR: "z \<in> R" using argR[OF z(1)] z(2) by simp
  have zval: "?c' z = ?m - e" using zR z(2) by simp
  have zmem: "?c' z \<in> ?c' ` V" by (rule imageI[OF z(1)])
  show "Max (?c' ` V) = ?m - e"
  proof (intro Max_eqI)
    show "finite (?c' ` V)" using assms(1) by simp
    show "?m - e \<in> ?c' ` V" using zmem zval by simp
    fix a assume "a \<in> ?c' ` V"
    then obtain x where x: "x \<in> V" "a = ?c' x" by auto
    show "a \<le> ?m - e" unfolding x(2) by (rule le_all[OF x(1)])
  qed
qed

text \<open>Hence the set of maximisers only enlarges: the old maximisers (all in \<open>R\<close>) drop to the new
maximum \<open>Max - \<epsilon>\<close>.\<close>
lemma argmax_reweight_mono:
  fixes c :: "'a \<Rightarrow> 'b :: linordered_ab_group_add"
  assumes "finite V" "0 < e"
    and gap: "\<And>y. y \<in> V \<Longrightarrow> y \<notin> R \<Longrightarrow> c y \<le> Max (c ` V) - e"
    and argR: "\<And>y. y \<in> V \<Longrightarrow> c y = Max (c ` V) \<Longrightarrow> y \<in> R"
  shows "{y \<in> V. c y = Max (c ` V)}
         \<subseteq> {y \<in> V. (\<lambda>z. if z \<in> R then c z - e else c z) y
                     = Max ((\<lambda>z. if z \<in> R then c z - e else c z) ` V)}"
proof (cases "V = {}")
  case True thus ?thesis by simp
next
  case False
  let ?c' = "\<lambda>z. if z \<in> R then c z - e else c z"
  have mmax: "Max (?c' ` V) = Max (c ` V) - e"
    by (rule argmax_reweight_newmax[OF assms(1) False assms(2) gap argR])
  show ?thesis
  proof
    fix y assume "y \<in> {y \<in> V. c y = Max (c ` V)}"
    hence yV: "y \<in> V" and ym: "c y = Max (c ` V)" by auto
    have "y \<in> R" using argR[OF yV] ym by simp
    hence "?c' y = Max (c ` V) - e" using ym by simp
    thus "y \<in> {y \<in> V. ?c' y = Max (?c' ` V)}" using yV mmax by simp
  qed
qed

text \<open>The dual increase step: raising the weight by \<open>\<epsilon>\<close> on \<open>R\<close> leaves the maximum unchanged, provided the
\<open>R\<close>-elements are all at least \<open>\<epsilon>\<close> below it and the maximisers lie outside \<open>R\<close> (so they keep their value).
Used for the \<open>T\<close>-endpoint case, where an unreachable maximiser pins the maximum.\<close>
lemma argmax_reweight_keepmax:
  fixes c :: "'a \<Rightarrow> 'b :: linordered_ab_group_add"
  assumes "finite V" "V \<noteq> {}" "0 < e"
    and gap: "\<And>y. y \<in> V \<Longrightarrow> y \<in> R \<Longrightarrow> c y \<le> Max (c ` V) - e"
    and argNR: "\<And>y. y \<in> V \<Longrightarrow> c y = Max (c ` V) \<Longrightarrow> y \<notin> R"
  shows "Max ((\<lambda>z. if z \<in> R then c z + e else c z) ` V) = Max (c ` V)"
proof -
  let ?m = "Max (c ` V)"
  let ?c' = "\<lambda>z. if z \<in> R then c z + e else c z"
  have fin: "finite (c ` V)" using assms(1) by simp
  have ne: "c ` V \<noteq> {}" using assms(2) by simp
  have le_all: "\<And>y. y \<in> V \<Longrightarrow> ?c' y \<le> ?m"
  proof -
    fix y assume yV: "y \<in> V"
    show "?c' y \<le> ?m"
    proof (cases "y \<in> R")
      case True thus ?thesis using gap[OF yV] by (simp add: le_diff_eq)
    next
      case False
      have "c y \<in> c ` V" by (rule imageI[OF yV])
      thus ?thesis using Max_ge[OF fin] False by simp
    qed
  qed
  obtain z where z: "z \<in> V" "c z = ?m" using Max_in[OF fin ne] by auto
  have zNR: "z \<notin> R" using argNR[OF z(1)] z(2) by simp
  have zval: "?c' z = ?m" using zNR z(2) by simp
  have zmem: "?c' z \<in> ?c' ` V" by (rule imageI[OF z(1)])
  show "Max (?c' ` V) = ?m"
  proof (intro Max_eqI)
    show "finite (?c' ` V)" using assms(1) by simp
    show "?m \<in> ?c' ` V" using zmem zval by simp
    fix a assume "a \<in> ?c' ` V"
    then obtain x where x: "x \<in> V" "a = ?c' x" by auto
    show "a \<le> ?m" unfolding x(2) by (rule le_all[OF x(1)])
  qed
qed

context double_matroid
begin

text \<open>A tight \<open>Gbar\<close>-arc whose endpoints both lie in \<open>R\<close> stays tight after the reweighting step: the
two endpoints shift by the same amount, so their equal weights stay equal.\<close>
lemma Gbar_reweight_tight:
  assumes "(a, b) \<in> weighted_intersection_graph.Gbar carrier indep1 indep2 c1 c2 X"
    "a \<in> R" "b \<in> R"
  shows "(a, b) \<in> weighted_intersection_graph.Gbar carrier indep1 indep2
             (\<lambda>z. if z \<in> R then c1 z - e else c1 z) (\<lambda>z. if z \<in> R then c2 z + e else c2 z) X"
proof -
  interpret W: weighted_intersection_graph carrier indep1 indep2 c1 c2 by unfold_locales
  interpret W': weighted_intersection_graph carrier indep1 indep2
      "\<lambda>z. if z \<in> R then c1 z - e else c1 z" "\<lambda>z. if z \<in> R then c2 z + e else c2 z" by unfold_locales
  from assms(1) have "(a, b) \<in> W.Abar1 X \<or> (a, b) \<in> W.Abar2 X" by (simp add: W.Gbar_def)
  thus ?thesis
  proof
    assume ab: "(a, b) \<in> W.Abar1 X"
    hence "(\<lambda>z. if z \<in> R then c1 z - e else c1 z) a = (\<lambda>z. if z \<in> R then c1 z - e else c1 z) b"
      using assms(2,3) by (simp add: W.Abar1_def)
    thus ?thesis using ab by (auto simp add: W'.Gbar_def W'.Abar1_def W.Abar1_def)
  next
    assume ab: "(a, b) \<in> W.Abar2 X"
    hence "(\<lambda>z. if z \<in> R then c2 z + e else c2 z) a = (\<lambda>z. if z \<in> R then c2 z + e else c2 z) b"
      using assms(2,3) by (simp add: W.Abar2_def)
    thus ?thesis using ab by (auto simp add: W'.Gbar_def W'.Abar2_def W.Abar2_def)
  qed
qed

text \<open>Conversely, a boundary arc of the auxiliary graph whose weight gap equals \<open>\<epsilon>\<close> \<^emph>\<open>becomes\<close> tight
after reweighting: the \<open>R\<close>-endpoint moves by \<open>\<epsilon>\<close> towards the other, closing the gap. These are the arcs
that grow the reachable set.\<close>
lemma A1_reweight_tight:
  assumes "(x, y) \<in> A1 X" "x \<in> R" "y \<notin> R" "c1 x - c1 y = e"
  shows "(x, y) \<in> weighted_intersection_graph.Gbar carrier indep1 indep2
             (\<lambda>z. if z \<in> R then c1 z - e else c1 z) c2 X"
proof -
  interpret W': weighted_intersection_graph carrier indep1 indep2
      "\<lambda>z. if z \<in> R then c1 z - e else c1 z" c2 by unfold_locales
  have "(\<lambda>z. if z \<in> R then c1 z - e else c1 z) x = (\<lambda>z. if z \<in> R then c1 z - e else c1 z) y"
    using assms(2,3,4) by (simp add: algebra_simps)
  thus ?thesis using assms(1) by (auto simp add: W'.Gbar_def W'.Abar1_def)
qed

lemma A2_reweight_tight:
  assumes "(y, x) \<in> A2 X" "y \<in> R" "x \<notin> R" "c2 x - c2 y = e"
  shows "(y, x) \<in> weighted_intersection_graph.Gbar carrier indep1 indep2
             c1 (\<lambda>z. if z \<in> R then c2 z + e else c2 z) X"
proof -
  interpret W': weighted_intersection_graph carrier indep1 indep2
      c1 "\<lambda>z. if z \<in> R then c2 z + e else c2 z" by unfold_locales
  have "(\<lambda>z. if z \<in> R then c2 z + e else c2 z) y = (\<lambda>z. if z \<in> R then c2 z + e else c2 z) x"
    using assms(2,3,4) by (simp add: algebra_simps)
  thus ?thesis using assms(1) by (auto simp add: W'.Gbar_def W'.Abar2_def)
qed

end

end
