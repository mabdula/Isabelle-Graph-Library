theory Matroid_Weighted_Intersection
  imports Matroid_Intersection Data_Structures.More_Arith
begin

section \<open>Theory for Weighted Matroid Intersection\<close>

text \<open>This file contains theory for weighted matroid intersection (Korte\&Vygen, Section 13.7). It formalises
the fact that splitting the weight into two functions, each optimal in one of the two matroids for a fixed
cardinality, yields an optimum common independent set of that cardinality (the implication (13.5) $\Rightarrow$
(13.4)), together with Frank's augmentation lemma (Lemma 13.35), the weighted analogue of Lemma 13.27.\<close>

locale weighted_double_matroid = double_matroid carrier indep1 indep2
  for carrier :: "'a set" and indep1 indep2 +
  fixes c :: "'a \<Rightarrow> 'b :: linordered_ab_group_add"
begin

text \<open>A set is optimum in the intersection if it is common independent and has maximum weight among all common
independent sets. This is the object the weighted matroid intersection algorithm ultimately computes.\<close>

definition "is_opt X \<longleftrightarrow> indep1 X \<and> indep2 X \<and> (\<forall> Y. indep1 Y \<and> indep2 Y
    \<longrightarrow> sum c Y \<le> sum c X)"

text \<open>The implication (13.5) $\Rightarrow$ (13.4): if the weight splits as \<open>c = c1 + c2\<close> and
\<open>X\<close> is a common independent set that is simultaneously \<open>c1\<close>-maximum in the first and
\<open>c2\<close>-maximum in the second matroid among the sets of its own cardinality, then \<open>X\<close> is
\<open>c\<close>-maximum among all common independent sets of that cardinality.\<close>

lemma opt_in_matroids_imp_opt_in_intersection:
  fixes c1 c2 :: "'a \<Rightarrow> 'b"
  assumes "\<And> e. e \<in> carrier \<Longrightarrow> c e = c1 e + c2 e"
    "indep1 X" "indep2 X" "k = card X"
    "\<And> Y. \<lbrakk>indep1 Y; card Y = k\<rbrakk> \<Longrightarrow> sum c1 Y \<le> sum c1 X"
    "\<And> Y. \<lbrakk>indep2 Y; card Y = k\<rbrakk> \<Longrightarrow> sum c2 Y \<le> sum c2 X"
    "indep1 Z" "indep2 Z" "card Z = k"
  shows "sum c Z \<le> sum c X"
  using assms matroid1.indep_subset_carrier sum.cong[of Z Z c "\<lambda>e. c1 e + c2 e"]
    sum.cong[of X X c "\<lambda>e. c1 e + c2 e"]
  by (auto simp: sum.distrib subset_iff intro: add_mono)

end

text \<open>Three list utilities for deleting the element at a fixed index, needed for the induction in Lemma
13.35.\<close>

lemma del_index_nth:
  "\<lbrakk>h < length zs; p < length zs - 1\<rbrakk> \<Longrightarrow>
     (take h zs @ drop (Suc h) zs) ! p = zs ! (if p < h then p else Suc p)"
  by (auto simp: nth_append min_def)

lemma del_index_distinct_decomp:
  "\<lbrakk>distinct zs; h < length zs\<rbrakk> \<Longrightarrow> distinct (take h zs @ zs ! h # drop (Suc h) zs)"
  by (simp flip: id_take_nth_drop)

lemma del_index_set:
  assumes "distinct zs" "h < length zs"
  shows "set (take h zs @ drop (Suc h) zs) = set zs - {zs ! h}"
proof-
  have "set zs = set (take h zs @ zs ! h # drop (Suc h) zs)"
    using assms(2)
    by (simp add: Cons_nth_drop_Suc)
  thus ?thesis
    using assms del_index_distinct_decomp
    by auto
qed

lemma del_index_distinct:
  "\<lbrakk>distinct zs; h < length zs\<rbrakk> \<Longrightarrow> distinct (take h zs @ drop (Suc h) zs)"
  using del_index_distinct_decomp
  by fastforce

lemma del_index_set_map:
  "\<lbrakk>distinct (map f zs); h < length zs\<rbrakk> \<Longrightarrow>
     set (map f (take h zs @ drop (Suc h) zs)) = set (map f zs) - {f (zs ! h)}"
  using del_index_set[of "map f zs" h]
  by (simp add: take_map drop_map)

lemma del_index_distinct_map:
  "\<lbrakk>distinct (map f zs); h < length zs\<rbrakk> \<Longrightarrow> distinct (map f (take h zs @ drop (Suc h)
    zs))"
  using del_index_distinct[of "map f zs" h]
  by (simp add: take_map drop_map)
context matroid
begin

text \<open>Basic circuit exchange: if \<open>x\<close> lies in the fundamental circuit \<open>C(X, y)\<close>, then
swapping \<open>x\<close> for \<open>y\<close> keeps the set independent.\<close>

lemma circuit_exchange_indep:
  assumes "indep X" "y \<in> carrier - X" "x \<in> the_circuit (insert y X)"
  shows "indep (insert y X - {x})"
  using assms circuit_extensional[of X y]
  by auto

text \<open>The fundamental circuit of \<open>y\<close> is unaffected by replacing \<open>X\<close> by an independent
\<open>X'\<close> that still contains that circuit (apart from \<open>y\<close>).\<close>

lemma the_circuit_swap_invariant:
  assumes "indep X" "indep X'" "y \<in> carrier" "y \<notin> X'"
    "\<not> indep (insert y X)"
    "the_circuit (insert y X) \<subseteq> insert y X'"
  shows "the_circuit (insert y X') = the_circuit (insert y X)"
  using assms indep_subset_carrier the_circuit_is_circuit(1)[of X y] circuit_is_the_circuit[of X' y]
    supset_circuit_imp_dep[of "the_circuit (insert y X)" "insert y X'"]
  by auto

end

text \<open>Index bookkeeping for deleting position \<open>h\<close>: every position of the shortened list comes from
a position other than \<open>h\<close>, and the order of positions is preserved.\<close>

lemma del_index_nth_ex:
  "\<lbrakk>h < length zs; i < length zs - 1\<rbrakk> \<Longrightarrow>
     \<exists>k < length zs. k \<noteq> h \<and> (take h zs @ drop (Suc h) zs) ! i = zs ! k"
  using del_index_nth[of h zs i]
  by (intro exI[of _ "if i < h then i else Suc i"]) auto

lemma del_index_nth_pair_ex:
  "\<lbrakk>h < length zs; i < length zs - 1; j < i\<rbrakk> \<Longrightarrow>
     \<exists>k l. k < length zs \<and> l < k \<and> k \<noteq> h \<and> l \<noteq> h \<and>
       (take h zs @ drop (Suc h) zs) ! i = zs ! k \<and> (take h zs @ drop (Suc h) zs) ! j = zs ! l"
  by (rule exI[of _ "if i < h then i else Suc i"], rule exI[of _ "if j < h then j else Suc j"])
    (auto simp: del_index_nth)

context matroid
begin

text \<open>The key step of Frank's lemma: swapping the removed element \<open>fst (xys ! h)\<close> of minimum weight
(with the smallest index among the minima) for its partner leaves every other fundamental circuit unchanged.\<close>

lemma min_swap_the_circuit:
  fixes c :: "'a \<Rightarrow> 'b :: linorder"
  assumes "indep X"
    "set (map fst xys) \<subseteq> X"
    "set (map snd xys) \<subseteq> carrier - X"
    "distinct (map snd xys)"
    "\<And> i. i < length xys \<Longrightarrow>
       fst (xys ! i) \<in> the_circuit (insert (snd (xys ! i)) X) \<and> c (fst (xys ! i)) = c (snd (xys ! i))"
    "\<And> i j. \<lbrakk>i < length xys; j < i\<rbrakk> \<Longrightarrow>
       fst (xys ! j) \<notin> the_circuit (insert (snd (xys ! i)) X) \<or> c (fst (xys ! j)) > c (snd (xys ! i))"
    "\<And> i j. \<lbrakk>i < length xys; j < i\<rbrakk> \<Longrightarrow>
       fst (xys ! i) \<notin> the_circuit (insert (snd (xys ! j)) X) \<or> c (fst (xys ! i)) \<ge> c (snd (xys ! j))"
    "h < length xys" "\<forall>j < length xys. c (fst (xys ! h)) \<le> c (fst (xys ! j))"
    "\<forall>i < h. c (fst (xys ! h)) < c (fst (xys ! i))"
    "j < length xys" "j \<noteq> h"
  shows "the_circuit (insert (snd (xys ! j)) (insert (snd (xys ! h)) X - {fst (xys ! h)}))
           = the_circuit (insert (snd (xys ! j)) X)"
proof-
  (* the minimum-weight removed element lies on none of the other fundamental circuits *)
  have "fst (xys ! h) \<notin> the_circuit (insert (snd (xys ! j)) X)"
    using assms(5)[of j] assms(6)[of j h] assms(7)[of h j] assms(8,11,12) assms(9,10)[rule_format, of j]
    by (cases "h < j") (auto simp: not_less)
  moreover have "snd (xys ! j) \<in> carrier - X" "snd (xys ! h) \<in> carrier - X" "fst (xys ! h) \<in> X"
    "snd (xys ! j) \<noteq> snd (xys ! h)"
    using assms(2-4,8,11,12)
    by (auto simp: distinct_conv_nth dest!: nth_mem)
  moreover have "\<not> indep (insert (snd (xys ! j)) X)"
    using assms(5)[of j] assms(11) the_circuit_non_empty_dependent[of "insert (snd (xys ! j)) X"]
    by blast
  ultimately show ?thesis
    using assms(1,5,8) indep_subset_carrier circuit_exchange_indep
      the_circuit_is_circuit(2)[of X "snd (xys ! j)"]
    by (intro the_circuit_swap_invariant) auto
qed

text \<open>Frank's augmentation lemma (Lemma 13.35), the weighted analogue of @{thm [source] single_matroid_augment}.
Given a weight \<open>c\<close>, a matching sequence of removed elements \<open>fst (xys ! i)\<close> and inserted
elements \<open>snd (xys ! i)\<close> where each removed element sits on the fundamental circuit of the inserted one
with equal weight, and the two cross conditions on circuit membership versus weight hold, the resulting swap keeps the
set independent. The proof deletes the pair of minimum weight and recurses on the shorter list.\<close>

lemma weighted_single_matroid_augment:
  fixes c :: "'a \<Rightarrow> 'b :: linorder"
  assumes "indep X"
    "set (map fst xys) \<subseteq> X"
    "set (map snd xys) \<subseteq> carrier - X"
    "distinct (map fst xys)"
    "distinct (map snd xys)"
    "\<And> i. i < length xys \<Longrightarrow>
       fst (xys ! i) \<in> the_circuit (insert (snd (xys ! i)) X) \<and> c (fst (xys ! i)) = c (snd (xys ! i))"
    "\<And> i j. \<lbrakk>i < length xys; j < i\<rbrakk> \<Longrightarrow>
       fst (xys ! j) \<notin> the_circuit (insert (snd (xys ! i)) X) \<or> c (fst (xys ! j)) > c (snd (xys ! i))"
    "\<And> i j. \<lbrakk>i < length xys; j < i\<rbrakk> \<Longrightarrow>
       fst (xys ! i) \<notin> the_circuit (insert (snd (xys ! j)) X) \<or> c (fst (xys ! i)) \<ge> c (snd (xys ! j))"
  shows "indep (X - set (map fst xys) \<union> set (map snd xys))"
  using assms
proof(induction "length xys" arbitrary: xys X rule: less_induct)
  case less
  show ?case
  proof(cases "xys = []")
    case False
    then obtain h where h: "h < length xys" "\<forall>j < length xys. c (fst (xys ! h)) \<le> c (fst (xys ! j))"
      "\<forall>i < h. c (fst (xys ! h)) < c (fst (xys ! i))"
      using least_argmin_index[of "length xys" "\<lambda>i. c (fst (xys ! i))"]
      by auto
    note circ_eq = min_swap_the_circuit[OF less.prems(1-3,5-8) this]
    (* delete pair h and apply the induction hypothesis to the shorter list *)
    have "indep (insert (snd (xys ! h)) X - {fst (xys ! h)}
            - set (map fst (take h xys @ drop (Suc h) xys))
            \<union> set (map snd (take h xys @ drop (Suc h) xys)))"
    proof(rule less.hyps, goal_cases)
      case (7 i)
      then obtain k where "k < length xys" "k \<noteq> h" "(take h xys @ drop (Suc h) xys) ! i = xys ! k"
        using h(1) del_index_nth_ex[of h xys i]
        by auto
      thus ?case
        using less.prems(6)[of k] circ_eq[of k]
        by simp
    next
      case (8 i j)
      then obtain k l where "k < length xys" "l < k" "k \<noteq> h"
        "(take h xys @ drop (Suc h) xys) ! i = xys ! k" "(take h xys @ drop (Suc h) xys) ! j = xys ! l"
        using h(1) del_index_nth_pair_ex[of h xys i j]
        by auto
      thus ?case
        using less.prems(7)[of k l] circ_eq[of k]
        by simp
    next
      case (9 i j)
      then obtain k l where "k < length xys" "l < k" "l \<noteq> h"
        "(take h xys @ drop (Suc h) xys) ! i = xys ! k" "(take h xys @ drop (Suc h) xys) ! j = xys ! l"
        using h(1) del_index_nth_pair_ex[of h xys i j]
        by auto
      thus ?case
        using less.prems(8)[of k l] circ_eq[of l]
        by simp
    qed ((insert h(1) less.prems del_index_set_map[of fst xys h] del_index_set_map[of snd xys h]
           del_index_distinct_map[of fst xys h] del_index_distinct_map[of snd xys h]
           circuit_exchange_indep[of X "snd (xys ! h)" "fst (xys ! h)"]; auto dest!: nth_mem)+)
    moreover have "insert (snd (xys ! h)) X - {fst (xys ! h)}
            - set (map fst (take h xys @ drop (Suc h) xys))
            \<union> set (map snd (take h xys @ drop (Suc h) xys))
          = X - set (map fst xys) \<union> set (map snd xys)"
      using h(1) less.prems(2-5) del_index_set_map[of fst xys h] del_index_set_map[of snd xys h]
      by (auto dest!: nth_mem)
    ultimately show ?thesis
      by simp
  qed (use less.prems(1) in simp)
qed

text \<open>Frank's lemma with the cross conditions stated for the reverse order of the pairs.\<close>

lemma weighted_single_matroid_augment_rev:
  fixes c :: "'a \<Rightarrow> 'b :: linorder"
  assumes "indep X"
    "set (map fst xys) \<subseteq> X"
    "set (map snd xys) \<subseteq> carrier - X"
    "distinct (map fst xys)"
    "distinct (map snd xys)"
    "\<And> i. i < length xys \<Longrightarrow>
       fst (xys ! i) \<in> the_circuit (insert (snd (xys ! i)) X) \<and> c (fst (xys ! i)) = c (snd (xys ! i))"
    "\<And> i j. \<lbrakk>j < length xys; i < j\<rbrakk> \<Longrightarrow>
       fst (xys ! j) \<notin> the_circuit (insert (snd (xys ! i)) X) \<or> c (fst (xys ! j)) > c (snd (xys ! i))"
    "\<And> i j. \<lbrakk>j < length xys; i < j\<rbrakk> \<Longrightarrow>
       fst (xys ! i) \<notin> the_circuit (insert (snd (xys ! j)) X) \<or> c (fst (xys ! i)) \<ge> c (snd (xys ! j))"
  shows "indep (X - set (map fst xys) \<union> set (map snd xys))"
proof-
  have "indep (X - set (map fst (rev xys)) \<union> set (map snd (rev xys)))"
  proof(rule weighted_single_matroid_augment[where c = c], goal_cases)
    case (7 i j)
    thus ?case
      using assms(7)[of "length xys - Suc j" "length xys - Suc i"]
      by (auto simp: rev_nth)
  next
    case (8 i j)
    thus ?case
      using assms(8)[of "length xys - Suc j" "length xys - Suc i"]
      by (auto simp: rev_nth)
  qed ((insert assms; auto simp: rev_nth simp flip: rev_map)+)
  thus ?thesis
    by simp
qed

end



section \<open>Algorithm-independent candidate lemmas for the weighted algorithm\<close>

text \<open>The snapshot lemmas behind Korte\&Vygen Theorem 13.36; see
\<open>Weighted_Intersection_Lemma_Candidates.md\<close>. They speak about a fixed common independent set, never about
the iteration.\<close>

text \<open>Exchanging one element of a finite set changes neither its cardinality nor, up to the two weights, its
total weight.\<close>

context matroid
begin

text \<open>\<open>max_weight_card c X\<close>: \<open>X\<close> has maximum \<open>c\<close>-weight among the
independent sets of its cardinality.\<close>

definition max_weight_card :: "('a \<Rightarrow> 'b :: linordered_ab_group_add) \<Rightarrow> 'a set \<Rightarrow>
    bool" where
  "max_weight_card c X \<longleftrightarrow> (\<forall> Y. indep Y \<and> card Y = card X \<longrightarrow> sum c Y
    \<le> sum c X)"

text \<open>\<open>local_opt c X\<close>: the two conditions of the greedy optimality criterion (Theorem 13.23) -- (a)
no profitable circuit swap, (b) no profitable single addition.\<close>

definition local_opt :: "('a \<Rightarrow> 'b :: linordered_ab_group_add) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "local_opt c X \<longleftrightarrow>
     (\<forall> y \<in> carrier - X. \<forall> x \<in> the_circuit (insert y X) - {y}. c y \<le> c x)
   \<and> (\<forall> x \<in> X. \<forall> y \<in> carrier - X. indep (insert y X) \<longrightarrow> c y \<le> c x)"

text \<open>Fact C of the symmetric exchange: an element of an independent set is not spanned by the rest.\<close>

lemma indep_notin_cl_remove:
  assumes "indep X" "x \<in> X"
  shows "x \<notin> cl (X - {x})"
proof
  assume "x \<in> cl (X - {x})"
  hence "rank_of X = rank_of (X - {x})"
    using assms(2) cl_rank_of[of x "X - {x}"]
    by (simp add: insert_absorb)
  moreover have "rank_of X = card X" "rank_of (X - {x}) = card (X - {x})"
    using assms(1) indep_subset[of X "X - {x}"] indep_subset_carrier
    by (auto simp flip: indep_iff_rank_of)
  ultimately show False
    using assms card_Diff1_less[of X x]
    by simp
qed

text \<open>Single-element symmetric exchange (Brualdi) -- the key sublemma for the hard direction of the greedy
optimality criterion; proved from the \<open>augment\<close> axiom (absent from the library).\<close>

lemma symmetric_exchange:
  assumes "indep X" "indep Y" "card X = card Y" "x \<in> X - Y"
  shows "\<exists> y \<in> Y - X. indep (insert y (X - {x})) \<and> indep (insert x (Y - {y}))"
proof(cases "indep (insert x Y)")
  case True
  (* x can be added to Y freely; augment X - {x} from Y to get the first swap *)
  obtain z where "z \<in> Y - (X - {x})" "indep (insert z (X - {x}))"
    using assms augment[of Y "X - {x}"] indep_subset[of X "X - {x}"] card_Diff1_less[of X x]
    by auto
  thus ?thesis
    using True assms(4) indep_subset[of "insert x Y" "insert x (Y - {z})"]
    by blast
next
  case False
  (* otherwise some element of the fundamental circuit of x in Y lies outside X and extends
      X - {x}; if none did, the circuit would lie in the closure of X - {x} *)
  have sub: "insert x Y \<subseteq> carrier"
    using assms(1,2,4) indep_subset_carrier
    by auto
  hence circ: "circuit (the_circuit (insert x Y))" "the_circuit (insert x Y) \<subseteq> insert x Y"
    "x \<in> the_circuit (insert x Y)"
    using assms(2,4) False the_circuit_is_circuit[of Y x] circuit_extensional[of Y x]
    by auto
  moreover have "\<exists>y \<in> the_circuit (insert x Y) - X. indep (insert y (X - {x}))"
  proof(rule ccontr)
    assume "\<not> (\<exists>y \<in> the_circuit (insert x Y) - X. indep (insert y (X - {x})))"
    hence "the_circuit (insert x Y) - {x} \<subseteq> cl (X - {x})"
      using assms(1) circ(1) indep_subset[of X "X - {x}"] indep_subset_carrier
        cl_subset[of "X - {x}"] clI_insert[of _ "X - {x}"] circuit_subset_carrier
      by blast
    hence "cl (the_circuit (insert x Y) - {x}) \<subseteq> cl (X - {x})"
      using assms(1) indep_subset_carrier cl_mono[of _ "cl (X - {x})"] cl_subset_carrier cl_cl_absorb[of "X - {x}"]
      by blast
    moreover have "x \<in> cl (the_circuit (insert x Y) - {x})"
      using circ(1) circ(3) sub
        circuit_min_dep circuit_dep
      by (intro clI_insert) (auto simp: insert_absorb)
    ultimately show False
      using assms(1,4) indep_notin_cl_remove
      by blast
  qed
  ultimately obtain y where "y \<in> Y - X" "indep (insert y (X - {x}))" "y \<in> the_circuit (insert x Y)"
    using assms(4)
    by blast
  moreover hence "indep (insert x Y - {y})"
    using assms(2) False circuit_extensional[of Y x] sub
    by simp
  moreover have "insert x Y - {y} = insert x (Y - {y})"
    using assms(4) calculation
    by auto
  ultimately show ?thesis
    by (auto intro!: bexI[of _ y])
qed

text \<open>A profitable exchange contradicts maximum weight at fixed cardinality.\<close>

lemma max_weight_card_exchange_le:
  fixes c :: "'a \<Rightarrow> 'b :: linordered_ab_group_add"
  assumes "indep X" "max_weight_card c X" "x \<in> X" "y \<in> carrier - X" "indep (insert y (X - {x}))"
  shows "c y \<le> c x"
proof-
  have "card (insert y (X - {x})) = card X"
    using assms(3,4) card_swap_finite[of X x y] assms(1) indep_finite
    by simp
  hence "sum c (insert y (X - {x})) \<le> sum c X"
    using assms(2,5)
    unfolding max_weight_card_def
    by blast
  thus ?thesis
    using assms(3,4) sum_swap[of X x y c] assms(1) indep_finite
    by simp
qed

text \<open>Under local optimality, an exchange is never profitable.\<close>

lemma local_opt_exchange_le:
  assumes "indep X" "local_opt c X" "x \<in> X" "y \<in> carrier - X" "indep (insert y (X - {x}))"
  shows "c y \<le> c x"
proof(cases "indep (insert y X)")
  case False
  hence "x \<in> the_circuit (insert y X) - {y}"
    using assms circuit_extensional[of X y]
    by (auto simp: insert_Diff_if)
  thus ?thesis
    using assms(2,4)
    by (auto simp: local_opt_def)
qed (insert assms; auto simp: local_opt_def)

lemma max_weight_card_imp_local_opt:
  fixes c :: "'a \<Rightarrow> 'b :: linordered_ab_group_add"
  assumes "indep X" "max_weight_card c X"
  shows "local_opt c X"
proof-
  have "c y \<le> c x" if "y \<in> carrier - X" "x \<in> the_circuit (insert y X) - {y}" for x y
  proof-
    have "x \<in> X"
      using that assms(1) indep_subset_carrier the_circuit_non_empty_dependent
        the_circuit_is_circuit(2)[of X y]
      by blast
    moreover have "insert y X - {x} = insert y (X - {x})"
      using that
      by auto
    ultimately show ?thesis
      using that assms circuit_exchange_indep[of X y x]
      by (auto intro: max_weight_card_exchange_le)
  qed
  moreover have "c y \<le> c x" if "x \<in> X" "y \<in> carrier - X" "indep (insert y X)" for x y
    using that assms indep_subset[of "insert y X" "insert y (X - {x})"]
    by (auto intro: max_weight_card_exchange_le)
  ultimately show ?thesis
    unfolding local_opt_def
    by blast
qed

text \<open>The hard direction: local optimality is global, by induction on \<open>card (X - Y)\<close> via symmetric
exchange.\<close>

lemma local_opt_imp_max_weight_card:
  fixes c :: "'a \<Rightarrow> 'b :: linordered_ab_group_add"
  assumes "indep X" "local_opt c X"
  shows "max_weight_card c X"
proof-
  have "sum c Y \<le> sum c X" if "indep Y" "card Y = card X" for Y
    using that
  proof(induction "card (X - Y)" arbitrary: Y rule: less_induct)
    case less
    show ?case
    proof(cases "X \<subseteq> Y")
      case False
      then obtain x where x: "x \<in> X - Y"
        by auto
      then obtain y where swap: "y \<in> Y - X" "indep (insert y (X - {x}))" "indep (insert x (Y - {y}))"
        using assms(1) less.prems symmetric_exchange[of X Y x]
        by auto
      (* the exchanged pair does not decrease the weight; move Y one step towards X and recurse *)
      moreover have "card (insert x (Y - {y})) = card X"
        using less.prems x swap(1) card_swap_finite[of Y y x] indep_finite
        by auto
      moreover have "X - insert x (Y - {y}) = X - Y - {x}"
        using swap(1)
        by auto
      hence "card (X - insert x (Y - {y})) < card (X - Y)"
        using x card_Diff1_less[of "X - Y" x] assms(1) indep_finite
        by simp
      ultimately have "sum c (insert x (Y - {y})) \<le> sum c X"
        using less.hyps
        by blast
      have "c y \<le> c x"
        using assms x swap(1) swap(2) less.prems(1) indep_subset_carrier
          local_opt_exchange_le[of X c x y]
        by blast
      hence "sum c Y \<le> sum c Y - c y + c x"
        by (simp add: algebra_simps)
      also have "\<dots> = sum c (insert x (Y - {y}))"
        using less.prems(1) x swap(1) sum_swap[of Y y x c] indep_finite
        by auto
      also have "\<dots> \<le> sum c X"
        by fact
      finally show ?thesis .
    qed (use less.prems card_subset_eq[of Y X] in auto)
  qed
  thus ?thesis
    by (auto simp: max_weight_card_def)
qed

text \<open>C1 -- Theorem 13.23: local optimality characterises maximum weight at fixed cardinality.\<close>

lemma greedy_optimality:
  fixes c :: "'a \<Rightarrow> 'b :: linordered_ab_group_add"
  shows "indep X \<Longrightarrow> max_weight_card c X \<longleftrightarrow> local_opt c X"
  using max_weight_card_imp_local_opt local_opt_imp_max_weight_card
  by blast

text \<open>C2: adding the heaviest addable element preserves local optimality (hence optimality at card+1).\<close>

lemma greedy_extension:
  fixes c :: "'a \<Rightarrow> 'b :: linordered_ab_group_add"
  assumes "indep X" "local_opt c X" "y0 \<in> carrier - X" "indep (insert y0 X)"
    "c y0 = Max (c ` {y \<in> carrier - X. indep (insert y X)})"
  shows "local_opt c (insert y0 X)"
proof-
  have "sum c Z \<le> sum c (insert y0 X)" if "indep Z" "card Z = card (insert y0 X)" for Z
  proof-
    have "card X < card Z"
      using that(2) assms(1,3) indep_finite
      by simp
    with that(1) assms(1) augment[of Z X] obtain w where "w \<in> Z - X" "indep (insert w X)"
      by auto
    (* every element addable to X is no heavier than the chosen y0 *)
    moreover hence "c w \<le> c y0"
      using assms(5) that(1) carrier_finite indep_subset_carrier
      by (auto intro!: Max_ge)
    (* and X is optimal at its cardinality *)
    moreover have "card (Z - {w}) = card X"
      using that(2) assms(3) calculation assms(1) that(1) indep_finite
      by simp
    hence "sum c (Z - {w}) \<le> sum c X"
      using that(1) local_opt_imp_max_weight_card[OF assms(1,2)] indep_subset[of Z "Z - {w}"]
      unfolding max_weight_card_def
      by blast
    ultimately show ?thesis
      using that(1) assms(3) sum.remove[of Z w c] assms(1) indep_finite
      by (auto intro: add_mono)
  qed
  thus ?thesis
    using assms(4)
    by (auto simp: max_weight_card_def intro!: max_weight_card_imp_local_opt)
qed

text \<open>A locally optimal \<open>X\<close> bounds the weight of every larger independent set: each further element
weighs at most the bound \<open>d\<close> on the elements addable to \<open>X\<close>.\<close>

lemma local_opt_larger_bound:
  fixes c :: "'a \<Rightarrow> 'b :: linordered_ab_group_add"
  assumes "indep X" "local_opt c X" "indep Y" "card Y = card X + k"
    "\<And> y. \<lbrakk>y \<in> carrier - X; indep (insert y X)\<rbrakk> \<Longrightarrow> c y \<le> d"
  shows "sum c Y \<le> sum c X + sum (\<lambda> _. d) {..<k}"
  using assms
proof(induction k arbitrary: X)
  case 0
  thus ?case
    using local_opt_imp_max_weight_card[OF 0(1,2)]
    by (simp add: max_weight_card_def)
next
  case (Suc k)
  (* extend X greedily by a heaviest addable element y0 and recurse *)
  obtain w where "w \<in> Y - X" "indep (insert w X)"
    using Suc.prems(1,3,4) augment[of Y X]
    by auto
  hence "Max (c ` {y \<in> carrier - X. indep (insert y X)}) \<in> c ` {y \<in> carrier - X. indep (insert y X)}"
    using Suc.prems(3) indep_subset_carrier carrier_finite
    by (intro Max_in) auto
  then obtain y0 where y0: "y0 \<in> carrier - X" "indep (insert y0 X)"
    "c y0 = Max (c ` {y \<in> carrier - X. indep (insert y X)})"
    by auto
  hence "local_opt c (insert y0 X)"
    by (rule greedy_extension[OF Suc.prems(1,2)])
  hence "sum c Y \<le> sum c (insert y0 X) + sum (\<lambda> _. d) {..<k}"
  proof(rule Suc.IH[OF y0(2) _ Suc.prems(3)])
    show "card Y = card (insert y0 X) + k"
      using Suc.prems(4) y0(1) Suc.prems(1) indep_finite
      by simp
  next
    fix y
    assume "y \<in> carrier - insert y0 X" "indep (insert y (insert y0 X))"
    thus "c y \<le> d"
      using Suc.prems(5)[of y] indep_subset[of "insert y (insert y0 X)" "insert y X"]
      by auto
  qed
  hence "sum c Y \<le> c y0 + (sum c X + sum (\<lambda> _. d) {..<k})"
    using y0(1) Suc.prems(1) indep_finite
    by (simp add: algebra_simps)
  also have "\<dots> \<le> d + (sum c X + sum (\<lambda> _. d) {..<k})"
    using Suc.prems(5)[of y0] y0(1) y0(2)
    by simp
  finally show ?case
    by (simp add: algebra_simps)
qed

text \<open>C3: shifting the weight down by \<open>\<epsilon>\<close> on a set \<open>R\<close> preserves local
optimality, provided \<open>\<epsilon>\<close> does not exceed any weight gap across the boundary of \<open>R\<close>.
This is the dual (reweighting) step.\<close>

lemma reweight_preserves_local_opt:
  fixes c :: "'a \<Rightarrow> 'b :: linordered_ab_group_add"
  assumes "indep X" "local_opt c X" "R \<subseteq> carrier" "0 < \<epsilon>"
    "\<And> y x. \<lbrakk>y \<in> carrier - X; x \<in> the_circuit (insert y X) - {y}; x \<in> R; y \<notin> R\<rbrakk>
              \<Longrightarrow> \<epsilon> \<le> c x - c y"
    "\<And> x y. \<lbrakk>x \<in> X; y \<in> carrier - X; indep (insert y X); x \<in> R; y \<notin> R\<rbrakk>
              \<Longrightarrow> \<epsilon> \<le> c x - c y"
  shows "local_opt (\<lambda> e. if e \<in> R then c e - \<epsilon> else c e) X"
  using assms(2,5,6) reweight_order[OF assms(4), of c]
  by (unfold local_opt_def) blast

text \<open>A set with the weight and cardinality of the greedy extension of a locally optimal \<open>X\<close> is
locally optimal.\<close>

lemma local_opt_insert_transfer:
  fixes c :: "'a \<Rightarrow> 'b :: linordered_ab_group_add"
  assumes "indep X" "local_opt c X" "u \<in> carrier - X" "indep (insert u X)"
    "c u = Max (c ` {y \<in> carrier - X. indep (insert y X)})"
    "indep X'" "card X' = card X + 1" "sum c X' = sum c X + c u"
  shows "local_opt c X'"
  using assms greedy_extension[of X c u] local_opt_imp_max_weight_card[of "insert u X" c]
    max_weight_card_imp_local_opt[of X' c] indep_finite[of X]
  by (auto simp: max_weight_card_def add.commute)

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

text \<open>The tight subgraph and restricted endpoints are subsets of the (weight-agnostic) auxiliary graph; hence
any tight path is a path in the full graph.\<close>

lemma Gbar_subset: "Gbar X \<subseteq> A1 X \<union> A2 X"
  by (auto simp add: Gbar_def Abar1_def Abar2_def)

lemma Sbar_subset: "Sbar X \<subseteq> S X"
  by (auto simp add: Sbar_def)

lemma Tbar_subset: "Tbar X \<subseteq> T X"
  by (auto simp add: Tbar_def)

text \<open>C4 -- facts (i)/(ii): every non-tight arc of the auxiliary graph has a strict weight drop.\<close>

lemma tight_gap1:
  "\<lbrakk>indep1 X; indep2 X; matroid1.local_opt c1 X; (x, y) \<in> A1 X; c1 x \<noteq> c1 y\<rbrakk>
    \<Longrightarrow> c1 y < c1 x"
  by (force simp: A1_def matroid1.local_opt_def order_less_le)

lemma tight_gap2:
  "\<lbrakk>indep1 X; indep2 X; matroid2.local_opt c2 X; (y, x) \<in> A2 X; c2 x \<noteq> c2 y\<rbrakk>
    \<Longrightarrow> c2 y < c2 x"
  by (force simp: A2_def matroid2.local_opt_def order_less_le)

text \<open>The fundamental circuit of the head of an exchange arc does not change when an independent extension of
\<open>X\<close> replaces \<open>X\<close>.\<close>

lemma A1_circuit_ext:
  "\<lbrakk>(a, b) \<in> A1 X; indep1 (insert u X)\<rbrakk> \<Longrightarrow>
     matroid1.the_circuit (insert b (insert u X)) = matroid1.the_circuit (insert b X)"
  using matroid1.the_circuit_non_empty_dependent[of "insert b X"]
  by (rule matroid1.same_cicuit_indep_part_extended; auto simp: A1_def)

lemma A2_circuit_ext:
  "\<lbrakk>(b, a) \<in> A2 X; indep2 (insert u X)\<rbrakk> \<Longrightarrow>
     matroid2.the_circuit (insert b (insert u X)) = matroid2.the_circuit (insert b X)"
  using matroid2.the_circuit_non_empty_dependent[of "insert b X"]
  by (rule matroid2.same_cicuit_indep_part_extended; auto simp: A2_def)

text \<open>Consequences for the pairs exchanged along a tight path: a tight arc keeps its tail on the fundamental
circuit of its head after extending \<open>X\<close>, and by local optimality every element of \<open>X\<close> on
that circuit is at least as heavy as the head and forms an arc with it.\<close>

lemma Abar1_circuit:
  "\<lbrakk>(a, b) \<in> Abar1 X; indep1 (insert u X)\<rbrakk> \<Longrightarrow>
     a \<in> matroid1.the_circuit (insert b (insert u X)) \<and> c1 a = c1 b"
  using A1_circuit_ext[of a b X u]
  by (auto simp: Abar1_def A1_def)

lemma Abar2_circuit:
  "\<lbrakk>(b, a) \<in> Abar2 X; indep2 (insert u X)\<rbrakk> \<Longrightarrow>
     a \<in> matroid2.the_circuit (insert b (insert u X)) \<and> c2 a = c2 b"
  using A2_circuit_ext[of b a X u]
  by (auto simp: Abar2_def A2_def)

lemma A1_local_opt:
  "\<lbrakk>(a, b) \<in> A1 X; indep1 (insert u X); matroid1.local_opt c1 X; a' \<in> X;
    a' \<in> matroid1.the_circuit (insert b (insert u X))\<rbrakk> \<Longrightarrow> (a', b) \<in> A1 X \<and> c1 b
      \<le> c1 a'"
  using A1_circuit_ext[of a b X u]
  by (auto simp: A1_def matroid1.local_opt_def)

lemma A2_local_opt:
  "\<lbrakk>(b, a) \<in> A2 X; indep2 (insert u X); matroid2.local_opt c2 X; a' \<in> X;
    a' \<in> matroid2.the_circuit (insert b (insert u X))\<rbrakk> \<Longrightarrow> (b, a') \<in> A2 X \<and> c2 b
      \<le> c2 a'"
  using A2_circuit_ext[of b a X u]
  by (auto simp: A2_def matroid2.local_opt_def)
text \<open>The facts about a shortest tight \<open>Sbar\<close>-\<open>Tbar\<close> path that the three augmentation
lemmas share: it has odd length and no repeated vertex, its odd-indexed arcs are tight \<open>A1\<close>-arcs and its
even-indexed arcs are tight \<open>A2\<close>-arcs.\<close>

lemma tight_path_props:
  assumes "indep1 X" "indep2 X" "vwalk_bet (Gbar X) x p y" "x \<in> Sbar X" "y \<in> Tbar X"
    "\<nexists> q. vwalk_bet (Gbar X) x q y \<and> length q < length p"
  shows "odd (length p)" "distinct p" "p ! 0 = x" "p ! (length p - 1) = y"
    "x \<in> carrier - X" "y \<in> carrier - X" "indep1 (insert x X)" "indep2 (insert y X)"
    "\<And> i. \<lbrakk>i < length p; odd i\<rbrakk> \<Longrightarrow> (p ! i, p ! Suc i) \<in> Abar1 X"
    "\<And> i. \<lbrakk>Suc i < length p; even i\<rbrakk> \<Longrightarrow> (p ! i, p ! Suc i) \<in> Abar2 X"
proof-
  have "vwalk_bet (A1 X \<union> A2 X) x p y"
    using assms(3) Gbar_subset
    by (rule vwalk_bet_subset)
  moreover have "x \<in> carrier - X" "y \<in> carrier - X" "indep1 (insert x X)" "indep2 (insert y X)"
    using assms(4,5) Sbar_subset Tbar_subset
    by (auto simp: S_def T_def)
  ultimately have alt: "alt_list (\<lambda> e. e \<in> A2 X) (\<lambda> e. e \<in> A1 X) (edges_of_vwalk p)"
    and odd: "odd (length p)" "x \<in> carrier - X" "y \<in> carrier - X" "indep1 (insert x X)"
    "indep2 (insert y X)"
    using walk_is_alternating[OF assms(1,2) vwalk_imp_awalk] walk_is_odd[OF assms(1,2)]
    by auto
  moreover have "p ! 0 = x"
    using assms(3)
    by (auto dest: hd_of_vwalk_bet)
  moreover have "p ! (length p - 1) = y"
    using assms(3)
    by (auto dest: last_of_vwalk_bet')
  ultimately show "odd (length p)" "p ! 0 = x" "p ! (length p - 1) = y"
    "x \<in> carrier - X" "y \<in> carrier - X" "indep1 (insert x X)" "indep2 (insert y X)"
    by auto
  show "distinct p"
    using assms(3,6)
    by (rule shortest_vwalk_bet_distinct)
  show "(p ! i, p ! Suc i) \<in> Abar1 X" if "i < length p" "odd i" for i
  proof-
    have "Suc i < length p"
      using that odd(1)
      by presburger
    moreover hence "(p ! i, p ! Suc i) \<in> Gbar X"
      using nth_mem[of i "edges_of_vwalk p"] assms(3) vwalk_bet_edges_in_edges[of "Gbar X" x p y]
        edges_of_vwalk_index[of i p]
      by (auto simp: edges_of_vwalk_length)
    ultimately show ?thesis
      using that(2) assms(1,2) alternating_list_odd_index[OF alt, of i] edges_of_vwalk_index[of i p]
        A2_edges(2)[of X "(p ! i, p ! Suc i)"] A1_edges(1)[of X "(p ! i, p ! Suc i)"]
      by (auto simp: Gbar_def Abar1_def Abar2_def edges_of_vwalk_length)
  qed
  show "(p ! i, p ! Suc i) \<in> Abar2 X" if "Suc i < length p" "even i" for i
  proof-
    have "(p ! i, p ! Suc i) \<in> Gbar X"
      using that(1) nth_mem[of i "edges_of_vwalk p"] assms(3) vwalk_bet_edges_in_edges[of "Gbar X" x p y]
        edges_of_vwalk_index[of i p]
      by (auto simp: edges_of_vwalk_length)
    thus ?thesis
      using that assms(1,2) alternating_list_even_index[OF alt, of i] edges_of_vwalk_index[of i p]
        A2_edges(2)[of X "(p ! i, p ! Suc i)"] A1_edges(1)[of X "(p ! i, p ! Suc i)"]
      by (auto simp: Gbar_def Abar1_def Abar2_def edges_of_vwalk_length)
  qed
qed


text \<open>Weighted analogue of @{thm [source] augment_in_matroid1}: a shortest tight path augments while keeping the
first matroid independent, via Frank's Lemma 13.35. Condition (a)'s cost equality comes from the tightness of the
\<open>Abar1\<close>-arcs, (b)'s strict gap from a \<open>Gbar\<close>-shortcut argument, and (c) directly from local
optimality of \<open>X\<close> in matroid 1.\<close>

lemma weighted_augment_in_matroid1:
  assumes "indep1 X" "indep2 X" "matroid1.local_opt c1 X"
    "vwalk_bet (Gbar X) x p y" "x \<in> Sbar X" "y \<in> Tbar X"
    "\<nexists> q. vwalk_bet (Gbar X) x q y \<and> length q < length p"
  shows "indep1 ((X \<union> {p ! i | i. i < length p \<and> even i}) - {p ! i | i. i < length p \<and> odd i})"
proof-
  note path = tight_path_props[OF assms(1,2,4-7)]
  let ?l = "[(p ! (2*i+1), p ! (2*i+2)). i <- [0..<(length p - 1) div 2]]"
  have arcs: "set ?l \<subseteq> Abar1 X"
  proof
    fix e
    assume "e \<in> set ?l"
    then obtain i where "i < (length p - 1) div 2" "e = (p ! (2*i+1), p ! Suc (2*i+1))"
      by auto
    moreover hence "2*i+1 < length p"
      by presburger
    ultimately show "e \<in> Abar1 X"
      using path(9)[of "2*i+1"]
      by simp
  qed
  have "p ! 0 \<notin> set (map snd ?l)"
    using odd_pairs_snd_notin1[OF path(2,1), of 0] path(1)
    by (force simp: odd_pos)
  hence bounds: "set (map fst ?l) \<subseteq> X"
    "set (map snd ?l) \<subseteq> carrier - insert (p ! 0) X" "set ?l \<subseteq> A1 X"
    using arcs assms(1,2) A1_edges
    by (fastforce simp: Abar1_def)+
  (* the conditions of Frank's lemma for the first matroid and insert x X *)
  have "indep1 (insert (p ! 0) X - set (map fst ?l) \<union> set (map snd ?l))"
  proof(rule matroid1.weighted_single_matroid_augment[where c = c1], goal_cases)
    case (6 i)
    hence "?l ! i \<in> Abar1 X"
      using nth_mem[of i ?l] arcs
      by blast
    thus ?case
      using path(3,7) Abar1_circuit[of "fst (?l ! i)" "snd (?l ! i)" X x]
      by simp
  next
    case (7 i j)
    (* a non-strict gap would give a tight shortcut arc from p ! (2j+1) to p ! (2i+2) *)
    show ?case
    proof(rule ccontr)
      assume "\<not> ?case"
      moreover have "?l ! i \<in> A1 X" "?l ! j \<in> A1 X"
        using 7 nth_mem[of i ?l] nth_mem[of j ?l] bounds(3) order.strict_trans[of j i "length ?l"]
        by blast+
      ultimately have "(fst (?l ! j), snd (?l ! i)) \<in> Gbar X"
        using assms(3) path(3,7) assms(1,2) A1_edges(1)[of X "?l ! j"]
          A1_local_opt[of "fst (?l ! i)" "snd (?l ! i)" X x "fst (?l ! j)"]
        by (auto simp: Gbar_def Abar1_def)
      moreover have "i < (length p - 1) div 2"
        using 7
        by simp
      hence "2*i+2 < length p"
        by presburger
      ultimately show False
        using 7 assms(4,7) shortest_vwalk_no_shortcut[of "Gbar X" x p y "2*j+1" "2*i+2"]
        by simp
    qed
  next
    case (8 i j)
    hence "?l ! i \<in> A1 X" "?l ! j \<in> A1 X"
      using nth_mem[of i ?l] nth_mem[of j ?l] bounds(3) order.strict_trans[of j i "length ?l"]
      by blast+
    thus ?case
      using assms(3) path(3,7) assms(1,2) A1_edges(1)[of X "?l ! i"]
        A1_local_opt[of "fst (?l ! j)" "snd (?l ! j)" X x "fst (?l ! i)"]
      by auto
  qed (use path odd_pairs_distinct1[of p] bounds(1)
         bounds(2) in auto)
  moreover have "set (map snd ?l) \<inter> {p ! i | i. i < length p \<and> odd i} = {}"
    using path(1,2) odd_pairs_snd_notin1[of p]
    by force
  moreover hence "X \<union> {p ! i | i. i < length p \<and> even i} - {p ! i | i. i < length p \<and> odd i}
      = insert (p ! 0) X - set (map fst ?l) \<union> set (map snd ?l)"
    using path(1) odd_pairs_fst1[of p] odd_pairs_snd1[of p] bounds(2)
    by auto
  ultimately show ?thesis
    by simp
qed

text \<open>Weighted analogue of @{thm [source] augment_in_matroid2}, with the pairs taken in the reverse order (the
variant @{thm [source] matroid.weighted_single_matroid_augment_rev} of Frank's lemma).\<close>

lemma weighted_augment_in_matroid2:
  assumes "indep1 X" "indep2 X" "matroid2.local_opt c2 X"
    "vwalk_bet (Gbar X) x p y" "x \<in> Sbar X" "y \<in> Tbar X"
    "\<nexists> q. vwalk_bet (Gbar X) x q y \<and> length q < length p"
  shows "indep2 ((X \<union> {p ! i | i. i < length p \<and> even i}) - {p ! i | i. i < length p \<and> odd i})"
proof-
  note path = tight_path_props[OF assms(1,2,4-7)]
  define l where "l = [(p ! (2*i+1), p ! (2*i)). i <- [0..<(length p - 1) div 2]]"
  have arcs: "(snd (l ! i), fst (l ! i)) \<in> Abar2 X" "(snd (l ! i), fst (l ! i)) \<in> A2 X" if "i < length l" for i
  proof-
    have "Suc (2*i) < length p"
      using that
      by (simp add: l_def)
    thus "(snd (l ! i), fst (l ! i)) \<in> Abar2 X"
      using that path(10)[of "2*i"]
      by (simp add: l_def)
    thus "(snd (l ! i), fst (l ! i)) \<in> A2 X"
      by (simp add: Abar2_def)
  qed
  have "p ! (length p - 1) \<notin> set (map snd l)"
    using path(1,2) odd_pos[of "length p"] odd_pairs_snd_notin2[of p "length p - 1", folded l_def]
    by (simp add: snd_eq_Range Range_iff)
  hence bounds: "set (map fst l) \<subseteq> X"
    "set (map snd l) \<subseteq> carrier - insert (p ! (length p - 1)) X"
    using arcs assms(1,2) A2_edges
    by (fastforce simp: in_set_conv_nth)+
  (* the conditions of Frank's lemma for the second matroid and insert y X *)
  have "indep2 (insert (p ! (length p - 1)) X - set (map fst l) \<union> set (map snd l))"
  proof(rule matroid2.weighted_single_matroid_augment_rev[where c = c2], goal_cases)
    case (6 i)
    thus ?case
      using 6 arcs(1) path(4,8) Abar2_circuit[of "snd (l ! i)" "fst (l ! i)" X y]
      by simp
  next
    case (7 i j)
    (* a non-strict gap would give a tight shortcut arc from p ! (2i) to p ! (2j+1) *)
    show ?case
    proof(rule ccontr)
      assume "\<not> ?case"
      hence "(snd (l ! i), fst (l ! j)) \<in> Gbar X"
        using 7 arcs(2)[of i] arcs(2)[of j] assms(3) path(4,8)
          assms(1,2) A2_edges(1)[of X "(snd (l ! j), fst (l ! j))"]
          A2_local_opt[of "snd (l ! i)" "fst (l ! i)" X y "fst (l ! j)"]
        by (auto simp: Gbar_def Abar2_def)
      moreover have "j < (length p - 1) div 2" "l ! i = (p ! (2*i+1), p ! (2*i))"
        "l ! j = (p ! (2*j+1), p ! (2*j))"
        using 7
        by (simp_all add: l_def)
      moreover hence "2*j+1 < length p"
        by presburger
      ultimately show False
        using 7 assms(4,7) shortest_vwalk_no_shortcut[of "Gbar X" x p y "2*i" "2*j+1"]
        by simp
    qed
  next
    case (8 i j)
    thus ?case
      using arcs(2)[of i] arcs(2)[of j] assms(3) path(4,8)
        assms(1,2) A2_edges(1)[of X "(snd (l ! i), fst (l ! i))"]
        A2_local_opt[of "snd (l ! j)" "fst (l ! j)" X y "fst (l ! i)"]
      by auto
  qed (use path odd_pairs_distinct2[of p, folded l_def] bounds(1)
         bounds(2) in auto)
  moreover have "set (map snd l) \<inter> {p ! i | i. i < length p \<and> odd i} = {}"
    using path(1,2) odd_pairs_snd_notin2[of p, folded l_def]
    by (auto simp: snd_eq_Range Range_iff)
  moreover hence "X \<union> {p ! i | i. i < length p \<and> even i} - {p ! i | i. i < length p \<and> odd i}
      = insert (p ! (length p - 1)) X - set (map fst l) \<union> set (map snd l)"
    using path(1) odd_pairs_fst2[of p, folded l_def] odd_pairs_snd2[of p, folded l_def]
      bounds(2)
    by auto
  ultimately show ?thesis
    by simp
qed


text \<open>The odd-position vertices of a shortest tight path lie in \<open>X\<close>, the even-position ones
outside.\<close>

lemma tight_path_evens_odds:
  assumes "indep1 X" "indep2 X" "vwalk_bet (Gbar X) x p y" "x \<in> Sbar X" "y \<in> Tbar X"
    "\<nexists> q. vwalk_bet (Gbar X) x q y \<and> length q < length p"
  shows "{p ! i | i. i < length p \<and> odd i} \<subseteq> X" "X \<inter> {p ! i | i. i < length p \<and> even i} = {}"
proof-
  note path = tight_path_props[OF assms]
  have "p ! i \<in> X" if "i < length p" "odd i" for i
  proof-
    have "Suc i < length p"
      using that path(1)
      by presburger
    thus ?thesis
      using that path(9)[of i] assms(1,2) A1_edges(1)[of X "(p ! i, p ! Suc i)"]
      by (auto simp: Abar1_def)
  qed
  moreover have "p ! i \<notin> X" if "i < length p" "even i" for i
  proof(cases "Suc i < length p")
    case True
    thus ?thesis
      using that path(10)[of i] assms(1,2) A2_edges(2)[of X "(p ! i, p ! Suc i)"]
      by (auto simp: Abar2_def)
  next
    case False
    hence "i = length p - 1"
      using that
      by simp
    thus ?thesis
      using path(4,6)
      by simp
  qed
  ultimately show "{p ! i | i. i < length p \<and> odd i} \<subseteq> X" "X \<inter> {p ! i | i. i < length p \<and>
    even i} = {}"
    by auto+
qed

text \<open>C5: a shortest tight \<open>Sbar\<close>-\<open>Tbar\<close> path preserves common independence and the
per-matroid local optimality while raising the cardinality by one (weighted analogue of @{thm [source]
augment_in_both_matroids}).\<close>

lemma augment_tight_path:
  assumes "indep1 X" "indep2 X" "matroid1.local_opt c1 X" "matroid2.local_opt c2 X"
    "vwalk_bet (Gbar X) u p v" "u \<in> Sbar X" "v \<in> Tbar X"
    "\<nexists> q. vwalk_bet (Gbar X) u q v \<and> length q < length p"
    "X' = (X \<union> {p ! i | i. i < length p \<and> even i}) - {p ! i | i. i < length p \<and> odd i}"
  shows "indep1 X'" "indep2 X'" "card X' = card X + 1"
    "matroid1.local_opt c1 X'" "matroid2.local_opt c2 X'"
    "sum c1 X' = sum c1 X + c1 u" "sum c2 X' = sum c2 X + c2 v"
proof-
  note path = tight_path_props[OF assms(1,2,5-8)]
  note evens_odds = tight_path_evens_odds[OF assms(1,2,5-8)]
  show indep: "indep1 X'" "indep2 X'"
    using assms weighted_augment_in_matroid1 weighted_augment_in_matroid2
    by auto
  (* the even positions outnumber the odd ones by one, and the tight arcs telescope the weights *)
  have "card {p ! i | i. i < length p \<and> even i} = length p div 2 + 1"
    "card {p ! i | i. i < length p \<and> odd i} = length p div 2"
    using assms(1,2) path(1,2) card_of_evens_under_odd card_of_odds_under_odd
    by (simp_all add: setcompr_eq_image card_image inj_on_nth)
  thus card: "card X' = card X + 1"
    using assms(9) evens_odds assms(1) matroid1.indep_finite
    by (simp add: card_Diff_subset card_Un_disjoint le_supI1)
  have "c1 (p ! i) = c1 (p ! Suc i)" if "i < length p" "odd i" for i
    using that path(9)
    by (auto simp: Abar1_def)
  moreover have "c2 (p ! i) = c2 (p ! Suc i)" if "Suc i < length p" "even i" for i
    using that path(10)
    by (auto simp: Abar2_def)
  ultimately have "sum c1 {p ! i | i. i < length p \<and> even i} = sum c1 {p ! i | i. i < length p \<and> odd i} + c1
    u"
    "sum c2 {p ! i | i. i < length p \<and> even i} = sum c2 {p ! i | i. i < length p \<and> odd i} + c2 v"
    using path(1-4) sum_evens_odds_tight[of "length p" "\<lambda>i. c1 (p ! i)"]
      sum_evens_odds_tight2[of "length p" "\<lambda>i. c2 (p ! i)"]
    by (simp_all add: setcompr_eq_image sum.reindex inj_on_nth comp_def)
  thus "sum c1 X' = sum c1 X + c1 u" "sum c2 X' = sum c2 X + c2 v"
    using assms(9) evens_odds assms(1) matroid1.indep_finite
    by (simp_all add: sum_diff sum.union_disjoint algebra_simps le_supI1)
  thus "matroid1.local_opt c1 X'" "matroid2.local_opt c2 X'"
    using assms(1-4,6,7) path(5-8) indep card
    by (auto intro!: matroid1.local_opt_insert_transfer[of X c1 u X']
          matroid2.local_opt_insert_transfer[of X c2 v X'] simp: Sbar_def Tbar_def S_def T_def)
qed

end

context double_matroid
begin

lemma weighted_intersection_graph_intro: "weighted_intersection_graph carrier indep1 indep2"
  by unfold_locales

text \<open>A tight \<open>Gbar\<close>-arc whose endpoints both lie in \<open>R\<close> stays tight after the
reweighting step: the two endpoints shift by the same amount, so their equal weights stay equal.\<close>

lemma Gbar_reweight_tight:
  "\<lbrakk>(a, b) \<in> weighted_intersection_graph.Gbar carrier indep1 indep2 c1 c2 X; a \<in> R; b \<in> R\<rbrakk>
    \<Longrightarrow>
     (a, b) \<in> weighted_intersection_graph.Gbar carrier indep1 indep2
       (\<lambda>z. if z \<in> R then c1 z - e else c1 z) (\<lambda>z. if z \<in> R then c2 z + e else c2 z) X"
  using weighted_intersection_graph_intro
  by (auto simp: weighted_intersection_graph.Gbar_def weighted_intersection_graph.Abar1_def
        weighted_intersection_graph.Abar2_def)

text \<open>Conversely, a boundary arc of the auxiliary graph whose weight gap equals \<open>\<epsilon>\<close>
\<^emph>\<open>becomes\<close> tight after reweighting: the \<open>R\<close>-endpoint moves by
\<open>\<epsilon>\<close> towards the other, closing the gap. These are the arcs that grow the reachable set.\<close>

lemma A1_reweight_tight:
  "\<lbrakk>(x, y) \<in> A1 X; x \<in> R; y \<notin> R; c1 x - c1 y = e\<rbrakk> \<Longrightarrow>
     (x, y) \<in> weighted_intersection_graph.Gbar carrier indep1 indep2
       (\<lambda>z. if z \<in> R then c1 z - e else c1 z) c2 X"
  using weighted_intersection_graph_intro
  by (auto simp: weighted_intersection_graph.Gbar_def weighted_intersection_graph.Abar1_def algebra_simps)

lemma A2_reweight_tight:
  "\<lbrakk>(y, x) \<in> A2 X; y \<in> R; x \<notin> R; c2 x - c2 y = e\<rbrakk> \<Longrightarrow>
     (y, x) \<in> weighted_intersection_graph.Gbar carrier indep1 indep2
       c1 (\<lambda>z. if z \<in> R then c2 z + e else c2 z) X"
  using weighted_intersection_graph_intro
  by (auto simp: weighted_intersection_graph.Gbar_def weighted_intersection_graph.Abar2_def algebra_simps)

end

end
