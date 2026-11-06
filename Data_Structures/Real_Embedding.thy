theory Real_Embedding
  imports Complex_Main
begin

text \<open>A ring embedding of the executable value type @{typ 'n} into the reals: an order-preserving
      ring homomorphism. Instantiated by @{term id} for the real program and by @{const of_int} for the
      integer program, it lets us certify the generic @{typ 'n}-program against the real specification by
      reading every executable flow @{term f} through @{term \<open>h \<circ> f\<close>}.\<close>

locale real_embedding =
  fixes h :: "'n :: linordered_idom \<Rightarrow> real"
  assumes h_add:  "\<And>a b. h (a + b) = h a + h b"
      and h_mult: "\<And>a b. h (a * b) = h a * h b"
      and h_one:  "h 1 = 1"
      and h_strict_mono: "\<And>a b. a < b \<Longrightarrow> h a < h b"
begin

lemma h_zero [simp]: "h 0 = 0"
  using h_add[of 0 0]
  by simp

lemma h_uminus [simp]: "h (- a) = - h a"
  using h_add[of a "- a"]
  by simp

lemma h_diff [simp]: "h (a - b) = h a - h b"
  using h_add[of a "- b"]
  by simp

lemma h_less_iff [simp]: "h a < h b \<longleftrightarrow> a < b"
  by (cases a b rule: linorder_cases) (auto dest: h_strict_mono)

lemma h_le_iff [simp]: "h a \<le> h b \<longleftrightarrow> a \<le> b"
  by (simp flip: not_less)

lemma h_eq_iff [simp]: "h a = h b \<longleftrightarrow> a = b"
  by (auto simp: order_eq_iff[of a b] order_eq_iff[of "h a"])

lemma h_one' [simp]: "h 1 = 1"
  by (rule h_one)

lemma h_neg_one [simp]: "h (- 1) = - 1"
  by simp

lemma h_mono: "a \<le> b \<Longrightarrow> h a \<le> h b"
  by simp

lemma h_nonneg: "0 \<le> a \<Longrightarrow> 0 \<le> h a"
  using h_le_iff[of 0 a]
  by simp

lemma h_less_zero [simp]: "h a < 0 \<longleftrightarrow> a < 0"
  using h_less_iff[of a 0]
  by simp

lemma h_zero_less [simp]: "0 < h a \<longleftrightarrow> 0 < a"
  using h_less_iff[of 0 a]
  by simp

lemma h_le_zero  [simp]: "h a \<le> 0 \<longleftrightarrow> a \<le> 0"
  using h_le_iff[of a 0]
  by simp

lemma h_zero_le  [simp]: "0 \<le> h a \<longleftrightarrow> 0 \<le> a"
  using h_le_iff[of 0 a]
  by simp

lemma h_eq_zero  [simp]: "h a = 0 \<longleftrightarrow> a = 0"
  using h_eq_iff[of a 0]
  by simp

lemma h_eq_neg1  [simp]: "h a = - 1 \<longleftrightarrow> a = - 1"
  using h_eq_iff[of a "- 1"]
  by simp

lemma h_neg1_eq  [simp]: "- 1 = h a \<longleftrightarrow> a = - 1"
  by (subst eq_commute, simp)

lemma h_min [simp]: "h (min a b) = min (h a) (h b)"
  by (cases "a \<le> b") (simp_all add: min_def)

lemma h_max [simp]: "h (max a b) = max (h a) (h b)"
  by (cases "a \<le> b") (simp_all add: max_def)

lemma h_sum: "h (sum f A) = (\<Sum>a\<in>A. h (f a))"
  by (induction A rule: infinite_finite_induct) (simp_all add: h_add)

lemma h_of_nat [simp]: "h (of_nat M) = of_nat M"
  by (induction M) (simp_all add: h_add)

end

locale additive_real_embedding =
  fixes h :: "'n :: linordered_ab_group_add \<Rightarrow> real"
  assumes h_add: "\<And>a b. h (a + b) = h a + h b"
      and h_strict_mono: "\<And>a b. a < b \<Longrightarrow> h a < h b"
begin

lemma h_zero [simp]: "h 0 = 0"
  using h_add[of 0 0]
  by simp

lemma h_uminus [simp]: "h (- a) = - h a"
  using h_add[of a "- a"]
  by simp

lemma h_diff [simp]: "h (a - b) = h a - h b"
  using h_add[of a "- b"]
  by simp

lemma h_less_iff [simp]: "h a < h b \<longleftrightarrow> a < b"
  by (cases a b rule: linorder_cases) (auto dest: h_strict_mono)

lemma h_le_iff [simp]: "h a \<le> h b \<longleftrightarrow> a \<le> b"
  by (simp flip: not_less)

lemma h_eq_iff [simp]: "h a = h b \<longleftrightarrow> a = b"
  by (auto simp: order_eq_iff[of a b] order_eq_iff[of "h a"])

lemma h_inj: "inj h"
  by (simp add: inj_on_def)

lemma h_mono: "a \<le> b \<Longrightarrow> h a \<le> h b"
  by simp

lemma h_less_zero [simp]: "h a < 0 \<longleftrightarrow> a < 0"
  using h_less_iff[of a 0]
  by simp

lemma h_zero_less [simp]: "0 < h a \<longleftrightarrow> 0 < a"
  using h_less_iff[of 0 a]
  by simp

lemma h_le_zero  [simp]: "h a \<le> 0 \<longleftrightarrow> a \<le> 0"
  using h_le_iff[of a 0]
  by simp

lemma h_zero_le  [simp]: "0 \<le> h a \<longleftrightarrow> 0 \<le> a"
  using h_le_iff[of 0 a]
  by simp

lemma h_eq_zero  [simp]: "h a = 0 \<longleftrightarrow> a = 0"
  using h_eq_iff[of a 0]
  by simp

lemma h_min [simp]: "h (min a b) = min (h a) (h b)"
  by (cases "a \<le> b") (simp_all add: min_def)

lemma h_max [simp]: "h (max a b) = max (h a) (h b)"
  by (cases "a \<le> b") (simp_all add: max_def)

lemma h_sum: "h (sum f A) = (\<Sum>a\<in>A. h (f a))"
  by (induction A rule: infinite_finite_induct) (simp_all add: h_add)

lemma h_sum_list: "h (sum_list xs) = sum_list (map h xs)"
  by (induction xs) (simp_all add: h_add)

end

locale dist_embedding = additive_real_embedding where h = h
  for h :: "'n :: linordered_ab_group_add \<Rightarrow> real" +
  fixes unreached :: 'n
  assumes h_unreached [simp]: "h unreached = -1"
begin

lemma h_eq_neg1 [simp]: "h a = -1 \<longleftrightarrow> a = unreached"
  using h_eq_iff[of a unreached]
  by simp

lemma h_neg1_eq [simp]: "-1 = h a \<longleftrightarrow> a = unreached"
  by (subst eq_commute, simp)

end

end
