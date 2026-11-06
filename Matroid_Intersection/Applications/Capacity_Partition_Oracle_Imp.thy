theory Capacity_Partition_Oracle_Imp
  imports Partition_Oracle_Imp
begin

section \<open>Partition Matroids with Capacities\<close>

text \<open>The carrier is partitioned into blocks by \<open>blk\<close>, and every block \<open>b\<close> has a
    capacity
  \<open>cap b\<close>. A set is independent iff it contains at most \<open>cap b\<close> elements of every block
    \<open>b\<close>.
  The unit partition matroids of @{theory Matroid_Intersection.Partition_Oracle} are the case
  \<open>cap = (\<lambda> _. 1)\<close>. The oracle works on the solution set itself: an insertion query compares
  the number of solution elements in the block of the new element with the capacity, and an
  exchange query (only asked when the block is full) compares two blocks. Imperatively, the
  counters per block of @{theory Matroid_Intersection.Partition_Oracle_Imp} and an array of
  capacities answer both in constant time; the exchange partners are again the blocks.\<close>

subsection \<open>Counting per Block\<close>

definition "blk_card blk X b = card {x \<in> X. blk x = b}"

lemma blk_card_insert:
  "\<lbrakk>finite X; x \<notin> X\<rbrakk> \<Longrightarrow>
   blk_card blk (insert x X) b = (if blk x = b then Suc (blk_card blk X b) else blk_card blk X b)"
  by (cases "blk x = b") (auto simp: blk_card_def conj_disj_distribR Collect_disj_eq Collect_conv_if)

lemma blk_card_delete:
  "\<lbrakk>finite X; x \<in> X\<rbrakk> \<Longrightarrow>
   blk_card blk (X - {x}) b = (if blk x = b then blk_card blk X b - 1 else blk_card blk X b)"
  using blk_card_insert[of "X - {x}" x blk b]
  by (auto simp: insert_absorb split: if_splits)

lemma blk_card_mono: "\<lbrakk>finite X; Y \<subseteq> X\<rbrakk> \<Longrightarrow> blk_card blk Y b \<le> blk_card
    blk X b"
  unfolding blk_card_def
  by (rule card_mono) auto

lemma blk_card_sum:
  "\<lbrakk>finite X; finite T; blk ` X \<subseteq> T\<rbrakk> \<Longrightarrow> card X = (\<Sum> b \<in> T. blk_card
    blk X b)"
  using sum.group[of X T blk "\<lambda> _. 1 :: nat"] unfolding blk_card_def
  by simp

lemma bcount_blk_card: "bcount bl X b = blk_card (\<lambda> i. bl ! i) X b"
  unfolding bcount_def blk_card_def ..

lemma blk_card_less:
  assumes "finite X" "finite Y" "card Y < card X"
  shows "\<exists> b. blk_card blk Y b < blk_card blk X b"
proof(rule ccontr)
  assume "\<nexists> b. blk_card blk Y b < blk_card blk X b"
  hence "blk_card blk X b \<le> blk_card blk Y b" for b
    using not_less
    by blast
  hence "(\<Sum> b \<in> blk ` (X \<union> Y). blk_card blk X b) \<le>
      (\<Sum> b \<in> blk ` (X \<union> Y). blk_card blk Y b)"
    by (rule sum_mono)
  moreover have "card X = (\<Sum> b \<in> blk ` (X \<union> Y). blk_card blk X b)"
    "card Y = (\<Sum> b \<in> blk ` (X \<union> Y). blk_card blk Y b)"
    by (rule blk_card_sum; use assms in auto)+
  ultimately show False
    using assms(3)
    by simp
qed

lemma blk_card_witness:
  assumes "finite Y" "blk_card blk Y b < blk_card blk X b"
  shows "\<exists> x \<in> X - Y. blk x = b"
  using assms card_mono[of "{z \<in> Y. blk z = b}" "{z \<in> X. blk z = b}"]
  by (auto simp: blk_card_def)

lemma blk_card_pos:
  "\<lbrakk>finite X; x \<in> X\<rbrakk> \<Longrightarrow> 0 < blk_card blk X (blk x)"
  by (auto simp: blk_card_def card_gt_0_iff)

subsection \<open>The Matroid\<close>

locale cap_partition_matroid =
  fixes carrier :: "'a set"
    and blk :: "'a \<Rightarrow> 'b"
    and cap :: "'b \<Rightarrow> nat"
  assumes carrier_finite: "finite carrier"
begin

definition "cap_indep X = (X \<subseteq> carrier \<and> (\<forall> b. blk_card blk X b \<le> cap b))"

lemma cap_indep_finite: "cap_indep X \<Longrightarrow> finite X"
  using carrier_finite finite_subset unfolding cap_indep_def
  by blast

lemma cap_indep_insert:
  assumes "cap_indep X" "y \<in> carrier - X"
  shows "cap_indep (insert y X) \<longleftrightarrow> blk_card blk X (blk y) < cap (blk y)"
  using assms cap_indep_finite[of X]
  by (auto simp: cap_indep_def blk_card_insert split: if_splits)

lemma cap_augment:
  assumes "cap_indep X" "cap_indep Y" "card Y < card X"
  shows "\<exists> x \<in> X - Y. cap_indep (insert x Y)"
proof-
  obtain b x where "x \<in> X - Y" "blk x = b" "blk_card blk Y b < blk_card blk X b"
    using assms cap_indep_finite blk_card_less[of X Y blk] blk_card_witness[of Y blk _ X]
    by blast
  moreover have "x \<in> carrier - Y"
    using calculation assms(1) unfolding cap_indep_def
    by blast
  ultimately show ?thesis
    using assms(1)[unfolded cap_indep_def]
    by (intro bexI[where x = x])
       (auto simp: cap_indep_insert[OF assms(2)]; blast intro: less_le_trans)
qed

lemma cap_indep_subset:
  "\<lbrakk>cap_indep X; Y \<subseteq> X\<rbrakk> \<Longrightarrow> cap_indep Y"
  using cap_indep_finite[of X] blk_card_mono[of X Y blk]
  by (auto simp: cap_indep_def) (blast intro: order_trans)

lemma cap_matroid: "matroid carrier cap_indep"
proof(unfold_locales, goal_cases)
  case 1
  show ?case
    by (rule carrier_finite)
next
  case 2
  then show ?case
    by (simp add: cap_indep_def)
next
  case 3
  show ?case
    by (rule exI[where x = "{}"]) (simp add: cap_indep_def blk_card_def)
next
  case 4
  then show ?case
    by (rule cap_indep_subset)
next
  case 5
  then show ?case
    by (intro cap_augment) simp_all
qed

sublocale cap: matroid carrier cap_indep
  by (rule cap_matroid)

lemma cap_indep_exch:
  assumes "cap_indep X" "y \<in> carrier - X" "x \<in> X" "\<not> cap_indep (insert y X)"
  shows "cap_indep (insert y (X - {x})) \<longleftrightarrow> blk x = blk y"
proof-
  note fin = cap_indep_finite[OF assms(1)]
  have full: "blk_card blk X (blk y) = cap (blk y)"
    using assms(1) assms(4)[unfolded cap_indep_insert[OF assms(1,2)]]
    by (auto simp: cap_indep_def intro: antisym)
  have "cap_indep (X - {x})" "y \<in> carrier - (X - {x})"
    using assms cap_indep_subset[of X "X - {x}"]
    by auto
  then show ?thesis
    using assms fin full blk_card_pos[of X x blk]
    by (auto simp: cap_indep_insert blk_card_delete split: if_splits)
qed

end

subsection \<open>The Oracle\<close>

text \<open>Solutions are sets; the oracle needs no preparation.\<close>

locale cap_partition_oracle = cap_partition_matroid
begin

definition "cap_ins X y = (blk_card blk X (blk y) < cap (blk y))"

definition "cap_exch (X :: 'a set) x y = (blk x = blk y)"

sublocale indep_oracle "\<lambda> X. X" cap_ins cap_exch carrier cap_indep "\<lambda> X. X" finite
proof(unfold_locales, goal_cases)
  case (1 X y)
  then show ?case
    by (simp add: cap_ins_def cap_indep_insert)
next
  case (2 X x y)
  then show ?case
    by (simp add: cap_exch_def cap_indep_exch)
qed

end

subsection \<open>Imperative Insertion Queries\<close>

text \<open>The capacities \<open>cap\<close> of the blocks below \<open>nb\<close> are an array. Counters, blocks,
    exchange
  queries and partners are those of the unit case.\<close>

definition "caps_assn nb cap Ka = Ka \<mapsto>\<^sub>a map cap [0..<nb]"

definition part_cap_ins_imp :: "nat array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat
    \<Rightarrow> bool Heap" where
  "part_cap_ins_imp Bl Ka C y = do {
     b \<leftarrow> Array.nth Bl y; c \<leftarrow> Array.nth C b; k \<leftarrow> Array.nth Ka b; return (c < k) }"

lemma caps_of_list: "<emp> Array.of_list (map cap [0..<nb]) <caps_assn nb cap>"
  unfolding caps_assn_def
  by sep_auto

lemma part_cap_ins_rule:
  "<cnt_assn nb bl X C * blocks_assn n nb bl Bl * caps_assn nb cap Ka * \<up>(y < n)>
     part_cap_ins_imp Bl Ka C y
   <\<lambda> r. cnt_assn nb bl X C * blocks_assn n nb bl Bl * caps_assn nb cap Ka *
         \<up>(finite X \<and> r = (blk_card (\<lambda> i. bl ! i) X (bl ! y) < cap (bl ! y)))>"
  unfolding part_cap_ins_imp_def cnt_assn_def blocks_assn_def caps_assn_def
  by (sep_auto simp: bcount_blk_card)


end
