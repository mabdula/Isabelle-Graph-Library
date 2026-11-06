section \<open>Matroid Partitioning (Korte--Vygen \S13.6)\<close>

theory Matroid_Partitioning
  imports Matroid_Intersection Data_Structures.More_Logic
begin

text \<open>
  This theory formalises \S13.6 of Korte--Vygen, \<^emph>\<open>Combinatorial Optimization\<close>: the
    \<^emph>\<open>union\<close>
  (or \<^emph>\<open>sum\<close>) of finitely many matroids over a common ground set, and the Nash-Williams rank
  formula (Theorem 13.34), which is the single main theorem of the section.

  The proof of Theorem 13.34 in the book folds together several genuinely self-contained facts.
  We isolate each one as a standalone lemma:
    \<^item> the union is an \<^emph>\<open>independence system\<close> (@{text partitionable_indep_system});
    \<^item> a partition may always be replaced by a mere \<^emph>\<open>cover\<close> by independent sets, and vice
      versa
      (@{text partitionable_iff_cover});
    \<^item> weak duality \<open>|Y| \<le> |X - A| + (\<Sum>i r\<^sub>i(A))\<close> for a partition of \<open>Y
      \<subseteq> X\<close>
      (@{text partition_card_le}), hence the easy inequality of the rank formula
      (@{text partitionable_card_le_rank_formula});
    \<^item> a purely set-theoretic submodular inequality on the deleted parts
      (@{text card_Diff_Un_Int_le});
    \<^item> monotonicity and submodularity of the rank formula itself
      (@{text rank_formula_mono}, @{text rank_formula_submodular}).

  The submodular apparatus lets us discharge the Whitney direction (\<open>submodular rank \<Rightarrow>
    matroid\<close>,
  Theorem 13.10) \<^emph>\<open>inline\<close>: from the min-max reduction we prove the exchange (augment) property
  directly (@{text partitionable_augment_aux}).  The only ingredient left as an explicit hypothesis
  of the main theorem is the reduction itself (Edmonds' construction, Theorem 13.34's use of
  Theorem 13.31): that the rank formula is \<^emph>\<open>attained\<close> by an actual partitionable subset.  This is
  the content obtained by applying matroid intersection min-max (available in this development as
  @{thm [source] double_matroid.two_matroid_max_min_eq}) to the two auxiliary matroids on
  \<open>X \<times> {1..k}\<close> described in the book.
\<close>

subsection \<open>Definition 13.33: the union of matroids\<close>

text \<open>
  We fix a finite index set \<open>I\<close> and, for every \<open>i \<in> I\<close>, a matroid \<open>(carrier, indep
    i)\<close> over the
  common ground set \<open>carrier\<close>.  (Finiteness of \<open>carrier\<close> is only needed for the degenerate
    case
  \<open>I = {}\<close>; for a nonempty family it already follows from the matroid axioms.)
\<close>

locale matroid_partition =
  fixes carrier :: "'a set"
    and I :: "'i set"
    and indep :: "'i \<Rightarrow> 'a set \<Rightarrow> bool"
  assumes I_finite:       "finite I"
      and carrier_finite: "finite carrier"
      and matroids:       "\<And>i. i \<in> I \<Longrightarrow> matroid carrier (indep i)"
begin

text \<open>The rank function of the \<open>i\<close>-th matroid.\<close>

abbreviation r :: "'i \<Rightarrow> 'a set \<Rightarrow> nat" where
  "r i \<equiv> indep_system.lower_rank_of (indep i)"

text \<open>
  Definition 13.33.  A set \<open>X\<close> is \<^emph>\<open>partitionable\<close> if it splits into a disjoint union
  \<open>X = X\<^sub>1 \<union> \<dots> \<union> X\<^sub>k\<close> with \<open>X\<^sub>i\<close> independent in the
    \<open>i\<close>-th matroid.  The \<^emph>\<open>union\<close> of the family is the
  independence system with ground set \<open>carrier\<close> whose independent sets are the partitionable ones.
\<close>

definition partition_by :: "('i \<Rightarrow> 'a set) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "partition_by f X \<longleftrightarrow> (X = (\<Union>i\<in>I. f i)
                        \<and> (\<forall>i\<in>I. \<forall>j\<in>I. i \<noteq> j \<longrightarrow> f i \<inter> f j =
                          {})
                        \<and> (\<forall>i\<in>I. indep i (f i)))"

definition partitionable :: "'a set \<Rightarrow> bool" where
  "partitionable X \<longleftrightarrow> (\<exists>f. partition_by f X)"

text \<open>
  The target of the Nash-Williams rank formula: \<open>min\<^bsub>A \<subseteq> X\<^esub> (|X - A| + \<Sum>\<^sub>i
    r\<^sub>i(A))\<close>.
\<close>

definition rank_formula :: "'a set \<Rightarrow> nat" where
  "rank_formula X = Min ((\<lambda>A. card (X - A) + (\<Sum>i\<in>I. r i A)) ` Pow X)"

text \<open>
  \<^bold>\<open>Matroid Partitioning Problem\<close> (Korte--Vygen, \S13.6).  Given the family of matroids, the task is
  to find a partitionable subset of maximum cardinality.  A set \<open>X\<close> is an \<^emph>\<open>optimum
    solution\<close> --
  \<open>partition_opt X\<close> -- if it is itself partitionable and no partitionable set has larger cardinality.
  By the Nash-Williams theorem the union is a matroid, so an optimum solution is exactly a basis of
  the union and its cardinality equals the rank of the union, \<^term>\<open>rank_formula carrier\<close>.
\<close>

definition partition_opt :: "'a set \<Rightarrow> bool" where
  "partition_opt X \<longleftrightarrow> partitionable X \<and> (\<forall>Y. partitionable Y \<longrightarrow> card Y
    \<le> card X)"


subsection \<open>Basic facts about a single member of the family\<close>

lemma indep_system_i: "i \<in> I \<Longrightarrow> indep_system carrier (indep i)"
  using matroids matroid.axioms(1)
  by blast

lemma indep_subset_carrier: "\<lbrakk>i \<in> I; indep i A\<rbrakk> \<Longrightarrow> A \<subseteq> carrier"
  using indep_system_i indep_system.indep_subset_carrier
  by blast

lemma indep_empty_i: "i \<in> I \<Longrightarrow> indep i {}"
  using indep_system_i indep_system.indep_empty
  by blast

lemma indep_subset_i: "\<lbrakk>i \<in> I; indep i A; B \<subseteq> A\<rbrakk> \<Longrightarrow> indep i B"
  using indep_system_i indep_system.indep_subset
  by blast

lemma card_le_rank: "\<lbrakk>i \<in> I; indep i B; B \<subseteq> A; A \<subseteq> carrier\<rbrakk> \<Longrightarrow>
    card B \<le> r i A"
  by (auto intro!: matroid.rank_of_indep_in_le[OF matroids] indep_system.indep_inI[OF indep_system_i])

lemma r_mono: "\<lbrakk>i \<in> I; A \<subseteq> B; B \<subseteq> carrier\<rbrakk> \<Longrightarrow> r i A \<le> r i B"
  using matroids matroid.rank_of_mono
  by blast

lemma r_submod:
  "\<lbrakk>i \<in> I; A \<subseteq> carrier; B \<subseteq> carrier\<rbrakk> \<Longrightarrow> r i (A \<union> B) + r
    i (A \<inter> B) \<le> r i A + r i B"
  using matroids matroid.rank_of_Un_Int_le
  by blast

lemma r_empty: "i \<in> I \<Longrightarrow> r i {} = 0"
  using indep_system_i indep_system.lower_rank_of_le[of carrier "indep i" "{}"]
  by simp


subsection \<open>Elementary facts about partitionable sets\<close>

lemma partition_by_subset_carrier: "partition_by f X \<Longrightarrow> X \<subseteq> carrier"
  by (force simp: partition_by_def dest: indep_subset_carrier)

lemma partitionable_subset_carrier: "partitionable X \<Longrightarrow> X \<subseteq> carrier"
  using partition_by_subset_carrier
  by (auto simp: partitionable_def)

lemma partitionable_finite: "partitionable X \<Longrightarrow> finite X"
  using partitionable_subset_carrier carrier_finite finite_subset
  by blast


subsection \<open>Standalone lemma 1: the union is an independence system\<close>

lemma partitionable_empty: "partitionable {}"
  by (auto simp: partitionable_def partition_by_def indep_empty_i intro!: exI[of _ "\<lambda>_. {}"])

lemma partitionable_subset: "\<lbrakk>partitionable X; Y \<subseteq> X\<rbrakk> \<Longrightarrow> partitionable Y"
  unfolding partitionable_def partition_by_def
  by (elim exE, rule exI[of _ "\<lambda>i. _ i \<inter> Y"], auto elim: indep_subset_i)

lemma partitionable_indep_system: "indep_system carrier partitionable"
  by unfold_locales
     (auto simp: carrier_finite partitionable_subset_carrier intro: partitionable_empty partitionable_subset)


subsection \<open>Standalone lemma 2: partition versus cover\<close>

text \<open>
  Because each matroid is closed under subsets, requiring a \<^emph>\<open>disjoint\<close> partition is no stronger
  than requiring a mere cover by independent sets: any cover can be disjointified by assigning each
  element to one of the parts that contains it.
\<close>

lemma partitionable_iff_cover:
  "partitionable X \<longleftrightarrow> (\<exists>f. X = (\<Union>i\<in>I. f i) \<and> (\<forall>i\<in>I. indep i (f
    i)))"
proof
  assume "\<exists>f. X = (\<Union>i\<in>I. f i) \<and> (\<forall>i\<in>I. indep i (f i))"
  then obtain f where cover: "X = (\<Union>i\<in>I. f i)" "\<forall>i\<in>I. indep i (f i)"
    by blast
  define phi where "phi x = (SOME i. i \<in> I \<and> x \<in> f i)" for x
  have "phi x \<in> I \<and> x \<in> f (phi x)" if "x \<in> X" for x
    using that cover(1) someI_ex[of "\<lambda>i. i \<in> I \<and> x \<in> f i"]
    by (auto simp: phi_def)
  hence "partition_by (\<lambda>i. {x \<in> X. phi x = i}) X"
    using cover(2)
    by (fastforce simp: partition_by_def intro: indep_subset_i)
  thus "partitionable X"
    by (auto simp: partitionable_def)
qed (auto simp: partitionable_def partition_by_def)


subsection \<open>Standalone lemma 3: weak duality (the easy inequality)\<close>

text \<open>
  For any partition of a subset \<open>Y \<subseteq> X\<close> and any \<open>A \<subseteq> X\<close> the book's chain
    of inequalities
  \<open>|Y| = |Y - A| + |Y \<inter> A| \<le> |X - A| + \<Sum>\<^sub>i |Y\<^sub>i \<inter> A| \<le> |X - A| +
    \<Sum>\<^sub>i r\<^sub>i(A)\<close> holds.
\<close>

lemma partition_card_le:
  assumes "partition_by f Y" "Y \<subseteq> X" "A \<subseteq> X" "X \<subseteq> carrier"
  shows "card Y \<le> card (X - A) + (\<Sum>i\<in>I. r i A)"
proof-
  have "finite X"
    using assms(4) carrier_finite finite_subset
    by blast
  moreover hence fin: "finite Y"
    using assms(2) finite_subset
    by blast
  (* split off the part inside A; the part outside A is bounded by |X - A| *)
  ultimately have "card Y = card (Y \<inter> A) + card (Y - A)" "card (Y - A) \<le> card (X - A)"
    using assms(2)
    by (auto simp: card_Int_Diff intro: card_mono)
  (* the part inside A is a disjoint union of the traces *)
  moreover have "card (Y \<inter> A) = (\<Sum>i\<in>I. card (f i \<inter> A))"
    using assms(1) I_finite fin
    by (subst card_UN_disjoint[symmetric]) (auto simp: partition_by_def)
  moreover have "(\<Sum>i\<in>I. card (f i \<inter> A)) \<le> (\<Sum>i\<in>I. r i A)"
    using assms(1,3,4)
    by (intro sum_mono card_le_rank) (auto simp: partition_by_def intro: indep_subset_i)
  ultimately show ?thesis
    by linarith
qed


subsection \<open>Standalone lemma 4: the rank formula bounds every partitionable subset\<close>

lemma rank_formula_set_finite_nonempty:
  "X \<subseteq> carrier \<Longrightarrow> finite ((\<lambda>A. card (X - A) + (\<Sum>i\<in>I. r i A)) ` Pow X)"
  "X \<subseteq> carrier \<Longrightarrow>
    ((\<lambda>A. card (X - A) + (\<Sum>i\<in>I. r i A)) ` Pow X) \<noteq> {}"
  using carrier_finite finite_subset
  by auto

lemma rank_formula_le:
  "\<lbrakk>A \<subseteq> X; X \<subseteq> carrier\<rbrakk> \<Longrightarrow> rank_formula X \<le> card (X - A) +
    (\<Sum>i\<in>I. r i A)"
  using rank_formula_set_finite_nonempty
  by (auto simp: rank_formula_def intro!: Min_le)

lemma partitionable_card_le_rank_formula:
  "\<lbrakk>partitionable Y; Y \<subseteq> X; X \<subseteq> carrier\<rbrakk> \<Longrightarrow> card Y \<le>
    rank_formula X"
  using rank_formula_set_finite_nonempty partition_card_le
  by (fastforce simp: rank_formula_def partitionable_def Min_ge_iff)


subsection \<open>Standalone lemma 6: the rank formula is monotone and submodular\<close>

lemma rank_formula_attained:
  "X \<subseteq> carrier \<Longrightarrow> \<exists>A\<subseteq>X. rank_formula X = card (X - A) + (\<Sum>i\<in>I. r i
    A)"
  using Min_in[OF rank_formula_set_finite_nonempty, of X]
  by (auto simp: rank_formula_def)

lemma rank_formula_mono:
  assumes "X \<subseteq> Y" "Y \<subseteq> carrier"
  shows "rank_formula X \<le> rank_formula Y"
proof-
  obtain B where "B \<subseteq> Y" "rank_formula Y = card (Y - B) + (\<Sum>i\<in>I. r i B)"
    using assms(2) rank_formula_attained
    by blast
  moreover have "rank_formula X \<le> card (X - B \<inter> X) + (\<Sum>i\<in>I. r i (B \<inter> X))"
    using assms
    by (intro rank_formula_le) auto
  moreover have "card (X - B \<inter> X) \<le> card (Y - B)"
    using assms carrier_finite
    by (auto intro!: card_mono intro: finite_subset)
  moreover have "(\<Sum>i\<in>I. r i (B \<inter> X)) \<le> (\<Sum>i\<in>I. r i B)"
    using assms calculation(1)
    by (intro sum_mono r_mono) auto
  ultimately show ?thesis
    by linarith
qed

lemma rank_formula_submodular:
  assumes "X \<subseteq> carrier" "Y \<subseteq> carrier"
  shows "rank_formula (X \<union> Y) + rank_formula (X \<inter> Y) \<le> rank_formula X + rank_formula Y"
proof-
  obtain A where "A \<subseteq> X" "rank_formula X = card (X - A) + (\<Sum>i\<in>I. r i A)"
    using assms(1) rank_formula_attained
    by blast
  moreover obtain B where "B \<subseteq> Y" "rank_formula Y = card (Y - B) + (\<Sum>i\<in>I. r i B)"
    using assms(2) rank_formula_attained
    by blast
  (* apply the rank-formula bound at the witnesses A \<union> B and A \<inter> B *)
  moreover have "rank_formula (X \<union> Y) \<le> card ((X \<union> Y) - (A \<union> B)) + (\<Sum>i\<in>I. r i (A
    \<union> B))"
    "rank_formula (X \<inter> Y) \<le> card ((X \<inter> Y) - (A \<inter> B)) + (\<Sum>i\<in>I. r i (A \<inter> B))"
    using assms calculation
    by (auto intro!: rank_formula_le)
  (* the set part is submodular *)
  moreover have "card ((X \<union> Y) - (A \<union> B)) + card ((X \<inter> Y) - (A \<inter> B)) \<le> card (X - A) +
    card (Y - B)"
    using assms carrier_finite
    by (intro card_Diff_Un_Int_le) (auto intro: finite_subset)
  (* the rank part is submodular in each matroid *)
  moreover have "(\<Sum>i\<in>I. r i (A \<union> B)) + (\<Sum>i\<in>I. r i (A \<inter> B)) \<le> (\<Sum>i\<in>I. r i
    A) + (\<Sum>i\<in>I. r i B)"
    using assms calculation(1,3)
    by (auto simp flip: sum.distrib intro!: sum_mono r_submod)
  ultimately show ?thesis
    by linarith
qed
subsection \<open>The main theorem: Nash-Williams (Theorem 13.34)\<close>

text \<open>
  We first collect the consequences of monotonicity and submodularity that turn the rank formula
  into a genuine matroid rank function (the Whitney direction of Theorem 13.10): a unit-increase
  law and the ``absorption'' lemma familiar from the AFP @{theory Matroids.Matroid} development.
\<close>

lemma rank_formula_insert_le:
  assumes "X \<subseteq> carrier" "x \<in> carrier"
  shows "rank_formula (insert x X) \<le> Suc (rank_formula X)"
proof-
  obtain A where "A \<subseteq> X" "rank_formula X = card (X - A) + (\<Sum>i\<in>I. r i A)"
    using assms(1) rank_formula_attained
    by blast
  moreover have "rank_formula (insert x X) \<le> card (insert x X - A) + (\<Sum>i\<in>I. r i A)"
    using assms calculation(1)
    by (intro rank_formula_le) auto
  moreover have "card (insert x X - A) \<le> Suc (card (X - A))"
    using assms(1) carrier_finite rev_finite_subset[of carrier X]
    by (auto simp: insert_Diff_if card_insert_if)
  ultimately show ?thesis
    by linarith
qed

lemma rank_formula_Un_absorbI:
  assumes "X \<subseteq> carrier" "Y \<subseteq> carrier"
    and "\<And>y. y \<in> Y - X \<Longrightarrow> rank_formula (insert y X) = rank_formula X"
  shows "rank_formula (X \<union> Y) = rank_formula X"
proof-
  have "finite (Y - X)"
    using assms(2) carrier_finite finite_subset
    by blast
  thus ?thesis
    using assms
  proof(induction "Y - X" arbitrary: Y rule: finite_induct)
    case (insert y F)
    have "rank_formula ((X \<union> (Y - {y})) \<union> insert y X) + rank_formula ((X \<union> (Y - {y})) \<inter>
      insert y X)
            \<le> rank_formula (X \<union> (Y - {y})) + rank_formula (insert y X)"
      using insert
      by (intro rank_formula_submodular) auto
    moreover have "(X \<union> (Y - {y})) \<union> insert y X = X \<union> Y" "(X \<union> (Y - {y})) \<inter> insert
      y X = X"
      using insert
      by auto
    moreover have "rank_formula (insert y X) = rank_formula X"
      using insert.hyps(4) insert.prems(3)
      by blast
    moreover have "rank_formula (X \<union> (Y - {y})) = rank_formula X"
      using insert
      by (intro insert.hyps(3)) auto
    moreover have "rank_formula X \<le> rank_formula (X \<union> Y)"
      using insert
      by (intro rank_formula_mono) auto
    ultimately show ?case
      by simp
  qed (auto simp: Un_absorb2)
qed

lemma rank_formula_le_card: "X \<subseteq> carrier \<Longrightarrow> rank_formula X \<le> card X"
  using rank_formula_le[of "{}" X]
  by (simp add: r_empty)

lemma partitionable_imp_rank_formula_eq_card: "partitionable X \<Longrightarrow> rank_formula X = card X"
  using partitionable_card_le_rank_formula[of X X] rank_formula_le_card[of X]
    partitionable_subset_carrier[of X]
  by (auto intro: le_antisym)

text \<open>
  The one deep ingredient of Theorem 13.34 is the reduction to matroid intersection (Edmonds'
  construction): the rank formula is \<^emph>\<open>attained\<close> by an actual partitionable subset.  We take it as
    an
  explicit hypothesis (the first assumption below); it is exactly what applying the
  matroid-intersection min-max theorem @{thm [source] double_matroid.two_matroid_max_min_eq} to the
  two auxiliary matroids of the book yields.  Everything else --- including matroid-ness --- is
  derived from it below.
\<close>

lemma rank_full_imp_partitionable:
  assumes "\<And>Z. Z \<subseteq> carrier \<Longrightarrow> \<exists>Y. partitionable Y \<and> Y \<subseteq> Z \<and>
    card Y = rank_formula Z"
    and "X \<subseteq> carrier" "rank_formula X = card X"
  shows "partitionable X"
proof-
  obtain Y where "partitionable Y" "Y \<subseteq> X" "card Y = rank_formula X"
    using assms(1,2)
    by blast
  moreover have "finite X"
    using assms(2) carrier_finite finite_subset
    by blast
  ultimately show ?thesis
    using assms(3) card_subset_eq[of X Y]
    by auto
qed

text \<open>
  The exchange property.  If no element of \<open>P - Q\<close> can be added to \<open>Q\<close>, then --- by
    unit-increase and
  the converse above --- none of them raises the rank of \<open>Q\<close>; absorption then collapses the rank of
  \<open>Q \<union> P\<close> down to \<open>|Q|\<close>, contradicting \<open>|P| > |Q|\<close>.  This is the inline
    Whitney argument (Thm 13.10).
\<close>

lemma partitionable_augment_aux:
  assumes "\<And>Z. Z \<subseteq> carrier \<Longrightarrow> \<exists>Y. partitionable Y \<and> Y \<subseteq> Z \<and>
    card Y = rank_formula Z"
    and "partitionable P" "partitionable Q" "card P = Suc (card Q)"
  shows "\<exists>e\<in>P - Q. partitionable (insert e Q)"
proof(rule ccontr, goal_cases)
  case 1
  (* no element of P - Q raises the rank of Q *)
  have "rank_formula (insert e Q) = rank_formula Q" if "e \<in> P - Q" for e
  proof-
    have "rank_formula (insert e Q) \<noteq> Suc (rank_formula Q)"
    proof
      assume "rank_formula (insert e Q) = Suc (rank_formula Q)"
      hence "partitionable (insert e Q)"
        using that assms partitionable_subset_carrier partitionable_finite
          partitionable_imp_rank_formula_eq_card
        by (intro rank_full_imp_partitionable) auto
      thus False
        using that 1
        by blast
    qed
    moreover have "rank_formula Q \<le> rank_formula (insert e Q)"
      "rank_formula (insert e Q) \<le> Suc (rank_formula Q)"
      using that assms(2,3) partitionable_subset_carrier
      by (auto intro: rank_formula_mono rank_formula_insert_le)
    ultimately show ?thesis
      by linarith
  qed
  (* hence the whole of P can be absorbed without changing the rank *)
  hence "rank_formula (Q \<union> P) = rank_formula Q"
    using assms(2,3) partitionable_subset_carrier
    by (intro rank_formula_Un_absorbI) auto
  moreover have "card P \<le> rank_formula (Q \<union> P)"
    using assms(2,3) partitionable_subset_carrier
    by (intro partitionable_card_le_rank_formula) auto
  ultimately show False
    using assms(3,4) partitionable_imp_rank_formula_eq_card
    by simp
qed

lemma union_is_matroid:
  assumes "\<And>Z. Z \<subseteq> carrier \<Longrightarrow> \<exists>Y. partitionable Y \<and> Y \<subseteq> Z \<and>
    card Y = rank_formula Z"
  shows "matroid carrier partitionable"
  using assms partitionable_augment_aux
  by (intro matroid.intro partitionable_indep_system) (auto simp: matroid_axioms_def)

lemma nash_williams_rank:
  assumes "\<And>Z. Z \<subseteq> carrier \<Longrightarrow> \<exists>Y. partitionable Y \<and> Y \<subseteq> Z \<and>
    card Y = rank_formula Z"
    and "X \<subseteq> carrier"
  shows "indep_system.lower_rank_of partitionable X = rank_formula X"
proof-
  interpret U: matroid carrier partitionable
    using assms(1)
    by (rule union_is_matroid)
  obtain Y where "partitionable Y" "Y \<subseteq> X" "card Y = rank_formula X"
    using assms(1)[of X] assms(2)
    by blast
  hence "rank_formula X \<le> U.rank_of X"
    using assms(2) U.rank_of_indep_in_le[of X Y]
    by (simp add: U.indep_in_def)
  moreover obtain B where "U.basis_in X B"
    using assms(2) U.basis_in_ex[of X]
    by blast
  hence "U.rank_of X \<le> rank_formula X"
    using assms(2) U.rank_of_eq_card_basis_in[of X B] U.basis_in_indep_in[of X B]
      partitionable_card_le_rank_formula[of B X]
    by (force simp: U.indep_in_def)
  ultimately show ?thesis
    by linarith
qed

text \<open>
  Theorem 13.34 (Nash-Williams).  The union of the matroids is itself a matroid, and its rank
  function is the rank formula.
\<close>

lemma nash_williams:
  assumes "\<And>Z. Z \<subseteq> carrier \<Longrightarrow> \<exists>Y. partitionable Y \<and> Y \<subseteq> Z \<and>
    card Y = rank_formula Z"
  shows "matroid carrier partitionable"
    and "X \<subseteq> carrier \<Longrightarrow> indep_system.lower_rank_of partitionable X = rank_formula X"
  using assms
  by (simp_all add: union_is_matroid nash_williams_rank)

end


subsection \<open>Discharging the reduction: Edmonds' two auxiliary matroids\<close>

text \<open>
  We now discharge the hypothesis @{text attn} of Theorem 13.34, obtaining the unconditional
  statement.  Following Edmonds' construction (the proof of Theorem 13.34 in Korte--Vygen), for a
  fixed \<open>X \<subseteq> carrier\<close> we build two matroids on the ground set \<open>X \<times> I\<close> (the
    \<open>|I|\<close> copies of \<open>X\<close>):
    \<^item> the \<^emph>\<open>direct sum\<close> \<open>pindep1\<close>, whose independent sets are those whose
      \<open>i\<close>-th section is
      independent in the \<open>i\<close>-th matroid; its rank is \<open>\<Sum>i r\<^sub>i(section i)\<close>;
    \<^item> the \<^emph>\<open>partition matroid\<close> \<open>pindep2\<close>, whose independent sets are those on
      which the first
      projection is injective (at most one copy of each element); its rank is the number of
      distinct elements used.
  A common independent set of the two corresponds to a partition of a subset of \<open>X\<close>, so the
  matroid-intersection min-max theorem @{thm [source] double_matroid.two_matroid_max_min_eq}
  yields that the largest partitionable subset of \<open>X\<close> has cardinality \<open>rank_formula X\<close>.
\<close>

context matroid_partition
begin

text \<open>The \<open>i\<close>-th section of \<open>R \<subseteq> X \<times> I\<close> is just the fibre
    \<open>R\<inverse> `` {i}\<close> of the relation \<open>R\<close>;
  we only introduce the notation \<open>sect\<close> for readability, together with its unfolding lemma.\<close>

abbreviation sect :: "('a \<times> 'i) set \<Rightarrow> 'i \<Rightarrow> 'a set" where
  "sect R i \<equiv> R\<inverse> `` {i}"

lemma sect_def: "sect R i = {e. (e, i) \<in> R}"
  by auto

definition pindep1 :: "'a set \<Rightarrow> ('a \<times> 'i) set \<Rightarrow> bool" where
  "pindep1 X Q \<longleftrightarrow> Q \<subseteq> X \<times> I \<and> (\<forall>i\<in>I. indep i (sect Q i))"

definition pindep2 :: "'a set \<Rightarrow> ('a \<times> 'i) set \<Rightarrow> bool" where
  "pindep2 X Q \<longleftrightarrow> Q \<subseteq> X \<times> I \<and> inj_on fst Q"

lemma sect_subset_X: "R \<subseteq> X \<times> I \<Longrightarrow> sect R i \<subseteq> X"
  by (auto simp: sect_def)

lemma sect_mono: "R \<subseteq> S \<Longrightarrow> sect R i \<subseteq> sect S i"
  by (auto simp: sect_def)

lemma sect_insert:
  "sect (insert (e, i0) Q) i = (if i = i0 then insert e (sect Q i) else sect Q i)"
  by (auto simp: sect_def)

lemma finite_carr': "X \<subseteq> carrier \<Longrightarrow> finite (X \<times> I)"
  using carrier_finite I_finite finite_subset
  by blast

lemma card_eq_sum_sect:
  assumes "R \<subseteq> X \<times> I" "finite X"
  shows "card R = (\<Sum>i\<in>I. card (sect R i))"
proof-
  have "R = (\<Union>i\<in>I. (\<lambda>e. (e, i)) ` sect R i)"
    using assms(1)
    by (auto simp: sect_def)
  moreover have "card (\<Union>i\<in>I. (\<lambda>e. (e, i)) ` sect R i) = (\<Sum>i\<in>I. card ((\<lambda>e. (e, i))
    ` sect R i))"
    using assms I_finite finite_subset[of R "X \<times> I"]
    by (intro card_UN_disjoint) (auto simp: sect_def intro: finite_subset)
  ultimately show ?thesis
    by (simp add: card_image inj_on_def)
qed


subsubsection \<open>The partition matroid\<close>

lemma indep_system_pindep2: "X \<subseteq> carrier \<Longrightarrow> indep_system (X \<times> I) (pindep2 X)"
  by unfold_locales
     (auto simp: finite_carr' pindep2_def intro: inj_on_subset exI[of _ "{}"])

lemma matroid_pindep2:
  assumes "X \<subseteq> carrier"
  shows "matroid (X \<times> I) (pindep2 X)"
proof(rule matroid.intro[OF indep_system_pindep2[OF assms]], unfold matroid_axioms_def,
      intro allI impI, goal_cases)
  case (1 P Q)
  hence "\<not> fst ` P \<subseteq> fst ` Q"
    using finite_carr'[OF assms] card_mono[of "fst ` Q" "fst ` P"]
    by (auto simp: pindep2_def card_image intro: finite_subset)
  then obtain e i where "(e, i) \<in> P" "e \<notin> fst ` Q"
    by fastforce
  thus "\<exists>x\<in>P - Q. pindep2 X (insert x Q)"
    using 1
    by (auto simp: pindep2_def intro!: bexI[of _ "(e, i)"] intro: rev_image_eqI)
qed

lemma rank2_eq:
  assumes "X \<subseteq> carrier" "R \<subseteq> X \<times> I"
  shows "indep_system.lower_rank_of (pindep2 X) R = card (fst ` R)"
proof-
  interpret M2: matroid "X \<times> I" "pindep2 X"
    using assms(1)
    by (rule matroid_pindep2)
  define T where "T = (\<lambda>e. (e, SOME i. (e, i) \<in> R)) ` (fst ` R)"
  have fin: "finite R"
    using assms finite_carr' finite_subset
    by blast
  obtain B where "M2.basis_in R B"
    using assms(2) M2.basis_in_ex
    by blast
  hence "inj_on fst B" "B \<subseteq> R" "M2.rank_of R = card B"
    using assms(2) M2.basis_in_indep_in[of R B] M2.rank_of_eq_card_basis_in[of R B]
    by (auto simp: M2.indep_in_def pindep2_def)
  hence "M2.rank_of R \<le> card (fst ` R)"
    using fin card_image[of fst B] card_mono[of "fst ` R" "fst ` B"] image_mono[of B R fst]
    by simp
  moreover have "T \<subseteq> R" "inj_on fst T" "fst ` T = fst ` R"
    by (force simp: T_def intro: someI) (auto simp: T_def inj_on_def image_image)
  hence "card (fst ` R) \<le> M2.rank_of R"
    using assms(2) M2.rank_of_indep_in_le[of R T] card_image[of fst T]
    by (auto simp: M2.indep_in_def pindep2_def)
  ultimately show ?thesis
    by linarith
qed


subsubsection \<open>The direct-sum matroid\<close>

lemma indep_system_pindep1: "X \<subseteq> carrier \<Longrightarrow> indep_system (X \<times> I) (pindep1 X)"
  using indep_subset_i sect_mono
  by unfold_locales (fastforce simp: finite_carr' pindep1_def indep_empty_i intro: exI[of _ "{}"])+

lemma matroid_pindep1:
  assumes "X \<subseteq> carrier"
  shows "matroid (X \<times> I) (pindep1 X)"
proof(rule matroid.intro[OF indep_system_pindep1[OF assms]], unfold matroid_axioms_def,
      intro allI impI, goal_cases)
  case (1 P Q)
  moreover have "finite X"
    using assms carrier_finite finite_subset
    by blast
  ultimately have "(\<Sum>i\<in>I. card (sect Q i)) < (\<Sum>i\<in>I. card (sect P i))"
    using card_eq_sum_sect[of P X] card_eq_sum_sect[of Q X]
    by (simp add: pindep1_def)
  hence "\<exists>i\<in>I. card (sect Q i) < card (sect P i)"
    using sum_mono[of I "\<lambda>i. card (sect P i)" "\<lambda>i. card (sect Q i)"]
    by (force simp: not_less)
  then obtain i where "i \<in> I" "card (sect Q i) < card (sect P i)"
    by blast
  moreover hence "indep i (sect P i)" "indep i (sect Q i)"
    using 1
    by (auto simp: pindep1_def)
  ultimately obtain e where "e \<in> sect P i - sect Q i" "indep i (insert e (sect Q i))"
    using matroid.augment[OF matroids[of i]]
    by blast
  thus "\<exists>x\<in>P - Q. pindep1 X (insert x Q)"
    using 1
    by (auto simp: pindep1_def sect_insert intro!: bexI[of _ "(e, i)"])
qed

lemma sect_basis_exists:
  assumes "i \<in> I" "S \<subseteq> carrier"
  shows "\<exists>B. indep i B \<and> B \<subseteq> S \<and> card B = r i S"
proof-
  interpret M: matroid carrier "indep i"
    using assms(1)
    by (rule matroids)
  obtain B where "M.basis_in S B"
    using assms(2) M.basis_in_ex
    by blast
  thus ?thesis
    using assms(2) M.basis_in_indep_in[of S B] M.rank_of_eq_card_basis_in[of S B]
    by (auto simp: M.indep_in_def intro!: exI[of _ B])
qed

lemma rank1_eq:
  assumes "X \<subseteq> carrier" "R \<subseteq> X \<times> I"
  shows "indep_system.lower_rank_of (pindep1 X) R = (\<Sum>i\<in>I. r i (sect R i))"
proof-
  interpret M1: matroid "X \<times> I" "pindep1 X"
    using assms(1)
    by (rule matroid_pindep1)
  have fin: "finite X"
    using assms(1) carrier_finite finite_subset
    by blast
  have "\<forall>i\<in>I. \<exists>B. indep i B \<and> B \<subseteq> sect R i \<and> card B = r i (sect R i)"
    using assms
    by (intro ballI sect_basis_exists) (auto simp: sect_def)
  then obtain bas where bas: "\<forall>i\<in>I. indep i (bas i) \<and> bas i \<subseteq> sect R i \<and> card (bas i)
    = r i (sect R i)"
    using bchoice[of I "\<lambda>i B. indep i B \<and> B \<subseteq> sect R i \<and> card B = r i (sect R i)"]
    by blast
  define T where "T = (\<Union>i\<in>I. (\<lambda>e. (e, i)) ` bas i)"
  obtain B where "M1.basis_in R B"
    using assms(2) M1.basis_in_ex
    by blast
  hence "pindep1 X B" "B \<subseteq> R" "M1.rank_of R = card B"
    using assms(2) M1.basis_in_indep_in[of R B] M1.rank_of_eq_card_basis_in[of R B]
    by (auto simp: M1.indep_in_def)
  hence "M1.rank_of R \<le> (\<Sum>i\<in>I. r i (sect R i))"
    using assms fin card_eq_sum_sect[of B X]
    by (auto simp: pindep1_def intro!: sum_mono card_le_rank)
  moreover have "\<And>i. i \<in> I \<Longrightarrow> sect T i = bas i" "T \<subseteq> R"
    using bas
    by (auto simp: T_def)
  hence "(\<Sum>i\<in>I. r i (sect R i)) \<le> M1.rank_of R"
    using assms fin card_eq_sum_sect[of T X] M1.rank_of_indep_in_le[of R T]
      bas
    by (auto simp: M1.indep_in_def pindep1_def)
  ultimately show ?thesis
    by linarith
qed


subsubsection \<open>The reduction and the unconditional theorem\<close>

lemma common_partition_by:
  assumes "pindep1 X Q" "pindep2 X Q"
  shows "partition_by (sect Q) (fst ` Q)"
  unfolding partition_by_def
proof(intro conjI ballI impI)
  show "fst ` Q = (\<Union>i\<in>I. sect Q i)"
    using assms(1)
    by (force simp: pindep1_def)
  show "sect Q i \<inter> sect Q j = {}" if "i \<in> I" "j \<in> I" "i \<noteq> j" for i j
    using that assms(2)
    by (force simp: pindep2_def inj_on_def)
  show "indep i (sect Q i)" if "i \<in> I" for i
    using that assms(1)
    by (simp add: pindep1_def)
qed

lemma common_imp_partitionable_fst:
  "\<lbrakk>pindep1 X Q; pindep2 X Q\<rbrakk> \<Longrightarrow> partitionable (fst ` Q)"
  "\<lbrakk>pindep1 X Q; pindep2 X Q\<rbrakk> \<Longrightarrow> card (fst ` Q) = card Q"
  using common_partition_by[of X Q]
  by (auto simp: partitionable_def pindep2_def card_image)

lemma common_imp_partitionable:
  "\<lbrakk>X \<subseteq> carrier; pindep1 X Q; pindep2 X Q\<rbrakk> \<Longrightarrow> \<exists>Y. partitionable Y
    \<and> Y \<subseteq> X \<and> card Y = card Q"
  using common_imp_partitionable_fst[of X Q]
  by (intro exI[of _ "fst ` Q"]) (auto simp: pindep1_def)

lemma fst_Diff_carr': "R \<subseteq> X \<times> I \<Longrightarrow> fst ` (X \<times> I - R) = X - (\<Inter>i\<in>I.
    sect R i)"
  by (auto simp: sect_def) (force intro: rev_image_eqI)

lemma rank2_compl:
  "\<lbrakk>X \<subseteq> carrier; R \<subseteq> X \<times> I\<rbrakk> \<Longrightarrow>
     indep_system.lower_rank_of (pindep2 X) (X \<times> I - R) = card (X - (\<Inter>i\<in>I. sect R i))"
  using rank2_eq[of X "X \<times> I - R"] fst_Diff_carr'
  by auto

text \<open>The min side of the matroid-intersection min-max theorem for the two auxiliary matroids
  is the rank formula.\<close>

lemma min_side_eq_rank_formula:
  assumes "X \<subseteq> carrier" "I \<noteq> {}"
  shows "Min {indep_system.lower_rank_of (pindep1 X) R + indep_system.lower_rank_of (pindep2 X) (X \<times> I - R)
              |R. R \<subseteq> X \<times> I} = rank_formula X" (is "Min ?S = _")
proof(rule Min_eqI)
  show "finite ?S"
    using finite_carr'[OF assms(1)]
    by (auto intro: finite_image_set simp flip: Pow_def)
next
  fix v
  assume "v \<in> ?S"
  then obtain R where "R \<subseteq> X \<times> I" "v = (\<Sum>i\<in>I. r i (sect R i)) + card (X - (\<Inter>i\<in>I.
    sect R i))"
    using assms(1)
    by (auto simp: rank1_eq rank2_compl)
  moreover have "rank_formula X \<le> card (X - (\<Inter>i\<in>I. sect R i)) + (\<Sum>i\<in>I. r i (\<Inter>i\<in>I.
    sect R i))"
    using assms calculation(1)
    by (intro rank_formula_le) auto
  moreover have "(\<Sum>i\<in>I. r i (\<Inter>i\<in>I. sect R i)) \<le> (\<Sum>i\<in>I. r i (sect R i))"
    using assms calculation(1)
    by (intro sum_mono r_mono) auto
  ultimately show "rank_formula X \<le> v"
    by linarith
next
  obtain A where "A \<subseteq> X" "rank_formula X = card (X - A) + (\<Sum>i\<in>I. r i A)"
    using assms(1) rank_formula_attained
    by blast
  moreover hence "A \<times> I \<subseteq> X \<times> I"
    by auto
  moreover have "\<And>i. i \<in> I \<Longrightarrow> sect (A \<times> I) i = A"
    by (auto simp: sect_def)
  moreover have "(\<Inter>i\<in>I. sect (A \<times> I) i) = A"
    using assms(2)
    by auto
  ultimately show "rank_formula X \<in> ?S"
    using rank1_eq[OF assms(1), of "A \<times> I"] rank2_compl[OF assms(1), of "A \<times> I"]
    by (auto cong: sum.cong intro!: exI[of _ "A \<times> I"])
qed

lemma max_common_exists:
  assumes "X \<subseteq> carrier"
  shows "\<exists>Q. pindep1 X Q \<and> pindep2 X Q \<and> card Q = Max {card Q |Q. pindep1 X Q \<and> pindep2 X Q}"
proof-
  have "finite {card Q |Q. pindep1 X Q \<and> pindep2 X Q}"
    using finite_carr'[OF assms]
    by (auto simp: pindep1_def intro: finite_subset[of _ "card ` Pow (X \<times> I)"])
  moreover have "pindep1 X {} \<and> pindep2 X {}"
    by (auto simp: pindep1_def pindep2_def indep_empty_i)
  ultimately show ?thesis
    using Max_in[of "{card Q |Q. pindep1 X Q \<and> pindep2 X Q}"]
    by force
qed

lemma partition_rank_attained:
  assumes "X \<subseteq> carrier"
  shows "\<exists>Y. partitionable Y \<and> Y \<subseteq> X \<and> card Y = rank_formula X"
proof(cases "I = {}")
  case True
  thus ?thesis
    using assms rank_formula_le[of X X] partitionable_empty
    by (auto intro!: exI[of _ "{}"])
next
  case False
  interpret dm: double_matroid "X \<times> I" "pindep1 X" "pindep2 X"
    using assms
    by (intro double_matroid.intro matroid_pindep1 matroid_pindep2)
  obtain Q where "pindep1 X Q" "pindep2 X Q" "card Q = Max {card Q |Q. pindep1 X Q \<and> pindep2 X Q}"
    using assms max_common_exists
    by blast
  moreover hence "card Q = rank_formula X"
    using assms False dm.two_matroid_max_min_eq min_side_eq_rank_formula
    by simp
  ultimately show ?thesis
    using assms common_imp_partitionable[of X Q]
    by simp
qed

text \<open>Theorem 13.34, unconditionally: the union of the matroids is a matroid whose rank
  function is the Nash-Williams formula.\<close>

lemma nash_williams_unconditional:
  shows "matroid carrier partitionable"
    and "X \<subseteq> carrier \<Longrightarrow> indep_system.lower_rank_of partitionable X = rank_formula X"
  using nash_williams[OF partition_rank_attained]
  by blast+


subsection \<open>Reduction: an optimum partition from a matroid intersection\<close>

text \<open>
  The construction inside the Nash-Williams proof also \<^emph>\<open>solves\<close> the Matroid Partitioning Problem.
  On the ground set \<^term>\<open>carrier \<times> I\<close> the two auxiliary matroids \<^term>\<open>pindep1
    carrier\<close> (direct sum)
  and \<^term>\<open>pindep2 carrier\<close> (partition matroid) form a \<^locale>\<open>double_matroid\<close>, and
    common
  independent sets of the two correspond -- cardinality-preservingly -- to partitionable subsets of
  \<^term>\<open>carrier\<close> via the first projection \<open>fst\<close>.  Hence projecting a
    \<^emph>\<open>maximum\<close> common independent
  set (an optimum of the matroid intersection problem, \<^const>\<open>double_matroid.is_max\<close>) yields an
  optimum solution of the partitioning problem.  A matroid-intersection algorithm applied to the two
  auxiliary matroids therefore solves matroid partitioning.

  The forward map is @{thm [source] common_imp_partitionable_fst} above: a common independent set
  projects, under \<open>fst\<close>, to a partition of the same size.
\<close>

text \<open>Backward map: a partitionable set lifts to a common independent set of the same size,
by tagging each element with the (unique) part it lies in.\<close>

lemma partitionable_imp_common:
  assumes "partitionable Y"
  shows "\<exists>Q. pindep1 carrier Q \<and> pindep2 carrier Q \<and> fst ` Q = Y \<and> card Q = card Y"
proof-
  obtain f where "partition_by f Y"
    using assms
    by (auto simp: partitionable_def)
  hence "Y = (\<Union>i\<in>I. f i)" "\<forall>i\<in>I. \<forall>j\<in>I. i \<noteq> j \<longrightarrow> f i \<inter>
    f j = {}" "\<forall>i\<in>I. indep i (f i)"
    "Y \<subseteq> carrier"
    using partition_by_subset_carrier
    by (simp_all add: partition_by_def)
  moreover define Q where "Q = (\<Union>i\<in>I. (\<lambda>e. (e, i)) ` f i)"
  moreover have "\<And>i. i \<in> I \<Longrightarrow> sect Q i = f i"
    by (auto simp: Q_def sect_def)
  ultimately have "pindep1 carrier Q" "inj_on fst Q" "fst ` Q = Y"
    by (auto simp: pindep1_def)
       (auto simp: inj_on_def disjoint_iff, force simp: image_UN image_image)
  thus ?thesis
    using card_image[of fst Q]
    by (auto simp: pindep2_def pindep1_def)
qed

text \<open>Main reduction: the \<open>fst\<close>-image of a \<^emph>\<open>maximum\<close> common independent set of
    the two auxiliary
matroids is an optimum solution of the matroid partitioning problem.\<close>

lemma partition_opt_from_intersection:
  assumes "pindep1 carrier Q" "pindep2 carrier Q"
    and "\<And>Q'. \<lbrakk>pindep1 carrier Q'; pindep2 carrier Q'\<rbrakk> \<Longrightarrow> card Q' \<le> card Q"
  shows "partition_opt (fst ` Q)"
  using assms partitionable_imp_common common_imp_partitionable_fst
  by (force simp: partition_opt_def)

text \<open>Phrased with the matroid-intersection optimum predicate \<^const>\<open>double_matroid.is_max\<close>:
    exactly
what a maximum-cardinality matroid-intersection algorithm returns for the two auxiliary matroids.\<close>

lemma partition_opt_from_is_max:
  "double_matroid.is_max (pindep1 carrier) (pindep2 carrier) Q \<Longrightarrow> partition_opt (fst ` Q)"
  using double_matroid.is_max_def[OF double_matroid.intro[OF matroid_pindep1 matroid_pindep2]]
  by (auto simp: not_less intro!: partition_opt_from_intersection)

text \<open>Sanity: an optimum partition exists, and its cardinality is the rank of the union
(the Nash-Williams value).\<close>

lemma partition_opt_card: "partition_opt X \<Longrightarrow> card X = rank_formula carrier"
  using partition_rank_attained[of carrier] partitionable_card_le_rank_formula partitionable_subset_carrier
  by (force simp: partition_opt_def intro: le_antisym)

lemma partition_opt_exists: "\<exists>X. partition_opt X"
  using partition_rank_attained[of carrier] partitionable_card_le_rank_formula partitionable_subset_carrier
  by (force simp: partition_opt_def)

end

end
