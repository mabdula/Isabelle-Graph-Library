theory Matroids_Theory
  imports Main Matroids.Indep_System Matroids.Matroid HOL.Rat
begin


definition Frac :: "int \<Rightarrow> int \<Rightarrow> rat" where
  "Frac a b = (if a = b then 1 else Fract a b)"

lemma Frac_of_int_leq_quotient:
  assumes "n \<le> m" "q = Frac (int n) (int m)"
  shows "rat_of_nat n = q * (rat_of_nat m)"
proof (cases "n = m")
  case True
  have "q = 1" using Frac_def \<open>q = Frac (int n) (int m)\<close> True by simp
  with True show ?thesis by auto
next
  case False
  have q_Fract: "q = Fract (int n) (int m)"
    using Frac_def \<open>q = Frac (int n) (int m)\<close> False by simp

  from \<open>n \<le> m\<close> False have "n < m" by simp
  then have "m > 0" by simp

  from \<open>m > 0\<close> q_Fract
  show ?thesis by (simp add: Fract_of_int_quotient)
qed

section \<open>Formalisation of results from Combinatorial Optimization (Korte, Vygen), 6th ed., Chapter 13\<close>

subsection \<open>Definition 13.2\<close>

subsubsection \<open>Auxiliary lemmas\<close>

context indep_system
begin

(* If a subset of X has strictly greater cardinality than all bases of X, it cannot be independent
in X *)
lemma card_greater_bases:
  assumes "X \<subseteq> carrier" "Y \<subseteq> X" "\<forall>B. basis_in X B \<longrightarrow> card Y > card B"
  shows "\<not> indep_in X Y"
proof-
  have "indep_in X Y \<longrightarrow> \<not>(\<forall>B. basis_in X B \<longrightarrow> card Y > card B)"
  proof
    assume "indep_in X Y"
    from indep_in_iff_subset_basis_in[OF assms(1)] \<open>indep_in X Y\<close>
    have "\<exists>B. basis_in X B \<and> Y \<subseteq> B" by simp
    then have "\<exists>B. basis_in X B \<and> card Y \<le> card B"
      by (meson assms basis_in_finite card_mono)
    then show "\<not>(\<forall>B. basis_in X B \<longrightarrow> card Y > card B)" using linorder_not_le by blast
  qed
  then show ?thesis using assms by blast
qed

subsubsection \<open>Rank definition\<close>

(* Note: We name the function rank instead of rank_of in order to avoid a naming conflict
with the function rank_of, defined in the matroid locale *)
definition rank :: "'a set \<Rightarrow> nat" where
  "rank carrier' = Max {card X | X. indep_in carrier' X}"

(* We show that the definition of the upper rank is equivalent to the definition of the rank *)
lemma upper_rank_equiv_rank:
  assumes "X \<subseteq> carrier"
  shows "upper_rank_of X = rank X"
proof-
  let ?basis_cards = "{card B | B. basis_in X B}"
  from assms(1) basis_in_ex have "?basis_cards \<noteq> {}" by simp
  from assms(1) collect_basis_in_finite finite_imageI have "finite ?basis_cards" by simp

  let ?indep_cards = "{card Y | Y. indep_in X Y}"
  from assms(1) indep_in_ex have "?indep_cards \<noteq> {}" by simp
  from assms(1) carrier_finite finite_Pow_iff finite_imageI have "finite ?indep_cards"
  proof -
    have "\<forall>n \<in> ?indep_cards. n \<le> card carrier"
    proof
      fix n
      assume "n \<in> ?indep_cards"
      then obtain Y where "n = card Y" "indep_in X Y" by blast
      from indep_in_indep[OF `indep_in X Y`] have "indep Y" .
      from indep_subset_carrier[OF this] have "Y \<subseteq> carrier" .
      with carrier_finite have "card Y \<le> card carrier" by (simp add: card_mono)
      with `n = card Y` show "n \<le> card carrier" by simp
    qed
    then show "finite ?indep_cards"
      using finite_nat_set_iff_bounded_le by blast
  qed

  have "\<forall>n. (upper_rank_of X = n) \<longleftrightarrow> (rank X = n)"
  proof
    fix n
    have upper_rank_eq_iff: "(n = upper_rank_of X) \<longleftrightarrow> 
      (\<exists>Y. basis_in X Y \<and> card Y = n \<and> (\<forall>Y'. basis_in X Y' \<longrightarrow> card Y \<ge> card Y'))"
    proof -
      have max_eq: "(Max ?basis_cards = n) \<longleftrightarrow> (n \<in> ?basis_cards \<and> (\<forall>a \<in> ?basis_cards. a \<le> n))"
        using Max_eq_iff[OF `finite ?basis_cards` `?basis_cards \<noteq> {}`] by auto
      show ?thesis
      proof
        assume "n = upper_rank_of X"
        then have "Max ?basis_cards = n" by (simp add: upper_rank_of_def)
        with max_eq have n_mem: "n \<in> ?basis_cards" and n_ub: "\<forall>a \<in> ?basis_cards. a \<le> n" by auto
        from n_mem obtain Y where Y_basis: "basis_in X Y" and Y_card: "card Y = n" by auto
        have Y_max: "\<forall>Y'. basis_in X Y' \<longrightarrow> card Y \<ge> card Y'"
        proof (rule allI, rule impI)
          fix Y'
          assume Y'_basis: "basis_in X Y'"
          then have "card Y' \<in> ?basis_cards" by auto
          with n_ub have "card Y' \<le> n" by auto
          with Y_card show "card Y \<ge> card Y'" by simp
        qed
        from Y_basis Y_card Y_max
        show "\<exists>Y. basis_in X Y \<and> card Y = n \<and> (\<forall>Y'. basis_in X Y' \<longrightarrow> card Y \<ge> card Y')"
          by blast
      next
        assume "\<exists>Y. basis_in X Y \<and> card Y = n \<and> (\<forall>Y'. basis_in X Y' \<longrightarrow> card Y \<ge> card Y')"
        then obtain Y where Y_basis: "basis_in X Y" and Y_card: "card Y = n"
          and Y_max: "\<forall>Y'. basis_in X Y' \<longrightarrow> card Y \<ge> card Y'" by blast
        have n_mem: "n \<in> ?basis_cards" using Y_basis Y_card by auto
        have n_ub: "\<forall>a \<in> ?basis_cards. a \<le> n"
        proof
          fix a
          assume "a \<in> ?basis_cards"
          then obtain Y' where a_eq: "a = card Y'" and Y'_basis: "basis_in X Y'" by auto
          from Y_max Y'_basis have "card Y' \<le> card Y" by auto
          with a_eq Y_card show "a \<le> n" by simp
        qed
        from n_mem n_ub max_eq have "Max ?basis_cards = n" by auto
        then show "n = upper_rank_of X" by (simp add: upper_rank_of_def)
      qed
    qed

    have rank_eq_iff: "(n = rank X) \<longleftrightarrow> 
      (\<exists>Y. indep_in X Y \<and> card Y = n \<and> (\<forall>Y'. indep_in X Y' \<longrightarrow> card Y \<ge> card Y'))"
      unfolding rank_def using Max_eq_iff[OF `finite ?indep_cards` `?indep_cards \<noteq> {}`]
      by force

    have "(\<exists>Y. basis_in X Y \<and> card Y = n \<and> (\<forall>Y'. basis_in X Y' \<longrightarrow> card Y \<ge> card Y')) \<longleftrightarrow>
      (\<exists>Y. indep_in X Y \<and> card Y = n \<and> (\<forall>Y'. indep_in X Y' \<longrightarrow> card Y \<ge> card Y'))"
    proof
      assume "(\<exists>Y. basis_in X Y \<and> card Y = n \<and> (\<forall>Y'. basis_in X Y' \<longrightarrow> card Y \<ge> card Y'))"
      then obtain Y where "basis_in X Y" "card Y = n" "(\<forall>Y'. basis_in X Y' \<longrightarrow> card Y \<ge> card Y')" by blast

      have "indep_in X Y" using basis_in_indep_in[OF assms `basis_in X Y`] .

      have "(\<forall>Y'. indep_in X Y' \<longrightarrow> card Y \<ge> card Y')"
      proof (rule ccontr, goal_cases False)
        case False
        then have "\<exists>Y'. indep_in X Y' \<and> \<not>card Y \<ge> card Y'" by blast
        then obtain Y' where "indep_in X Y'" "\<not>card Y \<ge> card Y'" by blast

        from indep_in_subset_carrier[OF `indep_in X Y'`] have "Y' \<subseteq> X" by blast
        from `\<not>card Y \<ge> card Y'` have "card Y' > card Y" using linorder_not_le by blast
        with `(\<forall>Y'. basis_in X Y' \<longrightarrow> card Y \<ge> card Y')` have
          "(\<forall>B. basis_in X B \<longrightarrow> card Y' > card B)" by auto

        from card_greater_bases[OF assms `Y' \<subseteq> X` `(\<forall>B. basis_in X B \<longrightarrow> card Y' > card B)`]
        have "\<not> indep_in X Y'" .

        with `indep_in X Y'` show ?case by blast
      qed

      with `indep_in X Y` `card Y = n`
      show "(\<exists>Y. indep_in X Y \<and> card Y = n \<and> (\<forall>Y'. indep_in X Y' \<longrightarrow> card Y \<ge> card Y'))" by blast
    next
      assume "(\<exists>Y. indep_in X Y \<and> card Y = n \<and> (\<forall>Y'. indep_in X Y' \<longrightarrow> card Y \<ge> card Y'))"
      then obtain Y where "indep_in X Y" "card Y = n" "(\<forall>Y'. indep_in X Y' \<longrightarrow> card Y \<ge> card Y')" by blast

      have "basis_in X Y"
      proof (rule ccontr, goal_cases False)
        case False
        with `indep_in X Y` have "\<exists>x \<in> (X - Y). indep_in X (insert x Y)"
          using assms basis_inI by blast
        then obtain x where "x \<in> (X - Y)" "indep_in X (insert x Y)" by blast
        then have "card (insert x Y) > card Y"
        proof -
          from \<open>x \<in> (X - Y)\<close> have "x \<notin> Y" by blast
          from indep_in_subset_carrier[OF \<open>indep_in X Y\<close>] have "Y \<subseteq> X" .
          with assms have "Y \<subseteq> carrier" by blast
          with carrier_finite have "finite Y" using finite_subset by blast
          with \<open>x \<notin> Y\<close> have "card (insert x Y) = Suc (card Y)"
            by (simp add: card_insert_disjoint)
          then show "card (insert x Y) > card Y" by simp
        qed

        with `indep_in X (insert x Y)` `(\<forall>Y'. indep_in X Y' \<longrightarrow> card Y \<ge> card Y')`
        show ?case by fastforce
      qed

      have "(\<forall>Y'. basis_in X Y' \<longrightarrow> card Y \<ge> card Y')"
        using `(\<forall>Y'. indep_in X Y' \<longrightarrow> card Y \<ge> card Y')` basis_in_indep_in[OF assms] by blast

      with `basis_in X Y` `card Y = n`
      show "(\<exists>Y. basis_in X Y \<and> card Y = n \<and> (\<forall>Y'. basis_in X Y' \<longrightarrow> card Y \<ge> card Y'))" by blast
    qed

    with upper_rank_eq_iff rank_eq_iff show "(upper_rank_of X = n) \<longleftrightarrow> (rank X = n)" by auto
  qed

  then show "upper_rank_of X = rank X" by blast
qed

subsection \<open>Theorem 13.5\<close>

subsubsection \<open>Theorem statement\<close>

lemma M3_equiv_M3':
  "(\<forall>X Y. indep X \<longrightarrow> indep Y \<longrightarrow> card X > card Y \<longrightarrow> (\<exists>x \<in> X - Y. indep (insert x Y))) \<longleftrightarrow>
  (\<forall>X Y. indep X \<longrightarrow> indep Y \<longrightarrow> card X = card Y + 1 \<longrightarrow> (\<exists>x \<in> X - Y. indep (insert x Y)))"
proof (standard, goal_cases LTR RTL)
  case LTR
  show ?case
  proof ((rule allI)+, (rule impI)+)
    fix X Y
    assume "indep X"
    assume "indep Y"
    assume "card X = card Y + 1"
    then have "card X > card Y" by simp
    from LTR `indep X` `indep Y` `card X > card Y`
    show "(\<exists>x \<in> X - Y. indep (insert x Y))" by blast
  qed
next
  case RTL
  show ?case
  proof ((rule allI)+, (rule impI)+)
    fix X Y
    assume "indep X"
    assume "indep Y"
    assume "card X > card Y"
    from indep_subset_carrier[OF `indep X`] carrier_finite finite_subset have "finite X" by blast
    with `card X > card Y` have "\<exists>X'. X' \<subseteq> X \<and> card X' = card Y + 1"
      by (simp add: card_subset_ex)
    then obtain X' where "X' \<subseteq> X" "card X' = card Y + 1" by blast

    from RTL indep_subset[OF `indep X` `X' \<subseteq> X`] `indep Y` `card X' = card Y + 1`
    have "(\<exists>x \<in> X' - Y. indep (insert x Y))" by blast

    with `X' \<subseteq> X` show "(\<exists>x \<in> X - Y. indep (insert x Y))" by blast
  qed
qed


lemma M3_equiv_M3'': 
  "(\<forall>X Y. indep X \<longrightarrow> indep Y \<longrightarrow> card X > card Y \<longrightarrow> (\<exists>x \<in> X - Y. indep (insert x Y))) \<longleftrightarrow>
  (\<forall>X \<subseteq> carrier. \<forall>B1 B2. basis_in X B1 \<longrightarrow> basis_in X B2 \<longrightarrow> card B1 = card B2)"
proof (standard, goal_cases LTR RTL)
  case LTR
  show ?case
  proof(rule ccontr, goal_cases False)
    case False
    then have "\<exists>X \<subseteq> carrier. \<exists>B1 B2. basis_in X B1 \<and> basis_in X B2 \<and> card B1 \<noteq> card B2" by blast
    then obtain X where ex_X: "X \<subseteq> carrier \<and> (\<exists>B1 B2. basis_in X B1 \<and> basis_in X B2 \<and> card B1 \<noteq> card B2)" by blast
    then obtain B1 B2 where ex_B1_B2: "basis_in X B1 \<and> basis_in X B2 \<and> card B1 \<noteq> card B2" by blast
    from ex_B1_B2 ex_X basis_in_subset_carrier have "B1 \<subseteq> X" by meson
    from ex_B1_B2 ex_X basis_in_subset_carrier have "B2 \<subseteq> X" by meson
    from ex_B1_B2 have "indep B1"
      using basis_in_indep_in ex_X indep_in_indep by blast    
    from ex_B1_B2 have "indep B2"
      using basis_in_indep_in ex_X indep_in_indep by blast

    from ex_B1_B2 consider (1) "card B1 < card B2" | (2) "card B1 > card B2" by linarith
    then show ?case
    proof cases
      case 1
      from LTR `indep B1` `indep B2` 1 have "\<exists>x \<in> B2 - B1. indep (insert x B1)" by blast
      with `B1 \<subseteq> X` `B2 \<subseteq> X` have "\<exists>x \<in> B2 - B1. indep_in X (insert x B1)"
        by (simp add: in_mono indep_in_def)
      with ex_B1_B2 show ?thesis 
      proof -
        from ex_B1_B2 have basis_B1: "basis_in X B1" by blast
        from ex_X have "X \<subseteq> carrier" by blast
        from \<open>\<exists>x \<in> B2 - B1. indep_in X (insert x B1)\<close>
        obtain x where x_mem: "x \<in> B2 - B1" and x_indep: "indep_in X (insert x B1)" by blast
        from x_mem have "x \<in> B2" and "x \<notin> B1" by simp_all
        from \<open>B2 \<subseteq> X\<close> \<open>x \<in> B2\<close> have "x \<in> X" by blast
        with \<open>x \<notin> B1\<close> have "x \<in> X - B1" by blast
        from basis_in_max_indep_in[OF \<open>X \<subseteq> carrier\<close> basis_B1 this]
        have "\<not> indep_in X (insert x B1)" .
        with x_indep show False by blast
      qed
    next
      case 2
      from LTR `indep B1` `indep B2` 2 have "\<exists>x \<in> B1 - B2. indep (insert x B2)" by blast
      with `B1 \<subseteq> X` `B2 \<subseteq> X` have "\<exists>x \<in> B1 - B2. indep_in X (insert x B2)"
        by (simp add: in_mono indep_in_def)
      with ex_B1_B2 show ?thesis
      proof -
        from ex_B1_B2 have basis_B2: "basis_in X B2" by blast
        from ex_X have "X \<subseteq> carrier" by blast
        from \<open>\<exists>x \<in> B1 - B2. indep_in X (insert x B2)\<close>
        obtain x where x_mem: "x \<in> B1 - B2" and x_indep: "indep_in X (insert x B2)" by blast
        from x_mem \<open>B1 \<subseteq> X\<close> have "x \<in> X - B2" by blast
        from basis_in_max_indep_in[OF \<open>X \<subseteq> carrier\<close> basis_B2 this]
        have "\<not> indep_in X (insert x B2)" .
        with x_indep show ?thesis by blast
      qed
    qed
  qed
next
  case RTL
  show ?case
  proof ((rule allI)+, (rule impI)+)
    fix X Y
    assume "indep X"
    assume "indep Y"
    assume "card X > card Y"
    from `indep X` `indep Y` indep_subset_carrier 
    have "X \<union> Y \<subseteq> carrier" by auto    

    from `indep Y` have "indep_in (X \<union> Y) Y" unfolding indep_in_def by blast
    from `indep X` have "indep_in (X \<union> Y) X" unfolding indep_in_def by blast

    from RTL have
      1: "\<forall>X \<subseteq> carrier. \<forall> B1 B2. (card B1 \<noteq> card B2 \<longrightarrow> \<not> basis_in X B1 \<or> \<not> basis_in X B2)"
      by blast
    with `X \<union> Y \<subseteq> carrier` `card X > card Y` have
      "\<not> basis_in (X \<union> Y) X \<or> \<not> basis_in (X \<union> Y) Y"
    proof -
      have "card X \<noteq> card Y" using `card X > card Y` by simp
      with `X \<union> Y \<subseteq> carrier` 1 show ?thesis by blast
    qed

    have "\<not> basis_in (X \<union> Y) Y"
    proof (rule ccontr, goal_cases False)
      case False
      then have "basis_in (X \<union> Y) Y" by blast

      from indep_in_imp_subset_basis_in[OF `X \<union> Y \<subseteq> carrier` `indep_in (X \<union> Y) X`] have 
        "\<exists>B. basis_in (X \<union> Y) B \<and> X \<subseteq> B" by blast
      then obtain B where "basis_in (X \<union> Y) B" "X \<subseteq> B" by blast
      then have "card X \<le> card B"
        using `X \<union> Y \<subseteq> carrier` basis_in_finite card_mono by blast
      with `card X > card Y`
      have "card Y < card B" by auto

      from `X \<union> Y \<subseteq> carrier` `basis_in (X \<union> Y) B` `basis_in (X \<union> Y) Y` `card Y < card B` RTL        
      show ?case
      proof -
        from RTL `X \<union> Y \<subseteq> carrier` `basis_in (X \<union> Y) B` `basis_in (X \<union> Y) Y`
        have "card B = card Y" by blast
        with `card Y < card B` show False by simp
      qed
    qed


    from indep_in_not_basis_in[OF `X \<union> Y \<subseteq> carrier` `indep_in (X \<union> Y) Y` `\<not> basis_in (X \<union> Y) Y`]
    have "\<exists>x \<in> X \<union> Y - Y. indep_in (X \<union> Y) (insert x Y)" by blast
    then have "\<exists>x \<in> X - Y. indep_in (X \<union> Y) (insert x Y)" by blast
    then show "\<exists>x \<in> X - Y. indep (insert x Y)" using indep_in_def by blast
  qed
qed

subsection \<open>Definition 13.6\<close>

subsubsection \<open>Rank quotient definition\<close>

(* Note: We cannot use Fract since Fract 0 0 evaluates to 0, when it should evaluate to 1, since
an equal numerator and denominator in the rank quotient expression should yield a value of 1 *)
definition rank_quotient :: "rat" where
  "rank_quotient = Min {Frac (int (lower_rank_of X)) (int (rank X)) | X. X \<subseteq> carrier}"


subsection \<open>Proposition 13.7\<close>

subsubsection \<open>Auxiliary lemmas\<close>

lemma lower_rank_le_upper_rank:
  assumes "X \<subseteq> carrier"
  shows "lower_rank_of X \<le> upper_rank_of X"
proof-
  let ?basis_cards = "{card B | B. basis_in X B}"
  from assms(1) basis_in_ex have "?basis_cards \<noteq> {}" by simp
  from assms(1) collect_basis_in_finite finite_imageI have "finite ?basis_cards" by simp
  from `finite ?basis_cards` `?basis_cards \<noteq> {}` show ?thesis 
    unfolding lower_rank_of_def upper_rank_of_def by (meson Max_in Min_le)
qed

lemma rq_fracs_leq_1:
  assumes "X \<subseteq> carrier"
  shows "Frac (int (lower_rank_of X)) (int (upper_rank_of X)) \<le> 1"
proof-
  have "lower_rank_of X \<le> upper_rank_of X"
    using assms lower_rank_le_upper_rank by blast
  then have 2: "int (lower_rank_of X) \<le> int (upper_rank_of X)"
    by simp

  have 3: "int (lower_rank_of X) \<ge> 0"
    by simp

  have 4: "int (upper_rank_of X) \<ge> 0"
    by simp

  from 2 3 4 show "Frac (int (lower_rank_of X)) (int (upper_rank_of X)) \<le> 1"
    using Fract_le_one_iff unfolding Frac_def by auto
qed


subsubsection \<open>Theorem statement\<close>

lemma rank_quotient_leq_1:
  "rank_quotient \<le> 1"
proof-
  have "finite carrier" using local.indep_system_axioms unfolding indep_system_def by blast

  let ?fracs = "{Frac (int (lower_rank_of X)) (int (upper_rank_of X)) | X. X \<subseteq> carrier}"
  have "?fracs \<noteq> {}" by blast
  have "finite ?fracs" using `finite carrier` by auto

  have 1: "rank_quotient = Min {Frac (int (lower_rank_of X)) (int (upper_rank_of X)) | X. X \<subseteq> carrier}"
    unfolding rank_quotient_def
  proof -
    have set_eq: "{Frac (int (lower_rank_of X)) (int (rank X)) | X. X \<subseteq> carrier} =
      {Frac (int (lower_rank_of X)) (int (upper_rank_of X)) | X. X \<subseteq> carrier}"
    proof (rule set_eqI)
      fix y
      show "y \<in> {Frac (int (lower_rank_of X)) (int (rank X)) | X. X \<subseteq> carrier} \<longleftrightarrow>
            y \<in> {Frac (int (lower_rank_of X)) (int (upper_rank_of X)) | X. X \<subseteq> carrier}"
      proof
        assume "y \<in> {Frac (int (lower_rank_of X)) (int (rank X)) | X. X \<subseteq> carrier}"
        then obtain X where X_carrier: "X \<subseteq> carrier"
          and y_eq: "y = Frac (int (lower_rank_of X)) (int (rank X))" by blast
        have "int (upper_rank_of X) = int (rank X)"
          using upper_rank_equiv_rank[OF X_carrier] by simp
        with y_eq have "y = Frac (int (lower_rank_of X)) (int (upper_rank_of X))" by simp
        with X_carrier
        show "y \<in> {Frac (int (lower_rank_of X)) (int (upper_rank_of X)) | X. X \<subseteq> carrier}" by auto
      next
        assume "y \<in> {Frac (int (lower_rank_of X)) (int (upper_rank_of X)) | X. X \<subseteq> carrier}"
        then obtain X where X_carrier: "X \<subseteq> carrier"
          and y_eq: "y = Frac (int (lower_rank_of X)) (int (upper_rank_of X))" by blast
        from upper_rank_equiv_rank[OF X_carrier] y_eq X_carrier
        show "y \<in> {Frac (int (lower_rank_of X)) (int (rank X)) | X. X \<subseteq> carrier}" by auto
      qed
    qed
    show "Min {Frac (int (lower_rank_of X)) (int (rank X)) | X. X \<subseteq> carrier} =
          Min {Frac (int (lower_rank_of X)) (int (upper_rank_of X)) | X. X \<subseteq> carrier}"
      using set_eq by simp
  qed

  have 2: "\<forall>X \<subseteq> carrier. Frac (int (lower_rank_of X)) (int (upper_rank_of X)) \<le> 1"
    using rq_fracs_leq_1 by auto

  from 1 2 Min_le_iff[OF `finite ?fracs` `?fracs \<noteq> {}`] show ?thesis by auto
qed

lemma matroid_iff_rq_eq_1:
  "matroid carrier indep \<longleftrightarrow> (rank_quotient = 1)"
proof-
  have bases_X_finite: "(\<forall>X \<subseteq> carrier. finite {card B | B. basis_in X B})"
    by (simp add: collect_basis_in_finite) 
  have bases_X_nonempty: "(\<forall>X \<subseteq> carrier. {card B | B. basis_in X B} \<noteq> {})"
    using indep_in_empty indep_in_iff_subset_basis_in by simp

  have rq_fracs_finite: 
    "finite {Frac (int (Min {card B | B. basis_in X B})) (int (Max {card B | B. basis_in X B})) | 
    X. X \<subseteq> carrier}"
    using carrier_finite by simp
  have rq_fracs_nonempty: 
    "{Frac (int (Min {card B | B. basis_in X B})) (int (Max {card B | B. basis_in X B})) | 
    X. X \<subseteq> carrier} \<noteq> {}"
    using carrier_finite by auto

  have rq_fracs_leq_1: 
    "\<forall>X \<subseteq> carrier. Frac (int (Min {card B | B. basis_in X B})) (int (Max {card B | B. basis_in X B})) \<le> 1"
    using rq_fracs_leq_1 lower_rank_of_def upper_rank_of_def by simp

  have "(\<forall>X Y. indep X \<longrightarrow> indep Y \<longrightarrow> card X = Suc (card Y) \<longrightarrow> (\<exists>x \<in> X - Y. indep (insert x Y)))
    \<longleftrightarrow> (\<forall>X Y. indep X \<longrightarrow> indep Y \<longrightarrow> card X > card Y \<longrightarrow> (\<exists>x \<in> X - Y. indep (insert x Y)))"
    using M3_equiv_M3' by auto
  also have "... 
    \<longleftrightarrow> (\<forall>X \<subseteq> carrier. \<forall>B1 B2. basis_in X B1 \<longrightarrow> basis_in X B2 \<longrightarrow> card B1 = card B2)"
    using M3_equiv_M3'' by auto
  also have "...
    \<longleftrightarrow> (\<forall>X \<subseteq> carrier. (\<exists>n. \<forall>n'. n' \<in> {card B | B. basis_in X B} \<longrightarrow> n' = n))"
    proof (rule iffI)
      assume LHS: "\<forall>X \<subseteq> carrier. \<forall>B1 B2. basis_in X B1 \<longrightarrow> basis_in X B2 \<longrightarrow> card B1 = card B2"
      show "\<forall>X \<subseteq> carrier. (\<exists>n. \<forall>n'. n' \<in> {card B | B. basis_in X B} \<longrightarrow> n' = n)"
      proof (intro allI impI)
        fix X
        assume "X \<subseteq> carrier"
        show "\<exists>n. \<forall>n'. n' \<in> {card B | B. basis_in X B} \<longrightarrow> n' = n"
        proof (cases "\<exists>B. basis_in X B")
          case True
          then obtain B0 where B0_basis: "basis_in X B0" by blast
          have n_eq: "\<forall>n'. n' \<in> {card B | B. basis_in X B} \<longrightarrow> n' = card B0"
          proof (intro allI impI)
            fix n'
            assume "n' \<in> {card B | B. basis_in X B}"
            then obtain B' where "n' = card B'" "basis_in X B'" by blast
            with LHS \<open>X \<subseteq> carrier\<close> B0_basis have "card B' = card B0" by blast
            with \<open>n' = card B'\<close> show "n' = card B0" by simp
          qed
          then show ?thesis by blast
        next
          case False
          then have "{card B | B. basis_in X B} = {}" by blast
          then show ?thesis by blast
        qed
      qed
    next
      assume RHS: "\<forall>X \<subseteq> carrier. (\<exists>n. \<forall>n'. n' \<in> {card B | B. basis_in X B} \<longrightarrow> n' = n)"
      show "\<forall>X \<subseteq> carrier. \<forall>B1 B2. basis_in X B1 \<longrightarrow> basis_in X B2 \<longrightarrow> card B1 = card B2"
      proof (intro allI impI)
        fix X B1 B2
        assume "X \<subseteq> carrier" "basis_in X B1" "basis_in X B2"
        from RHS \<open>X \<subseteq> carrier\<close> obtain n where n_prop: "\<forall>n'. n' \<in> {card B | B. basis_in X B} \<longrightarrow> n' = n"
          by blast
        from \<open>basis_in X B1\<close> have "card B1 \<in> {card B | B. basis_in X B}" by blast
        with n_prop have card_B1_eq: "card B1 = n" by blast
        from \<open>basis_in X B2\<close> have "card B2 \<in> {card B | B. basis_in X B}" by blast
        with n_prop have "card B2 = n" by blast
        then show "card B1 = card B2" using card_B1_eq by simp
      qed
    qed
  also have "...
    \<longleftrightarrow> (\<forall>X \<subseteq> carrier. Min {card B | B. basis_in X B} = Max {card B | B. basis_in X B})"
  proof
    assume LTR: "\<forall>X \<subseteq> carrier. (\<exists>n. \<forall>n'. n' \<in> {card B | B. basis_in X B} \<longrightarrow> n' = n)"
    show "\<forall>X \<subseteq> carrier. Min {card B | B. basis_in X B} = Max {card B | B. basis_in X B}"
    proof (rule allI, rule impI)
      fix X
      assume "X \<subseteq> carrier"
      with LTR obtain n where n_eq: "\<forall>n'. n' \<in> {card B | B. basis_in X B} \<longrightarrow> n' = n" by blast
      from `X \<subseteq> carrier` bases_X_nonempty have nonempty: "{card B | B. basis_in X B} \<noteq> {}" by blast
      then obtain s where s_in: "s \<in> {card B | B. basis_in X B}" by blast
      with n_eq have "s = n" by blast
      with n_eq s_in have "{card B | B. basis_in X B} = {n}" by blast
      then show "Min {card B | B. basis_in X B} = Max {card B | B. basis_in X B}" by simp
    qed
  next
    assume RTL: "\<forall>X \<subseteq> carrier. Min {card B | B. basis_in X B} = Max {card B | B. basis_in X B}"
    show "\<forall>X \<subseteq> carrier. (\<exists>n. \<forall>n'. n' \<in> {card B | B. basis_in X B} \<longrightarrow> n' = n)"
    proof (rule allI, rule impI)
      fix X
      assume "X \<subseteq> carrier"
      with RTL have min_eq_max: "Min {card B | B. basis_in X B} = Max {card B | B. basis_in X B}"
        by blast
      from `X \<subseteq> carrier` bases_X_finite have fin: "finite {card B | B. basis_in X B}" by blast
      have "\<forall>n'. n' \<in> {card B | B. basis_in X B} \<longrightarrow> n' = Min {card B | B. basis_in X B}"
      proof (rule allI, rule impI)
        fix n'
        assume n'_in: "n' \<in> {card B | B. basis_in X B}"
        from Min_le[OF fin n'_in] have le1: "Min {card B | B. basis_in X B} \<le> n'" .
        from Max_ge[OF fin n'_in] have "n' \<le> Max {card B | B. basis_in X B}" .
        with min_eq_max have le2: "n' \<le> Min {card B | B. basis_in X B}" by simp
        from le1 le2 show "n' = Min {card B | B. basis_in X B}" by simp
      qed
      then show "\<exists>n. \<forall>n'. n' \<in> {card B | B. basis_in X B} \<longrightarrow> n' = n" by blast
    qed
  qed
  also have "...
    \<longleftrightarrow> (\<forall>X \<subseteq> carrier. int (Min {card B | B. basis_in X B}) = int (Max {card B | B. basis_in X B}))"
    by simp
  also have "...
    \<longleftrightarrow> (\<forall>X \<subseteq> carrier. 
    Frac (int (Min {card B | B. basis_in X B})) (int (Max {card B | B. basis_in X B})) = 1)"
  proof (rule iffI)
    assume eq_assm: "\<forall>X \<subseteq> carrier. int (Min {card B | B. basis_in X B}) = int (Max {card B | B. basis_in X B})"
    show "\<forall>X \<subseteq> carrier. Frac (int (Min {card B | B. basis_in X B})) (int (Max {card B | B. basis_in X B})) = 1"
    proof (rule allI, rule impI)
      fix X
      assume "X \<subseteq> carrier"
      with eq_assm have eq: "Min {card B | B. basis_in X B} = Max {card B | B. basis_in X B}"
        by simp
      then show "Frac (int (Min {card B | B. basis_in X B})) (int (Max {card B | B. basis_in X B})) = 1"
        unfolding Frac_def by simp
    qed
  next
    assume frac_assm: "\<forall>X \<subseteq> carrier. Frac (int (Min {card B | B. basis_in X B})) (int (Max {card B | B. basis_in X B})) = 1"
    show "\<forall>X \<subseteq> carrier. int (Min {card B | B. basis_in X B}) = int (Max {card B | B. basis_in X B})"
    proof (rule allI, rule impI)
      fix X
      assume "X \<subseteq> carrier"
      let ?m = "Min {card B | B. basis_in X B}"
      let ?M = "Max {card B | B. basis_in X B}"

      from bases_X_finite \<open>X \<subseteq> carrier\<close> have fin: "finite {card B | B. basis_in X B}" by blast
      from bases_X_nonempty \<open>X \<subseteq> carrier\<close> have nonempty: "{card B | B. basis_in X B} \<noteq> {}" by blast

      from Min_in[OF fin nonempty] have m_in: "?m \<in> {card B | B. basis_in X B}" .
      from Max_ge[OF fin m_in] have m_le_M: "?m \<le> ?M" .

      from frac_assm \<open>X \<subseteq> carrier\<close>
      have frac_eq: "Frac (int ?m) (int ?M) = 1" by blast

      from Frac_of_int_leq_quotient[OF m_le_M refl]
      have "rat_of_nat ?m = Frac (int ?m) (int ?M) * rat_of_nat ?M" .
      also have "... = rat_of_nat ?M" using frac_eq by simp
      finally have "rat_of_nat ?m = rat_of_nat ?M" .
      then have "?m = ?M" by simp
      then show "int ?m = int ?M" by simp
    qed
  qed
  also have "...
    \<longleftrightarrow> (Min {Frac (int (Min {card B | B. basis_in X B})) (int (Max {card B | B. basis_in X B})) | 
    X. X \<subseteq> carrier} = 1)"
    using rq_fracs_finite rq_fracs_nonempty rq_fracs_leq_1
    by (smt (verit, best) Min.boundedE Min_in mem_Collect_eq verit_la_disequality)
  also have "...
    \<longleftrightarrow> (Min {Frac (int (lower_rank_of X)) (int (upper_rank_of X)) | X. X \<subseteq> carrier} = 1)"
    using lower_rank_of_def upper_rank_of_def by auto
  also have "...
    \<longleftrightarrow> (Min {Frac (int (lower_rank_of X)) (int (rank X)) | X. X \<subseteq> carrier} = 1)"
  proof -
  have set_eq: "{Frac (int (lower_rank_of X)) (int (upper_rank_of X)) | X. X \<subseteq> carrier} =
                {Frac (int (lower_rank_of X)) (int (rank X)) | X. X \<subseteq> carrier}"
  proof (rule subset_antisym)
    show "{Frac (int (lower_rank_of X)) (int (upper_rank_of X)) | X. X \<subseteq> carrier} \<subseteq>
          {Frac (int (lower_rank_of X)) (int (rank X)) | X. X \<subseteq> carrier}"
    proof (rule subsetI)
      fix q
      assume "q \<in> {Frac (int (lower_rank_of X)) (int (upper_rank_of X)) | X. X \<subseteq> carrier}"
      then obtain X where X_sub: "X \<subseteq> carrier"
        and q_eq: "q = Frac (int (lower_rank_of X)) (int (upper_rank_of X))"
        by blast
      from upper_rank_equiv_rank[OF X_sub] q_eq
      have "q = Frac (int (lower_rank_of X)) (int (rank X))" by simp
      with X_sub show "q \<in> {Frac (int (lower_rank_of X)) (int (rank X)) | X. X \<subseteq> carrier}"
        by blast
    qed
  next
    show "{Frac (int (lower_rank_of X)) (int (rank X)) | X. X \<subseteq> carrier} \<subseteq>
          {Frac (int (lower_rank_of X)) (int (upper_rank_of X)) | X. X \<subseteq> carrier}"
    proof (rule subsetI)
      fix q
      assume "q \<in> {Frac (int (lower_rank_of X)) (int (rank X)) | X. X \<subseteq> carrier}"
      then obtain X where X_sub: "X \<subseteq> carrier"
        and q_eq: "q = Frac (int (lower_rank_of X)) (int (rank X))"
        by blast
      from upper_rank_equiv_rank[OF X_sub] q_eq
      have "q = Frac (int (lower_rank_of X)) (int (upper_rank_of X))" by simp
      with X_sub show "q \<in> {Frac (int (lower_rank_of X)) (int (upper_rank_of X)) | X. X \<subseteq> carrier}"
        by blast
    qed
  qed
  show ?thesis by (simp add: set_eq)
  qed
  also have "... \<longleftrightarrow> (rank_quotient = 1)"
    unfolding rank_quotient_def by simp
  finally have augment_iff_rq_eq_1:
    "(\<forall>X Y. indep X \<longrightarrow> indep Y \<longrightarrow> card X = Suc (card Y) \<longrightarrow> (\<exists>x \<in> X - Y. indep (insert x Y)))
    \<longleftrightarrow> (rank_quotient = 1)" .

  show "matroid carrier indep \<longleftrightarrow> (rank_quotient = 1)"
  proof (standard, goal_cases LTR RTL)
    case LTR
    then have 
      "\<forall>X Y. indep X \<longrightarrow> indep Y \<longrightarrow> card X = Suc (card Y) \<longrightarrow> (\<exists>x \<in> X - Y. indep (insert x Y))"
      unfolding matroid_def matroid_axioms_def by blast
    with augment_iff_rq_eq_1 show ?case by simp
  next
    case RTL
    show ?case
      apply(unfold_locales)
      using RTL augment_iff_rq_eq_1 by blast
  qed
qed


subsection \<open>Theorem 13.8\<close>

subsubsection \<open>Abbreviations\<close>

abbreviation circuits_in where
  "circuits_in X \<equiv> {C | C. C \<subseteq> X \<and> circuit C}"

subsubsection \<open>Auxiliary lemmas\<close>

abbreviation X_prop where "X_prop K J l K_i i X \<equiv> 
  X \<subseteq> K_i - J \<and> (\<forall>C \<in> (Set.image ((\<inter>) (K_i - J)) (circuits_in (K_i \<union> {l ! i}))). \<exists>x \<in> X. x \<in> C) \<and>
  card X \<le> card (circuits_in (K_i \<union> {l ! i}))"

lemma ex_X: 
  assumes "F \<subseteq> carrier" "basis_in F J" "basis_in F K" "t = card (J - K)" "set l = (J - K)"
    "length l = t" "indep K_i" "i < card (J - K)"
  shows "\<exists>X. (X_prop K J l K_i i) X"
proof-
  from indep_in_indep[OF basis_in_indep_in[OF assms(1) assms(2)]]
  have "indep J" .  
  from basis_in_subset_carrier[OF assms(1) assms(2)] subset_trans \<open>F \<subseteq> carrier\<close>
  have "J \<subseteq> carrier" by simp

  let ?circuits_int = "(Set.image ((\<inter>) (K_i - J)) (circuits_in (K_i \<union> {l ! i})))"

  have circuits_int_nonempty: "\<forall>C. C \<in> ?circuits_int \<longrightarrow> (\<exists>x. x \<in> C)"
  proof (rule allI, rule impI)
    fix C
    assume "C \<in> ?circuits_int"
    then have "\<exists>C'. C = (K_i - J) \<inter> C' \<and> C' \<subseteq> K_i \<union> {l ! i} \<and> circuit C'" by auto
    then obtain C' where "C = (K_i - J) \<inter> C'" "C' \<subseteq> K_i \<union> {l ! i}" "circuit C'" by blast

    from circuit_nonempty[OF \<open>circuit C'\<close>] have "C' \<noteq> {}" by blast
    moreover have "\<not> C' \<subseteq> J"
      using \<open>indep J\<close> dep_iff_supset_circuit[OF \<open>J \<subseteq> carrier\<close>] \<open>circuit C'\<close> by blast
    ultimately have "\<exists>x. x \<in> C' \<and> x \<notin> J" by blast
    then obtain x where "x \<in> C'" "x \<notin> J" by blast

    from \<open>set l = (J - K)\<close> assms(8) have "l ! i \<in> J"
    proof -
  from assms(4) assms(8) have "i < t" by simp
  with assms(6) have "i < length l" by simp
  then have "l ! i \<in> set l" by (rule nth_mem)
  then have "l ! i \<in> J - K" using \<open>set l = (J - K)\<close> by simp
  then show "l ! i \<in> J" by (rule DiffD1)
qed
    from \<open>l ! i \<in> J\<close> \<open>x \<notin> J\<close> \<open>x \<in> C'\<close> \<open>C' \<subseteq> K_i \<union> {l ! i}\<close>
    have "x \<in> K_i" by blast

    from \<open>x \<in> C'\<close> \<open>x \<in> K_i\<close> \<open>x \<notin> J\<close> \<open>C = (K_i - J) \<inter> C'\<close>
    show "\<exists>x. x \<in> C" by blast
  qed
  then have circuits_int_nonempty: "\<forall>C. \<exists>x. C \<in> ?circuits_int \<longrightarrow> x \<in> C" by auto

  from indep_finite[OF assms(7)] have "finite (K_i \<union> {l ! i})" by blast
  then have "finite (circuits_in (K_i \<union> {l ! i}))" by simp
  then have card_circuits_int_leq: "card ?circuits_int \<le> card (circuits_in (K_i \<union> {l ! i}))"
    using card_image_le by blast

  from choice[OF circuits_int_nonempty]
  have "\<exists>f. \<forall>C \<in> ?circuits_int. f C \<in> C" by auto
  then obtain f where "\<forall>C \<in> ?circuits_int. f C \<in> C" by blast

  let ?X = "Set.image f ?circuits_int"

  have 1: "?X \<subseteq> K_i - J"
    using \<open>\<forall>C \<in> ?circuits_int. f C \<in> C\<close> by force

  from \<open>\<forall>C \<in> ?circuits_int. f C \<in> C\<close>
  have 2: "(\<forall>C \<in> ?circuits_int. \<exists>x \<in> ?X. x \<in> C)" by auto

  have 3: "card ?X \<le> card (circuits_in (K_i \<union> {l ! i}))"
    using card_circuits_int_leq \<open>finite (circuits_in (K_i \<union> {l ! i}))\<close>
      card_image_le dual_order.trans by blast
  from 1 2 3 show "\<exists>X. (X_prop K J l K_i i) X" by blast
qed

(* We use this function to define the sequence of sets needed for the proof of 13.8 *)
fun K_seq :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a set" where
  "K_seq K J l 0 = K" |
  "K_seq K J l (Suc i) = (K_seq K J l i - (Eps (X_prop K J l (K_seq K J l i) i))) \<union> {l ! i}"

lemma K_seq_props:
  assumes "F \<subseteq> carrier" "basis_in F J" "basis_in F K" "t = card (J - K)" "set l = (J - K)"
    "length l = t"
  shows "i \<le> t \<longrightarrow> (K_seq K J l i) \<subseteq> J \<union> K \<and> indep (K_seq K J l i) \<and> J \<inter> K \<subseteq> (K_seq K J l i) \<and>
    (K_seq K J l i) \<inter> (J - K) = set (take i l) \<and> K - (K_seq K J l i) = (\<Union>j \<in> {0..<i}.
    (Eps (X_prop K J l (K_seq K J l j) j)))"
proof (induction i)
  case 0
  from indep_in_indep[OF basis_in_indep_in[OF assms(1) assms(3)]]
  have "indep K" .

  from \<open>indep K\<close> have 1: "(K_seq K J l 0) \<subseteq> J \<union> K \<and> indep (K_seq K J l 0) \<and> J \<inter> K \<subseteq> (K_seq K J l 0)" by simp
  have 2: "(K_seq K J l 0) \<inter> (J - K) = set (take 0 l) \<and> 
    K - (K_seq K J l 0) = (\<Union>j \<in> {0..<0}. (Eps (X_prop K J l (K_seq K J l j) j)))" by auto

  from 1 2 show ?case by auto
next
  case (Suc i)
  show ?case
  proof (rule impI)
    assume "Suc i \<le> t"
    then have "i \<le> t - 1" by auto
    then have "i \<le> t" by auto

    from basis_in_subset_carrier[OF assms(1) assms(2)] subset_trans \<open>F \<subseteq> carrier\<close>
    have "J \<subseteq> carrier" by simp
    from basis_in_subset_carrier[OF assms(1) assms(3)] subset_trans \<open>F \<subseteq> carrier\<close>
    have "K \<subseteq> carrier" by simp

    from Suc.IH \<open>i \<le> t\<close>
    have K_seq_i: "K_seq K J l i \<subseteq> J \<union> K \<and> indep (K_seq K J l i) \<and> J \<inter> K \<subseteq> K_seq K J l i \<and>
      K_seq K J l i \<inter> (J - K) = set (take i l) \<and> K - (K_seq K J l i) = (\<Union>j \<in> {0..<i}.
      (Eps (X_prop K J l (K_seq K J l j) j)))" by auto

    from \<open>Suc i \<le> t\<close> assms(4) have "i < card (J - K)" by auto
    from assms(4) assms(6) have "length l = card (J - K)" by blast
    from K_seq_i have "indep (K_seq K J l i)" by blast
    from someI_ex[OF ex_X[OF \<open>F \<subseteq> carrier\<close> \<open>basis_in F J\<close> \<open>basis_in F K\<close> refl \<open>set l = (J - K)\<close>
          \<open>length l = card (J - K)\<close> \<open>indep (K_seq K J l i)\<close> \<open>i < card (J - K)\<close>]]
    have X_i: "X_prop K J l (K_seq K J l i) i (Eps (X_prop K J l (K_seq K J l i) i))" by blast


    from assms(5) assms(6) \<open>Suc i \<le> t\<close>
    have "l ! i \<in> J - K" by fastforce
    with K_seq_i
    have 1: "K_seq K J l (Suc i) \<subseteq> J \<union> K" by auto

    from 1 \<open>J \<subseteq> carrier\<close> \<open>K \<subseteq> carrier\<close> have "K_seq K J l (Suc i) \<subseteq> carrier" by blast
    have "\<forall>C. circuit C \<longrightarrow> \<not>C \<subseteq> K_seq K J l (Suc i)" 
    proof (rule allI, rule impI)
      fix C
      assume "circuit C"
      show "\<not> C \<subseteq> K_seq K J l (Suc i)"
      proof (cases "C \<in> (circuits_in ((K_seq K J l i) \<union> {l ! i}))")
        case True
        from X_i True
        have "\<exists>x. x \<in> ((K_seq K J l i) - J) \<inter> C \<and> x \<in> (Eps (X_prop K J l (K_seq K J l i) i))"
          by blast
        then obtain x where "x \<in> ((K_seq K J l i) - J) \<inter> C" "x \<in> (Eps (X_prop K J l (K_seq K J l i) i))"
          by blast
        then have "x \<in> C" by blast

        from K_seq_i have "K_seq K J l i \<inter> (J - K) = set (take i l)" by auto
        moreover have "l ! i \<notin> set (take i l)" using assms(4) assms(5) assms(6)
        proof -
          have length_l: "length l = card (J - K)"
            using assms(4) assms(6) by simp
          have set_l: "set l = J - K"
            using assms(5) by simp
          from length_l set_l have "card (set l) = length l"
            by simp
          then have distinct_l: "distinct l"
            by (rule card_distinct)
          from \<open>i < card (J - K)\<close> length_l have i_lt: "i < length l"
            by simp
          have split: "take i l @ drop i l = l"
            by (rule append_take_drop_id)
          from split distinct_l have distinct_split: "distinct (take i l @ drop i l)"
            by simp
          have disjoint: "set (take i l) \<inter> set (drop i l) = {}"
            using distinct_split by (blast dest: distinct_append[THEN iffD1])
          have drop_nonempty: "drop i l \<noteq> []"
          proof
            assume "drop i l = []"
            then have "length (drop i l) = 0" by simp
            then have "length l - i = 0" by (simp add: length_drop)
            with i_lt show False by simp
          qed
          have hd_eq: "hd (drop i l) = l ! i"
            using i_lt by (rule hd_drop_conv_nth)
          have mem: "l ! i \<in> set (drop i l)"
          proof -
            have "hd (drop i l) \<in> set (drop i l)"
              using drop_nonempty by (rule hd_in_set)
            then show ?thesis using hd_eq by simp
          qed
          show "l ! i \<notin> set (take i l)"
            using disjoint mem by blast
        qed
        ultimately have "l ! i \<notin> K_seq K J l i"
          using \<open>l ! i \<in> J - K\<close> by blast
        from \<open>x \<in> ((K_seq K J l i) - J) \<inter> C\<close> \<open>l ! i \<notin> K_seq K J l i\<close>
        have "x \<noteq> l ! i" by blast
        from \<open>x \<in> (Eps (X_prop K J l (K_seq K J l i) i))\<close> \<open>x \<in> C\<close> \<open>x \<noteq> l ! i\<close>
        show ?thesis by auto
      next
        case False
        with \<open>circuit C\<close> have "\<not>C \<subseteq> (K_seq K J l i) \<union> {l ! i}" by blast
        then show ?thesis by auto
      qed
    qed
    with dep_iff_supset_circuit[OF \<open>K_seq K J l (Suc i) \<subseteq> carrier\<close>]
    have 2: "indep (K_seq K J l (Suc i))" by blast

    from K_seq_i have "J \<inter> K \<subseteq> (K_seq K J l i)" by auto
    moreover have "(Eps (X_prop K J l (K_seq K J l i) i)) \<subseteq> (K_seq K J l i) - J"
      using X_i by auto
    ultimately have 3: "J \<inter> K \<subseteq> K_seq K J l (Suc i)" by auto

    have "i < length l" using \<open>Suc i \<le> t\<close> \<open>length l = t\<close> by auto
    from K_seq_i have "K_seq K J l i \<inter> (J - K) = set (take i l)" by auto
    with \<open>(Eps (X_prop K J l (K_seq K J l i) i)) \<subseteq> (K_seq K J l i) - J\<close>
    have "(K_seq K J l i - (Eps (X_prop K J l (K_seq K J l i) i))) \<inter> (J - K) = set (take i l)"
      by blast
    moreover have "{l ! i} \<inter> (J - K) = {l ! i}"
      using \<open>set l = (J - K)\<close> \<open>i < length l\<close> by fastforce
    ultimately have
      "(K_seq K J l i - (Eps (X_prop K J l (K_seq K J l i) i)) \<union> {l ! i}) \<inter> (J - K) =
      set (take i l) \<union> {l ! i}" by blast
    then have "K_seq K J l (Suc i) \<inter> (J - K) = set (take i l) \<union> {l ! i}" by auto
    then have 4: "K_seq K J l (Suc i) \<inter> (J - K) = set (take (Suc i) l)"
      using take_Suc_conv_app_nth[OF \<open>i < length l\<close>] by simp

    from \<open>l ! i \<in> J - K\<close> have "l ! i \<notin> K" by blast
    from \<open>(Eps (X_prop K J l (K_seq K J l i) i)) \<subseteq> (K_seq K J l i) - J\<close> K_seq_i
    have "(Eps (X_prop K J l (K_seq K J l i) i)) \<subseteq> K" by auto
    have "K - (K_seq K J l (Suc i)) = 
      K - ((K_seq K J l i) - (Eps (X_prop K J l (K_seq K J l i) i)) \<union> {l ! i})"
      by auto
    also have "... =
      K - ((K_seq K J l i) - (Eps (X_prop K J l (K_seq K J l i) i)))"
      using \<open>l ! i \<notin> K\<close> by auto
    also have "... =
      (K - (K_seq K J l i)) \<union> (K \<inter> (Eps (X_prop K J l (K_seq K J l i) i)))"
      by auto
    also have "... = 
      (K - (K_seq K J l i)) \<union> (Eps (X_prop K J l (K_seq K J l i) i))"
      using \<open>(Eps (X_prop K J l (K_seq K J l i) i)) \<subseteq> K\<close> by auto
    also have "... =
      (\<Union>j \<in> {0..<i}. (Eps (X_prop K J l (K_seq K J l j) j))) \<union> (Eps (X_prop K J l (K_seq K J l i) i))"
      using K_seq_i by blast
    also have "... =
      (\<Union>j \<in> {0..<(Suc i)}. (Eps (X_prop K J l (K_seq K J l j) j)))"
      using lessThan_Suc atLeast0LessThan by auto
    finally
    have 5: "K - (K_seq K J l (Suc i)) = (\<Union>j \<in> {0..<Suc i}. (Eps (X_prop K J l (K_seq K J l j) j)))" .

    from 1 2 3 4 5
    show "K_seq K J l (Suc i) \<subseteq> J \<union> K \<and> indep (K_seq K J l (Suc i)) \<and> J \<inter> K \<subseteq> K_seq K J l (Suc i) \<and>
      K_seq K J l (Suc i) \<inter> (J - K) = set (take (Suc i) l) \<and> K - (K_seq K J l (Suc i)) =
      (\<Union>j \<in> {0..<Suc i}. (Eps (X_prop K J l (K_seq K J l j) j)))" by blast
  qed
qed

subsubsection \<open>Theorem statement\<close>

lemma rank_quotient_lower_bound:
  assumes "p \<ge> 1" "\<forall>A. indep A \<longrightarrow> (\<forall>e \<in> carrier. card (circuits_in (A \<union> {e})) \<le> p)"
  shows "rank_quotient \<ge> Fract 1 (int p)"
proof-
  have basis_cards_ineq:
    "\<forall>F \<subseteq> carrier. (\<forall>J. basis_in F J \<longrightarrow> (\<forall>K. basis_in F K \<longrightarrow> card K \<le> p * card J))"
  proof ((rule allI, rule impI)+)
    fix F J K
    assume "F \<subseteq> carrier" "basis_in F J" "basis_in F K"

    from basis_in_subset_carrier[OF \<open>F \<subseteq> carrier\<close> \<open>basis_in F J\<close>]
    have "J \<subseteq> F" by blast
    from basis_in_subset_carrier[OF \<open>F \<subseteq> carrier\<close> \<open>basis_in F K\<close>]
    have "K \<subseteq> F" by blast

    from basis_in_finite \<open>basis_in F K\<close> \<open>F \<subseteq> carrier\<close> have "finite K"
      by blast
    from basis_in_finite \<open>basis_in F J\<close> \<open>F \<subseteq> carrier\<close> have "finite J"
      by blast
    then have "finite (J - K)" by blast
    let ?t = "card (J - K)"

(* We establish an order on the elements by using a list *)
    from `finite (J - K)` 
    have "\<exists>l. set l = (J - K) \<and> length l = ?t"
    proof -
  from finite_distinct_list[OF \<open>finite (J - K)\<close>]
  obtain xs where xs_set: "set xs = J - K" and xs_distinct: "distinct xs" by blast
  from distinct_card[OF xs_distinct] have "card (set xs) = length xs" .
  with xs_set have "length xs = card (J - K)" by simp
  with xs_set show "\<exists>l. set l = (J - K) \<and> length l = ?t" by blast
qed
    then obtain l where "set l = (J - K) \<and> length l = ?t" by blast

    from K_seq_props[OF \<open>F \<subseteq> carrier\<close> \<open>basis_in F J\<close> \<open>basis_in F K\<close> refl] 
      \<open>set l = (J - K) \<and> length l = ?t\<close>
    have K_seq_all: "\<forall>i. i \<le> ?t \<longrightarrow> (K_seq K J l i) \<subseteq> J \<union> K \<and> indep (K_seq K J l i) \<and> J \<inter> K \<subseteq> (K_seq K J l i) \<and>
    (K_seq K J l i) \<inter> (J - K) = set (take i l) \<and> K - (K_seq K J l i) = (\<Union>j \<in> {0..<i}.
    (Eps (X_prop K J l (K_seq K J l j) j)))"
      by presburger

    then have K_seq_t: 
      "(K_seq K J l ?t) \<subseteq> J \<union> K \<and> indep (K_seq K J l ?t) \<and> J \<inter> K \<subseteq> (K_seq K J l ?t) \<and>
      (K_seq K J l ?t) \<inter> (J - K) = set (take ?t l) \<and> K - (K_seq K J l ?t) = (\<Union>j \<in> {0..<?t}.
      (Eps (X_prop K J l (K_seq K J l j) j)))" by blast


    from K_seq_all have
      K_seq_indep: "\<forall>i. i \<le> ?t \<longrightarrow> indep (K_seq K J l i)"
      by blast

    from K_seq_t
    have "K - K_seq K J l ?t = (\<Union>j \<in> {0..<?t}. (Eps (X_prop K J l (K_seq K J l j) j)))" by blast
    then have
      card_leq_sum: "card (K - K_seq K J l ?t) \<le> (\<Sum>j = 0..<?t. card (Eps (X_prop K J l (K_seq K J l j) j)))"
      by (simp add: card_UN_le)

    have "\<forall>j. j < ?t \<longrightarrow> card (Eps (X_prop K J l (K_seq K J l j) j)) \<le> 
      card (circuits_in ((K_seq K J l j) \<union> {l ! j}))"
    proof (rule allI, rule impI)
      fix j
      assume "j < ?t"
      from \<open>set l = (J - K) \<and> length l = ?t\<close>
      have "set l = (J - K)" by blast
      from \<open>set l = (J - K) \<and> length l = ?t\<close>
      have "length l = ?t" by blast
      from \<open>j < ?t\<close> K_seq_indep have "indep (K_seq K J l j)" by auto
      from someI_ex[OF ex_X[OF \<open>F \<subseteq> carrier\<close> \<open>basis_in F J\<close> \<open>basis_in F K\<close> refl \<open>set l = (J - K)\<close>
            \<open>length l = ?t\<close> \<open>indep (K_seq K J l j)\<close> \<open>j < ?t\<close>]]
      show "card (Eps (X_prop K J l (K_seq K J l j) j)) \<le> 
        card (circuits_in ((K_seq K J l j) \<union> {l ! j}))" by blast
    qed

    moreover have "\<forall>j. j < ?t \<longrightarrow> card (circuits_in ((K_seq K J l j) \<union> {l ! j})) \<le> p"
    proof (rule allI, rule impI)
      fix j
      assume "j < ?t"

      from \<open>set l = (J - K) \<and> length l = ?t\<close> \<open>j < ?t\<close>
      have "l ! j \<in> J"
      proof -
        from \<open>set l = (J - K) \<and> length l = ?t\<close> have set_l: "set l = J - K" and len_l: "length l = ?t" by auto
        from \<open>j < ?t\<close> len_l have "j < length l" by simp
        then have "l ! j \<in> set l" by (rule nth_mem)
        with set_l have "l ! j \<in> J - K" by simp
        then show "l ! j \<in> J" by (rule DiffD1)
      qed
      with basis_in_subset_carrier[OF \<open>F \<subseteq> carrier\<close> \<open>basis_in F J\<close>] \<open>F \<subseteq> carrier\<close>
      have "l ! j \<in> carrier" by blast

      from \<open>j < ?t\<close> K_seq_indep have "indep (K_seq K J l j)" by auto

      from assms(2) \<open>indep (K_seq K J l j)\<close> \<open>l ! j \<in> carrier\<close>
      show "card (circuits_in ((K_seq K J l j) \<union> {l ! j})) \<le> p" by blast
    qed

    ultimately have "\<forall>j. j < ?t \<longrightarrow> card (Eps (X_prop K J l (K_seq K J l j) j)) \<le> p"
      using dual_order.trans by blast

    then have
      "(\<Sum>j = 0..<?t. card (Eps (X_prop K J l (K_seq K J l j) j))) \<le> (\<Sum>j = 0..<?t. p)"
      by (meson assms atLeastLessThan_iff sum_mono)

    with card_leq_sum
    have "card (K - K_seq K J l ?t) \<le> (\<Sum>j = 0..<?t. p)" by linarith
    moreover have 
      "(\<Sum>j = 0..<?t. p) = p * ?t" by simp
    ultimately have
      "card (K - K_seq K J l ?t) \<le> p * ?t" by presburger

    from K_seq_t have "(K_seq K J l ?t) \<inter> (J - K) = set (take ?t l)" by blast
    with \<open>set l = (J - K) \<and> length l = ?t\<close>
    have "(K_seq K J l ?t) \<inter> (J - K) = (J - K)" by simp
    then have "J - K \<subseteq> (K_seq K J l ?t)" by blast
    with K_seq_t have "J \<subseteq> (K_seq K J l ?t)" by blast

    have "J = (K_seq K J l ?t)"
    proof (rule ccontr)
      assume "J \<noteq> K_seq K J l ?t"
      with \<open>J \<subseteq> (K_seq K J l ?t)\<close>
      have "\<exists>J' x. J' = insert x J \<and> J' \<subseteq> (K_seq K J l ?t) \<and> x \<notin> J" by blast
      then obtain J' x where "J' = insert x J" "J' \<subseteq> (K_seq K J l ?t)" "x \<notin> J" by blast

      from K_seq_indep \<open>J' \<subseteq> (K_seq K J l ?t)\<close> indep_subset
      have "indep J'" by blast

      from K_seq_t have "(K_seq K J l ?t) \<subseteq> J \<union> K" by blast
      with \<open>J \<subseteq> F\<close> \<open>K \<subseteq> F\<close> have "(K_seq K J l ?t) \<subseteq> F" by blast

      from \<open>J' = insert x J\<close> \<open>J' \<subseteq> (K_seq K J l ?t)\<close> \<open>(K_seq K J l ?t) \<subseteq> F\<close>
      have "x \<in> F" by blast
      with \<open>x \<notin> J\<close> have "x \<in> F - J" by blast

      from basis_in_max_indep_in[OF \<open>F \<subseteq> carrier\<close> \<open>basis_in F J\<close> \<open>x \<in> F - J\<close>]
      have "\<not> indep_in F (insert x J)" by blast
      with \<open>J' = insert x J\<close> have "\<not> indep_in F J'" by blast

      have "J' \<subseteq> F"
        using \<open>J' \<subseteq> K_seq K J l ?t\<close> \<open>K_seq K J l ?t \<subseteq> F\<close> by blast 
      with \<open>\<not> indep_in F J'\<close> indep_in_def have "\<not> indep J'" by blast
      with \<open>indep J'\<close> show "False" by blast
    qed

    with \<open>card (K - K_seq K J l ?t) \<le> p * ?t\<close>
    have "card (K - J) \<le> p * card (J - K)" by simp

    have "card J \<ge> card (K \<inter> J)"
      by (simp add: \<open>finite J\<close> card_mono)
    then have "p * card J \<ge> p * card (K \<inter> J)"
      by auto

    from \<open>finite K\<close> have "card K = card (K - J) + card (K \<inter> J)"
    proof -
      have union_eq: "K - J \<union> K \<inter> J = K" by blast
      have disj: "(K - J) \<inter> (K \<inter> J) = {}" by blast
      have fin1: "finite (K - J)" using \<open>finite K\<close> by simp
      have fin2: "finite (K \<inter> J)" using \<open>finite K\<close> by simp
      have "card K = card (K - J \<union> K \<inter> J)" using union_eq by simp
      also have "... = card (K - J) + card (K \<inter> J)"
        using card_Un_disjoint[OF fin1 fin2 disj] by simp
      finally show "card K = card (K - J) + card (K \<inter> J)" .
    qed
    also have "... \<le>  p * card (J - K) + card (K \<inter> J)"
      using \<open>card (K - J) \<le> p * card (J - K)\<close> by auto
    also have "... = p * card (J - K) + p * card (K \<inter> J) - p * card (K \<inter> J) + card (K \<inter> J)"
      by auto
    also have "... = p * card J - p * card (K \<inter> J) + card (K \<inter> J)"
      by (simp add: Int_commute \<open>finite J\<close> card_Diff_subset_Int right_diff_distrib')
    also have "... = p * card J - (p - 1) * card (K \<inter> J)"
      using \<open>p * card J \<ge> p * card (K \<inter> J)\<close>
    proof -
      have distrib: "(p - 1) * card (K \<inter> J) = p * card (K \<inter> J) - card (K \<inter> J)"
        by (simp add: left_diff_distrib')
      have le1: "card (K \<inter> J) \<le> p * card (K \<inter> J)"
        using mult_le_mono1[OF \<open>1 \<le> p\<close>, of "card (K \<inter> J)"] by simp
      show "p * card J - p * card (K \<inter> J) + card (K \<inter> J) = p * card J - (p - 1) * card (K \<inter> J)"
        using distrib le1 \<open>p * card J \<ge> p * card (K \<inter> J)\<close> by arith
    qed
    also have "... \<le> p * card J" by auto
    finally show "card K \<le> p * card J" .
  qed

  let ?fracs = "{Frac (int (lower_rank_of X)) (int (upper_rank_of X)) | X. X \<subseteq> carrier}"
  have "?fracs \<noteq> {}" by blast
  from carrier_finite have "finite ?fracs" by auto

  from Min_in[OF \<open>finite ?fracs\<close> \<open>?fracs \<noteq> {}\<close>]
  have "\<exists>F \<subseteq> carrier. Frac (int (lower_rank_of F)) (int (upper_rank_of F)) = Min ?fracs"
  proof -
    have "Min ?fracs \<in> ?fracs"
      using Min_in[OF \<open>finite ?fracs\<close> \<open>?fracs \<noteq> {}\<close>] .
    then obtain F where "F \<subseteq> carrier"
      and "Min ?fracs = Frac (int (lower_rank_of F)) (int (upper_rank_of F))"
      by (auto simp: mem_Collect_eq)
    then show "\<exists>F \<subseteq> carrier. Frac (int (lower_rank_of F)) (int (upper_rank_of F)) = Min ?fracs"
      by auto
  qed
  then obtain F where "F \<subseteq> carrier" "Frac (int (lower_rank_of F)) (int (upper_rank_of F)) = Min ?fracs"
    by blast

  let ?basis_cards = "{card B | B. basis_in F B}"
  from basis_in_ex[OF \<open>F \<subseteq> carrier\<close>] have "?basis_cards \<noteq> {}" by blast
  from \<open>F \<subseteq> carrier\<close> have "finite ?basis_cards" by (simp add: collect_basis_in_finite)

  from Min_in[OF \<open>finite ?basis_cards\<close> \<open>?basis_cards \<noteq> {}\<close>]
  have "\<exists>J. basis_in F J \<and> card J = Min ?basis_cards" by auto
  then obtain J where "basis_in F J" "card J = Min ?basis_cards" by blast

  from Max_in[OF \<open>finite ?basis_cards\<close> \<open>?basis_cards \<noteq> {}\<close>]
  have "\<exists>K. basis_in F K \<and> card K = Max ?basis_cards" by auto
  then obtain K where "basis_in F K" "card K = Max ?basis_cards" by blast

  from \<open>card J = Min ?basis_cards\<close> \<open>card K = Max ?basis_cards\<close>
  have "card J \<le> card K"
    using \<open>Min ?basis_cards \<in> ?basis_cards\<close> \<open>finite ?basis_cards\<close> by auto

  from \<open>Frac (int (lower_rank_of F)) (int (upper_rank_of F)) = Min ?fracs\<close>
    \<open>card J = Min ?basis_cards\<close> \<open>card K = Max ?basis_cards\<close> lower_rank_of_def upper_rank_of_def
  have "Min ?fracs = Frac (int (card J)) (int (card K))"
  proof -
    have lower_eq: "lower_rank_of F = card J"
      using \<open>card J = Min ?basis_cards\<close> unfolding lower_rank_of_def by simp
    have upper_eq: "upper_rank_of F = card K"
      using \<open>card K = Max ?basis_cards\<close> unfolding upper_rank_of_def by simp
    from \<open>Frac (int (lower_rank_of F)) (int (upper_rank_of F)) = Min ?fracs\<close>
    have "Frac (int (card J)) (int (card K)) = Min ?fracs"
      by (simp add: lower_eq upper_eq)
    then show ?thesis by simp
  qed
  moreover have "rank_quotient = Min ?fracs"
  proof -
    have rw1: "\<And>X. X \<subseteq> carrier \<Longrightarrow>
      Frac (int (lower_rank_of X)) (int (rank X)) = Frac (int (lower_rank_of X)) (int (upper_rank_of X))"
      using upper_rank_equiv_rank by simp
    have rw2: "\<And>X. X \<subseteq> carrier \<Longrightarrow>
      Frac (int (lower_rank_of X)) (int (upper_rank_of X)) = Frac (int (lower_rank_of X)) (int (rank X))"
      using upper_rank_equiv_rank by simp
    have set_eq: "{Frac (int (lower_rank_of X)) (int (rank X)) | X. X \<subseteq> carrier} =
                  {Frac (int (lower_rank_of X)) (int (upper_rank_of X)) | X. X \<subseteq> carrier}"
    proof (rule set_eqI)
      fix q
      show "q \<in> {Frac (int (lower_rank_of X)) (int (rank X)) | X. X \<subseteq> carrier} \<longleftrightarrow>
            q \<in> {Frac (int (lower_rank_of X)) (int (upper_rank_of X)) | X. X \<subseteq> carrier}"
      proof
        assume "q \<in> {Frac (int (lower_rank_of X)) (int (rank X)) | X. X \<subseteq> carrier}"
        then obtain X where "X \<subseteq> carrier"
          and "q = Frac (int (lower_rank_of X)) (int (rank X))" by blast
        then have "q = Frac (int (lower_rank_of X)) (int (upper_rank_of X))"
          using rw1 by simp
        then show "q \<in> {Frac (int (lower_rank_of X)) (int (upper_rank_of X)) | X. X \<subseteq> carrier}"
          using \<open>X \<subseteq> carrier\<close> by blast
      next
        assume "q \<in> {Frac (int (lower_rank_of X)) (int (upper_rank_of X)) | X. X \<subseteq> carrier}"
        then obtain X where "X \<subseteq> carrier"
          and "q = Frac (int (lower_rank_of X)) (int (upper_rank_of X))" by blast
        then have "q = Frac (int (lower_rank_of X)) (int (rank X))"
          using rw2 by simp
        then show "q \<in> {Frac (int (lower_rank_of X)) (int (rank X)) | X. X \<subseteq> carrier}"
          using \<open>X \<subseteq> carrier\<close> by blast
      qed
    qed
    then show ?thesis
      unfolding rank_quotient_def by simp
  qed
  ultimately have "rank_quotient = Frac (int (card J)) (int (card K))" by simp
  from basis_cards_ineq \<open>F \<subseteq> carrier\<close> \<open>basis_in F J\<close> \<open>basis_in F K\<close>
  have "card K \<le> p * card J" by blast

  then have "Frac (int (card J)) (int (card K)) \<ge> Fract 1 (int p)"
  proof (cases "card J = card K")
    case True
    then have "Frac (int (card J)) (int (card K)) = 1" using Frac_def by simp
    also have "... \<ge> Fract 1 (int p)" using assms(1)
      by (simp add: Fract_le_one_iff)
    finally show ?thesis .
  next
    case False
    have "card K > 0"
    proof (rule ccontr)
      assume "\<not> card K > 0"
      then have "card K = 0" by blast
      with \<open>card J \<le> card K\<close> have "card J = 0" by simp
      with \<open>card K = 0\<close> False show False by simp
    qed

    from \<open>card K \<le> p * card J\<close>
    have "1 * (int (card K)) \<le> (int p) * (int (card J))"
      by (simp add: nat_int_comparison(3))
    then have
      "1 * (int (card K)) \<le> (int (card J)) * (int p)"
      by (simp add: mult.commute)

    with \<open>card K > 0\<close> assms(1) have
      "Fract 1 (int p) \<le> Fract (int (card J)) (int (card K))"
      by simp

    with Frac_def False show ?thesis by auto 
  qed

  with \<open>rank_quotient = Frac (int (card J)) (int (card K))\<close>
  show "rank_quotient \<ge> Fract 1 (int p)" by auto
qed


end


subsection \<open>Theorem 13.9\<close>

subsubsection \<open>Auxiliary lemmas\<close>

context matroid
begin

lemma card_eq_basis:
  "basis X \<Longrightarrow> indep Y \<Longrightarrow> card X = card Y \<Longrightarrow> basis Y"
proof -
  assume "basis X" and "indep Y" and "card X = card Y"

  from basis_subset_carrier[OF \<open>basis X\<close>] have X_carrier: "X \<subseteq> carrier" .
  from indep_subset_carrier[OF \<open>indep Y\<close>] have Y_carrier: "Y \<subseteq> carrier" .

  from basis_iff_rank_of[OF X_carrier] \<open>basis X\<close>
  have X_indep_rank: "rank_of X = card X \<and> rank_of X = rank_of carrier" by blast
  from indep_iff_rank_of[of X] X_carrier X_indep_rank
  have X_indep: "indep X" by blast
  from X_indep_rank have X_rank: "rank_of X = rank_of carrier" by blast

  from indep_iff_rank_of[OF X_carrier] X_indep
  have "rank_of X = card X" by blast
  with X_rank have carrier_rank: "rank_of carrier = card X" by simp

  from indep_iff_rank_of[OF Y_carrier] \<open>indep Y\<close>
  have "rank_of Y = card Y" by blast
  with \<open>card X = card Y\<close> carrier_rank
  have Y_rank: "rank_of Y = rank_of carrier" by simp

  from basis_iff_rank_of[OF Y_carrier] indep_iff_rank_of[OF Y_carrier] \<open>indep Y\<close> Y_rank
  show "basis Y" by blast
qed

end


lemma ex_max: "(A::nat set) \<noteq> {} \<Longrightarrow> finite A \<Longrightarrow> \<exists>a \<in> A. \<forall>a' \<in> A. a \<ge> a'"
  by (meson Max_ge Max_in)

lemma ex_max_card: "\<A> \<noteq> {} \<Longrightarrow> finite \<A> \<Longrightarrow> \<exists>A \<in> \<A>. \<forall>A' \<in> \<A>. card A \<ge> card A'"
proof-
  assume "\<A> \<noteq> {}" "finite \<A>"
  let ?card_set = "card ` \<A>"
  from `\<A> \<noteq> {}` have "?card_set \<noteq> {}" by blast
  from `finite \<A>` have "finite ?card_set" by blast
  from ex_max[OF `?card_set \<noteq> {}` `finite ?card_set`]
  have "\<exists>a \<in> ?card_set. \<forall>a' \<in> ?card_set. a \<ge> a'" by blast
  then show "\<exists>A \<in> \<A>. \<forall>A' \<in> \<A>. card A \<ge> card A'" by blast
qed

lemma ex_max_card_inter_P: 
  "\<A> \<noteq> {} \<Longrightarrow> finite \<A> \<Longrightarrow> 
    \<exists>A1 A2. A1 \<in> \<A> \<and> A2 \<in> \<A> \<and> P A1 A2 \<Longrightarrow>
    \<exists>A1 A2. A1 \<in> \<A> \<and> A2 \<in> \<A> \<and> P A1 A2 \<and>
      (\<forall>A1' A2'. A1' \<in> \<A> \<longrightarrow> A2' \<in> \<A> \<longrightarrow> P A1' A2' \<longrightarrow> card (A1 \<inter> A2) \<ge> card (A1' \<inter> A2'))"
proof-
  assume "\<A> \<noteq> {}"
  assume "finite \<A>"
  assume ex: "\<exists>A1 A2. A1 \<in> \<A> \<and> A2 \<in> \<A> \<and> P A1 A2"
  let ?cart_prod = "\<A> \<times> \<A>"
  let ?int_set = "{A1 \<inter> A2 | A1 A2 . (A1, A2) \<in> ?cart_prod}"
  let ?int_set_P = "{A1 \<inter> A2 | A1 A2 . (A1, A2) \<in> ?cart_prod \<and> P A1 A2}"

  let ?int_set_alt = "(\<lambda>(A, B). A \<inter> B) ` (\<A> \<times> \<A>)"
  have 1: "?int_set = ?int_set_alt" by auto
  from `finite \<A>` have 2: "finite ?int_set_alt" by blast

  from ex have "?int_set_P \<noteq> {}" by blast
  from 1 2 have "finite ?int_set" by auto
  then have "finite ?int_set_P" 
    proof -
      have "?int_set_P \<subseteq> ?int_set" by blast
      with \<open>finite ?int_set\<close> show ?thesis using finite_subset by blast
    qed

  from ex_max_card[OF `?int_set_P \<noteq> {}` `finite ?int_set_P`] show ?thesis by blast
qed


lemma all_cards_equal_member_iff:
  assumes "finite E" "\<forall>A1 A2. A1 \<in> S \<longrightarrow> A2 \<in> S \<longrightarrow> card A1 = card A2" "\<forall>A. A \<in> S \<longrightarrow> A \<subseteq> E"
  shows "B \<in> S \<longleftrightarrow> ((\<exists>B' \<in> S. B \<subseteq> B') \<and> (\<forall>x B'. (x \<in> E - B) \<longrightarrow> (B' \<in> S) \<longrightarrow> (\<not>(insert x B) \<subseteq> B')))"
proof-
  have LTR: "B \<in> S \<longrightarrow> ((\<exists>B' \<in> S. B \<subseteq> B') \<and> (\<forall>x B'. (x \<in> E - B) \<longrightarrow> (B' \<in> S) \<longrightarrow> (\<not>(insert x B) \<subseteq> B')))" 
  proof
    assume "B \<in> S"
    then have 1: "(\<exists>B' \<in> S. B \<subseteq> B')" by blast

    have 2: "(\<forall>x B'. (x \<in> E - B) \<longrightarrow> (B' \<in> S) \<longrightarrow> (\<not>(insert x B) \<subseteq> B'))"
    proof(cases "B = E")
      case True
      then show ?thesis by blast
    next
      case False
      show ?thesis
      proof ((rule allI)+, (rule impI)+)
        fix x B'
        assume "x \<in> E - B" "B' \<in> S"
        from `x \<in> E - B` have "x \<notin> B" by blast
        from `B \<in> S` assms `x \<notin> B` card_insert_disjoint finite_subset
        have "card (insert x B) = Suc (card B)"
        proof -
          from assms(3) \<open>B \<in> S\<close> have "B \<subseteq> E" by blast
          with assms(1) have "finite B" by (blast intro: finite_subset)
          from card_insert_disjoint[OF this \<open>x \<notin> B\<close>] show ?thesis .
        qed
        show "\<not>(insert x B) \<subseteq> B'"
        proof (rule notI)
          assume "insert x B \<subseteq> B'"
          from assms(3) `B' \<in> S` have "B' \<subseteq> E" by blast
          with assms(1) have "finite B'" using finite_subset by blast
          from card_mono[OF `finite B'` `insert x B \<subseteq> B'`]
          have "card (insert x B) \<le> card B'" .
          with `card (insert x B) = Suc (card B)` have "Suc (card B) \<le> card B'" by simp
          from assms(2) `B \<in> S` `B' \<in> S` have "card B = card B'" by blast
          with `Suc (card B) \<le> card B'` have "Suc (card B') \<le> card B'" by simp
          then show False using Suc_n_not_le_n by blast
        qed
      qed
    qed

    from 1 2 show "((\<exists>B' \<in> S. B \<subseteq> B') \<and> (\<forall>x B'. (x \<in> E - B) \<longrightarrow> (B' \<in> S) \<longrightarrow> (\<not>(insert x B) \<subseteq> B')))" by blast
  qed

  have "\<not>B \<in> S \<longrightarrow> (\<not>(\<exists>B' \<in> S. B \<subseteq> B') \<or> \<not>(\<forall>x B'. (x \<in> E - B) \<longrightarrow> (B' \<in> S) \<longrightarrow> (\<not>(insert x B) \<subseteq> B')))"
  proof
    assume "\<not>B \<in> S"
    show "(\<not>(\<exists>B' \<in> S. B \<subseteq> B') \<or> \<not>(\<forall>x B'. (x \<in> E - B) \<longrightarrow> (B' \<in> S) \<longrightarrow> (\<not>(insert x B) \<subseteq> B')))"
    proof (cases "(\<exists>B' \<in> S. B \<subseteq> B')")
      case True
      then obtain B' where B': "B' \<in> S \<and> B \<subseteq> B'" by blast

      from `\<not>B \<in> S` B' have "\<exists>x. ((insert x B) \<subseteq> B')"
      proof -
        from B' have B'_in_S: "B' \<in> S" by blast
        from B' have B_sub_B': "B \<subseteq> B'" by blast
        from `\<not>B \<in> S` B'_in_S have "B \<noteq> B'" by blast
        with B_sub_B' have "B \<subset> B'" by blast
        then obtain x where "x \<in> B' - B" by blast
        with B_sub_B' show "\<exists>x. insert x B \<subseteq> B'" by blast
      qed
      with B' `\<not>B \<in> S` have "\<exists>x B'. x \<in> E - B \<and> B' \<in> S \<and> ((insert x B) \<subseteq> B')"
        using assms(3) equalityI by fastforce
      then show ?thesis by blast
    next
      case False
      then show ?thesis by blast
    qed
  qed

  then have RTL: "((\<exists>B' \<in> S. B \<subseteq> B') \<and> (\<forall>x B'. (x \<in> E - B) \<longrightarrow> (B' \<in> S) \<longrightarrow> (\<not>(insert x B) \<subseteq> B'))) \<longrightarrow> B \<in> S"
    by blast

  from LTR RTL show ?thesis by blast
qed

lemma all_cards_equal_member_iff_alt:
  assumes "finite E" "\<forall>A1 A2. A1 \<in> S \<longrightarrow> A2 \<in> S \<longrightarrow> card A1 = card A2" "\<forall>A. A \<in> S \<longrightarrow> A \<subseteq> E"
  shows "B \<in> S \<longleftrightarrow> 
    ((B \<subseteq> E \<and> (\<exists>B' \<in> S. B \<subseteq> B')) \<and> (\<forall>x \<in> E - B. (\<not>(insert x B) \<subseteq> E) \<or> (\<forall> B'. (B' \<in> S) \<longrightarrow> (\<not>(insert x B) \<subseteq> B'))))"
proof -
  have iff1: "B \<in> S \<longleftrightarrow>
    ((\<exists>B' \<in> S. B \<subseteq> B') \<and> (\<forall>x B'. (x \<in> E - B) \<longrightarrow> (B' \<in> S) \<longrightarrow> (\<not>(insert x B) \<subseteq> B')))"
    using all_cards_equal_member_iff[OF assms] by blast
  show ?thesis
  proof
    assume "B \<in> S"
    with assms(3) have "B \<subseteq> E" by blast
    from iff1 \<open>B \<in> S\<close>
    have ex_B': "\<exists>B' \<in> S. B \<subseteq> B'"
      and forall1: "\<forall>x B'. (x \<in> E - B) \<longrightarrow> (B' \<in> S) \<longrightarrow> \<not> (insert x B \<subseteq> B')"
      by blast+
    have forall2: "\<forall>x \<in> E - B. (\<not>(insert x B) \<subseteq> E) \<or> (\<forall> B'. (B' \<in> S) \<longrightarrow> \<not> (insert x B \<subseteq> B'))"
    proof
      fix x
      assume "x \<in> E - B"
      with forall1 have "\<forall>B'. (B' \<in> S) \<longrightarrow> \<not> (insert x B \<subseteq> B')" by blast
      then show "(\<not>(insert x B) \<subseteq> E) \<or> (\<forall> B'. (B' \<in> S) \<longrightarrow> \<not> (insert x B \<subseteq> B'))" by blast
    qed
    from \<open>B \<subseteq> E\<close> ex_B' forall2
    show "(B \<subseteq> E \<and> (\<exists>B' \<in> S. B \<subseteq> B')) \<and>
      (\<forall>x \<in> E - B. (\<not>(insert x B) \<subseteq> E) \<or> (\<forall> B'. (B' \<in> S) \<longrightarrow> (\<not>(insert x B) \<subseteq> B')))"
      by blast
  next
    assume P2: "(B \<subseteq> E \<and> (\<exists>B' \<in> S. B \<subseteq> B')) \<and>
      (\<forall>x \<in> E - B. (\<not>(insert x B) \<subseteq> E) \<or> (\<forall> B'. (B' \<in> S) \<longrightarrow> (\<not>(insert x B) \<subseteq> B')))"
    then have "B \<subseteq> E" and ex_B': "\<exists>B' \<in> S. B \<subseteq> B'"
      and forall2: "\<forall>x \<in> E - B. (\<not>(insert x B) \<subseteq> E) \<or> (\<forall> B'. (B' \<in> S) \<longrightarrow> (\<not>(insert x B) \<subseteq> B'))"
      by blast+
    have forall1: "\<forall>x B'. (x \<in> E - B) \<longrightarrow> (B' \<in> S) \<longrightarrow> \<not> (insert x B \<subseteq> B')"
    proof (rule allI, rule allI, rule impI, rule impI)
      fix x B'
      assume "x \<in> E - B" "B' \<in> S"
      from \<open>x \<in> E - B\<close> \<open>B \<subseteq> E\<close> have "insert x B \<subseteq> E" by blast
      with forall2 \<open>x \<in> E - B\<close>
      have "\<forall> B'. (B' \<in> S) \<longrightarrow> \<not> (insert x B \<subseteq> B')" by blast
      with \<open>B' \<in> S\<close> show "\<not>(insert x B) \<subseteq> B'" by blast
    qed
    with ex_B' iff1
    show "B \<in> S" by blast
  qed
qed

lemma card_eq1:
  assumes "finite B1" "finite B2" "Y \<subseteq> B2"
  shows "card (B1 \<inter> B2) + card (Y - B1) + card ((B2 - B1) - Y) = card B2"
proof-
  have "B2 = (B1 \<inter> B2) \<union> (B2 - B1)" by auto
  also have "... = (B1 \<inter> B2) \<union> ((B2 - B1) - Y) \<union> ((B2 - B1) \<inter> Y)" by blast
  also have "... = (B1 \<inter> B2) \<union> ((B2 - B1) - Y) \<union> (Y - B1)" using assms by blast
  finally have 1: "B2 = (B1 \<inter> B2) \<union> ((B2 - B1) - Y) \<union> (Y - B1)" .

  have 2: "(B1 \<inter> B2) \<inter> (((B2 - B1) - Y) \<union> (Y - B1)) = {}" using assms by blast
  have 3: "((B2 - B1) - Y) \<inter> (Y - B1) = {}" by blast

  have finite_1: "finite (B1 \<inter> B2)" using assms by blast
  have finite_2: "finite (((B2 - B1) - Y) \<union> (Y - B1))" using assms by (simp add: finite_subset)
  have finite_3: "finite ((B2 - B1) - Y)" using assms by blast
  have finite_4: "finite (Y - B1)" using assms by (simp add: finite_subset)

  from 1 card_Un_disjoint[OF finite_1 finite_2 2] 
  have "card B2 = card (B1 \<inter> B2) + card (((B2 - B1) - Y) \<union> (Y - B1))"
  proof -
    have "B2 = (B1 \<inter> B2) \<union> ((B2 - B1) - Y \<union> (Y - B1))"
      using 1 by auto
    then show ?thesis
      using card_Un_disjoint[OF finite_1 finite_2 2] by simp
  qed

  with card_Un_disjoint[OF finite_3 finite_4 3]
  have "card B2 = card (B1 \<inter> B2) + card (Y - B1) + card ((B2 - B1) - Y)" 
    by simp
  then show ?thesis by simp
qed

lemma card_ineq2:
  assumes "finite B1" "finite B2" "X \<subseteq> B1" "Y \<subseteq> B2" "B2 \<inter> (X - Y) = {}"
  shows "card B1 \<ge> card (B1 \<inter> B2) + card (X - Y)"
proof-
  have "card (B1 - B2) \<ge> card (X - B2)" using assms by (simp add: Diff_mono card_mono)
  also have "... \<ge> card ((X - Y) - B2)" using assms 
    by (meson Diff_mono Diff_subset card_mono dual_order.trans equalityD1 finite_Diff2)
  have "(X - Y) \<inter> B2 = {}" using assms(5) by blast
  then have "X - Y - B2 = X - Y" by (rule Diff_triv)
  with \<open>card (X - Y - B2) \<le> card (B1 - B2)\<close> have "card (B1 - B2) \<ge> card (X - Y)" by simp
  have "card (B1 - B2) \<ge> card (X - Y)"
    using \<open>card (X - Y) \<le> card (B1 - B2)\<close> by blast

  have finite_1: "finite (B1 \<inter> B2)" using assms by blast
  have finite_2: "finite (B1 - B2)" using assms by blast
  have 1: "(B1 \<inter> B2) \<inter> (B1 - B2) = {}" by blast

  have "card B1 = card ((B1 \<inter> B2) \<union> (B1 - B2))"
    by (simp add: Int_Diff_Un)
  also have "... = card (B1 \<inter> B2) + card (B1 - B2)" 
    using card_Un_disjoint[OF finite_1 finite_2 1] by blast
  also have "... \<ge> card (B1 \<inter> B2) + card (X - Y)"
    using \<open>card (X - Y) \<le> card (B1 - B2)\<close> by auto
  then have "card B1 \<ge> card (B1 \<inter> B2) + card (X - Y)"
    using \<open>card (B1 \<inter> B2 \<union> (B1 - B2)) = card (B1 \<inter> B2) + card (B1 - B2)\<close>
      \<open>card B1 = card (B1 \<inter> B2 \<union> (B1 - B2))\<close> by presburger
  then show ?thesis by blast
qed


subsubsection \<open>Theorem statement\<close>

lemma matroid_set_of_bases_iff:
  assumes "finite E" "\<B> \<subseteq> Pow E"
  shows "(\<exists>indep. matroid E indep \<and> \<B> = {B. (indep_system.basis E indep B)}) \<longleftrightarrow> 
        (\<B> \<noteq> {} \<and> (\<forall>B1 B2 x. B1 \<in> \<B> \<longrightarrow> B2 \<in> \<B> \<longrightarrow> x \<in> B1 - B2 \<longrightarrow> 
                   (\<exists>y. y \<in> B2 - B1 \<and> insert y (B1 - {x}) \<in> \<B>)))"
proof-
  show ?thesis
  proof
    assume assm: "\<exists>indep. matroid E indep \<and> \<B> = {B. (indep_system.basis E indep B)}"
    then obtain indep where 
      indep_p: "matroid E indep \<and> \<B> = {B. (indep_system.basis E indep B)}" by blast
    have indep_sys: "indep_system E indep" using indep_p matroid.axioms(1) by blast

(* We show that there is at least one basis *)
    from indep_sys indep_system.indep_ex indep_system.indep_imp_subset_basis
    have "\<exists>B. indep_system.basis E indep B" by blast
    with indep_p have B1: "\<B> \<noteq> {}" by blast

(* We show the property (B2) *)
    have B2: "(\<forall>B1 B2 x. B1 \<in> \<B> \<longrightarrow> B2 \<in> \<B> \<longrightarrow> x \<in> B1 - B2 \<longrightarrow> 
              (\<exists>y. y \<in> B2 - B1 \<and> insert y (B1 - {x}) \<in> \<B>))"
    proof ((rule allI)+, (rule impI)+)
      fix B1 B2 x
      assume "B1 \<in> \<B>" "B2 \<in> \<B>" "x \<in> B1 - B2"
      from `B1 \<in> \<B>` indep_p have basis_B1: "indep_system.basis E indep B1" by blast
      from `B2 \<in> \<B>` indep_p have basis_B2: "indep_system.basis E indep B2" by blast

      from basis_B1 indep_sys indep_system.subset_basis_imp_indep 
      have indep_B1_x: "indep (B1 - {x})" by blast 

      from `B2 \<in> \<B>` indep_p indep_sys indep_system.basis_def
      have indep_B2: "indep B2" by blast 

      from indep_p matroid.basis_card basis_B1 basis_B2
      have "card B1 = card B2" by blast
      with `x \<in> B1 - B2` have card_less: "card (B1 - {x}) < card B2"
        using card_Diff1_less[OF indep_system.basis_finite[OF indep_sys basis_B1] DiffD1[OF \<open>x \<in> B1 - B2\<close>]]
        by simp

      from indep_p indep_B1_x indep_B2 matroid.augment card_less
      have "\<exists>y\<in>B2 - (B1 - {x}). indep (insert y (B1 - {x}))" by blast
      with `x \<in> B1 - B2` 
      have "\<exists>y\<in>B2 - B1. indep (insert y (B1 - {x}))" by blast

      then obtain y where y_p: "y \<in> B2 - B1 \<and> indep (insert y (B1 - {x}))" by blast

      from y_p `x \<in> B1 - B2` have "card (insert y (B1 - {x})) = card B1"
      proof -
        from `x \<in> B1 - B2` have x_in_B1: "x \<in> B1" by blast
        from y_p have "y \<in> B2 - B1" by blast
        then have y_notin: "y \<notin> B1 - {x}" by blast

        from indep_system.basis_finite[OF indep_sys basis_B1] have B1_finite: "finite B1" .
        then have finite_B1_x: "finite (B1 - {x})" by blast

        from card_insert_disjoint[OF finite_B1_x y_notin]
        have eq1: "card (insert y (B1 - {x})) = Suc (card (B1 - {x}))" .

        from card.remove[OF B1_finite x_in_B1]
        have eq2: "card B1 = Suc (card (B1 - {x}))" .

        from eq1 eq2 show "card (insert y (B1 - {x})) = card B1" by simp
      qed

      with basis_B1 y_p indep_p have "indep_system.basis E indep (insert y (B1 - {x}))"
        proof -
          have mat: "matroid E indep" using indep_p by blast
          have indep_y: "indep (insert y (B1 - {x}))" using y_p by blast
          from \<open>card (insert y (B1 - {x})) = card B1\<close>
          have card_eq: "card B1 = card (insert y (B1 - {x}))" by (rule sym)
          from matroid.card_eq_basis[OF mat basis_B1 indep_y card_eq]
          show "indep_system.basis E indep (insert y (B1 - {x}))" .
        qed

      with y_p indep_p show "\<exists>y. y \<in> B2 - B1 \<and> insert y (B1 - {x}) \<in> \<B>" by blast
    qed

    from B1 B2 show "(\<B> \<noteq> {} \<and> (\<forall>B1 B2 x. B1 \<in> \<B> \<longrightarrow> B2 \<in> \<B> \<longrightarrow> x \<in> B1 - B2 \<longrightarrow> 
                   (\<exists>y. y \<in> B2 - B1 \<and> insert y (B1 - {x}) \<in> \<B>)))" by blast
  next
    assume assm: "(\<B> \<noteq> {} \<and> (\<forall>B1 B2 x. B1 \<in> \<B> \<longrightarrow> B2 \<in> \<B> \<longrightarrow> x \<in> B1 - B2 \<longrightarrow> 
                   (\<exists>y. y \<in> B2 - B1 \<and> insert y (B1 - {x}) \<in> \<B>)))"
    from assm have B1: "\<B> \<noteq> {}" by blast
    from assm have B2: "(\<forall>B1 B2 x. B1 \<in> \<B> \<longrightarrow> B2 \<in> \<B> \<longrightarrow> x \<in> B1 - B2 \<longrightarrow> 
                   (\<exists>y. y \<in> B2 - B1 \<and> insert y (B1 - {x}) \<in> \<B>))" by blast

(* We show that all elements of \<B> have the same cardinality *)
    have cards_equal: "\<forall>B1 B2. B1 \<in> \<B> \<longrightarrow> B2 \<in> \<B> \<longrightarrow> card B1 = card B2"
    proof (rule ccontr, goal_cases False)
      case False
      then have ex_B1_B2: "\<exists>B1 B2. B1 \<in> \<B> \<and> B2 \<in> \<B> \<and> card B1 > card B2" by (meson nat_neq_iff)

      have "finite \<B>" using assms(1) assms(2)
        by (simp add: finite_subset)

      from ex_max_card_inter_P[OF `\<B> \<noteq> {}` `finite \<B>` ex_B1_B2]
      have ex_max_card_B1_B2: "\<exists>B1 B2. B1 \<in> \<B> \<and> B2 \<in> \<B> \<and> card B1 > card B2 \<and>
        (\<forall>B1' B2'. B1' \<in> \<B> \<longrightarrow> B2' \<in> \<B> \<longrightarrow> card B1' > card B2' \<longrightarrow> card(B1 \<inter> B2) \<ge> card(B1' \<inter> B2'))"
        by blast
      then obtain B1 B2 where ex_B1_B2: "B1 \<in> \<B> \<and> B2 \<in> \<B> \<and> card B1 > card B2 \<and>
        (\<forall>B1' B2'. B1' \<in> \<B> \<longrightarrow> B2' \<in> \<B> \<longrightarrow> card B1' > card B2' \<longrightarrow> card(B1 \<inter> B2) \<ge> card(B1' \<inter> B2'))" by blast
      then have card_greater: "card B1 > card B2" by blast
      then have "\<exists>x. x \<in> B1 - B2"
      proof -
        from ex_B1_B2 assms(2) have "B1 \<subseteq> E" by blast
        from ex_B1_B2 assms(2) have "B2 \<subseteq> E" by blast
        from assms(1) \<open>B2 \<subseteq> E\<close> have "finite B2" using finite_subset by blast
        show "\<exists>x. x \<in> B1 - B2"
        proof (rule ccontr)
          assume "\<not> (\<exists>x. x \<in> B1 - B2)"
          then have "B1 \<subseteq> B2" by blast
          from card_mono[OF \<open>finite B2\<close> this] have "card B1 \<le> card B2" .
          with card_greater show False by simp
        qed
      qed
      then obtain x where ex_x: "x \<in> B1 - B2" by blast
      from B2 ex_B1_B2 ex_x have "(\<exists>y. y \<in> B2 - B1 \<and> insert y (B1 - {x}) \<in> \<B>)" by blast
      then obtain y where ex_y: "y \<in> B2 - B1 \<and> insert y (B1 - {x}) \<in> \<B>" by blast

      from card_greater have card_insert_greater: 
        "card (insert y (B1 - {x})) > card B2"
      proof -
        have "B1 \<subseteq> E" using ex_B1_B2 assms(2) by blast
        with assms(1) have "finite B1" using finite_subset by blast

        from ex_x have "x \<in> B1" by blast
        from ex_y have "y \<notin> B1" by blast
        then have "y \<notin> B1 - {x}" by blast

        from \<open>finite B1\<close> have "finite (B1 - {x})" by blast

        from \<open>x \<in> B1\<close> have card_diff: "card (B1 - {x}) = card B1 - 1"
          by (rule card_Diff_singleton)

        from \<open>finite (B1 - {x})\<close> \<open>y \<notin> B1 - {x}\<close>
        have "card (insert y (B1 - {x})) = card (B1 - {x}) + 1"
          by (simp add: card_insert_disjoint)
        also have "... = card B1 - 1 + 1"
          using card_diff by simp
        also have "... = card B1"
        proof -
          have "B1 \<noteq> {}" using \<open>x \<in> B1\<close> by blast
          with \<open>finite B1\<close> have "0 < card B1" by (simp add: card_gt_0_iff)
          then show "card B1 - 1 + 1 = card B1" by simp
        qed
        finally have "card (insert y (B1 - {x})) = card B1" .

        with card_greater show "card (insert y (B1 - {x})) > card B2" by simp
      qed

      from ex_y have card_inter_greater: "card ((insert y (B1 - {x})) \<inter> B2) > card (B1 \<inter> B2)"
        proof -
          have "B1 \<in> \<B>" using ex_B1_B2 by blast
          then have "B1 \<subseteq> E" using assms(2) by auto
          have finB1: "finite B1"
            using \<open>B1 \<subseteq> E\<close> assms(1) by (rule finite_subset)
          have "x \<notin> B2" using ex_x by blast
          have "y \<in> B2" using ex_y by blast
          have "y \<notin> B1" using ex_y by blast
          have eq1: "insert y (B1 - {x}) \<inter> B2 = insert y ((B1 - {x}) \<inter> B2)"
            using \<open>y \<in> B2\<close> by blast
          have eq2: "(B1 - {x}) \<inter> B2 = B1 \<inter> B2"
            using \<open>x \<notin> B2\<close> by blast
          have eq: "insert y (B1 - {x}) \<inter> B2 = insert y (B1 \<inter> B2)"
            using eq1 eq2 by simp
          have finBI: "finite (B1 \<inter> B2)" using finB1 by blast
          have notin: "y \<notin> B1 \<inter> B2" using \<open>y \<notin> B1\<close> by blast
          have card_eq: "card (insert y (B1 \<inter> B2)) = card (B1 \<inter> B2) + 1"
            using card_insert_disjoint[OF finBI notin] by simp
          have "card (insert y (B1 - {x}) \<inter> B2) = card (B1 \<inter> B2) + 1"
            using eq card_eq by simp
          then show ?thesis by simp
        qed

      from card_insert_greater card_inter_greater ex_B1_B2 ex_y show ?case by fastforce
    qed

(* We show that we have an independence system *)
    let ?indep = "\<lambda>X. X \<subseteq> E \<and> (\<exists>B \<in> \<B>. X \<subseteq> B)"

    have indep_sys: "indep_system E ?indep"
      apply (unfold_locales)
      subgoal using assms(1) .
      subgoal by blast
      subgoal using assm by blast
      subgoal using assm by auto
      done

(* We show that \<B> is the set of bases of this independence system *)
    have all_subset_E: "\<forall>A. A \<in> \<B> \<longrightarrow> A \<subseteq> E" using assms
      by blast

    from all_cards_equal_member_iff_alt[OF assms(1) cards_equal all_subset_E] have
      "\<forall>B. (B \<in> \<B>) = ((B \<subseteq> E \<and> (\<exists>B'\<in>\<B>. B \<subseteq> B')) \<and> 
        (\<forall>x\<in>E - B. \<not> insert x B \<subseteq> E \<or> (\<forall>B'. B' \<in> \<B> \<longrightarrow> \<not> insert x B \<subseteq> B')))" by blast
    then have
      "\<forall>B. (B \<in> \<B>) = ((B \<subseteq> E \<and> (\<exists>B'\<in>\<B>. B \<subseteq> B')) \<and> 
        (\<forall>x\<in>E - B. \<not> (insert x B \<subseteq> E \<and> \<not> (\<forall>B'. B' \<in> \<B> \<longrightarrow> \<not> insert x B \<subseteq> B'))))" by meson
    then have
      "\<forall>B. (B \<in> \<B>) = ((B \<subseteq> E \<and> (\<exists>B'\<in>\<B>. B \<subseteq> B')) \<and> 
        (\<forall>x\<in>E - B. \<not> (insert x B \<subseteq> E \<and> (\<exists>B' \<in> \<B>. insert x B \<subseteq> B'))))" by meson
    with indep_system.basis_def[OF indep_sys]
    have "\<forall>B. B \<in> \<B> = indep_system.basis E ?indep B" by presburger
    then have basis_set: "\<B> = {B. (indep_system.basis E ?indep B)}" by blast

(* We show that the augmentation property is satisfied *)
    have augment: "\<forall>X Y. ?indep X \<longrightarrow> ?indep Y \<longrightarrow> card X = Suc (card Y) \<longrightarrow> 
      (\<exists>x \<in> X - Y. ?indep (insert x Y))"
    proof ((rule allI)+, (rule impI)+)
      fix X Y
      assume indep_X: "?indep X"
      assume indep_Y: "?indep Y"
      assume card_X_Y: "card X = Suc (card Y)"

      have "finite \<B>" using assms(1) assms(2)
        by (simp add: finite_subset)
      from indep_X indep_Y have ex_B1_B2: "\<exists>B1 B2. B1 \<in> \<B> \<and> B2 \<in> \<B> \<and> X \<subseteq> B1 \<and> Y \<subseteq> B2" by auto

      from ex_max_card_inter_P[OF `\<B> \<noteq> {}` `finite \<B>` ex_B1_B2]
      have ex_max_card_B1_B2: 
        "\<exists>B1 B2. B1 \<in> \<B> \<and> B2 \<in> \<B> \<and> (X \<subseteq> B1 \<and> Y \<subseteq> B2) \<and> 
        (\<forall>B1' B2'. B1' \<in> \<B> \<longrightarrow> B2' \<in> \<B> \<longrightarrow> X \<subseteq> B1' \<and> Y \<subseteq> B2' \<longrightarrow> card (B1' \<inter> B2') \<le> card (B1 \<inter> B2))" by blast
      then obtain B1 B2 where ex_B1_B2: "B1 \<in> \<B> \<and> B2 \<in> \<B> \<and> (X \<subseteq> B1 \<and> Y \<subseteq> B2) \<and> 
        (\<forall>B1' B2'. B1' \<in> \<B> \<longrightarrow> B2' \<in> \<B> \<longrightarrow> X \<subseteq> B1' \<and> Y \<subseteq> B2' \<longrightarrow> card (B1' \<inter> B2') \<le> card (B1 \<inter> B2))" by blast

      show "(\<exists>x \<in> X - Y. ?indep (insert x Y))"
      proof (cases "B2 \<inter> (X - Y) = {}")
        case True
        show ?thesis
        proof (rule ccontr, goal_cases False)
          case False
          have "B1 \<in> \<B>"
            using ex_B1_B2 by blast
          then have "B1 \<subseteq> E"
            using all_subset_E by blast
          then have "finite B1"
            using assms(1) finite_subset by blast
          have "finite B2"
          proof -
            have "B2 \<in> \<B>" using ex_B1_B2 by blast
            hence "B2 \<subseteq> E" using all_subset_E by blast
            thus "finite B2" using assms(1) finite_subset by blast
          qed

          from card_eq1[OF `finite B1` `finite B2`] ex_B1_B2 
          have 1: "card (B1 \<inter> B2) + card (Y - B1) + card ((B2 - B1) - Y) = card B2" by auto

          from cards_equal ex_B1_B2 have 2: "card B2 = card B1" by simp

          from card_ineq2[OF `finite B1` `finite B2`] ex_B1_B2 True
          have 3: "card B1 \<ge> card (B1 \<inter> B2) + card (X - Y)" by blast

          from 1 2 3 
          have "card (B1 \<inter> B2) + card (Y - B1) + card ((B2 - B1) - Y) \<ge> 
            card (B1 \<inter> B2) + card (X - Y)"
            by simp
          then have 4: "card (Y - B1) + card ((B2 - B1) - Y) \<ge> card (X - Y)" by simp

          from `finite B1` `finite B2` ex_B1_B2 card_less_sym_Diff card_X_Y 
          have X_sub_B1: "X \<subseteq> B1" using ex_B1_B2 by blast
          have Y_sub_B2: "Y \<subseteq> B2" using ex_B1_B2 by blast
          have "finite X" using \<open>finite B1\<close> X_sub_B1 finite_subset by blast
          have "finite Y" using \<open>finite B2\<close> Y_sub_B2 finite_subset by blast
          have finite_int: "finite (X \<inter> Y)" using \<open>finite X\<close> by blast
          have finite_XY: "finite (X - Y)" using \<open>finite X\<close> by blast
          have finite_YX: "finite (Y - X)" using \<open>finite Y\<close> by blast
          have X_eq: "X = (X \<inter> Y) \<union> (X - Y)" by blast
          have Y_eq: "Y = (X \<inter> Y) \<union> (Y - X)" by blast
          have disj_X: "(X \<inter> Y) \<inter> (X - Y) = {}" by blast
          have disj_Y: "(X \<inter> Y) \<inter> (Y - X) = {}" by blast
          have card_X_eq: "card X = card (X \<inter> Y) + card (X - Y)"
            using X_eq card_Un_disjoint[OF finite_int finite_XY disj_X] by simp
          have card_Y_eq: "card Y = card (X \<inter> Y) + card (Y - X)"
            using Y_eq card_Un_disjoint[OF finite_int finite_YX disj_Y] by simp
          have 5: "card (X - Y) > card (Y - X)"
            using card_X_eq card_Y_eq card_X_Y by linarith


          from `finite B1` `finite B2` ex_B1_B2 card_mono Diff_mono 
          have 6: "card (Y - X) \<ge> card (Y - B1)"
          proof -
            from ex_B1_B2 have "X \<subseteq> B1" by blast
            then have subset: "Y - B1 \<subseteq> Y - X" by blast
            from ex_B1_B2 have "Y \<subseteq> B2" by blast
            from this \<open>finite B2\<close> have "finite Y" by (rule finite_subset)
            then have "finite (Y - X)" by blast
            from card_mono[OF this subset] show ?thesis .
          qed

          from 5 6 have 7: "card (X - Y) > card (Y - B1)" by simp

          from 4 7 have "card ((B2 - B1) - Y) > 0" by linarith
          then have "\<exists>y. y \<in> (B2 - B1) - Y"
            by (auto simp: card_gt_0_iff ex_in_conv)
          then obtain y where ex_y: "y \<in> (B2 - B1) - Y" by blast
          with ex_B1_B2 have y_in: "y \<in> (B2 - B1)" by blast

          from B2 y_in ex_B1_B2
          have "(\<exists>x. x \<in> B1 - B2 \<and> insert x (B2 - {y}) \<in> \<B>)" by blast
          then obtain x where ex_x: "x \<in> B1 - B2 \<and> insert x (B2 - {y}) \<in> \<B>" by blast

          from ex_x have card_inter_greater: "card (B1 \<inter> (insert x (B2 - {y}))) > card (B1 \<inter> B2)"
          proof -
            from ex_x have x_in: "x \<in> B1" and x_notin: "x \<notin> B2" by auto
            from y_in have y_notin: "y \<notin> B1" by auto
            have "B1 \<inter> insert x (B2 - {y}) = insert x (B1 \<inter> (B2 - {y}))"
              using x_in by auto
            also have "B1 \<inter> (B2 - {y}) = B1 \<inter> B2"
              using y_notin by auto
            finally have eq: "B1 \<inter> insert x (B2 - {y}) = insert x (B1 \<inter> B2)" .
            have finite_inter: "finite (B1 \<inter> B2)" using \<open>finite B1\<close> by auto
            have x_notin_inter: "x \<notin> B1 \<inter> B2" using x_notin by auto
            from card_insert_disjoint[OF finite_inter x_notin_inter]
            have "card (insert x (B1 \<inter> B2)) = card (B1 \<inter> B2) + 1" by simp
            with eq show ?thesis by simp
          qed

          with ex_B1_B2 show ?case
          proof -
            from ex_B1_B2 have B1_in: "B1 \<in> \<B>" by blast
            from ex_x have B2'_in: "insert x (B2 - {y}) \<in> \<B>" by blast
            from ex_B1_B2 have X_sub_B1: "X \<subseteq> B1" by blast
            from ex_B1_B2 have Y_sub_B2: "Y \<subseteq> B2" by blast
            from ex_y have y_notin_Y: "y \<notin> Y" by blast
            from Y_sub_B2 y_notin_Y have Y_sub: "Y \<subseteq> insert x (B2 - {y})" by blast
            from ex_B1_B2 have max_prop:
              "\<forall>B1' B2'. B1' \<in> \<B> \<longrightarrow> B2' \<in> \<B> \<longrightarrow> X \<subseteq> B1' \<and> Y \<subseteq> B2' \<longrightarrow> card (B1' \<inter> B2') \<le> card (B1 \<inter> B2)"
              by blast
            from max_prop B1_in B2'_in X_sub_B1 Y_sub
            have "card (B1 \<inter> insert x (B2 - {y})) \<le> card (B1 \<inter> B2)" by blast
            with card_inter_greater show False by simp
          qed
        qed
      next
        case False
        then have "\<exists>x. x \<in> B2 \<inter> (X - Y)" by blast
        then obtain x where "x \<in> B2 \<inter> (X - Y)" by blast
        then have x_in: "x \<in> B2 \<and> x \<in> X - Y" by blast
        with ex_B1_B2 have "(insert x Y) \<subseteq> B2" by blast
        with x_in show ?thesis
          by (meson all_subset_E ex_B1_B2 subset_trans)
      qed
    qed

    have mat: "matroid E ?indep"
      apply (unfold_locales)  
      subgoal using assms(1) .
      subgoal by blast
      subgoal using assm by blast
      subgoal using assm by auto
      subgoal using augment by auto
      done

    from mat basis_set show "\<exists>indep. matroid E indep \<and> \<B> = {B. (indep_system.basis E indep B)}"
      by blast
  qed
qed


subsection \<open>Theorem 13.10\<close>

subsubsection \<open>Abbreviations\<close>

abbreviation R1 where "R1 E (r::('a set \<Rightarrow> nat)) \<equiv> (\<forall>X \<subseteq> E. r X \<le> card X)"
abbreviation R2 where "R2 E (r::('a set \<Rightarrow> nat)) \<equiv> (\<forall>X \<subseteq> E. \<forall>Y \<subseteq> E. X \<subseteq> Y \<longrightarrow> r X \<le> r Y)"
abbreviation R3 where "R3 E (r::('a set \<Rightarrow> nat)) \<equiv> (\<forall>X \<subseteq> E. \<forall>Y \<subseteq> E. r (X \<union> Y) + r (X \<inter> Y) \<le> r X + r Y)"

abbreviation R1' where "R1' (r::('a set \<Rightarrow> nat)) \<equiv> (r {} = 0)"
abbreviation R2' where "R2' E (r::('a set \<Rightarrow> nat)) \<equiv>
  (\<forall>X \<subseteq> E. \<forall>y \<in> E. r X \<le> r (X \<union> {y}) \<and> r (X \<union> {y}) \<le> r X + 1)"
abbreviation R3' where "R3' E (r::('a set \<Rightarrow> nat)) \<equiv>
  (\<forall>X \<subseteq> E. \<forall>x \<in> E. \<forall>y \<in> E. (r (X \<union> {x}) = r X \<and> r (X \<union> {y}) = r X) \<longrightarrow> r (X \<union> {x, y}) = r X)"


subsubsection \<open>Auxiliary lemmas\<close>

lemma rank_axioms2_imp_rank_leq_card:
  assumes "finite E" "r {} = 0"
    "(\<forall>X \<subseteq> E. \<forall>y \<in> E. r X \<le> r (X \<union> {y}) \<and> r (X \<union> {y}) \<le> r X + 1)"
  shows "n = card X \<longrightarrow> X \<subseteq> E \<longrightarrow> r X \<le> card X"
proof (induction n arbitrary: X)
  case 0
  show ?case
  proof ((rule impI)+)
    assume "0 = card X" "X \<subseteq> E"
    from \<open>X \<subseteq> E\<close> assms(1) have "finite X" by (rule finite_subset)
    with \<open>0 = card X\<close> have "X = {}" by (simp add: card_eq_0_iff)
    with assms(2) show "r X \<le> card X" by simp
  qed
next
  case (Suc n)
  show ?case
  proof ((rule impI)+)
    assume "Suc n = card X" "X \<subseteq> E"
    then have "\<exists>X' y. y \<notin> X' \<and> X = (insert y X')"
      by (metis card_Suc_eq)
    then obtain X' y where "y \<notin> X'" "X = (insert y X')" by blast

    from \<open>X \<subseteq> E\<close> \<open>X = (insert y X')\<close> have "X' \<subseteq> E" by blast
    from \<open>X = (insert y X')\<close> \<open>X \<subseteq> E\<close> have "y \<in> E" by auto
    from \<open>X = (insert y X')\<close> \<open>y \<notin> X'\<close> \<open>Suc n = card X\<close> \<open>X' \<subseteq> E\<close>
    have "n = card X'" by (simp add: assms finite_subset)

    from `X = (insert y X')` have "r X = r (X' \<union> {y})" by auto
    also have "... \<le> r X' + 1" using assms(3) \<open>X' \<subseteq> E\<close> \<open>y \<in> E\<close> by auto
    also have "... \<le> card X' + 1" using Suc.IH \<open>n = card X'\<close> \<open>X' \<subseteq> E\<close> by simp
    also have "... = card X" using \<open>Suc n = card X\<close> \<open>n = card X'\<close> by presburger
    finally show "r X \<le> card X" .
  qed
qed

lemma prop_preserved_subset_induct:
  assumes "finite E" "\<forall>X \<subseteq> E. \<forall>Y \<subseteq> E. \<forall>y. y \<notin> X \<longrightarrow> Y = (insert y X) \<longrightarrow> P Y \<longrightarrow> P X" "Y \<subseteq> E"
  shows "n \<le> card Y \<longrightarrow> card X = (card Y - n) \<longrightarrow> X \<subseteq> Y \<longrightarrow> P Y \<longrightarrow> P X"
proof (induction n arbitrary: X)
  case 0
  show ?case
  proof ((rule impI)+)
    assume "card X = card Y - 0" "X \<subseteq> Y" "P Y"
    then have card_eq: "card X = card Y" by simp
    from assms(1) assms(3) have "finite Y" using finite_subset by blast
    from card_subset_eq[OF this \<open>X \<subseteq> Y\<close> card_eq] have "X = Y" .
    with \<open>P Y\<close> show "P X" by simp
  qed
next
  case (Suc n)
  show ?case
  proof ((rule impI)+)
    assume "Suc n \<le> card Y" "card X = card Y - Suc n" "X \<subseteq> Y" "P Y"

    have "\<exists>X' x. x \<notin> X \<and> X' = (insert x X) \<and> X' \<subseteq> Y"
    proof -
      have "finite Y" using assms(1) assms(3) finite_subset by blast
      have "finite X" using \<open>X \<subseteq> Y\<close> \<open>finite Y\<close> finite_subset by blast
      have "card X < card Y"
        using \<open>card X = card Y - Suc n\<close> \<open>Suc n \<le> card Y\<close> by arith
      have "Y - X \<noteq> {}"
      proof (rule ccontr)
        assume "\<not> (Y - X \<noteq> {})"
        then have "Y - X = {}" by simp
        then have "Y \<subseteq> X" by blast
        with \<open>X \<subseteq> Y\<close> have "X = Y" by simp
        with \<open>card X < card Y\<close> show False by simp
      qed
      then obtain x where "x \<in> Y - X" by blast
      then have "x \<notin> X" "x \<in> Y" by auto
      have "insert x X \<subseteq> Y" using \<open>x \<in> Y\<close> \<open>X \<subseteq> Y\<close> by blast
      with \<open>x \<notin> X\<close> show ?thesis by blast
    qed
    then obtain X' x where "x \<notin> X" "X' = (insert x X)" "X' \<subseteq> Y" by blast
    with \<open>card X = card Y - Suc n\<close>
    have "card X' = card Y - n"
      proof -
        from \<open>X \<subseteq> Y\<close> assms(3) have "X \<subseteq> E" by auto
        from this assms(1) have "finite X" by (rule finite_subset)
        from \<open>X' = insert x X\<close> \<open>x \<notin> X\<close> \<open>finite X\<close> have "card X' = card X + 1"
          by (simp add: card_insert_disjoint)
        also from \<open>card X = card Y - Suc n\<close> have "... = card Y - Suc n + 1" by simp
        also from \<open>Suc n \<le> card Y\<close> have "... = card Y - n" by arith
        finally show ?thesis .
      qed

    from \<open>Suc n \<le> card Y\<close> have "n \<le> card Y" by auto

    from Suc.IH this \<open>card X' = card Y - n\<close> \<open>X' \<subseteq> Y\<close> \<open>P Y\<close>
    have "P X'" by blast

    from assms(3) \<open>X' \<subseteq> Y\<close> have "X' \<subseteq> E" by blast
    from assms(3) \<open>X \<subseteq> Y\<close> have "X \<subseteq> E" by blast
    from \<open>X' = (insert x X)\<close> have "x \<in> X'" by blast

    from assms(2) \<open>X' \<subseteq> E\<close> \<open>X \<subseteq> E\<close> \<open>x \<notin> X\<close> \<open>X' = (insert x X)\<close> \<open>P X'\<close>
    show "P X" by blast
  qed
qed

lemma rank_axioms2_imp_rank_eq_subsets:
  assumes "finite E" "X \<subseteq> E" "Y \<subseteq> E"
    "\<forall>x \<in> X - Y. r (Y \<union> {x}) = r Y"
    "\<forall>X \<subseteq> E. \<forall>x \<in> E. \<forall>y \<in> E. (r (X \<union> {x}) = r X \<and> r (X \<union> {y}) = r X) \<longrightarrow> r (X \<union> {x, y}) = r X"
  shows "n = card A \<longrightarrow> A \<subseteq> X - Y \<longrightarrow> r (Y \<union> A) = r Y"
proof (induction n arbitrary: A rule: less_induct)
  case (less n)
  then show ?case
  proof (cases "n = 0", goal_cases Zero Pos)
    case Zero
    show ?thesis
    proof ((rule impI)+)
      assume "n = card A" "A \<subseteq> X - Y"
      with Zero show "r (Y \<union> A) = r Y"
      proof -
        have "card A = 0" using \<open>n = card A\<close> Zero by simp
        have "A \<subseteq> E" using \<open>A \<subseteq> X - Y\<close> assms(2) by blast
        then have "finite A" using assms(1) finite_subset by blast
        with \<open>card A = 0\<close> have "A = {}" by (simp add: card_eq_0_iff)
        then show "r (Y \<union> A) = r Y" by simp
      qed
    qed
  next
    case Pos
    show ?thesis
    proof ((rule impI)+)
      assume "n = card A" "A \<subseteq> X - Y"
      show "r (Y \<union> A) = r Y"
      proof (cases "n = 1")
        case True
        with \<open>n = card A\<close> assms(4) show ?thesis
        proof -
          from True \<open>n = card A\<close> have "card A = 1" by simp
          then obtain a where "A = {a}" by (rule card_1_singletonE)
          with \<open>A \<subseteq> X - Y\<close> have "a \<in> X - Y" by blast
          with assms(4) have "r (Y \<union> {a}) = r Y" by blast
          with \<open>A = {a}\<close> show "r (Y \<union> A) = r Y" by simp
        qed
      next
        case False
        with Pos have "n \<ge> 2" by auto
        with \<open>n = card A\<close> have "\<exists>x y. x \<in> A \<and> y \<in> A \<and> x \<noteq> y"
        proof -
          have A_subset_E: "A \<subseteq> E"
            using \<open>A \<subseteq> X - Y\<close> assms(2) by blast
          have finite_A: "finite A"
            using assms(1) A_subset_E finite_subset by blast
          have card_A_ge_2: "card A \<ge> 2"
            using \<open>n \<ge> 2\<close> \<open>n = card A\<close> by simp
          have not_subset_singleton: "\<not> (\<exists>a. A \<subseteq> {a})"
            using card_le_Suc0_iff_eq[OF finite_A] card_A_ge_2 by auto
          have "A \<noteq> {}"
          proof
            assume "A = {}"
            with card_A_ge_2 show False by simp
          qed
          then obtain x where x_in: "x \<in> A" by blast
          have "\<not> A \<subseteq> {x}"
            using not_subset_singleton by blast
          then obtain y where y_in: "y \<in> A" and y_neq: "y \<noteq> x"
            by blast
          from x_in y_in y_neq show "\<exists>x y. x \<in> A \<and> y \<in> A \<and> x \<noteq> y" by blast
        qed
        then obtain x y where "x \<in> A" "y \<in> A" "x \<noteq> y" by blast

        from \<open>n \<ge> 2\<close> have "n - 1 < n" by simp
        from \<open>n \<ge> 2\<close> have "n - 2 < n" by simp

        from \<open>x \<in> A\<close> \<open>y \<in> A\<close> \<open>x \<noteq> y\<close> \<open>n = card A\<close> have "n - 1 = card (A - {x})" by simp
        from \<open>A \<subseteq> X - Y\<close> have "(A - {x}) \<subseteq> X - Y" by blast
        from \<open>n - 1 < n\<close> \<open>n - 1 = card (A - {x})\<close> \<open>(A - {x}) \<subseteq> X - Y\<close> less.IH
        have "r (Y \<union> (A - {x})) = r Y" by blast
        then have r_A_sub_y: "r ((Y \<union> (A - {x, y})) \<union> {y}) = r Y"
        proof -
          have "(Y \<union> (A - {x, y})) \<union> {y} = Y \<union> (A - {x})"
            using \<open>x \<noteq> y\<close> \<open>y \<in> A\<close> by blast
          then show ?thesis using \<open>r (Y \<union> (A - {x})) = r Y\<close> by simp
        qed

        from \<open>x \<in> A\<close> \<open>y \<in> A\<close> \<open>x \<noteq> y\<close> \<open>n = card A\<close> have "n - 1 = card (A - {y})" by simp
        from \<open>A \<subseteq> X - Y\<close> have "(A - {y}) \<subseteq> X - Y" by blast
        from \<open>n - 1 < n\<close> \<open>n - 1 = card (A - {y})\<close> \<open>(A - {y}) \<subseteq> X - Y\<close> less.IH
        have "r (Y \<union> (A - {y})) = r Y" by blast
        then have r_A_sub_x: "r ((Y \<union> (A - {x, y})) \<union> {x}) = r Y"
        proof -
          have "(Y \<union> (A - {x, y})) \<union> {x} = Y \<union> (A - {y})"
            using \<open>x \<in> A\<close> \<open>x \<noteq> y\<close> by blast
          with \<open>r (Y \<union> (A - {y})) = r Y\<close> show ?thesis by simp
        qed

        from \<open>x \<in> A\<close> \<open>y \<in> A\<close> \<open>x \<noteq> y\<close> \<open>n = card A\<close> have "n - 2 = card (A - {x, y})" by simp
        from \<open>A \<subseteq> X - Y\<close> have "(A - {x, y}) \<subseteq> X - Y" by blast
        from \<open>n - 2 < n\<close> \<open>n - 2 = card (A - {x, y})\<close> \<open>(A - {x, y}) \<subseteq> X - Y\<close> less.IH
        have r_A_sub_x_y: "r (Y \<union> (A - {x, y})) = r Y" by blast

        from \<open>A \<subseteq> X - Y\<close> assms(2) assms(3) have "Y \<union> (A - {x, y}) \<subseteq> E" by blast
        from \<open>x \<in> A\<close> \<open>A \<subseteq> X - Y\<close> assms(2) have "x \<in> E" by blast
        from \<open>y \<in> A\<close> \<open>A \<subseteq> X - Y\<close> assms(2) have "y \<in> E" by blast

        from r_A_sub_y r_A_sub_x_y have 1: "r ((Y \<union> (A - {x, y})) \<union> {y}) = r (Y \<union> (A - {x, y}))"
          by auto
        from r_A_sub_x r_A_sub_x_y have 2: "r ((Y \<union> (A - {x, y})) \<union> {x}) = r (Y \<union> (A - {x, y}))"
          by auto

        from assms(5) \<open>Y \<union> (A - {x, y}) \<subseteq> E\<close> \<open>x \<in> E\<close> \<open>y \<in> E\<close> 1 2
        have "r ((Y \<union> (A - {x, y})) \<union> {x, y}) = r (Y \<union> (A - {x, y}))" by blast
        then have "r (Y \<union> A) = r (Y \<union> (A - {x, y}))"
        proof -
          assume rank_eq: "r ((Y \<union> (A - {x, y})) \<union> {x, y}) = r (Y \<union> (A - {x, y}))"
          have set_eq: "Y \<union> (A - {x, y}) \<union> {x, y} = Y \<union> A"
            using \<open>x \<in> A\<close> \<open>y \<in> A\<close> by blast
          from rank_eq[unfolded set_eq] show ?thesis .
        qed
        with r_A_sub_x_y
        show "r (Y \<union> A) = r Y" by auto
      qed
    qed
  qed
qed

lemma rank_axioms2_imp_subset_rank_leq:
  assumes "finite E" "Y \<subseteq> E" "\<forall>X \<subseteq> E. \<forall>y \<in> E. (r::('a set \<Rightarrow> nat)) X \<le> r (X \<union> {y})"
  shows "n \<le> card Y \<longrightarrow> card X = (card Y - n) \<longrightarrow> X \<subseteq> Y \<longrightarrow> r X \<le> r Y"
proof (induction n arbitrary: X)
  case 0
  show ?case
  proof ((rule impI)+)
    assume "card X = card Y - 0" "X \<subseteq> Y"
      have "card X = card Y" using \<open>card X = card Y - 0\<close> by simp
      moreover have "finite Y" using assms(1) assms(2) finite_subset by blast
      ultimately have "X = Y" using \<open>X \<subseteq> Y\<close> card_subset_eq by blast
      then show "r X \<le> r Y" by simp
  qed
next
  case (Suc n)
  show ?case
  proof ((rule impI)+)
    assume "Suc n \<le> card Y" "card X = card Y - Suc n" "X \<subseteq> Y"
    have "\<exists>X' x. x \<notin> X \<and> X' = (insert x X) \<and> X' \<subseteq> Y"
    proof -
      have "finite Y" using assms(1) assms(2) finite_subset by blast
      have "Suc n + (card Y - Suc n) = card Y"
        using \<open>Suc n \<le> card Y\<close> by (rule le_add_diff_inverse)
      with \<open>card X = card Y - Suc n\<close> have "Suc n + card X = card Y" by simp
      then have "card X < card Y" by simp
      have "\<exists>x. x \<in> Y \<and> x \<notin> X"
      proof (rule ccontr)
        assume "\<not> (\<exists>x. x \<in> Y \<and> x \<notin> X)"
        then have "Y \<subseteq> X" by blast
        from subset_antisym[OF \<open>X \<subseteq> Y\<close> this] have "X = Y" .
        with \<open>card X < card Y\<close> show False by simp
      qed
      then obtain x where "x \<in> Y" "x \<notin> X" by blast
      then have "insert x X \<subseteq> Y" using \<open>X \<subseteq> Y\<close> by auto
      with \<open>x \<notin> X\<close> show ?thesis by blast
    qed
    then obtain X' x where "x \<notin> X" "X' = (insert x X)" "X' \<subseteq> Y" by blast
    with \<open>card X = card Y - Suc n\<close>
    have "card X' = card Y - n"
    proof -
      have "X \<subseteq> E" using \<open>X \<subseteq> Y\<close> assms(2) by blast
      have "finite X" using assms(1) \<open>X \<subseteq> E\<close> finite_subset by blast
      have card_X'_eq: "card X' = card X + 1"
        using \<open>X' = (insert x X)\<close> \<open>x \<notin> X\<close> \<open>finite X\<close> by simp
      show "card X' = card Y - n"
        using card_X'_eq \<open>card X = card Y - Suc n\<close> \<open>Suc n \<le> card Y\<close> by arith
    qed

    from \<open>Suc n \<le> card Y\<close> have "n \<le> card Y" by auto

    from Suc.IH this \<open>card X' = card Y - n\<close> \<open>X' \<subseteq> Y\<close>
    have "r X' \<le> r Y" by blast

    from \<open>X' = (insert x X)\<close> assms(3)
    have "r X \<le> r X'"
    proof -
      from \<open>X' = (insert x X)\<close> \<open>X' \<subseteq> Y\<close> assms(2) have "X \<subseteq> E" by blast
      from \<open>X' = (insert x X)\<close> \<open>X' \<subseteq> Y\<close> assms(2) have "x \<in> E" by blast
      from assms(3) \<open>X \<subseteq> E\<close> \<open>x \<in> E\<close> have "r X \<le> r (X \<union> {x})" by blast
      with \<open>X' = (insert x X)\<close> show "r X \<le> r X'" by simp
    qed

    with \<open>r X' \<le> r Y\<close> show "r X \<le> r Y" by simp
  qed
qed


subsubsection \<open>Theorem statement\<close>

lemma matroid_imp_rank_axioms1:
  assumes "finite E"
    "(\<exists>indep. matroid E indep \<and> (\<forall>X \<subseteq> E. r X = matroid.rank_of indep X))"
  shows "((\<forall>X \<subseteq> E. r X \<le> card X) \<and>
    (\<forall>X \<subseteq> E. \<forall>Y \<subseteq> E. X \<subseteq> Y \<longrightarrow> r X \<le> r Y) \<and>
    (\<forall>X \<subseteq> E. \<forall>Y \<subseteq> E. r (X \<union> Y) + r (X \<inter> Y) \<le> r X + r Y))"
  using assms matroid.rank_of_le matroid.rank_of_mono matroid.rank_of_Un_Int_le 
proof-
  from assms(2) obtain indep where
    indep_matroid: "matroid E indep" and
    r_eq: "\<forall>X \<subseteq> E. r X = matroid.rank_of indep X"
    by blast

  have R1: "\<forall>X \<subseteq> E. r X \<le> card X"
  proof (rule allI, rule impI)
    fix X
    assume "X \<subseteq> E"
    from r_eq \<open>X \<subseteq> E\<close> have "r X = matroid.rank_of indep X" by blast
    also have "... \<le> card X"
      using matroid.rank_of_le[OF indep_matroid \<open>X \<subseteq> E\<close>] .
    finally show "r X \<le> card X" .
  qed

  have R2: "\<forall>X \<subseteq> E. \<forall>Y \<subseteq> E. X \<subseteq> Y \<longrightarrow> r X \<le> r Y"
  proof ((rule allI, rule impI)+, rule impI)
    fix X Y
    assume "X \<subseteq> E" "Y \<subseteq> E" "X \<subseteq> Y"
    from r_eq \<open>X \<subseteq> E\<close> have "r X = matroid.rank_of indep X" by blast
    also have "... \<le> matroid.rank_of indep Y"
      using matroid.rank_of_mono[OF indep_matroid \<open>X \<subseteq> Y\<close> \<open>Y \<subseteq> E\<close>] .
    also from r_eq \<open>Y \<subseteq> E\<close> have "... = r Y" by (simp add: r_eq)
    finally show "r X \<le> r Y" .
  qed

  have R3: "\<forall>X \<subseteq> E. \<forall>Y \<subseteq> E. r (X \<union> Y) + r (X \<inter> Y) \<le> r X + r Y"
  proof ((rule allI, rule impI)+)
    fix X Y
    assume "X \<subseteq> E" "Y \<subseteq> E"
    then have "X \<union> Y \<subseteq> E" by blast
    from \<open>X \<subseteq> E\<close> have "X \<inter> Y \<subseteq> E" by blast

    from r_eq \<open>X \<union> Y \<subseteq> E\<close> have r_un: "r (X \<union> Y) = matroid.rank_of indep (X \<union> Y)" by blast
    from r_eq \<open>X \<inter> Y \<subseteq> E\<close> have r_int: "r (X \<inter> Y) = matroid.rank_of indep (X \<inter> Y)" by blast
    from r_eq \<open>X \<subseteq> E\<close> have r_X: "r X = matroid.rank_of indep X" by blast
    from r_eq \<open>Y \<subseteq> E\<close> have r_Y: "r Y = matroid.rank_of indep Y" by blast

    from matroid.rank_of_Un_Int_le[OF indep_matroid \<open>X \<subseteq> E\<close> \<open>Y \<subseteq> E\<close>]
    have "matroid.rank_of indep (X \<union> Y) + matroid.rank_of indep (X \<inter> Y) \<le>
      matroid.rank_of indep X + matroid.rank_of indep Y" .

    with r_un r_int r_X r_Y show "r (X \<union> Y) + r (X \<inter> Y) \<le> r X + r Y" by simp
  qed

  from R1 R2 R3 show ?thesis by blast
qed

lemma rank_axioms1_imp_rank_axioms2:
  assumes "finite E"
    "((\<forall>X \<subseteq> E. r X \<le> card X) \<and>
    (\<forall>X \<subseteq> E. \<forall>Y \<subseteq> E. X \<subseteq> Y \<longrightarrow> r X \<le> r Y) \<and>
    (\<forall>X \<subseteq> E. \<forall>Y \<subseteq> E. r (X \<union> Y) + r (X \<inter> Y) \<le> r X + r Y))"
  shows "(r {} = 0 \<and>
    (\<forall>X \<subseteq> E. \<forall>y \<in> E. r X \<le> r (X \<union> {y}) \<and> r (X \<union> {y}) \<le> r X + 1) \<and>
    (\<forall>X \<subseteq> E. \<forall>x \<in> E. \<forall>y \<in> E. 
      (r (X \<union> {x}) = r X \<and> r (X \<union> {y}) = r X) \<longrightarrow> r (X \<union> {x, y}) = r X))"
proof-
  from assms(2) have R1: "\<forall>X \<subseteq> E. r X \<le> card X" by auto
  from assms(2) have R2: "\<forall>X \<subseteq> E. \<forall>Y \<subseteq> E. X \<subseteq> Y \<longrightarrow> r X \<le> r Y" by auto
  from assms(2) have R3: "\<forall>X \<subseteq> E. \<forall>Y \<subseteq> E. r (X \<union> Y) + r (X \<inter> Y) \<le> r X + r Y" by auto

  from R1 have R1': "r {} = 0" by fastforce

  from R2 have "\<forall>X \<subseteq> E. \<forall>y \<in> E. r X \<le> r (X \<union> {y})"
    by (simp add: subset_insertI)

  have "\<forall>X \<subseteq> E. \<forall>y \<in> E. r (X \<union> {y}) \<le> r X + 1"
  proof (rule allI, rule impI)
    fix X
    assume "X \<subseteq> E"
    show "\<forall>y \<in> E. r (X \<union> {y}) \<le> r X + 1"
    proof
      fix y
      assume "y \<in> E"

      have "r (X \<union> {y}) \<le> r X + r {y} - r (X \<inter> {y})" using \<open>X \<subseteq> E\<close> \<open>y \<in> E\<close>
        by (meson R3 add_le_imp_le_diff empty_subsetI insert_subset)
      also have "... \<le> r X + r {y}" by auto
      also have "... \<le> r X + 1"
        proof -
          have "{y} \<subseteq> E" using \<open>y \<in> E\<close> by simp
          then have "r {y} \<le> card {y}" using R1 by blast
          also have "card {y} = 1" by simp
          finally have "r {y} \<le> 1" .
          then show ?thesis by linarith
        qed
      finally show "r (X \<union> {y}) \<le> r X + 1" .
    qed
  qed

  from \<open>\<forall>X \<subseteq> E. \<forall>y \<in> E. r X \<le> r (X \<union> {y})\<close> \<open>\<forall>X \<subseteq> E. \<forall>y \<in> E. r (X \<union> {y}) \<le> r X + 1\<close>
  have R2': "\<forall>X \<subseteq> E. \<forall>y \<in> E. r X \<le> r (X \<union> {y}) \<and> r (X \<union> {y}) \<le> r X + 1" by auto

  have R3': "\<forall>X \<subseteq> E. \<forall>x \<in> E. \<forall>y \<in> E. 
    (r (X \<union> {x}) = r X \<and> r (X \<union> {y}) = r X) \<longrightarrow> r (X \<union> {x, y}) = r X"
  proof (rule allI, rule impI, (rule ballI)+, rule impI)
    fix X x y
    assume "X \<subseteq> E" "x \<in> E" "y \<in> E" "(r (X \<union> {x}) = r X \<and> r (X \<union> {y}) = r X)"
    show "r (X \<union> {x, y}) = r X"
    proof (cases "x = y")
      case True
      with \<open>(r (X \<union> {x}) = r X \<and> r (X \<union> {y}) = r X)\<close> show ?thesis by auto
    next
      case False

      have un_sets: "(X \<union> {x}) \<union> (X \<union> {y}) = (X \<union> {x, y})" by auto
      from False have int_sets: "(X \<union> {x}) \<inter> (X \<union> {y}) = X" by auto

      have "r X \<le> r (X \<union> {x, y})" using R2 \<open>X \<subseteq> E\<close> \<open>x \<in> E\<close> \<open>y \<in> E\<close>
      proof -
        have "X \<union> {x, y} \<subseteq> E" using \<open>X \<subseteq> E\<close> \<open>x \<in> E\<close> \<open>y \<in> E\<close> by blast
        moreover have "X \<subseteq> X \<union> {x, y}" by blast
        ultimately show ?thesis using R2 \<open>X \<subseteq> E\<close> by blast
      qed

      have "r X + r (X \<union> {x, y}) \<le> r (X \<union> {x}) + r (X \<union> {y})"
        using R3 \<open>X \<subseteq> E\<close> \<open>x \<in> E\<close> \<open>y \<in> E\<close> un_sets int_sets
      proof -
        from \<open>X \<subseteq> E\<close> \<open>x \<in> E\<close> have x_subset: "X \<union> {x} \<subseteq> E" by simp
        from \<open>X \<subseteq> E\<close> \<open>y \<in> E\<close> have y_subset: "X \<union> {y} \<subseteq> E" by simp
        from R3 x_subset y_subset
        have "r ((X \<union> {x}) \<union> (X \<union> {y})) + r ((X \<union> {x}) \<inter> (X \<union> {y})) \<le> r (X \<union> {x}) + r (X \<union> {y})"
          by blast
        with un_sets int_sets
        have "r (X \<union> {x, y}) + r X \<le> r (X \<union> {x}) + r (X \<union> {y})"
          by simp
        then show "r X + r (X \<union> {x, y}) \<le> r (X \<union> {x}) + r (X \<union> {y})"
          by (simp add: add.commute)
      qed
      also have "... \<le> r X + r X" using \<open>(r (X \<union> {x}) = r X \<and> r (X \<union> {y}) = r X)\<close> by auto
      finally have "r (X \<union> {x, y}) \<le> r X" by simp

      with \<open>r X \<le> r (X \<union> {x, y})\<close> show ?thesis by simp
    qed
  qed

  from R1' R2' R3' show ?thesis by blast
qed

lemma rank_axioms2_imp_matroid:
  assumes "finite E"
    "(r {} = 0 \<and>
    (\<forall>X \<subseteq> E. \<forall>y \<in> E. r X \<le> r (X \<union> {y}) \<and> r (X \<union> {y}) \<le> r X + 1) \<and>
    (\<forall>X \<subseteq> E. \<forall>x \<in> E. \<forall>y \<in> E. 
      (r (X \<union> {x}) = r X \<and> r (X \<union> {y}) = r X) \<longrightarrow> r (X \<union> {x, y}) = r X))"
  shows "(\<exists>indep. matroid E indep \<and> (\<forall>X \<subseteq> E. r X = matroid.rank_of indep X))"
proof-
  let ?indep = "(\<lambda> X. X \<subseteq> E \<and> r X = card X)"

  from assms(2) have R1': "r {} = 0" by blast
  from assms(2) have R2': "(\<forall>X \<subseteq> E. \<forall>y \<in> E. r(X) \<le> r(X \<union> {y}) \<and> r(X \<union> {y}) \<le> r(X) + 1)" by blast
  from assms(2) have R3': "(\<forall>X \<subseteq> E. \<forall>x \<in> E. \<forall>y \<in> E. 
    (r (X \<union> {x}) = r X \<and> r (X \<union> {y}) = r X) \<longrightarrow> r (X \<union> {x, y}) = r X)" by blast

  have indep_ex: "\<exists>X \<subseteq> E. r X = card X"
    using R1' by fastforce

  from rank_axioms2_imp_rank_leq_card[OF assms(1) R1' R2']
  have rank_leq_card: "\<forall>X \<subseteq> E. r X \<le> card X" by blast

  have "\<forall>X \<subseteq> E. \<forall>Y \<subseteq> E. \<forall>y. y \<notin> X \<longrightarrow> Y = (insert y X) \<longrightarrow> ?indep Y \<longrightarrow> ?indep X"
  proof ((rule allI, rule impI)+, (rule impI)+)
    fix X Y y
    assume "X \<subseteq> E" "Y \<subseteq> E" "y \<notin> X" "Y = insert y X" "?indep Y"

    from \<open>Y \<subseteq> E\<close> \<open>Y = insert y X\<close> have "y \<in> E" by blast

    have "card X + 1 = card Y" using \<open>Y = insert y X\<close>
    proof -
      from \<open>X \<subseteq> E\<close> assms(1) have "finite X" by (rule finite_subset)
      from this \<open>y \<notin> X\<close> have "card (insert y X) = Suc (card X)" by (rule card_insert_disjoint)
      then show "card X + 1 = card Y" using \<open>Y = insert y X\<close> by simp
    qed
    also have "... = r Y" using \<open>?indep Y\<close> by simp
    also have "... = r (X \<union> {y})" using \<open>Y = insert y X\<close> by auto
    also have "... \<le> r X + 1" using R2' \<open>X \<subseteq> E\<close> \<open>y \<in> E\<close> by simp
    finally have "card X + 1 \<le> r X + 1" .
    then have "r X \<ge> card X" by auto
    with rank_leq_card \<open>X \<subseteq> E\<close> have "r X = card X"
      using order_antisym_conv by auto
    with \<open>X \<subseteq> E\<close> show "?indep X" by blast
  qed

  from prop_preserved_subset_induct[OF assms(1) this]
  have indep_subset: "\<forall>X Y. X \<subseteq> Y \<longrightarrow> ?indep Y \<longrightarrow> ?indep X"
  proof (intro allI impI)
    fix X Y
    assume F: "\<And>Y n X. Y \<subseteq> E \<Longrightarrow> n \<le> card Y \<longrightarrow> card X = card Y - n \<longrightarrow> X \<subseteq> Y \<longrightarrow> ?indep Y \<longrightarrow> ?indep X"
    assume "X \<subseteq> Y" and indep_Y: "?indep Y"
    from indep_Y have Y_subset: "Y \<subseteq> E" by blast
    have Y_finite: "finite Y" using assms(1) Y_subset finite_subset by blast
    from card_mono[OF Y_finite \<open>X \<subseteq> Y\<close>] have card_le: "card X \<le> card Y" .
    have n_le: "card Y - card X \<le> card Y" by (rule diff_le_self)
    have card_eq: "card X = card Y - (card Y - card X)"
      using diff_diff_cancel[OF card_le] by simp
    show "?indep X"
      using F[of Y "card Y - card X" X] Y_subset n_le card_eq \<open>X \<subseteq> Y\<close> indep_Y by blast
  qed

  have augment_aux: 
    "\<forall>X Y. ?indep X \<longrightarrow> ?indep Y \<longrightarrow> card X = Suc (card Y) \<longrightarrow> (\<exists>x \<in> X - Y. ?indep (insert x Y))" 
  proof ((rule allI)+, (rule impI)+)
    fix X Y
    assume "?indep X" "?indep Y" "card X = Suc (card Y)"
    show "\<exists>x \<in> X - Y. ?indep (insert x Y)"
    proof (rule ccontr, goal_cases False)
      case False
      then have "\<forall>x \<in> X - Y. \<not>?indep (insert x Y)" by blast
      with \<open>?indep X\<close> \<open>?indep Y\<close>
      have "\<forall>x \<in> X - Y. \<not>(r (insert x Y) = card (insert x Y))"
        by blast
      with rank_leq_card \<open>?indep X\<close> \<open>?indep Y\<close>
      have "\<forall>x \<in> X - Y. r (insert x Y) < card (insert x Y)"
        by (metis DiffD1 in_mono insert_subsetI order_less_le)
      then have "\<forall>x \<in> X - Y. r (insert x Y) < card Y + 1"
        proof (intro ballI)
          fix x
          assume "x \<in> X - Y"

          have lt: "r (insert x Y) < card (insert x Y)"
            using \<open>\<forall>x \<in> X - Y. r (insert x Y) < card (insert x Y)\<close> \<open>x \<in> X - Y\<close> by blast

          from \<open>?indep Y\<close> have "Y \<subseteq> E" by blast
          with assms(1) have fin: "finite Y" using finite_subset by blast
          from \<open>x \<in> X - Y\<close> have notin: "x \<notin> Y" by blast

          have "card (insert x Y) = card Y + 1"
            using card_insert_disjoint[OF fin notin] by simp

          with lt show "r (insert x Y) < card Y + 1" by simp
        qed      then have "\<forall>x \<in> X - Y. r (insert x Y) \<le> card Y"
        by force

      have "\<forall>x \<in> X - Y. r (insert x Y) \<ge> card Y"
      proof (rule ballI)
        fix x
        assume "x \<in> X - Y"
        from \<open>x \<in> X - Y\<close> \<open>?indep X\<close> have "x \<in> E" by blast
        from \<open>?indep Y\<close> have "Y \<subseteq> E" and rY_eq: "r Y = card Y" by blast+
        from R2' \<open>Y \<subseteq> E\<close> \<open>x \<in> E\<close> have "r Y \<le> r (Y \<union> {x})" by blast
        then show "r (insert x Y) \<ge> card Y" using rY_eq by simp
      qed
      with \<open>\<forall>x \<in> X - Y. r (insert x Y) \<le> card Y\<close>
      have "\<forall>x \<in> X - Y. r (insert x Y) = card Y" by force
      with \<open>?indep Y\<close>
      have rank_Y_un_x_eq_Y: "\<forall>x \<in> X - Y. r (Y \<union> {x}) = r Y" by simp

      from \<open>?indep X\<close> have "X \<subseteq> E" by blast
      from \<open>?indep Y\<close> have "Y \<subseteq> E" by blast

      have subset_rank_leq: "\<forall>X. \<forall>Y. Y \<subseteq> E \<longrightarrow> X \<subseteq> Y \<longrightarrow> r X \<le> r Y"
      proof ((rule allI)+, (rule impI)+)
        fix X Y
        assume "Y \<subseteq> E" "X \<subseteq> Y" 

        let ?n = "card Y - card X"
        have "?n \<le> card Y" by auto
        have "card X = card Y - ?n" 
        proof -
          have "finite Y" using assms(1) \<open>Y \<subseteq> E\<close> by (rule rev_finite_subset)
          from card_mono[OF this \<open>X \<subseteq> Y\<close>] have le: "card X \<le> card Y" .
          show ?thesis by (rule diff_diff_cancel[OF le, symmetric])
        qed

        from R2' have R2'_part: "\<forall>X\<subseteq>E. \<forall>y\<in>E. r X \<le> r (X \<union> {y})" by auto

        from rank_axioms2_imp_subset_rank_leq[OF assms(1) \<open>Y \<subseteq> E\<close> R2'_part]
          \<open>?n \<le> card Y\<close> \<open>card X = card Y - ?n\<close> \<open>X \<subseteq> Y\<close>
        show "r X \<le> r Y" by blast
      qed

      from rank_axioms2_imp_rank_eq_subsets[OF assms(1) \<open>X \<subseteq> E\<close> \<open>Y \<subseteq> E\<close> rank_Y_un_x_eq_Y R3',
          of "card (X - Y)" "X - Y"]
      have "r Y = r (Y \<union> (X - Y))"
        by simp
      also have "... = r (X \<union> Y)" by (simp add: Un_commute)
      also have "... \<ge> r X" using subset_rank_leq \<open>X \<subseteq> E\<close> \<open>Y \<subseteq> E\<close> by auto
      finally have "r Y \<ge> r X" .

      with \<open>?indep X\<close> \<open>?indep Y\<close> have "card Y \<ge> card X" by simp
      with \<open>card X = Suc (card Y)\<close> show ?case by auto
    qed
  qed

  have matroid_props: "matroid E (\<lambda> X. X \<subseteq> E \<and> r X = card X)"
    apply(unfold_locales)
    using assms(1) apply simp
    apply simp  
    using indep_ex apply simp
    using indep_subset apply simp
    using augment_aux apply simp
    done

  from matroid_props
  have indep_sys_props: "indep_system E (\<lambda> X. X \<subseteq> E \<and> r X = card X)"
    using matroid.axioms(1) by blast

  have r_rank_of_matroid: 
    "(\<forall>X \<subseteq> E. r(X) = matroid.rank_of (\<lambda> X. X \<subseteq> E \<and> r X = card X) X)"
  proof (rule allI, rule impI)
    fix X
    assume "X \<subseteq> E"

    have "\<exists>Y. indep_system.basis_in ?indep X Y"
      using indep_system.basis_in_ex[OF indep_sys_props \<open>X \<subseteq> E\<close>] by blast
    then obtain Y where Y_basis_in: "indep_system.basis_in ?indep X Y" by blast

    from indep_system.basis_in_subset_carrier[OF indep_sys_props \<open>X \<subseteq> E\<close> Y_basis_in]
    have "Y \<subseteq> X" .
    with \<open>X \<subseteq> E\<close> subset_trans have "Y \<subseteq> E" by blast

    from indep_system.basis_in_indep_in[OF indep_sys_props \<open>X \<subseteq> E\<close> Y_basis_in]
    have "r Y = card Y"
      using indep_sys_props indep_system.indep_in_indep by blast

    from Y_basis_in have "\<forall>x \<in> X - Y. \<not>(?indep (insert x Y))"
      using indep_system.basis_in_def[OF indep_sys_props] indep_system.basis_def[OF indep_sys_props]
    proof (rule_tac ballI)
      fix x
      assume "x \<in> X - Y"
      then have "x \<in> X" by blast
      with \<open>Y \<subseteq> X\<close> have subset: "insert x Y \<subseteq> X" by blast

      from indep_system.basis_in_max_indep_in[OF indep_sys_props \<open>X \<subseteq> E\<close> Y_basis_in]
      have "\<not> indep_system.indep_in ?indep X (insert x Y)"
        using \<open>x \<in> X - Y\<close> by blast

      show "\<not> ?indep (insert x Y)"
      proof
        assume "?indep (insert x Y)"
        with subset have "indep_system.indep_in ?indep X (insert x Y)"
          using indep_system.indep_in_def[OF indep_sys_props] by blast
        with \<open>\<not> indep_system.indep_in ?indep X (insert x Y)\<close> show False by blast
      qed
    qed

    with \<open>X \<subseteq> E\<close> \<open>Y \<subseteq> X\<close>
    have "\<forall>x \<in> X - Y. (r (insert x Y) \<noteq> card (insert x Y))"
      by blast
    with rank_leq_card \<open>X \<subseteq> E\<close> \<open>Y \<subseteq> X\<close>
    have "\<forall>x \<in> X - Y. (r (insert x Y) < card (insert x Y))"
      by (metis Diff_iff dual_order.trans insert_subsetI order_less_le)
    then have "\<forall>x \<in> X - Y. (r (insert x Y) < card Y + 1)"
      using \<open>Y \<subseteq> E\<close> assms(1) finite_subset by fastforce
    then have "\<forall>x \<in> X - Y. (r (Y \<union> {x}) \<le> card Y)" by force
    with \<open>r Y = card Y\<close>
    have "\<forall>x \<in> X - Y. (r (Y \<union> {x}) \<le> r Y)" by auto
    with R2' \<open>X \<subseteq> E\<close> \<open>Y \<subseteq> X\<close>
    have "\<forall>x \<in> X - Y. (r (Y \<union> {x}) = r Y)"
      by (meson DiffD1 dual_order.eq_iff subsetD subset_trans)

    from rank_axioms2_imp_rank_eq_subsets[OF assms(1) \<open>X \<subseteq> E\<close> \<open>Y \<subseteq> E\<close> this R3']
    have "r (Y \<union> X) = r Y"
    proof -
      assume fact2: "\<And>n A. n = card A \<longrightarrow> A \<subseteq> X - Y \<longrightarrow> r (Y \<union> A) = r Y"
      have "r (Y \<union> (X - Y)) = r Y"
        using fact2[of "card (X - Y)" "X - Y"] by simp
      hence "r (Y \<union> X) = r Y" by (simp add: Un_Diff_cancel)
      thus ?thesis .
    qed
    with \<open>Y \<subseteq> X\<close>
    have "r X = r Y"
      by (simp add: sup.absorb_iff2)
    with \<open>r Y = card Y\<close>
    have "r X = card Y" by simp

    have "matroid.rank_of ?indep X = Min {card B | B. indep_system.basis_in ?indep X B}"
      using matroid.rank_of_def[OF matroid_props] by auto
    also have "... = card Y"
    proof -
      have "matroid.rank_of (\<lambda>X. X \<subseteq> E \<and> r X = card X) X = card Y"
        using matroid.rank_of_eq_card_basis_in[OF matroid_props \<open>X \<subseteq> E\<close> Y_basis_in] .
      from calculation[symmetric] this show ?thesis by (rule trans)
    qed
    also have "... = r X"
      using \<open>r X = card Y\<close> by simp
    finally show "r X = matroid.rank_of (\<lambda> X. X \<subseteq> E \<and> r X = card X) X" by auto
  qed

  from matroid_props r_rank_of_matroid
  show "\<exists>indep. matroid E indep \<and> (\<forall>X \<subseteq> E. r X = matroid.rank_of indep X)" by blast
qed

lemma matroid_iff_rank_axioms1:
  assumes "finite E"
  shows "(\<exists>indep. matroid E indep \<and> (\<forall>X \<subseteq> E. r X = matroid.rank_of indep X)) \<longleftrightarrow>
    (R1 E r \<and> R2 E r \<and> R3 E r)"
proof
  assume "\<exists>indep. matroid E indep \<and> (\<forall>X \<subseteq> E. r X = matroid.rank_of indep X)"
  from matroid_imp_rank_axioms1[OF assms this]
  show "R1 E r \<and> R2 E r \<and> R3 E r" by blast
next
  assume "R1 E r \<and> R2 E r \<and> R3 E r"
  from rank_axioms1_imp_rank_axioms2[OF assms this]
  have "R1' r \<and> R2' E r \<and> R3' E r" by blast
  from rank_axioms2_imp_matroid[OF assms this]
  show "\<exists>indep. matroid E indep \<and> (\<forall>X \<subseteq> E. r X = matroid.rank_of indep X)" by simp
qed

lemma matroid_iff_rank_axioms2:
  assumes "finite E"
  shows "(\<exists>indep. matroid E indep \<and> (\<forall>X \<subseteq> E. r X = matroid.rank_of indep X)) \<longleftrightarrow>
    (R1' r \<and> R2' E r \<and> R3' E r)"
proof
  assume "\<exists>indep. matroid E indep \<and> (\<forall>X \<subseteq> E. r X = matroid.rank_of indep X)"
  from matroid_imp_rank_axioms1[OF assms this]
  have "R1 E r \<and> R2 E r \<and> R3 E r" by blast
  from rank_axioms1_imp_rank_axioms2[OF assms this]
  show "R1' r \<and> R2' E r \<and> R3' E r" by blast
next
  assume "R1' r \<and> R2' E r \<and> R3' E r"
  from rank_axioms2_imp_matroid[OF assms this]
  show "\<exists>indep. matroid E indep \<and> (\<forall>X \<subseteq> E. r X = matroid.rank_of indep X)" by simp
qed

lemma matroid_indep_expr_rank:
  assumes "matroid E indep"
  shows "indep = (\<lambda>X. X \<subseteq> E \<and> matroid.rank_of indep X = card X)"
proof (rule HOL.ext)
  fix X
  show "indep X = (X \<subseteq> E \<and> matroid.rank_of indep X = card X)"
  proof (cases "X \<subseteq> E")
    case True
    from matroid.indep_iff_rank_of[OF assms True] True
    show ?thesis by blast
  next
    case False
    from matroid.axioms(1)[OF assms] have "indep_system E indep" .
    from indep_system.indep_subset_carrier[OF \<open>indep_system E indep\<close>]
    have "\<forall>X. \<not>(X \<subseteq> E) \<longrightarrow> \<not>(indep X)" by blast
    with False show ?thesis by simp
  qed
qed


subsection \<open>Theorem 13.12\<close>

subsubsection \<open>Auxiliary lemmas\<close>

context indep_system
begin

lemma circuit_in_imp_circuit:
  assumes "X \<subseteq> carrier"
  shows "circuit_in X C \<Longrightarrow> circuit C"
  by (meson assms circuit_def circuit_in_dep_in circuit_in_subset_carrier dual_order.trans
      indep_in_def indep_system.circuit_in_min_dep_in indep_system_axioms)

lemma min_dep_imp_supset_circuit:
  assumes "indep X"
  assumes "circuit C"
  assumes "C \<subseteq> insert x X"
  shows "x \<in> C"
proof (rule ccontr)
  assume "x \<notin> C"
  then have "C \<subseteq> X" using assms by auto
  then have "indep C" using assms indep_subset by auto
  then show False using assms circuitD by auto
qed


end

context matroid
begin

lemma rank_of_eq_basis_subset:
  assumes "Y \<subseteq> carrier" "X \<subseteq> Y" "basis_in X B" "rank_of X = rank_of Y"
  shows "basis_in Y B"
proof -
  have X_carrier: "X \<subseteq> carrier" using assms(1) assms(2) by blast
  have B_subset_X: "B \<subseteq> X" using basis_in_subset_carrier[OF X_carrier assms(3)] .
  have B_subset_Y: "B \<subseteq> Y" using B_subset_X assms(2) by blast
  have rank_B: "rank_of B = rank_of X"
    using basis_in_iff_rank_of[OF X_carrier B_subset_X] assms(3) by blast
  have card_B: "rank_of B = card B"
    using basis_in_iff_rank_of[OF X_carrier B_subset_X] assms(3) by blast
  have "rank_of B = rank_of Y" using rank_B assms(4) by simp
  thus "basis_in Y B"
    using card_B basis_in_iff_rank_of[OF assms(1) B_subset_Y] by blast
qed

lemma rank_of_circuit:
  assumes "circuit X"
  shows "rank_of X = card X - 1"
proof -
  have X_carrier: "X \<subseteq> carrier" using assms unfolding circuit_def by blast
  have X_dep: "\<not> indep X" using assms unfolding circuit_def by blast
  have X_minus: "\<And>x. x \<in> X \<Longrightarrow> indep (X - {x})"
    using assms unfolding circuit_def by blast
  have X_nonempty: "X \<noteq> {}" using X_dep indep_empty by blast
  obtain x where x_in: "x \<in> X" using X_nonempty by blast
  have indep_X_minus_x: "indep (X - {x})" using X_minus x_in by blast
  have subset_X: "X - {x} \<subseteq> X" by blast
  have indep_in_X_minus_x: "indep_in X (X - {x})"
    using subset_X indep_X_minus_x unfolding indep_in_def by blast
  have insert_eq: "insert x (X - {x}) = X" using x_in by blast
  have basis_X_minus_x: "basis_in X (X - {x})"
  proof (rule basis_inI[OF X_carrier])
    show "indep_in X (X - {x})" using indep_in_X_minus_x .
  next
    fix y assume y_mem: "y \<in> X - (X - {x})"
    have y_eq: "y = x" using y_mem x_in by blast
    have not_indep_in_XX: "\<not> indep_in X X" using X_dep unfolding indep_in_def by blast
    show "\<not> indep_in X (insert y (X - {x}))"
      using y_eq insert_eq not_indep_in_XX by simp
  qed
  have rank_eq: "rank_of X = card (X - {x})"
    using rank_of_eq_card_basis_in[OF X_carrier basis_X_minus_x] .
  have finite_X: "finite X" using finite_subset[OF X_carrier carrier_finite] .
  have card_eq: "card (X - {x}) = card X - 1"
    using card_Diff_singleton[OF x_in] .
  from rank_eq card_eq show ?thesis by simp
qed

end


subsubsection \<open>Theorem statement\<close>

lemma indep_system_iff_C1_C2:
  assumes "finite E" "\<C> \<subseteq> Pow E"
  shows "(\<exists>indep. indep_system E indep \<and> \<C> = {C. (indep_system.circuit E indep C)}) \<longleftrightarrow> 
        ({} \<notin> \<C> \<and> (\<forall>C1 C2. C1 \<in> \<C> \<longrightarrow> C2 \<in> \<C> \<longrightarrow> C1 \<subseteq> C2 \<longrightarrow> C1 = C2))"
proof
  assume assm: "\<exists>indep. indep_system E indep \<and> \<C> = {C. indep_system.circuit E indep C}"
  then obtain indep where "indep_system E indep" "\<C> = {C. indep_system.circuit E indep C}" by blast

  from indep_system.circuit_nonempty[OF \<open>indep_system E indep\<close>] 
    \<open>\<C> = {C. indep_system.circuit E indep C}\<close>
  have C1: "{} \<notin> \<C>" by blast

  from indep_system.circuit_subset_eq[OF \<open>indep_system E indep\<close>]
    \<open>\<C> = {C. indep_system.circuit E indep C}\<close>
  have C2: "(\<forall>C1 C2. C1 \<in> \<C> \<longrightarrow> C2 \<in> \<C> \<longrightarrow> C1 \<subseteq> C2 \<longrightarrow> C1 = C2)" by simp

  from C1 C2 show "{} \<notin> \<C> \<and> (\<forall>C1 C2. C1 \<in> \<C> \<longrightarrow> C2 \<in> \<C> \<longrightarrow> C1 \<subseteq> C2 \<longrightarrow> C1 = C2)" by blast
next
  assume assm: "{} \<notin> \<C> \<and> (\<forall>C1 C2. C1 \<in> \<C> \<longrightarrow> C2 \<in> \<C> \<longrightarrow> C1 \<subseteq> C2 \<longrightarrow> C1 = C2)"
  from assm have C1: "{} \<notin> \<C>" by blast
  from assm have C2: "(\<forall>C1 C2. C1 \<in> \<C> \<longrightarrow> C2 \<in> \<C> \<longrightarrow> C1 \<subseteq> C2 \<longrightarrow> C1 = C2)" by blast

  let ?indep = "\<lambda>X. X \<subseteq> E \<and> \<not>(\<exists>C \<in> \<C>. C \<subseteq> X)"

  have indep_ex: "\<exists>X. ?indep X"
  proof (rule ccontr, goal_cases False)
    case False
    then have "\<forall>X \<subseteq> E. (\<exists>C \<in> \<C>. C \<subseteq> X)" by blast
    then have "\<exists>C \<in> \<C>. C \<subseteq> {}" by blast
    then have "{} \<in> \<C>" by auto
    with C1 show ?case by simp
  qed

  have indep_sys: "indep_system E ?indep"
    apply (unfold_locales)
    subgoal using assms(1) .
    subgoal by blast
    subgoal using indep_ex by blast
    subgoal by blast
    done

  have "\<forall>C. C \<in> \<C> = indep_system.circuit E ?indep C"
  proof (rule allI, rule iffI)
    fix C
    assume "C \<in> \<C>"
    from \<open>C \<in> \<C>\<close> assms(2) have "C \<subseteq> E" by blast

    from \<open>C \<in> \<C>\<close> have "(\<exists>C' \<in> \<C>. C' \<subseteq> C)" by blast
    then have "\<not> ?indep C" by blast

    have "\<forall>x \<in> C. \<not>(\<exists>C' \<in> \<C>. C' \<subseteq> (C - {x}))"
    proof (rule ballI, rule ccontr)
      fix x
      assume "x \<in> C"
      assume "\<not>(\<not>(\<exists>C' \<in> \<C>. C' \<subseteq> (C - {x})))"
      then have "(\<exists>C' \<in> \<C>. C' \<subseteq> (C - {x}))" by blast
      then obtain C' where "C' \<in> \<C>" "C' \<subseteq> (C - {x})" by blast
      then have "C' \<subseteq> C" by blast

      from C2 \<open>C' \<in> \<C>\<close> \<open>C \<in> \<C>\<close> \<open>C' \<subseteq> C\<close>
      have "C' = C" by blast

      with \<open>C' \<subseteq> (C - {x})\<close> \<open>x \<in> C\<close> show "False" by blast
    qed
    with \<open>C \<subseteq> E\<close> have "\<forall>x \<in> C. ((C - {x}) \<subseteq> E \<and> \<not>(\<exists>C' \<in> \<C>. C' \<subseteq> (C - {x})))" by blast
    then have "\<forall>x \<in> C. (?indep (C - {x}))" by blast

    from \<open>C \<subseteq> E\<close> \<open>\<not> ?indep C\<close> \<open>\<forall>x \<in> C. (?indep (C - {x}))\<close> indep_system.circuit_def[OF indep_sys]
    show "indep_system.circuit E ?indep C" by simp
  next
    fix C
    assume "indep_system.circuit E ?indep C"
    then have "(C \<subseteq> E \<and> \<not> (C \<subseteq> E \<and> \<not> (\<exists>C' \<in> \<C>. C' \<subseteq> C)) \<and> 
      (\<forall>x \<in> C. C - {x} \<subseteq> E \<and> \<not> (\<exists>C' \<in> \<C>. C' \<subseteq> C - {x})))"
      using indep_system.circuit_def[OF indep_sys] by auto
    then have "(C \<subseteq> E \<and> (\<exists>C' \<in> \<C>. C' \<subseteq> C) \<and> 
      (\<forall>x \<in> C. C - {x} \<subseteq> E \<and> \<not> (\<exists>C' \<in> \<C>. C' \<subseteq> C - {x})))"
      by blast
    then have "(C \<subseteq> E \<and> (\<exists>C' \<in> \<C>. C' \<subseteq> C) \<and> 
      (\<forall>x \<in> C. C - {x} \<subseteq> E \<and> (\<forall>C' \<subseteq> C - {x}. C' \<notin> \<C>)))"
      by blast
    then have "(C \<subseteq> E \<and> (\<exists>C' \<in> \<C>. C' \<subseteq> C) \<and> 
      (\<forall>C' \<subset> C. C' \<notin> \<C>))"
      by blast
    then show "C \<in> \<C>" by blast
  qed
  then have "\<C> = {C. indep_system.circuit E ?indep C}" by blast

  with indep_sys 
  show "\<exists>indep. indep_system E indep \<and> \<C> = {C. indep_system.circuit E indep C}" by blast
qed

lemma indep_system_indep_expr_circuits:
  assumes "indep_system E indep"
  shows "indep = (\<lambda>X. X \<subseteq> E \<and> \<not>(\<exists>C. indep_system.circuit E indep C \<and> C \<subseteq> X))"
proof (rule HOL.ext)
  fix X
  show "indep X = (X \<subseteq> E \<and>  \<not>(\<exists>C. indep_system.circuit E indep C \<and> C \<subseteq> X))"
  proof (cases "X \<subseteq> E")
    case True
    from indep_system.dep_iff_supset_circuit[OF assms True] True
    show ?thesis by blast
  next
    case False
    from indep_system.indep_subset_carrier[OF assms]
    have "\<forall>X. \<not>(X \<subseteq> E) \<longrightarrow> \<not>(indep X)" by blast
    with False show ?thesis by simp
  qed
qed



lemma matroid_imp_C3':
  assumes "matroid E indep" "\<C> = {C. (indep_system.circuit E indep C)}"
  shows "\<forall>C1 \<in> \<C>. \<forall>C2 \<in> \<C>. \<forall>e \<in> C1 \<inter> C2. \<forall>f \<in> C1 - C2. (\<exists>C3 \<in> \<C>. f \<in> C3 \<and> C3 \<subseteq> (C1 \<union> C2) - {e})"
proof (rule ballI, rule ballI, rule ballI, rule ballI)
  fix C1 C2 e f
  assume "C1 \<in> \<C>" "C2 \<in> \<C>" "e \<in> C1 \<inter> C2" "f \<in> C1 - C2"
  from matroid.axioms(1)[OF assms(1)] have indep_sys: "indep_system E indep" .
  have "finite E" using indep_system.carrier_finite[OF indep_sys] .

  from \<open>C1 \<in> \<C>\<close> assms(2) have C1_circuit:"indep_system.circuit E indep C1" by blast
  from \<open>C2 \<in> \<C>\<close> assms(2) have C2_circuit: "indep_system.circuit E indep C2" by blast
  from indep_system.circuit_subset_carrier[OF indep_sys C1_circuit] have "C1 \<subseteq> E" .
  from indep_system.circuit_subset_carrier[OF indep_sys C2_circuit] have "C2 \<subseteq> E" .
  from \<open>C1 \<subseteq> E\<close> \<open>finite E\<close> finite_subset
  have "finite C1" by blast
  from \<open>C2 \<subseteq> E\<close> \<open>finite E\<close> finite_subset
  have "finite C2" by blast

  from indep_system.circuit_nonempty[OF indep_sys C1_circuit] \<open>finite C1\<close>
  have "card C1 \<ge> 1" by (simp add: Suc_leI card_gt_0_iff)
  from indep_system.circuit_nonempty[OF indep_sys C2_circuit] \<open>finite C2\<close>
  have "card C2 \<ge> 1" by (simp add: Suc_leI card_gt_0_iff)

  from \<open>e \<in> C1 \<inter> C2\<close> \<open>f \<in> C1 - C2\<close> \<open>C1 \<subseteq> E\<close> \<open>C2 \<subseteq> E\<close> have "(C1 \<union> C2 - {e, f}) \<subseteq> E" by blast
  from \<open>e \<in> C1 \<inter> C2\<close> \<open>f \<in> C1 - C2\<close> have union1: "(C1 \<union> C2 - {e, f}) \<union> C2 = C1 \<union> C2 - {f}"
    by blast
  from \<open>e \<in> C1 \<inter> C2\<close> \<open>f \<in> C1 - C2\<close> have inter1: "(C1 \<union> C2 - {e, f}) \<inter> C2 = C2 - {e}"
    by blast

  from \<open>f \<in> C1 - C2\<close> \<open>C1 \<subseteq> E\<close> \<open>C2 \<subseteq> E\<close> have "(C1 \<union> C2 - {f}) \<subseteq> E" by blast
  from \<open>f \<in> C1 - C2\<close> have union2: "C1 \<union> (C1 \<union> C2 - {f}) = C1 \<union> C2"
    by blast
  from \<open>e \<in> C1 \<inter> C2\<close> \<open>f \<in> C1 - C2\<close> have inter2: "C1 \<inter> (C1 \<union> C2 - {f}) = C1 - {f}"
    by blast

  from \<open>C1 \<subseteq> E\<close> \<open>f \<in> C1 - C2\<close> have "(C1 - {f}) \<subseteq> E" by blast
  from indep_system.circuit_def[OF indep_sys] C1_circuit \<open>f \<in> C1 - C2\<close>
  have "indep (C1 - {f})" by blast
  with matroid.indep_iff_rank_of[OF assms(1) \<open>(C1 - {f}) \<subseteq> E\<close>] \<open>f \<in> C1 - C2\<close>
  have C1_minus_f_rank: "matroid.rank_of indep (C1 - {f}) = card C1 - 1"
  proof -
    have "matroid.rank_of indep (C1 - {f}) = card (C1 - {f})"
      using \<open>indep (C1 - {f})\<close> matroid.indep_iff_rank_of[OF assms(1) \<open>(C1 - {f}) \<subseteq> E\<close>] by blast
    moreover have "f \<in> C1" using \<open>f \<in> C1 - C2\<close> by (rule DiffD1)
    ultimately show ?thesis by (simp add: card_Diff_singleton)
  qed

  from \<open>C2 \<subseteq> E\<close> \<open>e \<in> C1 \<inter> C2\<close> have "(C2 - {e}) \<subseteq> E" by blast
  from indep_system.circuit_def[OF indep_sys] C2_circuit \<open>e \<in> C1 \<inter> C2\<close>
  have "indep (C2 - {e})" by blast
  with matroid.indep_iff_rank_of[OF assms(1) \<open>(C2 - {e}) \<subseteq> E\<close>] \<open>e \<in> C1 \<inter> C2\<close>
  have C2_minus_e_rank: "matroid.rank_of indep (C2 - {e}) = card C2 - 1"
  proof -
    from \<open>e \<in> C1 \<inter> C2\<close> have "e \<in> C2" by (rule IntD2)
    then have "card (C2 - {e}) = card C2 - 1" by (rule card_Diff_singleton)
    with matroid.indep_iff_rank_of[OF assms(1) \<open>(C2 - {e}) \<subseteq> E\<close>] \<open>indep (C2 - {e})\<close>
    show "matroid.rank_of indep (C2 - {e}) = card C2 - 1" by simp
  qed

  have 1: "card C1 - 1 + matroid.rank_of indep (C1 \<union> C2 - {e, f}) + card C2 - 1 =
    matroid.rank_of indep C1 + matroid.rank_of indep (C1 \<union> C2 - {e, f}) + matroid.rank_of indep C2"
    using matroid.rank_of_circuit[OF assms(1) C1_circuit] matroid.rank_of_circuit[OF assms(1) C2_circuit]
      \<open>card C1 \<ge> 1\<close> \<open>card C2 \<ge> 1\<close> by auto

  have 2: "matroid.rank_of indep C1 + matroid.rank_of indep (C1 \<union> C2 - {e, f}) + matroid.rank_of indep C2 \<ge>
    matroid.rank_of indep C1 + matroid.rank_of indep (C1 \<union> C2 - {f}) + matroid.rank_of indep (C2 - {e})"
    using matroid.rank_of_Un_Int_le[OF assms(1) \<open>(C1 \<union> C2 - {e, f}) \<subseteq> E\<close> \<open>C2 \<subseteq> E\<close>] union1 inter1
    by simp
  have
    3: "matroid.rank_of indep C1 + matroid.rank_of indep (C1 \<union> C2 - {f}) + matroid.rank_of indep (C2 - {e}) \<ge>
    matroid.rank_of indep (C1 - {f}) + matroid.rank_of indep (C1 \<union> C2) + matroid.rank_of indep (C2 - {e})"
    using matroid.rank_of_Un_Int_le[OF assms(1) \<open>C1 \<subseteq> E\<close> \<open>(C1 \<union> C2 - {f}) \<subseteq> E\<close>] union2 inter2
    by simp
  from 2 3 have
    4: "matroid.rank_of indep C1 + matroid.rank_of indep (C1 \<union> C2 - {e, f}) + matroid.rank_of indep C2 \<ge>
    matroid.rank_of indep (C1 - {f}) + matroid.rank_of indep (C1 \<union> C2) + matroid.rank_of indep (C2 - {e})"
    by simp

  have 5: "matroid.rank_of indep (C1 - {f}) + matroid.rank_of indep (C1 \<union> C2) + matroid.rank_of indep (C2 - {e}) = 
    card C1 - 1 + matroid.rank_of indep (C1 \<union> C2) + card C2 - 1"
    using C1_minus_f_rank C2_minus_e_rank \<open>1 \<le> card C2\<close> by auto

  from 1 4 5 have
    "card C1 - 1 + matroid.rank_of indep (C1 \<union> C2 - {e, f}) + card C2 - 1 \<ge>
    card C1 - 1 + matroid.rank_of indep (C1 \<union> C2) + card C2 - 1" by simp
  with \<open>card C1 \<ge> 1\<close> \<open>card C2 \<ge> 1\<close> have 
    ranks_leq: "matroid.rank_of indep (C1 \<union> C2 - {e, f}) \<ge> matroid.rank_of indep (C1 \<union> C2)" by simp

  have "(C1 \<union> C2 - {e, f}) \<subseteq> (C1 \<union> C2)" by blast
  from \<open>C1 \<subseteq> E\<close> \<open>C2 \<subseteq> E\<close> have "C1 \<union> C2 \<subseteq> E" by auto
  from matroid.rank_of_mono[OF assms(1) \<open>(C1 \<union> C2 - {e, f}) \<subseteq> (C1 \<union> C2)\<close> \<open>C1 \<union> C2 \<subseteq> E\<close>]
  have ranks_geq: "matroid.rank_of indep (C1 \<union> C2 - {e, f}) \<le> matroid.rank_of indep (C1 \<union> C2)" .

  from ranks_leq ranks_geq
  have ranks_eq: "matroid.rank_of indep (C1 \<union> C2 - {e, f}) = matroid.rank_of indep (C1 \<union> C2)"
    by simp


  from \<open>C1 \<subseteq> E\<close> \<open>C2 \<subseteq> E\<close> have "(C1 \<union> C2 - {e, f}) \<subseteq> E" by blast
  from indep_system.basis_in_ex[OF indep_sys \<open>(C1 \<union> C2 - {e, f}) \<subseteq> E\<close>]
  have "\<exists>B. indep_system.basis_in indep (C1 \<union> C2 - {e, f}) B" .
  then obtain B where B_basis_in: "indep_system.basis_in indep (C1 \<union> C2 - {e, f}) B" by blast


  have "C1 \<union> C2 - {e, f} \<subseteq> C1 \<union> C2" by blast

(* Because the ranks are equal, B is also a basis of C1 \<union> C2 *)
  from matroid.rank_of_eq_basis_subset[OF assms(1) \<open>C1 \<union> C2 \<subseteq> E\<close> \<open>C1 \<union> C2 - {e, f} \<subseteq> C1 \<union> C2\<close>
      B_basis_in ranks_eq]
  have B_basis_in2: "indep_system.basis_in indep (C1 \<union> C2) B" .

  from indep_system.basis_in_indep_in[OF indep_sys \<open>(C1 \<union> C2 - {e, f}) \<subseteq> E\<close> B_basis_in]
    indep_system.indep_in_def[OF indep_sys]
  have "B \<subseteq> (C1 \<union> C2 - {e, f})" by auto
  then have "f \<notin> B" by blast
  with \<open>f \<in> C1 - C2\<close> have "f \<in> C1 \<union> C2 - B" by auto
  from matroid.basis_in_ex1_supset_circuit_in[OF assms(1) \<open>(C1 \<union> C2) \<subseteq> E\<close> B_basis_in2
      \<open>f \<in> C1 \<union> C2 - B\<close>]
  have "\<exists>!C. indep_system.circuit_in indep (C1 \<union> C2) C \<and> C \<subseteq> insert f B" .
  then obtain C3 where "indep_system.circuit_in indep (C1 \<union> C2) C3" "C3 \<subseteq> insert f B" by blast

  from indep_system.circuit_in_imp_circuit[OF indep_sys \<open>(C1 \<union> C2) \<subseteq> E\<close> this(1)]
  have C3_circuit: "indep_system.circuit E indep C3" .
  with assms(2) have "C3 \<in> \<C>" by simp

  from indep_system.basis_in_indep_in[OF indep_sys \<open>(C1 \<union> C2 - {e, f}) \<subseteq> E\<close> B_basis_in]
    indep_system.indep_in_def[OF indep_sys]
  have "indep B" by blast
  from matroid.min_dep_imp_supset_circuit[OF assms(1) \<open>indep B\<close> C3_circuit \<open>C3 \<subseteq> insert f B\<close>]
  have "f \<in> C3" .

  from indep_system.basis_in_subset_carrier[OF indep_sys \<open>C1 \<union> C2 - {e, f} \<subseteq> E\<close> B_basis_in] 
  have "B \<subseteq> C1 \<union> C2 - {e, f}" .
  with \<open>C3 \<subseteq> insert f B\<close> have "C3 \<subseteq> insert f (C1 \<union> C2 - {e, f})"
    by blast
  then have "C3 \<subseteq> C1 \<union> C2 - {e}"
    using \<open>e \<in> C1 \<inter> C2\<close> \<open>f \<in> C1 - C2\<close> by blast

  from \<open>C3 \<in> \<C>\<close> \<open>f \<in> C3\<close> \<open>C3 \<subseteq> C1 \<union> C2 - {e}\<close>
  show "\<exists>C3 \<in> \<C>. f \<in> C3 \<and> C3 \<subseteq> C1 \<union> C2 - {e}" by blast
qed

lemma C3'_imp_C3:
  assumes "indep_system E indep" "\<C> = {C. (indep_system.circuit E indep C)}"
    "\<forall>C1 \<in> \<C>. \<forall>C2 \<in> \<C>. \<forall>e \<in> C1 \<inter> C2. \<forall>f \<in> C1 - C2. (\<exists>C3 \<in> \<C>. f \<in> C3 \<and> C3 \<subseteq> (C1 \<union> C2) - {e})"
  shows "\<forall>C1 \<in> \<C>. \<forall>C2 \<in> \<C>. C1 \<noteq> C2 \<longrightarrow> (\<forall>e \<in> C1 \<inter> C2. \<exists>C3 \<in> \<C>. C3 \<subseteq> (C1 \<union> C2) - {e})"
proof (rule ballI, rule ballI, rule impI, rule ballI)
  fix C1 C2 e
  assume "C1 \<in> \<C>" "C2 \<in> \<C>" "C1 \<noteq> C2" "e \<in> C1 \<inter> C2"
  from assms(3) \<open>C1 \<in> \<C>\<close> \<open>C2 \<in> \<C>\<close> \<open>e \<in> C1 \<inter> C2\<close>
  have "\<forall>f \<in> C1 - C2. (\<exists>C3 \<in> \<C>. f \<in> C3 \<and> C3 \<subseteq> (C1 \<union> C2) - {e})" by auto
  moreover have "C1 - C2 \<noteq> {}"
    using \<open>C1 \<in> \<C>\<close> \<open>C1 \<noteq> C2\<close> \<open>C2 \<in> \<C>\<close> assms(1) assms(2) indep_system.circuit_subset_eq by auto
  ultimately show "\<exists>C3 \<in> \<C>. C3 \<subseteq> (C1 \<union> C2) - {e}" by fastforce
qed

lemma C3_imp_at_most_one_circuit:
  assumes "indep_system E indep" "\<C> = {C. (indep_system.circuit E indep C)}"
    "\<forall>C1 \<in> \<C>. \<forall>C2 \<in> \<C>. C1 \<noteq> C2 \<longrightarrow> (\<forall>e \<in> C1 \<inter> C2. \<exists>C3 \<in> \<C>. C3 \<subseteq> (C1 \<union> C2) - {e})"
  shows "\<forall>X. indep X \<longrightarrow> (\<forall>e \<in> E. card (indep_system.circuits_in E indep (X \<union> {e})) \<le> 1)"
proof (rule allI, rule impI, rule ballI, rule ccontr)
  fix X e
  let ?circuits = "{C | C. C \<subseteq> (X \<union> {e}) \<and> indep_system.circuit E indep C}"
  assume "indep X" "e \<in> E"
  assume "\<not> card ?circuits \<le> 1"
  have "\<exists>C1 C2. C1 \<in> ?circuits \<and> C2 \<in> ?circuits \<and> C1 \<noteq> C2"
  proof -
    from indep_system.indep_subset_carrier[OF assms(1) \<open>indep X\<close>] have "X \<subseteq> E" .
    with \<open>e \<in> E\<close> have subset_E: "X \<union> {e} \<subseteq> E" by blast
    from indep_system.carrier_finite[OF assms(1)] subset_E have "finite (X \<union> {e})"
      using finite_subset by blast
    moreover have "?circuits \<subseteq> Pow (X \<union> {e})" by blast
    ultimately have finite_circuits: "finite ?circuits" using finite_subset by blast
    have "\<not> (\<forall>a1 \<in> ?circuits. \<forall>a2 \<in> ?circuits. a1 = a2)"
    proof
      assume "\<forall>a1 \<in> ?circuits. \<forall>a2 \<in> ?circuits. a1 = a2"
      with card_le_Suc0_iff_eq[OF finite_circuits] have "card ?circuits \<le> Suc 0" by blast
      with \<open>\<not> card ?circuits \<le> 1\<close> show False by simp
    qed
    then show "\<exists>C1 C2. C1 \<in> ?circuits \<and> C2 \<in> ?circuits \<and> C1 \<noteq> C2" by blast
  qed
  then obtain C1 C2 where "C1 \<in> ?circuits" "C2 \<in> ?circuits" "C1 \<noteq> C2" by blast

  from \<open>C1 \<in> ?circuits\<close> assms(2) have "C1 \<in> \<C>" by simp
  from \<open>C2 \<in> ?circuits\<close> assms(2) have "C2 \<in> \<C>" by simp
  from \<open>C1 \<in> ?circuits\<close> indep_system.circuit_subset_carrier[OF assms(1)] have "C1 \<subseteq> E" by simp
  from \<open>C2 \<in> ?circuits\<close> indep_system.circuit_subset_carrier[OF assms(1)] have "C2 \<subseteq> E" by simp
  from \<open>C1 \<subseteq> E\<close> \<open>C2 \<subseteq> E\<close> have "C1 \<union> C2 - {e} \<subseteq> E" by blast 

  from indep_system.min_dep_imp_supset_circuit[OF assms(1) \<open>indep X\<close>] \<open>C1 \<in> ?circuits\<close>
  have "e \<in> C1" by blast
  from indep_system.min_dep_imp_supset_circuit[OF assms(1) \<open>indep X\<close>] \<open>C2 \<in> ?circuits\<close>
  have "e \<in> C2" by blast
  from \<open>e \<in> C1\<close> \<open>e \<in> C2\<close> have "e \<in> C1 \<inter> C2" by blast

  from assms(3) \<open>C1 \<in> \<C>\<close> \<open>C2 \<in> \<C>\<close> \<open>C1 \<noteq> C2\<close> \<open>e \<in> C1 \<inter> C2\<close>
  have "\<exists>C3 \<in> \<C>. C3 \<subseteq> C1 \<union> C2 - {e}" by blast
  with assms(2) have "\<exists>C3. indep_system.circuit E indep C3 \<and> C3 \<subseteq> C1 \<union> C2 - {e}" by blast
  with indep_system.dep_iff_supset_circuit[OF assms(1) \<open>C1 \<union> C2 - {e} \<subseteq> E\<close>]
  have "\<not> indep (C1 \<union> C2 - {e})" by blast

  from \<open>C1 \<in> ?circuits\<close> have "C1 - {e} \<subseteq> X" by auto 
  from \<open>C2 \<in> ?circuits\<close> have "C2 - {e} \<subseteq> X" by auto 
  from \<open>C1 - {e} \<subseteq> X\<close> \<open>C2 - {e} \<subseteq> X\<close> have "(C1 \<union> C2 - {e}) \<subseteq> X" by blast
  from indep_system.indep_subset[OF assms(1) \<open>indep X\<close> \<open>(C1 \<union> C2 - {e}) \<subseteq> X\<close>]
  have "indep (C1 \<union> C2 - {e})" .

  from \<open>\<not> indep (C1 \<union> C2 - {e})\<close> \<open>indep (C1 \<union> C2 - {e})\<close>
  show "False" by blast
qed

lemma at_most_one_circuit_imp_matroid:
  assumes "indep_system E indep" "\<C> = {C. (indep_system.circuit E indep C)}"
    "\<forall>X. indep X \<longrightarrow> (\<forall>e \<in> E. card (indep_system.circuits_in E indep (X \<union> {e})) \<le> 1)"
  shows "matroid E indep"
  using indep_system.rank_quotient_lower_bound[OF assms(1) Nat.le_refl assms(3)]
    indep_system.rank_quotient_leq_1[OF assms(1)] indep_system.matroid_iff_rq_eq_1[OF assms(1)]
    One_rat_def by auto

lemma matroid_iff_at_most_one_circuit:
  assumes "indep_system E indep" "\<C> = {C. (indep_system.circuit E indep C)}"
  shows "matroid E indep \<longleftrightarrow> 
    (\<forall>X. indep X \<longrightarrow> (\<forall>e \<in> E. card (indep_system.circuits_in E indep (X \<union> {e})) \<le> 1))"
proof
  assume "matroid E indep"
  from C3_imp_at_most_one_circuit[OF assms
      C3'_imp_C3[OF assms matroid_imp_C3'[OF \<open>matroid E indep\<close> assms(2)]]]
  show "(\<forall>X. indep X \<longrightarrow> (\<forall>e \<in> E. card (indep_system.circuits_in E indep (X \<union> {e})) \<le> 1))" .
next
  assume "(\<forall>X. indep X \<longrightarrow> (\<forall>e \<in> E. card (indep_system.circuits_in E indep (X \<union> {e})) \<le> 1))"
  from at_most_one_circuit_imp_matroid[OF assms this]
  show "matroid E indep" .
qed

lemma matroid_iff_C3:
  assumes "indep_system E indep" "\<C> = {C. (indep_system.circuit E indep C)}"
  shows "matroid E indep \<longleftrightarrow> 
    (\<forall>C1 \<in> \<C>. \<forall>C2 \<in> \<C>. C1 \<noteq> C2 \<longrightarrow> (\<forall>e \<in> C1 \<inter> C2. \<exists>C3 \<in> \<C>. C3 \<subseteq> (C1 \<union> C2) - {e}))"
proof
  assume "matroid E indep"
  from C3'_imp_C3[OF assms matroid_imp_C3'[OF \<open>matroid E indep\<close> assms(2)]]
  show "(\<forall>C1 \<in> \<C>. \<forall>C2 \<in> \<C>. C1 \<noteq> C2 \<longrightarrow> (\<forall>e \<in> C1 \<inter> C2. \<exists>C3 \<in> \<C>. C3 \<subseteq> (C1 \<union> C2) - {e}))" .
next
  assume "(\<forall>C1 \<in> \<C>. \<forall>C2 \<in> \<C>. C1 \<noteq> C2 \<longrightarrow> (\<forall>e \<in> C1 \<inter> C2. \<exists>C3 \<in> \<C>. C3 \<subseteq> (C1 \<union> C2) - {e}))"
  from at_most_one_circuit_imp_matroid[OF assms C3_imp_at_most_one_circuit[OF assms]] this
  show "matroid E indep" by blast
qed

lemma matroid_iff_C3':
  assumes "indep_system E indep" "\<C> = {C. (indep_system.circuit E indep C)}"
  shows "matroid E indep \<longleftrightarrow> 
    (\<forall>C1 \<in> \<C>. \<forall>C2 \<in> \<C>. \<forall>e \<in> C1 \<inter> C2. \<forall>f \<in> C1 - C2. (\<exists>C3 \<in> \<C>. f \<in> C3 \<and> C3 \<subseteq> (C1 \<union> C2) - {e}))"
proof
  assume "matroid E indep"
  from matroid_imp_C3'[OF \<open>matroid E indep\<close> assms(2)]
  show "(\<forall>C1 \<in> \<C>. \<forall>C2 \<in> \<C>. \<forall>e \<in> C1 \<inter> C2. \<forall>f \<in> C1 - C2. (\<exists>C3 \<in> \<C>. f \<in> C3 \<and> C3 \<subseteq> (C1 \<union> C2) - {e}))" .
next
  assume "(\<forall>C1 \<in> \<C>. \<forall>C2 \<in> \<C>. \<forall>e \<in> C1 \<inter> C2. \<forall>f \<in> C1 - C2. (\<exists>C3 \<in> \<C>. f \<in> C3 \<and> C3 \<subseteq> (C1 \<union> C2) - {e}))"
  from at_most_one_circuit_imp_matroid[OF assms
      C3_imp_at_most_one_circuit[OF assms C3'_imp_C3[OF assms this]]]
  show "matroid E indep" .
qed


subsection \<open>Definition 13.13\<close>

subsubsection \<open>Dual definition\<close>

definition dual where 
  "dual E indep = (\<lambda> X. X \<subseteq> E \<and> (\<exists>B. indep_system.basis E indep B \<and> (X \<inter> B = {})))"

subsubsection \<open>Additional lemma\<close>

lemma dual_indep_system:
  assumes "indep_system E indep"
  shows "indep_system E (dual E indep)"
  unfolding dual_def
  apply(unfold_locales)
  using assms indep_system.carrier_finite apply blast
  apply simp
  subgoal
  proof -
    from indep_system.basis_ex[OF assms] obtain B where basis_B: "indep_system.basis E indep B" by blast
    have "{} \<subseteq> E" by (rule empty_subsetI)
    moreover have "{} \<inter> B = {}" by (rule inf_bot_left)
    ultimately show ?thesis using basis_B by blast
  qed
  using disjoint_iff apply blast
  done

subsection \<open>Proposition 13.14\<close>

subsubsection \<open>Auxiliary lemmas\<close>

lemma dual_basis_complement:
  assumes "indep_system E indep" "B' \<subseteq> E"
  shows "(indep_system.basis E (dual E indep) B') \<longleftrightarrow> 
    (\<exists>B. indep_system.basis E indep B \<and> B' = E - B)"
proof (rule iffI, erule HOL.contrapos_pp)
  assume "\<not>(\<exists>B. indep_system.basis E indep B \<and> B' = E - B)"
  then have not_complement: "(\<forall>B. indep_system.basis E indep B \<longrightarrow> B' \<noteq> E - B)" by blast

  have dual_indep_sys: "indep_system E (dual E indep)" using dual_indep_system[OF assms(1)] .

  show "\<not>(indep_system.basis E (dual E indep) B')"
  proof (cases "\<exists>B. indep_system.basis E indep B \<and> B' \<inter> B = {}")
    case True
    then obtain B where "indep_system.basis E indep B" "B' \<inter> B = {}" by blast

    let ?B_comp = "E - B"

    from assms(2) \<open>B' \<inter> B = {}\<close> have "B' \<subseteq> ?B_comp" by blast
    with \<open>indep_system.basis E indep B\<close> not_complement have "B' \<noteq> ?B_comp" by blast

    from \<open>B' \<subseteq> ?B_comp\<close> \<open>B' \<noteq> ?B_comp\<close>
    have "\<exists>x. x \<in> ?B_comp \<and> x \<notin> B' \<and> (insert x B') \<subseteq> ?B_comp" by blast
    then have "\<exists>x. x \<in> ?B_comp \<and> x \<notin> B' \<and> (insert x B') \<inter> B = {}" by auto

    with \<open>indep_system.basis E indep B\<close>
    have "\<exists>x \<in> E - B'. \<exists>B''. indep_system.basis E indep B'' \<and> (insert x B') \<inter> B'' = {}"
      by auto

    with indep_system.basis_def[OF dual_indep_sys] dual_def show ?thesis
      by (simp add: dual_def) 
  next
    case False
    from False have "\<not> (dual E indep) B'" by (simp add: dual_def)
    with indep_system.basis_def[OF dual_indep_sys] show ?thesis by auto
  qed
next
  assume complement: "(\<exists>B. indep_system.basis E indep B \<and> B' = E - B)"
  then obtain B where "indep_system.basis E indep B" "B' = E - B" by blast

  have dual_indep_sys: "indep_system E (dual E indep)" using dual_indep_system[OF assms(1)] .

  from complement have "\<exists>B. indep_system.basis E indep B \<and> B' \<inter> B = {}"
    by blast
  with assms(2) have B'_indep_in_dual: "(dual E indep) B'" using dual_def
    by metis

  have "\<forall>x. x \<in> E - B' \<longrightarrow> (\<forall>B''. indep_system.basis E indep B'' \<longrightarrow> ((insert x B') \<inter> B'' \<noteq> {}))"
  proof(rule allI, rule impI, rule allI, rule impI)
    fix x B''
    assume "x \<in> E - B'" "indep_system.basis E indep B''"
    show "((insert x B') \<inter> B'' \<noteq> {})"
    proof (cases "B'' \<inter> B' = {}")
      case True
      have "B'' = B"
      proof -
        have B''_subset_E: "B'' \<subseteq> E"
          using indep_system.basis_subset_carrier[OF assms(1) \<open>indep_system.basis E indep B''\<close>] .
        have "B'' \<inter> (E - B) = {}"
          using True \<open>B' = E - B\<close> by simp
        with B''_subset_E have "B'' \<subseteq> B" by blast
        from indep_system.basis_subset_eq[OF assms(1) \<open>indep_system.basis E indep B''\<close>
            \<open>indep_system.basis E indep B\<close> this]
        show "B'' = B" .
      qed
      with \<open>B' = E - B\<close> \<open>x \<in> E - B'\<close> have "x \<in> (insert x B') \<inter> B''" by simp
      then show ?thesis by blast
    next
      case False
      then show ?thesis by auto
    qed
  qed

  then have "\<forall>x \<in> E - B'. \<not>((insert x B') \<subseteq> E \<and> 
    (\<exists>B. indep_system.basis E indep B \<and> ((insert x B') \<inter> B = {})))"
    by blast

  then have "\<forall>x \<in> E - B'. \<not>(dual E indep) (insert x B')"
    using dual_def[of E indep] by auto

  with B'_indep_in_dual show "(indep_system.basis E (dual E indep) B')"
    using indep_system.basis_def[OF dual_indep_sys] by blast
qed

subsubsection \<open>Theorem statement\<close>

lemma dual_involution:
  assumes "indep_system E indep"
  shows "dual E (dual E indep) = indep"
proof
  from dual_indep_system[OF assms] 
  have dual_indep_sys: "indep_system E (dual E indep)" by blast

  fix X
  have "(dual E (dual E indep)) X = 
    (X \<subseteq> E \<and> (\<exists>B'. indep_system.basis E (dual E indep) B' \<and> (X \<inter> B' = {})))"
    unfolding dual_def by blast
  also have "... =
    (X \<subseteq> E \<and> (\<exists>B. indep_system.basis E indep B \<and> (X \<inter> (E - B) = {})))"
  proof (intro iffI)
    assume "X \<subseteq> E \<and> (\<exists>B'. indep_system.basis E (dual E indep) B' \<and> X \<inter> B' = {})"
    then obtain B' where "X \<subseteq> E" and B'_basis: "indep_system.basis E (dual E indep) B'"
      and B'_disj: "X \<inter> B' = {}" by blast
    from indep_system.basis_subset_carrier[OF dual_indep_sys B'_basis]
    have "B' \<subseteq> E" .
    from dual_basis_complement[OF assms this]
    have "indep_system.basis E (dual E indep) B' \<longleftrightarrow>
      (\<exists>B. indep_system.basis E indep B \<and> B' = E - B)" .
    with B'_basis obtain B where "indep_system.basis E indep B" and "B' = E - B" by blast
    with B'_disj have "X \<inter> (E - B) = {}" by simp
    with \<open>X \<subseteq> E\<close> \<open>indep_system.basis E indep B\<close>
    show "X \<subseteq> E \<and> (\<exists>B. indep_system.basis E indep B \<and> X \<inter> (E - B) = {})" by blast
  next
    assume "X \<subseteq> E \<and> (\<exists>B. indep_system.basis E indep B \<and> X \<inter> (E - B) = {})"
    then obtain B where "X \<subseteq> E" and B_basis: "indep_system.basis E indep B"
      and B_disj: "X \<inter> (E - B) = {}" by blast
    have "E - B \<subseteq> E" by blast
    from dual_basis_complement[OF assms this]
    have "indep_system.basis E (dual E indep) (E - B) \<longleftrightarrow>
      (\<exists>B'. indep_system.basis E indep B' \<and> E - B = E - B')" .
    with B_basis have "indep_system.basis E (dual E indep) (E - B)" by blast
    with \<open>X \<subseteq> E\<close> B_disj
    show "X \<subseteq> E \<and> (\<exists>B'. indep_system.basis E (dual E indep) B' \<and> X \<inter> B' = {})" by blast
  qed
  also have "... =
    (X \<subseteq> E \<and> (\<exists>B. indep_system.basis E indep B \<and> X \<subseteq> B))"
    by auto
  also have "... = indep X" using indep_system.indep_iff_subset_basis[OF assms]
  proof -
    from assms have cont: "\<And>Y. indep Y \<Longrightarrow> Y \<subseteq> E"
      by (auto simp: indep_system_def)
    show ?thesis
      using indep_system.indep_iff_subset_basis[OF assms] cont by blast
  qed
  finally show "(dual E (dual E indep)) X = indep X" .
qed


subsection \<open>Theorem 13.15\<close>

subsubsection \<open>Auxiliary lemmas\<close>

context matroid
begin

lemma rank_carrier_iff_contains_basis:
  assumes "X \<subseteq> carrier"
  shows "rank_of X = rank_of carrier \<longleftrightarrow> (\<exists>B. basis_in carrier B \<and> B \<subseteq> X)"
proof
  assume "rank_of X = rank_of carrier"
  from basis_in_iff_rank_of[OF assms] have "\<forall>B. basis_in X B \<longrightarrow> rank_of B = rank_of X"
    by (meson assms basis_in_subset_carrier)
  with \<open>rank_of X = rank_of carrier\<close>
  have "\<forall>B. basis_in X B \<longrightarrow> rank_of B = rank_of carrier" by simp
  with basis_in_iff_rank_of basis_in_indep_in indep_in_iff_rank_of
  have "\<forall>B. basis_in X B \<longrightarrow> basis_in carrier B" 
    by (meson assms indep_in_def indep_subset_carrier subset_refl)

  with basis_in_ex[OF assms] basis_in_subset_carrier[OF assms]
  show "(\<exists>B. basis_in carrier B \<and> B \<subseteq> X)" by auto
next
  assume "(\<exists>B. basis_in carrier B \<and> B \<subseteq> X)"
  then obtain B where "basis_in carrier B" "B \<subseteq> X" by blast

  have "carrier \<subseteq> carrier" by auto
  from \<open>B \<subseteq> X\<close> assms subset_trans have "B \<subseteq> carrier" by blast
  from \<open>basis_in carrier B\<close> basis_in_iff_rank_of[OF \<open>carrier \<subseteq> carrier\<close> this]
  have "rank_of B = rank_of carrier" by blast

  from rank_of_mono[OF \<open>B \<subseteq> X\<close> assms] \<open>rank_of B = rank_of carrier\<close> 
  have "rank_of X \<ge> rank_of carrier" by simp

  from rank_of_mono[OF assms \<open>carrier \<subseteq> carrier\<close>]
  have "rank_of X \<le> rank_of carrier" by simp

  from \<open>rank_of X \<ge> rank_of carrier\<close> \<open>rank_of X \<le> rank_of carrier\<close>
  show "rank_of X = rank_of carrier" by auto
qed

end

lemma dual_rank_well_def:
  assumes "matroid E indep"
  shows "\<forall>X \<subseteq> E. card X + matroid.rank_of indep (E - X) \<ge> matroid.rank_of indep E"
proof (rule allI, rule impI)
  fix X
  assume "X \<subseteq> E"
  have "E - X \<subseteq> E" by auto

  from matroid.rank_of_def[OF assms(1)] have "matroid.rank_of indep {} = 0"
  proof -
    have "indep_system E indep" using assms(1) by (rule matroid.axioms(1))
    then have "indep {}" by (rule indep_system.indep_empty)
    then have "matroid.rank_of indep {} = card {}"
      using matroid.indep_iff_rank_of[OF assms(1) empty_subsetI] by fastforce
    then show ?thesis by simp
  qed

  from matroid.rank_of_Un_Int_le[OF assms(1) \<open>X \<subseteq> E\<close> \<open>E - X \<subseteq> E\<close>]
  have "indep_system.lower_rank_of indep (X \<union> (E - X)) + indep_system.lower_rank_of indep (X \<inter> (E - X))
    \<le> indep_system.lower_rank_of indep X + indep_system.lower_rank_of indep (E - X)" by blast
  then have "indep_system.lower_rank_of indep E + indep_system.lower_rank_of indep ({})
    \<le> indep_system.lower_rank_of indep X + indep_system.lower_rank_of indep (E - X)"
    using Diff_partition \<open>X \<subseteq> E\<close> by fastforce
  with \<open>matroid.rank_of indep {} = 0\<close>
  have "indep_system.lower_rank_of indep E \<le> indep_system.lower_rank_of indep X +
    indep_system.lower_rank_of indep (E - X)" by simp
  with matroid.rank_of_le[OF assms(1) \<open>X \<subseteq> E\<close>]
  show "card X + matroid.rank_of indep (E - X) \<ge> matroid.rank_of indep E" by simp
qed


lemma dual_rank_sat_rank_axioms1:
  assumes "finite E" "matroid E indep"
    "\<forall>X \<subseteq> E. q X = card X + matroid.rank_of indep (E - X) - matroid.rank_of indep E"
  shows "((\<forall>X \<subseteq> E. q X \<le> card X) \<and>
    (\<forall>X \<subseteq> E. \<forall>Y \<subseteq> E. X \<subseteq> Y \<longrightarrow> q X \<le> q Y) \<and>
    (\<forall>X \<subseteq> E. \<forall>Y \<subseteq> E. q (X \<union> Y) + q (X \<inter> Y) \<le> q X + q Y))"
proof-

  from matroid.rank_of_def[OF assms(2)] have "matroid.rank_of indep {} = 0"
    using indep_system.indep_empty[OF matroid.axioms(1)[OF assms(2)]]
          matroid.indep_iff_rank_of[OF assms(2) empty_subsetI]
    by simp

  have q_well_def: "\<forall>X \<subseteq> E. card X + matroid.rank_of indep (E - X) \<ge> matroid.rank_of indep E"
    using dual_rank_well_def[OF assms(2)] by blast

  have R1: "\<forall>X \<subseteq> E. q X \<le> card X"
  proof (rule allI, rule impI)
    fix X
    assume "X \<subseteq> E"

    from matroid.rank_of_mono[OF assms(2)] have
      "matroid.rank_of indep (E - X) \<le> matroid.rank_of indep E" by auto
    then have "card X + matroid.rank_of indep (E - X) - matroid.rank_of indep E \<le> card X"
      by simp

    with \<open>X \<subseteq> E\<close> assms(3) show "q X \<le> card X" by simp
  qed

  have R2: "\<forall>X \<subseteq> E. \<forall>Y \<subseteq> E. X \<subseteq> Y \<longrightarrow> q X \<le> q Y"
  proof ((rule allI, rule impI)+, rule impI)
    fix X Y
    assume "X \<subseteq> E" "Y \<subseteq> E" "X \<subseteq> Y"

    from \<open>X \<subseteq> Y\<close> \<open>Y \<subseteq> E\<close> have "(E - Y) \<union> (Y - X) = E - X" by auto

    from matroid.rank_of_Un_Int_le[OF assms(2)] \<open>X \<subseteq> Y\<close> \<open>Y \<subseteq> E\<close>
    have "matroid.rank_of indep ((E - Y) \<union> (Y - X)) + matroid.rank_of indep ((E - Y) \<inter> (Y - X)) \<le>
        matroid.rank_of indep (E - Y) + matroid.rank_of indep (Y - X)"
      by (meson Diff_subset subset_trans)
    with \<open>X \<subseteq> Y\<close> have 
      "matroid.rank_of indep (E - X) + matroid.rank_of indep ((E - Y) \<inter> (Y - X)) \<le>
      matroid.rank_of indep (E - Y) + matroid.rank_of indep (Y - X)"
      by (simp add: \<open>E - Y \<union> (Y - X) = E - X\<close>)
    moreover have "(E - Y) \<inter> (Y - X) = {}" by blast
    ultimately have "matroid.rank_of indep (E - X) + matroid.rank_of indep ({}) \<le>
      matroid.rank_of indep (E - Y) + matroid.rank_of indep (Y - X)"
      by simp
    with \<open>matroid.rank_of indep {} = 0\<close> have
      "matroid.rank_of indep (E - X) \<le>
      matroid.rank_of indep (E - Y) + matroid.rank_of indep (Y - X)"
      by auto

    then have
      "matroid.rank_of indep (E - X) - matroid.rank_of indep (E - Y) \<le> 
      matroid.rank_of indep (Y - X)" by simp
    with matroid.rank_of_le[OF assms(2)] \<open>Y \<subseteq> E\<close> \<open>X \<subseteq> Y\<close> have
      "matroid.rank_of indep (E - X) - matroid.rank_of indep (E - Y) \<le> 
      card (Y - X)"
      by (meson Diff_subset order_trans)
    with \<open>X \<subseteq> Y\<close> have
      "matroid.rank_of indep (E - X) - matroid.rank_of indep (E - Y) \<le> 
      card Y - card X"
    proof -
      have "finite X" using rev_finite_subset[OF assms(1) \<open>X \<subseteq> E\<close>] .
      have "card (Y - X) = card Y - card X"
        using card_Diff_subset[OF \<open>finite X\<close> \<open>X \<subseteq> Y\<close>] .
      then show ?thesis
        using \<open>matroid.rank_of indep (E - X) - matroid.rank_of indep (E - Y) \<le> card (Y - X)\<close>
        by simp
    qed
    then have
      "card X + matroid.rank_of indep (E - X) \<le> card Y + matroid.rank_of indep (E - Y)"
    proof -
      have finite_Y: "finite Y" by (rule finite_subset[OF \<open>Y \<subseteq> E\<close> assms(1)])
      have card_le: "card X \<le> card Y" by (rule card_mono[OF finite_Y \<open>X \<subseteq> Y\<close>])
      show ?thesis
      proof (cases "matroid.rank_of indep (E - X) \<le> matroid.rank_of indep (E - Y)")
        case True
        show ?thesis by (rule add_mono[OF card_le True])
      next
        case False
        then have rank_le: "matroid.rank_of indep (E - Y) \<le> matroid.rank_of indep (E - X)"
          by presburger
        show ?thesis
          using \<open>matroid.rank_of indep (E - X) - matroid.rank_of indep (E - Y) \<le> card Y - card X\<close>
            rank_le card_le
          by presburger
      qed
    qed

    with assms(3) \<open>X \<subseteq> E\<close> \<open>Y \<subseteq> E\<close> show "q X \<le> q Y" by simp
  qed

  have R3: "\<forall>X \<subseteq> E. \<forall>Y \<subseteq> E. q (X \<union> Y) + q (X \<inter> Y) \<le> q X + q Y"
  proof ((rule allI, rule impI)+)
    fix X Y
    assume "X \<subseteq> E" "Y \<subseteq> E"

    from \<open>X \<subseteq> E\<close> \<open>Y \<subseteq> E\<close> have "X \<union> Y \<subseteq> E" by simp
    from \<open>X \<subseteq> E\<close> \<open>Y \<subseteq> E\<close> have "X \<inter> Y \<subseteq> E" by blast

    from \<open>X \<union> Y \<subseteq> E\<close> assms(3)
    have q_X_un_Y: "q (X \<union> Y) = card (X \<union> Y) + matroid.rank_of indep (E - (X \<union> Y))
      - matroid.rank_of indep E" by blast

    from \<open>X \<inter> Y \<subseteq> E\<close> assms(3)
    have q_X_int_Y: "q (X \<inter> Y) = card (X \<inter> Y) + matroid.rank_of indep (E - (X \<inter> Y))
      - matroid.rank_of indep E" by blast

    from \<open>X \<subseteq> E\<close> assms(3)
    have q_X: "q X = card X + matroid.rank_of indep (E - X) - matroid.rank_of indep E" by blast

    from \<open>Y \<subseteq> E\<close> assms(3)
    have q_Y: "q Y = card Y + matroid.rank_of indep (E - Y) - matroid.rank_of indep E" by blast

    have "E - X \<subseteq> E" by auto
    have "E - Y \<subseteq> E" by auto

    from q_X_un_Y q_X_int_Y
    have "q (X \<union> Y) + q (X \<inter> Y) = card (X \<union> Y) + card (X \<inter> Y) +
      matroid.rank_of indep (E - (X \<union> Y)) + matroid.rank_of indep (E - (X \<inter> Y))
      - matroid.rank_of indep E - matroid.rank_of indep E"
      using q_well_def Nat.add_diff_assoc \<open>X \<inter> Y \<subseteq> E\<close> \<open>X \<union> Y \<subseteq> E\<close> by force 
    also have "... = card X + card Y +
      matroid.rank_of indep (E - (X \<union> Y)) + matroid.rank_of indep (E - (X \<inter> Y))
      - matroid.rank_of indep E - matroid.rank_of indep E"
    proof -
      from assms(1) \<open>X \<subseteq> E\<close> have "finite X" by (rule rev_finite_subset)
      from assms(1) \<open>Y \<subseteq> E\<close> have "finite Y" by (rule rev_finite_subset)
      from card_Un_Int[OF \<open>finite X\<close> \<open>finite Y\<close>] show ?thesis by simp
    qed
    also have "... = card X + card Y +
      matroid.rank_of indep ((E - X) \<inter> (E - Y)) + matroid.rank_of indep ((E - X) \<union> (E - Y))
      - matroid.rank_of indep E - matroid.rank_of indep E"
      by (simp add: Diff_Int Diff_Un)
    also have "... \<le> card X + card Y +
      matroid.rank_of indep (E - X) + matroid.rank_of indep (E - Y)
      - matroid.rank_of indep E - matroid.rank_of indep E"
      using matroid.rank_of_Un_Int_le[OF assms(2) \<open>E - X \<subseteq> E\<close> \<open>E - Y \<subseteq> E\<close>] by auto
    also have "... = (card X + matroid.rank_of indep (E - X) - matroid.rank_of indep E)
      + (card Y + matroid.rank_of indep (E - Y) - matroid.rank_of indep E)"
      using q_well_def Nat.add_diff_assoc  by (simp add: \<open>X \<subseteq> E\<close> \<open>Y \<subseteq> E\<close>)
    also have "... = q X + q Y"
      using q_X q_Y by presburger

    finally show "q (X \<union> Y) + q (X \<inter> Y) \<le> q X + q Y" .
  qed

  from R1 R2 R3 show ?thesis by blast
qed


lemma matroids_eq_iff_eq_subset_carrier:
  assumes "finite E" "\<forall>X \<subseteq> E. indep X = indep' X" "\<forall>X. indep' X \<longrightarrow> X \<subseteq> E"
  shows "matroid E indep \<Longrightarrow> matroid E indep'"
proof-
  assume matroid_indep: "matroid E indep"

  from matroid.axioms(1)[OF matroid_indep] have "indep_system E indep"
    by blast

  show "matroid E indep'"
    apply(unfold_locales)
    using assms apply simp
    using assms(3) apply blast
    using indep_system.indep_ex[OF \<open>indep_system E indep\<close>] assms(2)
    apply (meson \<open>indep_system E indep\<close> indep_system.indep_subset_carrier)
    using indep_system.indep_subset[OF \<open>indep_system E indep\<close>] assms(2)
    apply (meson \<open>indep_system E indep\<close> assms(3) indep_system.indep_subset_carrier)
    using matroid.augment_aux[OF matroid_indep] assms(2)
    apply (meson \<open>indep_system E indep\<close> assms(3) indep_system.indep_subset_carrier)
    done
qed


subsubsection \<open>Theorem statement\<close>

lemma matroid_dual_rank_expr:
  assumes "finite E" "matroid E indep"
  shows "matroid E (dual E indep) \<and> (\<forall>X \<subseteq> E. matroid.rank_of (dual E indep) X =
    card X + matroid.rank_of indep (E - X) - matroid.rank_of indep E)"
proof-
  let ?q = "\<lambda> X. card X + matroid.rank_of indep (E - X) - matroid.rank_of indep E"
  from dual_rank_sat_rank_axioms1[OF assms(1) assms(2)]
  have "R1 E ?q \<and> R2 E ?q \<and> R3 E ?q" by force

  from matroid_iff_rank_axioms1[OF assms(1)] this
  have "\<exists>indep'. matroid E indep' \<and> (\<forall>X\<subseteq>E. ?q X = matroid.rank_of indep' X)"
    by simp
  then obtain indep' where "matroid E indep'" "\<forall>X\<subseteq>E. ?q X = matroid.rank_of indep' X"
    by blast

  have "\<forall>X \<subseteq> E. (?q X = card X) \<longleftrightarrow> ((dual E indep) X)"
  proof (rule allI, rule impI)
    fix X
    assume "X \<subseteq> E"
    have "E - X \<subseteq> E" by blast

    have "(?q X = card X) \<longleftrightarrow> (matroid.rank_of indep (E - X) = matroid.rank_of indep E)"
    proof -
      have le: "matroid.rank_of indep E \<le> card X + matroid.rank_of indep (E - X)"
        using dual_rank_well_def[OF assms(2)] \<open>X \<subseteq> E\<close> by blast
    show "(?q X = card X) \<longleftrightarrow> (matroid.rank_of indep (E - X) = matroid.rank_of indep E)"
      using le by presburger
    qed
    also have "... \<longleftrightarrow> (\<exists>B. indep_system.basis_in indep E B \<and> B \<subseteq> (E - X))"
      using matroid.rank_carrier_iff_contains_basis[OF assms(2) \<open>E - X \<subseteq> E\<close>] by simp
    also have "... \<longleftrightarrow> (\<exists>B. indep_system.basis_in indep E B \<and> X \<inter> B = {})"
      using assms(2) indep_system.basis_in_subset_carrier matroid_def by fastforce  
    also have "... \<longleftrightarrow> (\<exists>B. indep_system.basis E indep B \<and> X \<inter> B = {})"
      using assms(2) by (simp add: indep_system.basis_iff_basis_in matroid.axioms(1))
    also have "... \<longleftrightarrow> (X \<subseteq> E \<and> (\<exists>B. indep_system.basis E indep B \<and> X \<inter> B = {}))"
      using \<open>X \<subseteq> E\<close> by auto
    also have "... \<longleftrightarrow> (dual E indep) X"
      unfolding dual_def by auto
    finally show "(?q X = card X) \<longleftrightarrow> ((dual E indep) X)" by blast
  qed

  from matroid.indep_iff_rank_of[OF \<open>matroid E indep'\<close>]
  have "\<forall>X \<subseteq> E. indep' X \<longleftrightarrow> (matroid.rank_of indep' X = card X)" by blast
  with \<open>\<forall>X\<subseteq>E. ?q X = matroid.rank_of indep' X\<close>
  have "\<forall>X \<subseteq> E. indep' X \<longleftrightarrow> (?q X = card X)" by simp

  from \<open>\<forall>X \<subseteq> E. (?q X = card X) \<longleftrightarrow> ((dual E indep) X)\<close> \<open>\<forall>X \<subseteq> E. indep' X \<longleftrightarrow> (?q X = card X)\<close>
  have indep'_iff_dual: "\<forall>X \<subseteq> E. indep' X \<longleftrightarrow> ((dual E indep) X)" by blast

  have dual_imp_subset_E: "\<forall>X. ((dual E indep) X) \<longrightarrow> X \<subseteq> E" unfolding dual_def by simp
  from matroids_eq_iff_eq_subset_carrier[OF assms(1) indep'_iff_dual dual_imp_subset_E
      \<open>matroid E indep'\<close>]
  have "matroid E (dual E indep)" by simp

  from matroid.axioms(1)[OF \<open>matroid E indep'\<close>] have "indep_system E indep'" by blast
  from matroid.axioms(1)[OF \<open>matroid E (dual E indep)\<close>] have "indep_system E (dual E indep)"
    by blast

  have "\<forall>X \<subseteq> E. \<forall>B \<subseteq> E. indep_system.basis_in indep' X B \<longleftrightarrow>
    indep_system.basis_in (dual E indep) X B"
  proof ((rule allI, rule impI)+)
    fix X B
    assume "X \<subseteq> E" "B \<subseteq> E"

    have 1: "\<forall>Y. (indep_system.indep_in indep' X) Y \<longleftrightarrow>
      (indep_system.indep_in (dual E indep) X) Y"
    proof (rule allI)
      fix Y
      show "(indep_system.indep_in indep' X) Y \<longleftrightarrow>
        (indep_system.indep_in (dual E indep) X) Y"
      proof (cases "Y \<subseteq> E")
        case True
        then show ?thesis
          using indep_system.indep_in_def[OF \<open>indep_system E indep'\<close>]
            indep_system.indep_in_def[OF \<open>indep_system E (dual E indep)\<close>]
            indep'_iff_dual by simp
      next
        case False
        then show ?thesis
        proof -
          have not_indep': "\<not> (indep_system.indep_in indep' X) Y"
          proof (rule notI)
            assume "(indep_system.indep_in indep' X) Y"
            from indep_system.indep_in_subset_carrier[OF \<open>indep_system E indep'\<close> this]
            have "Y \<subseteq> X" .
            with \<open>X \<subseteq> E\<close> have "Y \<subseteq> E" using subset_trans by blast
            with False show False by blast
          qed
          have not_dual: "\<not> (indep_system.indep_in (dual E indep) X) Y"
          proof (rule notI)
            assume "(indep_system.indep_in (dual E indep) X) Y"
            from indep_system.indep_in_subset_carrier[OF \<open>indep_system E (dual E indep)\<close> this]
            have "Y \<subseteq> X" .
            with \<open>X \<subseteq> E\<close> have "Y \<subseteq> E" using subset_trans by blast
            with False show False by blast
          qed
          from not_indep' not_dual show ?thesis by simp
        qed
      qed
    qed

    have "indep_system.basis_in indep' X B \<longleftrightarrow> 
      indep_system.basis X (indep_system.indep_in indep' X) B"
      using indep_system.basis_in_def[OF \<open>indep_system E indep'\<close>] by simp
    also have "... \<longleftrightarrow> indep_system.basis X (indep_system.indep_in (dual E indep) X) B"
      using 1 by presburger
    also have "... \<longleftrightarrow> indep_system.basis_in (dual E indep) X B"
      using indep_system.basis_in_def[OF \<open>indep_system E (dual E indep)\<close>] by simp
    finally show "indep_system.basis_in indep' X B \<longleftrightarrow>
      indep_system.basis_in (dual E indep) X B" by blast
  qed

  then have "\<forall>X \<subseteq> E. indep_system.lower_rank_of indep' X =
    indep_system.lower_rank_of (dual E indep) X"
    using indep_system.lower_rank_of_def
      matroid.axioms(1)[OF \<open>matroid E indep'\<close>] matroid.axioms(1)[OF \<open>matroid E (dual E indep)\<close>]
    proof (intro allI impI)
      fix X
      assume "X \<subseteq> E"

      have basis_in_iff: "\<And>B. B \<subseteq> E \<Longrightarrow> indep_system.basis_in indep' X B \<longleftrightarrow>
        indep_system.basis_in (dual E indep) X B"
        using \<open>\<forall>X \<subseteq> E. \<forall>B \<subseteq> E. indep_system.basis_in indep' X B \<longleftrightarrow>
          indep_system.basis_in (dual E indep) X B\<close> \<open>X \<subseteq> E\<close>
        by blast

      have set_eq: "{card B | B. indep_system.basis_in indep' X B} =
        {card B | B. indep_system.basis_in (dual E indep) X B}"
      proof (rule equalityI)
        show "{card B | B. indep_system.basis_in indep' X B} \<subseteq>
              {card B | B. indep_system.basis_in (dual E indep) X B}"
        proof (rule subsetI)
          fix n
          assume "n \<in> {card B | B. indep_system.basis_in indep' X B}"
          then have "\<exists>B. n = card B \<and> indep_system.basis_in indep' X B" by auto
          then obtain B where n_def: "n = card B" and B_basis: "indep_system.basis_in indep' X B"
            by blast
          from indep_system.basis_in_subset_carrier[OF \<open>indep_system E indep'\<close> \<open>X \<subseteq> E\<close> B_basis]
          have "B \<subseteq> X" .
          with \<open>X \<subseteq> E\<close> have "B \<subseteq> E" by blast
          with basis_in_iff B_basis have "indep_system.basis_in (dual E indep) X B" by blast
          then show "n \<in> {card B | B. indep_system.basis_in (dual E indep) X B}"
            using n_def by auto
        qed
      next
        show "{card B | B. indep_system.basis_in (dual E indep) X B} \<subseteq>
              {card B | B. indep_system.basis_in indep' X B}"
        proof (rule subsetI)
          fix n
          assume "n \<in> {card B | B. indep_system.basis_in (dual E indep) X B}"
          then have "\<exists>B. n = card B \<and> indep_system.basis_in (dual E indep) X B" by auto
          then obtain B where n_def: "n = card B" and B_basis: "indep_system.basis_in (dual E indep) X B"
            by blast
          from indep_system.basis_in_subset_carrier[OF \<open>indep_system E (dual E indep)\<close> \<open>X \<subseteq> E\<close> B_basis]
          have "B \<subseteq> X" .
          with \<open>X \<subseteq> E\<close> have "B \<subseteq> E" by blast
          with basis_in_iff B_basis have "indep_system.basis_in indep' X B" by blast
          then show "n \<in> {card B | B. indep_system.basis_in indep' X B}"
            using n_def by auto
        qed
      qed

      have def1: "indep_system.lower_rank_of indep' X =
        Min {card B | B. indep_system.basis_in indep' X B}"
        using \<open>indep_system E indep'\<close> indep_system.lower_rank_of_def by blast
      have def2: "indep_system.lower_rank_of (dual E indep) X =
        Min {card B | B. indep_system.basis_in (dual E indep) X B}"
        using \<open>indep_system E (dual E indep)\<close> indep_system.lower_rank_of_def by blast

      show "indep_system.lower_rank_of indep' X = indep_system.lower_rank_of (dual E indep) X"
        unfolding def1 def2 using set_eq by simp
    qed

  with \<open>\<forall>X\<subseteq>E. ?q X = matroid.rank_of indep' X\<close>
  have "\<forall>X \<subseteq> E. matroid.rank_of (dual E indep) X = ?q X" by auto

  with \<open>matroid E (dual E indep)\<close>
  show ?thesis by auto
qed

lemma matroid_iff_dual_matroid:
  assumes "indep_system E indep"
  shows "matroid E indep \<longleftrightarrow> matroid E (dual E indep)"
proof (rule iffI)
  assume "matroid E indep"
  have fin: "finite E" using indep_system.carrier_finite[OF assms] .
  from matroid_dual_rank_expr[OF fin \<open>matroid E indep\<close>]
  show "matroid E (dual E indep)" by (rule conjunct1)
next
  assume "matroid E (dual E indep)"
  have fin: "finite E" using indep_system.carrier_finite[OF assms] .
  from matroid_dual_rank_expr[OF fin \<open>matroid E (dual E indep)\<close>]
  have "matroid E (dual E (dual E indep))" by (rule conjunct1)
  then show "matroid E indep" using dual_involution[OF assms] by simp
qed


(* --------------------------------------------------------------------------------------------- *)

section \<open>Additional theorems\<close>

(* The following theorem is relevant for invariant preservation proofs for the best-in greedy algorithm. *)

lemma set_take_aux_lemma:
  "l2 = x # xs \<Longrightarrow> l2 = drop (length l1 - length l2) l1 \<Longrightarrow> set (take (length l1 - length (tl l2)) l1) = 
    insert (hd l2) (set (take (length l1 - length l2) l1))"
proof-
  assume "l2 = x # xs" "l2 = drop (length l1 - length l2) l1"
  let ?j = "length l1 - length l2"

  from \<open>l2 = x # xs\<close> have "length l2 \<ge> 1" by auto
  from \<open>l2 = drop (length l1 - length l2) l1\<close> have "length l2 \<le> length l1"
  proof -
    have "length l2 = length (drop (length l1 - length l2) l1)"
      using \<open>l2 = drop (length l1 - length l2) l1\<close> by (rule arg_cong)
    also have "... = length l1 - (length l1 - length l2)"
      by (rule length_drop)
    finally have len_eq: "length l2 = length l1 - (length l1 - length l2)" .
    show "length l2 \<le> length l1"
    proof (subst len_eq)
      show "length l1 - (length l1 - length l2) \<le> length l1" by (rule diff_le_self)
    qed
  qed

  have "?j < length l1"
    using \<open>1 \<le> length l2\<close> \<open>length l2 \<le> length l1\<close> by linarith

  have "length l1 - length (tl l2) = (length l1 - length l2) + 1"
    using \<open>length l2 \<le> length l1\<close> \<open>length l2 \<ge> 1\<close>
    by (simp add: length_tl; linarith)
  moreover have "set (take (?j + 1) l1) = insert (hd (drop (?j) l1)) (set (take (?j) l1))"
    using take_hd_drop \<open>?j < length l1\<close>
  proof -
    have take_eq: "take (?j) l1 @ [hd (drop (?j) l1)] = take (Suc (?j)) l1"
      using take_hd_drop[OF \<open>?j < length l1\<close>] .
    have "set (take (Suc (?j)) l1) = set (take (?j) l1 @ [hd (drop (?j) l1)])"
      using take_eq by simp
    also have "... = insert (hd (drop (?j) l1)) (set (take (?j) l1))"
      by simp
    finally show ?thesis
      by simp
  qed
  then have "set (take (?j + 1) l1) = insert (hd l2) (set (take (?j) l1))"
    using \<open>l2 = drop (length l1 - length l2) l1\<close> by simp
  ultimately show ?thesis by auto
qed



context indep_system
begin

(* The following two theorems are relevant for an invariant preservation proof for the best-in greedy
algorithm. *)

lemma basis_in_preserved_indep:
  assumes "insert x X \<subseteq> carrier" "basis_in X B" "indep (insert x B)"
  shows "basis_in (insert x X) (insert x B)"
proof-
  from \<open>insert x X \<subseteq> carrier\<close> have "X \<subseteq> carrier" by auto
  from basis_in_indep_in[OF \<open>X \<subseteq> carrier\<close> \<open>basis_in X B\<close>]
  have "indep_in X B" .
  with indep_in_def have "B \<subseteq> X" by simp
  then have "(insert x B) \<subseteq> (insert x X)" by auto
  with \<open>indep (insert x B)\<close> indep_in_def have 
    indep_in: "indep_in (insert x X) (insert x B)" by blast

  from basis_in_max_indep_in[OF \<open>X \<subseteq> carrier\<close> \<open>basis_in X B\<close>]
  have "\<forall>y \<in> X - B. \<not>indep_in X (insert y B)" by blast
  moreover have "\<forall>y \<in> X - B. (insert y B) \<subseteq> X"
    using \<open>B \<subseteq> X\<close> by blast
  ultimately have
    "\<forall>y \<in> X - B. \<not>indep (insert y B)" using indep_in_def by auto

  have "B \<subseteq> (insert x B)" by auto
  with \<open>\<forall>y \<in> X - B. \<not>indep (insert y B)\<close> indep_subset have
    "\<forall>y \<in> X - B. \<not>indep (insert y (insert x B))" by blast
  then have "\<forall>y \<in> X - B. \<not>indep_in (insert x X) (insert y (insert x B))"
    using indep_in_def by blast
  then have indep_max:
    "\<forall>y \<in> (insert x X) - (insert x B). \<not>indep_in (insert x X) (insert y (insert x B))"
    by blast

  from \<open>(insert x X) \<subseteq> carrier\<close> indep_in indep_max 
  show "basis_in (insert x X) (insert x B)" 
    by (meson basis_inI basis_in_def)
qed

lemma basis_in_preserved_not_indep:
  assumes "insert x X \<subseteq> carrier" "basis_in X B" "\<not>indep (insert x B)"
  shows "basis_in (insert x X) B"
proof-
  from \<open>insert x X \<subseteq> carrier\<close> have "X \<subseteq> carrier" by auto
  from basis_in_indep_in[OF \<open>X \<subseteq> carrier\<close> \<open>basis_in X B\<close>]
  have "indep_in X B" .
  with indep_in_def have "B \<subseteq> X" by simp
  then have "B \<subseteq> (insert x X)" by auto

  from indep_in_indep[OF \<open>indep_in X B\<close>]
  have "indep B" .
  with \<open>B \<subseteq> (insert x X)\<close> indep_in_def have 
    indep_in: "indep_in (insert x X) B" by blast

  from basis_in_max_indep_in[OF \<open>X \<subseteq> carrier\<close> \<open>basis_in X B\<close>]
  have "\<forall>y \<in> X - B. \<not>indep_in X (insert y B)" by blast
  moreover have "\<forall>y \<in> X - B. (insert y B) \<subseteq> X"
    using \<open>B \<subseteq> X\<close> by blast
  ultimately have
    "\<forall>y \<in> X - B. \<not>indep (insert y B)" using indep_in_def by auto

  with \<open>\<not>indep (insert x B)\<close> have
    "\<forall>y \<in> (insert x X) - B. \<not>indep (insert y B)" by auto
  then have indep_max:
    "\<forall>y \<in> (insert x X) - B. \<not>indep_in (insert x X) (insert y B)"
    using indep_in_def by blast

  from \<open>insert x X \<subseteq> carrier\<close> indep_in indep_max
  show "basis_in (insert x X) B"
    by (meson basis_inI basis_in_def) 
qed

end

(* The following theorems are relevant for the final correctness proof of the greedy algorithm 
which proves the cost inequality for the greedy solution *)

lemma set_take_Suc_diff:
  assumes "set l = S" "length l = card S" "j < length l" 
  shows "{l ! j} = set (take (Suc j) l) - set (take j l)"
proof -
  have "distinct l" using assms(1) assms(2) card_distinct by force
  have take_eq: "take (Suc j) l = take j l @ [l ! j]"
    using take_Suc_conv_app_nth[OF assms(3)] .
  have l_j_notin: "l ! j \<notin> set (take j l)"
  proof
    assume "l ! j \<in> set (take j l)"
    from this[unfolded in_set_conv_nth]
    obtain i where i_lt: "i < length (take j l)" and eq: "take j l ! i = l ! j" by blast
    from i_lt assms(3) have i_less_j: "i < j" by simp
    from eq i_less_j assms(3) have l_eq: "l ! i = l ! j" by (simp add: nth_take)
    from i_less_j assms(3) have i_len: "i < length l" and j_len: "j < length l" by simp_all
    from nth_eq_iff_index_eq[OF \<open>distinct l\<close> i_len j_len] l_eq have "i = j" by simp
    with i_less_j show False by simp
  qed
  have "set (take (Suc j) l) = set (take j l) \<union> {l ! j}"
    using take_eq by simp
  with l_j_notin have "set (take (Suc j) l) - set (take j l) = {l ! j}"
    by auto
  then show ?thesis by simp
qed

lemma set_union_expr:
  assumes "n = length l" "set l = S" "length l = card S" "A \<subseteq> S"
  shows "A = (\<Union>j \<in> {1..(n::nat)}. (A \<inter> set (take j l)) - (A \<inter> set (take (j - 1) l)))"
proof-
  from set_take_Suc_diff[OF assms(2) assms(3)] assms(1)
  have "\<forall>j < n. {l ! j} = set (take (Suc j) l) - set (take j l)" by blast
  then have inter_diff_expr:
    "\<forall>j < n. A \<inter> {l ! j} = A \<inter> (set (take (Suc j) l) - set (take j l))" by blast

  from assms(1) have "set l = {l ! j | j. j < n}"
    by (simp add: set_conv_nth)
  then have "S = (\<Union>j \<in> {0..<n}. {l ! j})" 
    using assms(2) by auto
  then have "A \<inter> S = A \<inter> (\<Union>j \<in> {0..<n}. {l ! j})"
    by blast
  then have "A \<inter> S = (\<Union>j \<in> {0..<n}. A \<inter> {l ! j})"
    by blast
  then have "A = (\<Union>j \<in> {0..<n}. A \<inter> {l ! j})"
    using assms(4) by blast
  also have "... = (\<Union>j \<in> {0..<n}. A \<inter> ((set (take (Suc j) l)) - set (take j l)))"
    using inter_diff_expr by auto 
  also have "... = (\<Union>j \<in> {0..<n}. (A \<inter> set (take (Suc j) l)) - (A \<inter> set (take j l)))"
    by blast
  finally show ?thesis by fastforce
qed

lemma sum_inter_take_diff_expr:
  assumes "set l = S" "length l = card S" "A \<subseteq> S" "j \<ge> 1" "j - 1 < length l"
  shows "sum c (A \<inter> set (take j l) - A \<inter> set (take (j - 1) l)) = 
  rat_of_nat (card (A \<inter> set (take j l)) - card (A \<inter> set (take (j - 1) l))) * c (l ! (j - 1))"
proof-

  have "distinct l" using assms card_distinct by force

  from take_Suc_conv_app_nth[OF assms(5)]
  have set_take_diff_expr: "set (take j l) - set (take (j - 1) l) = {l ! (j - 1)}"
  proof -
    have j_eq: "Suc (j - 1) = j" using assms(4) by simp
    from set_take_Suc_diff[OF assms(1) assms(2) assms(5)]
    have "{l ! (j - 1)} = set (take (Suc (j - 1)) l) - set (take (j - 1) l)" .
    with j_eq show ?thesis by simp
  qed

  have card_diff_expr: "(card (A \<inter> set (take j l)) - card (A \<inter> set (take (j - 1) l))) =
    card (A \<inter> (set (take j l) - set (take (j - 1) l)))"
  proof -
    have subset_take: "set (take (j - 1) l) \<subseteq> set (take j l)"
    proof (rule set_take_subset_set_take)
      show "j - 1 \<le> j" by simp
    qed
    have subset_inter: "A \<inter> set (take (j - 1) l) \<subseteq> A \<inter> set (take j l)"
      using subset_take by blast
    have finite_inter: "finite (A \<inter> set (take (j - 1) l))" by simp
    have card_diff: "card (A \<inter> set (take j l) - A \<inter> set (take (j - 1) l)) =
      card (A \<inter> set (take j l)) - card (A \<inter> set (take (j - 1) l))"
      using card_Diff_subset[OF finite_inter subset_inter] .
    have set_eq: "A \<inter> set (take j l) - A \<inter> set (take (j - 1) l) =
      A \<inter> (set (take j l) - set (take (j - 1) l))"
      by blast
    have "card (A \<inter> set (take j l)) - card (A \<inter> set (take (j - 1) l)) =
      card (A \<inter> set (take j l) - A \<inter> set (take (j - 1) l))"
      using card_diff by simp
    also have "... = card (A \<inter> (set (take j l) - set (take (j - 1) l)))"
      using set_eq by simp
    finally show ?thesis .
  qed

  show ?thesis
  proof(cases "l ! (j - 1) \<in> A")
    case True
    from set_take_diff_expr True have "(A \<inter> set (take j l) - A \<inter> set (take (j - 1) l)) = {l ! (j - 1)}"
      by blast
    then have "sum c (A \<inter> set (take j l) - A \<inter> set (take (j - 1) l)) = c (l ! (j - 1))"
      by simp
    moreover have "(card (A \<inter> set (take j l)) - card (A \<inter> set (take (j - 1) l))) = 1" 
      using set_take_diff_expr True card_diff_expr by simp
    ultimately show ?thesis by auto
  next
    case False
    from set_take_diff_expr False have "(A \<inter> set (take j l) - A \<inter> set (take (j - 1) l)) = {}"
      by force
    then have "sum c (A \<inter> set (take j l) - A \<inter> set (take (j - 1) l)) = 0"
      unfolding \<open>A \<inter> set (take j l) - A \<inter> set (take (j - 1) l) = {}\<close>
      by simp
    moreover have "rat_of_nat (card (A \<inter> set (take j l)) - (card (A \<inter> set (take (j - 1) l)))) = 0"
      using set_take_diff_expr False card_diff_expr by auto
    ultimately show ?thesis by auto
  qed
qed

lemma all_inter_take_diff_pairs_disjoint:
  assumes "n = length l" "set l = S" "length l = card S" "G \<subseteq> S"
  shows "\<forall>i \<in> {1..n}. \<forall>j \<in> {1..n}. i \<noteq> j \<longrightarrow>
      ((G \<inter> set (take i l)) - (G \<inter> set (take (i - 1) l)))
      \<inter> ((G \<inter> set (take j l)) - (G \<inter> set (take (j - 1) l))) = {}"
proof-
  have "\<forall>i \<in> {1..n}. finite (set (take i l))" by blast
  then have sets_finite:
    "\<forall>i \<in> {1..n}. finite ((G \<inter> set (take i l)) - (G \<inter> set (take (i - 1) l)))" by blast

  from set_take_Suc_diff[OF assms(2) assms(3)] assms(1)
  have "\<forall>j < n. {l ! j} = set (take (Suc j) l) - set (take j l)" by blast
  then have
    "\<forall>j < n. G \<inter> (set (take (Suc j) l) - set (take j l)) \<subseteq> {l ! j}" by blast
  then have 1:
    "\<forall>j \<in> {1..n}. G \<inter> (set (take j l) - set (take (j - 1) l)) \<subseteq> {l ! (j - 1)}"
proof (intro ballI)
  fix j :: nat
  assume "j \<in> {1..n}"
  then have j_ge: "1 \<le> j" and j_le: "j \<le> n" by simp_all
  from j_ge have j_eq: "Suc (j - 1) = j" by arith
  from j_ge j_le have j1_lt_n: "j - 1 < n" by arith
  with \<open>\<forall>j < n. G \<inter> (set (take (Suc j) l) - set (take j l)) \<subseteq> {l ! j}\<close>
  have "G \<inter> (set (take (Suc (j - 1)) l) - set (take (j - 1) l)) \<subseteq> {l ! (j - 1)}"
    by blast
  with j_eq show "G \<inter> (set (take j l) - set (take (j - 1) l)) \<subseteq> {l ! (j - 1)}"
    by simp
qed

  from assms(2) assms(3) have "distinct l"
    by (simp add: card_distinct)
  with assms(1) nth_eq_iff_index_eq
  have "\<forall>i < n. \<forall>j < n. i \<noteq> j \<longrightarrow> l ! i \<noteq> l ! j" by blast
  then have
    2: "\<forall>i \<in> {1..n}. \<forall>j \<in> {1..n}. i \<noteq> j \<longrightarrow> l ! (i - 1) \<noteq> l ! (j - 1)"
    by auto

  from 1 2 have
    "\<forall>i \<in> {1..n}. \<forall>j \<in> {1..n}. i \<noteq> j \<longrightarrow> 
      (G \<inter> (set (take i l) - set (take (i - 1) l)))
      \<inter> (G \<inter> (set (take j l) - set (take (j - 1) l))) = {}" by blast
  then show
    "\<forall>i \<in> {1..n}. \<forall>j \<in> {1..n}. i \<noteq> j \<longrightarrow>
      ((G \<inter> set (take i l)) - (G \<inter> set (take (i - 1) l)))
      \<inter> ((G \<inter> set (take j l)) - (G \<inter> set (take (j - 1) l))) = {}" by fastforce
qed

lemma sum_set_union_expr:
  assumes "n = length l" "set l = S" "length l = card S" "G \<subseteq> S"
  shows "sum c G = (\<Sum>j \<in> {1..(n::nat)}.
    rat_of_nat (card (G \<inter> set (take j l)) - card (G \<inter> set (take (j - 1) l))) * c (l ! (j - 1)))"
proof-
  have "finite {1..n}" by blast
  have sets_finite: "\<forall>i \<in> {1..n}. finite ((G \<inter> set (take i l)) - (G \<inter> set (take (i - 1) l)))"
    by blast

  have aux: "\<forall>j \<in> {1..n}. sum c (G \<inter> set (take j l) - G \<inter> set (take (j - 1) l)) =
    rat_of_nat (card (G \<inter> set (take j l)) - card (G \<inter> set (take (j - 1) l))) * c (l ! (j - 1))"
    using sum_inter_take_diff_expr[OF assms(2) assms(3) assms(4)] assms(1)
    by auto

  have "sum c G = sum c (\<Union>j\<in>{1..n}. G \<inter> set (take j l) - G \<inter> set (take (j - 1) l))"
    using set_union_expr[OF assms] by simp
  also have "... = (\<Sum>j = 1..n. sum c (G \<inter> set (take j l) - G \<inter> set (take (j - 1) l)))"
    using sum.UNION_disjoint[OF \<open>finite {1..n}\<close> sets_finite all_inter_take_diff_pairs_disjoint[OF assms]]
    by blast
  also have "... = (\<Sum>j \<in> {1..(n::nat)}.
    rat_of_nat (card (G \<inter> set (take j l)) - card (G \<inter> set (take (j - 1) l))) * c (l ! (j - 1)))"
    using aux by simp
  finally show "sum c G = (\<Sum>j \<in> {1..(n::nat)}.
    rat_of_nat (card (G \<inter> set (take j l)) - card (G \<inter> set (take (j - 1) l))) * c (l ! (j - 1)))"
    by blast
qed


lemma sum_split_last:
  assumes "n \<ge> 1"
  shows "(\<Sum>j=1..(n - 1). g j) + g (n::nat) = (\<Sum>j=1..n. g j)"
  using assms
proof -
  from assms have n_eq: "n = Suc (n - 1)" by presburger
  have set_eq: "{1..Suc (n - 1)} = insert (Suc (n - 1)) {1..(n - 1)}" by auto
  have notin: "Suc (n - 1) \<notin> {1..(n - 1)}" by auto
  have "(\<Sum>j = 1..(n - 1). g j) + g n = (\<Sum>j = 1..(n - 1). g j) + g (Suc (n - 1))"
    by (rule arg_cong[OF n_eq])
  also have "... = g (Suc (n - 1)) + (\<Sum>j = 1..(n - 1). g j)" by (rule add.commute)
  also have "... = (\<Sum>j \<in> insert (Suc (n - 1)) {1..(n - 1)}. g j)"
    using sum.insert[OF finite_atLeastAtMost notin] by simp
  also have "... = (\<Sum>j = 1..Suc (n - 1). g j)"
    using set_eq by simp
  also have "... = (\<Sum>j = 1..n. g j)" by (rule arg_cong[OF n_eq, symmetric])
  finally show ?thesis .
qed

lemma sum_diff_mult_distr:
  assumes "\<forall>j \<in> {0..(n::nat)}. (g::(nat \<Rightarrow> rat)) j \<ge> 0" "\<forall>j \<in> {1..n}. c (j - 1) \<ge> 0" "g 0 = 0"
  shows 
    "(\<Sum>j \<in> {1..(n::nat)}. (g j - g (j - 1)) * c (j - 1)) =
    (\<Sum>j \<in> {1..n}. (g j) * (if j < n then c (j - 1) - c j else c (j - 1)))"
proof-
  have 1: "(\<Sum>j \<in> {1..(n::nat)}. (g j - g (j - 1)) * c (j - 1)) =
    (\<Sum>j \<in> {1..(n - 1)}. (g j) * (c (j - 1) - c j)) + g n * c (n - 1)"
  proof (induction n)
    case 0
    with assms(3) show ?case by auto
  next
    case (Suc n)
    have "(\<Sum>j \<in> {1..(Suc n)}. (g j - g (j - 1)) * c (j - 1)) =
    (\<Sum>j \<in> {1..(Suc n - 1)}. (g j - g (j - 1)) * c (j - 1)) + (g (Suc n) - g (Suc n - 1)) * c (Suc n - 1)"
      by force
    also have "... =
    (\<Sum>j \<in> {1..n}. (g j - g (j - 1)) * c (j - 1)) + (g (Suc n) - g (Suc n - 1)) * c (Suc n - 1)"
      by simp
    also have "... =
    (\<Sum>j = 1..n - 1. g j * (c (j - 1) - c j)) + g n * c (n - 1) + (g (Suc n) - g (Suc n - 1)) * c (Suc n - 1)"
      using Suc.IH by simp
    also have "... =
    (\<Sum>j = 1..n - 1. g j * (c (j - 1) - c j)) + g n * c (n - 1) + 
    g (Suc n) * c (Suc n - 1) - g (Suc n - 1) * c (Suc n - 1)"
      by algebra
    also have "... =
    (\<Sum>j = 1..n - 1. g j * (c (j - 1) - c j)) + g n * c (n - 1) + 
    g (Suc n) * c (Suc n - 1) - g n * c n"
      using Suc by simp
    also have "... =
    (\<Sum>j = 1..n - 1. g j * (c (j - 1) - c j)) + g n * (c (n - 1) - c n) + 
    g (Suc n) * c (Suc n - 1)"
      by algebra
    also have "... =
    (\<Sum>j = 1..n. g j * (c (j - 1) - c j)) + g (Suc n) * c (Suc n - 1)"
      using Suc
      proof (cases "n = 0")
        case True
        then show ?thesis by simp
      next
        case False
        then have "1 \<le> n" by simp
        from sum_split_last[OF this, of "\<lambda>j. g j * (c (j - 1) - c j)"]
        show ?thesis by simp
      qed
    also have "... =
    (\<Sum>j = 1..(Suc n - 1). g j * (c (j - 1) - c j)) + g (Suc n) * c (Suc n - 1)"
      by simp
    finally show ?case .
  qed

  have less: "\<forall>j \<in> {1..n - 1}. j < n" by auto
  have "(\<Sum>j \<in> {1..n}. (g j) * (if j < n then c (j - 1) - c j else c (j - 1))) =
    (\<Sum>j \<in> {1..n - 1}. (g j) * (if j < n then c (j - 1) - c j else c (j - 1)))
    + (g n) * (if n < n then c (n - 1) - c n else c (n - 1))"
proof (cases "n = 0")
  case True
  then show ?thesis using assms(3) by simp
next
  case False
  then have "1 \<le> n" by simp
  from sum_split_last[OF this, of "\<lambda>j. g j * (if j < n then c (j - 1) - c j else c (j - 1))"]
  show ?thesis by simp
qed
  also have "... = 
    (\<Sum>j \<in> {1..n - 1}. (g j) * (if j < n then c (j - 1) - c j else c (j - 1)))
    + (g n) * c (n - 1)"
    using less_not_refl by presburger
  also have "... = 
    (\<Sum>j \<in> {1..n - 1}. (g j) * (c (j - 1) - c j))
    + (g n) * c (n - 1)"
    using less by simp
  finally have 2: "(\<Sum>j \<in> {1..n}. (g j) * (if j < n then c (j - 1) - c j else c (j - 1))) = 
    (\<Sum>j \<in> {1..n - 1}. (g j) * (c (j - 1) - c j)) + (g n) * c (n - 1)" .

  from 1 2 show ?thesis by simp
qed



context indep_system
begin

lemma rank_quotient_geq_0:
  "rank_quotient \<ge> 0"
proof-
  have "finite carrier" using local.indep_system_axioms unfolding indep_system_def by blast

  let ?fracs = "{Frac (int (lower_rank_of X)) (int (upper_rank_of X)) | X. X \<subseteq> carrier}"
  have "?fracs \<noteq> {}" by blast
  have "finite ?fracs" using `finite carrier` by auto

  have 1: "rank_quotient = Min {Frac (int (lower_rank_of X)) (int (upper_rank_of X)) | X. X \<subseteq> carrier}"
    unfolding rank_quotient_def using upper_rank_equiv_rank by (metis (no_types, opaque_lifting))

  have "\<forall>X \<subseteq> carrier. int (lower_rank_of X) \<ge> 0"
    by simp
  moreover have "\<forall>X \<subseteq> carrier. int (upper_rank_of X) \<ge> 0"
    by simp
  ultimately have 2: "\<forall>X \<subseteq> carrier. Frac (int (lower_rank_of X)) (int (upper_rank_of X)) \<ge> 0"
  proof (intro allI impI)
    fix X
    assume X_subset: "X \<subseteq> carrier"
    show "Frac (int (lower_rank_of X)) (int (upper_rank_of X)) \<ge> 0"
    proof (cases "lower_rank_of X = upper_rank_of X")
      case True
      then show ?thesis unfolding Frac_def by simp
    next
      case False
      from lower_rank_le_upper_rank[OF X_subset]
      have le: "lower_rank_of X \<le> upper_rank_of X" .
      have lt: "lower_rank_of X < upper_rank_of X"
        using le False by linarith
      have upper_pos: "0 < upper_rank_of X"
        using lt by linarith
      have pos: "(0::int) < int (upper_rank_of X)"
        using upper_pos by simp
      have nonneg: "(0::int) \<le> int (lower_rank_of X)" by simp
      have fract_nonneg: "0 \<le> Fract (int (lower_rank_of X)) (int (upper_rank_of X))"
        using zero_le_Fract_iff[OF pos] nonneg by simp
      from fract_nonneg False show ?thesis unfolding Frac_def by simp
    qed
  qed

  from 1 2 Min_ge_iff[OF `finite ?fracs` `?fracs \<noteq> {}`] show ?thesis by auto
qed


lemma lower_rank_of_leq_card_basis_in:
  assumes "X \<subseteq> carrier" "basis_in X B"
  shows "lower_rank_of X \<le> card B"
proof-
  from collect_basis_in_finite[OF assms(1)]
  have "finite {card B |B. basis_in X B}" by auto
  moreover have "card B \<in> {card B |B. basis_in X B}" using assms(2) by fast
  ultimately show ?thesis using lower_rank_of_def by auto
qed


lemma rank_geq_card_indep_in:
  assumes "X \<subseteq> carrier" "indep_in X Y"
  shows "rank X \<ge> card Y"
proof-
  from indep_in_def have "finite {card Y | Y. indep_in X Y}"
  proof -
    have "\<forall>n \<in> {card Y | Y. indep_in X Y}. n \<le> card carrier"
    proof
      fix n
      assume "n \<in> {card Y | Y. indep_in X Y}"
      then obtain Y where "n = card Y" "indep_in X Y" by blast
      from indep_in_subset_carrier[OF this(2)] have "Y \<subseteq> X" .
      with assms(1) have "Y \<subseteq> carrier" by blast
      from card_mono[OF carrier_finite \<open>Y \<subseteq> carrier\<close>] have "card Y \<le> card carrier" .
      with \<open>n = card Y\<close> show "n \<le> card carrier" by simp
    qed
    then show "finite {card Y | Y. indep_in X Y}"
      using finite_nat_set_iff_bounded_le by blast
  qed
  moreover have "card Y \<in> {card Y | Y. indep_in X Y}" using assms(2) by fast 
  ultimately show ?thesis using rank_def by auto
qed


lemma lower_rank_geq_rank_quotient_prod_rank:
  assumes "X \<subseteq> carrier"
  shows "(rat_of_nat (lower_rank_of X)) \<ge> rank_quotient * (rat_of_nat (rank X))"
proof-

  have "finite carrier" using carrier_finite by blast

  let ?fracs = "{Frac (int (lower_rank_of X)) (int (rank X)) | X. X \<subseteq> carrier}"
  have "?fracs \<noteq> {}" by blast
  have "finite ?fracs" using `finite carrier` by auto

  from assms Min_le_iff[OF `finite ?fracs` `?fracs \<noteq> {}`]
  have rank_quotient_leq: "rank_quotient \<le> Frac (int (lower_rank_of X)) (int (rank X))"
    unfolding rank_quotient_def by auto

  then show ?thesis
  proof (cases "lower_rank_of X = rank X")
    case True
    then show ?thesis using rank_quotient_leq_1
      by (simp add: mult_left_le_one_le rank_quotient_geq_0)
  next
    case False
    with rank_quotient_leq 
    have "rank_quotient \<le> Fract (int (lower_rank_of X)) (int (rank X))"
      by (simp add: Frac_def)

    have "(rat_of_nat (rank X)) \<ge> 0" by simp
    moreover have "rank_quotient \<le> (rat_of_nat (lower_rank_of X)) / (rat_of_nat (rank X))"
      using \<open>rank_quotient \<le> Fract (int (lower_rank_of X)) (int (rank X))\<close>
      by (simp add: Fract_of_int_quotient)
    then show ?thesis
    proof (cases "rank X = 0")
      case True
      then show ?thesis by simp
    next
      case False
      then have rank_pos: "rat_of_nat (rank X) > 0" by (simp add: of_nat_0_less_iff)
      from pos_le_divide_eq[OF rank_pos, of rank_quotient "rat_of_nat (lower_rank_of X)"]
        \<open>rank_quotient \<le> rat_of_nat (lower_rank_of X) / rat_of_nat (rank X)\<close>
      show ?thesis by simp
    qed
  qed
qed



end



(* These theorems are relevant for the proof of BestInGreedy_bound_tight1 (Theorem 13.19, pt 2) *)

context indep_system
begin

lemma ex_rank_quotient_frac:
  "\<exists>F B1 B2. F \<subseteq> carrier \<and> basis_in F B1 \<and> basis_in F B2 \<and> card B1 \<le> card B2 \<and>
  Frac (int (card B1)) (int (card B2)) = rank_quotient"
proof-
  let ?fracs = "{Frac (int (lower_rank_of X)) (int (rank X)) | X. X \<subseteq> carrier}"
  have "?fracs \<noteq> {}" by blast
  have "finite ?fracs" using carrier_finite by auto

  from Min_in[OF `finite ?fracs` `?fracs \<noteq> {}`]
  have rank_quotient_leq: "\<exists>X. X \<subseteq> carrier \<and> 
    Frac (int (lower_rank_of X)) (int (rank X)) = rank_quotient"
    unfolding rank_quotient_def by auto
  then obtain X where X: "X \<subseteq> carrier" "Frac (int (lower_rank_of X)) (int (rank X)) = rank_quotient"
    by blast

  let ?basis_cards = "{card B | B. basis_in X B}"
  from \<open>X \<subseteq> carrier\<close> basis_in_ex have "?basis_cards \<noteq> {}" by simp
  from \<open>X \<subseteq> carrier\<close> collect_basis_in_finite finite_imageI have "finite ?basis_cards" by simp
  from Min_in[OF `finite ?basis_cards` `?basis_cards \<noteq> {}`]
  have "\<exists>B1. basis_in X B1 \<and> card B1 = lower_rank_of X"
    unfolding lower_rank_of_def by auto
  then obtain B1 where B1: "basis_in X B1" "card B1 = lower_rank_of X" by blast

  from Max_in[OF `finite ?basis_cards` `?basis_cards \<noteq> {}`]
  have "\<exists>B2. basis_in X B2 \<and> card B2 = upper_rank_of X"
    unfolding upper_rank_of_def by auto
  then obtain B2 where B2: "basis_in X B2" "card B2 = rank X"
    using upper_rank_equiv_rank[OF \<open>X \<subseteq> carrier\<close>] by auto

  from \<open>card B1 = lower_rank_of X\<close> \<open>card B2 = rank X\<close>
  have "card B1 \<le> card B2" 
  proof -
    have "lower_rank_of X \<le> upper_rank_of X" using lower_rank_le_upper_rank[OF X(1)] .
    also have "upper_rank_of X = rank X" using upper_rank_equiv_rank[OF X(1)] .
    finally show "card B1 \<le> card B2"
      using \<open>card B1 = lower_rank_of X\<close> \<open>card B2 = rank X\<close> by simp
  qed
  have "Frac (int (card B1)) (int (card B2)) = rank_quotient"
    using X(2) B1(2) B2(2) by simp
  with X(1) B1(1) B2(1) \<open>card B1 \<le> card B2\<close>
  show ?thesis by blast
qed

lemma rank_quotient_greater_0:
  "rank_quotient > 0"
proof (rule ccontr, goal_cases)
  case 1
  with rank_quotient_geq_0 have "rank_quotient = 0" by auto

  from ex_rank_quotient_frac obtain F B1 B2 where
    "F \<subseteq> carrier" "basis_in F B1" "basis_in F B2"
    "Frac (int (card B1)) (int (card B2)) = rank_quotient" by blast
  with \<open>rank_quotient = 0\<close> Frac_def
  have "(int (card B1)) \<noteq> (int (card B2))"
    by auto
  with \<open>Frac (int (card B1)) (int (card B2)) = rank_quotient\<close> Frac_def
  have "rank_quotient = Fract (int (card B1)) (int (card B2))" by simp

  with rank_quotient_leq_1 have "card B1 \<le> card B2" (* unclean, TODO change *)
  proof -
    from \<open>rank_quotient = Fract (int (card B1)) (int (card B2))\<close> rank_quotient_leq_1
    have le1: "Fract (int (card B1)) (int (card B2)) \<le> 1" by simp
    show "card B1 \<le> card B2"
    proof (cases "card B2 = 0")
      case True
      have "B2 = {}"
        using True \<open>F \<subseteq> carrier\<close> \<open>basis_in F B2\<close> basis_in_finite by auto
      with basis_in_max_indep_in[OF \<open>F \<subseteq> carrier\<close> \<open>basis_in F B2\<close>]
      have "\<forall>x \<in> F. \<not> indep_in F {x}" by simp
      then have not_indep: "\<forall>x \<in> F. \<not> indep {x}" using indep_in_def by blast
      have "B1 = {}"
      proof (rule ccontr)
        assume "B1 \<noteq> {}"
        then obtain x where "x \<in> B1" by blast
        from basis_in_subset_carrier[OF \<open>F \<subseteq> carrier\<close> \<open>basis_in F B1\<close>] have "B1 \<subseteq> F" .
        with \<open>x \<in> B1\<close> have "x \<in> F" by blast
        from indep_in_indep[OF basis_in_indep_in[OF \<open>F \<subseteq> carrier\<close> \<open>basis_in F B1\<close>]] have "indep B1" .
        with indep_subset \<open>x \<in> B1\<close> have "indep {x}" by auto
        with not_indep \<open>x \<in> F\<close> show False by blast
      qed
      with \<open>B2 = {}\<close> show ?thesis by simp
    next
      case False
      then have pos_b: "int (card B2) > 0" by simp
      from le1 pos_b have "int (card B1) \<le> int (card B2)"
        by (simp add: Fract_le_one_iff)
      then show ?thesis by simp
    qed
  qed

  with \<open>(int (card B1)) \<noteq> (int (card B2))\<close>
  have "card B1 < card B2" by simp

  with \<open>rank_quotient = Fract (int (card B1)) (int (card B2))\<close>  \<open>rank_quotient = 0\<close>
  have "card B1 = 0"
  proof -
    have B2_pos: "card B2 > 0" using \<open>card B1 < card B2\<close> by simp
    then have B2_nonzero: "of_int (int (card B2)) \<noteq> (0::rat)" by simp
    have "Fract (int (card B1)) (int (card B2)) = 0"
      using \<open>rank_quotient = Fract (int (card B1)) (int (card B2))\<close> \<open>rank_quotient = 0\<close> by simp
    then have "of_int (int (card B1)) / of_int (int (card B2)) = (0::rat)"
      by (simp add: Fract_of_int_quotient)
    with B2_nonzero have "of_int (int (card B1)) = (0::rat)"
      by (simp add: divide_eq_0_iff)
    then show "card B1 = 0" by simp
  qed

  with \<open>card B1 < card B2\<close>
  have "card B2 > 0" by simp


  from \<open>card B1 = 0\<close> have "B1 = {}"
    using \<open>F \<subseteq> carrier\<close> \<open>basis_in F B1\<close> basis_in_finite by auto

  with basis_in_max_indep_in[OF \<open>F \<subseteq> carrier\<close> \<open>basis_in F B1\<close>] 
  have "\<forall>x \<in> F. \<not> indep_in F {x}" by simp
  then have "\<forall>x \<in> F. \<not>indep {x}" using indep_in_def by blast

  from \<open>card B2 > 0\<close> have "\<exists>x. x \<in> B2"
  proof -
    from \<open>card B2 > 0\<close> have "B2 \<noteq> {}" by auto
    then show "\<exists>x. x \<in> B2" by blast
  qed
  then obtain x where "x \<in> B2" by blast

  from indep_in_indep[OF basis_in_indep_in[OF \<open>F \<subseteq> carrier\<close> \<open>basis_in F B2\<close>]]
  have "indep B2" .
  with indep_subset \<open>x \<in> B2\<close> have "indep {x}" by auto 

  from \<open>x \<in> B2\<close> basis_in_subset_carrier[OF \<open>F \<subseteq> carrier\<close> \<open>basis_in F B2\<close>]
  have "x \<in> F" by auto

  from \<open>\<forall>x \<in> F. \<not>indep {x}\<close> \<open>indep {x}\<close> \<open>x \<in> F\<close>
  show ?case by blast
qed


end


lemma bound_tight_set_aux:
  "F \<subseteq> carrier' \<Longrightarrow> B1 \<subseteq> F \<Longrightarrow>
    B1 \<subseteq> X \<Longrightarrow> X \<subseteq> carrier' - (F - B1) \<Longrightarrow> (\<exists>Y. X = Y \<union> B1 \<and> Y \<subseteq> carrier' - F)"
proof -
  assume "F \<subseteq> carrier'" and "B1 \<subseteq> F" and "B1 \<subseteq> X" and "X \<subseteq> carrier' - (F - B1)"
  have "X = (X - B1) \<union> B1"
    using \<open>B1 \<subseteq> X\<close> by blast
  moreover have "X - B1 \<subseteq> carrier' - F"
  proof
    fix x
    assume "x \<in> X - B1"
    then have "x \<in> X" and "x \<notin> B1" by auto
    with \<open>X \<subseteq> carrier' - (F - B1)\<close> have "x \<in> carrier'" and "x \<notin> F - B1" by auto
    then have "x \<notin> F" using \<open>x \<notin> B1\<close> by auto
    with \<open>x \<in> carrier'\<close> show "x \<in> carrier' - F" by auto
  qed
  ultimately show "\<exists>Y. X = Y \<union> B1 \<and> Y \<subseteq> carrier' - F" by blast
qed

lemma sorted_aux1:
  "distinct xs \<Longrightarrow> sorted_wrt (\<lambda>x1 x2. c x1 \<ge> c x2) xs \<Longrightarrow> (\<forall>x. c x = 1 \<or> c x = 0) \<Longrightarrow>
  length (filter (\<lambda>y. (c::('a \<Rightarrow> rat)) y = 1) xs) = k \<Longrightarrow> k \<le> length xs \<Longrightarrow> \<forall>i < k. c (xs ! i) = 1"
proof (rule ccontr, goal_cases)
  case 1
  then have "\<exists>i < k. c (xs ! i) \<noteq> 1" by blast
  then obtain i where "i < k" "c (xs ! i) \<noteq> 1" by blast
  with \<open>(\<forall>x. c x = 1 \<or> c x = 0)\<close> have "c (xs ! i) = 0" by blast

  from \<open>k \<le> length xs\<close> \<open>\<exists>i < k. c (xs ! i) \<noteq> 1\<close>
  have "\<exists>x \<in> set (take k xs). c x \<noteq> 1" using nth_image
    by fastforce
  then have "length (filter (\<lambda>y. c y = 1) (take k xs)) < k"
    using length_filter_less by fastforce

  with \<open>length (filter (\<lambda>y. c y = 1) xs) = k\<close> append_take_drop_id[of k xs] filter_append
  have "length (filter (\<lambda>y. c y = 1) (drop k xs)) \<ge> 1"
proof -
  have filter_eq: "filter (\<lambda>y. c y = 1) xs =
    filter (\<lambda>y. c y = 1) (take k xs) @ filter (\<lambda>y. c y = 1) (drop k xs)"
  proof -
    have "xs = take k xs @ drop k xs" by (simp add: append_take_drop_id)
    then show ?thesis by (subst \<open>xs = take k xs @ drop k xs\<close>) (rule filter_append)
  qed
  have len_eq: "length (filter (\<lambda>y. c y = 1) xs) =
    length (filter (\<lambda>y. c y = 1) (take k xs)) + length (filter (\<lambda>y. c y = 1) (drop k xs))"
    using filter_eq by simp
  show "length (filter (\<lambda>y. c y = 1) (drop k xs)) \<ge> 1"
    using len_eq \<open>length (filter (\<lambda>y. c y = 1) xs) = k\<close>
      \<open>length (filter (\<lambda>y. c y = 1) (take k xs)) < k\<close>
    by linarith
qed

  then have "card (set (filter (\<lambda>y. c y = 1) (drop k xs))) \<ge> 1"
  proof -
    from \<open>distinct xs\<close> have "distinct (drop k xs)" by (rule distinct_drop)
    then have "distinct (filter (\<lambda>y. c y = 1) (drop k xs))" by (rule distinct_filter)
    then have "card (set (filter (\<lambda>y. c y = 1) (drop k xs))) =
      length (filter (\<lambda>y. c y = 1) (drop k xs))" by (rule distinct_card)
    with \<open>length (filter (\<lambda>y. c y = 1) (drop k xs)) \<ge> 1\<close>
    show ?thesis by simp
  qed
  with set_filter
  have "card ({x \<in> set (drop k xs). c x = 1}) \<ge> 1" by simp
  with drop_eq_nths[of k xs] set_nths[of xs]
  have "card ({x \<in> {xs ! i |i. i < length xs \<and> i \<in> {i. k \<le> i}}. c x = 1}) \<ge> 1" by simp
  then have "\<exists>j. j \<ge> k \<and> j < length xs \<and> c (xs ! j) = 1"
  proof -
    have "{x \<in> {xs ! i |i. i < length xs \<and> i \<in> {i. k \<le> i}}. c x = 1} \<noteq> {}"
    proof
      assume "{x \<in> {xs ! i |i. i < length xs \<and> i \<in> {i. k \<le> i}}. c x = 1} = {}"
      then have "card ({x \<in> {xs ! i |i. i < length xs \<and> i \<in> {i. k \<le> i}}. c x = 1}) = 0" by simp
      with \<open>card ({x \<in> {xs ! i |i. i < length xs \<and> i \<in> {i. k \<le> i}}. c x = 1}) \<ge> 1\<close>
      show False by linarith
    qed
    then obtain x where "x \<in> {xs ! i |i. i < length xs \<and> i \<in> {i. k \<le> i}}" and "c x = 1"
      by auto
    then obtain j where "x = xs ! j" "j < length xs" "k \<le> j"
      by blast
    with \<open>c x = 1\<close> show ?thesis by auto
  qed
  then obtain j where "j \<ge> k" "j < length xs" "c (xs ! j) = 1" by blast

  from \<open>i < k\<close> \<open>j \<ge> k\<close> have "i < j" by auto

  from sorted_wrt_nth_less[OF \<open>sorted_wrt (\<lambda>x1 x2. c x1 \<ge> c x2) xs\<close> \<open>i < j\<close> \<open>j < length xs\<close>]
  have "c (xs ! i) \<ge> c (xs ! j)" by simp

  with \<open>c (xs ! i) = 0\<close> \<open>c (xs ! j) = 1\<close>
  show ?case by simp
qed

lemma sorted_aux2:
  "distinct xs \<Longrightarrow> sorted_wrt (\<lambda>x1 x2. c x1 \<ge> c x2) xs \<Longrightarrow> (\<forall>x. c x = 1 \<or> c x = 0) \<Longrightarrow>
  length (filter (\<lambda>y. (c::('a \<Rightarrow> rat)) y = 1) xs) = k \<Longrightarrow> k \<le> length xs \<Longrightarrow>
  \<forall>i \<ge> k. i < length xs \<longrightarrow> c (xs ! i) = 0"
proof (rule ccontr, goal_cases)
  case 1
  then have "\<exists>i. i \<ge> k \<and> i < length xs \<and> c (xs ! i) \<noteq> 0" by blast
  then obtain i where "i \<ge> k" "i < length xs" "c (xs ! i) \<noteq> 0" by blast
  with \<open>(\<forall>x. c x = 1 \<or> c x = 0)\<close> have "c (xs ! i) = 1" by blast

  from sorted_aux1[OF 1(1-5)]
  have "\<forall>i < k. c (xs ! i) = 1" by simp

  from length_filter_conv_card[of "(\<lambda>y. c y = 1)" xs] \<open>length (filter (\<lambda>y. c y = 1) xs) = k\<close>
  have "card {i. i < length xs \<and> c (xs ! i) = 1} = k" by simp

  from \<open>k \<le> length xs\<close> \<open>\<forall>i < k. c (xs ! i) = 1\<close> \<open>i < length xs\<close> \<open>c (xs ! i) = 1\<close>
  have "{0..<k} \<union> {i} \<subseteq> {i | i. i < length xs \<and> c (xs ! i) = 1}" by auto
  moreover have "card ({0..<k} \<union> {i}) = k + 1" using \<open>i \<ge> k\<close> by simp
  moreover have "finite {i | i. i < length xs \<and> c (xs ! i) = 1}" by simp
  ultimately have "card {i | i. i < length xs \<and> c (xs ! i) = 1} \<ge> k + 1"
    using card_mono[of "{i |i. i < length xs \<and> c (xs ! i) = 1}" "{0..<k} \<union> {i}"]
    by auto

  from \<open>card {i. i < length xs \<and> c (xs ! i) = 1} = k\<close>
    \<open>card {i | i. i < length xs \<and> c (xs ! i) = 1} \<ge> k + 1\<close>
  show ?case by simp
qed

lemma sorted_aux3:
  "\<lbrakk>distinct xs; xs = ys @ zs; \<And>x. x \<in> set xs \<Longrightarrow> (x \<in> set ys \<longleftrightarrow> P x)\<rbrakk> \<Longrightarrow> ys = filter P xs"
proof -
  assume dist: "distinct xs"
  assume decomp: "xs = ys @ zs"
  assume mem_iff: "\<And>x. x \<in> set xs \<Longrightarrow> (x \<in> set ys \<longleftrightarrow> P x)"

  have distinct_ys_zs: "distinct (ys @ zs)" using dist decomp by simp
  have disjoint: "set ys \<inter> set zs = {}" using distinct_ys_zs by (auto simp: distinct_append)

  have ys_sub: "set ys \<subseteq> set xs" using decomp by auto
  have zs_sub: "set zs \<subseteq> set xs" using decomp by auto

  have all_ys_P: "\<forall>x \<in> set ys. P x"
  proof
    fix x
    assume "x \<in> set ys"
    with ys_sub mem_iff show "P x" by blast
  qed

  have none_zs_P: "\<forall>x \<in> set zs. \<not> P x"
  proof
    fix x
    assume "x \<in> set zs"
    with disjoint have "x \<notin> set ys" by blast
    with zs_sub \<open>x \<in> set zs\<close> mem_iff show "\<not> P x" by blast
  qed

  have filter_ys: "filter P ys = ys" using all_ys_P filter_id_conv by blast
  have filter_zs: "filter P zs = []" using none_zs_P filter_empty_conv by blast

  have filter_eq: "filter P xs = ys"
    using decomp filter_ys filter_zs by simp

  from filter_eq show "ys = filter P xs" by simp
qed

lemma member_filter: "(x \<in> Set.filter P A) = (x \<in> A \<and> P x)"
  by simp

lemma sorted_aux4:
  "\<lbrakk>distinct xs; xs = (filter P xs) @ ys\<rbrakk> \<Longrightarrow> ys = (filter (\<lambda>x. \<not> P x) xs)"
proof -
  assume dist: "distinct xs" and split: "xs = filter P xs @ ys"

  from dist split have "distinct (filter P xs @ ys)" by simp
  then have disjoint: "set (filter P xs) \<inter> set ys = {}"
    by (simp add: distinct_append)

  have subset_ys: "set ys \<subseteq> set xs" by (subst split) simp

  have not_P: "\<forall>y \<in> set ys. \<not> P y"
  proof
    fix y
    assume "y \<in> set ys"
    show "\<not> P y"
    proof
      assume "P y"
      from \<open>y \<in> set ys\<close> subset_ys have "y \<in> set xs" by blast
      with \<open>P y\<close> have "y \<in> set (filter P xs)" by simp
      with disjoint \<open>y \<in> set ys\<close> show False by blast
    qed
  qed

  have filter_ys: "filter (\<lambda>x. \<not> P x) ys = ys"
    using not_P by (simp add: filter_id_conv)

  have all_P: "\<forall>x \<in> set (filter P xs). P x" by auto

  have step2: "filter (\<lambda>x. \<not> P x) (filter P xs) = []"
    using all_P by (simp add: filter_empty_conv)

  have "filter (\<lambda>x. \<not> P x) xs = filter (\<lambda>x. \<not> P x) (filter P xs) @ filter (\<lambda>x. \<not> P x) ys"
    by (subst split) (simp add: filter_append)
  also have "\<dots> = [] @ filter (\<lambda>x. \<not> P x) ys"
    using step2 by simp
  also have "\<dots> = ys"
    using filter_ys by simp
  finally have "filter (\<lambda>x. \<not> P x) xs = ys" .
  then show "ys = filter (\<lambda>x. \<not> P x) xs" by simp
qed


lemma sorted_aux5:
  assumes "distinct xs" "sorted_wrt (\<lambda>x1 x2. c x1 \<ge> c x2) xs" "(\<forall>x. c x = 1 \<or> c x = 0)"
    "length (filter (\<lambda>y. (c::('a \<Rightarrow> rat)) y = 1) xs) = k" "k \<le> length xs"
  shows "xs = (filter (\<lambda>y. c y = 1) xs) @ (filter (\<lambda>y. c y \<noteq> 1) xs)"
proof-
  from sorted_aux1[OF assms] sorted_aux2[OF assms] assms(3)
  have "\<forall>i < length xs. i < k \<longleftrightarrow> c (xs ! i) = 1"
  proof -
    show "\<forall>i < length xs. i < k \<longleftrightarrow> c (xs ! i) = 1"
    proof (rule allI, rule impI)
      fix i
      assume "i < length xs"
      show "(i < k) = (c (xs ! i) = 1)"
      proof (cases "i < k")
        case True
        then have "c (xs ! i) = 1" using sorted_aux1[OF assms] by blast
        with True show ?thesis by simp
      next
        case False
        then have "i \<ge> k" by simp
        with sorted_aux2[OF assms] \<open>i < length xs\<close> have "c (xs ! i) = 0" by blast
        with False show ?thesis by simp
      qed
    qed
  qed

  then have "\<And>x. x \<in> set xs \<Longrightarrow> (x \<in> set (take k xs) \<longleftrightarrow> c x = 1)"
  proof-
    fix x
    assume "x \<in> set xs"
    then have "\<exists>i. i < length xs \<and> xs ! i = x"
      by (simp add: in_set_conv_nth)

    show "(x \<in> set (take k xs) \<longleftrightarrow> c x = 1)"
    proof -
      obtain i where i_len: "i < length xs" and xs_i: "xs ! i = x"
        using \<open>\<exists>i<length xs. xs ! i = x\<close> by blast
      have iff_i: "(i < k) = (c (xs ! i) = 1)"
        using \<open>\<forall>i<length xs. (i < k) = (c (xs ! i) = 1)\<close> i_len by blast
      show "(x \<in> set (take k xs) \<longleftrightarrow> c x = 1)"
      proof
        assume "x \<in> set (take k xs)"
        then have "\<exists>j<length (take k xs). take k xs ! j = x"
          by (simp add: in_set_conv_nth)
        then obtain j where j_len: "j < length (take k xs)" and take_j: "take k xs ! j = x"
          by blast
        from j_len have j_lt_k: "j < k" and j_lt_len: "j < length xs"
          using length_take[of k xs] by auto
        from take_j j_lt_k have xs_j: "xs ! j = x"
          by (simp add: nth_take)
        have eq_ij: "xs ! i = xs ! j" using xs_i xs_j by simp
        from nth_eq_iff_index_eq[OF assms(1) i_len j_lt_len] eq_ij have "i = j" by simp
        with j_lt_k iff_i xs_i show "c x = 1" by simp
      next
        assume "c x = 1"
        with iff_i xs_i have i_lt_k: "i < k" by simp
        with i_len have i_lt_take: "i < length (take k xs)"
          using length_take[of k xs] by auto
        from i_lt_k xs_i have "take k xs ! i = x"
          by (simp add: nth_take)
        with i_lt_take have "\<exists>j<length (take k xs). take k xs ! j = x" by blast
        then show "x \<in> set (take k xs)"
          by (simp add: in_set_conv_nth)
      qed
    qed
  qed

  from append_take_drop_id[of k xs]
  have take_drop: "xs = take k xs @ drop k xs"
    by simp

  from sorted_aux3[OF assms(1) take_drop] \<open>\<And>x. x \<in> set xs \<Longrightarrow> (x \<in> set (take k xs) \<longleftrightarrow> c x = 1)\<close>
  have "take k xs = filter (\<lambda>y. c y = 1) xs" by auto

  with take_drop
  have "xs = (filter (\<lambda>y. c y = 1) xs) @ (drop k xs)" by auto
  from sorted_aux4[OF assms(1) this]
  have "drop k xs = filter (\<lambda>x. c x \<noteq> 1) xs" by simp
  with \<open>take k xs = filter (\<lambda>y. c y = 1) xs\<close> take_drop
  show "xs = (filter (\<lambda>y. c y = 1) xs) @ (filter (\<lambda>y. c y \<noteq> 1) xs)" by auto
qed






(* ---------------------------------------------------------------------------------------------- *)
(* The following theorems currently do not seem to be relevant *)

context matroid
begin

lemma indep_in_extend_to_basis_in:
  assumes "X \<subseteq> carrier"
  shows "card A = rank_of X - n \<Longrightarrow> n \<le> rank_of X \<Longrightarrow> indep_in X A \<Longrightarrow>
    \<exists>B. A \<inter> B = {} \<and> basis_in X (A \<union> B)"
proof (induction n arbitrary: A)
  case 0
  from 0 basis_in_iff_rank_of[OF assms]
  have "basis_in X A"
  proof -
    from 0 have indepXA: "indep_in X A" by blast
    from indep_in_subset_carrier[OF indepXA] have A_subset: "A \<subseteq> X" .
    from indep_in_iff_rank_of[OF assms A_subset] indepXA
    have rank_A_eq_card: "rank_of A = card A" by blast
    from 0 have "card A = rank_of X - 0" by blast
    then have card_A_eq: "card A = rank_of X" by simp
    from rank_A_eq_card card_A_eq have rank_eq: "rank_of A = rank_of X" by simp
    from basis_in_iff_rank_of[OF assms A_subset] indepXA rank_A_eq_card rank_eq
    show "basis_in X A" by blast
  qed
  then show ?case by fastforce
next
  case (Suc n)
  from Suc have "\<exists>A'. indep_in X A' \<and> card A' = rank_of X - n"
  proof -
    from Suc.prems(1) have card_A: "card A = rank_of X - Suc n" by simp
    from Suc.prems(2) have le_Suc: "Suc n \<le> rank_of X" by simp
    from Suc.prems(3) have indep_A: "indep_in X A" by simp

    have rank_eq: "rank_of X = card A + Suc n"
    proof -
      from le_Suc have "rank_of X - Suc n + Suc n = rank_of X"
        by (rule le_add_diff_inverse2)
      with card_A show ?thesis by simp
    qed

    have not_basis: "\<not> basis_in X A"
    proof
      assume basis_A: "basis_in X A"
      from rank_of_eq_card_basis_in[OF assms basis_A] have "rank_of X = card A" .
      with rank_eq show False by simp
    qed

    from indep_in_not_basis_in[OF assms indep_A not_basis]
    obtain x where x_mem: "x \<in> X - A" and indep_Ax: "indep_in X (insert x A)"
      by blast

    from indep_in_subset_carrier[OF indep_A] have "A \<subseteq> X" .
    with assms have A_subset_carrier: "A \<subseteq> carrier" by blast

    have carrier_fin: "finite carrier"
      using indep_system.carrier_finite[OF indep_system_axioms] .
    from carrier_fin A_subset_carrier have finite_A: "finite A"
      using finite_subset by blast

    from x_mem have x_notin: "x \<notin> A" by blast
    with finite_A have card_insert: "card (insert x A) = card A + 1"
      by (simp add: card_insert_disjoint)

    have card_next: "card A + 1 = rank_of X - n"
    proof -
      from rank_eq have "rank_of X - n = card A + Suc n - n" by simp
      also have "... = card A + 1" by simp
      finally show ?thesis by simp
    qed

    with card_insert have "card (insert x A) = rank_of X - n" by simp

    with indep_Ax show "\<exists>A'. indep_in X A' \<and> card A' = rank_of X - n" by blast
  qed
  then obtain A' where "indep_in X A'" "card A' = rank_of X - n" by blast

  from this(2) Suc(2) augment_aux_indep_in[OF assms \<open>indep_in X A'\<close> \<open>indep_in X A\<close>]
  have "\<exists>x \<in> A' - A. indep_in X (insert x A)"
  proof -
    have "card A' = Suc (card A)"
      using Suc.prems(1) Suc.prems(2) \<open>card A' = rank_of X - n\<close> by linarith
    from augment_aux_indep_in[OF assms \<open>indep_in X A'\<close> \<open>indep_in X A\<close> this]
    show "\<exists>x \<in> A' - A. indep_in X (insert x A)" .
  qed
  then obtain x where "x \<in> A' - A" "indep_in X (insert x A)" by blast

  with Suc.prems(1) have "card (insert x A) = rank_of X - n"
    by (metis DiffE Suc.prems(2) Suc.prems(3) Suc_diff_le card_insert_disjoint diff_Suc_Suc indep_finite
        indep_system.indep_in_def indep_system_axioms)

  from Suc.prems(2) have "n \<le> rank_of X" by auto

  from Suc.IH[OF \<open>card (insert x A) = rank_of X - n\<close> this \<open>indep_in X (insert x A)\<close>]
  have "\<exists>B. insert x A \<inter> B = {} \<and> basis_in X (insert x A \<union> B)" .
  then obtain B where "insert x A \<inter> B = {}" "basis_in X (insert x A \<union> B)" by blast

  with \<open>x \<in> A' - A\<close> have "A \<inter> ({x} \<union> B) = {}" by blast
  from \<open>basis_in X (insert x A \<union> B)\<close> have "basis_in X (A \<union> ({x} \<union> B))" by auto

  from \<open>A \<inter> ({x} \<union> B) = {}\<close> \<open>basis_in X (A \<union> ({x} \<union> B))\<close>
  show ?case by blast
qed

end

(* This lemma and its proof are taken from Lemma 2.1.2 in Matroid Theory (2nd ed.) by James Oxley *)
lemma basis_augment_alt:
  assumes
    "finite E"
    "matroid E indep"
    "indep_system.basis E indep B1" "indep_system.basis E indep B2" "x \<in> B2 - B1"
  shows "\<exists>y \<in> B1 - B2. indep_system.basis E indep (insert x (B1 - {y}))"
proof-
  from matroid.axioms(1) assms(2) have "indep_system E indep" by blast 

  from \<open>x \<in> B2 - B1\<close> \<open>indep_system.basis E indep B2\<close> have "x \<in> E - B1"
    by (metis DiffD1 DiffD2 DiffI assms(2) indep_system.basis_subset_carrier matroid.axioms(1) subsetD)
  from matroid.basis_ex1_supset_circuit[OF assms(2) assms(3) this] 
  have unique_circuit: "\<exists>!C. indep_system.circuit E indep C \<and> C \<subseteq> insert x B1" .
  then obtain C where "indep_system.circuit E indep C" "C \<subseteq> insert x B1" by blast

  have "C - B2 \<noteq> {}"
  proof (rule ccontr, goal_cases False)
    case False
    then have "C \<subseteq> B2" by auto
    with indep_system.indep_iff_subset_basis[OF `indep_system E indep`] assms(4)
    have "indep C" by auto
    with \<open>indep_system.circuit E indep C\<close> show ?case 
      using \<open>indep_system E indep\<close> indep_system.circuit_dep by blast
  qed    

  then have "\<exists>y. y \<in> C - B2" by auto
  then obtain y where "y \<in> C - B2" by blast

  have "y \<in> B1 - B2" using \<open>y \<in> C - B2\<close> \<open>C \<subseteq> insert x B1\<close>
    using assms(5) by blast

  from assms(3) assms(5) \<open>y \<in> C - B2\<close> have "(insert x (B1 - {y})) \<subseteq> E"
    by (metis DiffD1 \<open>indep_system E indep\<close> \<open>x \<in> E - B1\<close> \<open>y \<in> B1 - B2\<close> indep_system.basis_subset_carrier
        insert_Diff insert_subset)

  have "\<not> C \<subseteq> (insert x (B1 - {y}))" using \<open>x \<in> B2 - B1\<close> \<open>y \<in> C - B2\<close> by blast

  have "\<forall>C'. indep_system.circuit E indep C' \<longrightarrow> \<not> C' \<subseteq> (insert x (B1 - {y}))"
  proof (rule allI, rule impI)
    fix C'
    assume "indep_system.circuit E indep C'"
    show "\<not> C' \<subseteq> (insert x (B1 - {y}))"
    proof(cases "C' = C")
      case True
      with \<open>\<not> C \<subseteq> (insert x (B1 - {y}))\<close> show ?thesis by simp
    next
      case False
      with unique_circuit \<open>indep_system.circuit E indep C\<close> \<open>C \<subseteq> insert x B1\<close>
        \<open>indep_system.circuit E indep C'\<close>
      have "\<not> C' \<subseteq> (insert x B1)" by force

      then show ?thesis by blast
    qed
  qed

  with indep_system.dep_iff_supset_circuit[OF \<open>indep_system E indep\<close> \<open>(insert x (B1 - {y})) \<subseteq> E\<close>]
  have "indep (insert x (B1 - {y}))"
    by blast

  have "card B1 = card (insert x (B1 - {y}))"
    using \<open>x \<in> B2 - B1\<close> \<open>y \<in> C - B2\<close>
    by (metis Diff_iff \<open>C \<subseteq> insert x B1\<close> \<open>indep (insert x (B1 - {y}))\<close> \<open>indep_system E indep\<close>
        card.remove card_insert_if finite.emptyI finite_Diff2 finite_insert in_mono
        indep_system.indep_finite insert_iff)

  from matroid.card_eq_basis[OF assms(2) assms(3) `indep (insert x (B1 - {y}))` this]
  have "indep_system.basis E indep (insert x (B1 - {y}))" .

  with \<open>y \<in> B1 - B2\<close> show ?thesis by blast
qed




end
