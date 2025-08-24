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
    by (smt (verit) card_mono finite_nat_set_iff_bounded_le indep_in_def indep_subset_carrier mem_Collect_eq)

  have "\<forall>n. (upper_rank_of X = n) \<longleftrightarrow> (rank X = n)"
  proof
    fix n
    have upper_rank_eq_iff: "(n = upper_rank_of X) \<longleftrightarrow> 
      (\<exists>Y. basis_in X Y \<and> card Y = n \<and> (\<forall>Y'. basis_in X Y' \<longrightarrow> card Y \<ge> card Y'))"
      unfolding upper_rank_of_def using Max_eq_iff[OF `finite ?basis_cards` `?basis_cards \<noteq> {}`]
      by (smt (verit, del_insts) mem_Collect_eq)

    have rank_eq_iff: "(n = rank X) \<longleftrightarrow> 
      (\<exists>Y. indep_in X Y \<and> card Y = n \<and> (\<forall>Y'. indep_in X Y' \<longrightarrow> card Y \<ge> card Y'))"
      unfolding rank_def using Max_eq_iff[OF `finite ?indep_cards` `?indep_cards \<noteq> {}`]
      by (smt (verit, del_insts) mem_Collect_eq)

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
          by (metis DiffD2 \<open>indep_in X Y\<close> assms card_insert_disjoint finite_subset 
              indep_in_subset_carrier indep_system.carrier_finite indep_system_axioms lessI)

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
        by (metis DiffD2 DiffI basis_in_max_indep_in ex_X indep_in_subset_carrier insert_subset)
    next
      case 2
      from LTR `indep B1` `indep B2` 2 have "\<exists>x \<in> B1 - B2. indep (insert x B2)" by blast
      with `B1 \<subseteq> X` `B2 \<subseteq> X` have "\<exists>x \<in> B1 - B2. indep_in X (insert x B2)"
        by (simp add: in_mono indep_in_def)
      with ex_B1_B2 show ?thesis
        by (metis DiffD2 DiffI basis_in_max_indep_in ex_X indep_in_subset_carrier insert_subset)
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
      by (metis nat_neq_iff)

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
      show ?case by (metis nat_neq_iff)
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
    unfolding rank_quotient_def using upper_rank_equiv_rank by (metis (no_types, opaque_lifting))

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
    by (smt (verit, del_insts) mem_Collect_eq)
  also have "...
    \<longleftrightarrow> (\<forall>X \<subseteq> carrier. Min {card B | B. basis_in X B} = Max {card B | B. basis_in X B})"
    by (smt (verit, del_insts) Max.bounded_iff Max_eq_iff Min_eq_iff bases_X_finite bases_X_nonempty)
  also have "...
    \<longleftrightarrow> (\<forall>X \<subseteq> carrier. int (Min {card B | B. basis_in X B}) = int (Max {card B | B. basis_in X B}))"
    by simp
  also have "...
    \<longleftrightarrow> (\<forall>X \<subseteq> carrier. 
    Frac (int (Min {card B | B. basis_in X B})) (int (Max {card B | B. basis_in X B})) = 1)"
    by (smt (verit, best) Frac_def One_rat_def eq_rat(1) eq_rat(2) mult.commute mult_cancel_right)
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
    using upper_rank_equiv_rank arg_cong by (smt (verit, best) Collect_cong)
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
      by (metis Diff_iff assms(4) assms(6) nth_mem)
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
          by (metis \<open>i < card (J - K)\<close> card_distinct distinct_take id_take_nth_drop not_distinct_conv_prefix)
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
      by (metis distinct_card finite_distinct_list)
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
      have "l ! j \<in> J" by (metis Diff_iff nth_mem)
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
      by (metis Diff_Diff_Int Diff_disjoint Un_Diff_Int card_Un_disjoint finite_Diff) 
    also have "... \<le>  p * card (J - K) + card (K \<inter> J)"
      using \<open>card (K - J) \<le> p * card (J - K)\<close> by auto
    also have "... = p * card (J - K) + p * card (K \<inter> J) - p * card (K \<inter> J) + card (K \<inter> J)"
      by auto
    also have "... = p * card J - p * card (K \<inter> J) + card (K \<inter> J)"
      by (simp add: Int_commute \<open>finite J\<close> card_Diff_subset_Int right_diff_distrib')
    also have "... = p * card J - (p - 1) * card (K \<inter> J)"
      using \<open>p * card J \<ge> p * card (K \<inter> J)\<close> 
      by (smt (verit) Nat.add_diff_assoc \<open>1 \<le> p\<close> diff_diff_cancel diff_le_self le_add_diff_inverse2
          left_diff_distrib' nat_mult_1)
    also have "... \<le> p * card J" by auto
    finally show "card K \<le> p * card J" .
  qed

  let ?fracs = "{Frac (int (lower_rank_of X)) (int (upper_rank_of X)) | X. X \<subseteq> carrier}"
  have "?fracs \<noteq> {}" by blast
  from carrier_finite have "finite ?fracs" by auto

  from Min_in[OF \<open>finite ?fracs\<close> \<open>?fracs \<noteq> {}\<close>]
  have "\<exists>F \<subseteq> carrier. Frac (int (lower_rank_of F)) (int (upper_rank_of F)) = Min ?fracs"
    by (smt (verit, best) mem_Collect_eq)
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
    by metis
  moreover have "rank_quotient = Min ?fracs"
    unfolding rank_quotient_def using upper_rank_equiv_rank by (metis (no_types, opaque_lifting))
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
  by (metis basis_iff_rank_of basis_subset_carrier indep_iff_rank_of indep_subset_carrier) 

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
    by (smt (verit, best) finite_subset mem_Collect_eq subsetI)

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
        have "card (insert x B) = Suc (card B)" by metis
        with `B' \<in> S` assms show "\<not>(insert x B) \<subseteq> B'"
          by (metis `B \<in> S` Suc_n_not_le_n card_mono infinite_super)
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
        by (metis all_not_in_conv insert_absorb insert_subset)
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
  using assms all_cards_equal_member_iff
  by (smt (verit, del_insts) subset_trans)

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
    by (metis Un_assoc)

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
  then have "... \<ge> card (X - Y)" using assms 
    by (metis Diff_triv \<open>card (X - Y - B2) \<le> card (B1 - B2)\<close> inf.commute)
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
        by (metis DiffD1 basis_B1 card_Diff1_less indep_sys indep_system.basis_finite)

      from indep_p indep_B1_x indep_B2 matroid.augment card_less
      have "\<exists>y\<in>B2 - (B1 - {x}). indep (insert y (B1 - {x}))" by blast
      with `x \<in> B1 - B2` 
      have "\<exists>y\<in>B2 - B1. indep (insert y (B1 - {x}))" by blast

      then obtain y where y_p: "y \<in> B2 - B1 \<and> indep (insert y (B1 - {x}))" by blast

      from y_p `x \<in> B1 - B2` have "card (insert y (B1 - {x})) = card B1"
        by (metis DiffD1 DiffD2 basis_B1 card.remove card_insert_disjoint finite_Diff indep_sys
            indep_system.basis_finite)

      with basis_B1 y_p indep_p have "indep_system.basis E indep (insert y (B1 - {x}))"
        by (metis matroid.card_eq_basis)

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
        by (metis B2 Diff_Diff_Int Diff_empty Diff_eq_empty_iff all_not_in_conv ex_B1_B2
            inf.absorb_iff2 less_not_refl)
      then obtain x where ex_x: "x \<in> B1 - B2" by blast
      from B2 ex_B1_B2 ex_x have "(\<exists>y. y \<in> B2 - B1 \<and> insert y (B1 - {x}) \<in> \<B>)" by blast
      then obtain y where ex_y: "y \<in> B2 - B1 \<and> insert y (B1 - {x}) \<in> \<B>" by blast

      from card_greater have card_insert_greater: 
        "card (insert y (B1 - {x})) > card B2"
        by (metis DiffD1 DiffD2 bot_nat_0.extremum_strict card.infinite card.remove
            card_insert_disjoint ex_x ex_y finite_Diff)

      from ex_y have card_inter_greater: "card ((insert y (B1 - {x})) \<inter> B2) > card (B1 \<inter> B2)"
        by (metis (no_types, lifting) DiffD1 DiffD2 Int_insert_left_if0 Int_insert_left_if1 
            card.infinite card_greater ex_x finite_Int finite_insert inf_le1 insert_Diff psubset_card_mono 
            psubset_insert_iff subsetD subset_insert subset_insertI)

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
        (\<forall>x\<in>E - B. \<not> (insert x B \<subseteq> E \<and> \<not> (\<forall>B'. B' \<in> \<B> \<longrightarrow> \<not> insert x B \<subseteq> B'))))" by metis
    then have
      "\<forall>B. (B \<in> \<B>) = ((B \<subseteq> E \<and> (\<exists>B'\<in>\<B>. B \<subseteq> B')) \<and> 
        (\<forall>x\<in>E - B. \<not> (insert x B \<subseteq> E \<and> (\<exists>B' \<in> \<B>. insert x B \<subseteq> B'))))" by metis
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
          have "finite B1" using ex_B1_B2 assms finite_subset
            by (metis all_subset_E)
          have "finite B2" using ex_B1_B2 assms finite_subset
            by (metis all_subset_E)

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
          have 5: "card (X - Y) > card (Y - X)" by (metis finite_subset lessI) 

          from `finite B1` `finite B2` ex_B1_B2 card_mono Diff_mono 
          have 6: "card (Y - X) \<ge> card (Y - B1)" by (metis equalityD1 finite_Diff finite_subset)

          from 5 6 have 7: "card (X - Y) > card (Y - B1)" by simp

          from 4 7 have "card ((B2 - B1) - Y) > 0" by linarith
          then have "\<exists>y. y \<in> (B2 - B1) - Y"
            by (metis all_not_in_conv card_gt_0_iff)
          then obtain y where ex_y: "y \<in> (B2 - B1) - Y" by blast
          with ex_B1_B2 have y_in: "y \<in> (B2 - B1)" by blast

          from B2 y_in ex_B1_B2
          have "(\<exists>x. x \<in> B1 - B2 \<and> insert x (B2 - {y}) \<in> \<B>)" by blast
          then obtain x where ex_x: "x \<in> B1 - B2 \<and> insert x (B2 - {y}) \<in> \<B>" by blast

          from ex_x have card_inter_greater: "card (B1 \<inter> (insert x (B2 - {y}))) > card (B1 \<inter> B2)"
            by (metis DiffD2 Int_Diff_Un Int_commute Int_insert_right_if0 Int_insert_right_if1 UnCI 
                \<open>finite B1\<close> finite_Int insertCI insert_Diff psubsetI psubset_card_mono subset_insertI y_in)

          with ex_B1_B2 show ?case
            by (metis DiffD1 DiffD2 ex_x ex_y insert_Diff linorder_not_less subset_insert subset_insertI subset_trans)
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
    from assms(2) show "r X \<le> card X"
      by (metis \<open>0 = card X\<close> \<open>X \<subseteq> E\<close> assms(1) card_0_eq infinite_super nle_le)
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
    then show "P X" using assms(1) card_subset_eq finite_subset
      by (metis assms(3) minus_nat.diff_0)
  qed
next
  case (Suc n)
  show ?case
  proof ((rule impI)+)
    assume "Suc n \<le> card Y" "card X = card Y - Suc n" "X \<subseteq> Y" "P Y"
    then have
      "\<exists>X' x. x \<notin> X \<and> X' = (insert x X) \<and> X' \<subseteq> Y"
      by (metis Diff_eq_empty_iff assms(1) assms(3) card_Diff_subset card_gt_0_iff diff_diff_cancel
          finite_subset insert_subsetI subsetI zero_less_Suc)
    then obtain X' x where "x \<notin> X" "X' = (insert x X)" "X' \<subseteq> Y" by blast
    with \<open>card X = card Y - Suc n\<close>
    have "card X' = card Y - n"
      by (metis Suc_diff_le \<open>Suc n \<le> card Y\<close> \<open>X \<subseteq> Y\<close> assms(1) assms(3) card_insert_disjoint
          diff_Suc_Suc finite_subset)

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
        by (metis assms(1) assms(2) card_eq_0_iff finite_Diff finite_subset sup_bot.right_neutral)
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
          by (metis \<open>A \<subseteq> X - Y\<close> card_1_singletonE in_mono insertCI)
      next
        case False
        with Pos have "n \<ge> 2" by auto
        with \<open>n = card A\<close> have "\<exists>x y. x \<in> A \<and> y \<in> A \<and> x \<noteq> y"
          by (metis One_nat_def Suc_1 \<open>A \<subseteq> X - Y\<close> assms(1) assms(2) card_le_Suc0_iff_eq finite_Diff
              finite_subset not_less_eq_eq)
        then obtain x y where "x \<in> A" "y \<in> A" "x \<noteq> y" by blast

        from \<open>n \<ge> 2\<close> have "n - 1 < n" by simp
        from \<open>n \<ge> 2\<close> have "n - 2 < n" by simp

        from \<open>x \<in> A\<close> \<open>y \<in> A\<close> \<open>x \<noteq> y\<close> \<open>n = card A\<close> have "n - 1 = card (A - {x})" by simp
        from \<open>A \<subseteq> X - Y\<close> have "(A - {x}) \<subseteq> X - Y" by blast
        from \<open>n - 1 < n\<close> \<open>n - 1 = card (A - {x})\<close> \<open>(A - {x}) \<subseteq> X - Y\<close> less.IH
        have "r (Y \<union> (A - {x})) = r Y" by blast
        then have r_A_sub_y: "r ((Y \<union> (A - {x, y})) \<union> {y}) = r Y"
          by (metis (no_types, opaque_lifting) DiffI Diff_insert2 Un_insert_left \<open>x \<noteq> y\<close> \<open>y \<in> A\<close>
              emptyE insertE insert_Diff_single insert_absorb sup.commute sup_bot.left_neutral)

        from \<open>x \<in> A\<close> \<open>y \<in> A\<close> \<open>x \<noteq> y\<close> \<open>n = card A\<close> have "n - 1 = card (A - {y})" by simp
        from \<open>A \<subseteq> X - Y\<close> have "(A - {y}) \<subseteq> X - Y" by blast
        from \<open>n - 1 < n\<close> \<open>n - 1 = card (A - {y})\<close> \<open>(A - {y}) \<subseteq> X - Y\<close> less.IH
        have "r (Y \<union> (A - {y})) = r Y" by blast
        then have r_A_sub_x: "r ((Y \<union> (A - {x, y})) \<union> {x}) = r Y"
          by (smt (verit, ccfv_threshold) Diff_idemp Diff_insert2 Diff_insert_absorb Un_Diff Un_assoc
              \<open>x \<in> A\<close> \<open>x \<noteq> y\<close> insert_Diff insert_is_Un singleton_iff sup.commute)

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
          by (metis Un_Diff_cancel2 \<open>x \<in> A\<close> \<open>y \<in> A\<close> bot.extremum insert_subsetI sup.order_iff sup_assoc)
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
    then show "r X \<le> r Y"
      by (metis assms(1) assms(2) card_subset_eq diff_zero dual_order.eq_iff finite_subset)
  qed
next
  case (Suc n)
  show ?case
  proof ((rule impI)+)
    assume "Suc n \<le> card Y" "card X = card Y - Suc n" "X \<subseteq> Y"
    then have
      "\<exists>X' x. x \<notin> X \<and> X' = (insert x X) \<and> X' \<subseteq> Y"
      by (metis Diff_eq_empty_iff assms(1) assms(2) card_Diff_subset card_gt_0_iff diff_diff_cancel
          finite_subset insert_subsetI subsetI zero_less_Suc)
    then obtain X' x where "x \<notin> X" "X' = (insert x X)" "X' \<subseteq> Y" by blast
    with \<open>card X = card Y - Suc n\<close>
    have "card X' = card Y - n"
      by (metis Suc_diff_le \<open>Suc n \<le> card Y\<close> \<open>X \<subseteq> Y\<close> assms(1) assms(2) card_insert_disjoint
          diff_Suc_Suc finite_subset)

    from \<open>Suc n \<le> card Y\<close> have "n \<le> card Y" by auto

    from Suc.IH this \<open>card X' = card Y - n\<close> \<open>X' \<subseteq> Y\<close>
    have "r X' \<le> r Y" by blast

    from \<open>X' = (insert x X)\<close> assms(3)
    have "r X \<le> r X'"
      by (metis Un_commute \<open>X' \<subseteq> Y\<close> assms(2) insert_is_Un insert_subset subset_trans)

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
  by (smt (verit, best) Int_Un_eq(1) Un_subset_iff)

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
        by (metis One_nat_def R1 Un_subset_iff \<open>X \<subseteq> E\<close> \<open>y \<in> E\<close> add_left_mono card.empty
            card_insert_disjoint empty_iff finite.emptyI insert_subset sup_bot.right_neutral)
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
        by (metis Un_insert_right Un_upper1 insert_subset sup_bot.right_neutral)

      have "r X + r (X \<union> {x, y}) \<le> r (X \<union> {x}) + r (X \<union> {y})"
        using R3 \<open>X \<subseteq> E\<close> \<open>x \<in> E\<close> \<open>y \<in> E\<close> un_sets int_sets
        by (metis Un_empty_right Un_insert_right add.commute insert_subsetI)
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
      by (metis Suc_eq_plus1 \<open>X \<subseteq> E\<close> \<open>y \<notin> X\<close> assms(1) card_insert_disjoint finite_subset)
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
    by (metis assms(1) card_mono diff_diff_cancel diff_le_self finite_subset)

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
        by (metis DiffD2 Suc_eq_plus1 \<open>?indep Y\<close> assms(1) card_insert_disjoint finite_subset)
      then have "\<forall>x \<in> X - Y. r (insert x Y) \<le> card Y"
        by force

      from R2' \<open>?indep Y\<close> have "\<forall>x \<in> X - Y. r (insert x Y) \<ge> card Y"
        by (metis DiffD1 Un_commute \<open>?indep X\<close> insert_is_Un subsetD)
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
          by (metis \<open>X \<subseteq> Y\<close> \<open>Y \<subseteq> E\<close> assms(1) card_mono diff_diff_cancel rev_finite_subset)

        from R2' have R2'_part: "\<forall>X\<subseteq>E. \<forall>y\<in>E. r X \<le> r (X \<union> {y})" by auto

        from rank_axioms2_imp_subset_rank_leq[OF assms(1) \<open>Y \<subseteq> E\<close> R2'_part]
          \<open>?n \<le> card Y\<close> \<open>card X = card Y - ?n\<close> \<open>X \<subseteq> Y\<close>
        show "r X \<le> r Y" by blast
      qed

      from rank_axioms2_imp_rank_eq_subsets[OF assms(1) \<open>X \<subseteq> E\<close> \<open>Y \<subseteq> E\<close> rank_Y_un_x_eq_Y R3'] 
      have "r Y = r (Y \<union> (X - Y))"
        by (metis subset_refl)
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
      by (smt (verit, del_insts) DiffD1 Diff_eq_empty_iff \<open>X \<subseteq> E\<close> indep_sys_props
          indep_system.basis_in_max_indep_in indep_system.basis_in_subset_carrier indep_system.indep_in_def
          insert_Diff_if)

    with \<open>X \<subseteq> E\<close> \<open>Y \<subseteq> X\<close>
    have "\<forall>x \<in> X - Y. (r (insert x Y) \<noteq> card (insert x Y))"
      by blast
    with rank_leq_card \<open>X \<subseteq> E\<close> \<open>Y \<subseteq> X\<close>
    have "\<forall>x \<in> X - Y. (r (insert x Y) < card (insert x Y))"
      by (metis Diff_iff dual_order.trans insert_subsetI order_less_le)
    then have "\<forall>x \<in> X - Y. (r (insert x Y) < card Y + 1)"
      by (metis DiffD2 Suc_eq_plus1 \<open>X \<subseteq> E\<close> \<open>Y \<subseteq> X\<close> assms(1) card_insert_if rev_finite_subset)
    then have "\<forall>x \<in> X - Y. (r (Y \<union> {x}) \<le> card Y)" by force
    with \<open>r Y = card Y\<close>
    have "\<forall>x \<in> X - Y. (r (Y \<union> {x}) \<le> r Y)" by auto
    with R2' \<open>X \<subseteq> E\<close> \<open>Y \<subseteq> X\<close>
    have "\<forall>x \<in> X - Y. (r (Y \<union> {x}) = r Y)"
      by (meson DiffD1 dual_order.eq_iff subsetD subset_trans)

    from rank_axioms2_imp_rank_eq_subsets[OF assms(1) \<open>X \<subseteq> E\<close> \<open>Y \<subseteq> E\<close> this R3']
    have "r (Y \<union> X) = r Y"
      by (metis Un_Diff_cancel dual_order.refl)
    with \<open>Y \<subseteq> X\<close>
    have "r X = r Y"
      by (simp add: sup.absorb_iff2)
    with \<open>r Y = card Y\<close>
    have "r X = card Y" by simp

    have "matroid.rank_of ?indep X = Min {card B | B. indep_system.basis_in ?indep X B}"
      using matroid.rank_of_def[OF matroid_props] by auto
    also have "... = card Y"
      using matroid.basis_in_card[OF matroid_props \<open>X \<subseteq> E\<close>] Y_basis_in
      by (metis (no_types, lifting) \<open>X \<subseteq> E\<close> calculation matroid.rank_of_eq_card_basis_in matroid_props)
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
  using assms by (smt (verit) basis_in_iff_rank_of basis_in_subset_carrier subset_trans)

lemma rank_of_circuit:
  assumes "circuit X"
  shows "rank_of X = card X - 1"
  by (metis all_not_in_conv assms card_Diff_singleton circuit_imp_circuit_in circuit_in_iff_rank_of
      circuit_in_subset_carrier subset_refl)

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
    subgoal by (metis subset_trans)
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
    by (metis DiffD1 card_Diff_singleton)

  from \<open>C2 \<subseteq> E\<close> \<open>e \<in> C1 \<inter> C2\<close> have "(C2 - {e}) \<subseteq> E" by blast
  from indep_system.circuit_def[OF indep_sys] C2_circuit \<open>e \<in> C1 \<inter> C2\<close>
  have "indep (C2 - {e})" by blast
  with matroid.indep_iff_rank_of[OF assms(1) \<open>(C2 - {e}) \<subseteq> E\<close>] \<open>e \<in> C1 \<inter> C2\<close>
  have C2_minus_e_rank: "matroid.rank_of indep (C2 - {e}) = card C2 - 1"
    by (metis IntD2 card_Diff_singleton)

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
    by (smt (verit) \<open>\<not> card ?circuits \<le> 1\<close> card_insert_le is_singletonI is_singletonI'
        is_singleton_altdef verit_comp_simplify1(2))
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
  apply (metis assms empty_subsetI indep_system.basis_ex inf_bot_left)
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
    with indep_system.basis_def[OF dual_indep_sys] dual_def show ?thesis by metis
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
      with \<open>B' = E - B\<close> have "B'' = B" 
        by (metis Diff_eq_empty_iff Int_Diff \<open>indep_system.basis E indep B''\<close>
            \<open>indep_system.basis E indep B\<close> assms(1) indep_system.basis_subset_carrier
            indep_system.basis_subset_eq inf.orderE)
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
    (X \<subseteq> E \<and> (\<exists>B'. indep_system.basis E (dual E indep) B' \<and> (X \<inter> B' = {})))" using dual_def by metis
  also have "... =
    (X \<subseteq> E \<and> (\<exists>B. indep_system.basis E indep B \<and> (X \<inter> (E - B) = {})))"
    using dual_basis_complement[OF assms] indep_system.basis_subset_carrier
    by (metis Diff_subset dual_indep_sys)
  also have "... =
    (X \<subseteq> E \<and> (\<exists>B. indep_system.basis E indep B \<and> X \<subseteq> B))"
    by auto
  also have "... = indep X" using indep_system.indep_iff_subset_basis[OF assms]
    by (metis assms indep_system_def)
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
    by (metis assms(1) card.empty empty_subsetI indep_system.indep_empty matroid.axioms(1)
        matroid.indep_iff_rank_of) 

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
    by (metis assms(2) card.empty empty_subsetI indep_system.indep_empty matroid.axioms(1)
        matroid.indep_iff_rank_of)   

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
    then have "matroid.rank_of indep (E - X) + matroid.rank_of indep ({}) \<le>
      matroid.rank_of indep (E - Y) + matroid.rank_of indep (Y - X)"
      by (metis Diff_disjoint Int_Diff inf_commute)
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
      by (metis \<open>X \<subseteq> E\<close> assms(1) card_Diff_subset rev_finite_subset)
    then have
      "card X + matroid.rank_of indep (E - X) \<le> card Y + matroid.rank_of indep (E - Y)"
      by (smt (verit, ccfv_SIG) Nat.diff_cancel \<open>X \<subseteq> Y\<close> \<open>Y \<subseteq> E\<close> assms(1) card_mono diff_cancel2
          diff_diff_cancel diff_le_mono infinite_super le_antisym nat_le_linear)

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
      by (metis \<open>X \<subseteq> E\<close> \<open>Y \<subseteq> E\<close> assms(1) card_Un_Int rev_finite_subset)
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
      using dual_rank_well_def
      by (metis \<open>X \<subseteq> E\<close> assms(2) diff_add_inverse diff_add_inverse2 diff_diff_cancel)
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
        then show ?thesis using indep_system.indep_in_def[OF \<open>indep_system E indep'\<close>]
            indep_system.indep_in_def[OF \<open>indep_system E (dual E indep)\<close>]
          by (metis \<open>X \<subseteq> E\<close> subset_trans)
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
    by (smt (verit, ccfv_threshold) \<open>matroid E (dual E indep)\<close> \<open>matroid E indep'\<close>
        indep_system.basis_in_ex indep_system.basis_in_subset_carrier matroid.rank_of_eq_card_basis_in
        subset_trans)

  with \<open>\<forall>X\<subseteq>E. ?q X = matroid.rank_of indep' X\<close>
  have "\<forall>X \<subseteq> E. matroid.rank_of (dual E indep) X = ?q X" by auto

  with \<open>matroid E (dual E indep)\<close>
  show ?thesis by auto
qed

lemma matroid_iff_dual_matroid:
  assumes "indep_system E indep"
  shows "matroid E indep \<longleftrightarrow> matroid E (dual E indep)"
  using matroid_dual_rank_expr dual_involution
  by (metis assms indep_system_def)


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
    by (metis diff_le_self length_drop)

  have "?j < length l1"
    using \<open>1 \<le> length l2\<close> \<open>length l2 \<le> length l1\<close> by linarith

  have "length l1 - length (tl l2) = (length l1 - length l2) + 1"
    using \<open>length l2 \<le> length l1\<close> \<open>length l2 \<ge> 1\<close>
    by (metis Nat.add_diff_assoc2 Nat.diff_diff_right length_tl)
  moreover have "set (take (?j + 1) l1) = insert (hd (drop (?j) l1)) (set (take (?j) l1))"
    using take_hd_drop \<open>?j < length l1\<close>
    by (metis Suc_eq_plus1 list.simps(15) rotate1.simps(2) set_rotate1)
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
  using take_Suc_conv_app_nth[OF assms(3)] 
  by (metis Diff_Diff_Int Diff_insert_absorb assms(1) assms(2) card_distinct distinct_take inf_bot_right
      insert_inter_insert list.simps(15) not_distinct_conv_prefix rotate1.simps(2) set_rotate1)

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
    by (metis add.commute assms(1) assms(2) assms(4) assms(5) le_add_diff_inverse2 plus_1_eq_Suc set_take_Suc_diff)

  have card_diff_expr: "(card (A \<inter> set (take j l)) - card (A \<inter> set (take (j - 1) l))) =
    card (A \<inter> (set (take j l) - set (take (j - 1) l)))"
    by (metis Diff_Int_distrib List.finite_set card_Diff_subset diff_le_self equalityD1 finite_Int
        inf_mono set_take_subset_set_take)

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
      by (metis sum.empty)
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
    by (metis Suc_pred' atLeastAtMost_iff lessI less_imp_diff_less less_one nat_less_le)

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
  by (metis Suc_eq_plus1_left Suc_pred' add.commute atLeastLessThanSuc_atLeastAtMost lessI
      less_add_same_cancel1 order_le_less_trans sum.last_plus)

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
      by (smt (verit, best) Suc_pred' add_cancel_right_right assms(3) diff_Suc_1 diff_is_0_eq
          less_add_same_cancel1 linorder_not_less mult_zero_left nle_le plus_1_eq_Suc sum_split_last)
    also have "... =
    (\<Sum>j = 1..(Suc n - 1). g j * (c (j - 1) - c j)) + g (Suc n) * c (Suc n - 1)"
      by simp
    finally show ?case .
  qed

  have less: "\<forall>j \<in> {1..n - 1}. j < n" by auto
  have "(\<Sum>j \<in> {1..n}. (g j) * (if j < n then c (j - 1) - c j else c (j - 1))) =
    (\<Sum>j \<in> {1..n - 1}. (g j) * (if j < n then c (j - 1) - c j else c (j - 1)))
    + (g n) * (if n < n then c (n - 1) - c n else c (n - 1))"
    by (metis (no_types, lifting) add.right_neutral assms(3) less_one linorder_not_le mult_zero_left sum_split_last zero_diff)
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
    by (smt (verit, best) Frac_def One_rat_def lower_rank_le_upper_rank nat_int_comparison(3) zero_le_Fract_iff)

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
    by (smt (verit, del_insts) card_mono carrier_finite finite_nat_set_iff_bounded_le indep_subset_carrier
        mem_Collect_eq)
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
      by (metis mult_zero_right of_nat_0_le_iff order_le_less pos_le_divide_eq)
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
    by (metis X(1) lower_rank_le_upper_rank upper_rank_equiv_rank)
  with X B1 B2 show ?thesis by metis
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
    by (smt (verit, ccfv_SIG) Fract_le_one_iff \<open>F \<subseteq> carrier\<close> \<open>basis_in F B1\<close> \<open>basis_in F B2\<close>
        basis_in_finite basis_in_subset_eq card_0_eq empty_subsetI of_nat_le_0_iff of_nat_le_iff)

  with \<open>(int (card B1)) \<noteq> (int (card B2))\<close>
  have "card B1 < card B2" by simp

  with \<open>rank_quotient = Fract (int (card B1)) (int (card B2))\<close>  \<open>rank_quotient = 0\<close>
  have "card B1 = 0"
    by (metis gr_implies_not0 le0 nat_less_le of_nat_0_less_iff order_less_irrefl zero_less_Fract_iff)

  with \<open>card B1 < card B2\<close>
  have "card B2 > 0" by simp


  from \<open>card B1 = 0\<close> have "B1 = {}"
    using \<open>F \<subseteq> carrier\<close> \<open>basis_in F B1\<close> basis_in_finite by auto

  with basis_in_max_indep_in[OF \<open>F \<subseteq> carrier\<close> \<open>basis_in F B1\<close>] 
  have "\<forall>x \<in> F. \<not> indep_in F {x}" by simp
  then have "\<forall>x \<in> F. \<not>indep {x}" using indep_in_def by blast

  from \<open>card B2 > 0\<close> have "\<exists>x. x \<in> B2"
    by (metis \<open>B1 = {}\<close> \<open>int (card B1) \<noteq> int (card B2)\<close> all_not_in_conv)
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
  by (smt (verit) Diff_Un Diff_eq_empty_iff Diff_partition Diff_subset Diff_subset_conv double_diff
      sup.absorb_iff2 sup_commute)

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
    by (metis One_nat_def Suc_le_eq append_self_conv length_greater_0_conv nless_le)

  then have "card (set (filter (\<lambda>y. c y = 1) (drop k xs))) \<ge> 1"
    by (metis "1"(1) distinct_card distinct_drop distinct_filter)
  with set_filter
  have "card ({x \<in> set (drop k xs). c x = 1}) \<ge> 1" by simp
  with drop_eq_nths[of k xs] set_nths[of xs]
  have "card ({x \<in> {xs ! i |i. i < length xs \<and> i \<in> {i. k \<le> i}}. c x = 1}) \<ge> 1" by simp
  then have "\<exists>j. j \<ge> k \<and> j < length xs \<and> c (xs ! j) = 1"
    by (smt (verit, ccfv_threshold) Collect_empty_eq card.empty mem_Collect_eq not_one_le_zero)
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
  "distinct xs \<Longrightarrow> xs = ys @ zs \<Longrightarrow> (\<And>x. x \<in> set xs \<Longrightarrow> (x \<in> set ys \<longleftrightarrow> P x)) \<Longrightarrow> ys = filter P xs"
  by (smt (verit, best) IntI UnCI distinct_append filter_append filter_empty_conv filter_id_conv list.set(1)
      self_append_conv set_append)

lemma sorted_aux4:
  "distinct xs \<Longrightarrow> xs = (filter P xs) @ ys \<Longrightarrow> ys = (filter (\<lambda>x. \<not> P x) xs)"
  by (metis (no_types, lifting) filter_append filter_empty_conv filter_id_conv filter_set
      member_filter self_append_conv self_append_conv2)

lemma sorted_aux5:
  assumes "distinct xs" "sorted_wrt (\<lambda>x1 x2. c x1 \<ge> c x2) xs" "(\<forall>x. c x = 1 \<or> c x = 0)"
    "length (filter (\<lambda>y. (c::('a \<Rightarrow> rat)) y = 1) xs) = k" "k \<le> length xs"
  shows "xs = (filter (\<lambda>y. c y = 1) xs) @ (filter (\<lambda>y. c y \<noteq> 1) xs)"
proof-
  from sorted_aux1[OF assms] sorted_aux2[OF assms] assms(3)
  have "\<forall>i < length xs. i < k \<longleftrightarrow> c (xs ! i) = 1"
    by (metis linorder_le_less_linear zero_neq_one)

  then have "\<And>x. x \<in> set xs \<Longrightarrow> (x \<in> set (take k xs) \<longleftrightarrow> c x = 1)"
  proof-
    fix x
    assume "x \<in> set xs"
    then have "\<exists>i. i < length xs \<and> xs ! i = x"
      by (simp add: in_set_conv_nth)

    show "(x \<in> set (take k xs) \<longleftrightarrow> c x = 1)"
      by (metis \<open>\<exists>i<length xs. xs ! i = x\<close>  \<open>\<forall>i<length xs. (i < k) = (c (xs ! i) = 1)\<close>
          in_set_conv_nth length_take min_less_iff_conj nth_take)
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
    by (metis assms diff_zero indep_in_iff_rank_of indep_in_subset_carrier)
  then show ?case by fastforce
next
  case (Suc n)
  from Suc have "\<exists>A'. indep_in X A' \<and> card A' = rank_of X - n"
    by (metis DiffD2 Suc_diff_le assms card_insert_disjoint diff_Suc_Suc diff_le_self finite_subset
        indep_in_def indep_in_not_basis_in indep_system.carrier_finite indep_system_axioms not_less_eq_eq
        rank_of_eq_card_basis_in)
  then obtain A' where "indep_in X A'" "card A' = rank_of X - n" by blast

  from this(2) Suc(2) augment_aux_indep_in[OF assms \<open>indep_in X A'\<close> \<open>indep_in X A\<close>]
  have "\<exists>x \<in> A' - A. indep_in X (insert x A)"
    by (metis Suc.prems(2) Suc_diff_le diff_Suc_Suc)
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
