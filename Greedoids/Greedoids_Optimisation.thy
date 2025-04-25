theory Greedoids_Optimisation
  imports Greedoids "HOL-Eisbach.Eisbach"
begin

locale greedoid_algorithm = greedoid +
  fixes orcl::"'a \<Rightarrow> 'a set \<Rightarrow> bool"
  assumes orcl_correct: "\<And> X x. x \<in> E - X \<Longrightarrow> X \<in> F \<Longrightarrow> orcl x X \<longleftrightarrow> insert x X \<in> F"
begin

lemma finite_E: "finite E"
  using set_system_def ss_assum by auto
lemma modular_weightE: "valid_modular_weight_func E c \<Longrightarrow> 
               ((\<And> X Y. X \<subseteq> E \<Longrightarrow> Y \<subseteq> E \<Longrightarrow> c (X \<union> Y) = c X +  c Y - c (X \<inter> Y)) \<Longrightarrow> P ) \<Longrightarrow> P"
  by(auto simp add: valid_modular_weight_func_def)

lemma modular_weightI: "(\<And> X Y. X \<subseteq> E \<Longrightarrow> Y \<subseteq> E \<Longrightarrow> c (X \<union> Y) = c X +  c Y - c (X \<inter> Y)) 
                    \<Longrightarrow> valid_modular_weight_func E c"
  by(auto simp add: valid_modular_weight_func_def)

lemma modular_weight_split: "valid_modular_weight_func E c \<Longrightarrow> 
                X \<subseteq> E \<Longrightarrow> Y \<subseteq> E \<Longrightarrow> c (X \<union> Y) = c X +  c Y - c (X \<inter> Y)"
  by(auto simp add: valid_modular_weight_func_def)

lemma modular_function_single_costs:
  assumes "valid_modular_weight_func E c"  "X \<subseteq> E" 
  shows "c X = sum (\<lambda> x. c {x}) X - (real (card X) - 1) * c {}"
proof-
  have "finite X"
    using assms(2) finite_E rev_finite_subset by blast
  moreover have " finite X \<Longrightarrow> X \<subseteq> E \<Longrightarrow> ?thesis"
  proof(induction X rule: finite_induct)
    case empty
    then show ?case by simp 
  next
    case (insert x F)
    hence sets_in_E: "F \<subseteq> E" "{x} \<subseteq> E" "F \<inter> {x} = {}" by auto
    show ?case 
      apply(subst modular_weight_split[OF assms(1) sets_in_E(1,2), simplified])
      apply(subst insert(3)[OF sets_in_E(1)])
      apply(subst sets_in_E(3))
      apply(subst comm_monoid_add_class.sum.insert[OF _ insert(2)])
      by (auto simp add: card_insert_disjoint[OF  _ insert(2)] insert.hyps(1)  algebra_simps)
  qed
  ultimately show ?thesis
    using assms(2) by simp
qed

lemma sum_is_modular: "valid_modular_weight_func E (\<lambda> X. sum f X)"
  by(auto intro: modular_weightI sum_Un rev_finite_subset[OF finite_E])

definition "single_costs c X = c {} + sum (\<lambda> x. c {x} - c {}) X"
definition "elements_costs c x = c {x} - c {}"

lemma real_distrib_sum:"real (sum f X) = sum (real o f) X"
  by auto

lemma modular_function_elements_costs:
  assumes "valid_modular_weight_func E c"  "X \<subseteq> E" 
  shows "c X = sum (elements_costs c) X + c {}"
  apply(subst modular_function_single_costs[OF assms])
  unfolding elements_costs_def 
  apply(auto simp add: algebra_simps) 
  apply(subst card_eq_sum[of X])
  apply(subst real_distrib_sum)+
  apply(subst o_def)+
  apply(subst semiring_0_class.sum_distrib_left)+
  apply(subst comm_monoid_add_class.sum.distrib[symmetric])
  by simp

definition "opt_basis (c::'a set \<Rightarrow> real) X = (basis F X \<and>
                              (\<forall> Y. basis F Y \<longrightarrow> c X \<ge> c Y))"

lemma has_max_superset:  assumes "A \<in> F"
  obtains Xmax where "maximal (\<lambda> X. X \<in> F) Xmax" "Xmax \<supseteq> A"
proof(goal_cases)
  case 1
  have finiteF:"finite F" 
    using Sup_least finite_UnionD finite_subset[of _ "Pow E"] ss_assum
    by(fastforce simp add: set_system_def)
  have "card A \<in> {card  X | X. X \<in> F \<and> X \<supseteq> A}"
    using assms by blast
  moreover have finite_cards: "finite { card X | X. X \<in> F \<and> X \<supseteq> A}"
    by (simp add: finiteF)
  ultimately have "(Max { card X | X. X \<in> F \<and> X \<supseteq> A}) \<in> { card X | X. X \<in> F \<and> X \<supseteq> A}"
    using Max_in by auto
  then obtain X where X_prop: "X \<in> F" "X \<supseteq> A" "card X = (Max { card X | X. X \<in> F \<and> X \<supseteq> A})" by auto
  hence X_best:"Y \<in> F \<Longrightarrow> Y \<supseteq> A \<Longrightarrow>card Y \<le> card X" for Y
    using Max_ge[OF finite_cards,  of "card Y"] by auto
  have " maximal (\<lambda> X. X \<in> F) X" 
  proof(rule ccontr, goal_cases)
    case 1
    then obtain Y where Y_prop: "Y \<in> F" "Y \<supset> X" 
      using X_prop(1) by(auto simp add: maximal_def)
    moreover hence "card Y > card X" 
      using infinite_super[of Y E] psubset_card_mono[of Y X]  ss_assum
      by(auto simp add: set_system_def)
    ultimately show ?case 
      using X_best[of Y]  X_prop(2) linorder_not_le by blast
  qed
  thus ?case 
    using  X_prop(1,2) by(auto intro!: 1[of X] exI[of _ X])
qed


lemma opt_solution_exists: "Ex (opt_basis c)"
proof-
  have finiteF:"finite F" 
    using Sup_least finite_UnionD finite_subset[of _ "Pow E"] ss_assum
    by(fastforce simp add: set_system_def)
  hence fini:"finite {c X | X. X \<in> F \<and> maximal (\<lambda> X. X \<in> F) X}"
    by simp
  moreover obtain Xmax where non_empty:"c Xmax \<in> {c X | X. X \<in> F \<and> maximal (\<lambda> X. X \<in> F) X}"
  proof(goal_cases)
    case 1
    have "card {} \<in> {card  X | X. X \<in> F}"
      using contains_empty_set 
      by force
    moreover have finite_cards: "finite { card X | X. X \<in> F}"
      using finiteF by simp
    ultimately have "(Max { card X | X. X \<in> F}) \<in> { card X | X. X \<in> F}"
      using Max_in by auto
    then obtain X where X_prop: "X \<in> F" "card X = (Max { card X | X. X \<in> F})" by auto
    hence X_best:"Y \<in> F \<Longrightarrow> card Y \<le> card X" for Y
      using Max_ge finite_cards by auto
    have " maximal (\<lambda> X. X \<in> F) X" 
    proof(rule ccontr, goal_cases)
      case 1
      then obtain Y where "Y \<in> F" "Y \<supset> X" 
        using X_prop(1) by(auto simp add: maximal_def)
      moreover hence "card Y > card X" 
        using infinite_super[of Y E] psubset_card_mono[of Y X]  ss_assum
        by(auto simp add: set_system_def)
      ultimately show ?case using X_best by force
    qed
    thus ?case 
      using  X_prop(1) by(auto intro!: 1[of X] exI[of _ X])
  qed
  ultimately have "(Max {c X | X. X \<in> F \<and> maximal (\<lambda> X. X \<in> F) X}) 
                  \<in> {c X | X. X \<in> F \<and> maximal (\<lambda> X. X \<in> F) X}"
    using Max_in by auto
  then obtain X where "c X = Max {c X | X. X \<in> F \<and> maximal (\<lambda> X. X \<in> F) X}" "X \<in> F" "maximal (\<lambda> X. X \<in> F) X"
    by auto
  moreover hence "c X \<ge> c Y"  if "Y \<in> F" "maximal (\<lambda> X. X \<in> F) Y"for Y
    using Max_ge fini that by auto
  ultimately have "opt_basis c X"
    by(auto simp add: opt_basis_def maximal_def basis_alt_def)
  thus ?thesis by auto
qed

context 
  fixes es::"'a list" and c::"'a set \<Rightarrow> real"
begin

definition "find_best_candidate  F' = 
           foldr (\<lambda> e acc. if e \<in> F' \<or> \<not> (orcl e F') then acc
                                                      else (case acc of None \<Rightarrow> Some e |
                                                            Some d \<Rightarrow>
                (if elements_costs c e > elements_costs c d then Some e
                             else Some d))) es None"

function (domintros) greedoid_greedy::"'a list \<Rightarrow> 'a list"  where
  "greedoid_greedy  xs = 
 (case  (find_best_candidate  (set xs)) of 
      Some e \<Rightarrow> greedoid_greedy  (e#xs) 
    | None \<Rightarrow> xs)"
  by pat_completeness auto

definition "invar_find_best_cand xs = (\<forall> i < length xs. 
                        Some (xs ! i) = find_best_candidate  (set (drop (i+1) xs)))"

lemma invar_find_best_candI: "(\<And>i.  i < length xs \<Longrightarrow>
                        Some (xs ! i) = find_best_candidate  (set (drop (i+1) xs)))
         \<Longrightarrow> invar_find_best_cand  xs"
  by(auto simp add: invar_find_best_cand_def)

definition "invar_tails_indep xs = (\<forall> i \<le> length xs. set (drop i xs) \<in> F)"

lemma invar_tails_indepI: "(\<And> i. i \<le> length xs \<Longrightarrow> set (drop i xs) \<in> F) \<Longrightarrow> invar_tails_indep xs"
  by(auto simp add: invar_tails_indep_def)

context
  assumes set_assum: "set es = E" "distinct es" 
begin

lemma find_best_candidate_some:
  assumes "X \<subseteq> E" "find_best_candidate X = Some x" "X \<in> F"
  shows "\<exists> es1 es2. es = es1@[x]@es2 \<and> x \<notin> X \<and> (insert x X) \<in> F \<and>
          (\<forall> y \<in> E - X. (insert y X) \<in> F \<longrightarrow> elements_costs c y \<le> elements_costs c x)
          \<and> \<not> (\<exists> y \<in> set es2. y \<notin> X \<and> (insert y X) \<in> F  \<and> elements_costs c y \<ge> elements_costs c x)"
proof-
  let ?iteration = " (\<lambda>e acc.
         if e \<in> X \<or> \<not> orcl e X then acc
         else case acc of None \<Rightarrow> Some e | Some d \<Rightarrow> if elements_costs c d < elements_costs c e then Some e else Some d)"
  have none_no_solution:"foldr ?iteration xs None = None \<Longrightarrow> \<not> ( \<exists> x \<in> set xs. x \<notin> X \<and> orcl x X)"
    for xs
    by(induction xs)
      (auto simp add: option.case_eq_if, meson option.discI, smt (verit, best) not_Some_eq option.simps(5))
  have "set es \<subseteq> E"
    by (simp add: set_assum(1))
  hence "\<exists> es1 es2. es = es1@[x]@es2 \<and> x \<notin> X \<and> (insert x X) \<in> F \<and>
          (\<forall> y \<in> set es - X. (insert y X) \<in> F \<longrightarrow> elements_costs c y \<le> elements_costs c x)
          \<and> \<not> (\<exists> y \<in> set es2. y \<notin> X \<and> (insert y X) \<in> F  \<and> elements_costs c y \<ge> elements_costs c x)"
    using assms(1,2) set_assum(2)
    unfolding find_best_candidate_def
  proof(induction es arbitrary: x)
    case Nil
    then show ?case
      by simp
  next
    case (Cons a es)
    show ?case 
    proof(cases "a \<in> X \<or> \<not> orcl a X")
      case True
      hence "foldr ?iteration (a # es) None =  foldr ?iteration es None "
        by simp
      hence "\<exists>es1 es2.
        es = es1 @ [x] @ es2 \<and>
        x \<notin> X \<and>
        insert x X \<in> F \<and>
        (\<forall>y\<in>set es - X. insert y X \<in> F \<longrightarrow> elements_costs c x \<ge> elements_costs c y) \<and>
        \<not> (\<exists>y\<in>set es2. y \<notin> X \<and> insert y X \<in> F \<and> elements_costs c y \<ge>elements_costs c x)"
        using Cons.prems(1,3,4)  assms(1) by(intro Cons(1)[of x]) auto
      then obtain es1 es2 where es1es2_prop: "es = es1 @ [x] @ es2"
        "x \<notin> X"
        "insert x X \<in> F"
        "(\<forall>y\<in>set es - X. insert y X \<in> F \<longrightarrow>elements_costs c x \<ge>elements_costs c y)"
        "\<not> (\<exists>y\<in>set es2. y \<notin> X \<and> insert y X \<in> F \<and> elements_costs c y \<ge>elements_costs c x)" by auto
      moreover hence "a#es = (a#es1) @ [x] @ es2"
        using True by simp
      moreover have  "(\<forall>y\<in>set (a#es) - X. insert y X \<in> F \<longrightarrow> elements_costs c x \<ge> elements_costs c y)"  
        using True es1es2_prop(4) orcl_correct[OF  _ assms(3), of a] Cons.prems(1) by auto
      moreover have 
        "\<not> (\<exists>y\<in>set (es2). y \<notin> X \<and> insert y X \<in> F \<and> elements_costs c y \<ge> elements_costs c x)"
        using True es1es2_prop(5) orcl_correct[OF  _ assms(3), of a] Cons.prems(1) by auto
      ultimately show ?thesis by blast
    next
      case False
      show ?thesis
      proof(cases "foldr ?iteration es None")
        case None
        hence x_is_a:"x = a"
          using Cons.prems(3) False by force
        hence  "a # es = [x] @ es" by simp
        moreover have "x \<notin> X" 
          using False x_is_a by auto
        moreover have "insert x X \<in> F"
          using Cons.prems(1) False assms(1) assms(3) orcl_correct x_is_a by auto
        moreover have "(\<forall>y\<in>set (a # es) - X. insert y X \<in> F \<longrightarrow> elements_costs c x \<ge>elements_costs c y)"
          using x_is_a  none_no_solution[OF None] orcl_correct[OF  _ assms(3)]
            Cons.prems(1) by fastforce+
        moreover have  "\<not> (\<exists>y\<in>set es. y \<notin> X \<and> insert y X \<in> F \<and> elements_costs c y \<ge> elements_costs c x)" 
          using x_is_a  none_no_solution[OF None] orcl_correct[OF _ assms(3)]
            Cons.prems(1) by auto
        ultimately show ?thesis  by force
      next
        case (Some y)
        obtain es1 es2 where es1_es2_prop: "es = es1 @ [y] @ es2" "y \<notin> X" "insert y X \<in> F"
          "(\<forall>ya\<in>set es - X. insert ya X \<in> F \<longrightarrow> elements_costs c y \<ge> elements_costs c ya)"
          "\<not> (\<exists>ya\<in>set es2. ya \<notin> X \<and> insert ya X \<in> F \<and> elements_costs c ya \<ge> elements_costs c y)"
          using Cons(1)[OF _ _ Some]  Cons.prems(1,4) assms(1) by auto
        have "elements_costs c y \<ge> elements_costs c a \<Longrightarrow>  (a#es) = (a#es1) @ [y] @ es2"
          by (simp add: es1_es2_prop(1))
        moreover have "elements_costs c y \<ge>elements_costs  c a \<Longrightarrow> x = y"
          using  Cons.prems(3) Some False by auto
        moreover have "elements_costs c y < elements_costs c a \<Longrightarrow> (a#es) = []@[x]@es"
          using Cons.prems(3) False Some by simp
        moreover have  "x \<notin> X"
          using Cons.prems(3) Some es1_es2_prop(2) False
          by(auto split: option.split if_split intro: case_split[of "elements_costs c y < elements_costs c a"])
        moreover have "insert x X \<in> F"
          using Cons.prems(1,3) Some es1_es2_prop(3,4) False  assms(1,3) orcl_correct
          by (fastforce intro:  case_split[of "elements_costs c y <elements_costs c a"])
        moreover have  "(\<forall>ya\<in>set (a#es) - X. insert ya X \<in> F \<longrightarrow> elements_costs c x \<ge> elements_costs c ya)"
          using es1_es2_prop(4) False  Cons.prems Some
          by (cases "elements_costs c y <elements_costs c a") auto
        moreover have  "elements_costs c y \<ge> elements_costs c a \<Longrightarrow> 
                \<not> (\<exists>ya\<in>set (es2). ya \<notin> X \<and> insert ya X \<in> F \<and> elements_costs c ya \<ge> elements_costs c y)"
          by (simp add: es1_es2_prop(5))
        moreover have  "elements_costs c y < elements_costs c a \<Longrightarrow> 
                \<not> (\<exists>ya\<in>set es. ya \<notin> X \<and> insert ya X \<in> F \<and> elements_costs c ya \<ge> elements_costs c a)"
          using es1_es2_prop(4) by fastforce
        ultimately show ?thesis
          by(cases "elements_costs c y < elements_costs c a")
            (auto intro: exI[of "\<lambda> xs. \<exists>es2. _ xs es2" "a#es1"] exI[of _ "es2"])
      qed     
    qed
  qed
  thus ?thesis 
    using set_assum(1) by force
qed

lemma find_best_candidate_none:
  assumes "X \<subseteq> E" "find_best_candidate X = None" "X \<in> F"
  shows "\<nexists> x. x \<in> E - X \<and> insert x X \<in> F"
proof-
  let ?iteration = " (\<lambda>e acc.
         if e \<in> X \<or> \<not> orcl e X then acc
         else case acc of None \<Rightarrow> Some e | Some d \<Rightarrow> if elements_costs c d < elements_costs c e then Some e else Some d)"
  have es_in_E: "set es \<subseteq> E" 
    by (simp add: set_assum)
  show ?thesis
    apply(subst set_assum(1)[symmetric])
    using assms(2) es_in_E
    unfolding find_best_candidate_def 
  proof(induction es)
    case Nil
    then show ?case by simp
  next
    case (Cons a es)
    show ?case
    proof(cases "a \<in> X \<or> \<not> orcl a X")
      case True
      then show ?thesis 
        using orcl_correct[OF  _ assms(3), of a]
          Cons.IH Cons.prems(1) Cons.prems(2) by auto
    next
      case False
      have if_None:"(if A then Some B else Some C) = None  \<Longrightarrow> P" for A B C  P
        by(cases A) auto
      from False show ?thesis 
        using orcl_correct[OF  _ assms(3), of a]
          Cons.prems(1) Cons.prems(2)
        by(cases "foldr ?iteration es None")
          (auto split: if_split intro: if_None)
    qed
  qed
qed

(*Invariants: solution in E, solution independent, solution distinct, solution elements are best candidates*)

named_theorems loop_props

lemma solution_remains_independent[loop_props]:
  assumes "greedoid_greedy_dom xs" "set xs \<in> F"
  shows "set (greedoid_greedy  xs) \<in> F"
  using assms(2)
proof(induction rule: greedoid_greedy.pinduct[OF assms(1)])
  case (1  xs)
  note IH = this
  have xs_in_E:"set xs \<subseteq> E"
    using "1.prems" ss_assum by(auto simp add: set_system_def )
  show ?case
  proof(subst greedoid_greedy.psimps[OF 1(1)], cases "find_best_candidate  (set xs)", goal_cases)
    case 1
    then show ?case by(simp add: IH(3))
  next
    case (2 x)
    then show ?case 
      using find_best_candidate_some[OF xs_in_E 2 IH(3)] 
      by (auto intro!: IH(2)[OF 2])
  qed
qed

lemma solution_distinct[loop_props]:
  assumes "greedoid_greedy_dom xs" "set xs \<in> F" "distinct xs"
  shows "distinct (greedoid_greedy xs) "
  using assms(2,3)
proof(induction rule: greedoid_greedy.pinduct[OF assms(1)])
  case (1 xs)
  note IH = this
  have xs_in_E:"set xs \<subseteq> E"
    using "1.prems" ss_assum by(auto simp add: set_system_def )
  show ?case
  proof(subst greedoid_greedy.psimps[OF 1(1)], cases "find_best_candidate  (set xs)", goal_cases)
    case 1
    then show ?case by(simp add: IH(4))
  next
    case (2 x)
    then show ?case 
      using find_best_candidate_some[OF xs_in_E 2 IH(3)] IH(4)
      by (simp, intro IH(2)[OF 2]) auto
  qed
qed

lemma greedy_algo_term[loop_props]:
  assumes "set xs \<in> F" "n = card E - card (set xs)" "distinct xs"
  shows "greedoid_greedy_dom xs"
  using assms
proof(induction n arbitrary: xs)
  case 0
  have xs_in_E:"set xs \<subseteq> E"
    using "0.prems" ss_assum by(auto simp add: set_system_def )
  show ?case 
  proof(rule greedoid_greedy.domintros, goal_cases)
    case (1 x)
    have "insert x (set xs) \<in> F" "x \<notin> set xs"
      using find_best_candidate_some[OF xs_in_E 1 0(1)] by auto
    hence "set xs \<subset> E"
      using set_system_def ss_assum xs_in_E by fastforce
    hence "card E - card (set xs) > 0"
      using card_Diff_subset set_assum(1) by fastforce
    thus ?case 
      using 0(2) by simp
  qed
next
  case (Suc n)
  have xs_in_E:"set xs \<subseteq> E"
    using "Suc.prems" ss_assum by(auto simp add: set_system_def )
  show ?case
  proof(rule greedoid_greedy.domintros, goal_cases)
    case (1 x)
    have "insert x (set xs) \<in> F" "x \<notin> set xs" "distinct (x#xs)"
      using find_best_candidate_some[OF xs_in_E 1 Suc(2)] Suc(4) by auto
    moreover hence "set xs \<subset> E"
      using set_system_def ss_assum xs_in_E by fastforce
    moreover hence "card E - card (set xs) > 0"
      using card_Diff_subset set_assum(1) by fastforce
    moreover have "n = card E - card (set (x # xs))" 
      using Suc.prems(2) calculation(2) by force
    ultimately show ?case 
      by(auto intro: Suc(1)[of "x#xs"])
  qed
qed


lemma find_best_candidate_order[loop_props]:
  assumes "greedoid_greedy_dom xs" "set xs \<in> F" "distinct xs" "invar_find_best_cand xs" 
  shows "invar_find_best_cand (greedoid_greedy xs)"
  using assms(2,3,4)
proof(induction rule: greedoid_greedy.pinduct[OF assms(1)])
  case (1 xs)
  note IH = this
  have xs_in_E:"set xs \<subseteq> E"
    using "1.prems" ss_assum by(auto simp add: set_system_def)
  show ?case
  proof(subst greedoid_greedy.psimps[OF 1(1)], cases "find_best_candidate (set xs)", goal_cases)
    case 1
    then show ?case by(simp add: IH(5))
  next
    case (2 x)
    note two = this
    have xs_in_E:"set xs \<subseteq> E"
      using "IH" ss_assum by(auto simp add: set_system_def )
    have x_added: "insert x (set xs) \<in> F" "x \<notin> set xs" "distinct (x#xs)"
      using find_best_candidate_some[OF xs_in_E 2 IH(3)] IH(4) by auto
    have invar_next: "invar_find_best_cand (x # xs)"
    proof(rule invar_find_best_candI, goal_cases)
      case (1 i)
      show ?case 
      proof(insert 1, cases i, goal_cases)
        case 1
        then show ?case 
          by(simp add: 2)
      next
        case (2 nat)
        then show ?case 
          using  x_added  find_best_candidate_some[OF xs_in_E two IH(3)]  IH(5) 
          by(auto simp add: invar_find_best_cand_def)
      qed
    qed
    from 2 show ?case 
      using x_added IH(5) by(auto intro: IH(2)[OF 2] simp add: invar_next)
  qed
qed

lemma final_candidate_none[loop_props]:
  assumes "greedoid_greedy_dom xs" "set xs \<in> F" "distinct xs"
  shows "find_best_candidate (set (greedoid_greedy  xs))  = None"
  using assms(2,3)
proof(induction rule: greedoid_greedy.pinduct[OF assms(1)])
  case (1  xs)
  note IH = this
  have xs_in_E:"set xs \<subseteq> E"
    using "1.prems" ss_assum by(auto simp add: set_system_def)
  show ?case
  proof(subst greedoid_greedy.psimps[OF IH(1)], cases "find_best_candidate  (set xs)", goal_cases)
    case 1
    then show ?case by simp
  next
    case (2 x)
    then show ?case 
      using find_best_candidate_some[OF xs_in_E 2 IH(3)] IH(4) 
      by (simp, intro IH(2)[OF 2]) auto
  qed
qed

lemma intermediate_solutions_indep[loop_props]:
  assumes "greedoid_greedy_dom xs" "set xs \<in> F" "invar_tails_indep xs"
  shows "invar_tails_indep (local.greedoid_greedy  xs)"
  using assms(2,3)
proof(induction rule: greedoid_greedy.pinduct[OF assms(1)])
  case (1 xs)
  note IH = this
  have xs_in_E:"set xs \<subseteq> E"
    using "1.prems" ss_assum by(auto simp add: set_system_def)
  show ?case
  proof(subst greedoid_greedy.psimps[OF 1(1)], cases "find_best_candidate (set xs)", goal_cases)
    case 1
    then show ?case by(simp add: IH(4))
  next
    case (2 x)
    note two = this
    have xs_in_E:"set xs \<subseteq> E"
      using "IH" ss_assum by(auto simp add: set_system_def )
    have x_added: "insert x (set xs) \<in> F" 
      using find_best_candidate_some[OF xs_in_E 2 IH(3)] by auto
    have invar_next: "invar_tails_indep  (x # xs)"
    proof(rule invar_tails_indepI, goal_cases)
      case (1 i)
      show ?case 
      proof(insert 1, cases i, goal_cases)
        case 1
        then show ?case 
          by(simp add: x_added)
      next
        case (2 nat)
        then show ?case 
          using  x_added  find_best_candidate_some[OF xs_in_E two IH(3)]  IH(4) 
          by(auto simp add: invar_tails_indep_def)
      qed
    qed
    from 2 show ?case 
      using x_added IH(4) by(auto intro: IH(2)[OF 2] simp add: invar_next)
  qed
qed

lemma initial_props: "set Nil \<in> F" "card E = card E - card (set Nil)" "distinct Nil"
  "invar_find_best_cand Nil" "invar_tails_indep Nil"
  by(auto simp add: contains_empty_set intro: invar_find_best_candI invar_tails_indepI)

lemmas result_props =
  loop_props(3)[OF initial_props(1-3), of ] 
  loop_props(1)[OF loop_props(3)[OF initial_props(1-3)] initial_props(1), of ]
  loop_props(2)[OF loop_props(3)[OF initial_props(1-3)] initial_props(1,3), of ]
  loop_props(4)[OF loop_props(3)[OF initial_props(1-3)] initial_props(1,3,4)]
  loop_props(5)[OF loop_props(3)[OF initial_props(1-3)] initial_props(1,3), of ]
  loop_props(6)[OF loop_props(3)[OF initial_props(1-3)] initial_props(1,5), of ]

lemma algorithm_computes_basis:
  "basis F (set (greedoid_greedy  Nil))"
proof(rule ccontr, goal_cases)
  case 1
  note result_props = result_props(2,5)[of ]
  have alg_inF: "(set (local.greedoid_greedy  [])) \<in> F"
    using result_props(1) by auto
  then obtain X where X_prop:"X \<supset> set (local.greedoid_greedy [])" "X \<in> F" 
    using 1 by(auto simp add: maximal_def basis_alt_def)
  hence XinE: "X \<subseteq> E"
    using ss_assum by(auto simp add: set_system_def)
  hence "card X > card (set (local.greedoid_greedy []))"
    using  finite_subset psubset_card_mono set_assum(1)  X_prop(1) by blast
  then obtain y where y_prop:"y \<in> X - set (local.greedoid_greedy  [])" 
    "insert y (set (local.greedoid_greedy [])) \<in> F"
    using  result_props(1) third_condition  X_prop(2) by auto
  moreover hence "y \<in> E - set (local.greedoid_greedy []) "
    using XinE by fastforce
  moreover have "\<nexists>x. x \<in> E - set (local.greedoid_greedy []) \<and> insert x (set (local.greedoid_greedy [])) \<in> F"
    using   result_props(2) alg_inF ss_assum
    by (intro find_best_candidate_none[OF _ result_props(2)])
      (auto simp add: set_system_def)
  ultimately show False
    by blast
qed


lemma strong_exchange_modular_opt:
  assumes "valid_modular_weight_func E c" "strong_exchange_property E F"
  shows "opt_basis c (set (greedoid_greedy  Nil))"
proof-
  note result_props = result_props[of ]
  define max_P where "max_P = (\<lambda> n. n \<le> length (greedoid_greedy Nil) \<and>
                               (\<exists> B. opt_basis c B 
                               \<and> set (take n ( rev (greedoid_greedy Nil))) \<subseteq> B))"
  have "\<exists>nmax. max_P nmax \<and> \<not> (\<exists>m>nmax. max_P m)"
    by(fastforce intro:  max_n[of max_P "length (greedoid_greedy Nil)" 0] 
        simp add: max_P_def opt_solution_exists)
  then obtain k where k_prop: "max_P k" "\<not> (\<exists>m>k. max_P m)" by auto
  then obtain B where B_prop: "opt_basis c B" "set (take k ( rev (greedoid_greedy Nil))) \<subseteq> B"
    using max_P_def by blast
  hence B_unfolded: "B \<in> F" "B \<subseteq> E" "maximal (\<lambda> B. B \<in> F) B"
    using  ss_assum
    by(auto simp add: opt_basis_def set_system_def maximal_def basis_alt_def) 
  have k_length_less:"k \<le> length (greedoid_greedy  Nil)"
    using k_prop by(auto simp add: max_P_def) 
  moreover have "k < length (greedoid_greedy  Nil) \<Longrightarrow> False"
  proof(goal_cases)
    case 1
    note one = this
    hence length_non_zero: "length (local.greedoid_greedy  []) > 0" by auto
    define B' where "B' = B - (set (take k ( rev (greedoid_greedy  Nil))))"
    have a3: "set (take k (rev (local.greedoid_greedy  []))) \<subseteq> B" 
      by (simp add: B_prop(2))
    have a4: "maximal (\<lambda>B. B \<in> F) B"
      by (simp add: B_unfolded(3))
    have a5:"rev (local.greedoid_greedy  []) ! k \<in> E" 
    proof-
      have "set  (local.greedoid_greedy  []) \<in> F"
        using result_props(6) one by(auto simp add: invar_tails_indep_def)
      hence "set (local.greedoid_greedy  []) \<subseteq> E"
        using ss_assum by(auto simp add: set_system_def)
      moreover have "rev (local.greedoid_greedy  []) ! k \<in> set (local.greedoid_greedy  [])" 
        by (metis length_rev nth_mem one set_rev)
      ultimately show ?thesis by auto
    qed
    have a6: "rev (local.greedoid_greedy  []) ! k \<notin> B" 
    proof(rule ccontr, goal_cases 1)
      case 1
      hence "rev (local.greedoid_greedy  []) ! k \<in> B" by simp
      hence "set (take (k+1) ( rev (greedoid_greedy  Nil))) \<subseteq> B" 
        using  a3  one set_take_union_nth[of k "rev (greedoid_greedy  Nil)", symmetric] 
        by simp
      hence "max_P (k+1)"
        using B_prop(1) less_iff_succ_less_eq max_P_def one by blast
      thus False 
        using k_prop(2) by force
    qed
    have "\<exists> y \<in> B'. insert y (set (take k (rev (greedoid_greedy  Nil)))) \<in> F \<and> 
                    (B - {y}) \<union> {(rev (greedoid_greedy  Nil)) ! k} \<in> F"
    proof(rule strong_exchange_propertyE[OF assms(2)], goal_cases)
      case 1
      have a1: "set (take k (rev (local.greedoid_greedy  []))) \<in> F" 
        using diff_le_self[of ]  result_props(6) set_rev take_rev[of k "local.greedoid_greedy  []"]
        by(simp add: invar_tails_indep_def)
      have a2: "B \<in> F" 
        using B_prop by (auto simp add: opt_basis_def maximal_def basis_alt_def)
      have a4: "basis F B"
        by (simp add: B_unfolded(3) basis_alt_def)
      have a7: "insert (rev (local.greedoid_greedy  []) ! k) 
                         (set (take k (rev (local.greedoid_greedy  [])))) \<in> F"
        using HOL.spec[OF result_props(6)[simplified invar_tails_indep_def], 
            of "length (local.greedoid_greedy  []) - (k+1)"]
          one rev_rev_ident[of "greedoid_greedy  []"] 
          rev_take[of "k+1" "rev (greedoid_greedy  [])"] 
          set_take_union_nth[of k "(rev (local.greedoid_greedy  []))"]
        by (auto ,metis set_rev)         
      show ?case 
        using a1 a2 a3 a4 a5 a6 a7 
        by(auto intro!: 1[of "set (take k (rev (local.greedoid_greedy  [])))" B
              "rev (local.greedoid_greedy  []) ! k", simplified] simp add: B'_def)
    qed
    then obtain y where y_props: " insert y (set (take k (rev (local.greedoid_greedy  [])))) \<in> F"
      "B - {y} \<union> {rev (local.greedoid_greedy  []) ! k} \<in> F" "y \<in> B'" by auto
    have ak_better_costs_than_y:
      "elements_costs c ((rev (local.greedoid_greedy  [])) ! (k)) \<ge> elements_costs c y"
    proof-
      have cand_is: "Some (rev (local.greedoid_greedy []) ! (k )) = 
             find_best_candidate  (set (take k (rev (local.greedoid_greedy []))))"
        using HOL.spec[OF result_props(4)[simplified invar_find_best_cand_def], 
            of "length (local.greedoid_greedy  []) - Suc k"]
          Suc_diff_Suc[of k "length (local.greedoid_greedy  [])"]  one 
        by (fastforce simp add: rev_nth[OF one] take_rev)
      have take_k_in_F:"set (take k (rev (local.greedoid_greedy  []))) \<in> F"
        using result_props(6) 
        by(simp add: invar_tails_indep_def take_rev)
      hence take_k_in_E:"set (take k (rev (local.greedoid_greedy  []))) \<subseteq> E"
        using B_prop(2) B_unfolded(2) by blast
      have from_condidate_props:"(\<And> y. y\<in>E - set (take k (rev (local.greedoid_greedy []))) \<Longrightarrow>
             insert y (set (take k (rev (local.greedoid_greedy  [])))) \<in> F \<Longrightarrow>
            elements_costs c y \<le> elements_costs c (rev (local.greedoid_greedy  []) ! k))"
        using find_best_candidate_some[OF take_k_in_E cand_is[symmetric] take_k_in_F] by auto
      show ?thesis
        using y_props(3) B_unfolded(2) 
        by(auto intro: from_condidate_props[OF _ y_props(1)] simp add: B'_def)
    qed
    have new_b_better:"c (B - {y} \<union> {rev (local.greedoid_greedy []) ! k}) \<ge>  c B"
    proof-
      have "c B = c ((B-{y}) \<union> {y})"
        using B'_def insert_Diff y_props(3) by fastforce
      also have "... = c(B - {y}) + c {y} - c {}"
        using B_unfolded y_props(3) 
        by (subst modular_weight_split[OF assms(1)])(auto simp add: B'_def)
      also have "... =  c (B - {y}) +  elements_costs c y"
        by (simp add: elements_costs_def)
      also have "... \<le> c (B - {y}) + elements_costs c (rev (local.greedoid_greedy  []) ! k)"
        by (simp add: ak_better_costs_than_y)
      also have "... = c (B - {y}) + c {(rev (local.greedoid_greedy  []) ! k)} - c {}"
        by (simp add: elements_costs_def)
      also have "... = c (B - {y} \<union>  {(rev (local.greedoid_greedy  []) ! k)})"
        using B_unfolded(2)  ss_assum y_props(2)  a6  
        by (subst modular_weight_split[OF assms(1)]) (fastforce simp add: set_system_def )+
      finally show ?thesis by simp
    qed
    have maximal_exchange:"basis F (B - {y} \<union>  {(rev (local.greedoid_greedy  []) ! k)})"
    proof(rule ccontr, unfold basis_alt_def maximal_def, goal_cases)
      case 1
      then obtain Bgtr where Bgtr: "B - {y} \<union> {rev (local.greedoid_greedy  []) ! k} \<subset> Bgtr" "Bgtr \<in> F"
        using y_props(2) by auto
      hence "card (B - {y} \<union> {rev (local.greedoid_greedy  []) ! k}) < card Bgtr"
        using  finite_subset[of Bgtr E] psubset_card_mono[of Bgtr] ss_assum 
        by(simp add: set_system_def) 
      moreover have "card (B - {y} \<union> {rev (local.greedoid_greedy  []) ! k}) = card B" 
        using  B_unfolded(2)  Un_insert_right a6 card.remove[of B y]
          card_insert_disjoint[of "B - {y}" "rev (local.greedoid_greedy  []) ! k"] finite_E   y_props(3)
        by(unfold B'_def) fastforce
      ultimately have "card B < card Bgtr" by simp
      then obtain z where "z \<in> Bgtr - B"  "insert z B \<in> F" 
        using B_unfolded(1) Bgtr(2) third_condition by auto
      hence "\<not> maximal (\<lambda> X. X \<in> F) B" 
        by(auto simp add: maximal_def)
      thus False 
        by (simp add: a4)
    qed
    have "(k+1) \<le> length (greedoid_greedy  Nil)"
      using one by auto
    moreover have " opt_basis c (B - {y} \<union> {rev (local.greedoid_greedy  []) ! k})"
      using B_prop(1)  maximal_exchange new_b_better by (auto simp add: opt_basis_def)
    moreover have "set (take (k+1) ( rev (greedoid_greedy  Nil))) \<subseteq>
                  (B - {y} \<union> {rev (local.greedoid_greedy  []) ! k})"
      using one  B'_def a3  y_props(3)
      by (subst set_take_union_nth[symmetric])(auto simp add:  B'_def)
    ultimately have "max_P (k+1)"
      by(auto simp add: max_P_def)
    thus False
      using k_prop(2) by auto
  qed
  ultimately have "k = length (local.greedoid_greedy  [])" by force
  hence inB:"set (local.greedoid_greedy  []) \<subseteq> B" 
    using B_prop(2) by simp
  moreover have "set (local.greedoid_greedy  []) \<subset> B \<Longrightarrow> False"
  proof(goal_cases)
    case 1
    hence "card B > card (set (local.greedoid_greedy  []))"
      using B_unfolded(2) finite_subset psubset_card_mono set_assum(1) by blast
    then obtain y where y_prop:"y \<in> B - set (local.greedoid_greedy  [])" 
      "insert y (set (local.greedoid_greedy  [])) \<in> F"
      using B_unfolded(1) result_props(2) third_condition by auto
    moreover hence "y \<in> E - set (local.greedoid_greedy  []) "
      using B_unfolded(2) by blast
    moreover have "\<nexists>x. x \<in> E - set (local.greedoid_greedy  []) \<and> insert x (set (local.greedoid_greedy  [])) \<in> F"
      using B_unfolded inB  result_props(2) 
      by (intro find_best_candidate_none[OF _ result_props(5)]) auto
    ultimately show False
      by blast
  qed
  ultimately have "B = set (local.greedoid_greedy  [])"
    by blast
  thus ?thesis
    using B_prop(1) by auto
qed
end
end

context
  assumes no_strong_exchange: "\<not> strong_exchange_property E F"
begin

thm no_strong_exchange[simplified strong_exchange_property_def]

lemma no_strong_exchange_applied: 
  obtains A B x where
    "A \<in> F" "B \<in> F" "A \<subseteq> B" "basis F B" "x \<in> E - B" 
    "A \<union> {x} \<in> F"  "(\<And> y. y\<in>B - A \<Longrightarrow> A \<union> {y} \<in> F \<Longrightarrow> B - {y} \<union> {x} \<notin> F)"
  using no_strong_exchange by (auto simp add: strong_exchange_property_def)

definition "A = (SOME A. \<exists> B x. 
                  A \<in> F \<and> B \<in> F \<and> A \<subseteq> B \<and> basis F B \<and>  x \<in> E - B \<and>
                  A \<union> {x} \<in> F  \<and> (\<forall>  y\<in>B - A. A \<union> {y} \<in> F \<longrightarrow> B - {y} \<union> {x} \<notin> F))"

lemma there_is_A: "\<exists> A. (\<exists> B x. 
                  A \<in> F \<and> B \<in> F \<and> A \<subseteq> B \<and> basis F B \<and>  x \<in> E - B \<and>
                  A \<union> {x} \<in> F  \<and> (\<forall>  y\<in>B - A. A \<union> {y} \<in> F \<longrightarrow> B - {y} \<union> {x} \<notin> F))"
  using no_strong_exchange by (auto simp add: strong_exchange_property_def)

lemma A_props: "\<exists>B x. A \<in> F \<and> B \<in> F \<and> A \<subseteq> B \<and> basis F B \<and>  x \<in> E - B \<and>
                  A \<union> {x} \<in> F  \<and> (\<forall>  y\<in>B - A. A \<union> {y} \<in> F \<longrightarrow> B - {y} \<union> {x} \<notin> F)"
  by(unfold A_def )(rule someI_ex[OF there_is_A])

definition "B = (SOME B. \<exists> x. 
                  A \<in> F \<and> B \<in> F \<and> A \<subseteq> B \<and> basis F B \<and>  x \<in> E - B \<and>
                  A \<union> {x} \<in> F  \<and> (\<forall>  y\<in>B - A. A \<union> {y} \<in> F \<longrightarrow> B - {y} \<union> {x} \<notin> F))"

lemma B_props: "\<exists> x. A \<in> F \<and> B \<in> F \<and> A \<subseteq> B \<and> basis F B \<and>  x \<in> E - B \<and>
                  A \<union> {x} \<in> F  \<and> (\<forall>  y\<in>B - A. A \<union> {y} \<in> F \<longrightarrow> B - {y} \<union> {x} \<notin> F)"
  by(unfold B_def )(rule someI_ex[OF A_props])

definition "x = (SOME x. 
                  A \<in> F \<and> B \<in> F \<and> A \<subseteq> B \<and> basis F B \<and>  x \<in> E - B \<and>
                  A \<union> {x} \<in> F  \<and> (\<forall>  y\<in>B - A. A \<union> {y} \<in> F \<longrightarrow> B - {y} \<union> {x} \<notin> F))"

lemma x_props: "A \<in> F \<and> B \<in> F \<and> A \<subseteq> B \<and> basis F B \<and>  x \<in> E - B \<and>
                  A \<union> {x} \<in> F  \<and> (\<forall>  y\<in>B - A. A \<union> {y} \<in> F \<longrightarrow> B - {y} \<union> {x} \<notin> F)"
  by(unfold x_def )(rule someI_ex[OF B_props])

lemma ABx_props: "A \<in> F" "B \<in> F" "A \<subseteq> B" "basis F B" "x \<in> E - B" 
  "A \<union> {x} \<in> F"  "(\<And> y. y\<in>B - A \<Longrightarrow> A \<union> {y} \<in> F \<Longrightarrow> B - {y} \<union> {x} \<notin> F)"
  using x_props by auto

definition "Y = {y | y. y \<in> B - A \<and> insert y A \<in> F}"

lemma Y_in_B_without_A: "Y \<subseteq> B -  A"
  using Y_def by blast

lemma there_is_A_list: "(\<exists>l. set l = A \<and> (\<forall>i\<le>length l. set (take i l) \<in> F) \<and> distinct l)"
  using  accessible_characterisation contains_empty_set greedoid_accessible ss_assum x_props by blast

definition "A_list = (SOME l. set l = A \<and> (\<forall>i\<le>length l. set (take i l) \<in> F) \<and> distinct l)"

lemma A_list_props: "set A_list = A" "(\<forall>i\<le>length A_list. set (take i A_list) \<in> F)" "distinct A_list"
  "(\<And> i. i\<le>length A_list \<Longrightarrow> set (take i A_list) \<in> F)"
  by (smt (verit, del_insts) A_list_def someI_ex there_is_A_list)+

lemma finites: "finite A" "finite B" "finite Y"
  using  finite_Diff finite_subset[of _ E] ss_assum x_props 
  by(auto simp add: Y_def set_system_def)

lemma B_without_Y_without_A: "\<exists> l. set l = B - Y - A \<and> distinct l"
  by (auto intro: finite_distinct_list simp add: finites)

definition "BYA_list = (SOME l. set l = B - Y - A \<and> distinct l)"

lemma BYA_list_props: "set BYA_list = B - Y - A" "distinct BYA_list"
  using  someI_ex[OF B_without_Y_without_A] 
  by(auto simp add: BYA_list_def)

lemma B_without_A_without_Y_is: " B - Y - A = {y |y. y \<in> B - A \<and> \<not> insert y A \<in> F}"
  by(auto simp add: Y_def)

lemma Y_list_exists: "\<exists> l. set l = Y \<and> distinct l"
  by (auto intro: finite_distinct_list simp add: finites)

definition "Y_list = (SOME l. set l = Y \<and> distinct l)"

lemma Y_list_props: "set Y_list = Y" "distinct Y_list"
  using  someI_ex[OF Y_list_exists] 
  by(auto simp add: Y_list_def)

lemma E_without_W_without_x: "\<exists> l. set l = E - B - {x} \<and> distinct l"
  by (auto intro: finite_distinct_list simp add: finites finite_E)

definition "EBx_list = (SOME l. set l = E - B - {x} \<and> distinct l)"

lemma EBx_list_props: "set EBx_list = E - B - {x}" "distinct EBx_list"
  using  someI_ex[OF E_without_W_without_x] 
  by(auto simp add: EBx_list_def)

definition "es = EBx_list@Y_list@[x]@BYA_list@rev A_list"

lemma all_in_E: "A \<subseteq> E" "B \<subseteq> E" "Y \<subseteq> E"
  using  ABx_props(1,2,3) ss_assum Y_in_B_without_A by(auto simp add: set_system_def)

lemma es_prop: "set es = E" "distinct es"
  using EBx_list_props BYA_list_props  ABx_props(1-3,5) Y_in_B_without_A all_in_E A_list_props(1,3) Y_list_props 
  by(auto simp add:  es_def) 

definition "c y =
           (if y \<in> B - Y then (2::real)
            else if y \<in> insert x Y then (1::real)
            else if y \<in> E - B - {x} then 0
            else undefined)"

lemma costs_are:
  "y \<in> A ==> c y = 2"
  "y \<in> B - Y - A \<Longrightarrow> c y = 2"
  "y \<in> B - Y\<Longrightarrow> c y = 2"
  "c x = 1"
  "y \<in> Y \<Longrightarrow> c y = 1"
  "y \<in> E - B - {x} \<Longrightarrow> c y = 0"
  "y \<in> E \<Longrightarrow> c y \<le> 2"
  "y \<in> B \<Longrightarrow> c y \<ge> 1"
  "y \<in> E \<Longrightarrow> c y \<ge> 0"
  using ABx_props(5,3) all_in_E Y_in_B_without_A by(auto simp add: c_def split: if_split)

definition "costs = sum c"

lemma costs_modular: "valid_modular_weight_func E costs"
  using  sum_is_modular 
  by (fastforce simp add: valid_modular_weight_func_def costs_def)

lemmas result_props_specialised = result_props[OF es_prop, of costs]

definition "unique P = (\<forall> x y. P x \<longrightarrow> P y \<longrightarrow> x = y)"

lemma injective_predicate_unique_split:
  "distinct xs \<Longrightarrow> unique P \<Longrightarrow> xs = xs11@[xx]@xs12 \<Longrightarrow> xs = xs21@[yy]@xs22
         \<Longrightarrow> P xx \<Longrightarrow> P yy \<Longrightarrow> xs11=xs21 \<and> xx = yy \<and> xs12 = xs22"
  by (smt (verit, del_insts) Cons_eq_appendI append.left_neutral append_Cons_eq_iff distinct.simps(2)
      distinct_append in_set_conv_decomp unique_def inj_on_eq_iff not_distinct_conv_prefix)

definition "last_in_list P xs y = (y \<in> set xs \<and> P y \<and> (\<nexists> xs1 xs2 z. xs = xs1@[y]@xs2 \<and> z \<in> set xs2 \<and> P z))"

lemma last_in_list_unique: "unique (last_in_list P xs)"
  by (auto simp add: unique_def last_in_list_def  )(smt (verit, del_insts) Un_iff append.assoc append_Cons in_set_conv_decomp_first insert_iff list.set(2) set_append)

lemma find_best_cand_chain_gives_A_suffix:
  "(\<And> i. i < length l \<Longrightarrow> Some (l ! i) =
         find_best_candidate es costs (set (drop (i + 1) l)))
       \<Longrightarrow> (\<And> i. i < length l \<Longrightarrow> set (drop (i+1) l) \<in> F)
       \<Longrightarrow> length l \<le> length A_list \<Longrightarrow> l = rev (take (length l) A_list)"
proof(induction l)
  case Nil
  then show ?case by simp
next
  case (Cons x l)
  note IH = this
  show ?case 
  proof(cases A_list)
    case Nil
    then show ?thesis 
      using IH(4) by simp
  next
    case (Cons a arest)
    hence a1: "length A_list - Suc (length l) < length A_list"
      by auto
    have a2: " Suc (length l) \<le> length A_list"
      using Cons  IH(4) by simp
    have l_is:"l = rev (take (length l) A_list)"
      using IH(4) by (auto intro!: IH(1) IH(2)[of "_ + 1", simplified] IH(3)[of "Suc _", simplified])
    have split_off_first:"take ( length (x # l)) A_list = 
           take ( length l) A_list @[A_list ! ( (length l))]"
      using IH(4)
      by (simp add: take_Suc_conv_app_nth)
    have new_elem_in_es: "A_list ! ( (length l)) \<in> set es"
      using A_list_props(1) a2 all_in_E(1) es_prop(1) by auto
    thm IH(2)[of 0, simplified]
    have "x =  A_list ! (length l)"
    proof-
      have l_in_F:"set l \<in> F" 
        using IH(3)[of 0, simplified]  by simp
      hence l_in_E: "set l \<subseteq> E" 
        using ss_assum by(simp add:  set_system_def)
      have x_is_best_candidate:"find_best_candidate es costs (set l) = Some x"
        using IH(2)[of 0, simplified] by simp
      obtain es1 es2 where es_split:" es = es1 @ [x] @ es2" "x \<notin> set l"
        "insert x (set l) \<in> F"
        "(\<And> y. y\<in>E - set l \<Longrightarrow> insert y (set l) \<in> F \<Longrightarrow> elements_costs costs y \<le> elements_costs costs x)"
        "\<not> (\<exists>y\<in>set es2. y \<notin> set l \<and> insert y (set l) \<in> F \<and> elements_costs costs x \<le> elements_costs costs y)"
        using find_best_candidate_some[OF es_prop l_in_E x_is_best_candidate l_in_F] by auto 

      define P where "P =(\<lambda> x. (\<exists>es1 es2.
     es = es1 @ [x] @ es2 \<and> x \<notin> set l \<and> insert x (set l) \<in> F \<and>
     (\<forall>y\<in>E - set l. insert y (set l) \<in> F \<longrightarrow> elements_costs costs y \<le> elements_costs costs x)))"
      have x_last_P: "last_in_list P es x"
        using es_split
        by (auto simp add: last_in_list_def P_def )
          (metis DiffI append_Cons_eq_iff 
            distinct_append es_prop(1) es_prop(2) in_set_conv_decomp not_distinct_conv_prefix)
      have insert_new_element_is:"insert (A_list ! length l) (set (take (length l) A_list)) = (set (take (Suc (length l)) A_list))"
        using split_off_first by auto
      have " (A_list ! length l) \<in> set A_list" 
        using a2 by auto
      hence costs_of_new:"c (A_list ! length l) = 2 " 
        by(auto intro!: costs_are(1)simp add: A_list_props(1))   
      have A_last_P: "last_in_list P es ( A_list !  (length l))"
        unfolding P_def last_in_list_def
      proof(goal_cases)
        case 1
        define index where "index = length l"
        hence index_valid:"index < length A_list"
          by (simp add: a2 less_eq_Suc_le)
        have "A_list ! length l \<in> set es"
          using new_elem_in_es by auto
        moreover have es_split: "es = (take  (length es - index - 1) es) @ [A_list ! index]
                    @ rev (take index (A_list))"
          using index_valid
          by(unfold es_def append.assoc[symmetric], subst take_append, simp,
              subst rev_append[of  _ "[_]", simplified rev.simps(2)[of _ Nil]
                rev.simps(1) append.left_neutral append_Cons[of _ Nil], symmetric]
              ,simp add:  take_Suc_conv_app_nth[OF index_valid, symmetric] rev_take)
        moreover have "A_list ! index \<notin> set l" 
          using  distinct_take[OF A_list_props(3)] l_is not_distinct_conv_prefix[of "take _ A_list"] 
            split_off_first
          by(unfold index_def[symmetric]) auto
        moreover have "insert (A_list ! index) (set l) \<in> F"
          using A_list_props(4)[OF  a2] IH(4) index_def insert_new_element_is l_is
          by(unfold index_def[symmetric]) simp 
        moreover have " (\<forall>y\<in>E - set l.
            insert y (set l) \<in> F \<longrightarrow> elements_costs costs y \<le> elements_costs costs (A_list ! length l))"  
          by (auto simp add:  elements_costs_def costs_of_new costs_def intro: costs_are(7))
        moreover have "(\<nexists>xs1 xs2 z.
        es = xs1 @ [A_list ! length l] @ xs2 \<and>
        z \<in> set xs2 \<and>
        (\<exists>es1 es2.
            es = es1 @ [z] @ es2 \<and>
            z \<notin> set l \<and>
            insert z (set l) \<in> F \<and>
            (\<forall>y\<in>E - set l. insert y (set l) \<in> F \<longrightarrow> elements_costs costs y \<le> elements_costs costs z)))"
        proof(rule ccontr, goal_cases)
          case 1
          then obtain xs1 xs2 z where  es_split2:
            "es = xs1 @ [A_list ! length l] @ xs2" "z \<in> set xs2""z \<notin> set l"
            by metis
          have "xs2 = rev (take index (A_list))"
            using  injective_predicate_unique_split[OF es_prop(2) _ es_split es_split2(1),
                of "\<lambda> x.  x = A_list ! index"]
            by(auto simp add: index_def[symmetric] unique_def) 
          moreover have "rev (take index (A_list)) =  l"
            using l_is by(simp add: index_def[symmetric])
          ultimately show False 
            using es_split2(2,3) by simp
        qed
        ultimately show ?case by(auto simp add: index_def)
      qed
      show "x = A_list ! length l" 
        using  A_last_P last_in_list_unique x_last_P
        by(force simp add: unique_def)
    qed 
    thus ?thesis 
      using l_is split_off_first by force
  qed
qed

lemma find_best_cand_chain_gives_A:
  "(\<And> i. i < length l \<Longrightarrow> Some (l ! i) =
         find_best_candidate es costs (set (drop (i + 1) l)))
       \<Longrightarrow> (\<And> i. i < length l \<Longrightarrow> set (drop (i+1) l) \<in> F)
       \<Longrightarrow> length l = length A_list \<Longrightarrow> l = rev A_list"
  by(subst find_best_cand_chain_gives_A_suffix[of l]) auto

lemmas properties_of_result = initial_props[OF es_prop] result_props[OF es_prop]
  algorithm_computes_basis[OF es_prop]

lemma solution_looks_like:
  "\<exists> others. greedoid_greedy es costs Nil = others @ [x] @ rev A_list"
proof-
  have length_below:"length (greedoid_greedy es costs Nil) > length A_list"
  proof(rule ccontr, goal_cases)
    case 1
    define index where "index = length (local.greedoid_greedy es costs [])"
    from 1 have asm: "length A_list \<ge> length (local.greedoid_greedy es costs [])" by simp
    have a1:"local.greedoid_greedy es costs [] 
                     = rev (take (length (local.greedoid_greedy es costs [])) A_list)"
      using properties_of_result(9,11) 
      by(auto intro!: find_best_cand_chain_gives_A_suffix asm
          simp add: invar_tails_indep_def invar_find_best_cand_def)
    have a2: "\<nexists> y. y \<in> E - set (greedoid_greedy es costs []) \<and> 
                  insert y ( set (greedoid_greedy es costs [])) \<in> F" 
      using properties_of_result(7,10) find_best_candidate_none[OF es_prop]  ss_assum  
      by(force simp add: set_system_def)
    moreover have "x \<in> E - set (greedoid_greedy es costs [])"
      using  A_list_props(1) a1  in_set_takeD[of x "length (greedoid_greedy es costs [])" A_list]
        set_rev[of "take (length (local.greedoid_greedy es costs [])) A_list"] x_props
      by auto 
    moreover have "length A_list = length (local.greedoid_greedy es costs []) \<Longrightarrow>
                      insert x ( set (greedoid_greedy es costs [])) \<in> F"
      using  A_list_props(1) a1 x_props by auto
    moreover have "length A_list > length (local.greedoid_greedy es costs []) \<Longrightarrow>
                      insert (A_list ! length (local.greedoid_greedy es costs []) ) ( set (greedoid_greedy es costs [])) \<in> F"
      unfolding index_def[symmetric] 
      unfolding a1[simplified index_def[symmetric]] rev_take
      apply(rule back_subst, rule A_list_props(4)[of "index + 1"])
      using set_take_union_nth
      by(auto intro!: cong[OF refl, of _  _ "\<lambda> x. x \<in> F"] simp  add: rev_take[of "index" A_list, symmetric])
    moreover have "length A_list > length (local.greedoid_greedy es costs []) \<Longrightarrow>
                  (A_list ! length (local.greedoid_greedy es costs []) )
                 \<in> E - ( set (greedoid_greedy es costs []))"
      using A_list_props(1,3) distinct_take id_take_nth_drop not_distinct_conv_prefix  set_rev
      using  all_in_E(1) nth_mem[of index A_list] 
      by (fastforce simp add: index_def[symmetric] a1[simplified index_def[symmetric]])
    ultimately show False
      using asm 
      by(cases "length (local.greedoid_greedy es costs []) = length A_list") auto
  qed
  have tail_is:"drop (length (local.greedoid_greedy es costs []) - length A_list) (local.greedoid_greedy es costs [])
       = rev A_list"
    using length_below
    by(auto intro: find_best_cand_chain_gives_A 
        simp add:  mp[OF HOL.spec[OF result_props_specialised(4)[simplified invar_find_best_cand_def]]] 
        mp[OF HOL.spec[OF result_props_specialised(6)[simplified invar_tails_indep_def]]]
        add.commute)
  have b1:"x \<in> E - set A_list"
    using A_list_props(1) x_props by blast
  have b2:"(set A_list) \<in> F" 
    using A_list_props(1) x_props by fastforce
  hence b3: "(set A_list)\<subseteq> E"
    using  ss_assum by(auto simp add: set_system_def)
  have b4:"insert x (set A_list) \<in> F" 
    using A_list_props(1) x_props by fastforce
  have "find_best_candidate es costs (set A_list) \<noteq> None"
    using  find_best_candidate_none[OF es_prop b3 _ b2] b1 b4 by auto
  then obtain cand where cand_is: "find_best_candidate es costs (set A_list) = Some cand" by auto
  obtain es1 es2 where es1es2:"es = es1 @ [cand] @ es2" "cand \<notin> set A_list"
    "insert cand (set A_list) \<in> F"
    "(\<And> y. y\<in>E - set A_list \<Longrightarrow> insert y (set A_list) \<in> F \<Longrightarrow> elements_costs costs y \<le> elements_costs costs cand)"
    "\<not> (\<exists>y\<in>set es2.
          y \<notin> set A_list \<and> insert y (set A_list) \<in> F \<and> elements_costs costs cand \<le> elements_costs costs y)"
    using  find_best_candidate_some[OF es_prop b3 cand_is b2] by auto
  have cand_is_x:"cand = x"
  proof(rule ccontr, goal_cases)
    case 1
    note x_not_cand = this
    hence x_in_es1_or_es2: "x \<in> set es1 \<or> x \<in> set es2"
      using b1 es1es2(1) es_prop(1) by force
    have "elements_costs costs cand \<le> 1" 
      using es1es2(2) 1 es1es2(3) ss_assum
      by(auto simp add: elements_costs_def costs_def c_def A_list_props(1) Y_def set_system_def)
    hence "x \<notin> set es2"
      using es1es2(5) b1 b4 
      by(auto simp add: elements_costs_def costs_def  costs_are(4))
    hence x_in_es1:"x \<in> set es1"
      using x_in_es1_or_es2 by auto
    have "cand \<in> set ( BYA_list @ A_list)"
    proof(rule ccontr, goal_cases)
      case 1
      hence  "cand \<in> set (EBx_list @ Y_list)"
        using  es1es2(1) x_in_es1 A_list_props(1) BYA_list_props(1)  EBx_list_props(1) Y_list_props(1)  es_prop 
        by (auto simp add:  es_def)
      then obtain as bs where "EBx_list @ Y_list = as@[cand]@bs"
        by (metis append.left_neutral append_Cons in_set_conv_decomp)
      hence es_split4: "es = as@[cand]@bs@[x]@BYA_list @ rev A_list" 
        unfolding es_def by simp
      have "as = es1" 
        using append_Cons_eq_iff[of cand es1 es2 as "bs @ [x] @ BYA_list @ rev A_list"] 
          es1es2(1-3, 5) es_prop(2) not_distinct_conv_prefix[of es]
        by(simp add: es_split4)
      hence "\<not> distinct es"
        using \<open>x \<notin> set es2\<close> es1es2(1) es_split4 by fastforce
      thus False
        by (simp add: es_prop(2))
    qed
    moreover have "cand \<notin> set BYA_list"
      using A_list_props(1) BYA_list_props(1) B_without_A_without_Y_is es1es2(3) by auto
    ultimately have "cand \<in> set A_list" by simp
    thus False
      by (simp add: es1es2(2))
  qed
  have cand_is_2:" (local.greedoid_greedy es costs []) !
                        (length (local.greedoid_greedy es costs []) - length A_list - 1) = cand"
    using Suc_diff_Suc tail_is  cand_is length_below
      mp[OF HOL.spec[OF result_props_specialised(4)[simplified invar_find_best_cand_def]],
        of "length (local.greedoid_greedy es costs []) - length A_list - 1"]
    by simp
  have "local.greedoid_greedy es costs [] = 
                 take (length (local.greedoid_greedy es costs []) - length A_list - 1) (local.greedoid_greedy es costs [])
                 @[x]@ rev A_list" 
    using  Suc_diff_Suc length_below  tail_is 
      id_take_nth_drop [of "length (local.greedoid_greedy es costs []) - length A_list - 1" " (local.greedoid_greedy es costs [])"]
    by (auto simp add: cand_is_x[symmetric] cand_is_2[symmetric] tail_is[symmetric])
  thus ?thesis by auto
qed

lemma f_zero_sum_sero: "(\<And> x. x \<in> X \<Longrightarrow> f x = 0) \<Longrightarrow> sum f X =  0"
  by auto

lemma no_opt_solution: "\<not> opt_basis costs (set (greedoid_greedy es costs Nil))"
proof-
  have solution_in_E:" set (greedoid_greedy es costs Nil) \<subseteq> E"
    by (meson properties_of_result(7) set_system_def ss_assum)
  have "B \<inter> (E - set (greedoid_greedy es costs Nil)) \<noteq> {}"
  proof(rule ccontr, goal_cases)
    case 1
    hence  "B \<subset>  set (greedoid_greedy es costs Nil)"
      using solution_looks_like x_props  all_in_E(2) by auto
    hence "\<not> basis F B" 
      using  properties_of_result(12) by(auto simp add: maximal_def basis_alt_def)
    then show ?case
      by (simp add: ABx_props(4))
  qed
  then obtain y where y_prop: "y \<in> E" "y \<in> B" "y \<notin> set (greedoid_greedy es costs Nil)"
    by auto 
  obtain others where others: "greedoid_greedy es costs [] = others @ [x] @ rev A_list"
    using solution_looks_like by presburger
  hence sol_distinct: "distinct (others @ [x] @ rev A_list)"
    using result_props_specialised(3) by argo
  have y_not_in_others:"y \<notin> set others" "y\<noteq> x" "y \<notin> set A_list"
    using others y_prop(3) by auto 
  have costs_less_eq_B:"costs (set (greedoid_greedy es costs Nil)) \<le> costs B"
    unfolding costs_def
  proof-
    have "sum c (set (local.greedoid_greedy es (sum c) [])) =
         sum c (set others) +  sum c {x} +  sum c (set A_list)"
      using  sol_distinct  others[simplified costs_def] 
      by (auto simp add:  comm_monoid_add_class.sum.union_disjoint[symmetric])
    also have "... = sum c (set others \<inter> B) + (sum c (set others - B)) +  sum c {x} +  sum c (set A_list)"
      using sum.Int_Diff by auto
    also have "... = sum c (set others \<inter> B) +  sum c {x} +  sum c (set A_list)"
      using others solution_in_E result_props_specialised(3)  
      by (auto intro!: f_zero_sum_sero costs_are(6))
    also have "... \<le>  sum c (set others \<inter> B) +  sum c {y} +  sum c (set A_list)"
      using y_prop(2) by(auto simp add: costs_are(4) intro!: costs_are(8))
    also have "... = sum c ((set others \<inter> B) \<union> {y} \<union> set A_list)"
      using y_not_in_others others result_props_specialised(3)
      by (subst  comm_monoid_add_class.sum.union_disjoint[symmetric] | 
          force simp add:  y_not_in_others(3))+
    also have "... \<le> sum c B"
      using costs_are(8) A_list_props(1)  x_props y_prop(2) 
      by  (force intro: sum_mono2 simp add: finites(2))
    finally show "sum c (set (local.greedoid_greedy es (sum c) [])) \<le> sum c B" by simp
  qed
  show ?thesis
  proof(cases "costs (set (local.greedoid_greedy es costs [])) < costs B")
    case True
    then show ?thesis 
      using x_props by (fastforce simp add: opt_basis_def)
  next
    case False
    hence costs_eq:"costs (set (local.greedoid_greedy es costs [])) = costs B"
      using costs_less_eq_B by auto
    have "B \<inter>  (E - (set (local.greedoid_greedy es costs []))) = {y} \<and> c y = 1"
    proof(rule ccontr, goal_cases)
      case 1
      have "sum c (set (local.greedoid_greedy es (sum c) [])) =
         sum c (set others) +  sum c {x} +  sum c (set A_list)"
        using  sol_distinct  others[simplified costs_def] 
        by (auto simp add:  comm_monoid_add_class.sum.union_disjoint[symmetric])
      also have "... = sum c (set others \<inter> B) + (sum c (set others - B)) +  sum c {x} +  sum c (set A_list)"
        using sum.Int_Diff by auto
      also have "... = sum c (set others \<inter> B) +  sum c {x} +  sum c (set A_list)"
        using others solution_in_E result_props_specialised(3)  
        by (auto intro!: f_zero_sum_sero costs_are(6))
      finally have eq_result: "sum c (set (local.greedoid_greedy es (sum c) [])) =
              sum c (set others \<inter> B) + sum c {x} + sum c (set A_list)" by simp
      have "c y = 2 \<Longrightarrow> False"
      proof-
        assume asm: "c y = 2"
        have "sum c (set others \<inter> B) +  sum c {x} +  sum c (set A_list) 
               \<le>  sum c (set others \<inter> B) +  sum c {y} +  sum c (set A_list) - 1"
          using y_prop(2)  costs_are(8) asm by(auto simp add: costs_are(4)) 
        also have "... =  sum c ((set others \<inter> B) \<union> {y} \<union> set A_list) -  1"
          using y_not_in_others others result_props_specialised(3) 
          by simp (subst  comm_monoid_add_class.sum.union_disjoint[symmetric] | 
              force simp add:  y_not_in_others(3))+
        also have "... \<le> sum c B - 1"
          using costs_are(8) A_list_props(1)  x_props y_prop(2)
          by  (force intro: sum_mono2 simp add: finites(2))
        finally have "sum c (set (local.greedoid_greedy es (sum c) [])) \<le> sum c B -  1" 
          using eq_result costs_eq by auto
        thus False 
          using  costs_eq by(auto simp add: costs_def)
      qed
      hence "c y = 1"
        using costs_are(3) costs_are(5) y_prop(2) by auto
      hence "B \<inter>  (E - (set (local.greedoid_greedy es costs []))) \<supset> {y}"
        using all_in_E(2) y_prop(2) y_prop(3) 1 by auto
      then obtain z where z_prop:"z \<in> B" "z \<in> (E - (set (local.greedoid_greedy es costs [])))"
        "z \<noteq> y" by auto
      have "sum c (set (local.greedoid_greedy es (sum c) [])) =
         sum c (set others) +  sum c {x} +  sum c (set A_list)"
        using  sol_distinct  others[simplified costs_def] 
        by (auto simp add:  comm_monoid_add_class.sum.union_disjoint[symmetric])
      have "sum c (set others \<inter> B) +  sum c {x} +  sum c (set A_list) \<le>  sum c (set others \<inter> B) +  sum c {y, z} +  sum c (set A_list) - 1"
        using y_prop(2) z_prop costs_are(8) ordered_ab_semigroup_add_class.add_mono[OF costs_are(8) costs_are(8), simplified, of y z]
        by(auto simp add: costs_are(4))
      also have "... =  sum c ((set others \<inter> B) \<union> {y, z} \<union> set A_list) -  1"
        using y_not_in_others others result_props_specialised(3) z_prop
        by simp (subst  comm_monoid_add_class.sum.union_disjoint[symmetric] | 
            force simp add:  y_not_in_others(3))+
      also have "... \<le> sum c B - 1"
        using costs_are(8) A_list_props(1)  x_props y_prop(2) z_prop
        by  (force intro: sum_mono2 simp add: finites(2))
      finally have "sum c (set (local.greedoid_greedy es (sum c) [])) \<le> sum c B -  1" 
        using eq_result by simp
      thus False 
        using  costs_eq by(auto simp add: costs_def)
    qed
    hence solution_shares_y: "B \<inter> (E - set (local.greedoid_greedy es costs [])) = {y}" "c y = 1" by auto
    hence y_in_Y: "y \<in> Y"
      using costs_are(3) by fastforce
    show ?thesis 
    proof(cases "(E - B - {x}) \<inter> (set (local.greedoid_greedy es costs [])) = {}")
      case True
      hence solution_is_now: "(set (local.greedoid_greedy es costs [])) = B - {y} \<union> {x}"
        using others solution_in_E  y_not_in_others(1,3) solution_shares_y all_in_E(2) by auto
      hence "(B - {y} \<union> {x}) \<in> F"
        using result_props_specialised(2) by argo
      moreover have "y \<in> B -  A"
        using A_list_props(1) y_not_in_others(3) y_prop(2) by blast
      moreover have "A \<union> {y} \<in> F" 
        using y_in_Y by (auto simp add: Y_def)
      ultimately have False 
        using ABx_props(7) by blast
      thus ?thesis by simp
    next
      case False
      moreover have "(B \<union> {x}) \<inter> set (local.greedoid_greedy es costs []) = 
             (B - {y} \<union> {x})"
        using all_in_E(2) others solution_shares_y(1) by auto
      moreover have "card (set (local.greedoid_greedy es costs [])) = 
                     card ((B \<union> {x}) \<inter> set (local.greedoid_greedy es costs []))
                   + card (set (local.greedoid_greedy es costs []) - B - {x})"
        by(subst card_Un_disjoint[symmetric]) (auto intro!: cong[OF refl, of  _ _ card])
      moreover have "set (local.greedoid_greedy es costs []) - B - {x} = 
                 (E - B - {x}) \<inter> set (local.greedoid_greedy es costs [])" 
        using solution_in_E by blast
      ultimately have "card (set (local.greedoid_greedy es costs [])) > card  (B - {y} \<union> {x})"
        by (simp add: card_gt_0_iff)
      also have " card  (B - {y} \<union> {x}) = card B" 
        using ABx_props(5) card.remove[OF finites(2) y_prop(2)] 
        by (auto simp add: finites(2))
      ultimately have "card (set (local.greedoid_greedy es costs [])) > card B"
        by simp
      then obtain z where "z \<in> (set (local.greedoid_greedy es costs [])) -  B"
        "insert z B \<in> F"
        using ABx_props(2) result_props_specialised(2) third_condition by auto
      hence "\<not> basis F B" 
        by(auto simp add: maximal_def basis_alt_def)
      hence False
        by (simp add: ABx_props(4))
      thus ?thesis by simp
    qed
  qed
qed

lemma costs_is_empty_minimal: "empty_minimal E costs"
  by(auto simp add: empty_minimal_def costs_def 
      intro: ordered_comm_monoid_add_class.sum_nonneg costs_are(9))
end

theorem greedoid_characterisation:
  "(\<forall> c es. valid_modular_weight_func E c \<and>  E = set es \<and> distinct es 
          \<longrightarrow> opt_basis c (set (greedoid_greedy es c Nil)))
 \<longleftrightarrow> strong_exchange_property E F"
  using no_opt_solution  costs_is_empty_minimal costs_modular es_prop  strong_exchange_modular_opt
  by fast

end

locale greedoid_greedy_impl_spec =
  fixes orcl_impl::"'a \<Rightarrow> 'sol_set \<Rightarrow> bool"
    and to_sol_set::"'sol_set \<Rightarrow> 'a set"
    and sol_inv::"'sol_set \<Rightarrow> bool"
    and sol_insert::"'a \<Rightarrow> 'sol_set \<Rightarrow> 'sol_set"
    and sol_empty::'sol_set
    and to_compl_set::"'compl_set \<Rightarrow> 'a set"
    and compl_inv::"'compl_set \<Rightarrow> bool"
    and compl_del::"'a \<Rightarrow> 'compl_set \<Rightarrow> 'compl_set"
    and full_compl::"'compl_set"
    and compl_iterate:: "('a \<Rightarrow> 'a option \<Rightarrow> 'a option) \<Rightarrow> 'compl_set \<Rightarrow> 'a option \<Rightarrow> 'a option"
    and flaten_compl::"'compl_set \<Rightarrow> 'a list"
    and c_impl::"'a \<Rightarrow> real"
    and cc::"'a set \<Rightarrow> real"
begin
definition "find_best_candidate_impl X E_without_X = 
           compl_iterate (\<lambda> e acc. if  \<not> (orcl_impl e X) then acc
                           else (case acc of None \<Rightarrow> Some e |
                                    Some d \<Rightarrow>
                (if c_impl e > c_impl d then Some e
                             else Some d))) E_without_X None"

partial_function (tailrec) greedoid_greedy_impl::"'sol_set \<times> 'compl_set \<Rightarrow> 'sol_set"  where
  "greedoid_greedy_impl sol = 
 (case sol of (X, E_without_X) \<Rightarrow>
    (case  (find_best_candidate_impl X E_without_X) of 
            Some e \<Rightarrow> greedoid_greedy_impl (sol_insert e X, compl_del e E_without_X) 
          | None \<Rightarrow> X))"

definition "greedoid_init = (sol_empty, full_compl)"

lemmas [code] = greedoid_greedy_impl.simps find_best_candidate_impl_def greedoid_init_def
end


locale greedoid_greedy_impl = greedoid_algorithm  where E= "E::'a set" +
  greedoid_greedy_impl_spec where orcl_impl = "orcl_impl::'a \<Rightarrow> 'sol_set \<Rightarrow> bool" 
for E orcl_impl +
assumes orcl_impl_corresp: "\<And> X x. to_sol_set X \<subseteq> E \<Longrightarrow> x \<in> E - to_sol_set X 
                          \<Longrightarrow> to_sol_set X \<in> F \<Longrightarrow> sol_inv X \<Longrightarrow>
                               orcl_impl x X = orcl x (to_sol_set X)"
assumes sol_set_spec: "to_sol_set sol_empty = {}"
  "sol_inv sol_empty"
  "\<And> x X. sol_inv X \<Longrightarrow> sol_inv (sol_insert x X)"
  "\<And> x X. sol_inv X \<Longrightarrow> to_sol_set (sol_insert x X) = insert x (to_sol_set X)"
assumes compl_set_spec:"compl_inv full_compl"
  "\<And> x X. compl_inv X \<Longrightarrow> compl_inv (compl_del x X)"
  "\<And> x X. compl_inv X \<Longrightarrow> to_compl_set (compl_del x X) = (to_compl_set X) - {x}"
assumes compl_iterate: "\<And> X init. compl_inv X \<Longrightarrow> compl_iterate f X init = foldr f (flaten_compl X) init "
assumes flaten_compl:  "\<And> X. compl_inv X \<Longrightarrow> distinct (flaten_compl X)"
  "\<And> X. compl_inv X \<Longrightarrow> set (flaten_compl X) = to_compl_set X"
  "\<And> X x. compl_inv X \<Longrightarrow> x \<in> to_compl_set X \<Longrightarrow>
                                 \<exists> xs1 xs2. flaten_compl X = xs1 @[x]@xs2 \<and>
                                            flaten_compl (compl_del x X) = xs1@xs2"  
assumes c_impl: "\<And> x. x\<in> E \<Longrightarrow> c_impl x = cc {x}"
begin

context 
  fixes es::"'a list"
begin

context 
  assumes es_prop: "set es = E" "distinct es"
    and flaten_full_compl_es: "flaten_compl full_compl = es"
begin

lemma same_candidate:
  assumes "to_sol_set X \<subseteq> E" "to_sol_set X \<in> F" "flaten_compl E_without_X = filter (\<lambda> x. x \<notin> to_sol_set X) es"
    "compl_inv E_without_X" "sol_inv X"
  shows "find_best_candidate_impl X E_without_X = find_best_candidate es cc (to_sol_set X)"
  unfolding find_best_candidate_def find_best_candidate_impl_def
    compl_iterate[OF assms(4)] assms(3)
proof(goal_cases)
  case 1
  define init where "init = (None::'a option)"
  let ?iteration = "(\<lambda>e acc.
         if e \<in> to_sol_set X \<or> \<not> orcl e (to_sol_set X) then acc
         else case acc of None \<Rightarrow> Some e
              | Some d \<Rightarrow> if elements_costs cc d < elements_costs cc e then Some e else Some d)"
  have some_candidate_in_E: "set es \<subseteq> E \<Longrightarrow> (\<And> a. init = Some a \<Longrightarrow> a \<in> E) \<Longrightarrow> foldr ?iteration es init = Some a \<Longrightarrow> a \<in> E" 
    for a es init
  proof(induction es arbitrary: init)
    case Nil
    then show ?case by simp
  next
    case (Cons x es)
    thus ?case 
      by(cases "x \<in> to_sol_set X \<or> \<not> orcl x (to_sol_set X)",
          all \<open>cases "foldr ?iteration es init"\<close>,
          all \<open>cases "elements_costs cc (the (foldr ?iteration es init)) < elements_costs cc x"\<close>)
        auto
  qed
  have "(\<And> a. init = Some a \<Longrightarrow> a \<in> E)" by(auto simp add: init_def)
  then show ?case
    using equalityD1[OF es_prop(1)] 
    unfolding init_def[symmetric]
  proof(induction es arbitrary: init)
    case Nil
    then show ?case by simp
  next
    case (Cons x es)
    have P_of_ifI: "(b \<Longrightarrow> P left) \<Longrightarrow> (\<not> b \<Longrightarrow> P right) \<Longrightarrow> P (if b then left else right)"
      for b P left right by auto
    show ?case
    proof(subst foldr_Cons, subst filter.simps(2), rule P_of_ifI, all \<open>(subst foldr_Cons)?\<close>,
        all \<open>(subst o_apply)+\<close>,
        goal_cases)
      case 1
      note x_not_in_X = this
      show ?case
      proof(rule if_cong, goal_cases)
        case 1
        then show ?case 
          using x_not_in_X assms(1,2,5) Cons(2,3)
          by (auto simp add:  orcl_impl_corresp)
      next
        case 2
        show ?case 
          using Cons(2,3) by(auto intro: Cons(1))
      next
        case 3
        hence "orcl x (to_sol_set X)"
          by simp
        show ?case 
          using Cons(2,3) 
          by(subst Cons(1) | intro option.case_cong[OF refl refl]| subst c_impl | 
              force simp add: c_impl elements_costs_def intro: some_candidate_in_E[of es init])+
      qed
    next
      case 2
      note two = this
      show ?case 
      proof(rule P_of_ifI, goal_cases)
        case 1
        show ?case 
          using Cons(2,3) by(auto intro: Cons(1))
      next
        case 2
        thus ?case using two by simp
      qed
    qed
  qed
qed

lemma same_result_general:
  assumes "greedoid_greedy_dom es cc xs" "set xs = to_sol_set X"
    and "to_sol_set X \<subseteq> E" "to_sol_set X \<in> F" "flaten_compl E_without_X = filter (\<lambda> x. x \<notin> to_sol_set X) es"
    "compl_inv E_without_X" "sol_inv X" "to_compl_set E_without_X = E- to_sol_set X" "distinct xs"
  shows "to_sol_set (greedoid_greedy_impl (X, E_without_X)) = set (greedoid_greedy es cc xs)"
  using assms(2-)
proof(induction arbitrary: X E_without_X rule: greedoid_greedy.pinduct[OF assms(1)])
  case (1 xs)
  note IH = this
  have same_cand:"find_best_candidate_impl X E_without_X = find_best_candidate es cc (set xs)"
    using IH(4-) by (auto intro: same_candidate simp add: IH(3))
  thm find_best_candidate_some[OF es_prop IH(4) _ IH(5)]
  show ?case 
  proof(subst greedoid_greedy_impl.simps,
      subst greedoid_greedy.psimps[OF IH(1)[simplified IH(4)]],
      subst prod.case, subst same_cand,
      cases "find_best_candidate es cc (set xs)", goal_cases)
    case 1
    then show ?case 
      using IH(3) by simp
  next
    case (2 a)
    note cand_props =  find_best_candidate_some[OF es_prop IH(4) 2[simplified IH(3)] IH(5)]
    hence cand_satisfies: "a \<notin> to_sol_set X" "insert a (to_sol_set X) \<in> F" "a \<in> E"
      "insert a (to_sol_set X) \<subseteq> E" "a \<in> to_compl_set E_without_X"
      using es_prop(1) IH(4,9) by auto
    have flaten_filter: "flaten_compl (compl_del a E_without_X) = filter (\<lambda>x. x \<notin> to_sol_set (sol_insert a X)) es"
    proof-
      obtain xs1 xs2 where xs1xs2:"flaten_compl E_without_X = xs1 @ [a] @ xs2" 
        "flaten_compl (compl_del a E_without_X) = xs1 @ xs2"
        using flaten_compl(3)[OF IH(7) cand_satisfies(5)] by auto
      moreover have "xs1 @ xs2 =  filter (\<lambda>x. x \<noteq> a) (xs1 @ [a] @ xs2)"
        using flaten_compl(1)[OF IH(7)]
        by(unfold xs1xs2(1), induction xs1, induction xs2) auto
      moreover have "filter (\<lambda>x. x \<noteq> a) (xs1 @ [a] @ xs2) 
            = filter (\<lambda>x. x \<notin> to_sol_set (sol_insert a X)) es"
        by(unfold sol_set_spec(4)[OF IH(8)] xs1xs2(1)[simplified IH(6), symmetric])
          (auto intro: filter_cong[OF refl])
      ultimately show ?thesis by simp
    qed       
    show ?case
      using cand_satisfies(2,4)   IH(9) 
      by(simp add: 2, intro IH(2)[OF 2])
        (auto intro: IH(2)[OF 2] simp add: IH(8) sol_set_spec(3) compl_set_spec(3)  IH(3) sol_set_spec(4) 2  
          IH(10)  cand_satisfies(1) IH(7) compl_set_spec(2) flaten_filter)
  qed
qed

lemma same_result: 
  "to_sol_set (greedoid_greedy_impl (sol_empty, full_compl)) = set (greedoid_greedy es cc Nil)"
  using  flaten_compl(2)[OF compl_set_spec(1)]
  by(intro same_result_general)
    (auto simp add: es_prop result_props(1) sol_set_spec(1) contains_empty_set
      flaten_full_compl_es  compl_set_spec(1) sol_set_spec(2))

end
end
end
end