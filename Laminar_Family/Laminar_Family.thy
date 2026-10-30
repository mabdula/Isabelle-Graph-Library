section \<open>Laminar Families\<close>

theory Laminar_Family
  imports Main "HOL-Eisbach.Eisbach" 
begin

lemma card_one_iff: "card X = 1 \<longleftrightarrow> (\<exists> x. X = {x})"
  by (simp add: card_1_singleton_iff) 

lemma inter_nemptyI: "\<lbrakk>A \<subseteq> B; A \<subseteq> C; A \<noteq> {}\<rbrakk> \<Longrightarrow> B \<inter> C \<noteq> {}"
  by auto

lemma card_geq_1_iff: "card X \<ge> Suc 0 \<longleftrightarrow> (finite X \<and> X \<noteq> {})"
  using  card_gt_0_iff[of X] by auto

lemma odd_disjoint_Union:
 "\<lbrakk>odd (card \<X>);\<And> X. X \<in> \<X> \<Longrightarrow> odd (card X);
   \<And> X Y. \<lbrakk> X \<in> \<X>; Y \<in> \<X>; X \<noteq> Y\<rbrakk> \<Longrightarrow> X \<inter> Y = {}\<rbrakk> \<Longrightarrow> odd (card (\<Union> \<X>))"
proof(subst card_Union_disjoint, goal_cases)
  case 3
  then show ?case 
  proof(subst semiring_parity_class.even_sum_iff, goal_cases)
    case 1
    then show ?case 
      using card.infinite[of \<X>] 
      by fastforce
  next
    case 2
    moreover hence "{a \<in> \<X>. odd (card a)} = \<X>" 
      by blast
    ultimately show ?case 
      by auto
  qed
qed (fastforce simp add: pairwise_def disjnt_def)+

definition "laminar U \<X> = 
            ((\<forall> X Y. X \<in> \<X> \<longrightarrow> Y \<in> \<X> \<longrightarrow> (X \<subseteq> Y \<or> Y \<subseteq> X \<or> X \<inter> Y = {}))
            \<and> (\<forall> X \<in> \<X>. X \<noteq> {} \<and> X \<subseteq> U))"

lemma laminarI: 
 "\<lbrakk>\<And> X Y. \<lbrakk>X \<in> \<X>; Y \<in> \<X>\<rbrakk> \<Longrightarrow> (X \<subseteq> Y \<or> Y \<subseteq> X \<or> X \<inter> Y = {});
   \<And> X.  X \<in> \<X> \<Longrightarrow> X \<noteq> {} \<and> X \<subseteq> U\<rbrakk> \<Longrightarrow> laminar U \<X>"
and  laminarE: 
 "\<lbrakk>laminar U \<X>;
   \<lbrakk>\<And> X Y. \<lbrakk>X \<in> \<X>; Y \<in> \<X>\<rbrakk> \<Longrightarrow> (X \<subseteq> Y \<or> Y \<subseteq> X \<or> X \<inter> Y = {});
    \<And> X.  X \<in> \<X> \<Longrightarrow> X \<noteq> {} \<and> X \<subseteq> U\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto | unfold laminar_def)+

lemma finite_U_finite_family:
  "\<lbrakk>finite U; laminar U \<X>\<rbrakk> \<Longrightarrow> finite \<X>"
  by(auto intro!: finite_UnionD[of \<X>] finite_subset[of "\<Union> \<X>" U] simp add: laminar_def)

lemma laminar_subset:
 "\<lbrakk>laminar U \<X>; U \<subseteq> U'; \<X>' \<subseteq> \<X>\<rbrakk> \<Longrightarrow> laminar U' \<X>'"
  by(auto intro!: laminarI elim!: laminarE) blast+

lemma laminar_subset':
 "\<lbrakk>laminar U' \<X>; \<X>' \<subseteq> \<X>; \<Union> \<X>' \<subseteq> U\<rbrakk> \<Longrightarrow> laminar U \<X>'"
  by(auto intro!: laminarI elim!: laminarE) blast+

lemma laminar_bigger_universe:
 "\<lbrakk>laminar U \<X>; U \<subseteq> U'\<rbrakk> \<Longrightarrow> laminar U' \<X>"
  by(auto intro!: laminarI elim!: laminarE) blast+

lemma laminar_union:
 "\<lbrakk>laminar U \<X>; laminar U' \<X>'; U \<inter> U' = {}\<rbrakk> \<Longrightarrow> laminar (U \<union> U') (\<X> \<union> \<X>')"
  by(auto intro!: laminarI 
           elim!: laminarE 
        simp add: subset_eq[of _ U'] subset_eq[of _ U] disjoint_iff[of U U'], force, force)
    (metis disjoint_insert(1) insert_absorb insert_subset)

lemma empty_nin_laminar: "laminar U \<X> \<Longrightarrow> {} \<notin> \<X>"
  by(auto elim!: laminarE)

lemma laminar_Union_finite: "\<lbrakk>finite U; laminar U \<X>\<rbrakk> \<Longrightarrow> finite (\<Union> \<X>)"
  by(auto intro!: finite_Union rev_finite_subset[of U] 
           elim!: laminarE simp add: finite_U_finite_family laminarI) 

definition "maximal_sets \<X> = { X| X. X \<in> \<X> \<and> (\<nexists> Y. Y \<in> \<X> \<and> Y \<supset> X)}"

lemma in_maximal_setsE:
  "\<lbrakk>X \<in> maximal_sets \<X>; \<lbrakk>X \<in> \<X>; \<And> Y. Y \<in> \<X> \<Longrightarrow> \<not> Y \<supset> X\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
and in_maximal_setsI:
  "\<lbrakk>X \<in> \<X>; \<nexists> Y. Y \<in> \<X> \<and> Y \<supset> X\<rbrakk> \<Longrightarrow> X \<in> maximal_sets \<X>"
and in_maximal_setsD:
  "\<lbrakk>X \<in> maximal_sets \<X>; X \<in> \<X>; Y \<in> \<X>\<rbrakk> \<Longrightarrow> \<not> Y \<supset> X"
  by (auto simp add: maximal_sets_def)

lemma not_in_maximal_setsE:
  "\<lbrakk>X \<notin> maximal_sets \<X>;
    X \<notin> \<X> \<Longrightarrow> P;
    (\<And> Y. \<lbrakk>Y \<in> \<X>; Y \<supset> X\<rbrakk> \<Longrightarrow> P)\<rbrakk> 
   \<Longrightarrow> P"
  by(auto simp add: maximal_sets_def)

lemma maximal_sets_subset: "maximal_sets \<X> \<subseteq> \<X>"
  by(auto simp add: maximal_sets_def)

lemma disjoint_maximal_sets_insert:
  assumes "maxes \<subseteq> maximal_sets \<X>" "maxes \<noteq> {}" 
          "\<And> X Y. \<lbrakk>X \<in> maxes; Y \<in> maxes\<rbrakk> \<Longrightarrow> X \<inter> Y = {}"
  shows   "maximal_sets (insert (\<Union> maxes) \<X>) = maximal_sets \<X> - maxes \<union> {\<Union> maxes}"
  using assms
  by(force simp add: maximal_sets_def)

lemma finite_there_is_maximal_set:
  "\<lbrakk>finite \<X>; X \<in> \<X>\<rbrakk> \<Longrightarrow> \<exists> M \<in> maximal_sets \<X>. X \<subseteq> M"
  by (auto dest!: finite_has_maximal2 simp add: maximal_sets_def)

lemma finite_maximal_set:
  "\<lbrakk>finite (\<Union> \<X>); X \<in> maximal_sets \<X>\<rbrakk> \<Longrightarrow> finite X"
  by(auto elim!: in_maximal_setsE intro: rev_finite_subset)

lemma split_with_maximal_sets:
  "finite \<X> \<Longrightarrow> \<X> = \<Union> {{X | X. X \<in> \<X> \<and> X \<subseteq> M} | M. M \<in> maximal_sets \<X>}" 
proof(rule, goal_cases)
  case 1
  then show ?case 
    by (auto dest!: finite_there_is_maximal_set)
next
  case 2
  then show ?case 
    by auto
qed

lemma union_split_with_maximal_sets:
  "finite \<X> \<Longrightarrow> \<Union> \<X> = \<Union> (maximal_sets \<X>)" 
proof(rule, goal_cases)
  case 1
  then show ?case 
    by (auto dest!: finite_there_is_maximal_set)
next
  case 2
  then show ?case 
    by (simp add: Sup_subset_mono maximal_sets_subset)
qed
 
lemma laminar_maximal_sets_disjoint:
 "\<lbrakk>laminar U \<X>; X \<in> maximal_sets \<X>; Y \<in> maximal_sets \<X>; X \<noteq> Y\<rbrakk> \<Longrightarrow> X \<inter> Y = {}"
  by(auto elim!: laminarE simp add: maximal_sets_def) fast+

lemma laminar_maximal_sets_eq_if_not_disjoint:
 "\<lbrakk>laminar U \<X>; X \<in> maximal_sets \<X>; Y \<in> maximal_sets \<X>; X \<inter> Y \<noteq> {}\<rbrakk> \<Longrightarrow> X  = Y"
  by(auto elim!: laminarE simp add: maximal_sets_def) fast+

lemma maximal_disjoint_subsets_disjoint:
  assumes  "M \<in> maximal_sets \<X>"  "M' \<in> maximal_sets \<X>" "M \<inter> M' = {}" "{} \<notin> \<X>"
  shows "{X |X. X \<in> \<X> \<and> X \<subseteq> M} \<inter> {X |X. X \<in> \<X> \<and> X \<subseteq> M'} = {}"
  using assms
  by (auto simp add: maximal_sets_def) (metis le_inf_iff subset_empty)

lemma laminar_maximal_sets_nempty:
 "\<lbrakk>laminar U \<X>; X \<in> maximal_sets \<X>\<rbrakk> \<Longrightarrow> X \<noteq> {}"
  by(auto elim!: laminarE simp add: maximal_sets_def)

lemma laminar_union_maximal_sets_not_in:
 "\<lbrakk>laminar U \<X>; X \<in> maximal_sets \<X>; Y \<in> maximal_sets \<X>; X \<noteq> Y\<rbrakk> \<Longrightarrow> X \<union> Y \<notin> \<X>"
  by(auto elim!: laminarE simp add: maximal_sets_def)

lemma insertE_strict:
  "\<lbrakk>y \<in> insert x X; y \<in> X \<Longrightarrow> P; \<lbrakk>y = x;y \<notin> X\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by blast

lemma laminar_extension_with_maximal_sets:
  assumes "laminar U \<X>" "\<Y> \<subseteq> maximal_sets \<X>" "\<Y> \<noteq> {}"
  shows "laminar U (insert (\<Union> \<Y>) \<X>)"
proof(cases "(\<Union> \<Y>) \<in> \<X>")
  case True
  hence "insert (\<Union> \<Y>) \<X> = \<X>" by blast
  then show ?thesis 
    using assms(1) by simp 
next
  case False
  show ?thesis 
  proof(rule laminarI, goal_cases)
    case (1 X Y)
    then show ?case 
  proof(elim insertE_strict, goal_cases)
    case 1
    then show ?case
      using assms(1) by(auto elim!: laminarE)
  next
    case 2
    have "\<lbrakk>X \<in> \<X>; x \<in> X; \<forall>xa\<in>\<Y>. x \<notin> xa; xa \<in> Xa; Xa \<in> \<Y>; xa \<notin> X; xb \<in> X; xb \<in> Xaa; Xaa \<in> \<Y>\<rbrakk>
          \<Longrightarrow> False"
      for x xa Xa xb Xaa
       proof(goal_cases)
      case 1
      then show ?case 
      proof(cases "Xa = Xaa", goal_cases)
        case 1
        then show ?case 
          using  assms(1,2)  maximal_sets_subset[of \<X>] 
          by(auto elim!: laminarE simp add: disjoint_iff dest!: subsetD)       
      next
        case 2
        hence maximals:"Xa \<in> maximal_sets \<X>" "Xaa \<in> maximal_sets \<X>"
          using assms(2) by auto
        hence "X \<subseteq> Xaa \<or> Xaa \<subseteq> X \<or> X \<inter> Xaa = {}" 
          using "2"(1,5) assms(1)
          by(auto elim!: in_maximal_setsE laminarE)
        moreover have "Xaa \<in> \<X>" 
          using in_maximal_setsE maximals(2) by blast
        moreover have "\<not> Xaa \<subset> X"
           using "2"(1)  maximals(2)
           by(auto elim!: in_maximal_setsE)
        ultimately show ?case 
          using "2"(2-9) by auto  
      qed
    qed
    then show ?case 
      using 2 by blast
  next
    case 3
    note 2 = this
     have "\<lbrakk>Y \<in> \<X>; x \<in> Y; \<forall>xa\<in>\<Y>. x \<notin> xa; xa \<in> Xa; Xa \<in> \<Y>; xa \<notin> Y; xb \<in> Y; xb \<in> Xaa; Xaa \<in> \<Y>\<rbrakk>
          \<Longrightarrow> False"
      for x xa Xa xb Xaa
       proof(goal_cases)
      case 1
      then show ?case 
      proof(cases "Xa = Xaa", goal_cases)
        case 1
        then show ?case 
          using  assms(1,2)  maximal_sets_subset[of \<X>] 
          by(auto elim!: laminarE simp add: disjoint_iff dest!: subsetD)       
      next
        case 2
        hence maximals:"Xa \<in> maximal_sets \<X>" "Xaa \<in> maximal_sets \<X>"
          using assms(2) by auto
        hence "Y \<subseteq> Xaa \<or> Xaa \<subseteq> Y \<or> Y \<inter> Xaa = {}" 
          using "2"(1,5) assms(1)
          by(auto elim!: in_maximal_setsE laminarE)
        moreover have "Xaa \<in> \<X>" 
          using in_maximal_setsE maximals(2) by blast
        moreover have "\<not> Xaa \<subset> Y"
           using "2"(1)  maximals(2)
           by(auto elim!: in_maximal_setsE)
        ultimately show ?case 
          using "2"(2-9) by auto  
      qed
    qed
    then show ?case 
      using 2 by blast
  next
    case 4
    then show ?case 
      by simp
  qed
  next
    case (2 X)
    then show ?case 
      using assms(1-3) by (force elim!: laminarE  in_maximal_setsE)
  qed
qed

lemma laminar_family_number_of_sets:
  assumes "n = card U" "finite U" "laminar U \<X>"
  shows "card \<X> \<le> 2 * n - 1"
  using assms
proof(induction n arbitrary: \<X> U)
  case 0
  then show ?case 
    unfolding laminar_def by simp
next
  case (Suc n)
  note IH = this
  show ?case 
  proof(cases n)
    case 0
    then obtain x where x_prop:"U = {x}" 
      using Suc.prems(1) card_1_singletonE by auto
    hence "\<X> = {{x}} \<or> \<X> = {}"
    proof(cases "\<X> = {}")
      case False
      then obtain X where "X \<in> \<X>" by auto
      hence "X = {x}"
        using Suc(4) x_prop unfolding laminar_def by auto
      moreover have "Y \<in> \<X> \<Longrightarrow> Y = {x}" for Y
        using Suc(4) x_prop unfolding laminar_def by auto
      ultimately show ?thesis by auto
    qed simp
    then show ?thesis
      by force
  next
    case (Suc nat)
    have "card \<X> = 0 \<Longrightarrow> card \<X> \<le> 2 * Suc n - 1" by simp
    moreover have "card \<X> = 1 \<Longrightarrow> card \<X> \<le> 2 * Suc n - 1" by simp
    moreover have "card \<X> \<ge> 2 \<Longrightarrow> card \<X> \<le> 2 * Suc n - 1"
    proof(goal_cases)
      case 1
      note cardX = this
      then obtain x V where x_V_prop:"U = insert x V \<and> x \<notin> V"
     using Suc.prems(1) card_Suc_eq[of U n] by auto
    have V_non_empt: "V \<noteq> {}"
      using Suc Suc.prems(1) x_V_prop by fastforce
    define \<Y> where "\<Y> = {X - {x} | X.  X \<in> \<X> \<and> X - {x} \<noteq> {}}"
    have laminar_Y: "laminar V \<Y>"
    proof(rule laminarI, goal_cases)
      case (1 X Y)
      note XY = this
      obtain X' where X'_prop: "X = X' \<or> insert x X = X'" "X' \<in> \<X>"
        using 1 unfolding \<Y>_def by auto
      obtain Y' where Y'_prop: "Y = Y' \<or> insert x Y = Y'" "Y' \<in> \<X>"
        using 1 unfolding \<Y>_def by auto
      have xXY: "x \<notin> X" "x \<notin> Y" 
        using XY unfolding \<Y>_def by auto
      have "\<not> X \<subseteq> Y \<Longrightarrow> \<not> Y \<subseteq> X \<Longrightarrow> \<not>  X \<inter> Y = {} \<Longrightarrow> False"
      proof(goal_cases)
        case 1
        obtain a where aXY: "a \<in> X" "a \<notin> Y" using 1 by auto
        have a1:"a \<noteq> x" 
          using \<open>a \<in> X\<close> xXY(1) by auto
        hence a2:"a \<notin> Y'" 
          using Y'_prop(1) aXY(2) by blast
        have a3: "\<not> X' \<subseteq> Y'"  
          using X'_prop(1) a2 aXY(1) by blast
        obtain b where bXY: "b \<in> Y" "b \<notin> X" using 1 by auto
        have a4:"b \<noteq> x" 
          using bXY(1) xXY(2) by blast
        hence a5:"b \<notin> X'" 
          using X'_prop(1) bXY(2) by auto
        have a6: "\<not> Y' \<subseteq> X'"  
          using Y'_prop(1) a5 bXY(1) by blast
        have "X' \<inter> Y' = {}" 
          using Suc.prems(3) X'_prop(2) Y'_prop(2) a3 a6 unfolding laminar_def by auto
        hence "X \<inter> Y = {}"
          using X'_prop(1) Y'_prop(1) by blast
        thus False using 1(3) by simp
      qed
      thus ?case by auto
    next
      case (2 X)
      note XX = this
      obtain X' where X'_prop: "X = X' \<or> (insert x X = X' \<and> x \<notin> X)" "X' \<in> \<X>"
        using 2 unfolding \<Y>_def by auto
      have "X \<noteq> {}"
        using "2" \<Y>_def by fastforce
      moreover have "X \<subseteq> V"
      proof(cases rule: disjE[OF  X'_prop(1)])
        case 1
        hence "x \<notin> X'"
          using XX \<Y>_def by blast
        then show ?thesis 
          using "1" Suc.prems(3) X'_prop(2) x_V_prop
          unfolding laminar_def 
          by auto
      next
        case 2
        then show ?thesis 
          using  Suc.prems(3) X'_prop(2)   x_V_prop 
          unfolding  laminar_def by auto
      qed
      ultimately show ?case by simp
    qed
    have cardY: "card \<Y> \<le> 2 * n - 1"
      using Suc.prems(1) Suc.prems(2) x_V_prop  
      by (fastforce intro!: IH(1)[OF _ _  laminar_Y])
    have finite_X: "finite \<X>"
      using IH(4)[simplified laminar_def] IH(3) 
      by (simp add: Suc.prems(3) finite_U_finite_family)
    hence finite_Y: "finite \<Y>" unfolding \<Y>_def
      by simp
    have "\<Y> \<subseteq> {X. X \<in> \<X> \<and> x \<notin> X \<and> insert x X \<notin> \<X>}
            \<union> {X. X \<in> \<X> \<and> x \<notin> X \<and> insert x X \<in> \<X>}
            \<union> {X. X \<notin> \<X> \<and> x \<notin> X \<and> insert x X \<in> \<X> \<and> X \<noteq> {}}" 
      unfolding \<Y>_def 
    proof(rule, goal_cases)
      case (1 Y)
      then obtain X where X_pr:"X \<in> \<X> " "X - {x} \<noteq> {}" "Y = X - {x}"
        by auto
      show ?case
      proof(cases "Y \<in> \<X>")
        case True
        then show ?thesis 
          using X_pr by simp
      next
        case False
        hence " insert x Y = X"
          using X_pr(1) X_pr(3) by auto
        moreover have "Y \<noteq> {}" 
          using X_pr(2) X_pr(3) by blast
        ultimately show ?thesis 
          by (simp add: X_pr(1) X_pr(3))
      qed
    qed
    moreover have "{X. X \<in> \<X> \<and> x \<notin> X \<and> insert x X \<notin> \<X>} \<subseteq> \<Y>" 
      unfolding \<Y>_def 
    proof(rule, goal_cases)
      case (1 X)
      hence "X \<in> \<X> \<and> x \<notin> X \<and> insert x X \<notin> \<X>" by simp
      hence "X \<in> \<X> \<and> X - {x} \<noteq> {}" "X = X - {x}"
        using Suc.prems(3) laminar_def
        by (fastforce, simp add: \<open>X \<in> \<X> \<and> x \<notin> X \<and> insert x X \<notin> \<X>\<close>)
      then show ?case 
        by auto
    qed
    moreover have "{X. X \<in> \<X> \<and> x \<notin> X \<and> insert x X \<in> \<X>} \<subseteq> \<Y>" 
      unfolding \<Y>_def
    proof(rule, goal_cases)
      case (1 X)
      hence "X \<in> \<X> \<and> x \<notin> X \<and> insert x X \<in> \<X>" by simp
      moreover hence "insert x X \<in> \<X> \<and> insert x X - {x} \<noteq> {}"
        using Suc.prems(3) laminar_def by fastforce
      ultimately show ?case
        by blast
    qed
    moreover have " {X. X \<notin> \<X> \<and> x \<notin> X \<and> insert x X \<in> \<X> \<and> X \<noteq> {}} \<subseteq> \<Y>" 
      unfolding \<Y>_def 
    proof(rule, goal_cases)
      case (1 X)
      hence " insert x X \<in> \<X> \<and> (insert x X) - {x} \<noteq> {}" 
        by blast
      moreover hence "X = (insert x X) - {x}" 
        using 1 by auto
      ultimately show ?case by force
    qed
    ultimately have Y_same:"\<Y> = {X. X \<in> \<X> \<and> x \<notin> X \<and> insert x X \<notin> \<X>}
            \<union> {X. X \<in> \<X> \<and> x \<notin> X \<and> insert x X \<in> \<X>}
            \<union> {X. X \<notin> \<X> \<and> x \<notin> X \<and> insert x X \<in> \<X> \<and> X \<noteq> {}}" by auto
(*TODO MOVE*)
    have add_cong1: "a = b \<Longrightarrow> c + a = c + b" for a b c by simp
    have add_cong2: "a = b \<Longrightarrow> a +c = b + c" for a b c by simp
    have aa: "finite {X. X \<notin> \<X> \<and> x \<notin> X \<and> insert x X \<in> \<X> \<and> X \<noteq> {}}"
      using \<open>{X. X \<notin> \<X> \<and> x \<notin> X \<and> insert x X \<in> \<X> \<and> X \<noteq> {}} \<subseteq> \<Y>\<close> finite_Y infinite_super by auto
    have bb:"{X \<in> \<X>. x \<in> X \<and> X - {x} \<notin> \<X> \<and> X - {x} \<noteq> {}}
           \<subseteq> insert x ` {X. X \<notin> \<X> \<and> x \<notin> X \<and> insert x X \<in> \<X> \<and> X \<noteq> {}}"
    proof(rule, goal_cases)
      case (1 Y)
      hence "(Y- {x}) \<notin> \<X> \<and> x \<notin> (Y- {x}) \<and> insert x (Y- {x}) \<in> \<X> \<and> (Y- {x}) \<noteq> {}"
        by (simp add: insert_absorb)
      moreover hence "insert x (Y - {x}) = Y" 
        using "1" by blast
      ultimately show ?case by blast
    qed    
    have " card ({X. X \<in> \<X> \<and> x \<notin> X \<and> insert x X \<notin> \<X>}
            \<union> {X. X \<in> \<X> \<and> x \<notin> X \<and> insert x X \<in> \<X>}
            \<union> {X. X \<notin> \<X> \<and> x \<notin> X \<and> insert x X \<in> \<X> \<and> X \<noteq> {}}) =
           card {X. X \<in> \<X> \<and> x \<notin> X \<and> insert x X \<notin> \<X>} +
           card {X. X \<in> \<X> \<and> x \<notin> X \<and> insert x X \<in> \<X>} +
           card {X. X \<notin> \<X> \<and> x \<notin> X \<and> insert x X \<in> \<X> \<and> X \<noteq> {}}"
      apply(subst card_Un_disjnt[OF _ aa], simp add: finite_X, subst disjnt_Un1, rule)
      using finite_X  disjnt_iff
      by (blast, blast, subst card_Un_disjnt) auto
    also have "... = card {X. X \<in> \<X> \<and> x \<notin> X \<and> insert x X \<notin> \<X>} +
           card {X. X \<in> \<X> \<and> x \<notin> X \<and> insert x X \<in> \<X>} +
           card {X. X \<in> \<X> \<and> x \<in> X \<and> X - {x}  \<notin> \<X> \<and> X - {x} \<noteq> {}}"
      using bb 
      by (auto intro!:add_cong1 bij_betw_same_card[where f="insert x"] 
             simp add: bij_betw_def inj_on_def)
    also have "... = card ({X. X \<in> \<X> \<and> x \<notin> X \<and> insert x X \<notin> \<X>}
                           \<union> {X. X \<in> \<X> \<and> x \<notin> X \<and> insert x X \<in> \<X>}
                           \<union> {X. X \<in> \<X> \<and> x \<in> X \<and> X - {x}  \<notin> \<X> \<and> X - {x} \<noteq> {}})"
      apply(subst card_Un_disjnt[OF])
      using finite_X apply(simp, simp)
      apply(fastforce simp add: disjnt_iff , rule add_cong2, subst card_Un_disjnt)
      using finite_X disjnt_iff by auto
    also have "... = card (\<X> - insert {x} {X. X \<in> \<X> \<and> x \<in> X \<and> X - {x}  \<in> \<X> \<and> X - {x} \<noteq> {}})"
    proof(rule cong[of _ card, OF refl], rule, goal_cases)
      case 1
      show ?case 
      proof(rule, goal_cases)
        case (1 Y)
        hence "Y \<in> \<X>" by auto
        moreover have " Y \<notin> insert {x} {X \<in> \<X>. x \<in> X \<and> X - {x} \<in> \<X> \<and> X - {x} \<noteq> {}}"
          using 1 by blast
        ultimately show ?case by simp
      qed
    next
      case 2
      show ?case 
      proof(rule, goal_cases)
        case (1 Y)
        hence Y_prop: "Y \<in> \<X>"  "Y \<noteq> {x}" "Y \<notin> {X \<in> \<X>. x \<in> X \<and> X - {x} \<in> \<X> \<and> X - {x} \<noteq> {}}"
          by auto
        show ?case
        proof(cases "x \<notin> Y ")
          case True
          then show ?thesis 
            using Y_prop by simp
        next
          case False
          hence xY:"x \<in> Y" by simp
          have "x \<in> Y \<and> Y - {x} \<notin> \<X> \<and> Y - {x} \<noteq> {}"
            using False Y_prop(1) Y_prop(2) Y_prop(3) by blast
          then show ?thesis 
            using Y_prop by simp
        qed
      qed
    qed
    also have "\<dots> \<ge> card \<X> - 2"
    proof(rule order.trans[OF _ diff_card_le_card_Diff], rule diff_le_mono2,
          subst card.insert_remove, goal_cases)
      case 2
      show ?case 
      proof(rule ccontr, goal_cases)
        case 1
        then obtain X Y where X_prop: "X \<in> \<X>" "x \<in> X" "X - {x} \<in> \<X>" "\<not> X \<subseteq> {x}"
                        and   Y_prop: "Y \<in> \<X>" "x \<in> Y" "Y - {x} \<in> \<X>" "\<not> Y \<subseteq> {x}" 
                        and  X_neq_Y: "X \<noteq> Y" 
          by simp (metis (mono_tags, lifting) card.infinite card_le_Suc0_iff_eq le_SucI le_zero_eq mem_Collect_eq)
        hence X_Y_subs:"X \<subseteq> Y \<or> Y \<subseteq> X" using IH(4)[simplified laminar_def] by auto
        show ?case
        proof(rule disjE[OF X_Y_subs], goal_cases)
          case 1
          note X_subs_Y = this
          have "\<not> X \<subseteq> Y - {x}"
            using X_prop(2) by blast
          moreover have " \<not> Y - {x} \<subseteq> X"
          proof(rule , goal_cases)
            case 1
            hence "Y \<subseteq> insert x X" by auto
            moreover have "insert x X \<subseteq> X" using X_prop by simp
            ultimately show ?case using X_subs_Y X_neq_Y by auto
          qed
          moreover have "X \<inter> (Y - {x}) \<noteq> {}" 
            using X_prop(4) X_subs_Y by auto
          ultimately show ?case 
            using IH(4)[simplified laminar_def] X_prop(1) Y_prop(3) by auto
        next
          case 2
          note Y_subs_X = this
          have "\<not> Y \<subseteq> X - {x}"
            using Y_prop(2) by blast
          moreover have " \<not> X - {x} \<subseteq> Y"
          proof(rule , goal_cases)
            case 1
            hence "X \<subseteq> insert x Y" by auto
            moreover have "insert x Y \<subseteq> Y" using Y_prop by simp
            ultimately show ?case using Y_subs_X X_neq_Y by auto
          qed
          moreover have "Y \<inter> (X - {x}) \<noteq> {}" 
            using Y_prop(4) Y_subs_X by auto
          ultimately show ?case 
            using IH(4)[simplified laminar_def] Y_prop(1) X_prop(3) by auto
        qed
      qed
    qed (auto simp add: finite_X)
    finally have "card \<Y> \<ge> card \<X> - 2" 
      using Y_same by auto
    hence card_Y_card_X_2:"card \<X> \<le> card \<Y> + 2" by simp
    also have "\<dots> \<le>  2 * n - 1 + 2"
      using cardY by simp
    also have "\<dots> = 2*(Suc n) - 1" 
      by (simp add: Suc)
    finally show ?thesis by simp
  qed
  ultimately show ?thesis by force
 qed
qed

lemma laminar_card_and_maximal_sets:
  assumes "finite U" "laminar U \<X>" 
  shows   "card \<X> \<le> 2* card (\<Union> \<X>) - card (maximal_sets \<X>)"
proof-
  have X_split:"\<X> = \<Union> {{X | X. X \<in> \<X> \<and> X \<subseteq> M} | M. M \<in> maximal_sets \<X>}"
    using assms(1,2) finite_U_finite_family 
    by(intro split_with_maximal_sets) auto
  have X_split':"\<Union> \<X> = \<Union> (maximal_sets \<X>)"
    using assms(1,2) finite_U_finite_family 
    by(intro union_split_with_maximal_sets) auto
  have "card \<X> = sum card {{X | X. X \<in> \<X> \<and> X \<subseteq> M} | M. M \<in> maximal_sets \<X>}"
  proof(subst  X_split, rule card_UN_disjoint[where A = id, simplified], goal_cases)
    case 1
    then show ?case 
      using assms(1,2) X_split finite_U_finite_family[of U \<X>]
        finite_UnionD[of "{{uuba \<in> \<X>. uuba \<subseteq> uub} |uub. uub \<in> maximal_sets \<X>}"]
      by simp
  next
    case 2
    then show ?case 
      using assms(1,2) finite_U_finite_family by fastforce
  next
    case 3
    then show ?case
    proof(rule, rule,rule, rule, rule, goal_cases)
      case (1 XX YY X)
      then obtain M M' where MM': "M \<in> maximal_sets \<X>" "XX = {X |X. X \<in> \<X> \<and> X \<subseteq> M}"
          "M' \<in> maximal_sets \<X>" "YY = {X |X. X \<in> \<X> \<and> X \<subseteq> M'}"
        by auto
      hence X_props: "X \<in> \<X>" "X \<subseteq> M"  "X \<subseteq> M'"
        using 1 by auto
      then show ?case 
        using 1(3,4) MM' laminar_maximal_sets_disjoint[OF assms(2) MM'(1,3)]
              empty_nin_laminar[OF assms(2)] subset_empty[of X] 
        by blast
    next
      case (2 i j)
      then show ?case
        by simp
    qed
  qed
  also have "... = sum (\<lambda> M. card {X |X. X \<in> \<X> \<and> X \<subseteq> M}) (maximal_sets \<X>)"
  proof(subst comm_monoid_add_class.sum.reindex[of
            "\<lambda> M. {X |X. X \<in> \<X> \<and> X \<subseteq> M}"_ card, simplified comp_def, symmetric], goal_cases)
    case 1
    then show ?case
      by(auto intro!: inj_onI elim!: in_maximal_setsE)
  next
    case 2
    then show ?case  
      by(auto intro!: arg_cong[of _ _ "sum _"])
  qed
  also have "... \<le> sum (\<lambda> X. 2* card X - 1) (maximal_sets \<X>)"
  proof(rule ordered_comm_monoid_add_class.sum_mono, goal_cases)
    case (1 M)
    then show ?case 
      using assms(1,2)
      by(intro laminar_family_number_of_sets[OF refl])
        (auto intro: finite_maximal_set[OF laminar_Union_finite]
             intro!: laminarI
               elim: laminarE) 
  qed
  also have "... =  2* sum card (maximal_sets \<X>) - card (maximal_sets \<X>)"
  proof(subst sum_subtractf_nat, goal_cases)
    case (1 x)
    then show ?case
      using assms(1,2)
      by (auto simp add: card_geq_1_iff finite_maximal_set[OF laminar_Union_finite] 
                         laminar_maximal_sets_nempty)
  next
    case 2
    then show ?case 
      by(auto intro!: arg_cong2[where f = "(-)"] simp add: semiring_0_class.sum_distrib_left)
  qed
  also have "... = 2 * (card (\<Union> \<X>)) - card (maximal_sets \<X>)"
  proof(rule arg_cong2[where f = "(-)", OF _ refl], goal_cases)
    case 1
    have "sum card (maximal_sets \<X>) = card (\<Union> \<X>)"
    proof(subst X_split', subst card_UN_disjoint[where A = id, simplified], goal_cases)
      case 1
      then show ?case 
        by(auto intro!: finite_UnionD laminar_Union_finite[OF assms(1,2)] simp add: X_split'[symmetric])
    next
      case 2
      then show ?case 
        using assms(1,2) 
        by(auto intro: finite_maximal_set[OF laminar_Union_finite])
    next
      case 3
      then show ?case
        using assms(2) laminar_maximal_sets_disjoint by fastforce
    next
      case 4
      then show ?case by simp
    qed
    then show ?case 
      by simp
  qed
  finally show ?thesis 
    by simp
qed

lemma laminar_card_and_maximal_sets_card_universe:
  assumes "finite U" "laminar U \<X>" 
  shows   "card \<X> \<le> 2* card U - card (maximal_sets \<X>)"
proof-
  note laminar_card_and_maximal_sets[OF assms]
  moreover have "2 * card (\<Union> \<X>) - card (maximal_sets \<X>) \<le> 2 * card U - card (maximal_sets \<X>)"
    using assms(1,2) by(auto elim!: laminarE intro!: diff_le_mono card_mono)+
  ultimately show ?thesis
    by simp
qed

lemma two_maxes_laminar_card_not_max:
  assumes "finite U" "laminar U \<X>" "X \<in> maximal_sets \<X>" "Y \<in> maximal_sets \<X>" "X \<noteq> Y"
  shows   "card \<X> \<le> 2* (card U - 1)"
proof(rule ccontr, goal_cases)
  case 1
  hence "card \<X> = 2 * card U - 1"
    using laminar_family_number_of_sets[OF refl assms(1,2)] by simp
  moreover have "card (insert (X \<union> Y) \<X>) = card \<X> + 1"
    using laminar_union_maximal_sets_not_in assms finite_U_finite_family[OF assms(1)]
    by(subst card_insert_disjoint) auto
  moreover have "laminar U (insert (X \<union> Y) \<X>)"
    using assms(3,4)
    by(auto intro!: laminar_extension_with_maximal_sets[OF assms(2), of "{X, Y}", simplified])
  moreover hence  "card (insert (X \<union> Y) \<X>) \<le> 2 * card U - 1" 
    using laminar_family_number_of_sets[OF refl assms(1)] by simp
  ultimately show ?case 
    by simp
qed

definition "laminar_singleton U \<X> = 
  (laminar U \<X> \<and> (\<forall> u \<in> U. {u} \<in> \<X>))"

lemma 
  laminar_singletonI: "\<lbrakk>laminar U \<X>; \<And>u. u \<in> U \<Longrightarrow> {u} \<in> \<X>\<rbrakk> \<Longrightarrow> laminar_singleton U \<X>" and
  laminar_singletonE:  "\<lbrakk>laminar_singleton U \<X>; \<lbrakk>laminar U \<X>; \<And>u. u \<in> U \<Longrightarrow> {u} \<in> \<X>\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" and
  laminar_singletonD: "laminar_singleton U \<X> \<Longrightarrow> laminar U \<X>" and
   "\<lbrakk>laminar_singleton U \<X>; u \<in> U\<rbrakk> \<Longrightarrow> {u} \<in> \<X>"
  unfolding laminar_singleton_def by auto

definition "composed_family \<X> = (\<forall> X \<in> \<X> - {{}}. (\<nexists> x. X = {x}) \<longrightarrow> (\<exists> \<Y>. \<Y> \<subseteq> \<X> - {X} \<and> \<Union> \<Y> = X))"

lemma composed_familyI [intro]: 
  "(\<And>X. \<lbrakk>X \<in> \<X>; X \<noteq> {}; \<nexists>x. X = {x}\<rbrakk> \<Longrightarrow> \<exists>\<Y>. \<Y> \<subseteq> \<X> - {X} \<and> \<Union>\<Y> = X) \<Longrightarrow> composed_family \<X>"
  and composed_familyD [dest]: 
  "\<lbrakk>composed_family \<X>; X \<in> \<X>; X \<noteq> {}; \<nexists>x. X = {x}\<rbrakk> \<Longrightarrow> \<exists>\<Y>. \<Y> \<subseteq> \<X> - {X} \<and> \<Union>\<Y> = X"
  and composed_familyE [elim]: 
  "\<lbrakk>composed_family \<X>; (\<And> X. \<lbrakk>X \<in> \<X>; X \<noteq> {}; \<nexists>x. X = {x}\<rbrakk> \<Longrightarrow> \<exists>\<Y>. \<Y> \<subseteq> \<X> - {X} \<and> \<Union>\<Y> = X) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  unfolding composed_family_def 
  by auto

lemma composed_family_contract_maximals:
  assumes "composed_family \<X>" "\<Y>\<subseteq> maximal_sets \<X>" "\<Y> \<noteq> {}"
  shows "composed_family (\<X> \<union> {\<Union> \<Y>})"
proof(cases "\<exists> Y X. \<Y> \<supseteq> {X, Y} \<and> X\<noteq>Y")
  case True
  show ?thesis
proof(rule composed_familyI, elim UnE, goal_cases)
  case (1 X)
  then obtain \<Y>' where "\<Y>'\<subseteq>\<X>- {X}" "\<Union> \<Y>' = X"
    using assms(1) by(auto dest!: composed_familyD)
  then show ?case 
    by blast
next
  case (2 X)
  moreover have "\<Y> \<noteq> {\<Union> \<Y>}"
    using True by auto
  moreover have "\<Y> \<subseteq> \<X>"
    using assms(2) maximal_sets_subset by auto
  moreover have "\<Union> \<Y> \<notin> \<X>" 
    using assms(2) True by (auto elim: in_maximal_setsE[OF set_mp])
  ultimately show ?case
   using assms(2) maximal_sets_subset
   by(auto intro!: exI[of _ \<Y>])
qed
next
  case False
  note false = this
  show ?thesis
  proof(cases "\<Y> = {}")
    case True
    then show ?thesis 
      using assms(3) by simp
  next
    case False
    then obtain X where "\<Y> = {X}"
      using false by auto
    moreover hence "X \<in> \<X>" 
      using assms(2) in_maximal_setsE by auto
    ultimately have "\<X> \<union> {\<Union> \<Y>} = \<X>"
      by auto
    then show ?thesis 
      by (simp add: assms(1))
  qed
qed

lemma composed_family_contract_more_sets:
  assumes "composed_family \<X>" "\<Union> \<Y>\<subseteq> \<X>" 
        shows "composed_family (\<X> \<union> {\<Union> Y | Y. Y \<in> \<Y>})"
proof(rule composed_familyI, goal_cases)
  case (1 X)
  then show ?case
  proof(elim UnE, goal_cases)
    case 1
    obtain Y where "Y\<subseteq>\<X> - {X}" "\<Union> Y = X"
      using composed_familyD[OF assms(1) 1(3,1,2)] by auto
    then show ?case 
      by blast
  next
    case 2
    then obtain Y where "Y \<in> \<Y>" "X = \<Union> Y"
      by auto
    moreover then obtain \<Y>' where "\<Y>'\<subseteq>\<X> - {X}" "\<Union> \<Y>' = X"
      using "2"(1,2) assms(2) composed_familyD[OF assms(1) _ 2(1,2)] 
      by(cases "X \<in> \<X>") auto
    ultimately show ?case
      by blast
  qed
qed

lemma composed_family_expand_maximal:
  assumes "composed_family \<X>" "X \<in> maximal_sets \<X>"
  shows "composed_family (\<X> - {X})"
proof(rule composed_familyI, goal_cases)
  case (1 Y)
  obtain \<Y> where "\<Y>\<subseteq>\<X> - {Y}" "\<Union> \<Y> = Y" 
    using  "1"(1,2,3) assms(1) by (auto dest!: composed_familyD)
  moreover hence "\<Y> \<subseteq> \<X> - {X} - {Y}" 
    using 1 assms(2) by (auto elim!: in_maximal_setsE)
  ultimately show ?case 
    by(auto intro!: exI[of _ "\<Y>"]) 
qed

lemma composed_family_expand_maximal_same_universe:
  assumes "composed_family \<X>" "X \<in> maximal_sets \<X>" "\<nexists> x. X = {x}"
  shows "\<Union> (\<X> - {X}) = \<Union> \<X>"
proof(rule, all \<open>rule\<close>, goal_cases)
  case (2 x)
  then obtain Y where Y: "x \<in> Y" "Y \<in> \<X>"
    by auto
  show ?case 
  proof(cases "X = Y")
    case True
    then show ?thesis 
      using assms Y
      by(fastforce elim!: composed_familyE in_maximal_setsE)
  next
    case False
    then show ?thesis 
      using Y by auto
  qed
qed auto

lemma composed_family_expand_some_maximals:
  assumes "composed_family \<X>" "\<M> \<subseteq> maximal_sets \<X>"
  shows "composed_family (\<X> - \<M>)"
proof(rule composed_familyI, goal_cases)
  case (1 Y)
  obtain \<Y> where "\<Y>\<subseteq>\<X> - {Y}" "\<Union> \<Y> = Y" 
    using  "1"(1,2,3) assms(1) by (auto dest!: composed_familyD)
  moreover hence "\<Y> \<subseteq> \<X> - \<M> - {Y}" 
    using 1 assms(2) by (auto elim!: in_maximal_setsE[OF set_mp])
  ultimately show ?case 
    by(auto intro!: exI[of _ "\<Y>"]) 
qed

lemma laminar_extension_with_set_of_maximal_sets:
  assumes "laminar U \<X>" "\<Union> \<Y> \<subseteq> maximal_sets \<X>" 
          "\<And> X Y. \<lbrakk>X\<in>\<Y>;Y\<in>\<Y>; X \<noteq> Y\<rbrakk> \<Longrightarrow> X \<inter> Y = {}"
          "\<And> X. X\<in>\<Y> \<Longrightarrow> X \<noteq> {}"
    shows "laminar U ( {\<Union> Y| Y. Y \<in> \<Y>} \<union> \<X>)"
proof(rule laminarI, all \<open>elim UnE\<close>, goal_cases)
  case (1 X Y)
  note one = this
  have "X \<inter> Y = {}" if "X \<noteq> Y"
  proof(rule ccontr, goal_cases)
    case 1
    then obtain x where x: "x \<in> X" "x \<in> Y" by auto
    then obtain XX YY where XX_YY:"XX \<in> \<Y>" "X = \<Union> XX" "YY \<in> \<Y>" "Y = \<Union> YY"
      using one(1,2) by blast
    then obtain XXX YYY where XXX_YYY: "x \<in> XXX" "x \<in> YYY" "XXX \<in> XX" "YYY \<in> YY"
      using x(1,2) by blast
    hence "XXX \<in> maximal_sets \<X>" "YYY \<in> maximal_sets \<X>" 
      using XX_YY assms(2)  by auto
    hence "XXX = YYY"
      using XXX_YYY(1,2) assms(1) 
      by(auto dest: laminar_maximal_sets_disjoint)
    hence "XX \<inter> YY \<noteq> {}"
      using XXX_YYY(3,4) by blast
    hence "XX = YY"
      using XX_YY(1,3) assms(3) by blast
    then show ?case 
      using XX_YY(2,4) that by auto
  qed
  then show ?case
    by auto
next
  case (2 X Y)
  note two = this
  have "X \<inter> Y \<noteq> {} \<Longrightarrow> Y \<subseteq> X"
  proof(goal_cases)
    case 1
   then obtain x where x: "x \<in> X" "x \<in> Y" by auto
    then obtain XX where XX:"XX \<in> \<Y>" "X = \<Union> XX"
      using two by blast
    then obtain XXX where XXX: "x \<in> XXX"  "XXX \<in> XX"
      using x(1,2) by blast
    hence XXX_maximal:"XXX \<in> maximal_sets \<X>"
      using XX assms(2)  by auto
    hence "Y \<subseteq> XXX \<or> XXX \<subseteq> Y"
      using XXX(1) assms(1) two(2) x(2)
      by(auto elim!: in_maximal_setsE laminarE)
    hence "Y \<subseteq> XXX"
      using XXX_maximal in_maximal_setsE two(2) by auto
    then show ?case
      using XX(2) XXX(2) by auto
  qed
  then show ?case 
    by auto
next
  case (3 X Y)
  note three = this
  have "X \<inter> Y \<noteq> {} \<Longrightarrow> X \<subseteq> Y"
  proof(goal_cases)
    case 1
   then obtain x where x: "x \<in> X" "x \<in> Y" by auto
    then obtain YY where YY:"YY \<in> \<Y>" "Y = \<Union> YY"
      using three by blast
    then obtain YYY where YYY: "x \<in> YYY"  "YYY \<in> YY"
      using x(1,2) by blast
    hence YYY_maximal:"YYY \<in> maximal_sets \<X>"
      using YY assms(2)  by auto
    hence "X \<subseteq> YYY \<or> YYY \<subseteq> X"
      using YYY(1) assms(1) three(1) x
      by(auto elim!: in_maximal_setsE laminarE)
    hence "X \<subseteq> YYY"
      using YYY_maximal in_maximal_setsE three(1) by auto
    then show ?case
      using YY(2) YYY(2) by auto
  qed
  then show ?case 
    by auto
next
  case (4 X Y)
  then show ?case
    using assms(1) 
    by(auto elim!: laminarE)
next
  case (5 X)
  then obtain Y where Y: "X = \<Union> Y" "Y \<in> \<Y>"
    by auto
  moreover then obtain YY where "YY \<in> Y"
    using assms(4) by auto
  moreover hence "YY \<noteq> {}"
    using assms(1,2) calculation(2) laminar_maximal_sets_nempty by fastforce
  ultimately have "X \<noteq> {}"
    by blast
  moreover have "YY \<in> Y \<Longrightarrow> YY \<in> \<X>" for YY
    using Y(2) assms(2) maximal_sets_subset[of \<X>] by auto
  moreover hence "YY \<in> Y \<Longrightarrow> YY \<subseteq> U" for YY
    using assms(1) by(force elim!: laminarE)
  ultimately show ?case
    using Y(1) by auto
next
  case (6 X)
  then show ?case
    using assms(1) 
    by(auto elim!: laminarE)
qed

definition "immediate_subsets \<X> X = {Y| Y. Y \<in> \<X> \<and> Y \<subset> X \<and> (\<nexists> Y'. Y'\<in> \<X> \<and> Y' \<subset> X \<and> Y'  \<supset> Y)}"

lemma in_immediate_subsetsD:
  "Y \<in> immediate_subsets \<X> X \<Longrightarrow> Y \<in> \<X>"
  "Y \<in> immediate_subsets \<X> X \<Longrightarrow> Y \<subset> X "
  "Y \<in> immediate_subsets \<X> X \<Longrightarrow>\<nexists> Y'. Y'\<in> \<X> \<and> Y' \<subset> X \<and> Y'  \<supset> Y"
  by(auto simp add: immediate_subsets_def)

lemma not_in_immediate_subsetsE:
  "\<lbrakk>Y \<notin> immediate_subsets \<X> X;
    Y \<notin> \<X> \<Longrightarrow> P;
    \<not> Y \<subset> X \<Longrightarrow> P; 
    (\<And> Y'. \<lbrakk> Y'\<in> \<X>; Y' \<subset> X; Y' \<supset> Y\<rbrakk> \<Longrightarrow> P)\<rbrakk>
    \<Longrightarrow> P"
  by(auto simp add: immediate_subsets_def)

lemma in_immediate_subsetsE:
  "\<lbrakk>Y \<in> immediate_subsets \<X> X;
     \<lbrakk>Y \<in> \<X>; Y \<subset> X;\<nexists> Y'. Y'\<in> \<X> \<and> Y' \<subset> X \<and> Y'  \<supset> Y\<rbrakk> \<Longrightarrow> P\<rbrakk> 
    \<Longrightarrow> P"
  by(auto simp add: immediate_subsets_def)

lemma immediate_subsets_same_add_more:
  assumes "\<And> X'. X' \<in> \<Y> \<Longrightarrow> \<not> X \<supset> X'"
  shows "immediate_subsets (\<X> \<union> \<Y>) X = immediate_subsets \<X> X"
  using assms
  by(auto simp add: immediate_subsets_def)

lemma immediate_subsets_same_add_more':
  assumes "\<And> X'. X' \<in> \<Y> \<Longrightarrow> \<not> X \<supset> X'"
  shows "immediate_subsets (\<Y> \<union> \<X>) X = immediate_subsets \<X> X"
  using assms 
  by(auto simp add: immediate_subsets_def)

lemma immediate_subsets_remove:
  assumes "\<And> X'. X' \<in> \<Y> \<Longrightarrow> \<not> X \<supset> X'"
  shows "immediate_subsets (\<X> - \<Y>) X = immediate_subsets \<X> X"
  using assms
  by(auto simp add: immediate_subsets_def)

lemma immediate_subsets_subset:
  "Y \<in> immediate_subsets \<X> X  \<Longrightarrow> Y \<subset> X"
  "Y \<in> immediate_subsets \<X> X  \<Longrightarrow> Y \<subseteq> X"
  by(auto simp add: immediate_subsets_def)

lemma immediate_subsets_laminar_disjoint:
  assumes "laminar U \<X>"
  "Y1 \<in> immediate_subsets \<X> X"
 "Y2 \<in> immediate_subsets \<X> X"
shows "Y1 \<noteq> Y2 \<longleftrightarrow> Y1 \<inter> Y2 = {}"
proof(rule, goal_cases)
  case 1
  note one = this
  show ?case
  proof(rule ccontr, goal_cases)
    case 1
    hence "Y1 \<subseteq> Y2 \<or> Y2 \<subseteq> Y1"
      using assms(1,2,3)
      by(auto elim!: laminarE simp add:  immediate_subsets_def)
    moreover have "Y1 \<subset> Y2 \<or> Y2 \<subset> Y1 \<Longrightarrow> False" 
      using  assms(2,3) by(auto simp add: immediate_subsets_def)
    ultimately have "Y1 = Y2"
      by auto
    thus False
      using one
      by simp
  qed
next
  case 2
  then show ?case 
    using assms(1,2) empty_nin_laminar 
    by(fastforce simp add: immediate_subsets_def)
qed

lemma laminar_inter_maximal_set:
  assumes "laminar U \<X>" "X \<in> maximal_sets \<X>" "Y \<inter> X \<noteq> {}" "Y \<in> \<X>"
  shows "Y \<subseteq> X"
  using assms psubsetI[of X Y] 
  by(auto elim!: laminarE simp add: maximal_sets_def)

lemma immediate_subsets_remove_lowers:
  assumes "\<And> Y. \<lbrakk>Y \<in> \<Y>; Y \<subset> X; Y \<notin> \<X>\<rbrakk> \<Longrightarrow> \<exists> X' \<in> \<X>. X' \<supseteq> Y \<and> X' \<subset> X" "\<X> \<subseteq> \<Y>"
  shows "immediate_subsets \<Y> X = immediate_subsets \<X> X"
proof(rule, all \<open>rule\<close>, goal_cases)
  case (1 Y)
  hence Y: "Y \<in> \<Y>" "Y \<subset> X" "\<nexists>Y'. Y' \<in>  \<Y> \<and> Y' \<subset> X \<and> Y \<subset> Y'"
    by(auto simp add: immediate_subsets_def)
  moreover have "Y \<in> \<X>"
  proof(rule ccontr, goal_cases)
    case 1
    obtain X' where "X' \<in> \<X>" "X' \<supseteq> Y" " X' \<subset> X"
      using assms(1) Y(1,2) by fast
    then show ?case 
      using "1" Y(3) assms(2) by auto
  qed
  moreover have "\<nexists>Y'. Y' \<in> \<X> \<and> Y' \<subset> X \<and> Y \<subset> Y'"
    using Y(3) assms(2) by auto
  ultimately show ?case
   by(simp add: immediate_subsets_def)
next
  case (2 X')
  hence X': "X' \<in> \<X>" "X' \<subset> X" "\<nexists>Y'. Y' \<in> \<X> \<and> Y' \<subset> X \<and> X' \<subset> Y'"
    by(auto simp add: immediate_subsets_def)
  moreover have "X' \<in> \<Y>" 
    using X'(1) assms(2) by auto
  moreover have "\<nexists>Y'. Y' \<in> \<Y> \<and> Y' \<subset> X \<and> X' \<subset> Y'"
  proof(rule ccontr, goal_cases)
    case 1
    then obtain Y' where "Y' \<in> \<Y>" "Y' \<subset> X" "X' \<subset> Y'"
      by auto
    thus ?case
       using X'(3) assms(1)[of Y'] by blast
   qed
  ultimately show ?case 
    by(simp add: immediate_subsets_def)
qed

lemma immediate_subsets_remove_lowers_2:
  assumes "\<And> Y. \<lbrakk>Y \<in> \<Y>; Y \<subset> X; Y \<notin> \<X>\<rbrakk> \<Longrightarrow> \<exists> X' \<in> immediate_subsets \<X> X. X' \<supseteq> Y" "\<X> \<subseteq> \<Y>"
  shows "immediate_subsets \<Y> X = immediate_subsets \<X> X"
proof(rule, all \<open>rule\<close>, goal_cases)
  case (1 Y)
  hence Y: "Y \<in> \<Y>" "Y \<subset> X" "\<nexists>Y'. Y' \<in>  \<Y> \<and> Y' \<subset> X \<and> Y \<subset> Y'"
    by(auto simp add: immediate_subsets_def)
  moreover have "Y \<in> \<X>"
  proof(rule ccontr, goal_cases)
    case 1
    obtain X' where "X' \<in> immediate_subsets \<X> X" "X' \<supseteq> Y" 
      using assms(1)[OF Y(1,2) 1] by auto
    then show ?case 
      using "1" Y(3) assms(2) 
      by(auto simp add: immediate_subsets_def)
  qed
  moreover have "\<nexists>Y'. Y' \<in> \<X> \<and> Y' \<subset> X \<and> Y \<subset> Y'"
    using Y(3) assms(2) by auto
  ultimately show ?case
   by(simp add: immediate_subsets_def)
next
  case (2 X')
  hence X': "X' \<in> \<X>" "X' \<subset> X" "\<nexists>Y'. Y' \<in> \<X> \<and> Y' \<subset> X \<and> X' \<subset> Y'"
    by(auto simp add: immediate_subsets_def)
  moreover have "X' \<in> \<Y>" 
    using X'(1) assms(2) by auto
  moreover have "\<nexists>Y'. Y' \<in> \<Y> \<and> Y' \<subset> X \<and> X' \<subset> Y'"
  proof(rule ccontr, goal_cases)
    case 1
    then obtain Y' where Y':"Y' \<in> \<Y>" "Y' \<subset> X" "X' \<subset> Y'"
      by auto
    moreover have Y'_not_in_X: "Y' \<notin> \<X>" 
      using X'(3) calculation(2,3) by auto
    ultimately obtain X'' where X'': "X''\<in>immediate_subsets \<X> X" "Y' \<subseteq> X''"
      using assms(1)[of Y'] by auto
    hence "X'' \<in> \<X>" "X'' \<subset> X" "\<nexists>Y'. Y' \<in> \<X> \<and> Y' \<subset> X \<and> X'' \<subset> Y'"
      by (auto simp add: immediate_subsets_def)
    then show False
      using X''(2) X'(3) Y'(3) by blast
  qed
  ultimately show ?case 
    by(simp add: immediate_subsets_def)
qed

lemma immediate_subsets_restrict_to_set:
  "immediate_subsets \<X> X = immediate_subsets {X' | X'. X' \<subset> X \<and> X' \<in> \<X>} X"
  by(auto simp add: immediate_subsets_def)

lemma immediate_subsets_disjoints:
  assumes "\<And> X'. X' \<in> \<X> \<Longrightarrow> X' \<subset> X"
          "\<And> X Y. \<lbrakk>X \<in> \<X>; Y \<in> \<X>\<rbrakk> \<Longrightarrow> X \<inter> Y = {}"
    shows "immediate_subsets \<X> X = \<X>"
  using assms
  by(auto simp add: immediate_subsets_def)

lemma immediate_subsets_are_maximals:
  "immediate_subsets \<X> X = maximal_sets {Y | Y. Y \<in> \<X> \<and> Y \<subset> X}"
  by (auto simp add: immediate_subsets_def maximal_sets_def)

lemma composed_family_Union_of_immediate_subsets:
  assumes "composed_family \<X>" "X \<in> \<X>" "\<nexists> x. X = {x}" "finite \<X>"
  shows "X = \<Union> (immediate_subsets \<X> X)"
  unfolding immediate_subsets_are_maximals
proof(rule, all \<open>rule\<close>, goal_cases)
  case (1 x)
  moreover then obtain X' where "X' \<in> \<X>" "X' \<subset> X" "x \<in> X'"
    using assms(1,2,3) by(auto dest!: composed_familyD)
  moreover then obtain X'' where "X'' \<in> maximal_sets {Y |Y. Y \<in> \<X> \<and> Y \<subset> X}" "X'' \<supseteq> X'"
    using assms(4) finite_there_is_maximal_set[of "{uub \<in> \<X>. uub \<subset> X}" X'] 
    by auto
  ultimately  show ?case 
    by auto
next
  case (2 x)
  then show ?case 
    by (auto elim!: in_maximal_setsE)
qed

lemma remove_maximal_set_from_laminar_family:
  assumes "laminar U \<X>" "X \<in> maximal_sets \<X>"
  shows "maximal_sets (\<X> - {X}) = maximal_sets  \<X> - {X} \<union> immediate_subsets \<X> X"
proof(rule, all \<open>rule\<close>, goal_cases)
  case (1 x)
  then show ?case
   by (auto intro!: in_maximal_setsI elim!: in_maximal_setsE not_in_immediate_subsetsE)
next
  case (2 x)
  then show ?case
    apply(auto elim!: in_immediate_subsetsE in_maximal_setsE not_in_maximal_setsE)
    using assms(1,2) bot.extremum_uniqueI[of x]
        empty_nin_laminar[of U \<X>] subsetD[of _ X] le_infI[of x _ X] laminar_inter_maximal_set[of U \<X> X]
     apply metis
    by (metis Int_greatest assms(1,2) bot.extremum_unique empty_nin_laminar laminar_inter_maximal_set
        order_le_imp_less_or_eq)
qed

lemma same_immediate_subsets_remove:
  assumes "\<not> Y \<subset> X"
  shows "immediate_subsets (\<X> - {Y}) X = immediate_subsets \<X> X"
  using assms
  by(auto simp add: immediate_subsets_def)

end