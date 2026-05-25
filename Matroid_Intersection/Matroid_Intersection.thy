theory Matroid_Intersection
  imports Matroids.Matroid Directed_Set_Graphs.Awalk "HOL-Eisbach.Eisbach" 
         "Directed_Set_Graphs.Pair_Graph_Specs" Alternating_Lists.Alternating_Lists
begin

section \<open>Theory for Matroid Intersection\<close>

text \<open>This file contains theory for matroid intersection, including Edmonds' Rank Criterion,
his Max-Min Equality,
the auxiliary graph for intersection (see Korte&Vygen),
 augmentation lemmas and a characterisation of optimality (Korte&Vygen).\<close>

lemma exists_smallest_witness: 
  assumes "P x" "fx = f x"
  shows "\<exists> y. P y \<and> (\<nexists> z. P z \<and> ((f z)::nat) < f y)"
  using assms(1,2)
proof(induction fx arbitrary: x rule: less_induct)
  case (less fx)
  show ?case 
  proof(cases "\<nexists> z. P z \<and> ((f z)::nat) < f x")
    case True
    then show ?thesis 
      using less(2,3) by blast
  next
    case False
    then obtain y where y_prop: "P y" "f y < fx"
      using less(2,3) by auto
    show ?thesis using less(1)[OF y_prop(2,1) refl] by blast
  qed
qed

lemma exists_greatest_witness: 
  assumes "P x" "n = card {y | y. P y \<and> f y > f x}" 
    "finite {y | y. P y \<and> f y > f x}"
  shows "\<exists> y. P y \<and> (\<nexists> z. P z \<and> ((f z)::nat) > f y)"
  using assms(1,2,3)
proof(induction n arbitrary: x rule: less_induct)
  case (less n)
  show ?case 
  proof(cases "\<nexists> z. P z \<and> ((f z)::nat) > f x")
    case True
    then show ?thesis 
      using less(2,3) by blast
  next
    case False
    then obtain y where y_prop: "P y" "f y > f x"
      by auto
    hence "{z |z. P z \<and> f y < f z} \<subset> {z |z. P z \<and> f x < f z}" by auto
    moreover hence less_card:"card {z |z. P z \<and> f y < f z} < n" 
      using less(3,4)
      by (simp add: psubset_card_mono)
    ultimately show ?thesis 
      using less.prems(3) rev_finite_subset 
      by (intro less(1)[OF less_card y_prop(1) refl] less(4)) auto
  qed
qed

context matroid
begin

lemma finite_number_of_indeps: "finite (Collect indep)"
  using indep_subset_carrier 
  by (auto intro!: finite_subset[of _ "Pow carrier"] simp add: carrier_finite)

definition "the_circuit X = (if indep X then {} else (SOME C. circuit C \<and> C \<subseteq> X))"

lemma the_circuit_non_empty_dependent: "the_circuit X \<noteq> {} \<Longrightarrow> \<not> indep X"
  using the_circuit_def by force

lemma independent_empty_circuit: "indep X \<Longrightarrow> the_circuit X = {}"
  using the_circuit_def by force

lemma the_circuit_X_in_X:
  assumes  "X \<subseteq> Y" "X \<subseteq> carrier"
  shows "the_circuit X \<subseteq> Y" 
proof(cases "indep X")
  case True
  then show ?thesis 
    by (simp add: the_circuit_def)
next
  case False
  then obtain C where "circuit C" "C \<subseteq> X" 
    using assms(2) dep_iff_supset_circuit by auto
  hence "the_circuit X \<subseteq> X"
    by (metis (no_types, lifting) False the_circuit_def verit_sko_ex_indirect)
  then show ?thesis 
    using assms(1) by simp
qed

lemma the_circuit_is_circuit:
  assumes "indep X" "\<not> indep (insert x X)" "insert x X \<subseteq> carrier" 
  shows "circuit (the_circuit (insert x X))" (is ?thesis1)
    and "the_circuit (insert x X) \<subseteq> insert x X" (is ?thesis2)
proof-
  have "(SOME C. circuit C \<and> C \<subseteq> insert x X) = the_circuit (insert x X)"
    by (simp add: assms(2) the_circuit_def)
  moreover obtain C where "circuit C" "C \<subseteq> insert x X"
    using assms  dep_iff_supset_circuit by auto
  moreover then obtain D where D_prop:"D = (SOME C. circuit C \<and> C \<subseteq> insert x X)" "circuit D" "D \<subseteq> insert x X" 
    by (metis (no_types, lifting) someI_ex)
  ultimately show ?thesis1 and ?thesis2 by auto
qed

lemma circuit_is_the_circuit:
  assumes "indep X" "\<not> indep (insert x X)" 
    "circuit C" "C \<subseteq> insert x X" 
  shows  "C = the_circuit (insert x X)" 
proof-
  have "(SOME C. circuit C \<and> C \<subseteq> insert x X) = the_circuit (insert x X)"
    by (simp add: assms(2) the_circuit_def)
  moreover  obtain D where D_prop:"D = (SOME C. circuit C \<and> C \<subseteq> insert x X)" "circuit D" "D \<subseteq> insert x X" 
    by (metis (no_types, lifting) assms(3) assms(4) someI_ex)
  moreover have "x \<in> carrier" 
    using assms(1) calculation(3) calculation(4) circuit_subset_carrier min_dep_imp_supset_circuit by blast
  ultimately show ?thesis
    using assms min_dep_imp_ex1_supset_circuit[of x X] by blast
qed

corollary circuit_is_unique:
  assumes "indep X" "\<not> indep (insert x X)" 
    "circuit C" "C \<subseteq> insert x X"
    "circuit D" "D \<subseteq> insert x X"
  shows "C = D"
  using  circuit_is_the_circuit[OF assms(1,2,3,4)] circuit_is_the_circuit[OF assms(1,2,5,6)]
  by simp

lemma same_cicuit_indep_part_extended: 
  assumes "\<not> indep (insert a X)" "indep Y" "X \<subseteq> Y" "a \<in> carrier"
  shows   "the_circuit (insert a Y) = the_circuit (insert a X)"
  apply(rule sym)
  using  assms  indep_subset
  by(intro circuit_is_the_circuit[OF assms(2)])
    (auto simp add: the_circuit_is_circuit(1) indep_subset_carrier subset_insertI2 the_circuit_X_in_X)

lemma circuit_extensional:
  assumes "indep X"  "y \<in> carrier"
  shows   "the_circuit (insert y X) = {x | x. x \<in> insert y X \<and> \<not> indep (insert y X) \<and> indep (insert y X - {x})}"
proof(cases "indep (insert y X)")
  case True
  then show ?thesis 
    by(simp add: the_circuit_def) 
next
  case False
  hence circuit: "circuit (the_circuit (insert y X))" "the_circuit (insert y X) \<subseteq> insert y X"
    by (simp add: assms(1) assms(2) indep_subset_carrier the_circuit_is_circuit)+
  show ?thesis
  proof(rule, all \<open>rule\<close>, goal_cases)
    case (1 x)   
    hence "x \<in> insert y X" 
      using circuit(2) by auto
    moreover have "indep (insert y X - {x})" 
      using "1"  assms(1) assms(2) circuit(1) circuit(2)
        dep_iff_supset_circuit[of "insert y X  - {x}" ] indep_subset_carrier
        min_dep_imp_ex1_supset_circuit[OF assms(2,1) False]
      by blast
    ultimately show ?case 
      using False by simp
  next
    case (2 x)
    hence 2: "x \<in> insert y X" "\<not> indep (insert y X)" "indep (insert y X - {x})" by auto
    show ?case 
      using  circuit(2)  min_dep_imp_supset_circuit[OF 2(3)  circuit(1), of x] by auto
  qed
qed

lemma single_matroid_augment_general: 
  assumes "indep X"
    "set (map fst xys) \<subseteq> X"
    "set (map snd xys) \<subseteq> carrier - X"
    "s + 1 = length xys"
    "\<And> i. i \<le> s \<Longrightarrow> fst (xys ! i) \<in> the_circuit (insert (snd (xys ! i)) X)"
    "\<And> i j. i \<le> s \<Longrightarrow> j \<le> s \<Longrightarrow> j < i \<Longrightarrow> fst (xys ! j) \<notin> the_circuit (insert (snd (xys ! i)) X)"
    "r \<le> s + 1"
    "XR = X - set (map fst (take r xys)) \<union>  set (map snd (take r xys))"
  shows  "indep XR"
  using assms(7,8)
proof(induction r arbitrary: XR)
  case 0
  then show ?case 
    by(auto simp add: assms(1))
next
  case (Suc r)
  have r_length: "r < length xys"
    using Suc.prems(1) assms(4) by auto
  define XRold where "XRold = X - set (map fst (take r xys)) \<union> set (map snd (take r xys))"
  have indep_XRold:"indep XRold"
    using Suc.IH Suc.prems(1) Suc_leD XRold_def by presburger
  have XR_is:"XR = X -( set (map fst (take r xys)) \<union> {fst (xys ! r)})  \<union> set (map snd (take r xys))  \<union> {snd (xys ! r)}"
    by(auto simp add: Suc(3) take_Suc_conv_app_nth[OF r_length])
  have XRold_Carrier: "XRold \<subseteq> carrier"
    by (simp add: indep_XRold indep_subset_carrier)
  have y_r_incarrier: "snd (xys ! r) \<in> carrier - X" 
    using assms(3) r_length 
    by (metis length_map nth_map nth_mem subsetD)
  show ?case 
  proof(cases "indep (insert (snd (xys ! r)) XRold)")
    case True
    then show ?thesis 
      by(auto intro: indep_subset simp add: XR_is XRold_def)
  next
    case False
    define C where "C = the_circuit (insert (snd (xys ! r)) XRold)"
    hence "circuit C" "C \<subseteq> insert (snd (xys ! r)) XRold"
      using the_circuit_is_circuit[OF indep_XRold False]  XRold_Carrier y_r_incarrier by auto
    have "the_circuit (insert (snd (xys ! r)) X) \<noteq> {}"
      using assms(5)[of r] assms(4) r_length  Suc.prems(1) 
      by auto
    hence not_indep_X_xr:"\<not> indep (insert (snd (xys ! r)) X)"
      by (simp add: the_circuit_non_empty_dependent)
    define D where "D = the_circuit (insert (snd (xys ! r)) X)" 
    have D_prop: "circuit D" "D \<subseteq> (insert (snd (xys ! r)) X)"
      using indep_subset_carrier[OF assms(1)]
        the_circuit_is_circuit[OF assms(1) not_indep_X_xr] y_r_incarrier 
      by (auto simp add:  D_def)
    have ys_up_to_r_in_carrier_without_X:"set (map snd (take r xys)) \<subseteq> carrier - X"
      using assms(3)  set_take_subset[of r xys] take_map[of r snd xys] by auto
    have length_take_r:"length (take r xys) = r" 
      by (simp add: r_length)
    have "D \<subseteq> (insert (snd (xys ! r)) XRold)"
    proof-
      have "x \<in> D \<Longrightarrow> x \<notin> (insert (snd (xys ! r)) XRold) \<Longrightarrow> False" for x
      proof(goal_cases)
        case 1
        hence "x \<in> insert (snd (xys ! r)) X" 
          using D_prop(2) by blast
        hence "x \<in> set (map fst (take r xys))" 
          using 1(2)
          by(auto simp add: XRold_def)
        then obtain j where "x = ((map fst (take r xys)) ! j)"  "j < length (take r xys)" 
          by (metis in_set_conv_nth length_map)
        hence x_prop:"x = fst (xys ! j)" "j < r"
          by auto
        have "fst (xys ! j) \<notin> the_circuit (insert (snd (xys ! r)) X)"
          using assms(6)[OF _ _ x_prop(2)]  Suc.prems(1) x_prop(2) by auto
        then show ?case 
          using "1"(1) D_def x_prop(1) by blast
      qed
      thus ?thesis by blast
    qed
    hence C_is_D:"C = D" 
      using C_def D_prop(1) False indep_XRold circuit_is_the_circuit by fastforce
    have xr_neq_yr: "fst (xys ! r) \<noteq> snd (xys ! r)" 
      using  assms(2) length_map nth_map[OF r_length] nth_mem[OF r_length]  y_r_incarrier by auto
    have new_X_in_carrier: "insert (snd (xys ! r)) XRold - {fst (xys ! r)} \<subseteq> carrier" 
      using XRold_Carrier y_r_incarrier by fastforce
    have x_r_in_C:"fst (xys ! r) \<in> C" 
      using C_is_D D_def assms(4) assms(5) r_length by force
    have "indep ((insert (snd (xys ! r)) XRold) - {fst (xys ! r)})" 
    proof(rule ccontr, goal_cases)
      case 1
      obtain C2 where C2_prop: "circuit C2" "C2 \<subseteq> (insert (snd (xys ! r)) XRold) - {fst (xys ! r)}" 
        using dep_iff_supset_circuit[OF new_X_in_carrier ]  1 by auto
      hence "C2 = C"
        using circuit_is_the_circuit[OF indep_XRold, of "snd (xys ! r)" C2] 
          supset_circuit_imp_dep
        by(auto simp add: C_def)
      moreover have "fst (xys ! r) \<notin> C2"
        using C2_prop(2) by blast
      ultimately show ?case 
        using x_r_in_C by auto
    qed
    moreover have XR_is':"XR = insert (snd (xys ! r)) XRold - {fst (xys ! r)}" 
      using xr_neq_yr assms(3) D_prop(2) x_r_in_C ys_up_to_r_in_carrier_without_X
      by (auto simp add:  C_is_D XR_is XRold_def )
    ultimately show ?thesis by blast
  qed
qed

lemma single_matroid_augment: 
  assumes "indep X"
    "set (map fst xys) \<subseteq> X"
    "set (map snd xys) \<subseteq> carrier - X"
    "s  = length xys"
    "\<And> i. i < s \<Longrightarrow> fst (xys ! i) \<in> the_circuit (insert (snd (xys ! i)) X)"
    "\<And> i j. i < s \<Longrightarrow> j < s \<Longrightarrow> j < i \<Longrightarrow> fst (xys ! j) \<notin> the_circuit (insert (snd (xys ! i)) X)"
    "XR = X - set (map fst xys) \<union>  set (map snd xys)"
  shows  "indep XR"
proof(cases xys)
  case Nil
  then show ?thesis 
    using assms(1,7) by simp
next
  case (Cons a list)
  have length_xys:"(s - 1) + 1= length xys" 
    by (simp add: assms(4) local.Cons)
  moreover have XR_is:"XR = X - set (map fst (take (s) xys)) \<union> set (map snd (take (s) xys))"
    unfolding assms(7) length_xys
    by (simp add: assms(4))
  show ?thesis 
    using assms(4) length_xys unfolding XR_is
    by(intro single_matroid_augment_general[OF assms(1,2,3) length_xys  assms(5,6)  , of "s "]) auto
qed
end

locale double_matroid =
  matroid1: matroid carrier indep1 +
  matroid2: matroid carrier indep2
  for carrier indep1 indep2
begin

definition "is_max X = (indep1 X \<and> indep2 X \<and> (\<nexists> Y. indep1 Y \<and> indep2 Y \<and> card Y > card X))"

lemma indep_set_rank_bound:
  assumes "Q \<subseteq> carrier" "indep1 F" "indep2 F"
  shows "card F \<le> matroid1.rank_of Q + matroid2.rank_of (carrier - Q)"
proof-
  have claim1:"indep1 (F \<inter> Q)" 
    using assms matroid1.indep_subset by fastforce
  hence claim2:"matroid1.rank_of Q \<ge> card (F \<inter> Q)"
    by (simp add: assms(1) matroid1.indep_in_def matroid1.rank_of_indep_in_le)
  have claim3: "indep2 (F - Q)"
    using assms(3) matroid2.indep_subset by force
  hence claim4: "matroid2.rank_of (carrier - Q) \<ge> card (F - Q)" 
    by (simp add: Diff_mono assms(3) matroid2.indep_inI matroid2.indep_subset_carrier matroid2.rank_of_indep_in_le)
  have claim5: "card F = card (F \<inter> Q) + card (F - Q)" 
    by(auto intro: card_Int_Diff simp add: assms(2))
  show ?thesis
    using claim2 claim4 claim5 by linarith
qed

corollary optimality_from_rank:
  (*Note that F does not even need to be independent!*)
  assumes "Q \<subseteq> carrier" "card F = matroid1.rank_of Q + matroid2.rank_of (carrier - Q)"
  shows "\<nexists> X. indep1 X \<and> indep2 X \<and> card X > card F"
  using  assms(2) indep_set_rank_bound[OF assms(1)] by fastforce

context fixes X::"'a set"
begin
definition "A1 = {(x, y) | x y. y \<in> carrier - X \<and> x \<in> matroid1.the_circuit (insert y X) - {y}}"

definition "A2 = {(y, x) | x y. y \<in> carrier - X \<and> x \<in> matroid2.the_circuit (insert y X) - {y}}"

definition "S = {y | y. y \<in> carrier - X \<and> indep1 (insert y X)}"
definition "T = {y | y. y \<in> carrier - X \<and> indep2 (insert y X)}"

context 
  assumes indep1X:"indep1 X"  and indep2X: "indep2 X"
begin

lemma X_in_carrier: "X \<subseteq> carrier" 
  by (simp add: indep1X matroid1.indep_subset_carrier)

lemma S_in_carrier: "S \<subseteq> carrier"
  by (simp add: S_def)

lemma T_in_carrier: "T \<subseteq> carrier"
  by (simp add: T_def)

lemma A1_edges:
  assumes "e \<in> A1"
  shows "fst e \<in> X" (is ?thesis1) and  "snd e \<in> carrier - X" (is ?thesis2)
proof-
  have "snd e \<in> carrier - X" "fst e \<in> matroid1.the_circuit (insert (snd e) X) - {snd e}"
    using assms by(auto simp add: A1_def)
  moreover then show ?thesis1
    using indep1X matroid1.indep_subset_carrier matroid1.the_circuit_is_circuit(2)
      matroid1.the_circuit_non_empty_dependent by fastforce
  ultimately show ?thesis2 by simp
qed

lemma A2_edges:
  assumes "e \<in> A2"
  shows "snd e \<in> X" (is ?thesis1) and  "fst e \<in> carrier - X" (is ?thesis2)
proof-
  have "fst e \<in> carrier - X" "snd e \<in> matroid2.the_circuit (insert (fst e) X) - {fst e}"
    using assms by(auto simp add: A2_def)
  moreover then show ?thesis1
    using indep2X matroid2.indep_subset_carrier matroid2.the_circuit_is_circuit(2)
      matroid2.the_circuit_non_empty_dependent by fastforce
  ultimately show ?thesis2 by simp
qed

lemma dVs_A1_carrier: "dVs (A1) \<subseteq> carrier" 
proof(rule, goal_cases)
  case (1 xx)
  then obtain e where "e \<in> A1" "xx = fst e \<or> xx = snd e" by(auto simp add: dVs_def)
  moreover then obtain x y where "y \<in> carrier - X" "x \<in> matroid1.the_circuit (insert y X) - {y}" "e =(x,y)"
    by(auto simp add: A1_def)
  moreover hence "x \<in> X" 
    using indep1X matroid1.indep_subset_carrier matroid1.the_circuit_is_circuit(2) 
      matroid1.the_circuit_non_empty_dependent by fastforce
  moreover have "X \<subseteq> carrier"
    by (simp add: indep2X matroid2.indep_subset_carrier)
  ultimately show ?case by auto
qed

lemma dVs_A2_carrier: "dVs (A2) \<subseteq> carrier" 
proof(rule, goal_cases)
  case (1 xx)
  then obtain e where "e \<in> A2" "xx = fst e \<or> xx = snd e" by(auto simp add: dVs_def)
  moreover then obtain x y where "y \<in> carrier - X" "x \<in> matroid2.the_circuit (insert y X) - {y}" "e=(y,x)"
    by(auto simp add: A2_def)
  moreover hence "x \<in> X" 
    using indep2X matroid2.indep_subset_carrier matroid2.the_circuit_is_circuit(2) 
      matroid2.the_circuit_non_empty_dependent by fastforce
  moreover have "X \<subseteq> carrier"
    by (simp add: indep2X matroid2.indep_subset_carrier)
  ultimately show ?case by auto
qed

lemma dVs_A1A2_carrier: "dVs (A1 \<union> A2) \<subseteq> carrier" 
  by (simp add: dVs_A1_carrier dVs_A2_carrier)

lemma A1_single_edge_endpoints_X_carrier:
  assumes "(x,y) \<in> A1"
  shows "x \<in> X" "y \<in> carrier - X"
  using assms unfolding A1_def
  using A1_edges(1) assms by auto

lemma A2_single_edge_endpoints_X_carrier:
  assumes "(x,y) \<in> A2"
  shows "y \<in> X" "x \<in> carrier - X"
  using assms unfolding A2_def
  using A2_edges(1) assms by auto
(*express as alternating list*) 
lemma walk_is_alternating_gen:
  assumes "awalk (A1 \<union> A2) start p end" "start \<in> carrier - X" "end \<in> carrier - X"
    "l = length p"
  shows "even l \<and>  alt_list (\<lambda> e. e\<in>  A2) (\<lambda> e. e \<in> A1) p"
(*"even l \<and> (\<forall> i < l. (even i \<longrightarrow> p ! i \<in> A2) \<and> (odd i \<longrightarrow> p ! i \<in> A1))"*)
  using assms
proof(induction l arbitrary: start p "end" rule: less_induct)
  case (less l)
  have l_cases:"(l = (0::nat) \<Longrightarrow>P l) \<Longrightarrow> (l = 1 \<Longrightarrow> P l) \<Longrightarrow> (\<And> ll. l = ll + 2 \<Longrightarrow> P l) \<Longrightarrow> P l" for l P
    by (metis One_nat_def add_2_eq_Suc' not0_implies_Suc)
  show ?case 
  proof(rule l_cases[of l], goal_cases)
    case 1
    then show ?case using less(5) by (auto intro: alt_list.intros)
  next
    case 2
    then obtain e where p_is: "p = [e]" 
      using less(5) by(cases p) auto
    hence e_inA1A2:"e \<in> A1 \<union> A2"
      using less.prems(1) by auto
    have "snd e \<in> X"
      using  A1_edges(1)[of e]  less.prems(1) less.prems(2) A2_edges(1)[of e] 
      by(auto simp add: awalk_Cons_iff  p_is)
    moreover have "snd e = end" 
      using awalk_ends less.prems(1) by(auto simp add:  awalk_Cons_iff  p_is)  
    ultimately show ?case
      using less.prems(3) by blast
  next
    case (3 ll)
    then obtain e1 e2 q where p_decompose:"p = e1#e2#q"
      using less(5) by(auto intro: vwalk_arcs.cases[of p])
    have some_properties: "e1 \<in> A1 \<union> A2" "fst e1 = start" "snd e1 = fst e2" 
      "e2 \<in> A1 \<union> A2" "awalk (A1 \<union> A2) (snd e2) q end"
      using  less.prems(1) by(auto simp add: awalk_Cons_iff p_decompose)
    have e1A2:"e1 \<in> A2" 
      using A1_edges(1) less.prems(2) some_properties(1) some_properties(2) by blast
    have e2A1: "e2 \<in> A1"
      using  A2_edges(1)[OF e1A2] some_properties(3)
      by (auto intro: UnE[OF  some_properties(4)] DiffE[OF A2_edges(2)[of e2]])
    have snd_e2_in:"snd e2 \<in> carrier - X"
      using A1_edges(2) e2A1 by auto
    have IH_applied:"even ll \<and> alt_list (\<lambda>e. e \<in> A2) (\<lambda>e. e \<in> A1) q"
      using 3 less(4,5) p_decompose 
      by (intro less.IH[ OF _  some_properties(5)  snd_e2_in]) auto
    hence "even l" 
      by (simp add: "3")
    moreover have "alt_list (\<lambda>e. e \<in> A2) (\<lambda>e. e \<in> A1) p"
      using e1A2 e2A1 IH_applied
      by(auto intro: alt_list.intros simp add: p_decompose )  
    ultimately show ?case by auto
  qed
qed

lemma walk_is_alternating:
  assumes "awalk (A1 \<union> A2) start p end" "start \<in> carrier - X" "end \<in> carrier - X"
  shows "alt_list (\<lambda> e. e\<in>  A2) (\<lambda> e. e \<in> A1) p"
  using assms(1,2,3) walk_is_alternating_gen by blast

lemma walk_is_even:
  assumes "awalk (A1 \<union> A2) start p end" "start \<in> carrier - X" "end \<in> carrier - X"
  shows "even (length p)"
  using assms(1,2,3) walk_is_alternating_gen by blast

lemma walk_is_odd:
  assumes "vwalk_bet (A1 \<union> A2) start p end" "start \<in> carrier - X" "end \<in> carrier - X"
  shows   "odd (length p)" 
 using assms(1)  walk_is_even[OF vwalk_imp_awalk[OF assms(1)] assms(2,3)]
 by (auto simp add:  edges_of_vwalk_length'[symmetric])

lemma take_last:"i < length xs  \<Longrightarrow> last (take (i+1) xs) = xs ! i"
  using take_Suc_conv_app_nth by fastforce

lemma augment_in_matroid1: 
  assumes  "vwalk_bet (A1 \<union> A2) x p y" "x \<in> S" "y \<in> T" 
    "\<nexists> q. vwalk_bet (A1 \<union> A2) x q y \<and> length q < length p"
  shows "indep1 ((X \<union> {p ! i | i. i < length p \<and> even i}) -  {p ! i | i. i < length p \<and> odd i})"
proof-
  have p_non_empt:"p \<noteq> []"
    using assms(1) by auto
  have p_init:"p ! 0 = x"
    using assms(1) hd_conv_nth[OF p_non_empt] by(auto simp add: vwalk_bet_def)
  have X0: "indep1 (insert (p ! 0) X)"
    using assms(2) by(auto simp add: S_def p_init)
  have odd_p: "odd (length p)"
    using assms(2,3)
    by(intro  walk_is_odd[OF assms(1)])(auto simp add: S_def T_def) 
  have distinct_p: "distinct p" 
    using shortest_vwalk_bet_distinct assms by auto
  define s where "s = (length p -1) div 2"
  define list where "list = [(p! (2*i+1), p ! (2*i+2)).  i <-[0..<s]]"
  have "s -1 = length list - 1"
    by(auto simp add:  s_def list_def)
  have odds_are:"set (map fst list) =  {p ! i | i. i < length p \<and> odd i}"
    using odd_p 
    by (presburger | 
        auto intro!: image_eqI[of "_ i" _ "(i - 1) div 2" for i] image_eqI[of "p ! i" fst for i]
        intro: less_mult_imp_div_less 
        simp add: dvd_div_mult_self list_def s_def)+
  have evens_are:"set (map snd list) \<union> {p! 0} =  {p ! i | i. i < length p \<and> even i}"
    using odd_p not_less_eq_eq
    by (auto intro!: less_mult_imp_div_less  diff_less_mono cong[OF refl, of _ _ "\<lambda> i. p ! i"]
                     image_eqI[of "_ i" _ "(i -1) div 2" for i]
                     image_eqI[of "p!i" snd 
                     "(p ! Suc (2 * ((i-1) div 2)), p ! Suc (Suc (2 * ((i-1) div 2))))" for i]
          simp add: dvd_div_mult_self list_def s_def)+
  have helper1:"i < length p \<Longrightarrow> odd i \<Longrightarrow> (a, p ! i) \<in> set list \<Longrightarrow> False" for i a
    using distinct_p 
    by (auto simp add:  list_def nth_eq_iff_index_eq s_def)
  have thm_precond1:"(X \<union> {p ! i | i. i < length p \<and> even i}) -  {p ! i | i. i < length p \<and> odd i} = 
            insert (p ! 0) X - set (map fst list) \<union> set (map snd list)"
    using  odds_are evens_are helper1 by auto
  have list_and_p: "set (map fst list) \<subseteq> set p"  "set (map snd list) \<subseteq> set p" 
    by(auto simp add: list_def s_def)
  have awalk_p:"awalk (A1 \<union> A2) x (edges_of_vwalk p) y" 
    by (simp add: assms(1) vwalk_imp_awalk)
  have x_not_inX: "x \<in> carrier - X" 
    using S_def assms(2) by blast
  have y_not_inX: "y \<in> carrier - X" 
    using T_def assms(3) by blast
  have list_in_A1:"set list \<subseteq> A1"
    using walk_is_alternating[OF awalk_p x_not_inX y_not_inX]
    by (force intro: alternating_list_odd_index 
           simp add: edges_of_vwalk_length  edges_of_vwalk_index[symmetric] list_def s_def)
  have fst_list_in_X: "set (map fst list) \<subseteq> X"
    using A1_edges(1) list_in_A1 by auto
  have snd_list_not_in_X: "set (map snd list) \<subseteq> carrier - X"
    using A1_edges(2) list_in_A1 by auto
  have thm_precond2: "set (map fst list) \<subseteq> insert (p ! 0) X"
    using fst_list_in_X by blast
  have helper3:" snd ` set list \<subseteq> carrier - X \<Longrightarrow> (a, p ! 0) \<in> set list \<Longrightarrow> False" for a
    using distinct_p nth_eq_iff_index_eq odd_p by (fastforce simp add:  list_def s_def)
  have thm_precond3: "set (map snd list) \<subseteq> carrier - insert (p ! 0) X"
    using snd_list_not_in_X by (auto intro: helper3)
  have p_carrier: "set p \<subseteq> carrier" 
    using assms(1) dVs_A1A2_carrier vwalk_bet_in_dVs by fast
  have thm_precond4:" i < length list \<Longrightarrow>
      fst (list ! i) \<in> matroid1.the_circuit (insert (snd (list ! i)) (insert (p ! 0) X))" for i
      using nth_mem  list_in_A1
      by(subst matroid1.same_cicuit_indep_part_extended[of "snd (list ! i)" X, OF _ X0],
         (force intro!: matroid1.the_circuit_non_empty_dependent 
              simp add: A1_def )+)
  have thm_precond5: "i < length list \<Longrightarrow>
        j < length list \<Longrightarrow>
        j < i \<Longrightarrow> fst (list ! j) \<notin> matroid1.the_circuit (insert (snd (list ! i)) (insert (p ! 0) X))" for i j
  proof(rule ccontr,subst (asm) not_not, goal_cases)
    case 1
    hence fst_in_list:"fst (list ! j) \<in> set (map fst list)" using 1 by simp
    have j_length_p:"2 * j + 2 < length p" 
      using 1 by(simp add: list_def s_def)
    have i_length_p:"2 * i + 2 < length p" 
      using 1 by(simp add: list_def s_def)
    have list_j_is:"list ! j = (p ! (2*j+1) , p! (2*j + 2))"
      using 1 by(simp add: list_def s_def)
    have list_i_is:"list ! i = (p ! (2*i+1) , p! (2*i + 2))"
      using 1 by(simp add: list_def s_def)
    have non_indep_snd:" \<not> indep1 (insert (snd (list ! i)) X)" 
      using list_in_A1 1(1)  nth_mem 
      by (force intro!: matroid1.the_circuit_non_empty_dependent simp add: A1_def)
    have snd_j_in_carrier:"snd (list ! i) \<in> carrier -  X" 
      using "1"(1) nth_mem thm_precond3 by fastforce
    have circuit_is:" matroid1.the_circuit (insert (snd (list ! i)) (insert (p ! 0) X)) =
              matroid1.the_circuit (insert (snd (list ! i)) X)" 
      using  snd_j_in_carrier
      by(auto intro!: matroid1.same_cicuit_indep_part_extended[OF non_indep_snd X0 _])
    have fst_not_snd: "snd (list ! i) \<noteq> fst (list ! j)"
      using fst_in_list fst_list_in_X snd_j_in_carrier by fastforce
    moreover have "last (take (2*j +2) p) = p ! (2*j+1)" 
      using take_last[of "2*j+1" p] j_length_p by simp
    ultimately have walk_x_inter: "vwalk_bet (A1 \<union> A2) x (take (2*j +2) p) (fst (list ! j))"
      using vwalk_bet_prefix_is_vwalk_bet[of "(take (2*j +2) p)" "A1 \<union> A2" x "drop (2*j +2) p" y]
        i_length_p  assms(1) 
      by (simp add: list_j_is)
    have found_edge_in:"(fst (list ! j) , (snd (list ! i))) \<in> A1"
      using 1(4) snd_j_in_carrier  fst_not_snd by (auto simp add: A1_def circuit_is)
    have "hd (drop (2 * i + 2) p) = snd (list ! i)"
      by(subst hd_drop_conv_nth[OF i_length_p])(simp add: list_i_is)   
    hence vwalk_further:"vwalk_bet (A1 \<union> A2)  (snd (list ! i)) (drop (2*i+2) p) y"
      using vwalk_bet_suffix_is_vwalk_bet[of "(drop (2*i +2) p)" "A1 \<union> A2" x "take (2*i +2) p" y]
            i_length_p  assms(1) 
      by auto
    have better_walk: "vwalk_bet (A1 \<union> A2) x (take (2*j + 2) p  @
                                              (drop (2*i+2) p)) y"
      using walk_x_inter found_edge_in vwalk_further 
      by (auto intro: vwalk_append_intermediate_edge)
    moreover have "length (take (2*j + 2) p  @ (drop (2*i+2) p)) < length p" 
      using j_length_p  "1"(3) i_length_p by auto
    ultimately show ?case
      using assms by auto
  qed
  show ?thesis
    using  matroid1.single_matroid_augment[OF X0 thm_precond2 thm_precond3 refl thm_precond4
        thm_precond5 thm_precond1]
    by simp
qed

lemma augment_in_matroid1_single: 
  assumes  "x \<in> S" "x \<in> T" 
  shows "indep1 (insert x X)"
  using assms by(auto simp add: S_def T_def) 

lemma augment_in_matroid2_single: 
  assumes  "x \<in> S" "x \<in> T" 
  shows "indep2 (insert x X)"
  using assms by(auto simp add: S_def T_def) 

lemma augment_in_matroid2: 
  assumes "vwalk_bet (A1 \<union> A2) x p y" "x \<in> S" "y \<in> T" 
    "\<nexists> q. vwalk_bet (A1 \<union> A2) x q y \<and> length q < length p"
  shows "indep2 ((X \<union> {p ! i | i. i < length p \<and> even i}) -  {p ! i | i. i < length p \<and> odd i})"
proof-
  have upt_image_nat_0: "f ` {..<(y::nat)} = {f z | z. z < y} " for f  y
  by auto
  have p_non_empt:"p \<noteq> []"
    using assms(1) by auto
  have p_init:"p ! (length p -1) = y"
    using assms(1) last_conv_nth[OF p_non_empt] by(auto simp add: vwalk_bet_def)
  have X0: "indep2 (insert (p ! (length p - 1)) X)"
    using assms(3)p_init by(auto simp add: T_def)
  have odd_p: "odd (length p)"
    using assms(2,3)
    by(intro  walk_is_odd[OF assms(1)])(auto simp add: S_def T_def) 
  have distinct_p: "distinct p" 
    using shortest_vwalk_bet_distinct assms by auto

  define s where "s = (length p -1) div 2"

  define list where "list = [(p! (2*i+1), p ! (2*i)).  i <- [0..<s]]"
  have "s -1 = length list - 1"
    by(auto simp add:  s_def list_def)
  have odds_are:"set (map fst list) =  {p ! i | i. i < length p \<and> odd i}"
    using odd_p 
    by (presburger | 
        auto intro!: image_eqI[of "_ i" _ "(i - 1) div 2" for i] image_eqI[of "p ! i" fst for i]
        intro: less_mult_imp_div_less 
        simp add: list_def s_def)+
  have evens_are:"set (map snd list) \<union> {p! (length p -1)} =  {p ! i | i. i < length p \<and> even i}"
    using odd_p  p_non_empt
    by (auto intro!: less_mult_imp_div_less  diff_less_mono cong[OF refl, of _ _ "\<lambda> i. p ! i"]
                     image_eqI[of "_ i" _ "(i ) div 2" for i]
                     image_eqI[of "p!i" snd 
                     "(p ! Suc (2 * ((i) div 2)), p !  (2 * ((i) div 2)))" for i]
          simp add: list_def s_def)
  have helper1:"i < length p \<Longrightarrow> odd i \<Longrightarrow> (a, p ! i) \<in> set list \<Longrightarrow> False" for i a
    using distinct_p 
    by (auto simp add:  list_def nth_eq_iff_index_eq s_def)
  have thm_precond1:"(X \<union> {p ! i | i. i < length p \<and> even i}) -  {p ! i | i. i < length p \<and> odd i} = 
            insert (p ! (length p - 1)) X - set (map fst list) \<union> set (map snd list)"
    using  odds_are evens_are helper1 by auto
  hence thm_precond1: "X \<union> {p ! i |i. i < length p \<and> even i} - {p ! i |i. i < length p \<and> odd i} =
    insert (p ! (length p - 1)) X - set (map fst (rev list)) \<union> set (map snd (rev list))"
    by simp
  have list_and_p: "set (map fst list) \<subseteq> set p"  "set (map snd list) \<subseteq> set p" 
    by(auto simp add: list_def s_def)
  have awalk_p:"awalk (A1 \<union> A2) x (edges_of_vwalk p) y" 
    by (simp add: assms(1) vwalk_imp_awalk)
  have x_not_inX: "x \<in> carrier - X" 
    using S_def assms(2) by blast
  have y_not_inX: "y \<in> carrier - X" 
    using T_def assms(3) by blast
  have list_in_A2:"set list \<subseteq> prod.swap ` A2" "set (map prod.swap list) \<subseteq>  A2"
    using walk_is_alternating[OF awalk_p x_not_inX y_not_inX]
    by (force intro: alternating_list_even_index 
           simp add: edges_of_vwalk_length  edges_of_vwalk_index[symmetric] list_def s_def)+
  have fst_list_in_X: "set (map fst list) \<subseteq> X"
    using list_in_A2 
    by(force intro: A2_single_edge_endpoints_X_carrier(1))
  have snd_list_not_in_X: "set (map snd list) \<subseteq> carrier - X"
    using list_in_A2
    by(force dest: A2_single_edge_endpoints_X_carrier(2))
  have thm_precond2: "set (map fst list) \<subseteq> insert (p ! (length p -1)) X"
    using fst_list_in_X by blast
  hence thm_precond2: "set (map fst (rev list)) \<subseteq> insert (p ! (length p -1)) X"
    by simp
  have helper3:" snd ` set list \<subseteq> carrier - X \<Longrightarrow> (a, p ! (length p -1)) \<in> set list \<Longrightarrow> False" for a
    using distinct_p nth_eq_iff_index_eq odd_p by (fastforce simp add:  list_def s_def)
  have thm_precond3: "set (map snd list) \<subseteq> carrier - insert (p ! (length p -1)) X"
    using snd_list_not_in_X by (auto intro: helper3)
  hence thm_precond3: "set (map snd (rev list)) \<subseteq> carrier - insert (p ! (length p -1)) X"
    by auto
  have p_carrier: "set p \<subseteq> carrier" 
    using assms(1) dVs_A1A2_carrier vwalk_bet_in_dVs by fast
  have thm_precond4:" i < length list \<Longrightarrow>
      fst (list ! i) \<in> matroid2.the_circuit (insert (snd (list ! i)) (insert (p ! (length p -1)) X))" for i
        using nth_mem  list_in_A2(1)  list_and_p(2) p_carrier nth_mem 
        by(subst matroid2.same_cicuit_indep_part_extended[of "snd (list ! i)" X, OF _ X0])
          (force intro!: matroid2.the_circuit_non_empty_dependent simp add: A2_def image_Collect)+
  have thm_precond4: "i < length (rev list) \<Longrightarrow>
         fst (rev list ! i)
         \<in> matroid2.the_circuit (insert (snd (rev list ! i)) (insert (p ! (length p - 1)) X))" for i
    using thm_precond4[of "length list - Suc i"] by ((subst rev_nth, simp)+)  auto
  have thm_precond5: "i < length list \<Longrightarrow>
        j < length list \<Longrightarrow>
        i < j \<Longrightarrow> fst (list ! j) \<notin> matroid2.the_circuit (insert (snd (list ! i)) (insert (p ! (length p -1)) X))" for i j
  proof(rule ccontr,subst (asm) not_not, goal_cases)
    case 1
    hence fst_in_list:"fst (list ! j) \<in> set (map fst list)" using 1 by simp
    have j_length_p:"2 * j +1  < length p" 
      using 1 by(simp add: list_def s_def)
    have i_length_p:"2 * i < length p" 
      using 1 by(simp add: list_def s_def)
    have list_j_is:"list ! j = (p ! (2*j+1) , p! (2*j))"
      using 1 by(simp add: list_def s_def)
    have list_i_is:"list ! i = (p ! (2*i+1) , p! (2*i))"
      using 1 by(simp add: list_def s_def)
    have non_indep_snd:" \<not> indep2 (insert (snd (list ! i)) X)" 
      using list_in_A2 1(1)  nth_mem 
      by (force intro!: matroid2.the_circuit_non_empty_dependent simp add: A2_def)
    have snd_j_in_carrier:"snd (list ! i) \<in> carrier -  X" 
      using "1"(1) nth_mem thm_precond3 by fastforce
    have circuit_is:" matroid2.the_circuit (insert (snd (list ! i)) (insert (p ! (length p -1)) X)) =
              matroid2.the_circuit (insert (snd (list ! i)) X)" 
      using  snd_j_in_carrier  matroid2.same_cicuit_indep_part_extended[OF non_indep_snd X0 _] 
      by auto
    have fst_not_snd: "snd (list ! i) \<noteq> fst (list ! j)"
      using fst_in_list fst_list_in_X snd_j_in_carrier by fastforce
    moreover have "last (take (2*i  + 1) p) = p ! (2*i)" 
      using take_last[of "2*i" p] i_length_p by simp
    ultimately have walk_x_inter: "vwalk_bet (A1 \<union> A2) x (take (2*i + 1) p) (snd (list ! i))"
      using vwalk_bet_prefix_is_vwalk_bet[of "(take (2*i + 1) p)" "A1 \<union> A2" x "drop (2*i + 1) p" y]
        i_length_p  assms(1) 
      by (simp add: list_i_is)
    have found_edge_in:"((snd (list ! i)), fst (list ! j) ) \<in> A2"
      using 1(4) snd_j_in_carrier   unfolding A2_def circuit_is
      using fst_not_snd by auto
    have "hd (drop (2 * j + 1) p) = fst (list ! j)"
      using  hd_drop_conv_nth[OF j_length_p]
      by(auto simp add: list_j_is)
    hence vwalk_further:"vwalk_bet (A1 \<union> A2)  (fst (list ! j)) (drop (2*j+1) p) y"
      using vwalk_bet_suffix_is_vwalk_bet[of "(drop (2*j +1) p)" "A1 \<union> A2" x "take (2*j +1) p" y]
      using j_length_p  assms(1) 
      by auto
    have better_walk: "vwalk_bet (A1 \<union> A2) x (take (2*i + 1) p  @
                                              (drop (2*j+1) p)) y"
      using walk_x_inter found_edge_in vwalk_further 
      by (auto intro: vwalk_append_intermediate_edge)
    moreover have "length (take (2*i + 1) p  @ (drop (2*j+1) p)) < length p" 
      using j_length_p  "1"(3) i_length_p by auto
    ultimately show ?case
      using assms by auto
  qed
  have thm_precond5: "i < length (rev list) \<Longrightarrow>
           j < length (rev list) \<Longrightarrow>
           j < i \<Longrightarrow>
           fst (rev list ! j)
           \<notin> matroid2.the_circuit (insert (snd (rev list ! i)) (insert (p ! (length p - 1)) X))" for i j
    using thm_precond5[of "length list - Suc i" "length list - Suc j"] by ((subst rev_nth, simp)+)  auto
  show ?thesis
    by(auto intro: matroid2.single_matroid_augment[OF X0 thm_precond2 thm_precond3 
          refl thm_precond4 thm_precond5 thm_precond1])     
qed

lemma card_of_evens_under_odd:
  assumes "odd i"
  shows "card {x. x < i \<and> even x} = i div 2 + 1"
proof-
  obtain j where i_is:"i = 2*j + 1"
    using assms(1) oddE by blast
  show ?thesis
  proof((subst i_is)+, induction j)
    case 0
    have "{x. x < 2 * 0 + (1::nat) \<and> even x} = {0}" by auto
    then show ?case by simp
  next
    case (Suc j)
    have "{x. x < 2 * Suc j + 1 \<and> even x} = 
          {x. x <  2* j + 1 \<and> even x} \<union> {2*Suc j}"
      using less_Suc_eq by auto
    hence card_split: "card {x. x < 2 * Suc j + 1 \<and> even x} = 
          card {x. x <  2* j + 1 \<and> even x}  + 1"
      by simp
    show ?case
      by(subst card_split, subst Suc(1)) simp
  qed
qed

lemma card_of_odds_under_odd:
  assumes "odd i"
  shows "card {x. x < i \<and> odd x} = i div 2"
proof-
  obtain j where i_is:"i = 2*j + 1"
    using assms(1) oddE by blast
  show ?thesis
  proof((subst i_is)+, induction j)
    case 0
    have "{x. x < 2 * 0 + (1::nat) \<and> odd x} = {}" 
      by fastforce
    then show ?case by simp
  next
    case (Suc j)
    have "{x. x < 2 * Suc j + 1 \<and> odd x} = 
          {x. x <  2* j + 1 \<and> odd x} \<union> {2* j + 1}"
      using less_Suc_eq by fastforce
    hence card_split: "card {x. x < 2 * Suc j + 1 \<and> odd x} = 
          card {x. x <  2* j + 1 \<and> odd x}  + 1"
      by simp
    show ?case
      by(subst card_split, subst Suc(1)) simp
  qed
qed

lemma augment_in_both_matroids:
  assumes  "vwalk_bet (A1 \<union> A2) x p y" "x \<in> S" "y \<in> T" 
    "\<nexists> q. vwalk_bet (A1 \<union> A2) x q y \<and> length q < length p"
    "X' = ((X \<union> {p ! i | i. i < length p \<and> even i}) -  {p ! i | i. i < length p \<and> odd i})"
  shows "indep1 X'" (is ?thesis1)
    and  "indep2 X'" (is ?thesis2)
    and  "card X' = card X + 1" (is ?thesis3)
proof-
  show ?thesis1 
    using assms augment_in_matroid1 by auto
  show ?thesis2
    using assms augment_in_matroid2 by auto
  have awalk:"awalk (A1 \<union> A2) x (edges_of_vwalk p) y"
    using assms(1) by(auto intro!:  vwalk_imp_awalk )
  have x_in_carrier: " x \<in> carrier - X"
    using S_def assms(2) by blast
  have y_in_carrier: " y \<in> carrier - X"
    using T_def assms(3) by blast
  have alternation: "even (length (edges_of_vwalk p))"
    "(\<And> i. i<length (edges_of_vwalk p) \<Longrightarrow> even i \<Longrightarrow> edges_of_vwalk p ! i \<in> A2)"
    "\<And> i. i<length (edges_of_vwalk p) \<Longrightarrow> odd i \<Longrightarrow> edges_of_vwalk p ! i \<in> A1"
    by(auto intro: alternating_list_even_index[OF 
           walk_is_alternating[OF awalk x_in_carrier y_in_carrier]]
                      alternating_list_odd_index[OF 
           walk_is_alternating[OF awalk x_in_carrier y_in_carrier]]
            simp add: walk_is_even[OF awalk x_in_carrier y_in_carrier])
  have odd_in_X: "{p ! i | i. i < length p \<and> odd i} \<subseteq> X"
      using alternation(1)[simplified edges_of_vwalk_length]
      by(intro  forw_subst[ of "p!i" "fst (p ! i, p ! Suc i)" "\<lambda> x. x \<in> X" for i,
                              OF fst_conv[symmetric]]|
         subst edges_of_vwalk_index[of _ p, symmetric]|
         presburger | 
         auto intro!: A1_edges(1)[OF alternating_list_odd_index[OF 
                          walk_is_alternating[OF awalk x_in_carrier y_in_carrier],
                                simplified edges_of_vwalk_length]]
         simp add: edges_of_vwalk_index[of _ p, symmetric])+
    have even_not_in_X: "a \<in> {p ! i | i. i < length p \<and> even i} \<Longrightarrow> a \<notin> X" for a
  proof( goal_cases)
    case 1
    then obtain i where i_prop:"i < length p" "even i" "p ! i = a" by auto
    show ?case
    proof(cases "i = length p -1")
      case True
      hence "a = y" using assms(1) i_prop(3) last_conv_nth 
        by(force simp add: vwalk_bet_def)
      then show ?thesis 
        using assms(3)
        by(simp add: T_def)
    next
      case False
      have p_edge_is: " (p ! i, p ! (i+1)) = edges_of_vwalk p ! i"
        using edges_of_vwalk_index[of "i" p] i_prop  False by auto
      have "(p ! i, p ! (i+1)) \<in> A2"
        using False 
        by(subst  p_edge_is)
          (auto intro!: alternation(2)[simplified edges_of_vwalk_length] 
            simp add: i_prop(1) i_prop(2) less_diff_conv Suc_lessI)
      then show ?thesis
        using i_prop(3) A2_edges(1) by (auto simp add: A2_def)
    qed
  qed
  have distinct_p: "distinct p" 
    by (rule shortest_vwalk_bet_distinct[OF assms(1) assms(4)])
  have p_non_empt:"p \<noteq> []" 
    using assms(1) by auto
  have odd_p: "odd (length p )" 
    using  alternation(1) p_non_empt by (simp add: edges_of_vwalk_length)
  have card_even:"card {p ! i |i. i < length p \<and> even i} = length p div 2 + 1"
    by(subst setcompr_eq_image, subst card_image)
      (auto intro: inj_on_nth[OF distinct_p] simp add: card_of_evens_under_odd[OF odd_p])
  have card_odd:"card {p ! i |i. i < length p \<and> odd i} = length p div 2"
    by(subst setcompr_eq_image, subst card_image)
      (auto intro: inj_on_nth[OF distinct_p] simp add: card_of_odds_under_odd[OF odd_p])
  have disjnt: "disjnt X {p ! i |i. i < length p \<and> even i}"
    using even_not_in_X by(fastforce simp add: disjnt_def)
  show ?thesis3
    using odd_in_X disjnt card_even card_odd 
    by (subst assms(5), subst card_Diff_subset)
      (auto simp add:  card_Un_disjnt diff_add_assoc indep1X)
qed

lemma augment_in_both_matroids_single:
  assumes  "x \<in> S" "x \<in> T" 
  shows "indep1 (insert x X)"
    and  "indep2 (insert x X)"
    and  "card (insert x X) = card X + 1"
  using augment_in_matroid2_single[OF assms]  augment_in_matroid1_single[OF assms] assms(2) indep1X 
  by (auto simp add:  T_def)

theorem if_maximum_then_no_augpath:
  "(\<nexists> Y. indep1 Y \<and> indep2 Y \<and> card Y > card X) 
   \<Longrightarrow> \<not> (\<exists> p x y. x \<in> S \<and> y \<in> T \<and> (vwalk_bet (A1 \<union> A2) x p y \<or> x= y))"
proof(rule ccontr, goal_cases)
  case 1
  then obtain x p y where xpy:"x \<in> S" "y \<in> T" "vwalk_bet (A1 \<union> A2) x p y \<or> x = y"
    by auto
  have "x \<noteq> y" using "1"(1) augment_in_both_matroids_single[of x]   xpy(1,2) by fastforce
  hence xpy:"x \<in> S" "y \<in> T" "vwalk_bet (A1 \<union> A2) x p y"
    using xpy by simp+
  obtain q where  q_prop:"vwalk_bet (A1 \<union> A2) x q y"  "\<nexists> q'. vwalk_bet (A1 \<union> A2) x q' y
                          \<and> length q' < length q" 
    using exists_smallest_witness[ where P = "\<lambda> p. vwalk_bet (A1 \<union> A2) x p y" and f = length, OF xpy(3) refl]
    by auto
  show ?case
    using augment_in_both_matroids[OF q_prop(1) xpy(1,2) q_prop(2) refl] 1(1) by auto
qed

lemma if_no_augpath_then_maximum:
  assumes "\<not> (\<exists> p x y. x \<in> S \<and> y \<in> T \<and> (vwalk_bet (A1 \<union> A2) x p y \<or> x= y))"
    and R_def:  "R = { y | y.  \<exists> x p. (vwalk_bet (A1 \<union> A2) x p y \<or> x = y) \<and> x \<in> S}"
  shows "(\<nexists> Y. indep1 Y \<and> indep2 Y \<and> card Y > card X) "
    and "matroid2.rank_of R = card (X \<inter> R)"
    and "matroid1.rank_of (carrier  - R) = card (X - R)"
    and "card X = matroid2.rank_of R + matroid1.rank_of (carrier - R)"
    and "R \<subseteq> carrier"
proof-
  note 2 = assms(1)
  have T_R: " T \<inter> R = {}"
    using 2 by (auto simp add: R_def)
  have S_in_R: "S \<subseteq>  R"
    by(auto simp add: R_def S_def)
  show R_in_carrier:"R \<subseteq> carrier"
    unfolding R_def
  proof(rule, goal_cases)
    case (1 x)
    then obtain z p where "(vwalk_bet (A1 \<union> A2) z p x \<or> x = z)" "z \<in> S" by auto
    hence "x \<in> dVs (A1 \<union> A2) \<or> x \<in> S"
      by (meson awalkE' vwalk_imp_awalk)
    then show ?case
      using S_in_carrier dVs_A1A2_carrier by blast
  qed
  show "matroid2.rank_of R = card (X \<inter> R)"
  proof(rule ccontr, goal_cases)
    case 1
    have indep_inter:"indep2 (X \<inter> R)"
      by (metis indep2X inf_le1 matroid2.indep_subset)
    hence card_rank_inter: "card (X \<inter> R) = matroid2.rank_of (X \<inter> R)" 
      using matroid2.indep_iff_rank_of[of "X \<inter> R"] matroid2.indep_subset_carrier[of "X \<inter> R"] by auto
    moreover have "matroid2.rank_of R  \<ge> matroid2.rank_of (X \<inter> R)" 
      by (simp add: R_in_carrier matroid2.rank_of_mono)
    ultimately have rank_strict:"matroid2.rank_of R  > matroid2.rank_of (X \<inter> R)" 
      using "1" by linarith
    have "\<exists> y. y \<in> R - X \<and> indep2 (insert y (X \<inter> R ))" 
    proof(rule ccontr)
      assume asm: "\<nexists>y. y \<in> R - X \<and> indep2 (insert y (X \<inter> R))"
      hence "matroid2.basis_in R (X \<inter> R)" 
        using matroid2.indep_in_indep 
        by  (intro matroid2.basis_inI[of R "X \<inter> R"])(auto simp add: R_in_carrier indep_inter matroid2.indep_inI)
      hence "matroid2.rank_of R  = matroid2.rank_of (X \<inter> R)" 
        using "1" R_in_carrier matroid2.rank_of_eq_card_basis_in by blast 
      thus False using rank_strict by auto
    qed
    then obtain y where y_prop: "y \<in> R - X" "indep2 (insert y (X \<inter> R ))" 
      by auto
    have y_not_in_T:"y \<notin> T" 
      using T_R y_prop(1) by auto
    hence non_indep_y_X: "\<not> indep2 (insert y X)"
      using R_in_carrier T_def y_prop(1) by auto
    have "\<exists> x. x \<in> matroid2.the_circuit (insert y X) \<and> x \<in> X - R" 
    proof-
      have "matroid2.the_circuit (insert y X) \<subseteq> insert y X"
        using  matroid2.indep_subset_carrier[OF indep2X ]
          matroid2.the_circuit_is_circuit(2)[OF indep2X non_indep_y_X ]  y_prop(2)
          matroid2.indep_subset_carrier by auto
      moreover have "\<not> matroid2.the_circuit (insert y X) \<subseteq> insert y (X \<inter> R )"
        using y_prop(2)  matroid2.indep_subset_carrier  indep2X  matroid2.indep_subset 
          matroid2.the_circuit_is_circuit(1)[OF  indep2X, of y]  non_indep_y_X           
        by (force simp add:  matroid2.circuit_def )
      ultimately show "\<exists> x. x \<in> matroid2.the_circuit (insert y X) \<and> x \<in> X - R" by auto
    qed
    then obtain x where x_prop:"x \<in> matroid2.the_circuit (insert y X)" "x \<in> X - R" by auto
    moreover have "x \<noteq> y"
      using x_prop(2) y_prop(1) by blast
    moreover have "y \<in> carrier - X" 
      using R_in_carrier y_prop(1) by auto
    ultimately have yx_A2:"(y, x) \<in> A2" 
      by(auto simp add: A2_def)
    have "x \<in> R"
    proof-
      obtain z p where zp:"(vwalk_bet (A1 \<union> A2) z p y \<or> y = z)" "z \<in> S"
        using R_def y_prop(1) by blast
      have "vwalk_bet (A1 \<union> A2) z (p@[x]) x \<or> vwalk_bet (A1 \<union> A2) z ([z, x]) x" 
        apply(rule disjE[OF zp(1)])
        using yx_A2  zp(2)
        by(unfold R_def edge_iff_vwalk_bet, auto simp add: append_vwalk dVsI(2) vwalk_bet_def)
      thus "x \<in> R"
        using zp(2)
        by(unfold R_def) fast
    qed
    thus False
      using x_prop(2) by force
  qed
  moreover show "matroid1.rank_of (carrier  - R) = card (X - R)"
  proof(rule ccontr, goal_cases)
    case 1
    have indep_inter:"indep1 (X - R)"
      by (meson Diff_subset indep1X matroid1.indep_subset)
    hence card_rank_inter: "card (X - R) = matroid1.rank_of (X - R)" 
      using matroid1.indep_iff_rank_of[of "X - R"] matroid1.indep_subset_carrier[of "X - R"] by auto
    moreover have "matroid1.rank_of (carrier - R)  \<ge> matroid1.rank_of (X - R)" 
      by (simp add: Diff_mono X_in_carrier matroid1.rank_of_mono)
    ultimately have rank_strict:"matroid1.rank_of (carrier - R)  > matroid1.rank_of (X - R)" 
      using "1" by linarith
    have "\<exists> y. y \<in> (carrier - R)  - X \<and> indep1 (insert y (X - R ))" 
    proof(rule ccontr)
      assume asm: "\<nexists>y. y \<in> (carrier - R)  - X \<and> indep1 (insert y (X - R))"
      hence "matroid1.basis_in (carrier - R)  (X - R)" 
        using matroid1.indep_in_indep 
        by (intro matroid1.basis_inI[of "(carrier - R) " "X - R"])
          (auto simp add: R_in_carrier indep_inter matroid1.indep_inI  Diff_mono X_in_carrier)       
      hence "matroid1.rank_of (carrier - R)  = matroid1.rank_of (X - R)" 
        using "1" R_in_carrier matroid1.rank_of_eq_card_basis_in by blast 
      thus False using rank_strict by auto
    qed
    then obtain y where y_prop: "y \<in> (carrier - R) - X" "indep1 (insert y (X - R ))" 
      by auto
    have y_not_in_T:"y \<notin> S"
      using S_in_R y_prop(1) by auto
    hence non_indep_y_X: "\<not> indep1 (insert y X)"
      using R_in_carrier S_def y_prop(1) by auto
    have "\<exists> x. x \<in> matroid1.the_circuit (insert y X) \<and> x \<in> X \<inter> R" 
    proof-
      have "matroid1.the_circuit (insert y X) \<subseteq> insert y X"
        using  matroid1.indep_subset_carrier[OF indep1X ]
          matroid1.the_circuit_is_circuit(2)[OF indep1X non_indep_y_X ]  y_prop(2)
          matroid1.indep_subset_carrier by auto
      moreover have "\<not> matroid1.the_circuit (insert y X) \<subseteq> insert y (X - R )"
        using y_prop(2)  matroid1.indep_subset_carrier  indep1X  matroid1.indep_subset 
          matroid1.the_circuit_is_circuit(1)[OF  indep1X, of y]  non_indep_y_X           
        by (force simp add:  matroid1.circuit_def )
      ultimately show "\<exists> x. x \<in> matroid1.the_circuit (insert y X) \<and> x \<in> X \<inter> R" by auto
    qed
    then obtain x where x_prop:"x \<in> matroid1.the_circuit (insert y X)" "x \<in> X \<inter> R" by auto
    moreover have "x \<noteq> y"
      using x_prop(2) y_prop(1) by blast
    moreover have "y \<in> carrier - X" 
      using R_in_carrier y_prop(1) by auto
    ultimately have yx_A1:"(x, y) \<in> A1" 
      by(auto simp add: A1_def)
    have "y \<in> R"
    proof-
      obtain z p where zp:"(vwalk_bet (A1 \<union> A2) z p x \<or> x = z)" "z \<in> S"
        using R_def x_prop(2) by blast
      have "vwalk_bet (A1 \<union> A2) z (p@[y]) y \<or> vwalk_bet (A1 \<union> A2) z ([z, y]) y" 
        apply(rule disjE[OF zp(1)])
        using yx_A1  zp(2)
        by(unfold R_def edge_iff_vwalk_bet, auto simp add: append_vwalk dVsI(2) vwalk_bet_def)
      thus "y \<in> R"
        using zp(2)
        by(unfold R_def) fast
    qed
    thus False
      using y_prop(1) by force
  qed
  ultimately show "card X = matroid2.rank_of R + matroid1.rank_of (carrier - R)" 
    using   matroid2.indep_finite[OF indep2X]
    by(auto intro!: card_Int_Diff )
  thus "\<nexists>Y. indep1 Y \<and> indep2 Y \<and> card X < card Y"
    by(intro optimality_from_rank[of "carrier - R"])
      (auto simp add: R_in_carrier double_diff)
qed

theorem maximum_characterisation:
  "is_max X 
      \<longleftrightarrow> \<not> (\<exists> p x y. x \<in> S \<and> y \<in> T \<and> (vwalk_bet (A1 \<union> A2) x p y \<or> x= y))"
  using if_maximum_then_no_augpath if_no_augpath_then_maximum[OF _ refl] 
    indep1X indep2X by(unfold is_max_def) blast
end
end

corollary two_matroid_max_min_eq: 
  "Max {card X | X. indep1 X \<and> indep2 X} = 
   Min {matroid1.rank_of Q + matroid2.rank_of (carrier - Q) | Q. Q \<subseteq> carrier}"
proof-
  have "\<exists>y. (indep1 y \<and> indep2 y) \<and> (\<nexists>z. (indep1 z \<and> indep2 z) \<and> card y < card z)"
    by(fastforce intro!: exists_greatest_witness[of "\<lambda> X. indep1 X \<and> indep2 X" "{}" _ card, OF _ refl]
        matroid1.finite_number_of_indeps finite_subset[of _ "Collect indep1"])
  then obtain X where X_prop:"\<nexists> Y.  indep1 Y \<and> indep2 Y \<and> card Y > card X"
    "indep1 X" "indep2 X" by auto
  hence X_in_carrier:"X \<subseteq> carrier " 
    using matroid1.indep_subset_carrier by blast
  define R where "R = {y |y. \<exists>x p. (vwalk_bet (A1 X \<union> A2 X) x p y \<or> x = y) \<and> x \<in> S X}"
  have cardX_Max: "Max {card X | X. indep1 X \<and> indep2 X} = card X"
    using X_prop linorder_not_le 
    by(auto intro!: linorder_class.Max_eqI simp add: matroid2.finite_number_of_indeps)
  have cardX_is_rank_R:"card X = matroid2.rank_of R + matroid1.rank_of (carrier - R)"
    and  R_in_carrier: "R \<subseteq> carrier" 
    using  if_no_augpath_then_maximum(4,5)[OF X_prop(2,3)  _ R_def ] 
      if_maximum_then_no_augpath[OF X_prop(2,3,1)] by auto
  have "card X =  Min {matroid1.rank_of Q + matroid2.rank_of (carrier - Q) | Q. Q \<subseteq> carrier}"
    using indep_set_rank_bound[OF _ X_prop(2,3)] cardX_is_rank_R R_in_carrier
    by(auto intro!: sym[OF linorder_class.Min_eqI] exI[of _ "carrier - R"] 
        simp add: matroid2.carrier_finite double_diff)
  thus ?thesis
    using cardX_Max by argo
qed
end
end
