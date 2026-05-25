theory Cardinality_Sums
  imports Basic_Matching.Matching Basic_Matching.Berge
begin

lemma matching_int_card_is_sum:
  assumes "finite (Vs M)"
  assumes "matching M"
  assumes "C \<subseteq> M "
  shows "card ((Vs C) \<inter> X) = sum (\<lambda> e. card (e \<inter> X)) C" 
proof -
  have "finite M" using assms(1) 
    by (metis Vs_def finite_UnionD)
  then have "finite C"  
    using assms(3) finite_subset by auto
  show ?thesis using `finite C` assms(3)
  proof(induct C)
    case empty
    then show ?case   by (simp add: Vs_def)
  next
    case (insert x F)
      then have "finite (Vs F)" 
      by (meson Vs_subset assms(1) finite_subset insert.prems insert_subset)
    have "finite (Vs {x})" 
      by (metis Vs_subset assms(1) insert.prems insert_is_Un le_supE rev_finite_subset)
    have "matching (insert x F)" 
      by (meson assms(2) insert.prems matching_def subset_eq)
    then have card_sum_hyp: "card (Vs F \<inter> X) = (\<Sum>e\<in>F. card (e \<inter> X))" 
      using insert.hyps(3) insert.prems by blast
    then have "\<forall>y \<in> F. x \<inter> y = {}"
      using `matching (insert x F)`
      unfolding matching_def 
      by (metis insert.hyps(2) insertCI)
    then have "Vs F \<inter> Vs {x} = {}" 
      by (auto, simp add: disjoint_iff vs_member)   
    then have "card ((Vs F \<inter> X) \<union> (Vs {x} \<inter> X)) = card (Vs F \<inter> X) + card (Vs {x} \<inter> X)"
      by (simp add: Int_commute Int_left_commute \<open>finite (Vs F)\<close> \<open>finite (Vs {x})\<close> card_Un_disjoint disjoint_iff)
    then have "card (Vs (insert x F) \<inter> X ) = card (Vs F \<inter> X) + card (x \<inter> X)"   
      by (simp add: Int_Un_distrib2 Un_commute Vs_def)
    then show ?case 
      by (simp add: card_sum_hyp insert.hyps(1) insert.hyps(2))
  qed
qed

lemma matching_card_is_sum:
  assumes "finite (Vs M)"
  assumes "matching M"
  assumes "C \<subseteq> M"
  shows "card (Vs C) = sum (\<lambda> e. card e) C" 
proof -
  have "\<forall> c \<in> C. c \<inter> Vs C = c"
    by blast
  then show ?thesis
    using assms matching_int_card_is_sum[of M C "Vs C"] 
    by auto
qed

(*
lemma card_sum_is_mult:
  fixes k :: real
  assumes "finite A"
  shows "sum (\<lambda> e. k) A = k * (card A)"
  by simp
*)

lemma union_card_is_sum:
  assumes "finite A"
  assumes "\<forall>C \<in> A. finite (f C)" 
  assumes "\<forall> C1 \<in> A. \<forall> C2 \<in> A. C1 \<noteq> C2 \<longrightarrow> f C1 \<inter> f C2 = {}"
  shows "sum (\<lambda> C. card (f C)) A = card (\<Union>C\<in>A. (f C))" using assms
proof(induct A)
  case empty
  then show ?case 
    by simp
next
  case (insert x F)
  then have "\<forall>C1 \<in> F. \<forall>C2 \<in> F. C1 \<noteq> C2 \<longrightarrow> f C1 \<inter> f C2 = {}"
    using insert.prems by simp
  then have card_hyps:"(\<Sum>C\<in>F. card (f C)) = card (\<Union> (f ` F))"
    using insert.hyps(3) by (simp add: insert.prems(1))
  have "\<Union> (f ` F) \<inter> f x = {}" 
    using insert.hyps(2) insert.prems by fastforce
  then have "card ((\<Union> (f ` F)) \<union> f x) =  card (\<Union> (f ` F)) + card (f x)" 
    by (meson card_Un_disjoint finite_UN_I insert.hyps(1) insert.prems(1) insertCI)
  then have "card (\<Union> (f ` (insert x F))) = card (\<Union> (f ` F)) + card (f x)"    
    by (metis Un_commute Union_image_insert)
  then show ?case 
    by (simp add: card_hyps insert.hyps(1) insert.hyps(2))
qed

(*
lemma union_card_is_at_least_sum:
  assumes "finite A"
  shows "sum (\<lambda> C. card (f C)) A \<ge> card (\<Union>C\<in>A. (f C))" 
  using assms Groups_Big.card_UN_le by blast
*)

lemma sum_card_connected_components:
  assumes "graph_invar E"
  shows "sum (\<lambda> x. card x) (connected_components E) = card (Vs E)"
proof -
  let ?Cs = "connected_components E"
  have "finite ?Cs"  
    by (simp add: assms finite_con_comps)
  moreover have "\<forall>C \<in> ?Cs. finite C" 
    by (meson assms connected_component_subs_Vs finite_subset)
  moreover have "\<forall> C1 \<in> ?Cs. \<forall> C2 \<in> ?Cs. C1 \<noteq> C2 \<longrightarrow>  C1 \<inter>  C2 = {}"
    by (simp add: connected_components_disj)
  ultimately have "sum (\<lambda> C. card C) ?Cs = card (\<Union>C\<in>?Cs. C)"
    using union_card_is_sum[of ?Cs "(\<lambda> C. C)"] by blast
  then show ?thesis using graph_component_partition[of E] assms by auto
qed


lemma inj_cardinality:
  assumes "finite A"
  assumes "finite B"
  assumes "\<forall>a1 \<in>A.\<forall>a2\<in>A. a1 \<noteq> a2 \<longrightarrow> a1 \<inter> a2 = {}"
  assumes "\<forall>a\<in>A. \<exists>b\<in>B. b \<in> a"
  shows "card A \<le> card B" 
  using assms 
proof(induct A arbitrary: B)
  case empty
  then show ?case by auto
next
  case (insert x F)
  then obtain b where "b \<in> B \<and> b \<in> x" by auto
  then have " \<forall>a\<in>F. b \<notin> a" 
    using UnionI insert.hyps(2) insert.prems(2) by auto
  then have " \<forall>a\<in>F. \<exists>b1\<in>B. b1 \<in> a \<and> b1 \<noteq> b" 
    using insert.prems(3)
    by (metis insert_iff)
  then have "\<forall>a\<in>F. \<exists>b1\<in>B-{b}. b1 \<in> a" 
    by (metis \<open>b \<in> B \<and> b \<in> x\<close> insertE insert_Diff)
  have "finite (B - {b})" 
    using insert.prems(1) by blast
  then  have "card F \<le> card (B - {b})" using insert.prems(2)
    using  \<open>\<forall>a\<in>F. \<exists>b1\<in>B - {b}. b1 \<in> a\<close> insert.hyps(3) 
    by auto
 then have "card F \<le> card B - 1" 
   by (metis \<open>b \<in> B \<and> b \<in> x\<close> card_Diff_singleton)
  have "card B \<ge> 1" 
    using \<open>b \<in> B \<and> b \<in> x\<close> card_0_eq insert.prems(1) linorder_le_less_linear by auto
  then have "card F + 1 \<le> card B" 
    using  \<open>card F \<le> card B - 1\<close> ordered_cancel_comm_monoid_diff_class.le_diff_conv2 by blast
  then have "card (insert x F) \<le> card B" 
    by (simp add: insert.hyps(1) insert.hyps(2))
  then show ?case by auto
qed


lemma ex_subset_same_elem_card:
  assumes "finite A"
  assumes "finite B"
  assumes "\<forall>a1 \<in>A.\<forall>a2\<in>A. a1 \<noteq> a2 \<longrightarrow> a1 \<inter> a2 = {}"
  assumes "\<forall>a\<in>A. \<exists>b\<in>B. b \<in> a"
  shows "\<exists>C\<subseteq>B . \<forall>a\<in>A. \<exists>!b\<in>C. b \<in> a"
  using assms(1) assms(2) assms(3) assms(4)
proof(induct A arbitrary: B)
  case empty
  then show ?case by auto
next
  case (insert x F)
  then obtain b where "b \<in> B \<and> b \<in> x" by auto
  then have " \<forall>a\<in>F. b \<notin> a" 
    using UnionI insert.hyps(2) insert.prems(2) by auto
  then have " \<forall>a\<in>F. \<exists>b1\<in>B. b1 \<in> a \<and> b1 \<noteq> b" 
    using insert.prems(3)
    by (metis insert_iff)
  then have " \<forall>a\<in>F. \<exists>b1\<in>B. b1 \<in> a \<and> b1 \<notin> x" 
    using insert.hyps(2) insert.prems(2) by fastforce 
  then have "\<forall>a\<in>F. \<exists>b1\<in>B-x. b1 \<in> a" 
    by (meson DiffI)
  have "finite (B - x)" 
    using insert.prems(1) by blast
  then obtain C where "C\<subseteq> (B - x) \<and> ( \<forall>a\<in>F. \<exists>!b. b \<in> C \<and>  b \<in> a)"
    using \<open>\<forall>a\<in>F. \<exists>b1\<in>B - x. b1 \<in> a\<close> insert.hyps(3) insert.prems(2) by fastforce
  moreover then  have "C \<union>{b} \<subseteq> B" 
    using \<open>b \<in> B \<and> b \<in> x\<close> by blast
  moreover have "\<forall>a\<in> F. \<exists>!b1. b1 \<in> C\<union>{b} \<and> b1 \<in> a" 
    using `\<forall>a\<in>F. b \<notin> a` DiffD2 calculation(1) by auto
  moreover have "\<exists>!b1. b1 \<in> C\<union>{b} \<and> b1 \<in> x" 
    using \<open>b \<in> B \<and> b \<in> x\<close> calculation(1) by blast
  ultimately show ?case 
    using `\<forall>a\<in>F. b \<notin> a` by (smt (verit, ccfv_SIG) insert_iff)
qed


lemma ex_subset_same_card:
  assumes "finite A"
  assumes "finite B"
  assumes "\<forall>a1 \<in>A. \<forall>a2\<in>A. a1 \<noteq> a2 \<longrightarrow> a1 \<inter> a2 = {}"
  assumes "\<forall>a\<in>A. \<exists>b\<in>B. b \<in> a"
  shows "\<exists>C\<subseteq>B. \<forall>a\<in>A. \<exists>b\<in>C. b \<in> a \<and> card A = card C"
  using assms
proof(induct A arbitrary: B)
  case empty
  then show ?case by auto
next
  case (insert x F)
  then obtain b where "b \<in> B \<and> b \<in> x" by auto
  then have "\<forall>a\<in>F. b \<notin> a" 
    using UnionI insert.hyps(2) insert.prems(2) by auto
  then have "\<forall>a\<in>F. \<exists>b1\<in>B. b1 \<in> a \<and> b1 \<noteq> b" 
    using insert.prems(3)
    by (metis insert_iff)
  then have "\<forall>a\<in>F. \<exists>b1\<in>B-{b}. b1 \<in> a" 
    by (metis \<open>b \<in> B \<and> b \<in> x\<close> insertE insert_Diff)
  have "finite (B - {b})" 
    using insert.prems(1) by blast
  have "\<exists>C\<subseteq>(B - {b}). \<forall>a\<in>F. \<exists>b\<in>C. b \<in> a  \<and> card F = card C"
    using \<open>\<forall>a\<in>F. \<exists>b1\<in>B - {b}. b1 \<in> a\<close> \<open>finite (B - {b})\<close> insert.hyps(3) insert.prems(2) by auto
  then  obtain C where "C \<subseteq> (B - {b}) \<and> (\<forall>a\<in>F. \<exists>b\<in>C. b \<in> a) \<and> card F = card C"
    by (metis card.empty empty_subsetI finite_has_maximal insert.hyps(1))
  moreover then  have "(C \<union> {b}) \<subseteq> B" 
    using \<open>b \<in> B \<and> b \<in> x\<close> by blast
  moreover have  "\<forall>a\<in>insert x F. \<exists>b\<in> (C \<union> {b}). b \<in> a" 
    using \<open>b \<in> B \<and> b \<in> x\<close> calculation(1) by blast
  ultimately show ?case 
    by (metis Un_insert_right \<open>finite (B - {b})\<close> card.insert insert.hyps(1) insert.hyps(2) 
        rev_finite_subset subset_Diff_insert sup_bot.right_neutral)
qed

end