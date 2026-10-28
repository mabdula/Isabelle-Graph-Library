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
    unfolding Vs_def by (rule finite_UnionD)
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
    proof -
      have "{x} \<subseteq> M"
        using insert.prems by auto
      hence "Vs {x} \<subseteq> Vs M"
        by (rule Vs_subset)
      with assms(1) show ?thesis
        by (rule rev_finite_subset)
    qed
    have "matching (insert x F)" 
      by (meson assms(2) insert.prems matching_def subset_eq)
    then have card_sum_hyp: "card (Vs F \<inter> X) = (\<Sum>e\<in>F. card (e \<inter> X))" 
      using insert.hyps(3) insert.prems by blast
    then have "\<forall>y \<in> F. x \<inter> y = {}"
    proof -
      have matching_prop: "\<forall>e1\<in>insert x F. \<forall>e2\<in>insert x F. e1 \<noteq> e2 \<longrightarrow> e1 \<inter> e2 = {}"
        using `matching (insert x F)` unfolding matching_def by simp
      show ?thesis
      proof (intro ballI)
        fix y assume hy: "y \<in> F"
        have hne: "x \<noteq> y"
          using insert.hyps(2) hy by blast
        from matching_prop have "x \<inter> y = {}"
          using hy hne by blast
        thus "x \<inter> y = {}" .
      qed
    qed
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
  proof -
    have ex_neq: "\<exists>b1\<in>B. b1 \<in> a \<and> b1 \<noteq> b" if "a \<in> F" for a
    proof -
      from that have "a \<in> insert x F" by simp
      with insert.prems(3) obtain b1 where "b1 \<in> B" and "b1 \<in> a" by blast
      have "b \<notin> a" using \<open>\<forall>a\<in>F. b \<notin> a\<close> that by blast
      then have "b1 \<noteq> b" using \<open>b1 \<in> a\<close> by auto
      then show ?thesis using \<open>b1 \<in> B\<close> \<open>b1 \<in> a\<close> by blast
    qed
    show ?thesis using ex_neq by blast
  qed
  then have "\<forall>a\<in>F. \<exists>b1\<in>B-{b}. b1 \<in> a" 
    by blast
  have "finite (B - {b})" 
    using insert.prems(1) by blast
  then  have "card F \<le> card (B - {b})" using insert.prems(2)
    using  \<open>\<forall>a\<in>F. \<exists>b1\<in>B - {b}. b1 \<in> a\<close> insert.hyps(3) 
    by auto
 then have "card F \<le> card B - 1" 
  proof -
    have "b \<in> B"
      using \<open>b \<in> B \<and> b \<in> x\<close> by simp
    then have "card (B - {b}) = card B - 1"
      by (simp add: card_Diff_singleton)
    then show ?thesis
      using \<open>card F \<le> card (B - {b})\<close> by simp
  qed
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
    by blast
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
    proof (intro ballI)
      fix a assume aF: "a \<in> F"
      then have aIns: "a \<in> insert x F" by simp
      have "\<exists>c\<in>B. c \<in> a"
        using insert.prems(3) aIns by blast
      then obtain c where cB: "c \<in> B" and ca: "c \<in> a" by blast
      have "c \<noteq> b"
        using ca aF \<open>\<forall>a\<in>F. b \<notin> a\<close> by blast
      then show "\<exists>b1\<in>B. b1 \<in> a \<and> b1 \<noteq> b"
        using cB ca by blast
    qed
  then have "\<forall>a\<in>F. \<exists>b1\<in>B-{b}. b1 \<in> a" 
  proof -
    assume hyp: "\<forall>a\<in>F. \<exists>b1\<in>B. b1 \<in> a \<and> b1 \<noteq> b"
    have "\<exists>b1\<in>B - {b}. b1 \<in> a" if "a \<in> F" for a
    proof -
      from hyp that obtain b1 where b1: "b1 \<in> B" "b1 \<in> a" "b1 \<noteq> b"
        by blast
      from b1(1) b1(3) have "b1 \<in> B - {b}"
        by simp
      with b1(2) show ?thesis ..
    qed
    then show ?thesis by blast
  qed
  have "finite (B - {b})" 
    using insert.prems(1) by blast
  have "\<exists>C\<subseteq>(B - {b}). \<forall>a\<in>F. \<exists>b\<in>C. b \<in> a  \<and> card F = card C"
    using \<open>\<forall>a\<in>F. \<exists>b1\<in>B - {b}. b1 \<in> a\<close> \<open>finite (B - {b})\<close> insert.hyps(3) insert.prems(2) by auto
  then  obtain C where "C \<subseteq> (B - {b}) \<and> (\<forall>a\<in>F. \<exists>b\<in>C. b \<in> a) \<and> card F = card C"
  proof -
    from \<open>\<exists>C\<subseteq>(B - {b}). \<forall>a\<in>F. \<exists>b\<in>C. b \<in> a \<and> card F = card C\<close>
    obtain C' where C'_sub: "C' \<subseteq> B - {b}"
      and C'_cov: "\<forall>a\<in>F. \<exists>b'\<in>C'. b' \<in> a \<and> card F = card C'"
      by blast
    show thesis
    proof (cases "F = {}")
      case True
      have "{} \<subseteq> B - {b} \<and> (\<forall>a\<in>F. \<exists>b'\<in>{}. b' \<in> a) \<and> card F = card {}"
        using True by simp
      then show thesis by (rule that)
    next
      case False
      then obtain a0 where "a0 \<in> F" by blast
      then have card_eq: "card F = card C'"
        using C'_cov by blast
      have "\<forall>a\<in>F. \<exists>b'\<in>C'. b' \<in> a"
        using C'_cov by blast
      with C'_sub card_eq
      have "C' \<subseteq> B - {b} \<and> (\<forall>a\<in>F. \<exists>b'\<in>C'. b' \<in> a) \<and> card F = card C'"
        by blast
      then show thesis by (rule that)
    qed
  qed
  moreover then  have "(C \<union> {b}) \<subseteq> B" 
    using \<open>b \<in> B \<and> b \<in> x\<close> by blast
  moreover have  "\<forall>a\<in>insert x F. \<exists>b\<in> (C \<union> {b}). b \<in> a" 
    using \<open>b \<in> B \<and> b \<in> x\<close> calculation(1) by blast
  ultimately show ?case 
  proof -
    obtain b0 where b0B: "b0 \<in> B" and b0x: "b0 \<in> x"
      using insert.prems(3) by blast
    show ?thesis
    proof (cases "F = {}")
      case True
      have "{b0} \<subseteq> B \<and>
            (\<forall>a\<in>insert x F. \<exists>b1\<in>{b0}. b1 \<in> a \<and> card (insert x F) = card {b0})"
        using True b0B b0x by auto
      then show ?thesis by blast
    next
      case False
      then obtain a0 where a0: "a0 \<in> F" by blast
      have notin: "\<forall>a\<in>F. b0 \<notin> a"
      proof (intro ballI notI)
        fix a assume aF: "a \<in> F" and b0a: "b0 \<in> a"
        have "a \<noteq> x" using aF insert.hyps(2) by blast
        then have "a \<inter> x = {}" using insert.prems(2) aF by blast
        moreover have "b0 \<in> a \<inter> x" using b0a b0x by simp
        ultimately show False by simp
      qed
      have fin': "finite (B - {b0})" using insert.prems(1) by blast
      have disj': "\<forall>a1\<in>F. \<forall>a2\<in>F. a1 \<noteq> a2 \<longrightarrow> a1 \<inter> a2 = {}"
        using insert.prems(2) by blast
      have cov': "\<forall>a\<in>F. \<exists>b1\<in>B - {b0}. b1 \<in> a"
        using insert.prems(3) notin by blast
      obtain C0 where C0sub: "C0 \<subseteq> B - {b0}"
        and C0cov: "\<forall>a\<in>F. \<exists>b1\<in>C0. b1 \<in> a \<and> card F = card C0"
        using insert.hyps(3)[OF fin' disj' cov'] by blast
      have cardFC0: "card F = card C0" using a0 C0cov by blast
      have b0C0: "b0 \<notin> C0" using C0sub by blast
      have C0B: "C0 \<subseteq> B" using C0sub by blast
      have finC0: "finite C0" using C0B insert.prems(1) by (rule finite_subset)
      have card1: "card (insert b0 C0) = Suc (card C0)"
        using finC0 b0C0 by (rule card_insert_disjoint)
      have card2: "card (insert x F) = Suc (card F)"
        using insert.hyps(1) insert.hyps(2) by (rule card_insert_disjoint)
      have cardeq: "card (insert x F) = card (insert b0 C0)"
        using card1 card2 cardFC0 by simp
      have sub: "insert b0 C0 \<subseteq> B" using b0B C0B by blast
      have cov: "\<forall>a\<in>insert x F. \<exists>b1\<in>insert b0 C0. b1 \<in> a"
        using b0x C0cov by blast
      have "insert b0 C0 \<subseteq> B \<and>
            (\<forall>a\<in>insert x F. \<exists>b1\<in>insert b0 C0. b1 \<in> a \<and>
               card (insert x F) = card (insert b0 C0))"
        using sub cov cardeq by blast
      then show ?thesis by blast
    qed
  qed
qed

end
