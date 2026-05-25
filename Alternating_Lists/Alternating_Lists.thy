theory Alternating_Lists
imports Undirected_Set_Graphs.Undirected_Set_Graphs
begin


subsection\<open>Alternating lists and auxilliary theory about them\<close>

text\<open>Alternating lists are lists whose members alternate in satisfying two given predicates. Their
     main application in matching is that augmenting paths are laternating lists.\<close>

inductive alt_list where
"alt_list P1 P2 []" |
"P1 x \<Longrightarrow> alt_list P2 P1 l \<Longrightarrow> alt_list P1 P2 (x#l)"

lemma alt_list_singleton: "P1 x \<Longrightarrow> alt_list P1 P2 [x]"
  by(auto intro!: alt_list.intros)

inductive_simps alt_list_empty: "alt_list P1 P2 []"
inductive_simps alt_list_step: "alt_list P1 P2 (x#l)"

lemma induct_alt_list012[consumes 1, case_names nil single sucsuc]:
  assumes "alt_list P1 P2 l"
  assumes "T []"
  assumes "\<And>x. P1 x \<Longrightarrow> T [x]"
  assumes "\<And>x y zs. P1 x \<Longrightarrow> P2 y \<Longrightarrow> T zs \<Longrightarrow> T (x#y#zs)"
  shows "T l"
  using assms(1)
proof(induction l rule: induct_list012)
  case nil thus ?case using assms(2) by simp
next
  case (single x) thus ?case
    by (simp add: alt_list_step assms(3))
next
  case (sucsuc x y zs)
  thus ?case
    by (simp add: alt_list_step assms(4))
qed

lemma induct_pcpl_2:
  "\<lbrakk>P []; \<And>x. P [x]; \<And>x y. P [x,y]; \<And>x y z. P [x,y,z]; \<And>w x y z zs. P zs \<Longrightarrow> P (w # x # y # z # zs)\<rbrakk> \<Longrightarrow> P xs"
  by induction_schema (pat_completeness, lexicographic_order)

lemma alternating_length:
  assumes "\<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x"
  shows "length l = length (filter P1 l) + length (filter P2 l)"
  using assms by (induction l) auto

lemma alternating_length_balanced:
  assumes "alt_list P1 P2 l" "\<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x"
  shows "length (filter P1 l) = length (filter P2 l) \<or>
         length (filter P1 l) = length (filter P2 l) + 1"
  using assms by (induction l) auto

lemma alternating_eq_iff_even:
  assumes "alt_list P1 P2 l" "\<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x"
  shows "length (filter P1 l) = length (filter P2 l) \<longleftrightarrow> even (length l)"
proof
  assume "length (filter P1 l) = length (filter P2 l)"
  thus "even (length l)" using assms alternating_length by force
next
  assume "even (length l)"
  thus "length (filter P1 l) = length (filter P2 l)"
    using alternating_length_balanced[OF assms] alternating_length[OF assms(2)]
    by auto
qed

lemma alternating_eq_iff_odd:
  assumes "alt_list P1 P2 l" "\<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x"
  shows "length (filter P1 l) = length (filter P2 l) + 1 \<longleftrightarrow> odd (length l)"
proof
  assume "length (filter P1 l) = length (filter P2 l) + 1"
  thus "odd (length l)" using assms alternating_length by force
next
  assume "odd (length l)"
  thus "length (filter P1 l) = length (filter P2 l) + 1"
    using assms alternating_length_balanced alternating_eq_iff_even by blast
qed

lemma alternating_list_odd_index:
  assumes "alt_list P1 P2 l" "odd n" "n < length l"
  shows "P2 (l ! n)"
  using assms                                  
proof(induction arbitrary: n rule: induct_alt_list012)
  case (sucsuc x y zs)
  consider (l) "n = 1" | (h) "n \<ge> 2" using odd_pos sucsuc.prems(1) by fastforce
  thus ?case
  proof cases
    case l thus ?thesis by (simp add: sucsuc.hyps(2))
  next
    case h
    then obtain m where "n = Suc (Suc m)" using add_2_eq_Suc le_Suc_ex by blast
    hence "P2 (zs ! m)" using sucsuc.IH sucsuc.prems(1, 2) by fastforce
    thus ?thesis by (simp add: \<open>n = Suc (Suc m)\<close>)
  qed
qed simp_all

lemma alternating_list_even_index:
  assumes "alt_list P1 P2 l" "even n" "n < length l"
  shows "P1 (l ! n)"
  using assms
proof(induction arbitrary: n rule: induct_alt_list012)
  case (sucsuc x y zs)
  consider (l) "n = 0" | (h) "n \<ge> 2" using odd_pos sucsuc.prems(1) by fastforce
  thus ?case
  proof cases
    case l thus ?thesis by (simp add: sucsuc.hyps(1))
  next
    case h
    then obtain m where "n = Suc (Suc m)" using add_2_eq_Suc le_Suc_ex by blast
    hence "P1 (zs ! m)" using sucsuc.IH sucsuc.prems(1, 2) by fastforce
    thus ?thesis by (simp add: \<open>n = Suc (Suc m)\<close>)
  qed
qed simp_all

lemma alternating_list_even_last:
  assumes "alt_list P1 P2 l" "even (length l)" "l \<noteq> []"
  shows "P2 (last l)"
proof-
  have "odd (length l - 1)" by (simp add: assms(2) assms(3))
  hence "P2 (l ! (length l - 1))" 
    by(auto intro: alternating_list_odd_index[OF assms(1)])
  thus ?thesis using assms(3) by (simp add: last_conv_nth)
qed

lemma alternating_list_odd_last:
  assumes "alt_list P1 P2 l" "odd (length l)"
  shows "P1 (last l)"
proof-
  have "even (length l - 1)" by (simp add: assms(2))
  hence "P1 (l ! (length l - 1))" using alternating_list_even_index
    using assms(1) assms(2) odd_pos by fastforce
  thus ?thesis using assms(2) last_conv_nth odd_pos by force
qed

lemma alternating_list_gt_odd:
  assumes "length (filter P1 l) > length (filter P2 l)"
  assumes "alt_list P1 P2 l"
  assumes "\<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x"
  shows "odd (length l)"
  using assms alternating_eq_iff_even by fastforce

lemma alternating_list_eq_even:
  assumes "length (filter P1 l) = length (filter P2 l)"
  assumes "alt_list P1 P2 l" (* not actually used but complements gt_odd *)
  assumes "\<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x"
  shows "even (length l)"
  using assms alternating_eq_iff_even by fastforce

lemma alternating_list_eq_last':
  "\<lbrakk>length (filter P1 l) = length (filter P2 l); \<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x; l \<noteq> []; P2 (last l)\<rbrakk>
    \<Longrightarrow> \<not> alt_list P2 P1 l"
  using alternating_eq_iff_even alternating_list_even_last last_in_set
  by fastforce

lemma gt_zero:"x < (y::nat) \<Longrightarrow> 0 < y"
  by auto

lemma alternating_list_gt:
  "\<lbrakk>length (filter P1 l) > length (filter P2 l); \<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x; alt_list P1 P2 l\<rbrakk> \<Longrightarrow>
    P1 (hd l) \<and> P1 (last l)"
  apply(intro conjI)
  subgoal by (fastforce  simp: neq_Nil_conv alt_list_step dest: gt_zero order.strict_trans2[OF _ length_filter_le])
  subgoal using alternating_list_odd_last alternating_list_gt_odd
    by fastforce
  done

lemma alt_list_not_commute:
  assumes "alt_list P1 P2 l"
          "\<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x"
          "l \<noteq> []"
    shows "\<not> alt_list P2 P1 l"
  using assms
  by(auto simp add: neq_Nil_conv alt_list_step)

lemma alternating_list_gt_or:
  assumes "length (filter P1 l) > length (filter P2 l)"
          "\<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x"
    shows "\<not> alt_list P2 P1 l"
  using alternating_length_balanced assms by fastforce

lemma alt_list_cong_1:
  assumes "alt_list P1 P2 l" "\<forall>x \<in> set l. P2 x \<longrightarrow> P3 x"
  shows "alt_list P1 P3 l"
  using assms
  by (induction rule: induct_alt_list012)
     (simp_all add: alt_list_empty alt_list_step)

lemma alt_list_cong_2:
  assumes "alt_list P1 P2 l" "\<And>x. \<lbrakk>x \<in> set l; P1 x\<rbrakk> \<Longrightarrow> P3 x"
  shows "alt_list P3 P2 l"
  using assms
  by (induction rule: induct_alt_list012)
     (simp_all add: alt_list_empty alt_list_step)

lemma alt_list_cong:
  assumes "alt_list P1 P2 l" "\<forall>x \<in> set l. P1 x \<longrightarrow> P3 x" "\<forall>x \<in> set l. P2 x \<longrightarrow> P4 x"
  shows "alt_list P3 P4 l"
  using assms
  by (induction rule: induct_alt_list012)
     (simp_all add: alt_list_empty alt_list_step)

lemma alt_list_append_1:
  assumes "alt_list P1 P2 (l1 @ l2)"
  shows "alt_list P1 P2 l1  \<and> (alt_list P1 P2 l2 \<or> alt_list P2 P1 l2)"
  using assms
  by (induction l1 rule: induct_list012)
     (simp_all add: alt_list_empty alt_list_step)

lemma alt_list_append_2:
  assumes "alt_list P1 P2 l1" "alt_list P2 P1 l2" "odd (length l1)"
  shows "alt_list P1 P2 (l1 @ l2)"
  using assms
proof (induction l1 rule: induct_list012)
  case (sucsuc x y zs)
  thus ?case
    by (auto simp: alt_list_step)
qed (simp_all add: alt_list_step)


lemma alt_list_append_3:
  assumes "alt_list P1 P2 l1" "alt_list P1 P2 l2" "even (length l1)"
  shows "alt_list P1 P2 (l1 @ l2)"
  using assms
proof (induction l1 rule: induct_list012)
  case (sucsuc x y zs)
  thus ?case
    by (auto simp: alt_list_step)
qed (simp_all add: alt_list_step)

lemma alt_list_split_1:
  assumes "alt_list P1 P2 (l1 @ l2)" "even (length l1)"
  shows "alt_list P1 P2 l2"
  using assms
  by (induction l1 rule: induct_list012)
     (simp_all add: alt_list_step)

lemma alt_list_split_2:
  assumes "alt_list P1 P2 (l1 @ l2)" "odd (length l1)"
  shows "alt_list P2 P1 l2"
  using assms
  by (induction l1 rule: induct_list012)
     (simp_all add: alt_list_step)

lemma alt_list_append_1':
  assumes "alt_list P1 P2 (l1 @ l2)" "l1 \<noteq> []" "\<And>x. x\<in>set l1 \<Longrightarrow> P1 x = (\<not> P2 x)"
  shows "(alt_list P1 P2 l1  \<and> ((P2 (last l1) \<and> alt_list P1 P2 l2) \<or> (P1 (last l1) \<and> alt_list P2 P1 l2)))"
proof(cases "alt_list P2 P1 l2")
  case True
  then show ?thesis
    using assms[unfolded neq_Nil_conv] alt_list_append_1[OF assms(1)]
    by (force simp add: alt_list_step dest!: alt_list_split_2 alternating_list_even_last)
next
  case False
  then show ?thesis
    using assms[unfolded neq_Nil_conv] alt_list_append_1[OF assms(1)]
    by (force simp add: alt_list_step dest: alt_list_split_1 alternating_list_odd_last)
qed

lemma alt_list_rev_even:
  assumes "alt_list P1 P2 l" "even (length l)"
  shows "alt_list P2 P1 (rev l)"
  using assms
proof(induction rule: induct_alt_list012)
  case (sucsuc x y zs)
  hence "alt_list P2 P1 (rev zs)" by simp
  moreover have "alt_list P2 P1 [y, x]"
    by (simp add: alt_list_empty alt_list_step sucsuc.hyps(1) sucsuc.hyps(2))
  ultimately have "alt_list P2 P1 (rev zs @ [y, x])"
    using alt_list_append_3 sucsuc.prems by fastforce
  thus ?case by simp
qed (simp_all add: alt_list_empty)

lemma alt_list_rev:
  assumes "alt_list P1 P2 l" "odd (length l)"
  shows "alt_list P1 P2 (rev l)" 
  using assms
proof-
  obtain x zs where "l = x # zs" using assms(2) by (cases l, fastforce+)
  hence "alt_list P1 P2 (rev zs)"using assms
    by (auto intro!: alt_list_rev_even simp: alt_list_step) 
  moreover have "alt_list P1 P2 [x]"
    using assms(1)[simplified \<open>l = x # zs\<close>]
    by (auto simp: alt_list_empty alt_list_step )
  ultimately show ?thesis using alt_list_append_3 \<open>l = x # zs\<close> assms(2) by fastforce
qed


(******)

lemma alternating_list_eq_last:
  "\<lbrakk>length (filter P1 l) = length (filter (\<lambda>x. P2 x) l); alt_list P1 P2 l; l \<noteq> [];
    \<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x\<rbrakk> \<Longrightarrow> P2 (last l)"
  using alternating_list_eq_even alternating_list_even_last
  by blast

lemmas alternating_list_gt_last = conjunct2[OF alternating_list_gt(1)]

lemma alternating_list_eq_last'':
  "\<lbrakk>length (filter P1 l) = length (filter (\<lambda>x. P2 x) l); alt_list P1 P2 l \<or> alt_list P2 P1 l;
    l \<noteq> []; \<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x; P2 (last l)\<rbrakk>
     \<Longrightarrow> alt_list P1 P2 l"
  using alternating_list_eq_last'
  by blast

lemma alternating_list_gt_or':
  "\<lbrakk>length (filter P1 l) > length (filter (\<lambda>x. P2 x) l); alt_list P1 P2 l \<or> alt_list P2 P1 l;
    \<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x\<rbrakk>
    \<Longrightarrow> alt_list P1 P2 l"
  using alternating_list_gt_or by blast

lemma alt_list_cong_1':
  "\<lbrakk>alt_list P1 P2 l; \<forall>x \<in> set l. P2 x = P3 x\<rbrakk> \<Longrightarrow> alt_list P1 P3 l"
  by(auto intro: alt_list_cong)

lemma alt_list_cong_2':
  "\<lbrakk>alt_list P1 P2 l; \<forall>x \<in> set l. P1 x = P3 x\<rbrakk> \<Longrightarrow> alt_list P3 P2 l"
  by(auto intro: alt_list_cong)

lemma alt_list_cong':
  "\<lbrakk>alt_list P1 P2 l; \<forall>x \<in> set l. P1 x = P3 x; \<forall>x \<in> set l. P2 x = P4 x\<rbrakk> \<Longrightarrow> alt_list P3 P4 l"
  using alt_list_cong
  by fastforce

lemma alt_list_cong_eq:
  "\<lbrakk>\<forall>x \<in> set l. P1 x = P3 x; \<forall>x \<in> set l. P2 x = P4 x\<rbrakk> \<Longrightarrow> alt_list P1 P2 l = alt_list P3 P4 l"
  using alt_list_cong_1 alt_list_cong_2
  by metis

lemma alt_list_append_2':
  "\<lbrakk>alt_list P1 P2 l1; alt_list P2 P1 l2; l1 \<noteq> []; P1 (last l1); \<forall>x\<in>set l1. P1 x = (\<not> P2 x)\<rbrakk>
     \<Longrightarrow> alt_list P1 P2 (l1 @ l2)"
  using alt_list_append_2 alternating_list_even_last last_in_set
  by blast

lemma alt_list_append_3':
  "\<lbrakk>alt_list P1 P2 l1; alt_list P1 P2 l2; l1 \<noteq> [] \<longrightarrow> P2 (last l1); \<forall>x\<in>set l1. P1 x = (\<not> P2 x)\<rbrakk>
    \<Longrightarrow> alt_list P1 P2 (l1 @ l2)"
  using alt_list_append_3
  by (metis alternating_list_odd_last append_Nil last_in_set)

lemma alt_list_append_1'':
  "\<lbrakk>alt_list P1 P2 (l1 @ a # a' # l2); \<forall>x\<in> {a, a'}. P1 x = (\<not> P2 x); P1 a\<rbrakk> \<Longrightarrow>
     P2 a'"
  by (metis alt_list_append_1 alt_list_step insert_iff)

lemma alt_list_append_1''':
  "\<lbrakk>alt_list P1 P2 (l1 @ a # a' # l2); \<forall>x\<in> {a, a'}. P1 x = (\<not> P2 x); P1 a'\<rbrakk> \<Longrightarrow> P2 a"
  by (metis alt_list_append_1'' insertCI)

lemma alt_list_append_1'''':
  "\<lbrakk>alt_list P1 P2 (l1 @ a # a' # l2); \<forall>x\<in> {a, a'}. P1 x = (\<not> P2 x); P2 a'\<rbrakk> \<Longrightarrow> P1 a"
  by (metis alt_list_append_1 alt_list_step insertCI)

lemma alt_list_append_1''''':
  "\<lbrakk>alt_list P1 P2 (l1 @ a # a' # l2); \<forall>x\<in> {a, a'}. P1 x = (\<not> P2 x); P2 a\<rbrakk> \<Longrightarrow> P1 a'"
  by (metis alt_list_append_1'''' insertCI)

lemma alt_list_rev':
  "\<lbrakk>P1 (last l); \<forall>x\<in>set l. P1 x = (\<not> P2 x); alt_list P1 P2 l\<rbrakk> \<Longrightarrow> alt_list P1 P2 (rev l)" 
  by (metis Nil_is_rev_conv alt_list_rev alternating_list_even_last last_in_set)

lemma alt_list_rev_2:
  "\<lbrakk>P2 (last l); \<forall>x\<in>set l. P1 x = (\<not> P2 x); alt_list P1 P2 l\<rbrakk> \<Longrightarrow> alt_list P2 P1 (rev l)" 
  by (metis alt_list_rev_even alternating_list_odd_last dvd_0_right last_in_set list.size(3))


lemma alternating_eq_even_2:
  (* For some reason this has the same proof as alternating_list_eq_last. *)
  "\<lbrakk>alt_list P1 P2 l; even (length l); \<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x\<rbrakk> \<Longrightarrow> 
    length (filter P1 l) = length (filter P2 l)"
  using alternating_eq_iff_even by blast
                                         
lemmas last_even_P2 = alternating_list_even_last

lemma alternating_eq_even':
  "\<lbrakk>alt_list P1 P2 l; odd (length l); \<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x\<rbrakk> \<Longrightarrow> 
     length (filter P1 l) \<noteq> length (filter P2 l)"
  using alternating_list_eq_even by blast  

lemma last_odd_P1':
  "\<lbrakk>alt_list P1 P2 l; P1 (last l); \<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x; l \<noteq> []\<rbrakk> \<Longrightarrow> odd (length l)"
  using last_even_P2
  by auto

lemma alternating_gt_odd:
  "\<lbrakk>alt_list P1 P2 l; odd (length l); \<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x; l \<noteq> []\<rbrakk>
     \<Longrightarrow> length (filter P1 l) > length (filter P2 l)"
  using alternating_eq_iff_even alternating_list_gt_or linorder_neqE_nat by blast

lemma alt_list_append_end:
  "\<lbrakk>alt_list P1 P2 l; P1 (last l); P2 a; l \<noteq> []; \<forall>x\<in>set l. P1 x = (\<not> P2 x)\<rbrakk>
     \<Longrightarrow> alt_list P1 P2 (l @ [a])"
  by (simp add: alt_list.intros(1) alt_list.intros(2) alt_list_append_2')

lemma alt_list_or:
  "alt_list P1 P2 vs \<Longrightarrow> v \<in> set vs \<Longrightarrow> P1 v \<or> P2 v"
proof(induction vs rule: induct_list012)
  case nil
  then show ?case
    by auto
next
  case (single x)
  then show ?case
    by (auto simp add: alt_list_step alt_list_empty)
next
  case (sucsuc x y zs)
  then show ?case
    by (auto simp add: alt_list_step alt_list_empty)
qed

lemma alt_list_distinct:
  assumes "alt_list P Q xs"
  assumes "distinct [x <- xs. P x]"
  assumes "distinct [x <- xs. Q x]"
  assumes "\<forall>x. \<not>(P x \<and> Q x)"
  shows "distinct xs"
  using assms
  by (induction xs rule: induct_alt_list012)
     (auto split: if_splits)

lemma alt_list_adjacent:
     "alt_list P Q (xs@[x,y]@ys) \<Longrightarrow> (P x \<and> Q y) \<or> (Q x \<and> P y)"
  by (metis alt_list_append_1 alt_list_step)

lemma alt_list_split_off_first_two:
  "alt_list P Q (x#y#xs) \<Longrightarrow> alt_list P Q xs"
  by (simp add: alt_list_step)

lemma alt_list_from_indices:
  assumes "\<And> i. \<lbrakk>i < length p; even i\<rbrakk> \<Longrightarrow> P1 (p!i) "
          "\<And> i. \<lbrakk>i < length p; odd i\<rbrakk> \<Longrightarrow> P2 (p!i) "
    shows "alt_list P1 P2 p"
  using assms
proof(induction p arbitrary: P1 P2)
  case Nil
  then show ?case
    by (auto intro!: alt_list.intros)
next
  case (Cons a p)
  have "alt_list P2 P1 p"
  proof(rule Cons(1), goal_cases)
    case (1 i)
    then show ?case 
      using Cons(2,3)
      by(cases i) fastforce+
  next
    case (2 i)
    then show ?case 
      using Cons(2,3)
      by(cases i) fastforce+
  qed
  thus ?case
    using Cons.prems(1)
    by(force intro!: alt_list.intros)
qed

end