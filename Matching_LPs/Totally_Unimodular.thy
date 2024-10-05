theory Totally_Unimodular
  imports
    Integer_Polyhedron
    Integer_hull_f_to_a
begin

context gram_schmidt_floor
begin

definition tot_unimodular where
  "tot_unimodular A = (\<forall> B. (\<exists> I J. submatrix A I J = B) \<longrightarrow> det B \<in> {-1, 0, 1})"

definition pos_polyhedron where 
  "pos_polyhedron A b = {x. x \<in> carrier_vec n \<and> A *\<^sub>v x \<le> b \<and> x \<ge> 0\<^sub>v n}"

definition int_polyh where
  "int_polyh P = (integer_hull P = P)" 

(*
lemma tot_unimod_entries:
  assumes "tot_unimodular A"
  shows "elements_mat A \<subseteq> {-1, 0, 1}"
  sorry
*)

lemma pos_polyh_is_polyh:
  fixes A :: "'a  mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes "b \<in> carrier_vec nr"
  shows "pos_polyhedron A b = polyhedron (A @\<^sub>r - 1\<^sub>m n) (b @\<^sub>v 0\<^sub>v n)"
proof -
  have "{x. x \<in> carrier_vec n \<and> A *\<^sub>v x \<le> b \<and> x \<ge> 0\<^sub>v n} = 
        {x. x \<in> carrier_vec n \<and> (A @\<^sub>r - 1\<^sub>m n) *\<^sub>v x \<le> (b @\<^sub>v 0\<^sub>v n)}"
  proof safe
    have carr_mone:"- 1\<^sub>m n \<in> carrier_mat n n"
      by simp
    {   fix x
      assume asm: " A *\<^sub>v x \<le> b" "0\<^sub>v n \<le> x " "x \<in> carrier_vec n"
      then have " \<forall> i < n. x $ i \<ge> 0\<^sub>v n $ i" 
        by (metis Matrix.less_eq_vec_def carrier_vecD)
      then have "\<forall> i < n. x $ i \<ge> 0"
        using asm(2) unfolding zero_vec_def using index_vec[of _ n "(\<lambda>i. 0)"] 
        by simp
      then have "\<forall> i < n. unit_vec n i \<bullet> x \<ge> 0 "
        by (metis M.zero_closed Matrix.less_eq_vec_def asm(2) carrier_dim_vec scalar_prod_left_unit)
      then have "\<forall> i < n. - unit_vec n i \<bullet> x \<le> 0" 
        by (metis M.add.one_closed Matrix.less_eq_vec_def asm(2) carrier_vecD index_unit_vec(3) 
            minus_equation_iff neg_0_le_iff_le scalar_prod_uminus_left)
      then have "\<forall> i < n. row (- 1\<^sub>m n) i \<bullet> x \<le> 0" 
        by simp
      then have "(- 1\<^sub>m n) *\<^sub>v x \<le> 0\<^sub>v n" 
        by (simp add: Matrix.less_eq_vec_def)
      then show "(A @\<^sub>r - 1\<^sub>m n) *\<^sub>v x  \<le> b @\<^sub>v 0\<^sub>v n" using asm(1)
          append_rows_le[OF A carr_mone]
        using asm(3) assms(2) by presburger
    }
    fix x
    assume asm:"(A @\<^sub>r - 1\<^sub>m n) *\<^sub>v x \<le> b @\<^sub>v 0\<^sub>v n" "x \<in> carrier_vec n"
    show "A *\<^sub>v x \<le> b" using asm append_rows_le[OF A carr_mone]
      using assms(2) by blast
    have "(- 1\<^sub>m n) *\<^sub>v x \<le> 0\<^sub>v n" 
      using A append_rows_le asm(1) asm(2) assms(2) carr_mone by blast
    then have "\<forall> i < n. row (- 1\<^sub>m n) i \<bullet> x \<le> 0" 
      unfolding less_eq_vec_def
      by simp
    then have "\<forall> i < n. unit_vec n i \<bullet> x \<ge> 0 " 
      using asm(2) by force
    then have "\<forall> i < n. x $ i \<ge> 0" 
      by (simp add: asm(2))
    then show "0\<^sub>v n \<le> x" 
      by (metis M.add.one_closed asm(2) index_zero_vec(1) lesseq_vecI)
  qed
  then show ?thesis unfolding pos_polyhedron_def polyhedron_def by auto
qed

lemma pick_card_of_elem_ge_elem:
  assumes "card {i. i < k \<and> i \<in> I} < card I \<or> infinite I"
  shows "pick I (card {i. i < k \<and> i \<in> I}) \<ge> k"
proof -
  have 1:"pick I (card {a \<in> I. a < k}) = (LEAST a. a \<in> I \<and> k \<le> a)"
    using pick_card by blast
  have 2:"pick I (card {a \<in> I. a < k}) \<in> I" 
    by (metis (no_types, lifting) Collect_cong assms pick_in_set_inf pick_in_set_le)
  have "(LEAST a. a \<in> I \<and> k \<le> a) \<in> I" 
    using 1 2 by presburger
  have "(LEAST a. a \<in> I \<and> k \<le> a) \<ge> k"
  proof (rule ccontr)
    assume "\<not> k \<le> (LEAST a. a \<in> I \<and> k \<le> a)"
    then  have " k > (LEAST a. a \<in> I \<and> k \<le> a)" 
      by linarith
    have "\<exists> t. t \<in> I \<and> t \<ge> k"
    proof(rule ccontr)
      assume asm:"\<nexists>t. t \<in> I \<and> k \<le> t"
      then have "finite I" 
        by (meson infinite_nat_iff_unbounded_le)
      have 3:"card {i. i < k \<and> i \<in> I} < card I"
        using \<open>finite I\<close> assms by blast
      have "card {a\<in>I. a < pick I (card {i. i < k \<and> i \<in> I})} = card {i. i < k \<and> i \<in> I}"
        using \<open>card {i. i < k \<and> i \<in> I} < card I\<close> card_pick by blast
      then show False 
        by (metis (mono_tags, lifting) Collect_cong Collect_mem_eq asm 3 not_less order.refl)
    qed
    then obtain t where "t \<in> I \<and> t \<ge> k" by auto
    then show False using LeastI[of "\<lambda> a. a \<in> I \<and> k \<le> a" t] 
      using \<open>\<not> k \<le> (LEAST a. a \<in> I \<and> k \<le> a)\<close> by presburger
  qed
  then show ?thesis
    by (simp add: 1 set_le_in)
qed

lemma pick_suc_diff_set:
  assumes "Suc j < card J \<or> infinite J"
  shows "pick J (Suc j) = pick (J - {pick J j}) j" 
proof(cases "infinite J")
  case True
  have "pick J (Suc j) > pick J j" 
    using True pick_mono_le 
    using lessI pick_mono by presburger
  have "pick J (Suc j) \<in> J - {pick J j}" 
    by (metis Diff_iff True \<open>pick J j < pick J (Suc j)\<close> nat_neq_iff pick_in_set_inf singletonD)
  then have 1: "pick (J - {pick J j}) (card {a\<in>(J - {pick J j}). a < pick J (Suc j)}) = 
                pick J (Suc j)"
    using pick_card_in_set 
    by presburger
  have 2:"{a\<in>(J - {pick J j}). a < pick J (Suc j)} \<union> {pick J j} = {a\<in>J. a < pick J (Suc j)}"
    apply safe 
     apply (simp add: True pick_in_set)
    using \<open>pick J j < pick J (Suc j)\<close> by blast
  have "pick J j \<notin> {a\<in>(J - {pick J j}). a < pick J (Suc j)}"
    by blast
  have "card {a\<in>J. a < pick J (Suc j)} = (Suc j)" 
    using True card_pick by blast
  have "card ({a\<in>(J - {pick J j}). a < pick J (Suc j)} \<union> {pick J j}) = 
        card {a\<in>(J - {pick J j}). a < pick J (Suc j)} + card {pick J j}"
    by force
  then have "card {a\<in>(J - {pick J j}). a < pick J (Suc j)} + 1 = card {a\<in>J. a < pick J (Suc j)}"
    by (metis 2 card_eq_1_iff)
  then have "card {a\<in>(J - {pick J j}). a < pick J (Suc j)} = (Suc j) - 1" 
    using \<open>card {a \<in> J. a < pick J (Suc j)} = (Suc j)\<close> by presburger
  then have "pick (J - {pick J j}) ((Suc j) - 1) = pick J (Suc j)" 
    using 1 by presburger
  then show ?thesis 
    by (metis diff_Suc_1)
next
  case False
  have "Suc j < card J" 
    using False assms by force
  have 3:"pick J (Suc j) > pick J j" 
    using \<open>Suc j < card J\<close> pick_mono_le by blast
  have "pick J (Suc j) \<in> J - {pick J j}" 
    by (metis Diff_iff False 3 assms nat_neq_iff pick_in_set_le singletonD)
  then have 1: "pick (J - {pick J j}) (card {a\<in>(J - {pick J j}). a < pick J (Suc j)}) =
                pick J (Suc j)"
    using pick_card_in_set 
    by presburger
  have 2:"{a\<in>(J - {pick J j}). a < pick J (Suc j)} \<union> {pick J j} = {a\<in>J. a < pick J (Suc j)}"
    apply safe
     apply (simp add: Suc_lessD \<open>Suc j < card J\<close> pick_in_set_le)
    using \<open>pick J j < pick J (Suc j)\<close> by blast
  have "pick J j \<notin> {a\<in>(J - {pick J j}). a < pick J (Suc j)}"
    by blast
  have "card {a\<in>J. a < pick J (Suc j)} = (Suc j)" 
    using \<open>Suc j < card J\<close> card_pick by presburger
  have "card ({a\<in>(J - {pick J j}). a < pick J (Suc j)} \<union> {pick J j}) = 
        card {a\<in>(J - {pick J j}). a < pick J (Suc j)} + card {pick J j}"
    by force
  then have "card {a\<in>(J - {pick J j}). a < pick J (Suc j)} + 1 = card {a\<in>J. a < pick J (Suc j)}"
    by (metis 2 card_eq_1_iff)
  then have "card {a\<in>(J - {pick J j}). a < pick J (Suc j)} = (Suc j) - 1" 
    using \<open>card {a \<in> J. a < pick J (Suc j)} = (Suc j)\<close> by presburger
  then have "pick (J - {pick J j}) ((Suc j) - 1) = pick J (Suc j)"
    using 1 by presburger
  then show ?thesis 
    by (metis diff_Suc_1)
qed

lemma pick_same_if_less:
  assumes "j < card J \<or> infinite J"
  assumes "k < j"
  shows "pick (J - {pick J j}) k = pick J k"
proof -
  have 1: "k < card J \<or> infinite J" using assms by auto
  have "pick J (insert_index j k) = pick J k" unfolding insert_index_def 
    using assms(2) 
    by simp
  have "pick J k < pick J j" 
    using pick_mono
    using assms(2) assms(1) by blast    
  then have "pick J k \<in> J - {pick J j}" using pick_in_set[OF assms(1)]
    by (metis Diff_iff 1 nat_neq_iff pick_in_set singletonD)
  then have 2: "pick (J - {pick J j}) (card {a\<in>(J - {pick J j}). a < pick J k}) = pick J k" 
    using pick_card_in_set 
    by presburger
  have 3:"card {a\<in>J. a < pick J k} = k" 
    using 1 card_pick by blast
  have "pick J k < pick J j" 
    using \<open>pick J k < pick J j\<close> by blast
  then  have "{a\<in>J. a < pick J k} = {a\<in>(J - {pick J j}). a < pick J k}"
    by auto
  then show "pick (J - {pick J j}) k = pick J k" 
    using 3 2 by presburger
qed

lemma pick_is_Suc_if_one_removed:
  assumes "k < card J \<or> infinite J"
  assumes "j < k"
  shows "pick (J - {pick J j}) k = pick J (Suc k)"
proof -
  have "pick J k > pick J j" 
    using assms(1) assms(2) pick_mono by blast
  have "pick J k \<in> J - {pick J j}" 
    by (metis Diff_iff \<open>pick J j < pick J k\<close> assms(1) nat_neq_iff pick_in_set singletonD)
  then have 1: "pick (J - {pick J j}) (card {a\<in>(J - {pick J j}). a < pick J k}) = pick J k"
    using pick_card_in_set 
    by presburger
  have 2:"{a\<in>(J - {pick J j}). a < pick J k} \<union> {pick J j} = {a\<in>J. a < pick J k}"
    apply safe
    using assms(1) assms(2) basic_trans_rules(19) pick_in_set apply blast
    by (simp add: \<open>pick J j < pick J k\<close>)
  have "pick J j \<notin> {a\<in>(J - {pick J j}). a < pick J k}"
    by blast
  have "card {a\<in>J. a < pick J k} = k" 
    using assms(1) card_pick by blast
  have "card ({a\<in>(J - {pick J j}). a < pick J k} \<union> {pick J j}) = 
        card {a\<in>(J - {pick J j}). a < pick J k} + card {pick J j}"
    by force
  then have 4: "card {a\<in>(J - {pick J j}). a < pick J k} + 1 = card {a\<in>J. a < pick J k}"
    by (metis 2 card_eq_1_iff)
  then have 5:"card {a\<in>(J - {pick J j}). a < pick J k} = k - 1" 
    using \<open>card {a \<in> J. a < pick J k} = k\<close> by presburger
  then have 3:"pick (J - {pick J j}) (k - 1) = pick J k" using 1 
    by presburger
  have 6:"pick (J - {pick J j}) (Suc (k - 1)) = 
        (LEAST a. a \<in> (J - {pick J j}) \<and> pick (J - {pick J j}) (k - 1) < a)" 
    using DL_Missing_Sublist.pick.simps(2) by blast
  have 7:"pick J (Suc k) = (LEAST a. a \<in> J \<and> pick J k < a)"
    using DL_Missing_Sublist.pick.simps(2) by blast
  have "(LEAST a. a \<in> (J - {pick J j}) \<and> pick (J - {pick J j}) (k - 1) < a) = 
              (LEAST a. a \<in> J \<and> pick J k < a)" 
    by (metis Diff_iff 3 \<open>pick J j < pick J k\<close> basic_trans_rules(19) less_not_refl2 singletonD)
  then show "pick (J - {pick J j}) k = pick J (Suc k)" 
    by (metis Suc_eq_plus1 4 5 \<open>card {a \<in> J. a < pick J k} = k\<close> 6 7)
qed

lemma pick_is_Suc_if_one_removed':
  assumes "Suc i < card I \<or> infinite I"
  assumes "card {i. i < k \<and> i \<in> I} \<le> i" 
  assumes "k \<in> I"
  shows "pick (I - {k}) i  = pick I (Suc i)"
proof - 
  let ?j = "(card {a \<in> I. a < k})"
  have 1:"pick I ?j = k" using pick_card_in_set 
    using assms(3) by presburger
  have "{a \<in> I. a < k} \<union> {k} = {i. i < Suc k \<and> i \<in> I}" 
    apply safe 
      apply linarith
    using assms(3) less_SucE by blast+
  then have "{a \<in> I. a < k} \<subset> {i. i < Suc k \<and> i \<in> I}" 
    by force
  then have "?j < card {i. i < Suc k \<and> i \<in> I}" 
    by (simp add: psubset_card_mono)
  then have "?j \<le> i" 
    using assms(2) basic_trans_rules(22) 
    by (smt (verit, best) Collect_cong)
  then show ?thesis 
  proof(cases "?j = i")
    case True
    have "pick I (Suc i) = pick (I - {pick I i}) i" 
      using pick_suc_diff_set[OF assms(1)] by auto
    then show ?thesis 
      by (metis (no_types, lifting) Suc_lessD \<open>?j \<le> i\<close> 1 assms(1) le_neq_implies_less 
          pick_is_Suc_if_one_removed)
  next
    case False
    then show ?thesis 
      using pick_is_Suc_if_one_removed[of i I ?j] False 
      by (metis Suc_lessD \<open>?j \<le> i\<close> 1 assms(1) le_neq_implies_less)
  qed
qed

lemma pick_remove_elem_set_Suc_same:
  assumes "i  < card I \<or> infinite I"
  assumes "card {i. i < Suc k \<and> i \<in> I} \<le> i" 
  shows "pick (I - {i. i < Suc k \<and> i \<in> I}) (i - card {i. i < Suc k \<and> i \<in> I}) =
    pick (I - {i. i < k \<and> i \<in> I}) (i - card {i. i < k \<and> i \<in> I})"
proof(cases "k \<in> I")
  case True
  let ?i = "i - card {i. i < Suc k \<and> i \<in> I}"
  let ?j = "(card {a \<in> I. a < k})"
  have "pick I ?j = k" using pick_card_in_set 
    using True by presburger
  have 7:"{a \<in> I. a < k} \<union> {k} = {i. i < Suc k \<and> i \<in> I}" 
    apply safe 
      apply linarith
    using True less_SucE by blast+
  then have "{a \<in> I. a < k} \<subset> {i. i < Suc k \<and> i \<in> I}" 
    by force
  then have 3:"?j < card {i. i < Suc k \<and> i \<in> I}" 
    by (simp add: psubset_card_mono)
  then have "?j < i" 
    using assms(2) basic_trans_rules(22) by blast
  have 6:"I - {i. i < Suc k \<and> i \<in> I} = (I - {i. i < k \<and> i \<in> I}) - {k}"
    by force
  have 2: "k \<in> I - {i. i < k \<and> i \<in> I}" 
    using True by force
  have 1: "Suc ?i < card (I - {i. i < k \<and> i \<in> I}) \<or> infinite (I - {i. i < k \<and> i \<in> I})" 
  proof(cases "infinite I")
    case True
    have "infinite (I - {i. i < k \<and> i \<in> I})" using True by auto
    then show ?thesis by auto
  next
    case False
    have "i < card I" 
      using False assms(1) by blast
    then have 8: "?i < card I - card {i. i < Suc k \<and> i \<in> I}" 
      using assms(2) diff_less_mono by blast
    have "{i. i < k \<and> i \<in> I} \<subseteq> I" by auto
    then have 7:"card (I - {i. i < k \<and> i \<in> I}) = card I - card {i. i < k \<and> i \<in> I}"
      by (simp add: card_Diff_subset)
    have "Suc ?i < card I - card {i. i < Suc k \<and> i \<in> I} + 1" 
      by (simp add: 8)
    then have "Suc ?i < card I - card {i. i < k \<and> i \<in> I}" 
      by (smt (verit, del_insts) "2" "3" Diff_iff False 6 7 \<open>{i. i < k \<and> i \<in> I} \<subseteq> I\<close> 
          basic_trans_rules(22) bot_least card.empty card.infinite card_Diff_insert 
          card_Diff_subset card_mono card_seteq diff_card_le_card_Diff empty_iff finite.intros(1)
          less_Suc_eq_le less_diff_conv2 linorder_not_le minus_nat.simps(1) plus_1_eq_Suc)
    then show ?thesis 
      using 7 by presburger
  qed
  have 3: "card {i. i < k \<and> i \<in> I - {i. i < k \<and> i \<in> I}} \<le> i - card {i. i < Suc k \<and> i \<in> I}" 
    by (metis (no_types, lifting) Collect_empty_eq DiffE card_eq_0_iff mem_Collect_eq zero_le)
  have 5:"pick (I - {i. i < k \<and> i \<in> I} - {k}) (i - card {i. i < Suc k \<and> i \<in> I}) =
           pick (I - {i. i < k \<and> i \<in> I}) (Suc (i - card {i. i < Suc k \<and> i \<in> I}))"
    using pick_is_Suc_if_one_removed'[OF 1 3 2] 
    by blast
  have "card {i. i < Suc k \<and> i \<in> I} = card ({i. i < k \<and> i \<in> I} \<union> {k})" 
    by (metis (no_types, lifting) Collect_cong 7)
  then have "card {i. i < Suc k \<and> i \<in> I} =  card {i. i < k \<and> i \<in> I} + card {k}" 
    by force
  then have "card {i. i < Suc k \<and> i \<in> I} = card {i. i < k \<and> i \<in> I} + 1" 
    by auto
  then have 4: " (Suc (i - card {i. i < Suc k \<and> i \<in> I})) = (i - card {i. i < k \<and> i \<in> I})" 
    using assms(2) by linarith
  have "pick (I - {i. i < k \<and> i \<in> I} - {k}) (i - card {i. i < Suc k \<and> i \<in> I}) =
    pick ((I - {i. i < Suc k \<and> i \<in> I})) ((i - card {i. i < Suc k \<and> i \<in> I}))" 
    using 6 by presburger
  then show ?thesis using 4 5 
    by presburger
next
  case False
  have "{i. i < Suc k \<and> i \<in> I} = {i. i <  k \<and> i \<in> I} \<union> {i. i=k \<and> i \<in> I}" 
    apply (simp only: less_Suc_eq)
    by blast
  then have "{i. i < Suc k \<and> i \<in> I} = {i. i <  k \<and> i \<in> I}" using False 
    by blast
  then show ?thesis 
    by presburger
qed

lemma pick_remove_set_of_less_elem:
  assumes "i < card I \<or> infinite I"
  assumes "card {i. i < nr1 \<and> i \<in> I} \<le> i" 
  shows "pick (I - {i. i < nr1 \<and> i \<in> I}) (i - card {i. i < nr1 \<and> i \<in> I}) =  pick I i" 
  using assms
proof(induct nr1)
  case 0
  then show ?case 
    by simp
next
  case (Suc nr1)
  have "finite {i. i < nr1 \<and> i \<in> I}" 
    by simp
  have "{i. i < nr1 \<and> i \<in> I} \<subseteq>  {i. i < Suc nr1 \<and> i \<in> I}" by auto 
  then have "card {i. i < nr1 \<and> i \<in> I} \<le> card {i. i < Suc nr1 \<and> i \<in> I}"
    by (simp add: card_mono)
  then have "card {i. i < nr1 \<and> i \<in> I} \<le> i" 
    using Suc(3) basic_trans_rules(23) by blast
  have 1: "pick (I - {i. i < nr1 \<and> i \<in> I}) (i - card {i. i < nr1 \<and> i \<in> I}) = pick I i" 
    using Suc(1-2) \<open>card {i. i < nr1 \<and> i \<in> I} \<le> i\<close> by blast
  have " pick (I - {i. i < nr1 \<and> i \<in> I}) (i - card {i. i < nr1 \<and> i \<in> I}) =
       pick (I - {i. i < Suc nr1 \<and> i \<in> I}) (i - card {i. i < Suc nr1 \<and> i \<in> I})" 
    using pick_remove_elem_set_Suc_same[of i I nr1] assms(1) Suc(3) by presburger  
  then show ?case 
    using 1 by presburger
qed

lemma pick_apply_diff_func_minus_elem:
  fixes I :: "nat set"
  assumes "i < card I \<or> infinite I"
  assumes "\<forall> i \<in> I. i \<ge> k"
  shows "pick ((\<lambda>i. i - k) ` I) i = pick I i - k"
proof(cases "I = {}")
  case True
  then show ?thesis 
    using assms by auto
next
  case False
  let ?f = "(\<lambda>i. i - k)"
  have "mono ?f" 
    by (simp add: diff_le_mono mono_def)
  have "\<exists>x\<in>I. \<forall>y\<in>I. x \<le> y" 
    by (metis Collect_mem_eq False empty_Collect_eq exists_least_iff le_simps(2) not_less_eq)
  then have 3:"(LEAST a. a\<in>I) - k = (LEAST a. a\<in>(\<lambda>i. i - k) ` I)"
    by (simp add: Least_mono \<open>incseq (\<lambda>i. i - k)\<close>)
  show ?thesis using assms(1)
  proof(induct i)
    case 0
    have 4:"pick ((\<lambda>i. i - k) ` I) 0 = (LEAST a. a\<in>(\<lambda>i. i - k) ` I)" 
      using DL_Missing_Sublist.pick.simps(1) 0 by blast
    have "pick I 0 - k = (LEAST a. a\<in>I) - k"
      using DL_Missing_Sublist.pick.simps(1) 0 
      by presburger
    then show ?case 
      using 3 4 by presburger
  next
    case (Suc i)
    have "i < card I \<or> infinite I" 
      using Suc(2) Suc_lessD by blast
    have "pick I i < pick I (Suc i)" 
      using Suc(2) lessI pick_mono_inf pick_mono_le by presburger
    have 1: "pick ((\<lambda>i. i - k) ` I) i = pick I i - k" 
      using Suc(1) \<open>i < card I \<or> infinite I\<close>  by blast
    have "pick ((\<lambda>i. i - k) ` I) (Suc i) = 
          (LEAST a. a\<in>((\<lambda>i. i - k) ` I) \<and> a > pick ((\<lambda>i. i - k) ` I) i)"
      using DL_Missing_Sublist.pick.simps(2) by presburger
    then have 8:"pick ((\<lambda>i. i - k) ` I) (Suc i) = 
                (LEAST a. a\<in>((\<lambda>i. i - k) ` I) \<and> a > pick I i - k)"
      using "1" by presburger
    have 5:"{a. a\<in>((\<lambda>i. i - k) ` I) \<and> a > pick I i - k} =
    (\<lambda>i. i - k) ` ( {x. x \<in> I \<and> x > pick I i})" 
      apply safe
        apply force+
      using 1 assms(2) 
      using \<open>i < card I \<or> infinite I\<close> diff_less_mono pick_in_set by presburger
    have 6:"(LEAST a. a\<in>((\<lambda>i. i - k) ` I) \<and> a > pick I i - k) = 
        (LEAST a. a\<in>((\<lambda>i. i - k) ` ( {x. x \<in> I \<and> x > pick I i})))"
      by (metis (no_types, lifting) 5 mem_Collect_eq)
    have 9:"pick I (Suc i) = (LEAST a. a\<in>I \<and> a > pick I i)"
      using DL_Missing_Sublist.pick.simps(2)
      by presburger
    have 7:"(LEAST a. a\<in>I \<and> a > pick I i) = (LEAST a. a\<in> {x. x \<in> I \<and> x > pick I i})"
      by fastforce
    show ?case
    proof(cases "{x. x \<in> I \<and> x > pick I i} = {}")
      case True
      then show ?thesis 
        by (metis Suc.prems empty_Collect_eq lessI pick_in_set pick_mono)
    next
      case False
      have 2: "\<exists>x\<in>{x. x \<in> I \<and> x > pick I i}. \<forall>y\<in>{x. x \<in> I \<and> x > pick I i}. x \<le> y" 
        using  Collect_mem_eq False empty_Collect_eq exists_least_iff le_simps(2) not_less_eq
        by (metis (no_types, lifting))
      have " (LEAST a. a\<in> {x. x \<in> I \<and> x > pick I i}) - k = 
      (LEAST a. a\<in>((\<lambda>i. i - k) ` ( {x. x \<in> I \<and> x > pick I i})))"
        using Least_mono[OF \<open>incseq (\<lambda>i. i - k)\<close> 2]  by auto
      then show ?thesis 
        using 6 7 8 9 by presburger
    qed 
  qed
qed

lemma pick_apply_diff_func_minus_elem':
  assumes "i < card I \<or> infinite I"
  assumes "card {i. i < k \<and> i \<in> I} \<le> i" 
  shows "pick ((\<lambda>i. i - k) ` (I - {0..<k})) (i - card {i. i < k \<and> i \<in> I}) = pick I i - k"
proof -
  have 3:"(I - {0..<k}) = I - {i. i < k \<and> i \<in> I}"
    apply safe
     apply simp
    using atLeastLessThan_iff by blast
  have 4:"pick (I - {i. i < k \<and> i \<in> I}) (i - card {i. i < k \<and> i \<in> I}) = pick I i" 
    using assms(1-2) pick_remove_set_of_less_elem by blast
  have 1: "\<forall> i \<in> I - {i. i < k \<and> i \<in> I}. i \<ge> k" 
    using linorder_not_less by blast
  have 2: "i -card {i. i < k \<and> i \<in> I} < card (I - {i. i < k \<and> i \<in> I}) \<or> 
      infinite (I - {i. i < k \<and> i \<in> I})" 
  proof(cases "infinite I")
    case True
    have "infinite (I - {i. i < k \<and> i \<in> I})" 
      using True by auto
    then show ?thesis by auto
  next
    case False
    have "i < card I" 
      using assms(1) False by auto
    have "card (I - {i. i < k \<and> i \<in> I}) = card I - card {i. i < k \<and> i \<in> I}" 
      by (metis (no_types, lifting) False card_Diff_subset finite_subset mem_Collect_eq subsetI)
    then show ?thesis 
      using False assms(1) assms(2) diff_less_mono by presburger
  qed
  have "pick ((\<lambda>i. i - k) ` (I - {i. i < k \<and> i \<in> I})) (i - card {i. i < k \<and> i \<in> I}) = 
        pick (I - {i. i < k \<and> i \<in> I}) (i - card {i. i < k \<and> i \<in> I}) - k"
    using pick_apply_diff_func_minus_elem[OF 2 1]  
    by blast
  then show ?thesis 
    using 3 4 by presburger
qed

lemma card_apply_minus_func_same:
  fixes I :: "nat set"
  shows "card {i. i < a \<and> i \<in> ((\<lambda> i. i - b) ` (I - {0..<b}))} = 
         card {i. i \<ge> b \<and> i < b + a \<and> i \<in> I}" 
proof(induct a rule:nat_induct)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have " card {i. i < n \<and> i \<in> (\<lambda>i. i - b) ` (I - {0..<b})} =
  card {i. b \<le> i \<and> i < b + n \<and> i \<in> I}" 
    using Suc.hyps by blast
  show ?case
  proof(cases "b + n \<in> I")
    case True
    have "n \<in> (\<lambda>i. i - b) ` (I - {0..<b})" 
      by (metis Diff_iff True add_less_same_cancel1 atLeastLessThan_iff 
          diff_add_inverse imageI zero_order(3))
    then have 1:"{i. i < Suc n \<and> i \<in> ((\<lambda> i. i - b) ` (I - {0..<b}))} = 
          {i. i < n \<and> i \<in> ((\<lambda> i. i - b) ` (I - {0..<b}))} \<union> {n}" 
      using less_Suc_eq by blast
    have 2: "{i. b \<le> i \<and> i < b + Suc n \<and> i \<in> I} = {i. b \<le> i \<and> i < b + n \<and> i \<in> I} \<union> {b + n}"
      using True by force
    have "{i. i < n \<and> i \<in> ((\<lambda> i. i - b) ` (I - {0..<b}))} \<inter> {n} = {}" by auto
    then have 3:"card {i. i < Suc n \<and> i \<in> ((\<lambda> i. i - b) ` (I - {0..<b}))} =
        card {i. i < n \<and> i \<in> ((\<lambda> i. i - b) ` (I - {0..<b}))} + card {n}"
      using 1 by force
    have "{i. b \<le> i \<and> i < b + n \<and> i \<in> I} \<inter> {b + n} = {}" by auto
    then have "card {i. b \<le> i \<and> i < b + Suc n \<and> i \<in> I} = 
               card {i. b \<le> i \<and> i < b + n \<and> i \<in> I} + card {b + n}" 
      using 2 by fastforce
    then show ?thesis 
      by (simp add: Suc.hyps 3)
  next
    case False
    have "b + n \<notin> (I - {0..<b})"
      using False by auto
    then have "n \<notin> (\<lambda>i. i - b) ` (I - {0..<b})" 
      by auto
    then have 3:"{i. i < Suc n \<and> i \<in> (\<lambda>i. i - b) ` (I - {0..<b})} = 
    {i. i < n \<and> i \<in> (\<lambda>i. i - b) ` (I - {0..<b})}" 
      using less_Suc_eq by blast
    have "{i. b \<le> i \<and> i < b + Suc n \<and> i \<in> I} = {i. b \<le> i \<and> i < b + n \<and> i \<in> I}" 
      using False less_Suc_eq by auto
    then show ?thesis 
      using Suc.hyps 3 by presburger
  qed
qed

lemma append_submatrix_is_submatrix:
  fixes A :: "'a  mat"
  assumes A: "A \<in> carrier_mat nr1 n" 
  assumes B: "B \<in> carrier_mat nr2 n"
  shows "submatrix (A @\<^sub>r B) I J = 
         submatrix A I J @\<^sub>r submatrix B ((\<lambda> i. i - nr1) ` (I - {0..<nr1})) J"
proof 
  have 11:"dim_row (submatrix (A @\<^sub>r B) I J) = card {i. i < dim_row (A @\<^sub>r B) \<and> i \<in> I}" 
    using dim_submatrix(1) by blast
  have "dim_row (A @\<^sub>r B)= nr1 + nr2" 
    using assms(1) assms(2) carrier_matD(1) by blast
  then have 12:"{i. i < dim_row (A @\<^sub>r B) \<and> i \<in> I} = {i. i < nr1 + nr2  \<and> i \<in> I}"
    by presburger
  have 13:"{i. i < nr1 + nr2  \<and> i \<in> I} = {0..<nr1+nr2} \<inter> I" 
    by fastforce
  then have 29:"dim_row (submatrix (A @\<^sub>r B) I J) = card ({0..<nr1+nr2} \<inter> I)" 
    using 11 12 by presburger
  have 18:"dim_row (submatrix A I J) = card {i. i < nr1 \<and> i \<in> I}" 
    using assms(1) dim_submatrix(1) by blast
  have 15:"dim_row (submatrix B ((\<lambda> i. i - nr1) ` (I - {0..<nr1})) J) = 
        card {i. i < nr2 \<and> i \<in> ((\<lambda> i. i - nr1) ` (I - {0..<nr1}))}"
    using assms(2) dim_submatrix(1) by blast
  have 14:"card {i. i < nr2 \<and> i \<in> ((\<lambda> i. i - nr1) ` (I - {0..<nr1}))} = 
         card {i. i \<ge> nr1 \<and> i < nr1 + nr2 \<and> i \<in> I}" 
    using card_apply_minus_func_same by blast
  have 1:"{i. i < nr1 + nr2  \<and> i \<in> I} = {i. i < nr1 \<and> i \<in> I} \<union> 
          {i. i \<ge> nr1 \<and> i < nr1 + nr2 \<and> i \<in> I}" 
    by force
  have "{i. i < nr1 \<and> i \<in> I} \<inter> {i. i \<ge> nr1 \<and> i < nr1 + nr2 \<and> i \<in> I} = {}" 
    by fastforce
  then have 16:"card {i. i < nr1 + nr2  \<and> i \<in> I} = 
        card {i. i < nr1 \<and> i \<in> I} + card {i. i \<ge> nr1 \<and> i < nr1 + nr2 \<and> i \<in> I}"
    using 1 
    by (metis (mono_tags, lifting) 13 card_Un_disjoint finite_Int finite_Un finite_atLeastLessThan)
  have 17:"dim_row (submatrix A I J @\<^sub>r submatrix B ((\<lambda> i. i - nr1) ` (I - {0..<nr1})) J) =
         dim_row (submatrix A I J) + dim_row (submatrix B ((\<lambda> i. i - nr1) ` (I - {0..<nr1})) J)"
    by (simp add: append_rows_def)
  have 27:"dim_row (submatrix B ((\<lambda> i. i - nr1) ` (I - {0..<nr1})) J) = 
        card {i. i \<ge> nr1 \<and> i < nr1 + nr2 \<and> i \<in> I}" 
    using 14 15 by presburger
  then show 22:"dim_row (submatrix (A @\<^sub>r B) I J) = dim_row (submatrix A I J @\<^sub>r
                                          submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J)"
    using 16 11 17 18 12 by presburger
  have "dim_col (A @\<^sub>r B) = n"  
    using assms(1) assms(2) carrier_matD(2) by blast
  then have 19: "dim_col (submatrix (A @\<^sub>r B) I J) =  card {j. j < n \<and> j \<in> J}"
    using dim_submatrix(2) by blast
  have 20: "dim_col (submatrix A I J) = card {j. j < n \<and> j \<in> J}"
    using dim_submatrix(2) assms(1) by blast
  have 23:"dim_col (submatrix B ((\<lambda> i. i - nr1) ` (I - {0..<nr1})) J) = card {j. j < n \<and> j \<in> J}"
    using dim_submatrix(2) assms(2) by blast
  then show 21:"dim_col (submatrix (A @\<^sub>r B) I J) =
    dim_col (submatrix A I J @\<^sub>r submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J)"
    by (smt (verit, best) 19 20 carrier_append_rows carrier_matD(2) carrier_matI)
  fix i j
  assume asmi: "i < dim_row (submatrix A I J @\<^sub>r submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J)"
  assume asmj: "j < dim_col (submatrix A I J @\<^sub>r submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J)"
  have 25:"submatrix (A @\<^sub>r B) I J $$ (i, j) = (A @\<^sub>r B) $$ (pick I i, pick J j)"
    by (metis (no_types, lifting) 21 22 asmi asmj dim_submatrix(1-2) submatrix_index)
  show "submatrix (A @\<^sub>r B) I J $$ (i, j) =
           (submatrix A I J @\<^sub>r submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J) $$ (i, j)" 
  proof(cases "i < dim_row (submatrix A I J)")
    case True
    have 24:"(submatrix A I J @\<^sub>r submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J) $$ (i, j) = 
          (submatrix A I J) $$ (i, j)" 
      by (smt (verit, best) Missing_Matrix.append_rows_nth(1) True 19 21 20 23 asmi asmj
          carrier_matI index_row(1))
    have 26:"(submatrix A I J) $$ (i, j) = A $$ (pick I i, pick J j)"
      by (metis (no_types, lifting) True 19 21 20 asmj dim_submatrix(1-2) submatrix_index)
    have 2: "pick I i < nr1"
      using True dim_submatrix(1) pick_le assms(1) 
      by (simp add: \<open>dim_row (submatrix A I J) = card {i. i < nr1 \<and> i \<in> I}\<close>)
    have "dim_col (A @\<^sub>r B) = dim_col A" 
      by (metis A \<open>dim_col (A @\<^sub>r B) = n\<close> carrier_matD(2))
    have "j < card {j. j < n \<and> j \<in> J}" using asmj 
      using 19 21 by presburger
    then have "pick J j < n" 
      using pick_le by blast
    then have "(A @\<^sub>r B) $$ (pick I i, pick J j) = A $$ (pick I i, pick J j)"
      using index_row(1) append_rows_nth(1)[OF A B 2]
      by (metis "2" A \<open>dim_col (A @\<^sub>r B) = dim_col A\<close> \<open>dim_col (A @\<^sub>r B) = n\<close> 
          \<open>dim_row (A @\<^sub>r B) = nr1 + nr2\<close> carrier_matD(1) trans_less_add1)
    then show ?thesis 
      using 24 25 26 by presburger
  next
    case False
    have 3: "submatrix A I J \<in> carrier_mat (card {i. i < nr1 \<and> i \<in> I}) (card {j. j < n \<and> j \<in> J})"
      using 20 18 by blast
    have 4: "submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J  \<in> 
               carrier_mat (card {i. i \<ge> nr1 \<and> i < nr1 + nr2 \<and> i \<in> I}) (card {j. j < n \<and> j \<in> J})"
      using 23 27 by blast
    have 5:"i < card {i. i < nr1 \<and> i \<in> I} + card {i. nr1 \<le> i \<and> i < nr1 + nr2 \<and> i \<in> I}"
      by (metis 18 27 append_rows_def asmi index_mat_four_block(2) index_zero_mat(2))
    have 6:"card {i. i < nr1 \<and> i \<in> I} \<le> i"  
      using False 18 by linarith
    have 30:"(submatrix A I J @\<^sub>r submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J) $$ (i, j) =
          (submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J) $$ (i - card {i. i < nr1 \<and> i \<in> I}, j)"
      using append_rows_nth(2)[OF 3 4 6 5] False asmi
      by (smt (verit, ccfv_threshold) "3" "4" SNF_Missing_Lemmas.append_rows_nth
          19 21 17 18 27 asmj)
    have 32:"(submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J) 
              $$ (i - card {i. i < nr1 \<and> i \<in> I}, j) = 
          B $$ (pick ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) (i - card {i. i < nr1 \<and> i \<in> I}), pick J j)"
      by (metis (no_types, lifting) False 19 21 23 17 18 add_diff_inverse_nat asmi asmj
          dim_submatrix(1-2) nat_add_left_cancel_less submatrix_index)
    have 31:"(submatrix (A @\<^sub>r B) I J) $$ (i, j) = (A @\<^sub>r B) $$ (pick I i, pick J j)"
      using \<open>submatrix (A @\<^sub>r B) I J $$ (i, j) = (A @\<^sub>r B) $$ (pick I i, pick J j)\<close>
      by fastforce
    have "i \<ge> card {i. i < nr1 \<and> i \<in> I}" 
      using "6" by fastforce
    then have "pick I i \<ge> pick I (card {i. i < nr1 \<and> i \<in> I})" 
      by (smt (verit, best) "5" IntE 16 18 13 basic_trans_rules(21) card_mono dim_submatrix(1)
          le_eq_less_or_eq linorder_neqE_nat not_le not_less order.refl pick_mono_inf
          pick_mono_le subsetI)
    have "pick I (card {i. i < nr1 \<and> i \<in> I}) \<ge> nr1"
    proof(cases "infinite I")
      case True
      then show ?thesis  using pick_card_of_elem_ge_elem 
        by blast
    next
      case False
      have "{i. i < nr1 \<and> i \<in> I} \<subseteq> I" by auto
      then have "card {i. i < nr1 \<and> i \<in> I} < card I" 
        by (metis (mono_tags, lifting) "5" "6" Collect_empty_eq False card.empty card_seteq
            mem_Collect_eq nat_arith.rule0 not_le)
      then show ?thesis using pick_card_of_elem_ge_elem 
        by blast
    qed
    then have 7: "pick I i \<ge> nr1" 
      using \<open>pick I (card {i. i < nr1 \<and> i \<in> I}) \<le> pick I i\<close> basic_trans_rules(23) by blast
    have 8:"pick I i < nr1 + nr2" 
      using "5" 16 pick_le by presburger
    have "j < card {j. j < n \<and> j \<in> J}" using asmj 
      using 19 21 by presburger
    then have "pick J j < n" 
      using pick_le by blast
    then have 9:"(A @\<^sub>r B) $$ (pick I i, pick J j) =  B $$ (pick I i - nr1, pick J j)"
      using append_rows_nth(2)[OF A B 7 8]
      by (metis "7" "8" B SNF_Missing_Lemmas.append_rows_nth assms(1) carrier_matD(1) not_le)
    have "i < card I \<or> infinite I" 
      by (metis IntE 29 22 asmi basic_trans_rules(21) card_mono not_le subsetI)
    then have "B $$ 
              (pick ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) (i - card {i. i < nr1 \<and> i \<in> I}), pick J j) = 
              B $$ (pick I i - nr1, pick J j)" 
      using pick_apply_diff_func_minus_elem' "6" by presburger
    then show ?thesis 
      using 9 30 31 32 by presburger
  qed
qed

lemma submatrix_inter_rows':
  shows "submatrix A I J = submatrix A (I \<inter> {0..<dim_row A}) J"
proof
  show 1:"dim_row (submatrix A I J) = dim_row (submatrix A (I \<inter> {0..<dim_row A}) J)" 
    using dim_submatrix 
    by (smt (verit) Collect_cong Int_iff atLeastLessThan_iff
        less_nat_zero_code linorder_le_less_linear)
  show "dim_col (submatrix A I J) = dim_col (submatrix A (I \<inter> {0..<dim_row A}) J)" 
    using dim_submatrix 
    by (smt (verit) Collect_cong Int_iff atLeastLessThan_iff 
        less_nat_zero_code linorder_le_less_linear)
  fix i j
  assume asmi: "i < dim_row (submatrix A (I \<inter> {0..<dim_row A}) J)" 
  assume asmj: "j < dim_col (submatrix A (I \<inter> {0..<dim_row A}) J)" 
  have 3:"submatrix A I J $$ (i, j) = A $$ (pick I i, pick J j)"
    using submatrix_index
    by (metis (no_types, lifting) 1 asmi asmj dim_submatrix(1-2))
  have 2:"{a. a < dim_row A \<and> a \<in> I} = (I \<inter> {0..<dim_row A})" 
    by fastforce
  have "i < card {a. a < dim_row A \<and> a \<in> I}"
    by (metis 1 asmi dim_submatrix(1))
  then have "pick (I  \<inter> {0..<dim_row A}) i= pick I i"
    using pick_reduce_set[of i "dim_row A" I] 2
    by presburger
  then show " submatrix A I J $$ (i, j) = submatrix A (I \<inter> {0..<dim_row A}) J $$ (i, j)"
    by (metis (no_types, lifting) asmi asmj 3 dim_submatrix(1-2) submatrix_index)
qed

lemma mat_delete_index':
  assumes A: "A \<in> carrier_mat (Suc nr) (Suc nc)"
    and i: "i < Suc nr" and j: "j < Suc nc"
    and i': "i' < nr" and j': "j' < nc"
  shows "A $$ (insert_index i i', insert_index j j') = mat_delete A i j $$ (i', j')"
  unfolding mat_delete_def permutation_insert_expand insert_index_def
  using A i j i' j' by auto

lemma mat_delete_last_row_submatrix:
  fixes A :: "'a  mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec (dim_col B)"
  assumes "B = submatrix A I J" 
  assumes "j < dim_col B" 
  shows "mat_delete (B @\<^sub>r mat_of_rows (dim_col B) [b]) (dim_row B) j = 
         submatrix A I (J - {pick J j})"
proof
  show 13:"dim_row (mat_delete (B @\<^sub>r mat_of_rows (dim_col B) [b]) (dim_row B) j) =
    dim_row (submatrix A I (J - {pick J j}))" 
    by (simp add: append_rows_def assms(3) dim_submatrix(1))
  have 17:"dim_col (B @\<^sub>r mat_of_rows (dim_col B) [b]) = dim_col B"
    by (meson carrier_append_rows carrier_matD(2) carrier_matI mat_of_rows_carrier(1))
  then have 10:"dim_col (mat_delete (B @\<^sub>r mat_of_rows (dim_col B) [b]) (dim_row B) j) =
      dim_col B - 1" using mat_delete_dim(2) 
    by metis 
  have 11:"dim_col (submatrix A I (J - {pick J j})) = 
           card {i. i < dim_col A \<and> i \<in> (J - {pick J j})}"
    using dim_submatrix(2)[of A I "J - {pick J j}"] 
    by blast
  have 12:"dim_col B = card {i. i < dim_col A \<and> i \<in> J}" 
    using assms(3) dim_submatrix(2) by blast 
  have 8:"j < card {i. i < dim_col A \<and> i \<in> J}" 
    using \<open>dim_col B = card {i. i < dim_col A \<and> i \<in> J}\<close> assms(4) by presburger
  have 9:"{i. i < dim_col A \<and> i \<in> J} \<subseteq> J" 
    by fastforce
  have "{i. i < dim_col A \<and> i \<in> J} = {i. i < dim_col A \<and> i \<in> (J - {pick J j})} \<union> {pick J j}"
    apply safe
    using \<open>dim_col B = card {i. i < dim_col A \<and> i \<in> J}\<close> assms(4) pick_le apply presburger
    apply(cases "infinite J")
     apply (simp add: pick_in_set_inf)
    by (meson 8 9 basic_trans_rules(22) card_mono pick_in_set)
  then have 21: "card {i. i < dim_col A \<and> i \<in> J} - 1 = 
                 card {i. i < dim_col A \<and> i \<in> (J - {pick J j})}"
    by force
  then show 14:"dim_col (mat_delete (B @\<^sub>r mat_of_rows (dim_col B) [b]) (dim_row B) j) =
             dim_col (submatrix A I (J - {pick J j}))" 
    by (metis 10 11 12)
  fix i k
  assume asmi: "i < dim_row (submatrix A I (J - {pick J j}))"
  assume asmk: "k < dim_col (submatrix A I (J - {pick J j}))"
  have asmi': "i < dim_row (mat_delete (B @\<^sub>r mat_of_rows (dim_col B) [b]) (dim_row B) j)" 
    using 13 asmi by linarith
  have asmk': "k < dim_col (mat_delete (B @\<^sub>r mat_of_rows (dim_col B) [b]) (dim_row B) j)" 
    using 14 asmk by presburger
  have k_less_card:"k < card J \<or> infinite J" 
    by (smt (verit, ccfv_threshold) Diff_iff asmk basic_trans_rules(21) card_mono 
        dim_submatrix(2) mem_Collect_eq not_less subsetI)
  have 15: "(B @\<^sub>r mat_of_rows (dim_col B) [b]) \<in> carrier_mat (dim_row B + 1) (dim_col B)" 
    by (metis Num.numeral_nat(7) add_0 carrier_append_rows carrier_matI list.size(3) 
        list.size(4) mat_of_rows_carrier(1))
  show "mat_delete (B @\<^sub>r mat_of_rows (dim_col B) [b]) (dim_row B) j $$ (i, k) =
         submatrix A I (J - {pick J j}) $$ (i, k)"
  proof(cases "dim_col B = 0")
    case True
    then show ?thesis 
      using assms(4) by linarith
  next
    case False
    have 1:"j < Suc (dim_col B - 1)" 
      using assms(4) by linarith 
    have 2: "i < dim_row B" 
      by (metis asmi assms(3) dim_submatrix(1))
    have 3: "k < dim_col B - 1" 
      using 14 10 asmk by presburger
    have 4:"B @\<^sub>r mat_of_rows (dim_col B) [b] \<in> carrier_mat (Suc (dim_row B)) (Suc (dim_col B - 1))"
      by (metis "3" Suc_eq_plus1 15 add_diff_inverse_nat less_nat_zero_code
          nat_diff_split_asm plus_1_eq_Suc)
    have 5: "dim_row B < Suc (dim_row B)" 
      by blast
    have 18: "mat_delete (B @\<^sub>r mat_of_rows (dim_col B) [b]) (dim_row B) j $$ (i, k) =
            (B @\<^sub>r mat_of_rows (dim_col B) [b]) $$ (insert_index (dim_row B) i, insert_index j k)" 
      using mat_delete_index'[OF 4 5 1 2 3] by presburger
    have 16:"insert_index (dim_row B) i = i" 
      using 2 insert_index(1) by blast
    have "(B @\<^sub>r mat_of_rows (dim_col B) [b]) $$ (insert_index (dim_row B) i, insert_index j k) =
          (B @\<^sub>r mat_of_rows (dim_col B) [b]) $$ (i, insert_index j k)"
      using 16 by presburger
    have "(B @\<^sub>r mat_of_rows (dim_col B) [b]) $$ (i, insert_index j k) = 
        B $$ (i, insert_index j k)"
      by (smt (verit, best) "2" "4" Missing_Matrix.append_rows_nth(1) Suc_eq_plus1 17 10
          asmk' carrier_matD(1) carrier_matD(2) carrier_matI index_row(1) insert_index_def 
          mat_of_rows_carrier(1) nat_add_left_cancel_less plus_1_eq_Suc trans_less_add1)
    then have 6: "mat_delete (B @\<^sub>r mat_of_rows (dim_col B) [b]) (dim_row B) j $$ (i, k) =
                  B $$ (i, insert_index j k)"
      using 16 18 by presburger
    obtain i' where i':"row A i' = row (submatrix A I UNIV) i \<and> i' < dim_row A \<and> i' = pick I i"
      by (metis (full_types) asmi dim_submatrix(1) pick_le row_submatrix_UNIV)
    have 19:"insert_index j k < dim_col B" 
      by (metis "3" "4"17 basic_trans_rules(20) carrier_matD(2) insert_index_def not_less_eq)
    then obtain k1 where k1: "col A k1 = col (submatrix A UNIV J) (insert_index j k) \<and> 
                                         k1 < dim_col A \<and> 
                                         k1 = pick J (insert_index j k)" 
      using asmk  pick_le col_submatrix_UNIV 
      by (metis (no_types, lifting) Collect_cong 12)
    obtain k2 where k2: "col A k2 = col (submatrix A UNIV (J - {pick J j})) k \<and> 
                                    k2 < dim_col A \<and> 
                                    k2 = pick (J - {pick J j}) k"
      using asmk dim_submatrix(2) pick_le col_submatrix_UNIV 
      by (metis (no_types, lifting) Collect_cong)
    have 7: "B = submatrix (submatrix A I UNIV) UNIV J" 
      using assms(3) submatrix_split2 by blast
    have "B $$ (i, insert_index j k) = A $$ (pick I i, pick J (insert_index j k))"
      apply(simp only: assms(3))
      by (metis (no_types, lifting) 19 asmi assms(3) dim_submatrix(1-2) submatrix_index)
    then have 29:"B $$ (i, insert_index j k) = A $$ (i', k1)" 
      using i' k1 by blast
    have 30:"submatrix A I (J - {pick J j}) $$ (i, k) = A $$ (i', k2)"
      by (metis (no_types, lifting) asmi asmk dim_submatrix(1-2) i' k2 submatrix_index)
    have "pick J (insert_index j k) = pick (J - {pick J j}) k"
    proof(cases "k < j")
      case True
      have "pick J (insert_index j k) = pick J k" 
        unfolding insert_index_def 
        using True by simp
      have "pick J k \<in> J - {pick J j}" 
        by (smt (verit, del_insts) DiffI True 12 19 9 assms(4) card_mono insert_index(1) 
            nat_neq_iff order_less_le_trans pick_eq_iff_inf pick_in_set_inf pick_in_set_le 
            pick_mono_le singletonD)
      then have 21:"pick (J - {pick J j}) (card {a\<in>(J - {pick J j}). a < pick J k}) = pick J k" 
        using pick_card_in_set by presburger
      have 20: "card {a\<in>J. a < pick J k} = k" 
        by (metis True 12 19 9 card_mono card_pick insert_index(1) order_trans_rules(22))
      have "pick J k < pick J j" 
        by (metis True 12 9 assms(4) card_mono order_trans_rules(22) pick_mono_inf pick_mono_le)
      then  have "{a\<in>J. a < pick J k} = {a\<in>(J - {pick J j}). a < pick J k}"
        by auto
      then have "pick (J - {pick J j}) k = pick J k" 
        using 20 21 by presburger
      then show ?thesis 
        using \<open>pick J (insert_index j k) = pick J k\<close> by presburger
    next
      case False
      have "pick J (insert_index j k) = pick J (Suc k)" 
        using False insert_index_def by presburger
      show ?thesis
      proof(cases "k = j")
        case True
        have "pick J (Suc k) = pick J (Suc j)"
          using True by fastforce
        have "j < dim_col B - 1"
          using "3" True by blast
        then show ?thesis using pick_suc_diff_set
          by (metis (no_types, lifting) "12" "19" "9" True card_mono insert_index(2)
              le_eq_less_or_eq order_trans_rules(22))
      next
        case False
        have "k > j" using `\<not> k < j` False 
          using nat_neq_iff by blast
        then have "pick J k > pick J j" 
          using k_less_card  pick_mono_inf pick_mono_le by presburger 
        then have "pick J k \<in> J - {pick J j}" 
          by (metis (no_types, lifting) DiffI 12 19 9 basic_trans_rules(22) card_mono 
              insert_index_def le_eq_less_or_eq lessI nat_neq_iff pick_in_set_inf 
              pick_in_set_le singletonD)
        then have 1: "pick (J - {pick J j}) (card {a\<in>(J - {pick J j}). a < pick J k}) = pick J k"
          using pick_card_in_set 
          by presburger
        have 22:"{a\<in>(J - {pick J j}). a < pick J k} \<union> {pick J j} = {a\<in>J. a < pick J k}"
          apply safe
           apply (metis Diff_empty Diff_insert0 21 11 12 assms(3-4) diff_less less_nat_zero_code
              order.irrefl semiring_norm(135) zero_less_iff_neq_zero)
          by (simp add: \<open>pick J j < pick J k\<close>)
        have "pick J j \<notin> {a\<in>(J - {pick J j}). a < pick J k}"
          by blast
        have 26:"card {a\<in>J. a < pick J k} = k" 
          using card_pick k_less_card by blast
        have "card ({a\<in>(J - {pick J j}). a < pick J k} \<union> {pick J j}) = 
              card {a\<in>(J - {pick J j}). a < pick J k} + card {pick J j}"
          by force
        then have 24:"card {a\<in>(J - {pick J j}). a < pick J k} + 1 = card {a\<in>J. a < pick J k}"
          by (metis 22 card_eq_1_iff)
        then have 25:"card {a\<in>(J - {pick J j}). a < pick J k} = k - 1" 
          using \<open>card {a \<in> J. a < pick J k} = k\<close> by presburger
        then have 23: "pick (J - {pick J j}) (k - 1) = pick J k" using 1 
          by presburger
        have 27:"pick (J - {pick J j}) (Suc (k - 1)) = 
            (LEAST a. a \<in> (J - {pick J j}) \<and> pick (J - {pick J j}) (k - 1) < a)" 
          using DL_Missing_Sublist.pick.simps(2) by blast
        have 28:"pick J (Suc k) = (LEAST a. a \<in> J \<and> pick J k < a)"
          using DL_Missing_Sublist.pick.simps(2) by blast
        have "(LEAST a. a \<in> (J - {pick J j}) \<and> pick (J - {pick J j}) (k - 1) < a) = 
              (LEAST a. a \<in> J \<and> pick J k < a)" 
          by (metis Diff_iff 23 \<open>pick J j < pick J k\<close> basic_trans_rules(19) less_not_refl2 
              singletonD)
        then have "pick (J - {pick J j}) k = pick J (Suc k)" 
          by (metis Suc_eq_plus1 24 25 26 27 28)
        then show ?thesis 
          using \<open>pick J (insert_index j k) = pick J (Suc k)\<close> by presburger
      qed
    qed
    then have "k1 = k2" using k1 k2 
      by blast 
    then show ?thesis 
      using "6" 29 30 by presburger
  qed
qed

lemma mat_delete_is_submatrix:
  fixes A :: "'a  mat"
  assumes A: "A \<in> carrier_mat nk1 nk2"
  assumes "B = submatrix A I J" 
  assumes "i < dim_row B"
  assumes "j < dim_col B" 
  shows "mat_delete B i j =  submatrix A (I - {pick I i})  (J - {pick J j})"
proof
  have 14:"dim_col (mat_delete B i j) = dim_col B - 1" 
    using mat_delete_dim(2) by metis 
  have 15:"dim_col (submatrix A (I - {pick I i}) (J - {pick J j})) = 
        card {i. i < dim_col A \<and> i \<in> (J - {pick J j})}"
    using dim_submatrix(2) by blast
  have 10:"dim_col B = card {i. i < dim_col A \<and> i \<in> J}" 
    using assms(2-4) dim_submatrix(2) by blast
  then have 11:"j < card {i. i < dim_col A \<and> i \<in> J}" 
    using assms(4) by presburger
  have 12:"{i. i < dim_col A \<and> i \<in> J} \<subseteq> J" 
    by fastforce
  have "{i. i < dim_col A \<and> i \<in> J} = {i. i < dim_col A \<and> i \<in> (J - {pick J j})} \<union> {pick J j}"
    apply safe
    using 10 assms(4) pick_le apply presburger
    apply(cases "infinite J")
     apply (simp add: pick_in_set_inf)
    by (meson 11 12 basic_trans_rules(22) card_mono pick_in_set)
  then have 13:"card {i. i < dim_col A \<and> i \<in> J} - 1 = 
             card {i. i < dim_col A \<and> i \<in> (J - {pick J j})}"
    by force
  show 21: "dim_col (mat_delete B i j) =  dim_col (submatrix A (I - {pick I i})  (J - {pick J j}))" 
    using 13 14 15 10 by presburger
  have 19:"dim_row (mat_delete B i j) = dim_row B - 1"
    using mat_delete_dim(1) by metis 
  have 20:"dim_row (submatrix A (I - {pick I i}) (J - {pick J j})) = 
        card {k. k < dim_row A \<and> k \<in> (I - {pick I i})}" 
    using dim_submatrix(1) by blast
  have 16: "dim_row B = card {k. k < dim_row A \<and> k \<in> I}"
    using dim_submatrix(1) assms(2) by blast
  then have 17:"i < card {i. i < dim_row A \<and> i \<in> I}" 
    using assms(3) by presburger
  have 18:"{i. i < dim_row A \<and> i \<in> I} \<subseteq> I" 
    by fastforce
  have "{i. i < dim_row A \<and> i \<in> I} = {k. k < dim_row A \<and> k \<in> (I - {pick I i})} \<union> {pick I i}"
    apply safe
    using 16 assms(3) pick_le 
     apply presburger
    apply(cases "infinite I")
     apply (simp add: pick_in_set_inf)
    by (meson 17 18 basic_trans_rules(22) card_mono pick_in_set)
  then have "card {i. i < dim_row A \<and> i \<in> I} - 1 = card {k. k < dim_row A \<and> k \<in> (I - {pick I i})}"
    by force
  then show 22: "dim_row (mat_delete B i j) =
                 dim_row (submatrix A (I - {pick I i})  (J - {pick J j}))" 
    using 19 20 16 by presburger
  fix t k
  assume asmi: "t < dim_row (submatrix A (I - {pick I i}) (J - {pick J j}))"
  assume asmk: "k < dim_col (submatrix A (I - {pick I i}) (J - {pick J j}))"
  have asmi': "t < dim_row (mat_delete B i j)"  
    using 22 asmi by presburger
  have asmk': "k < dim_col (mat_delete B i j)" 
    using 21 asmk by presburger
  have k_less_card: "k < card J \<or> infinite J" 
    by (smt (verit, ccfv_threshold) Diff_iff asmk basic_trans_rules(21) card_mono 
        dim_submatrix(2) mem_Collect_eq not_less subsetI)
  have t_less_card: "t < card I \<or> infinite I"
    by (smt (verit, ccfv_threshold) Diff_iff asmi basic_trans_rules(21) card_mono 
        dim_submatrix(1) mem_Collect_eq not_less subsetI)
  show "(mat_delete B i j) $$ (t, k) =  submatrix A (I - {pick I i}) (J - {pick J j}) $$ (t, k)"
  proof(cases "dim_col B = 0")
    case True
    then show ?thesis 
      using assms(4) by linarith
  next
    case False
    have 1:"j < Suc (dim_col B - 1)" 
      using assms(4) by linarith 
    have 2: "i < Suc (dim_row B - 1)" 
      using assms(3) by linarith
    have 3: "k < dim_col B - 1" 
      using 14 asmk' by presburger
    have 4:"B \<in> carrier_mat (Suc (dim_row B - 1)) (Suc (dim_col B - 1))" 
      by (metis "3" 19 add_diff_inverse_nat asmi' carrier_matI less_nat_zero_code 
          nat_diff_split_asm plus_1_eq_Suc)
    have 5: "t < (dim_row B -1)" 
      using 19 asmi' by presburger
    have 44: "mat_delete B i j $$ (t, k) = B $$ (insert_index i t, insert_index j k)" 
      using mat_delete_index'[OF 4 2 1 5 3] by presburger
    have 23: "insert_index j k < dim_col B" 
      by (metis "3" "4" basic_trans_rules(20) carrier_matD(2) insert_index_def not_less_eq)
    obtain k1 where k1: "col A k1 = col (submatrix A UNIV J) (insert_index j k) \<and> 
                         k1 < dim_col A \<and>
                         k1 = pick J (insert_index j k)" 
      using asmk pick_le col_submatrix_UNIV 
      by (metis (no_types, lifting) Collect_cong 10 23)
    obtain k2 where k2: "col A k2 = col (submatrix A UNIV (J - {pick J j})) k \<and>
                         k2 < dim_col A \<and> 
                         k2 = pick (J - {pick J j}) k"
      using asmk dim_submatrix(2) pick_le col_submatrix_UNIV 
      by (metis (no_types, lifting) Collect_cong)
    have 24:"insert_index i t < dim_row B" 
      by (metis "4" 19 asmi' basic_trans_rules(20) carrier_matD(1) insert_index_def not_less_eq)
    obtain t1 where t1: "row A t1 = row (submatrix A I UNIV) (insert_index i t) \<and> 
                         t1 < dim_row A \<and> 
                         t1 = pick I (insert_index i t)" 
      using asmi pick_le row_submatrix_UNIV 
      by (metis (full_types) 16 24)
    obtain t2 where t2: "row A t2 = row (submatrix A (I - {pick I i}) UNIV) t \<and> 
                         t2 < dim_row A \<and> 
                         t2 = pick (I - {pick I i}) t"
      using asmi dim_submatrix(1) pick_le row_submatrix_UNIV 
      by (metis (full_types))
    have 7: "B = submatrix (submatrix A I UNIV) UNIV J" 
      using assms(2) submatrix_split2 by blast
    have 25:"B $$ (insert_index i t, insert_index j k) = 
          A $$ (pick I (insert_index i t), pick J (insert_index j k))"
      apply(simp only: assms(2))
      by (metis (no_types, lifting) 24 23 assms(2) dim_submatrix(1-2) submatrix_index)
    have "B $$ (insert_index i t, insert_index j k) = A $$ (t1, k1)" 
      using 25 k1 t1 by blast
    have 47: "submatrix A (I - {pick I i}) (J - {pick J j}) $$ (t, k) = A $$ (t2, k2)"
      by (metis (no_types, lifting) asmi asmk dim_submatrix(1-2) t2 k2 submatrix_index)
    have 46: "pick J (insert_index j k) = pick (J - {pick J j}) k"
    proof(cases "k < j")
      case True
      have "pick J (insert_index j k) = pick J k" 
        unfolding insert_index_def 
        using True by simp
      have "pick J k \<in> J - {pick J j}"
        by (smt (verit, del_insts) DiffI True 10 23 12  assms(4) card_mono insert_index(1)
            nat_neq_iff order_less_le_trans pick_eq_iff_inf pick_in_set_inf pick_in_set_le
            pick_mono_le singletonD)
      then have 27:"pick (J - {pick J j}) (card {a\<in>(J - {pick J j}). a < pick J k}) = pick J k" 
        using pick_card_in_set 
        by presburger
      have 26: "card {a\<in>J. a < pick J k} = k" 
        by (metis True 10 23 12 card_mono card_pick insert_index(1) order_trans_rules(22))
      have "pick J k < pick J j" 
        by (metis True 10 12 assms(4) card_mono order_trans_rules(22) pick_mono_inf pick_mono_le)
      then  have "{a\<in>J. a < pick J k} = {a\<in>(J - {pick J j}). a < pick J k}"
        by auto
      then have "pick (J - {pick J j}) k = pick J k" 
        using 26 27 by presburger
      then show ?thesis 
        using \<open>pick J (insert_index j k) = pick J k\<close> by presburger
    next
      case False
      have "pick J (insert_index j k) = pick J (Suc k)" 
        using False insert_index_def by presburger
      show ?thesis
      proof(cases "k = j")
        case True
        have "pick J (Suc k) = pick J (Suc j)"
          using True by fastforce
        have "j < dim_col B - 1"
          using "3" True by blast
        then show ?thesis using pick_suc_diff_set 
          by (metis False True 10 23 12 basic_trans_rules(22) card_mono insert_index_def)
      next
        case False
        have "k > j"
          using `\<not> k < j` False nat_neq_iff by blast
        then have 30: "pick J k > pick J j"
          using k_less_card pick_mono_inf pick_mono_le by presburger
        have "pick J k \<in> J - {pick J j}" 
          using k_less_card
          by (metis Diff_iff 30 nat_neq_iff pick_in_set_inf 
              pick_in_set_le singletonD)
        then have 1: "pick (J - {pick J j}) (card {a\<in>(J - {pick J j}). a < pick J k}) = pick J k"
          using pick_card_in_set 
          by presburger
        have 28: "{a\<in>(J - {pick J j}). a < pick J k} \<union> {pick J j} = {a\<in>J. a < pick J k}"
          apply safe
           apply (meson 11 12 card_mono order_trans_rules(22) pick_in_set_inf pick_in_set_le)
          by (simp add: \<open>pick J j < pick J k\<close>)
        have "pick J j \<notin> {a\<in>(J - {pick J j}). a < pick J k}"
          by blast
        have "card {a\<in>J. a < pick J k} = k" 
          using k_less_card card_pick by presburger
        have "card ({a\<in>(J - {pick J j}). a < pick J k} \<union> {pick J j}) = 
              card {a\<in>(J - {pick J j}). a < pick J k} + card {pick J j}"
          by force
        then have 31:"card {a\<in>(J - {pick J j}). a < pick J k} + 1 = card {a\<in>J. a < pick J k}"
          by (metis 28 card_eq_1_iff)
        then have 32: "card {a\<in>(J - {pick J j}). a < pick J k} = k - 1" 
          using \<open>card {a \<in> J. a < pick J k} = k\<close> by presburger
        then have 29:"pick (J - {pick J j}) (k - 1) = pick J k" 
          using 1 by presburger
        have 33: "pick (J - {pick J j}) (Suc (k - 1)) = 
              (LEAST a. a \<in> (J - {pick J j}) \<and> pick (J - {pick J j}) (k - 1) < a)" 
          using DL_Missing_Sublist.pick.simps(2) by blast
        have 34: "pick J (Suc k) = (LEAST a. a \<in> J \<and> pick J k < a)"
          using DL_Missing_Sublist.pick.simps(2) by blast
        have "(LEAST a. a \<in> (J - {pick J j}) \<and> pick (J - {pick J j}) (k - 1) < a) = 
              (LEAST a. a \<in> J \<and> pick J k < a)" 
          by (metis Diff_iff 29 30 basic_trans_rules(19) less_not_refl2 singletonD)
        then have "pick (J - {pick J j}) k = pick J (Suc k)" 
          by (metis Suc_eq_plus1 31 32 \<open>card {a \<in> J. a < pick J k} = k\<close> 33 34)
        then show ?thesis 
          using \<open>pick J (insert_index j k) = pick J (Suc k)\<close> by presburger
      qed
    qed
    then have "k1 = k2"
      using k1 k2 by blast 
    have 45: "pick I (insert_index i t) = pick (I - {pick I i}) t"
    proof(cases "t < i")
      case True
      have "pick I (insert_index i t) = pick I t"
        unfolding insert_index_def 
        using True by simp
      have "pick I t \<in> I - {pick I i}" 
        using t_less_card 
        by (metis (no_types, lifting) Diff_iff True 16 18 assms(3) card_mono order_less_imp_not_eq 
            order_less_le_trans pick_in_set_inf pick_in_set_le pick_mono singletonD)
      then have 35: "pick (I - {pick I i}) (card {a\<in>(I - {pick I i}). a < pick I t}) = pick I t" 
        using pick_card_in_set by presburger
      have 9:"card {a\<in>I. a < pick I t} = t" 
        by (metis True 16 24 18 card_mono card_pick insert_index(1) order_trans_rules(22))
      have "pick I t < pick I i" 
        by (metis True 16 18 assms(3) card_mono order_trans_rules(22) pick_mono_inf pick_mono_le)
      then  have 8: "{a\<in>I. a < pick I t} = {a\<in>(I - {pick I i}). a < pick I t}"
        by auto
      then have "pick (I - {pick I i}) t = pick I t" 
        using "9" 35 by presburger
      then show ?thesis 
        using \<open>pick I (insert_index i t) = pick I t\<close> by presburger
    next
      case False
      have "pick I (insert_index i t) = pick I (Suc t)" 
        using False insert_index_def by presburger
      show ?thesis
      proof(cases "t = i")
        case True
        have "pick I (Suc t) = pick I (Suc i)"
          using True by fastforce
        have "i < dim_row B - 1" 
          using "5" True by blast
        then show ?thesis 
          using pick_suc_diff_set
          by (metis False True 16 24 18 basic_trans_rules(22) card_mono insert_index_def)
      next
        case False
        have "t > i" using `\<not> t < i` False 
          using nat_neq_iff by blast
        then have 39: "pick I t > pick I i"
          using pick_mono_inf pick_mono_le t_less_card by presburger
        have "pick I t \<in> I - {pick I i}" 
          by (metis Diff_iff \<open>pick I i < pick I t\<close> nat_neq_iff pick_in_set singletonD t_less_card)
        then have 1: "pick (I - {pick I i}) (card {a\<in>(I - {pick I i}). a < pick I t}) = pick I t"
          using pick_card_in_set 
          by presburger
        have 36:"{a\<in>(I - {pick I i}). a < pick I t} \<union> {pick I i} = {a\<in>I. a < pick I t}"
          apply safe
           apply (metis "4" "5" 16 \<open>i < t\<close> 18 card_mono carrier_matD(1) less_SucI less_or_eq_imp_le 
              order_trans_rules(22) pick_in_set_inf pick_in_set_le)
          by (simp add: 39)
        have "pick I i \<notin> {a\<in>(I - {pick I i}). a < pick I t}"
          by blast
        have 37: "card {a\<in>I. a < pick I t} = t" 
          using card_pick t_less_card by blast
        have "card ({a\<in>(I - {pick I i}). a < pick I t} \<union> {pick I i}) = 
              card {a\<in>(I - {pick I i}). a < pick I t} + card {pick I i}"
          by force
        then have 40: "card {a\<in>(I - {pick I i}). a < pick I t} + 1 = card {a\<in>I. a < pick I t}"
          by (metis 36 card_eq_1_iff)
        then have 41: "card {a\<in>(I - {pick I i}). a < pick I t} = t - 1" 
          using 37 by presburger
        then have 38: "pick (I - {pick I i}) (t - 1) = pick I t"
          using 1 by presburger
        have 42: "pick (I - {pick I i}) (Suc (t - 1)) = 
              (LEAST a. a \<in> (I - {pick I i}) \<and> pick (I - {pick I i}) (t - 1) < a)" 
          using DL_Missing_Sublist.pick.simps(2) by blast
        have 43:"pick I (Suc t) = (LEAST a. a \<in> I \<and> pick I t < a)"
          using DL_Missing_Sublist.pick.simps(2) by blast
        have "(LEAST a. a \<in> (I - {pick I i}) \<and> pick (I - {pick I i}) (t - 1) < a) = 
              (LEAST a. a \<in> I \<and> pick I t < a)" 
          by (metis Diff_iff 38 39 basic_trans_rules(19) less_not_refl2 singletonD)
        then have "pick (I - {pick I i}) t = pick I (Suc t)" 
          by (metis Suc_eq_plus1 40 41 37 42 43)
        then show ?thesis 
          using \<open>pick I (insert_index i t) = pick I (Suc t)\<close> by presburger
      qed
    qed
    then have "t1 = t2" using t1 t2 
      by blast
    show ?thesis 
      using 25 44 45 46 47 k2 t2 by presburger
  qed
qed

lemma submatrix_one_row_mat_of_rows:
  assumes "b \<in> carrier_vec n"
  shows "submatrix (mat_of_rows n [b]) {0} J =
         mat_of_rows (card ({0..<n} \<inter> J)) [vec_of_list (nths (list_of_vec (b)) J)]"
proof
  have 7: "dim_row (mat_of_rows n [b]) = 1"
    by simp
  have 1:"dim_row (submatrix (mat_of_rows n [b]) {0} J) = 
          card {i. i < dim_row (mat_of_rows n [b]) \<and> i \<in> {0}}" 
    using dim_submatrix(1) by blast
  have "{i. i < dim_row (mat_of_rows n [b]) \<and> i \<in> {0}} = {0}"
    by auto
  then have 6: "dim_row (submatrix (mat_of_rows n [b]) {0} J) = 1"
    by (simp add: "1")
  then show "dim_row (submatrix (mat_of_rows n [b]) {0} J) =
    dim_row (mat_of_rows (card ({0..<n} \<inter> J))  [vec_of_list (nths (list_of_vec b) J)])"
    by simp 
  have 2: "dim_col (submatrix (mat_of_rows n [b]) {0} J) = 
      card {j. j < dim_col (mat_of_rows n [b]) \<and> j \<in> J}"
    by (simp add: dim_submatrix(2))
  have 3: "{j. j < dim_col (mat_of_rows n [b]) \<and> j \<in> J} =  {j. j < n \<and> j \<in> J}" 
    by auto
  then have "{j. j < n \<and> j \<in> J} = {0..<n} \<inter> J" 
    by auto
  then have 4: "card {j. j < dim_col (mat_of_rows n [b]) \<and> j \<in> J} = (card ({0..<n} \<inter> J))" 
    using 3 by presburger
  then show 5: "dim_col (submatrix (mat_of_rows n [b]) {0} J) =
         dim_col (mat_of_rows (card ({0..<n} \<inter> J)) [vec_of_list (nths (list_of_vec b) J)])"
    by (simp add: 2)
  fix i
  fix j
  assume asmi: "i < dim_row (mat_of_rows (card ({0..<n} \<inter> J))
                 [vec_of_list (nths (list_of_vec b) J)])"
  assume asmj: "j < dim_col (mat_of_rows (card ({0..<n} \<inter> J)) 
                 [vec_of_list (nths (list_of_vec b) J)])"
  have "i = 0" 
    by (metis Num.numeral_nat(7) Suc_eq_plus1 asmi less_one list.size(3-4) mat_of_rows_carrier(2))
  have "j < (card ({0..<n} \<inter> J))" 
    using 4 2 5 asmj by presburger
  have "row (submatrix (mat_of_rows n [b]) {0} J) 0 = col (submatrix (mat_of_rows n [b]) {0} J)\<^sup>T 0" 
    by (simp add: 6)
  have 8: "mat_of_rows (card ({0..<n} \<inter> J)) [vec_of_list (nths (list_of_vec b) J)] $$ (i, j) =
       vec_of_list (nths (list_of_vec b) J) $ j"
    by (metis One_nat_def Suc_eq_plus1 \<open>i = 0\<close> \<open>j < card ({0..<n} \<inter> J)\<close> list.size(3-4) 
        mat_of_rows_index nth_Cons_0 zero_less_one_class.zero_less_one)
  have 10: "vec_of_list (nths (list_of_vec b) J) $ j = b $ (pick J j)" 
  proof -
    have f1: "card ({0..<n} \<inter> J) = card {na. na < n \<and> na \<in> J}"
      by (smt (z3) 4 3)
    have f2: "j < card ({0..<n} \<inter> J)"
      using \<open>j < card ({0..<n} \<inter> J)\<close> by fastforce
    have "dim_vec b = n"
      by (smt (z3) assms carrier_vecD)
    then show ?thesis
      using f2 f1 by (simp add: list_of_vec_index nth_nths)
  qed
  have 9: "submatrix (mat_of_rows n [b]) {0} J $$ (i, j) = 
        (mat_of_rows n [b]) $$ (pick {0} i, pick J j)" 
    by (metis (no_types, lifting) 4 2 6 \<open>i = 0\<close> \<open>j < card ({0..<n} \<inter> J)\<close> dim_submatrix(1-2)
        submatrix_index zero_less_one_class.zero_less_one)
  have "(mat_of_rows n [b]) $$ (pick {0} i, pick J j) = b $ (pick J j)" 
    by (metis "1" One_nat_def Suc_eq_plus1 7 6 \<open>i = 0\<close> \<open>j < card ({0..<n} \<inter> J)\<close>
        \<open>{j. j < n \<and> j \<in> J} = {0..<n} \<inter> J\<close> less_one list.size(3-4) mat_of_rows_index
        nth_Cons_0 pick_le)
  then show "submatrix (mat_of_rows n [b]) {0} J $$ (i, j) =
           mat_of_rows (card ({0..<n} \<inter> J)) [vec_of_list (nths (list_of_vec b) J)] $$ (i, j)"
    using 8 9 10 by presburger
qed

lemma only_one_nonzero_is_sum:
  assumes "finite S" 
  assumes "a \<in> S"
  assumes "\<forall> x \<in> S. x \<noteq> a \<longrightarrow> f x = 0"
  shows "sum f S = f a" 
  by (metis (mono_tags, opaque_lifting) Diff_iff add.right_neutral assms
      insert_iff sum.neutral sum.remove)

lemma empty_set_submatrix_iz_zero_mat:
  shows "submatrix A {} J = 0\<^sub>m 0 (dim_col (submatrix A {} J))"
  unfolding submatrix_def 
  apply rule
  by simp+

lemma row_apend_last_row:
  fixes A :: "'a  mat"
  assumes A: "A \<in> carrier_mat nr nc" 
  assumes "b \<in> carrier_vec nc" 
  assumes "B = A @\<^sub>r mat_of_rows nc [b]"
  shows "row B nr = b" 
  by (smt (verit, del_insts) add.right_neutral add_Suc_right assms(1-3) diff_add_inverse 
      gram_schmidt.append_rows_index_same' le_refl length_nth_simps(3) lessI list.size(3) 
      list.size(4) mat_of_rows_carrier(1) mat_of_rows_row)

lemma tot_unimod_append_unit_vec:
  fixes A :: "'a  mat"
  assumes A: "A \<in> carrier_mat nr n" 
  assumes "tot_unimodular A"
  shows "tot_unimodular (A @\<^sub>r mat_of_rows n [unit_vec n i])" (is "tot_unimodular ?A'")
  unfolding tot_unimodular_def
proof rule
  fix B
  show " (\<exists>I J. submatrix (A @\<^sub>r mat_of_rows n [unit_vec n i])I J = B) \<longrightarrow> det B \<in> {- 1, 0, 1}" 
  proof
    assume asm:"\<exists>I J. submatrix (A @\<^sub>r mat_of_rows n [unit_vec n i]) I J = B"
    then show "det B \<in> {-1,0,1}" 
    proof(cases "dim_row B \<noteq> dim_col B")
      case True
      then show ?thesis unfolding Determinant.det_def 
        by (meson insertCI)
    next
      case False
      then  have "dim_row B = dim_col B"
        by auto
      obtain I J where I_J: "submatrix (A @\<^sub>r mat_of_rows n [unit_vec n i]) I J = B"
        using asm by presburger
      have 1: "mat_of_rows n [unit_vec n i] \<in> carrier_mat 1 n" 
        using mat_of_rows_carrier(1)[of n "[unit_vec n i]"] 
        by auto
      have 24: "row ?A' nr = unit_vec n i" 
        using append_rows_nth(2)[OF A 1] mat_of_rows_row by simp 
      have 2: "B \<in> carrier_mat (dim_row B) (dim_row B)" 
        by (metis False carrier_matI)
      let ?f = "(\<lambda> i. i - nr)"
      have 10:"B = submatrix A I J @\<^sub>r 
               submatrix (mat_of_rows n [unit_vec n i]) (?f ` (I - {0..<nr})) J"
        using append_submatrix_is_submatrix[OF A 1] I_J by blast
      show ?thesis 
      proof(cases "nr \<in> I")
        case True
        have 15: "dim_row (A @\<^sub>r mat_of_rows n [unit_vec n i]) = nr + 1"
          by (meson "1" assms(1) carrier_append_rows carrier_matD(1))
        have 16: "{ia. ia < dim_row (A @\<^sub>r mat_of_rows n [unit_vec n i]) \<and> ia \<in> I} \<noteq> {}"
          by (metis "15" Collect_empty_eq Suc_eq_plus1 True lessI)
        have "finite {ia. ia < dim_row (A @\<^sub>r mat_of_rows n [unit_vec n i]) \<and> ia \<in> I}"
          using finite_nat_set_iff_bounded by blast
        then have "card {ia. ia < dim_row (A @\<^sub>r mat_of_rows n [unit_vec n i]) \<and> ia \<in> I} > 0"
          using 16 card_gt_0_iff by blast
        then have "dim_row (submatrix ?A' I J) > 0" 
          using dim_submatrix(1)[of ?A' I J] by linarith
        then have "dim_row B - 1 < dim_row B" 
          using I_J diff_less verit_comp_simplify(28) by blast
        have 4: "det B = (\<Sum>j<dim_row B. B $$ (dim_row B - 1,j) * cofactor B (dim_row B - 1) j)"
          using laplace_expansion_row[OF 2] \<open>dim_row B - 1 < dim_row B\<close> by blast
        have 3:"dim_row (mat_of_rows n [unit_vec n i]) =  1"
          using 1 by fast
        have 18: "submatrix (mat_of_rows n [unit_vec n i]) (?f ` (I - {0..<nr})) J =
              submatrix (mat_of_rows n [unit_vec n i]) (?f ` (I - {0..<nr})\<inter>{0..<1}) J"
          using submatrix_inter_rows' 3 
          by metis
        have 17: "?f ` (I - {0..<nr}) \<inter> {0..<1} = {0}" 
          apply safe 
            apply simp+
           apply (metis DiffI True atLeastLessThan_iff diff_self_eq_0 image_iff less_irrefl)
          by simp
        have 19: "submatrix (mat_of_rows n [unit_vec n i]) (?f ` (I - {0..<nr})) J =
              submatrix (mat_of_rows n [unit_vec n i]) {0} J" 
          by (metis 17 18)
        have 20: "B = submatrix A I J @\<^sub>r submatrix (mat_of_rows n [unit_vec n i]) {0} J" 
          by (simp add: 10 19)
        have 21: "B = submatrix A I J @\<^sub>r mat_of_rows (card ({0..<n} \<inter> J)) 
                  [vec_of_list (nths (list_of_vec (unit_vec n i)) J)]"
          by (simp add: 20 submatrix_one_row_mat_of_rows)
        have "row (submatrix A I J @\<^sub>r
              mat_of_rows (card ({0..<n} \<inter> J)) [vec_of_list (nths (list_of_vec (unit_vec n i)) J)]) 
              (dim_row (submatrix A I J)) = vec_of_list (nths (list_of_vec (unit_vec n i)) J)"
          by (smt (verit, best) A Collect_cong carrier_dim_vec carrier_matD(2)
              carrier_matI dim_submatrix(2) dim_vec row_apend_last_row submatrix_one_row_mat_of_rows
              mat_of_rows_carrier(3) nths_list_pick_vec_same unit_vec_carrier)
        then  have 22: "row B (dim_row B - 1) = vec_of_list (nths (list_of_vec (unit_vec n i)) J)"
          using row_apend_last_row 
          by (simp add: 21 append_rows_def)
        have 5:"vec_of_list (nths (list_of_vec (unit_vec n i)) J) =
                vec (card {ia. ia<dim_vec (unit_vec n i) \<and> ia \<in> J}) 
                (\<lambda> ia. (unit_vec n i) $ (pick J ia))"
          using nths_list_pick_vec_same[of "(unit_vec n i)" J]
          by force
        then have 6:"\<forall> j < dim_col B. B $$ (dim_row B - 1,j) = (unit_vec n i) $ (pick J j)" 
          using 5 
          by (smt (verit, best) Matrix.row_def 22 index_vec row_carrier vec_carrier_vec)
        show ?thesis
        proof(cases "i < n")
          case True
          have 7: "\<forall> j < dim_col B. pick J j \<noteq> i \<longrightarrow>  B $$ (dim_row B - 1,j) = 0"
          proof safe
            fix k
            assume asm: "k < dim_col B" "pick J k \<noteq> i"
            have "pick J k < n" 
              by (metis (no_types, lifting) "5" Collect_cong 22 asm(1) index_unit_vec(3) pick_le
                  row_carrier vec_carrier_vec)
            then have "(unit_vec n i) $ (pick J k) = 0" 
              unfolding unit_vec_def 
              using asm(2) by force
            then show " B $$ (dim_row B - 1, k) = 0" 
              using "6" asm(1) by auto
          qed
          have 23: "\<forall> j < dim_col B. pick J j = i \<longrightarrow>  B $$ (dim_row B - 1,j) = 1"
            by (metis "6" True index_unit_vec(2))
          show ?thesis 
          proof(cases "\<exists>j. j < dim_col B \<and> pick J j = i")
            case True
            obtain j where j: "pick J j = i \<and> j < dim_col B" 
              using True by blast
            have "B $$ (dim_row B - 1,j) = 1" 
              using 23 j by presburger
            have 26: "\<forall> k < dim_col B. k \<noteq> j \<longrightarrow>  B $$ (dim_row B - 1,k) = 0" 
            proof safe
              fix k
              assume asm: "k < dim_col B" " k \<noteq> j"
              have "pick J k \<noteq> i" 
              proof(rule ccontr)
                assume asm_not_eq: "\<not> pick J k \<noteq> i"
                then have 25: "pick J k = pick J j" 
                  using j by fastforce
                show False
                proof(cases "infinite J")
                  case True
                  then show ?thesis 
                    using \<open>pick J k = pick J j\<close> asm(2) pick_eq_iff_inf by blast
                next
                  case False
                  have "dim_col B = 
                        (card {ia. ia<dim_col (A @\<^sub>r mat_of_rows n [unit_vec n i]) \<and> ia\<in>J})" 
                    using I_J dim_submatrix(2) by blast
                  then have 26: "dim_col B = (card {ia. ia<n \<and> ia\<in>J})" 
                    by (metis 24 index_row(2) index_unit_vec(3))
                  then have "j < card J" 
                    by (metis (mono_tags, lifting) 25 asm(2) basic_trans_rules(21) card_mono j 
                        mem_Collect_eq not_less pick_eq_iff_inf subsetI)
                  then show ?thesis 
                    by (metis (mono_tags, lifting) False asm_not_eq 26 asm(1-2) mem_Collect_eq
                        basic_trans_rules(21) card_mono j nat_neq_iff not_less pick_mono subsetI)
                qed
              qed
              then show " B $$ (dim_row B - 1, k) = 0" 
                using "7" asm(1) by presburger
            qed
            have "\<forall>k \<in> {0..<dim_col B}. j \<noteq> k \<longrightarrow>  B $$ (dim_row B - 1, k) = 0" 
              using 26 atLeastLessThan_iff by blast
            then have "(\<Sum>j \<in> {0..<dim_col B}. 
                        B $$ (dim_row B - 1,j) * cofactor B (dim_row B - 1) j) =
                        B $$ (dim_row B - 1,j) * cofactor B (dim_row B - 1) j" 
              using only_one_nonzero_is_sum[of "{0..<dim_col B}" j]
              by (metis (no_types, lifting) atLeast0LessThan finite_atLeastLessThan j lessThan_iff
                  vector_space_over_itself.scale_eq_0_iff)
            then have "(\<Sum>j<dim_col B. B $$ (dim_row B - 1,j) * cofactor B (dim_row B - 1) j) =
                       B $$ (dim_row B - 1,j) * cofactor B (dim_row B - 1) j" 
              by (metis atLeast0LessThan)
            then have 27: "det B =  B $$ (dim_row B - 1,j) * cofactor B (dim_row B - 1) j"
              by (metis "4" \<open>dim_row B = dim_col B\<close>)
            then have 28: "det B = cofactor B (dim_row B - 1) j" 
              using \<open>B $$ (dim_row B - 1, j) = 1\<close> l_one by presburger
            have 8: "cofactor B (dim_row B - 1) j = 
                (-1)^((dim_row B - 1)+j) * det (mat_delete B (dim_row B - 1) j)" 
              by (meson Determinant.cofactor_def)
            have 9:"mat_delete B (dim_row B - 1) j = submatrix A I (J - {pick J j})"
              using mat_delete_last_row_submatrix 
              by (smt (z3) "5" A Collect_cong One_nat_def Suc_eq_plus1 10 22 19 append_rows_def 
                  carrier_matD(2) diff_add_inverse dim_submatrix(2) dim_vec vec_carrier
                  submatrix_one_row_mat_of_rows index_mat_four_block(2) index_row(2) 
                  index_unit_vec(3) index_zero_mat(2) j list.size(3) list.size(4) 
                  mat_of_rows_carrier(1) mat_of_rows_carrier(2) plus_1_eq_Suc unit_vec_carrier )
            have "det (submatrix A I (J - {pick J j})) \<in> {-1, 0, 1}" 
              using assms(2) unfolding tot_unimodular_def 
              by blast
            then  have "det (mat_delete B (dim_row B - 1) j) \<in> {-1, 0, 1}" 
              using "9" by presburger 
            then have "cofactor B (dim_row B - 1) j \<in> {-1, 0, 1}" using 8 9 
              by (smt (verit) R.add.inv_equality UNIV_I add_neg_numeral_special(7) 
                  cring_simprules(29) insert_iff mult_cancel_right2 mult_minus1_right 
                  nat_pow_distrib singletonD square_eq_one)
            then show ?thesis 
              using `det B = cofactor B (dim_row B - 1) j` by auto
          next
            case False
            then have "\<forall> j < dim_col B. B $$ (dim_row B - 1,j) = 0"
              using "7" by blast
            then have "det B = 0" 
              by (simp add: "4" \<open>dim_row B = dim_col B\<close>)
            then show ?thesis by auto
          qed
        next
          case False
          have "unit_vec n i = 0\<^sub>v n"
            unfolding unit_vec_def zero_vec_def 
            using False by fastforce
          then have "\<forall> j < dim_col B. B $$ (dim_row B - 1,j) = 0" 
            using 6
            by (metis (no_types, lifting) "5" Collect_cong 22 \<open>unit_vec n i = 0\<^sub>v n\<close> carrier_vecD
                index_row(2) index_unit_vec(3) index_zero_vec(1) pick_le vec_carrier)
          then show ?thesis using 4 
            by (simp add: \<open>dim_row B = dim_col B\<close>)
        qed
      next
        case False
        have 3:"dim_row (mat_of_rows n [unit_vec n i]) =  1" using 1 
          by fast
        have 29: "submatrix (mat_of_rows n [unit_vec n i]) (?f ` (I - {0..<nr})) J =
              submatrix (mat_of_rows n [unit_vec n i]) (?f ` (I - {0..<nr})\<inter>{0..<1}) J"
          using submatrix_inter_rows' 3 
          by metis
        have 28: "?f ` (I - {0..<nr}) \<inter> {0..<1} = {}" 
          apply safe 
          apply simp+
          using False by auto
        have 30: "submatrix (mat_of_rows n [unit_vec n i]) (?f ` (I - {0..<nr})) J = 
            submatrix (mat_of_rows n [unit_vec n i]) {} J" 
          by (metis 28 29)
        then have 11: "submatrix (mat_of_rows n [unit_vec n i]) {} J  = 
              0\<^sub>m 0 (dim_col (submatrix (mat_of_rows n [unit_vec n i]) (?f ` (I - {0..<nr})) J))"
          using empty_set_submatrix_iz_zero_mat 
          by (smt (verit) Collect_cong dim_submatrix(2) mat_of_rows_carrier(3))
        have "B = submatrix A I J" 
          apply rule
            apply (metis "10" append_rows_def index_mat_four_block(1) trans_less_add1)
           apply (metis (no_types, lifting) "10" "11" 30 add.right_neutral append_rows_def
              index_mat_four_block(2) index_zero_mat(2))
          by (metis (no_types, lifting) A Collect_cong I_J 24 carrier_matD(2) dim_submatrix(2) 
              index_row(2) index_unit_vec(3))
        then show ?thesis
          using assms(2) unfolding tot_unimodular_def by auto
      qed
    qed
  qed
qed

lemma uminus_unit_vec:
  shows "- unit_vec n i = vec n (\<lambda> j. if j = i then - 1 else (0::'a))"
  unfolding uminus_vec_def unit_vec_def
  by force

lemma uminus_zero_vec:
  shows "(0\<^sub>v n :: 'a vec) = - 0\<^sub>v n" 
  unfolding zero_vec_def 
proof
  show "dim_vec (Matrix.vec n (\<lambda>i. 0)) = dim_vec (- Matrix.vec n (\<lambda>i. 0))" by simp
  fix i
  assume "i  < dim_vec (- Matrix.vec n (\<lambda>i. 0))"
  show " Matrix.vec n (\<lambda>i. 0 :: 'a) $v i = (- Matrix.vec n (\<lambda>i. 0)) $v i"
    using \<open>i < dim_vec (- Matrix.vec n (\<lambda>i. 0))\<close> by auto
qed

lemma uminus_vec_if_zero:
  assumes "v \<in> carrier_vec n"
  assumes "v = (0\<^sub>v n :: 'a vec)"
  shows "-v = 0\<^sub>v n"
  using uminus_zero_vec assms 
  by argo

lemma tot_unimod_append_minus_unit_vec:
  fixes A :: "'a  mat"
  assumes A: "A \<in> carrier_mat nr n" 
  assumes "tot_unimodular A"
  shows "tot_unimodular (A @\<^sub>r mat_of_rows n [(- (unit_vec n i):: 'a vec)])"
    (is "tot_unimodular ?A'")
  unfolding tot_unimodular_def
proof rule
  fix B
  show " (\<exists>I J. submatrix ?A' I J = B) \<longrightarrow> det B \<in> {- 1, 0, 1}" 
  proof
    assume asm:"\<exists>I J. submatrix ?A' I J = B"
    then show "det B \<in> {-1,0,1}" 
    proof(cases "dim_row B \<noteq> dim_col B")
      case True
      then show ?thesis unfolding Determinant.det_def 
        by (meson insertCI)
    next
      case False
      then  have "dim_row B = dim_col B" by auto
      obtain I J where I_J: "submatrix ?A' I J = B"
        using asm by presburger
      have 1: "mat_of_rows n [(- (unit_vec n i) :: 'a vec)] \<in> carrier_mat 1 n" 
        using mat_of_rows_carrier(1)[of n "[unit_vec n i]"] 
        by auto
      have 25: "row ?A' nr = (- (unit_vec n i) :: 'a vec)" 
        using append_rows_nth(2)[OF A 1] mat_of_rows_row by simp 
      have 2: "B \<in> carrier_mat (dim_row B) (dim_row B)" 
        by (metis False carrier_matI)
      let ?f = "(\<lambda> i. i - nr)"
      have 10:"B = submatrix A I J @\<^sub>r
               submatrix (mat_of_rows n [(- (unit_vec n i) :: 'a vec)]) (?f ` (I - {0..<nr})) J"
        using append_submatrix_is_submatrix[OF A 1] I_J by blast
      show ?thesis 
      proof(cases "nr \<in> I")
        case True
        have 15: "dim_row (A @\<^sub>r mat_of_rows n [- unit_vec n i]) = nr + 1"
          using "1" assms(1) carrier_matD(1) by blast          
        have 16: "{ia. ia < 
                      dim_row (A @\<^sub>r mat_of_rows n [- (unit_vec n i) :: 'a vec]) \<and> ia \<in> I} \<noteq> {}"
          by (metis "15" True empty_iff less_add_one mem_Collect_eq)
        have "finite {ia. ia < dim_row (A @\<^sub>r mat_of_rows n [- (unit_vec n i) :: 'a vec]) \<and> ia \<in> I}"
          using finite_nat_set_iff_bounded by blast
        then have "card {ia. ia < 
                   dim_row (A @\<^sub>r mat_of_rows n [- (unit_vec n i) :: 'a vec]) \<and> ia \<in> I} > 0"
          using 16 card_gt_0_iff by blast
        then have "dim_row (submatrix ?A' I J) > 0" 
          using dim_submatrix(1)[of ?A' I J]  
          by linarith
        then have "dim_row B - 1 < dim_row B" 
          using I_J diff_less verit_comp_simplify(28) by blast
        have 4: "det B = (\<Sum>j<dim_row B. B $$ (dim_row B - 1,j) * cofactor B (dim_row B - 1) j)"
          using laplace_expansion_row[OF 2] 
          using \<open>dim_row B - 1 < dim_row B\<close> by blast
        have 3:"dim_row (mat_of_rows n [- (unit_vec n i) :: 'a vec]) =  1" using 1 
          by fast
        have 18: "submatrix (mat_of_rows n [- (unit_vec n i) :: 'a vec]) (?f ` (I - {0..<nr})) J =
              submatrix (mat_of_rows n [- (unit_vec n i) :: 'a vec]) 
                        (?f ` (I - {0..<nr}) \<inter> {0..<1}) J"
          using submatrix_inter_rows' 3 
          by metis
        have 17: "?f ` (I - {0..<nr}) \<inter> {0..<1} = {0}" 
          apply safe 
            apply simp+
           apply (metis DiffI True atLeastLessThan_iff diff_self_eq_0 image_iff less_irrefl)
          by simp
        have 19: "submatrix (mat_of_rows n [- (unit_vec n i) :: 'a vec]) (?f ` (I - {0..<nr})) J =
          submatrix (mat_of_rows n [(- (unit_vec n i) :: 'a vec)]) {0} J" 
          by (metis 17 18)
        have 20: "B = submatrix A I J @\<^sub>r 
                      submatrix (mat_of_rows n [(- (unit_vec n i) :: 'a vec)]) {0} J" 
          by (simp add: 10 19)
        have 21: "B = submatrix A I J @\<^sub>r
                   mat_of_rows (card ({0..<n} \<inter> J)) 
                   [vec_of_list (nths (list_of_vec ((- (unit_vec n i) :: 'a vec))) J)]"
          by (simp add: 20 submatrix_one_row_mat_of_rows)
        have 12:"(- (unit_vec n i) :: 'a vec) \<in> carrier_vec n" 
          using uminus_carrier_vec unit_vec_carrier by blast
        then have "row (submatrix A I J @\<^sub>r
                   mat_of_rows (card ({0..<n} \<inter> J)) 
                   [vec_of_list (nths (list_of_vec (- (unit_vec n i) :: 'a vec)) J)]) 
                  (dim_row (submatrix A I J)) = 
                  vec_of_list (nths (list_of_vec ((- (unit_vec n i) :: 'a vec))) J)"
          by (smt (verit, best) A Collect_cong carrier_dim_vec carrier_matD(2) carrier_matI 
              dim_submatrix(2) dim_vec mat_of_rows_carrier(3) nths_list_pick_vec_same 
              row_apend_last_row submatrix_one_row_mat_of_rows)
        then have 22: "row B (dim_row B - 1) = 
                    vec_of_list (nths (list_of_vec (- (unit_vec n i) :: 'a vec)) J)"
          using row_apend_last_row 
          by (simp add: 21 append_rows_def)
        have 5: "vec_of_list (nths (list_of_vec ((- (unit_vec n i) :: 'a vec))) J) =
                vec (card {ia. ia < dim_vec (- (unit_vec n i) :: 'a vec) \<and> ia\<in>J}) 
                (\<lambda> ia. (- (unit_vec n i) :: 'a vec) $ (pick J ia))"
          using nths_list_pick_vec_same[of "((- (unit_vec n i) :: 'a vec))" J]
          by force
        then have 6:"\<forall> j < dim_col B. B $$ (dim_row B - 1,j) = 
                    (- (unit_vec n i) :: 'a vec) $ (pick J j)" 
          using 5 
          by (smt (verit, best) Matrix.row_def 22 index_vec row_carrier vec_carrier_vec)
        show ?thesis
        proof(cases "i < n")
          case True
          have 7: "\<forall> j < dim_col B. pick J j \<noteq> i \<longrightarrow>  B $$ (dim_row B - 1,j) = 0"
          proof safe
            fix k
            assume asm: "k < dim_col B" "pick J k \<noteq> i"
            have "pick J k < n" using 12 
                "5" Collect_cong 22 asm(1)  pick_le row_carrier vec_carrier_vec 
              by (metis (no_types, lifting) carrier_vecD)
            have 8:"- Matrix.vec n (\<lambda>j. if j = i then 1 else (0::'a)) = 
           Matrix.vec n (\<lambda>j. if j = i then - 1 else (0::'a))"
            proof rule
              show "dim_vec (- Matrix.vec n (\<lambda>j. if j = i then 1 else (0::'a))) =
                    dim_vec (Matrix.vec n (\<lambda>j. if j = i then - 1 else (0::'a)))"
                by simp
              fix ia
              assume asm: "ia < dim_vec (Matrix.vec n (\<lambda>j. if j = i then - 1 else (0::'a)))"
              show "(- Matrix.vec n (\<lambda>j. if j = i then 1 else (0::'a))) $v ia =
                    Matrix.vec n (\<lambda>j. if j = i then - 1 else (0::'a)) $v ia"
              proof(cases "ia = i")
                case True
                then show ?thesis 
                  using \<open>ia < dim_vec (Matrix.vec n (\<lambda>j. if j = i then - 1 else 0))\<close> by auto
              next
                case False
                have 23: "(- Matrix.vec n (\<lambda>j. if j = i then 1 else (0::'a))) $v ia = - (0::'a)"
                  using False asm by force
                have "(Matrix.vec n (\<lambda>j. if j = i then - 1 else (0::'a))) $v ia = (0::'a)"
                  using False asm by auto
                then show ?thesis  
                  using 23 by linarith
              qed
            qed
            have "((- (unit_vec n i) :: 'a vec)) $ (pick J k) = 0"
              unfolding uminus_vec_def unit_vec_def using 8 
              by (simp add: \<open>pick J k < n\<close> asm(2))
            then show " B $$ (dim_row B - 1, k) = 0" 
              using "6" asm(1) by auto
          qed
          have 24: "\<forall> j < dim_col B. pick J j = i \<longrightarrow>  B $$ (dim_row B - 1,j) = (- 1 :: 'a)"
            using "6" True by auto
          show ?thesis 
          proof(cases "\<exists>j. j < dim_col B \<and> pick J j = i")
            case True
            obtain j where j: "pick J j = i \<and> j < dim_col B" 
              using True by blast
            have "B $$ (dim_row B - 1,j) = - 1" 
              using 24 \<open>pick J j = i \<and> j < dim_col B\<close> by presburger
            have 27: "\<forall> k < dim_col B. k \<noteq> j \<longrightarrow>  B $$ (dim_row B - 1,k) = 0" 
            proof safe
              fix k
              assume asm: "k < dim_col B" " k \<noteq> j"
              have "pick J k \<noteq> i" 
              proof(rule ccontr)
                assume asm_not_eq: "\<not> pick J k \<noteq> i"
                then have "pick J k = pick J j" 
                  using j by fastforce
                show False
                proof(cases "infinite J")
                  case True
                  then show ?thesis 
                    using \<open>pick J k = pick J j\<close> asm(2) pick_eq_iff_inf by blast
                next
                  case False
                  have "dim_col B = 
                        card {ia. ia < dim_col (A @\<^sub>r mat_of_rows n [- unit_vec n i]) \<and> ia \<in> J}" 
                    using I_J dim_submatrix(2)
                    by blast
                  then have 26: "dim_col B = (card {ia. ia<n \<and> ia\<in>J})" 
                    by (metis "12" 25 carrier_vecD index_row(2))
                  then have "j < card J" 
                    by (metis (mono_tags, lifting) \<open>pick J k = pick J j\<close> asm(2) pick_eq_iff_inf
                        basic_trans_rules(21) card_mono j mem_Collect_eq not_less  subsetI)
                  then show ?thesis 
                    by (metis (mono_tags, lifting) False asm_not_eq 26 asm(1-2) mem_Collect_eq  
                        basic_trans_rules(21)  j nat_neq_iff not_less pick_mono subsetI card_mono)
                qed
              qed
              then show " B $$ (dim_row B - 1, k) = 0" 
                using "7" asm(1) by presburger
            qed
            have "\<forall>k \<in> {0..<dim_col B}. j\<noteq>k \<longrightarrow>  B $$ (dim_row B - 1,k) = 0" 
              using 27 atLeastLessThan_iff by blast
            then have "(\<Sum>j \<in> {0..<dim_col B}. B $$ (dim_row B - 1,j) * 
                        cofactor B (dim_row B - 1) j) =
                        B $$ (dim_row B - 1,j) * cofactor B (dim_row B - 1) j" 
              using only_one_nonzero_is_sum[of "{0..<dim_col B}" j]
              by (metis (no_types, lifting) atLeast0LessThan finite_atLeastLessThan j lessThan_iff 
                  vector_space_over_itself.scale_eq_0_iff)
            then have "(\<Sum>j<dim_col B. B $$ (dim_row B - 1,j) * cofactor B (dim_row B - 1) j) =
              B $$ (dim_row B - 1,j) * cofactor B (dim_row B - 1) j" 
              by (metis atLeast0LessThan)
            then have 28: "det B =  B $$ (dim_row B - 1,j) * cofactor B (dim_row B - 1) j"
              by (metis "4" \<open>dim_row B = dim_col B\<close>)
            then have 29: "det B = - cofactor B (dim_row B - 1) j" 
              by (metis \<open>B $$ (dim_row B - 1, j) = - 1\<close> mult_minus1)
            have 8: "cofactor B (dim_row B - 1) j = 
                (-1)^((dim_row B - 1)+j) * det (mat_delete B (dim_row B - 1) j)" 
              by (meson Determinant.cofactor_def)
            have " - unit_vec n i \<in> carrier_vec n" 
              by simp
            then have "vec_of_list (nths (list_of_vec (- unit_vec n i)) J) \<in> 
                       carrier_vec (dim_col (submatrix A I J))"
              by (smt (verit) A Collect_cong carrier_dim_vec carrier_matD(2) dim_submatrix(2)
                  dim_vec nths_list_pick_vec_same)
            then have 9:"mat_delete B (dim_row B - 1) j = submatrix A I (J - {pick J j})"
              using mat_delete_last_row_submatrix 10 22 19
              by (smt (verit, best) "12" "5" Collect_cong assms(1) carrier_vecD dim_submatrix(1) 
                  dim_submatrix(2) submatrix_one_row_mat_of_rows index_row(2) j mat_delete_dim(1) 
                  mat_of_rows_carrier(3) vec_carrier_vec)
            have "det (submatrix A I (J - {pick J j})) \<in> {-1, 0, 1}" 
              using assms(2) unfolding tot_unimodular_def 
              by blast
            then  have "det (mat_delete B (dim_row B - 1) j) \<in> {-1, 0, 1}" 
              using "9" by presburger 
            then have "cofactor B (dim_row B - 1) j \<in> {-1, 0, 1}" 
              by (smt (verit, best) "8" R.minus_equality UNIV_I add_neg_numeral_special(7) 
                  cring_simprules(28) insertCI insertE mult_cancel_right2 mult_minus1_right 
                  nat_pow_distrib singletonD square_eq_one)
            then show ?thesis 
              using `det B = - cofactor B (dim_row B - 1) j` by auto
          next
            case False
            then have "\<forall> j < dim_col B. B $$ (dim_row B - 1,j) = 0"
              using "7" by blast
            then have "det B = 0" 
              by (simp add: "4" \<open>dim_row B = dim_col B\<close>)
            then show ?thesis by auto
          qed
        next
          case False
          have 13:"unit_vec n i \<in> carrier_vec n" 
            by simp
          have 14:"unit_vec n i = 0\<^sub>v n" 
            unfolding unit_vec_def  zero_vec_def 
            using False by fastforce
          have "((- unit_vec n i) :: 'a vec) = 0\<^sub>v n"
            using uminus_vec_if_zero[OF 13 14] 
            by simp
          then have "\<forall> j < dim_col B. B $$ (dim_row B - 1,j) = 0" 
            using 6 "5" Collect_cong 22  carrier_vecD index_row(2)  index_zero_vec(1) 
              pick_le vec_carrier 
            by (smt (verit, ccfv_SIG) index_uminus_vec(2) index_unit_vec(3))
          then show ?thesis using 4 
            by (simp add: \<open>dim_row B = dim_col B\<close>)
        qed
      next
        case False
        have 3:"dim_row (mat_of_rows n [(- unit_vec n i):: 'a vec]) =  1" 
          using 1 
          by fast
        have 31: "submatrix (mat_of_rows n [(- unit_vec n i):: 'a vec]) (?f ` (I - {0..<nr})) J =
            submatrix (mat_of_rows n [(- unit_vec n i):: 'a vec]) (?f ` (I - {0..<nr})\<inter>{0..<1}) J"
          using submatrix_inter_rows' 3 
          by metis
        have 30: "?f ` (I - {0..<nr}) \<inter> {0..<1} = {}" 
          apply safe 
          apply simp+
          using False by auto
        have 32: "submatrix (mat_of_rows n [(- unit_vec n i):: 'a vec]) (?f ` (I - {0..<nr})) J = 
            submatrix (mat_of_rows n [- unit_vec n i]) {} J" 
          by (metis 30 31)
        then have 11: "submatrix (mat_of_rows n [- unit_vec n i]) {} J = 
          0\<^sub>m 0 (dim_col (submatrix (mat_of_rows n [- unit_vec n i]) (?f ` (I - {0..<nr})) J))"
          using empty_set_submatrix_iz_zero_mat 
          by (smt (verit) Collect_cong dim_submatrix(2) mat_of_rows_carrier(3))
        have "B = submatrix A I J" 
          apply rule
            apply (metis "10" append_rows_def index_mat_four_block(1) trans_less_add1)
           apply (metis (no_types, lifting) "10" "11" 32 add.right_neutral append_rows_def 
              index_mat_four_block(2) index_zero_mat(2))
          using A  I_J 25 carrier_matD(2) dim_submatrix(2) index_row(2) index_unit_vec(3)
          by (metis (mono_tags) index_uminus_vec(2))
        then show ?thesis
          using assms(2) unfolding tot_unimodular_def by auto
      qed
    qed
  qed
qed

lemma submatrix_minus_last_row_carr:
  fixes A :: "'a  mat"
  assumes A: "A \<in> carrier_mat nr n"
  shows "submatrix A {0..<nr-1} UNIV \<in> carrier_mat (nr-1) n"
proof
  show "dim_row (submatrix A {0..<nr - 1} UNIV) = nr - 1" 
  proof -
    have "dim_row (submatrix A {0..<nr-1} UNIV) = card {i. i<dim_row A \<and> i\<in>{0..<nr-1}}" 
      using dim_submatrix(1) by blast
    moreover have "{i. i<dim_row A \<and> i\<in>{0..<nr-1}} = {i. i<nr \<and> i\<in>{0..<nr-1}}" 
      using A by blast
    moreover have "{i. i<nr \<and> i\<in>{0..<nr-1}} = {0..<nr-1}" 
      apply safe
      by simp
    ultimately show ?thesis 
      using card_atLeastLessThan minus_nat.diff_0 by presburger
  qed
  show "dim_col (submatrix A {0..<nr - 1} UNIV) = n" 
    using A dim_col_submatrix_UNIV by blast
qed

lemma append_last_row_submatrix_is_mat:
  fixes A :: "'a  mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes "nr > 0"
  shows "A = (submatrix A {0..<nr-1} UNIV) @\<^sub>r (mat_of_rows n [row A (nr-1)])"
proof 
  have 6: "dim_row (submatrix A {0..<nr - 1} UNIV @\<^sub>r mat_of_rows n [Matrix.row A (nr - 1)]) = nr" 
    using submatrix_minus_last_row_carr[OF A]
    by (metis (no_types, lifting) One_nat_def Suc_eq_plus1 append_rows_def assms(2) carrier_matD(1)
        discrete index_mat_four_block(2) index_zero_mat(2) le_add_diff_inverse2 list.size(3) 
        list.size(4) mat_of_rows_carrier(2)) 
  then show 5: "dim_row A = dim_row (submatrix A {0..<nr - 1} UNIV @\<^sub>r 
                         mat_of_rows n [Matrix.row A (nr - 1)])"
    by (metis assms(1) carrier_matD(1))
  show 4: "dim_col A = dim_col (submatrix A {0..<nr - 1} UNIV @\<^sub>r
                    mat_of_rows n [Matrix.row A (nr - 1)])" 
    by (metis assms(1) carrier_matD(2) row_apend_last_row index_row(2)
        submatrix_minus_last_row_carr row_carrier)
  fix i j
  assume asmi: "i < dim_row (submatrix A {0..<nr - 1} UNIV @\<^sub>r 
                             mat_of_rows n [Matrix.row A (nr - 1)])"
  assume asmj: "j < dim_col (submatrix A {0..<nr - 1} UNIV @\<^sub>r
                     mat_of_rows n [Matrix.row A (nr - 1)])"
  show "A $$ (i, j) = (submatrix A {0..<nr - 1} UNIV @\<^sub>r 
                       mat_of_rows n [Matrix.row A (nr - 1)]) $$ (i, j)"
  proof(cases "i < nr-1")
    case True
    have 3: "row (submatrix A {0..<nr - 1} UNIV @\<^sub>r mat_of_rows n [Matrix.row A (nr - 1)]) i = 
          row (submatrix A {0..<nr - 1} UNIV) i" 
      by (meson Missing_Matrix.append_rows_nth(1) True assms(1) mat_of_rows_carrier(1) 
          submatrix_minus_last_row_carr)
    have 2: "row (submatrix A {0..<nr - 1} UNIV) i = row A (pick  {0..<nr - 1} i)"
      using row_submatrix_UNIV[of i A "{0..<nr - 1}"]
      by (metis (no_types, lifting) A True carrier_matD(1) dim_submatrix(1) 
          submatrix_minus_last_row_carr row_submatrix_UNIV)
    have "i \<in> {0..<nr - 1}" using True 
      by simp
    then have 1: "pick {0..<nr - 1} (card {a \<in> {0..<nr - 1}. a < i}) = i" 
      using pick_card_in_set by presburger
    have "{a \<in> {0..<nr - 1}. a < i} = {0..< i}"
      apply safe 
      using atLeastLessThan_iff apply blast
      using True by auto+
    then have "card {a \<in> {0..<nr - 1}. a < i} = i" 
      by force
    then have "(pick  {0..<nr - 1} i) = i" 
      using 1 by presburger
    then have "row A i = row (submatrix A {0..<nr - 1} UNIV) i" 
      using 2 by presburger
    then show ?thesis 
      by (metis 3 4 5 asmi asmj index_row(1))
  next
    case False
    have "i = nr - 1" 
      using False 6 asmi by linarith
    then show ?thesis 
      by (metis 4 5 asmi asmj assms(1) carrier_matD(2) row_apend_last_row index_row(1)
          submatrix_minus_last_row_carr row_carrier)
  qed
qed

lemma append_mat_assoc:
  fixes A :: "'a  mat"
  assumes A: "A \<in> carrier_mat nr1 n" 
  assumes B: "B \<in> carrier_mat nr2 n"
  assumes C: "C \<in> carrier_mat nr3 n"
  shows "A @\<^sub>r (B @\<^sub>r C) = (A @\<^sub>r B) @\<^sub>r C" 
proof
  show 4: "dim_row (A @\<^sub>r B @\<^sub>r C) = dim_row ((A @\<^sub>r B) @\<^sub>r C)" 
    by (simp add: append_rows_def)
  show 3: "dim_col (A @\<^sub>r B @\<^sub>r C) = dim_col ((A @\<^sub>r B) @\<^sub>r C)" 
    by (smt (verit, ccfv_SIG) C assms(1-2) carrier_append_rows carrier_matD(2))
  fix i j
  assume asmi: "i < dim_row ((A @\<^sub>r B) @\<^sub>r C)"
  assume asmj: "j < dim_col ((A @\<^sub>r B) @\<^sub>r C)"
  show "(A @\<^sub>r B @\<^sub>r C) $$ (i, j) = ((A @\<^sub>r B) @\<^sub>r C) $$ (i, j)" 
  proof(cases "i < nr1 + nr2")
    case True
    have 1: "row ((A @\<^sub>r B) @\<^sub>r C) i = row (A @\<^sub>r B) i" 
      by (meson Missing_Matrix.append_rows_nth(1) True assms carrier_append_rows)
    show ?thesis 
    proof(cases "i < nr1")
      case True
      have 2: "row (A @\<^sub>r B @\<^sub>r C) i = row A i" 
        by (metis True append_rows_index_same assms carrier_append_rows carrier_matD(1))
      have "row (A @\<^sub>r B) i = row A i" 
        using Missing_Matrix.append_rows_nth(1) True assms(1-2) by blast
      then show ?thesis 
        by (metis 1 2 3 4 asmi asmj index_row(1))
    next
      case False
      have 5: "row (A @\<^sub>r B) i = row B (i - nr1)" 
        by (meson B False True assms(1) gram_schmidt.append_rows_index_same' not_le)
      have "row (A @\<^sub>r B @\<^sub>r C) i = row (B @\<^sub>r C) (i - nr1)" 
        by (smt (verit, ccfv_SIG) B C False 4 add_diff_inverse_nat append_rows_def 
            append_rows_index_same append_rows_index_same' asmi assms(1) carrier_matD(1)
            carrier_matD(2) carrier_matI index_mat_four_block(2) index_row(2) index_zero_mat(2) 
            nat_add_left_cancel_less not_less)
      then show ?thesis 
        by (metis (no_types, lifting) B C False True 1 5 3 4 add_diff_inverse_nat 
            append_rows_index_same asmi asmj carrier_matD(1) index_row(1) nat_add_left_cancel_less)
    qed
  next
    case False
    have "i \<ge> nr1" 
      using False by linarith
    have 6: "B @\<^sub>r C \<in> carrier_mat (nr2 + nr3) n" 
      using assms(2) assms(3) by blast
    have "i < nr1 + nr2 + nr3" 
      by (metis append_rows_def asmi assms carrier_matD(1) 
          index_mat_four_block(2) index_zero_mat(2))
    have 7: "row (A @\<^sub>r B @\<^sub>r C) i = row (B @\<^sub>r C) (i - nr1)" 
      using append_rows_nth(2)[of A nr1 n "B @\<^sub>r C" "nr2 + nr3" i]
      by (metis Groups.add_ac(1) 6 \<open>i < nr1 + nr2 + nr3\<close> \<open>nr1 \<le> i\<close>  assms(1))
    have 1:"i - nr1 \<ge> nr2" 
      using False by linarith
    have 8: "row (B @\<^sub>r C) (i - nr1) = row C (i - (nr1+nr2))" 
      using append_rows_nth(2)[OF B C 1] 
      by (metis \<open>i < nr1 + nr2 + nr3\<close> \<open>nr1 \<le> i\<close> add.assoc add.commute diff_diff_eq less_diff_conv2)
    have "row ((A @\<^sub>r B) @\<^sub>r C) i = row C (i - (nr1+nr2))"
      using append_rows_nth(2)[of "A @\<^sub>r B" "nr1+nr2" n C nr3 i] 
      by (meson False \<open>i < nr1 + nr2 + nr3\<close> assms carrier_append_rows leI)
    then show ?thesis 
      by (metis 7 8 3 4 asmi asmj index_row(1))
  qed
qed

lemma append_mat_empty:
  fixes A :: "'a  mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes B: "B \<in> carrier_mat 0 n"
  shows "A @\<^sub>r B = A" 
proof
  show 2: "dim_row (A @\<^sub>r B) = dim_row A" 
    by (metis add_cancel_right_right append_rows_def assms(2) carrier_matD(1)
        index_mat_four_block(2) index_zero_mat(2))
  show 1: "dim_col (A @\<^sub>r B) = dim_col A" 
    using assms(1) assms(2) carrier_matD(2) by blast
  fix i j
  assume asmi: "i < dim_row A" 
  assume asmj: "j < dim_col A" 
  show "(A @\<^sub>r B) $$ (i, j) = A $$ (i, j)" 
  proof(cases "i < nr")
    case True
    have "row (A @\<^sub>r B) i = row A i" 
      using Missing_Matrix.append_rows_nth(1) True assms(1) assms(2) by blast
    then show ?thesis 
      by (metis 1 2 asmi asmj index_row(1))
  next
    case False
    then show ?thesis 
      using A asmi by blast
  qed
qed

lemma tot_unimod_append_unit_vec_mat:
  fixes A :: "'a  mat"
  assumes A: "A \<in> carrier_mat nr1 n"
  assumes B: "B \<in> carrier_mat nr2 n"
  assumes "tot_unimodular A"
  assumes "\<forall> i < nr2. \<exists> j. row B i = unit_vec n j"
  shows "tot_unimodular (A @\<^sub>r B)"
  using assms(2,4)
proof(induct nr2 arbitrary: B)
  case 0
  have "A @\<^sub>r B = A" using  append_mat_empty 
    using "0"(1) assms(1) by blast
  then show ?case 
    using assms(3) by fastforce
next
  case (Suc nr2)
  have 1: "B = (submatrix B {0..<nr2} UNIV) @\<^sub>r (mat_of_rows n [row B (nr2)])" 
    using append_last_row_submatrix_is_mat 
    by (metis Suc(2) diff_add_inverse plus_1_eq_Suc zero_less_Suc)
  have 2: "submatrix B {0..<nr2} UNIV \<in> carrier_mat nr2 n" 
    by (metis Suc(2) diff_Suc_1 submatrix_minus_last_row_carr)
  have 3: "\<forall> i < nr2. \<exists> j. row (submatrix B {0..<nr2} UNIV) i = unit_vec n j"
  proof safe
    fix i
    assume asmi: "i < nr2"
    obtain k where k: "row (submatrix B {0..<nr2} UNIV) i = row B k \<and> k < dim_row B" 
      by (smt (verit, best) Missing_Matrix.append_rows_nth(1) Suc(2) 1 2 asmi basic_trans_rules(19) 
          carrier_matD(1) lessI mat_of_rows_carrier(1))
    then have "\<exists>j. row B k = unit_vec n j" 
      by (metis Suc(2) Suc(3) carrier_matD(1))
    then show "\<exists>j. Matrix.row (submatrix B {0..<nr2} UNIV) i = unit_vec n j"
      using k  by presburger
  qed
  have "tot_unimodular (A @\<^sub>r (submatrix B {0..<nr2} UNIV))" 
    using Suc.hyps 3 2 by presburger
  have 4: "A @\<^sub>r B = (A @\<^sub>r (submatrix B {0..<nr2} UNIV)) @\<^sub>r (mat_of_rows n [row B (nr2)])" 
    by (metis (no_types, lifting) 1 2 assms(1) mat_of_rows_carrier(1) append_mat_assoc)
  obtain j where j: "row B nr2 = unit_vec n j" 
    using Suc(3) by blast
  then have "(A @\<^sub>r (submatrix B {0..<nr2} UNIV)) @\<^sub>r (mat_of_rows n [row B (nr2)]) = 
             (A @\<^sub>r (submatrix B {0..<nr2} UNIV)) @\<^sub>r (mat_of_rows n [unit_vec n j])" 
    by presburger
  then show ?case 
    by (metis 4 2 \<open>tot_unimodular (A @\<^sub>r submatrix B {0..<nr2} UNIV)\<close> assms(1) carrier_append_rows
        gram_schmidt_floor.tot_unimod_append_unit_vec)
qed

lemma tot_unimod_append_minus_unit_vec_mat:
  fixes A :: "'a  mat"
  assumes A: "A \<in> carrier_mat nr1 n"
  assumes B: "B \<in> carrier_mat nr2 n"
  assumes "tot_unimodular A"
  assumes "\<forall> i < nr2. \<exists> j. row B i = - unit_vec n j"
  shows "tot_unimodular (A @\<^sub>r B)"
  using assms(2,4)
proof(induct nr2 arbitrary: B)
  case 0
  have "A @\<^sub>r B = A" using  append_mat_empty 
    using "0"(1) assms(1) by blast
  then show ?case 
    using assms(3) by fastforce
next
  case (Suc nr2)
  have 1: "B = (submatrix B {0..<nr2} UNIV) @\<^sub>r (mat_of_rows n [row B (nr2)])" 
    using append_last_row_submatrix_is_mat 
    by (metis Suc(2) diff_add_inverse plus_1_eq_Suc zero_less_Suc)
  have 2: "submatrix B {0..<nr2} UNIV \<in> carrier_mat nr2 n" 
    by (metis Suc(2) diff_Suc_1 submatrix_minus_last_row_carr)
  have 3: "\<forall> i < nr2. \<exists> j. row (submatrix B {0..<nr2} UNIV) i = - unit_vec n j"
  proof safe
    fix i
    assume asmi: "i < nr2"
    obtain k where k: "row (submatrix B {0..<nr2} UNIV) i = row B k \<and> k < dim_row B" 
      by (smt (verit, best) Missing_Matrix.append_rows_nth(1) Suc(2) 1 2 asmi basic_trans_rules(19)
          carrier_matD(1) lessI mat_of_rows_carrier(1))
    then have "\<exists>j. row B k = - unit_vec n j" 
      by (metis Suc(2) Suc(3) carrier_matD(1))
    then show "\<exists>j. Matrix.row (submatrix B {0..<nr2} UNIV) i = - unit_vec n j"
      using k by presburger
  qed
  have 5: "tot_unimodular (A @\<^sub>r (submatrix B {0..<nr2} UNIV))" 
    using Suc.hyps 3 2 by presburger
  have 4: "A @\<^sub>r B = (A @\<^sub>r (submatrix B {0..<nr2} UNIV)) @\<^sub>r (mat_of_rows n [row B (nr2)])" 
    by (metis (no_types, lifting) 1 2 assms(1) mat_of_rows_carrier(1) append_mat_assoc)
  obtain j where "row B nr2 = - unit_vec n j" 
    using Suc(3) by blast
  then have "(A @\<^sub>r (submatrix B {0..<nr2} UNIV)) @\<^sub>r (mat_of_rows n [row B (nr2)]) = 
            (A @\<^sub>r (submatrix B {0..<nr2} UNIV)) @\<^sub>r (mat_of_rows n [- unit_vec n j])" 
    by presburger
  then show ?case 
    by (metis 4 2 5 assms(1) carrier_append_rows tot_unimod_append_minus_unit_vec)
qed

lemma tot_unimod_append_one:
  fixes A :: "'a  mat"
  assumes A: "A \<in> carrier_mat nr1 n"
  assumes "tot_unimodular A"
  shows "tot_unimodular (A @\<^sub>r 1\<^sub>m n)" 
proof -
  have 1:"1\<^sub>m n \<in> carrier_mat n n" 
    by simp
  have "\<forall> i < n. row (1\<^sub>m n) i = unit_vec n i" 
    by simp
  then have 2: "\<forall> i < n. \<exists> j. row (1\<^sub>m n) i = unit_vec n j" 
    by blast
  then show ?thesis
    using tot_unimod_append_unit_vec_mat[OF assms(1) 1 assms(2) 2] by auto
qed

lemma tot_unimod_append_minus_one:
  fixes A :: "'a  mat"
  assumes A: "A \<in> carrier_mat nr1 n" 
  assumes "tot_unimodular A"
  shows "tot_unimodular (A @\<^sub>r - 1\<^sub>m n)"
proof -
  have 1:" - 1\<^sub>m n \<in> carrier_mat n n" 
    by simp
  have "\<forall> i < n. row (- 1\<^sub>m n) i = - unit_vec n i" 
    by simp
  then have 2: "\<forall> i < n. \<exists> j. row (- 1\<^sub>m n) i = - unit_vec n j" 
    by blast
  then show ?thesis
    using tot_unimod_append_minus_unit_vec_mat[OF assms(1) 1 assms(2)] by auto
qed

lemma totally_unimod_mat_int:
  assumes "tot_unimodular A"
  shows "A \<in> \<int>\<^sub>m "
proof -
  have "\<forall> i < dim_row A. \<forall> j < dim_col A. A $$ (i, j) \<in> {-1, 0, 1}" 
  proof safe
    fix i j
    assume asm: "i < dim_row A" "j < dim_col A" "A $$ (i, j) \<noteq> - 1"
      "A $$ (i, j) \<noteq> 0" "A $$ (i, j) \<notin> {}"
    have 6: "det (submatrix A {i} {j}) \<in> {- 1, 0, 1}" 
      using assms tot_unimodular_def by blast
    have 2: "{k. k<dim_row A \<and> k\<in>{i}} = {i}" 
      using \<open>i < dim_row A\<close> by blast
    have 1: "{k. k<dim_col A \<and> k\<in>{j}} = {j}" 
      using \<open>j < dim_col A\<close> by blast
    have 3: "(submatrix A {i} {j}) = mat 1 1 ((\<lambda>(i1,j1). A $$ (pick {i} i1, pick {j} j1)))"
      unfolding submatrix_def
      using 1 2 by force
    then have 4: "det (submatrix A {i} {j}) = (submatrix A {i} {j}) $$ (0,0)"
      using determinant_one_element 
      by (metis mat_carrier)
    have 5: "(submatrix A {i} {j}) $$ (0,0) =  A $$ (pick {i} 0, pick {j} 0)" 
      by (simp add: 3)
    have "pick {i} 0 = i" 
      by (metis card_eq_1_iff less_one pick_in_set singletonD)
    have "pick {j} 0 = j" 
      by (metis card_eq_1_iff less_one pick_in_set singletonD)
    then have "det (submatrix A {i} {j}) = A $$ (i, j)" 
      using 4 5 \<open>pick {i} 0 = i\<close> by presburger
    then show "A $$ (i, j) = 1" 
      using 6 asm(3) asm(4) by fastforce
  qed
  then have "\<forall> i < dim_row A. \<forall> j < dim_col A. A $$ (i, j) \<in> \<int>" 
    by fastforce
  then show ?thesis 
    using Ints_mat_def by blast
qed

lemma tot_unimod_then_int_polyhedron:
  fixes A :: "'a  mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes tot_unimod: "tot_unimodular A"
  shows "\<forall> b \<in> carrier_vec nr. b \<in> \<int>\<^sub>v \<longrightarrow> int_polyh (pos_polyhedron A b)"
proof rule+
  fix b :: "'a vec"
  assume "b \<in> carrier_vec nr"
  assume "b \<in> \<int>\<^sub>v"
  show "int_polyh (pos_polyhedron A b)"
    unfolding int_polyh_def
  proof -
    let ?fullA = "A @\<^sub>r - 1\<^sub>m n"
    let ?fullb = "b @\<^sub>v 0\<^sub>v n" 
    have 1:"?fullA \<in> carrier_mat (nr+n) n" 
      by (meson assms(1) carrier_append_rows one_carrier_mat uminus_carrier_iff_mat)
    have 2:"?fullb \<in> carrier_vec (nr+n)" 
      by (simp add: \<open>b \<in> carrier_vec nr\<close>)
    have AI: "A \<in> \<int>\<^sub>m" 
      using totally_unimod_mat_int tot_unimod by auto
    then have 3:"?fullA \<in> \<int>\<^sub>m" 
      by (meson assms(1) gram_schmidt.append_int_mat_is_int gram_schmidt.one_mat_int
          minus_in_Ints_mat_iff one_carrier_mat uminus_carrier_iff_mat)
    have 4:"?fullb \<in> \<int>\<^sub>v" 
      using \<open>b \<in> \<int>\<^sub>v\<close> \<open>b \<in> carrier_vec nr\<close> append_int_vec_is_int zero_vec_is_int by blast
    have " integer_hull (polyhedron ?fullA ?fullb) = polyhedron ?fullA ?fullb"
    proof(cases "polyhedron ?fullA ?fullb = {}")
      case True
      have "integer_hull {} = {}" 
        by (simp add: integer_hull_def)
      then show ?thesis 
        using True by presburger
    next
      case False
      have 5: "\<forall>x \<in> (polyhedron ?fullA ?fullb). \<forall> i < n. x $ i \<ge> 0" 
        using pos_polyh_is_polyh
        unfolding pos_polyhedron_def polyhedron_def 
        by (metis (no_types, lifting) \<open>b \<in> carrier_vec nr\<close> assms(1) index_zero_vec(1) 
            lesseq_vecD mem_Collect_eq)
      then have 6: "(\<forall>x\<in>local.polyhedron (A @\<^sub>r - 1\<^sub>m n) (b @\<^sub>v 0\<^sub>v n). \<forall>i<n. x $v i \<le> 0) \<or>
                    (\<forall>x\<in>local.polyhedron (A @\<^sub>r - 1\<^sub>m n) (b @\<^sub>v 0\<^sub>v n). \<forall>i<n. 0 \<le> x $v i)" 
        by blast
      have "(\<forall> F. min_face (polyhedron ?fullA ?fullb) F \<longrightarrow> (\<exists> x \<in> F. x \<in> \<int>\<^sub>v))"
      proof safe
        fix F
        assume asm: "min_face (polyhedron ?fullA ?fullb) F"
        obtain A' b' I'  where A'b':"((A', b') = sub_system ?fullA ?fullb I')" 
          " F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'}"
          "dim_vec b' = Min {dim_vec d| C d I. F = {x. x \<in> carrier_vec n \<and> C *\<^sub>v x = d} \<and> 
                                           (C, d) = sub_system ?fullA ?fullb I}"
          using min_face_min_subsyst[OF 1 2] 
          using \<open>min_face (local.polyhedron (A @\<^sub>r - 1\<^sub>m n) (b @\<^sub>v 0\<^sub>v n)) F\<close> 
          by (smt (z3) Collect_cong)
        have "\<exists> x \<in> F. abs(det A') \<cdot>\<^sub>v x \<in>  \<int>\<^sub>v" 
          using min_face_has_int[OF 1 2 3 4 False 6 asm] A'b'
          by blast
        have "det A' \<noteq> 0" 
          using bounded_min_faces_det_non_zero[OF 1 2 False 6 asm] A'b' by blast
        have 7:" \<exists> I J. submatrix ?fullA I J = A'" using A'b'(1)
          by (metis prod.sel(1) sub_system_fst)
        have "tot_unimodular ?fullA"
          using assms tot_unimod_append_minus_one by blast
        then have "det A' \<in> {-1, 0, 1}" unfolding tot_unimodular_def using 7 
          by presburger 
        then have "det A' = -1 \<or> det A' = 1"
          using \<open>Determinant.det A' \<noteq> 0\<close> by blast
        then have "abs (det A') = 1"
          by (metis abs_1 abs_neg_one)
        then have "\<exists> x \<in> F. 1 \<cdot>\<^sub>v x \<in>  \<int>\<^sub>v"
          using \<open>\<exists>x\<in>F. \<bar>Determinant.det A'\<bar> \<cdot>\<^sub>v x \<in> \<int>\<^sub>v\<close> by presburger
        then show "\<exists> x \<in> F. x \<in>  \<int>\<^sub>v"
          by auto
      qed
      then  show " integer_hull (polyhedron ?fullA ?fullb) = polyhedron ?fullA ?fullb"
        using min_face_iff_int_polyh[OF 1 2 3 4]
        by blast
    qed
    then show "integer_hull (pos_polyhedron A b) = pos_polyhedron A b"
      using pos_polyh_is_polyh
      using \<open>b \<in> carrier_vec nr\<close> assms(1) by presburger
  qed
qed

end
end