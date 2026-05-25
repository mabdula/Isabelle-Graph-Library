theory Misc
  imports "Directed_Set_Graphs.enat_misc" "HOL-Eisbach.Eisbach_Tools" "HOL-Library.FuncSet" 
          "HOL-Library.Disjoint_Sets" Main "Directed_Set_Graphs.More_Lists"
begin

subsection \<open>Misc\<close>

text\<open>Since one of the matchings is bigger, there must be one edge equivalence class
  that has more edges from the bigger matching.\<close>

lemma lt_sum:
  "(\<Sum>x\<in>s. g x) < (\<Sum>x\<in>s. f x) \<Longrightarrow> \<exists>(x::'a ) \<in> s. ((g::'a \<Rightarrow> nat) x < f x)"
  by (auto simp add: not_le[symmetric] intro: sum_mono)

lemma Union_lt:
  assumes finite: "finite S" "finite t" "finite u" and
    card_lt: "card ((\<Union> S) \<inter> t) < card ((\<Union> S) \<inter> u)" and 
    disj: "\<forall>s\<in>S.\<forall>s'\<in>S. s \<noteq> s' \<longrightarrow> s \<inter> s' = {}"
  shows "\<exists>s\<in>S. card (s \<inter> t) < card (s \<inter> u)"
proof-
  {
    fix t::"'a set"
    assume ass: "finite t"
    have "card (\<Union>s\<in>S. s \<inter> t) = (\<Sum>s\<in>S. card (s \<inter> t))"
      using ass disj
      by(fastforce intro!: card_UN_disjoint finite)
  }note * = this
  show ?thesis
    using card_lt *[OF finite(2)] *[OF finite(3)]
    by (auto intro: lt_sum)
qed

lemma finite_image_of_unordered_pairs:
  "finite G \<Longrightarrow> finite {f x y | x y. {x, y}\<in> G}"
proof(induction G rule: finite_induct)
  case (insert e F)
  show ?case 
  proof(cases "\<exists> x y. e = {x, y}")
    case True
    then obtain x y where e: "e = {x, y}"
      by auto
    show ?thesis 
      by(rule finite_subset[of _ "{f x y, f y x} \<union> {f x y |x y. {x, y} \<in> F} "])
        (insert insert, auto simp add: e doubleton_eq_iff)
  next
    case False
    show ?thesis
      apply(rule finite_subset[of _ "{f x y |x y. {x, y} \<in> F} "])
      using False insert
      by auto
  qed
qed auto

definition card' :: "'a set \<Rightarrow> enat" where
  "card' A = (if infinite A then \<infinity> else card A)"

lemma card'_finite: "finite A \<Longrightarrow> card' A = card A"
  unfolding card'_def by simp

lemma card'_mono: "A \<subseteq> B \<Longrightarrow> card' A \<le> card' B"
  using finite_subset
  by (auto simp add: card'_def intro: card_mono)

lemma card'_empty[iff]: "(card' A = 0) \<longleftrightarrow> A = {}"
  unfolding card'_def using enat_0_iff(2) by auto

lemma card'_finite_nat[iff]: "(card' A = numeral m) \<longleftrightarrow> (finite A \<and> card A = numeral m)"
  unfolding card'_def
  by (simp add: numeral_eq_enat)

(*TODO: remove the enat notions*)

lemma card'_finite_enat[iff]: "(card' A = enat m) \<longleftrightarrow> (finite A \<and> card A = m)"
  unfolding card'_def by simp

lemma card'_1_singletonE:
  assumes "card' A = 1"
  obtains x where "A = {x}"
  using assms
  unfolding card'_def
  by (fastforce elim!: card_1_singletonE dest: iffD1[OF enat_1_iff(1)] split: if_splits)

lemma card'_insert[simp]: "card' (insert a A) = (if a \<in> A then id else eSuc) (card' A)"
  using card_insert_if finite_insert
  by (simp add: card_insert_if card'_def)

lemma card'_empty_2[simp]: "card' {} = enat 0"
  by (simp add: card'_def)

lemma card'_subset: "\<lbrakk>A \<subset> B; finite A\<rbrakk> \<Longrightarrow> card' A < card' B"
  by(auto intro!: psubset_card_mono simp add: card'_def)

lemma exists_conj_elim_2_1: "\<lbrakk>\<And>x. \<lbrakk>P x; Q x\<rbrakk> \<Longrightarrow> V x; \<lbrakk>\<And>x. P x \<and> Q x \<Longrightarrow> V x\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S"
  by auto

lemma exists_conj_elim_3_1: "\<lbrakk>\<And>x. \<lbrakk>P x; Q x; V x\<rbrakk> \<Longrightarrow> W x; \<lbrakk>\<And>x. P x \<and> Q x \<and> V x \<Longrightarrow> W x\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S"
  by auto

lemma exists_conj_elim_4_1: "\<lbrakk>\<And>x. \<lbrakk>P x; Q x; V x; W x\<rbrakk> \<Longrightarrow> X x; \<lbrakk>\<And>x. P x \<and> Q x \<and> V x \<and> W x \<Longrightarrow> X x\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S"
  by auto

lemma exists_conj_elim_2_2: "\<lbrakk>\<And>x y. \<lbrakk>P x y; Q x y\<rbrakk> \<Longrightarrow> V x y; \<lbrakk>\<And>x y. P x y \<and> Q x y \<Longrightarrow> V x y\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S"
  by auto

lemma exists_conj_elim_3_2: "\<lbrakk>\<And>x y. \<lbrakk>P x y; Q x y; V x y\<rbrakk> \<Longrightarrow> W x y; \<lbrakk>\<And>x y. P x y \<and> Q x y \<and> V x y \<Longrightarrow> W x y\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S"
  by auto

lemma exists_conj_elim_4_2: "\<lbrakk>\<And>x y. \<lbrakk>P x y; Q x y; V x y; W x y\<rbrakk> \<Longrightarrow> X x y; \<lbrakk>\<And>x y. P x y \<and> Q x y \<and> V x y \<and> W x y \<Longrightarrow> X x y\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S"
  by auto

lemma exists_conj_elim_2_3: "\<lbrakk>\<And>x y z. \<lbrakk>P x y z; Q x y z\<rbrakk> \<Longrightarrow> V x y z; \<lbrakk>\<And>x y z. P x y z \<and> Q x y z \<Longrightarrow> V x y z\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S"
  by auto

lemma exists_conj_elim_3_3: "\<lbrakk>\<And>x y z. \<lbrakk>P x y z; Q x y z; V x y z\<rbrakk> \<Longrightarrow> W x y z; \<lbrakk>\<And>x y z. P x y z \<and> Q x y z \<and> V x y z \<Longrightarrow> W x y z\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S"
  by auto

lemma exists_conj_elim_4_3: "\<lbrakk>\<And>x y z. \<lbrakk>P x y z; Q x y z; V x y z; W x y z\<rbrakk> \<Longrightarrow> X x y z; \<lbrakk>\<And>x y z. P x y z \<and> Q x y z \<and> V x y z \<and> W x y z \<Longrightarrow> X x y z\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S"
  by auto

lemma exists_conj_elim_5_3: "\<lbrakk>\<And>x y z. \<lbrakk>P x y z; Q x y z; V x y z; W x y z; X x y z\<rbrakk> \<Longrightarrow> Y x y z; \<lbrakk>\<And>x y z. P x y z \<and> Q x y z \<and> V x y z \<and> W x y z \<and> X x y z \<Longrightarrow> Y x y z\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S"
  by auto

lemma exists_conj_elim_5_3': "\<lbrakk>\<And>x y z. \<lbrakk>P x y z; Q x y z; V x y z; W x y z; X x y z\<rbrakk> \<Longrightarrow> Y x y z; \<lbrakk>\<And>x y z. P x y z \<and> Q x y z \<and> V x y z \<and> W x y z \<and> X x y z \<Longrightarrow> Y x y z\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S"
  by auto

lemma exists_conj_elim_6_3: "\<lbrakk>\<And>x y z. \<lbrakk>P x y z; Q x y z; V x y z; W x y z; X x y z; Y x y z\<rbrakk> \<Longrightarrow> Z x y z; \<lbrakk>\<And>x y z. P x y z \<and> Q x y z \<and> V x y z \<and> W x y z \<and> X x y z \<and> Y x y z \<Longrightarrow> Z x y z\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S"
  by auto

method instsantiate_obtains =
  (match conclusion in "P" for P
     \<Rightarrow> \<open>(match premises in ass[thin]: "\<And>x. _ x \<Longrightarrow> P" \<Rightarrow> \<open>rule ass\<close>) |
         (match premises in ass[thin]: "\<And>x y. _ x y \<Longrightarrow> P" \<Rightarrow> \<open>rule ass\<close>)\<close>)

lemmas exists_conj_elims = exists_conj_elim_2_1 exists_conj_elim_3_1 exists_conj_elim_4_1
                           exists_conj_elim_2_2 exists_conj_elim_3_2 exists_conj_elim_4_2

lemma sum_inner_function_to_image:
  "inj_on g X \<Longrightarrow> sum (\<lambda> x. f (g x)) X = sum f (g ` X)"
  by (simp add: sum.reindex_cong)

lemma distinct_singleton_set: "distinct xs \<Longrightarrow> set xs = {x} \<longleftrightarrow> xs = [x]"
  by (induction xs arbitrary:) (fastforce simp add: neq_Nil_conv intro: ccontr[where P = "_ = []"])+

lemma empty_iff_card_0: "finite s \<Longrightarrow> s = {} \<longleftrightarrow> card s = 0"
  by auto

lemma in_singleton: "\<lbrakk>s = {x}; y \<in> s\<rbrakk> \<Longrightarrow> x = y"
  by auto

lemma reverse_pigeonhole:
  "\<lbrakk>finite X; (f ` X) \<subseteq> Y; card X < card Y\<rbrakk> \<Longrightarrow> \<exists>y \<in> Y. \<forall>x \<in> X. y \<noteq> f x"
  by (metis imageI less_le_not_le subset_eq surj_card_le)

definition "pair_list_distinct xs = 
(distinct xs \<and> (\<forall> x \<in> set xs. prod.swap x \<notin> set xs \<or> fst x = snd x))"

lemma pair_list_distinctI:
  "\<lbrakk>distinct xs; \<And> x. x \<in> set xs \<Longrightarrow>  prod.swap x \<notin> set xs \<or> fst x = snd x\<rbrakk>
    \<Longrightarrow> pair_list_distinct xs"
and pair_list_extended_distinctE:
  "pair_list_distinct xs \<Longrightarrow>
  (\<lbrakk>distinct xs; \<And> x. x \<in> set xs \<Longrightarrow>  prod.swap x \<notin> set xs \<or> fst x = snd x\<rbrakk> \<Longrightarrow> P)
    \<Longrightarrow> P"
  by(auto simp add: pair_list_distinct_def)

lemma pair_list_distinct_front[simp]: 
 "pair_list_distinct (x#xs) = (x \<notin> set xs \<and>  prod.swap x \<notin> set xs \<and> pair_list_distinct xs)"
  by(cases x)(auto simp add: pair_list_distinct_def)

lemma finite_union_singleton: 
  "finite A \<Longrightarrow> finite ({a}\<union>A)"
  by simp

lemma set_of_f_up_to_n_image:"{f i |i. i < n} = f ` {0..<n::nat}" 
  by auto

lemma inj_image_rev_mono:"\<lbrakk>inj f; f `A \<subseteq> f `B\<rbrakk> \<Longrightarrow> A \<subseteq> B"
  by (auto simp add: in_mono inj_image_subset_iff)

lemma not_in_imageE:
  "\<lbrakk>y \<notin> f ` X; (\<And> x. x \<in> X \<Longrightarrow> y = f x \<Longrightarrow> False) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  and not_in_imageD:
  "\<lbrakk>y \<notin> f ` X;  x \<in> X; y = f x\<rbrakk> \<Longrightarrow> False"
  by blast+

lemma same_sum_card_prod:
  "\<lbrakk>\<And> x. x \<in> X \<Longrightarrow> f x = (c::real); finite X \<rbrakk> \<Longrightarrow> sum f X = real (card X) * c"
  by simp

lemma int_minus_leq:"a \<le> b \<Longrightarrow> int b - int a = int ( b- a)"
  by auto

lemma extract_first_x:
  "\<lbrakk>x \<in> set xs; P x\<rbrakk> \<Longrightarrow> \<exists> y ys zs. xs = ys@[y]@zs \<and> P y \<and>( \<nexists> z. z \<in> set ys \<and>  P z)"
  apply(induction xs, simp)
  subgoal for a xs
    apply(cases "P a") 
    apply fastforce
    by (metis append_Cons set_ConsD)
  done

lemma induct_list012[case_names nil single sucsuc]:
  "\<lbrakk>P []; \<And>x. P [x]; \<And>x y zs. \<lbrakk> P zs; P (y # zs) \<rbrakk> \<Longrightarrow> P (x # y # zs)\<rbrakk> \<Longrightarrow> P xs"
  by induction_schema (pat_completeness, lexicographic_order)

lemma induct_list0123[consumes 0, case_names nil list1 list2 list3]:
  "\<lbrakk>P []; \<And>x. P [x]; \<And>x y. P [x, y]; 
    \<And>x y z zs. \<lbrakk> P zs; P (z # zs); P (y # z # zs) \<rbrakk> \<Longrightarrow> P (x # y # z # zs)\<rbrakk>
    \<Longrightarrow> P xs"
  by induction_schema (pat_completeness, lexicographic_order)

lemma element_of_list_cases:
  assumes "u \<in> set p"
      "p = [u] \<Longrightarrow> P"
      "\<And> p'. p = u#p' \<Longrightarrow> P"
      "\<And> p'. p = p'@[u] \<Longrightarrow> P"
      "\<And> a b p1 p2. p = p1@[a,u,b]@p2 \<Longrightarrow> P"
 shows P
proof-
  obtain p1 p2 where "p = p1@[u]@p2" 
    by (metis append_Cons append_Nil assms(1) in_set_conv_decomp_first)
  thus P
    by(cases p1 rule: rev_cases, all \<open>cases p2\<close>)
      (auto intro: assms(2-))
qed

lemma list_sing_conv:
  "([x] = ys @ [y]) \<longleftrightarrow> (ys = [] \<and> y = x)"
  "([x] = y#ys) \<longleftrightarrow> (ys = [] \<and> y = x)"
  by (induction ys) auto

lemma exists_Unique_iff: "(\<exists>!x. P x) \<longleftrightarrow> (\<exists>x. P x \<and> (\<forall>y. P y \<longrightarrow> y = x))"
  by auto

lemma Hilbert_choice_singleton: "(SOME x. x \<in> {y}) = y"
  by force

lemma Hilbert_set_minus: "s - {y} \<noteq>{} \<Longrightarrow> y \<noteq> (SOME x. x \<in> s - {y})"
  by(force dest!: iffD2[OF some_in_eq])

lemma gr_zeroI: "(x::enat) \<noteq> 0 \<Longrightarrow> 0 < x"
  by auto

lemma nempty_tl_hd_tl:
  "(tl l) \<noteq>[] \<Longrightarrow> l = (hd l) # (tl l)"
  by (induct "l"; simp)

lemma card3_subset:
  assumes "card s \<ge> 3"
  shows "\<exists>x y z. {x, y, z} \<subseteq> s \<and> x \<noteq> y  \<and> x \<noteq> z  \<and> y \<noteq> z"  
  using assms by(auto simp: numeral_3_eq_3 card_le_Suc_iff)

lemma snoc_eq_iff_butlast':
  "ys = xs @ [x] \<longleftrightarrow> (ys \<noteq> [] \<and> butlast ys = xs \<and> last ys = x)"
  by fastforce

lemma neq_Nil_conv_snoc: "xs \<noteq> [] \<longleftrightarrow> (\<exists>x ys. xs = ys @ [x])"
  by (auto simp add: snoc_eq_iff_butlast')

end