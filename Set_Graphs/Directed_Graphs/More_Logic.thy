theory More_Logic
  imports Complex_Main  "HOL-Eisbach.Eisbach"
begin

lemma option_Some_theE: 
  "\<lbrakk>x = Some y; P (f ( the  x))\<rbrakk> \<Longrightarrow> P (case x of Some y \<Rightarrow> f y | None \<Rightarrow> g)"
  by auto

lemma option_None_E: 
  "\<lbrakk>x = None; P g\<rbrakk> \<Longrightarrow> P (case x of Some y \<Rightarrow> f y | None \<Rightarrow> g)"
  by auto

lemma binary_collection_cong:
  "\<lbrakk>\<And>  x y. P x y = Q x y; \<And> x y. f x y = g x y\<rbrakk>
   \<Longrightarrow> {f x y | x y. P x y} = {g x y | x y. Q x y}" 
  by simp

lemma binary_collection_disj_union: 
  "{f x y | x y. P x y \<or> Q x y} = {f x y | x y. P x y} \<union> {f x y | x y.  Q x y}"
  by auto

lemma binary_collection_disj_collapse: 
  "(\<And> x y. P x y = Q y x) \<Longrightarrow> {f x y | x y. P x y} = {f y x | x y.  Q x y}"
  by auto

definition "the_default d x = (case x of Some y \<Rightarrow> y | _ \<Rightarrow> d)"

lemma ex_disjE: "\<lbrakk>A \<or> B; \<lbrakk>A; \<not> B\<rbrakk> \<Longrightarrow> P; \<lbrakk>\<not> A; B\<rbrakk> \<Longrightarrow> P; \<lbrakk>A; B\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by auto

lemma if_E: "\<lbrakk>P (if b then a else c); \<lbrakk>b; P a\<rbrakk> \<Longrightarrow> Q; \<lbrakk>\<not> b; P c\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
  by presburger

lemma make_cong: "\<lbrakk>f x = g x; x = y; x = z\<rbrakk> \<Longrightarrow> f y = g z" by simp

lemma let_swap: "f (let x = y in g x) = (let x = y in f (g x))" by simp

lemma if_elim: "\<lbrakk>(if b then a else c); \<lbrakk>b; a\<rbrakk> \<Longrightarrow> Q; \<lbrakk>\<not> b; c\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q" 
 by(cases b) auto

lemma option_caseE: 
  "\<lbrakk>P (case arg of None \<Rightarrow> a | Some x \<Rightarrow> b x);
   \<lbrakk>arg = None; P a\<rbrakk> \<Longrightarrow> Q; \<And> x. \<lbrakk>arg = Some x; P (b x)\<rbrakk> \<Longrightarrow> Q\<rbrakk>
   \<Longrightarrow> Q"
  by (metis option.case_eq_if option.collapse)

lemma option_some_simp: 
  "x = Some a \<Longrightarrow> (case x of Some a \<Rightarrow> z a | None \<Rightarrow> y) = z a"
  "x = Some a \<Longrightarrow> (case x of None \<Rightarrow> y | Some a \<Rightarrow> z a) = z a"
  by (auto split: option.split)

lemma cases_distr: "f (case e of (x, y) \<Rightarrow> g x y) = f (g (fst e) (snd e))" 
  by(auto split: prod.splits)

lemma option_none_simp: 
  "x = None \<Longrightarrow> (case x of Some a \<Rightarrow> z a | None \<Rightarrow> y) = y"
  "x = None \<Longrightarrow> (case x of None \<Rightarrow> y | Some a \<Rightarrow> z a) = y"
  by (auto split: option.split)

lemma fst_snd_are_same: "prod.swap e = e \<Longrightarrow> fst e = snd e"  for e
  by (metis snd_swap)

lemma P_of_let_I: "(\<And> x. x = g \<Longrightarrow> P (t x)) \<Longrightarrow>P (let x = g in t x)" 
  by simp

lemma P_of_case_prod_I: 
  "(\<And> x y. xy = (x, y) \<Longrightarrow> P (f x y)) \<Longrightarrow> P (case xy of (x, y) \<Rightarrow> (f x y))"
  by(auto split: prod.split)

lemma case_simp:
  "\<exists> a. x = Some a \<Longrightarrow> (case x of  None \<Rightarrow> g | Some y \<Rightarrow> f y) = f (the x)"
  "\<nexists> a. x = Some a \<Longrightarrow> (case x of  None \<Rightarrow> g | Some y \<Rightarrow> f y) = g"
  by(auto split: option.split)

lemma sufficientE:"\<lbrakk>A; A \<Longrightarrow> B\<rbrakk> \<Longrightarrow> B"
  by auto

lemma  orE: "\<lbrakk>A \<or> B; A  \<Longrightarrow> P; B \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" 
  by auto

lemma  orE': "\<lbrakk>A \<or> B; \<lbrakk>A; \<not> B\<rbrakk> \<Longrightarrow> P; B \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by auto

lemma letE: "(\<And> x. P ( (g x))) \<Longrightarrow> (let x = y in P( (g x)))" 
  by simp

lemma if_left: "Q \<Longrightarrow> (if Q then expr1 else expr2) = expr1" 
  by simp

lemma if_right: "\<not>Q \<Longrightarrow> (if Q then expr1 else expr2) = expr2" 
  by simp

lemma triple_or_strictE: 
  "\<lbrakk>A \<or> B \<or> C; A \<Longrightarrow> P; \<lbrakk>B; \<not> A\<rbrakk> \<Longrightarrow> P; \<lbrakk>C; \<not> A; \<not> B \<rbrakk>\<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" 
  by auto

lemma double_or_strictE: "\<lbrakk>A \<or> B; A \<Longrightarrow> P; \<lbrakk>B; \<not> A\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by auto

lemma double_quadruple_orE:
 "\<lbrakk>A \<or> B \<or> C \<or> D; A' \<or> B' \<or> C' \<or> D';
  \<lbrakk>A; A'\<rbrakk> \<Longrightarrow> P; \<lbrakk>B; A'\<rbrakk> \<Longrightarrow> P; \<lbrakk>C; A'\<rbrakk> \<Longrightarrow> P; \<lbrakk>D; A'\<rbrakk> \<Longrightarrow> P;
  \<lbrakk>A; B'\<rbrakk> \<Longrightarrow> P; \<lbrakk>B; B'\<rbrakk> \<Longrightarrow> P; \<lbrakk>C; B'\<rbrakk> \<Longrightarrow> P; \<lbrakk>D; B'\<rbrakk> \<Longrightarrow> P;
  \<lbrakk>A; C'\<rbrakk> \<Longrightarrow> P; \<lbrakk>B; C'\<rbrakk> \<Longrightarrow> P; \<lbrakk>C; C'\<rbrakk> \<Longrightarrow> P; \<lbrakk>D; C'\<rbrakk> \<Longrightarrow> P;
  \<lbrakk>A; D'\<rbrakk> \<Longrightarrow> P; \<lbrakk>B; D'\<rbrakk> \<Longrightarrow> P; \<lbrakk>C; D'\<rbrakk> \<Longrightarrow> P; \<lbrakk>D; D'\<rbrakk>\<Longrightarrow> P\<rbrakk> 
  \<Longrightarrow> P" 
  by argo

lemma quadruple_orE: "\<lbrakk>A \<or> B \<or> C \<or> D; A  \<Longrightarrow> P; B \<Longrightarrow> P; C  \<Longrightarrow> P; D  \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" 
  by argo

lemma ex2E: "\<lbrakk>\<exists>x y. P x y; \<And>x y. P x y \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q" 
  by auto

lemma ex3E: "\<lbrakk>\<exists> x y z.  P x y z; \<And>x y z. P x y z \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q" 
  by auto

lemma prod_elim: "\<lbrakk>P p; \<And> a b. \<lbrakk>p = (a,b); P p\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
  by (metis prod.exhaust_sel)

lemma in_insertE: "\<lbrakk>y \<in> insert x X; x = y \<Longrightarrow> P x; \<And> x. y \<in> X \<Longrightarrow> P y\<rbrakk> \<Longrightarrow> P y"
  by auto

lemma in_insertE_pair: 
  "\<lbrakk>y \<in> insert x X; z \<in> insert x X; y \<noteq> z;
    \<lbrakk>y = x; z \<in> X\<rbrakk> \<Longrightarrow> P; \<lbrakk>z = x; y \<in> X\<rbrakk> \<Longrightarrow> P; \<lbrakk>y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> P\<rbrakk>
    \<Longrightarrow> P"
  by auto

lemma not_in_card_del: "x \<notin> A \<Longrightarrow> card (A - {x}) = card A"
  by force

lemma ball_cong: "\<lbrakk>A = B; \<And> a. \<lbrakk>a \<in> A; a \<in> B\<rbrakk> \<Longrightarrow> P a = Q a\<rbrakk> \<Longrightarrow> (\<forall> a \<in> A. P a) \<longleftrightarrow> (\<forall> a \<in> B. Q a)" 
  by simp

lemma finite_set_increase_by_1: "\<lbrakk>finite A; x \<notin> A\<rbrakk> \<Longrightarrow> card (insert x A) = card A +1" 
  by force

lemma function_union: "{f x | x . x \<in> A \<union> B} = {f x | x . x \<in> A } \<union> {f x | x . x \<in>  B}" 
  by auto

lemma function_subset: "A \<subseteq> B \<Longrightarrow>  {f x | x . x \<in> A } \<subseteq> {f x | x . x \<in>  B}" 
  by auto

lemma set_union_eq_cong: "\<lbrakk>A = B; C = D\<rbrakk> \<Longrightarrow> A \<union> C = B \<union> D"
  by simp

lemma elem_mono: "\<lbrakk>x \<in> A; A \<subseteq> C\<rbrakk> \<Longrightarrow> x \<in> C"
  by auto

lemma finite_img: "finite X \<Longrightarrow> finite { y. \<exists> x. y = f x \<and> x \<in> X}"
  by force

lemma collapse_to_img: "{f x| x. x\<in> X} = f ` X"
  by blast

lemma set_img_extract: 
  "{y. \<exists>x. x \<in> set xs \<and> y = f x} \<union> {f z} = {y. \<exists>x. x \<in> set (z#xs) \<and> y = f x}" 
  by auto

lemma set_extract_singleton: "x \<in> X \<Longrightarrow> X = (X - {x}) \<union> {x}"
  by blast

lemma inter_minus_distr: "Z \<inter> Y = {} \<Longrightarrow> (X - Y) \<union> Z = (X \<union> Z) -Y"
  by blast

lemma card_grteq_2: 
  assumes "finite A" "card A \<ge> 2"
  obtains x y where "x \<in> A \<and> y \<in> A \<and> x \<noteq> y" 
  by (meson assms(2) card_2_iff' obtain_subset_with_card_n subset_eq)

lemma inter_Big_union_distr_empt: "(\<And> C. C \<in> B \<Longrightarrow> A \<inter> C = {}) \<Longrightarrow> (A \<inter> \<Union> B) = {}" 
  by auto

lemma empty_trans: "\<lbrakk>A \<subseteq> B; B ={}\<rbrakk> \<Longrightarrow> A = {}" 
  by simp

lemma set_minus_assoc: "A \<inter> B = {} \<Longrightarrow> (A \<union> C) - B = A \<union> (C - B)"
  by fast

lemmas finite_BigU = finite_Union

lemma superset_inter_empty: 
  "\<lbrakk>F1 \<subseteq> G1; F2 \<subseteq> G2; G1 \<inter> G2 = {}\<rbrakk> \<Longrightarrow> F1 \<inter> F2 = {}" 
  by auto

lemma single_diff_remove: "x \<notin> A \<Longrightarrow> A - {x} = A" 
  by simp

lemma from_comprehension:
  assumes "fx \<in> {f x| x. P x}"
  obtains x where "P x" "f x = fx"
  using assms by auto

lemma neg_neq:"(\<not> (a \<noteq> b) ) = (a = b)"
  by simp

lemma  union_empt_cong: "A = {} \<Longrightarrow> A \<union> B = B" 
  by simp

lemma Big_union_single_img: "(\<Union> x \<in> {y}. f x )= f y" 
  by auto

lemma P_of_ifI: "\<lbrakk>b \<Longrightarrow> P a; \<not> b \<Longrightarrow> P c\<rbrakk> \<Longrightarrow> P (if b then a else c)"
  by simp

lemma pair_set_subsetE: 
  "\<lbrakk>{x, y} \<subseteq> A \<union> B; \<lbrakk>x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow> P; \<lbrakk>x \<in> A; y \<in> B\<rbrakk> \<Longrightarrow> P;
                    \<lbrakk>x \<in> B; y \<in> A\<rbrakk> \<Longrightarrow> P; \<lbrakk>x \<in> B; y \<in> B\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" 
  by auto

lemma piar_setE: 
  "\<lbrakk>X \<subseteq> {x, y}; X = {} \<Longrightarrow> P; X = {x} \<Longrightarrow> P; X = {y} \<Longrightarrow> P; X = {x, y} \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by auto

lemmas set_union_subset_cong = Un_mono

lemma disjoint_subs_commute: "B \<inter> C = {} \<Longrightarrow> (A - B) -C = (A - C) - B"
  by blast

lemma set_diff_eq_cong: "\<lbrakk>A = B; C = D\<rbrakk> \<Longrightarrow> A - C = B - D"
  by simp

lemma image_singleton: "f ` {x} = {f x}" 
  by simp

lemma non_emptyE:"\<lbrakk>X \<noteq> {}; \<And> x. x \<in> X \<Longrightarrow> P\<rbrakk> \<Longrightarrow>P" 
  by auto

lemma all_to_meta_set: "\<forall> x \<in> X. P x \<Longrightarrow> (\<And>x. x\<in> X \<Longrightarrow> P x)" 
  by simp

lemma allTurn: "(\<forall> x. P x) \<Longrightarrow> (\<And> x. P x)" 
  by simp

lemma allTurnSet: "(\<forall> x \<in> S. P x) \<Longrightarrow> (\<And> x. x \<in> S \<Longrightarrow>P x)" 
  by simp

lemma membershipE: "\<lbrakk>y \<in> {f x | x. P x }; \<And> x. \<lbrakk>y = f x; P x\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow>Q"
  by auto

lemma in_Union_of_pairs_E: 
  "\<lbrakk>x \<in> \<Union> {{a,b} | a b. Q a b} ; \<And> a b . \<lbrakk>Q a b; x \<in> {a ,b}\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using UnionE by auto

lemma insert_with_P: 
  "P x \<Longrightarrow> insert x {y \<in> S. P y} = { y \<in> insert x S. P y}"
  "\<not> P x \<Longrightarrow>  {y \<in> S. P y} = { y \<in> insert x S. P y}"
  by auto

lemma Collect_cong_set: "(\<And>x. x \<in> S \<Longrightarrow> P x = Q x) \<Longrightarrow> {x \<in> S. P x} = {x \<in> S. Q x}"
  by auto

lemma if_non_empty_finite_finite: " (A \<noteq> {} \<Longrightarrow> finite A) \<Longrightarrow> finite A" 
  by auto

lemma if_of_bools: 
 "(if b then True else False) \<Longrightarrow> b"
 "(if b then False else True) \<Longrightarrow> \<not> b"
  by argo+

lemma f_of_double_if_cond_same:
 "f (if b then a1 else c1) (if b then a2 else c2) = (if b then f a1 a2 else f c1 c2)"
  by auto

lemma if_PQ:"if P then False else if Q then False else True \<Longrightarrow> \<not> P \<and> \<not> Q" 
  by argo

lemma if_PQ_E: "\<lbrakk>if P then False else if Q then False else True; \<not> P \<and> \<not> Q \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by metis

lemma image_two_Collect: "{f x y | x y. P x y} = (\<lambda> (x, y). f x y) ` { (x, y) | x y. P x y}"
  by auto

lemma finite_pairs_of_finite_set_set: "finite G \<Longrightarrow> finite {(u, v). {u, v} \<in> G}"
proof(induction G rule: finite_induct)
  case (insert x F)
  have "{a. case a of (u, v) \<Rightarrow> {u, v} \<in> {x} \<union> F}
        = {a. case a of (u, v) \<Rightarrow> {u, v} \<in> F} \<union> {a. case a of (u, v) \<Rightarrow> {u, v}= x}"
    by auto
  moreover have "{(u, v). {u, v} = x} = {} \<or> (\<exists> a b. {(u, v). {u, v} = x} = {(a, b), (b, a)})"
  proof(cases "\<exists>a b. {(u, v). {u, v} = x}= {(a, b), (b, a)}")
    case True
    then show ?thesis by auto
  next
    case False
    note false = this
    have x_not_weak_dbltn:"\<nexists> u v. {u, v} = x" 
    proof(rule ccontr, goal_cases)
      case 1
      then obtain u v where "{u, v} = x" by auto
      hence "{(u, v). {u, v} = x}= {(u, v), (v, u)}"
        by fast
      then show ?case 
        using False by blast
    qed
    show ?thesis 
    proof(cases "{(u, v). {u, v} = x} = {}")
      case True
      then show ?thesis by simp
    next
      case False
      then obtain u v w where "u \<noteq> v" "v \<noteq> w" "u \<noteq> w" "{u, v, w} \<subseteq> x"
        using x_not_weak_dbltn by simp
      hence "{(u, v). {u, v} = x} = {}" by auto
      then show ?thesis by simp
    qed
  qed
  ultimately show ?case
    by (auto simp add: insert(3))
qed auto

lemma finite_g_applied_double:
  assumes "finite {f x y | x y. P x y}" 
  shows   "finite {g (f x y) | x y. P x y}"
proof-
  have "{g (f x y) |x y. P x y} = g ` {f x y | x y. P x y}" by blast
  thus ?thesis
    using assms by auto
qed

lemma finite_g_applied_single:
  assumes "finite {f x | x . P x}" 
  shows   "finite {g (f x) | x. P x}"
proof-
  have "{g (f x) | x. P x} = g ` {f x | x . P x}" by auto
  thus ?thesis 
    using assms by auto
qed

lemma Collect_double_f_to_single: 
  "{g (f x y) | x y. P x y} = {g ff | ff. \<exists> x y. ff = f x y \<and> P x y}"
  by auto

lemma Collect_single_f_to_single: "{g (f x) | x. P x} = {g ff | ff. \<exists> x. ff = f x \<and> P x}"
  by auto

lemma pair_eq_fst_snd_eq:
 "(a, b) = c \<Longrightarrow> a = fst c"
 "(a, b) = c \<Longrightarrow> b = snd c"
  by auto

lemma in_image_with_fst_eq: "a \<in> fst ` A \<longleftrightarrow> (\<exists> b. (a, b) \<in> A)" 
  by force

lemma finite_double_image_of_pairs_in_set_of_sets: "finite G \<Longrightarrow> finite {f x y | x y. {x, y} \<in> G}"
proof(induction G rule: finite_induct)
  case (insert e F)
  show ?case 
  proof(cases "\<exists> x y. e = {x, y}")
    case True
    then obtain x y where "e = {x, y}" by auto
    hence "{f x y | x y. {x, y} \<in> insert e F} = 
           {f x y | x y. {x, y} \<in> F} \<union> {f x y, f y x}" 
      by (auto simp add: doubleton_eq_iff)
    then show ?thesis 
      using insert by simp
  next
    case False
  hence "{f x y | x y. {x, y} \<in> insert e F} = 
           {f x y | x y. {x, y} \<in> F}" by auto
  then show ?thesis
    using insert by simp
  qed
qed simp

lemma conj6I: "\<lbrakk>P1;P2;P3;P4;P5;P6\<rbrakk> \<Longrightarrow> P1 \<and> P2 \<and> P3 \<and> P4 \<and> P5 \<and>P6" 
  by simp

lemma conj6D:
 "P1 \<and> P2 \<and> P3 \<and> P4 \<and> P5 \<and>P6 \<Longrightarrow> P1"
 "P1 \<and> P2 \<and> P3 \<and> P4 \<and> P5 \<and>P6 \<Longrightarrow> P2"
 "P1 \<and> P2 \<and> P3 \<and> P4 \<and> P5 \<and>P6 \<Longrightarrow> P3"
 "P1 \<and> P2 \<and> P3 \<and> P4 \<and> P5 \<and>P6 \<Longrightarrow> P4"
 "P1 \<and> P2 \<and> P3 \<and> P4 \<and> P5 \<and>P6  \<Longrightarrow> P5"
 "P1 \<and> P2 \<and> P3 \<and> P4 \<and> P5 \<and>P6  \<Longrightarrow> P6"
 by auto

end