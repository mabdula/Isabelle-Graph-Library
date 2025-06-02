theory Logic_Lemmas
  imports Complex_Main  "HOL-Eisbach.Eisbach"
begin


lemma inj_onI: "(\<And> x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> f x = f y \<Longrightarrow> x = y) \<Longrightarrow> inj_on f A" for f A
           by(auto simp add: inj_on_def)

lemma option_Some_theE: "x = Some y \<Longrightarrow> P (f ( the  x)) \<Longrightarrow> P (case x of Some y \<Rightarrow> f y | None \<Rightarrow> g)"
  by auto

lemma option_None_E: "x = None \<Longrightarrow> P g \<Longrightarrow> P (case x of Some y \<Rightarrow> f y | None \<Rightarrow> g)"
  by auto

lemma binary_collection_cong:"(\<And>  x y. P x y = Q x y) \<Longrightarrow> (\<And> x y. f x y = g x y) \<Longrightarrow> 
                           {f x y | x y. P x y} = {g x y | x y. Q x y}" 
  by simp

lemma binary_collection_disj_union: "{f x y | x y. P x y \<or> Q x y} = {f x y | x y. P x y} \<union> {f x y | x y.  Q x y}"
  by auto

lemma binary_collection_disj_collapse: "(\<And> x y. P x y = Q y x) \<Longrightarrow> {f x y | x y. P x y} = {f y x | x y.  Q x y}"
  by auto

definition "the_default d x = (case x of Some y \<Rightarrow> y | _ \<Rightarrow> d)"

lemma ex_disjE: "(A \<or> B) \<Longrightarrow> (A \<Longrightarrow> \<not> B \<Longrightarrow> P)
                        \<Longrightarrow>  (\<not> A \<Longrightarrow> B \<Longrightarrow> P) 
                        \<Longrightarrow>  (A \<Longrightarrow> B \<Longrightarrow> P) \<Longrightarrow> P"
  for A B by auto

lemma if_E:"P (if b then a else c) \<Longrightarrow> (b \<Longrightarrow> P a \<Longrightarrow> Q) \<Longrightarrow> (\<not> b \<Longrightarrow> P c \<Longrightarrow> Q) \<Longrightarrow> Q"
  by presburger

lemma make_cong: "f x = g x \<Longrightarrow> x = y \<Longrightarrow> x =z \<Longrightarrow> f y = g z" by simp

lemma let_swap: "f (let x = y in g x) = (let x = y in f (g x))" by simp

lemma if_elim: "(if b then a else c) \<Longrightarrow> (b \<Longrightarrow>  a \<Longrightarrow> Q) \<Longrightarrow>
                    (\<not> b \<Longrightarrow>  c \<Longrightarrow> Q) \<Longrightarrow> Q" for a b c Q 
    by(cases b) auto

lemma option_caseE: "P (case arg of None \<Rightarrow> a | Some x \<Rightarrow> b x) \<Longrightarrow>
                     (arg = None \<Longrightarrow> P a \<Longrightarrow> Q) \<Longrightarrow> (\<And> x. arg = Some x \<Longrightarrow> P (b x) \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (metis option.case_eq_if option.collapse)

lemma option_some_simp: "x = Some a \<Longrightarrow> (case x of Some a \<Rightarrow> z a | None \<Rightarrow> y) = z a"
                         "x = Some a \<Longrightarrow> (case x of None \<Rightarrow> y | Some a \<Rightarrow> z a) = z a"
  by (auto split: option.split)

lemma cases_distr: "f (case e of (x, y) \<Rightarrow> g x y) = f (g (fst e) (snd e))" 
  by(auto split: prod.splits)

lemma option_none_simp: "x = None \<Longrightarrow> (case x of Some a \<Rightarrow> z a | None \<Rightarrow> y) = y"
                         "x = None \<Longrightarrow> (case x of None \<Rightarrow> y | Some a \<Rightarrow> z a) = y"
  by (auto split: option.split)

lemma fst_snd_are_same: "prod.swap e = e \<Longrightarrow> fst e = snd e"  for e
      by (metis snd_swap)

lemma P_of_let_I: "(\<And> x. x = g \<Longrightarrow> P (t x)) \<Longrightarrow>P (let x = g in t x)" 
  by simp

lemma P_of_case_prod_I: "(\<And> x y. xy = (x, y) \<Longrightarrow> P (f x y)) \<Longrightarrow> P (case xy of (x, y) \<Rightarrow> (f x y))"
  by(auto split: prod.split)

lemma case_simp:"\<exists> a. x = Some a \<Longrightarrow> (case x of  None \<Rightarrow> g | Some y \<Rightarrow> f y) = f (the x)"
                "\<nexists> a. x = Some a \<Longrightarrow> (case x of  None \<Rightarrow> g | Some y \<Rightarrow> f y) = g"
  by(auto split: option.split)

lemma sufficientE:"A \<Longrightarrow> (A \<Longrightarrow> B) \<Longrightarrow> B" for A B by auto

lemma  orE: "A \<or> B \<Longrightarrow> (A  \<Longrightarrow> P) \<Longrightarrow> (B \<Longrightarrow> P) \<Longrightarrow> P" for A B P by auto
lemma  orE': "A \<or> B \<Longrightarrow> (A \<Longrightarrow>\<not> B \<Longrightarrow> P) \<Longrightarrow> (B \<Longrightarrow> P) \<Longrightarrow> P" for A B P by auto

lemma letE: "(\<And> x. P ( (g x))) \<Longrightarrow> (let x = y in P( (g x)))" by simp

lemma if_left: "Q \<Longrightarrow> (if Q then expr1 else expr2) = expr1" for Q expr1 expr2 by simp

lemma if_right: "\<not>Q \<Longrightarrow> (if Q then expr1 else expr2) = expr2" for Q expr1 expr2 by simp

lemma triple_or_strictE: "A \<or> B \<or> C \<Longrightarrow> (A \<Longrightarrow> P) 
                   \<Longrightarrow> (B \<Longrightarrow> \<not> A \<Longrightarrow> P) \<Longrightarrow> (C \<Longrightarrow> \<not> A \<Longrightarrow> \<not> B\<Longrightarrow> P) \<Longrightarrow> P" for A B C P
  by auto

lemma double_or_strictE:"A \<or> B \<Longrightarrow> (A \<Longrightarrow> P) 
                   \<Longrightarrow> (B \<Longrightarrow> \<not> A \<Longrightarrow> P)  \<Longrightarrow> P" for A B P
  by auto

lemma double_quadruple_orE:
 "(A \<or> B \<or> C \<or> D) \<Longrightarrow> (A' \<or> B' \<or> C' \<or> D') \<Longrightarrow> 
 (A \<and> A' \<Longrightarrow> P) \<Longrightarrow> (B \<and> A' \<Longrightarrow> P) \<Longrightarrow> (C \<and> A' \<Longrightarrow> P) \<Longrightarrow> (D \<and> A' \<Longrightarrow> P) \<Longrightarrow>
 (A \<and> B' \<Longrightarrow> P) \<Longrightarrow> (B \<and> B' \<Longrightarrow> P) \<Longrightarrow> (C \<and> B' \<Longrightarrow> P) \<Longrightarrow> (D \<and> B' \<Longrightarrow> P) \<Longrightarrow>
 (A \<and> C' \<Longrightarrow> P) \<Longrightarrow> (B \<and> C' \<Longrightarrow> P) \<Longrightarrow> (C \<and> C' \<Longrightarrow> P) \<Longrightarrow> (D \<and> C' \<Longrightarrow> P) \<Longrightarrow>
 (A \<and> D' \<Longrightarrow> P) \<Longrightarrow> (B \<and> D' \<Longrightarrow> P) \<Longrightarrow> (C \<and> D' \<Longrightarrow> P) \<Longrightarrow> (D \<and> D'\<Longrightarrow> P) 
 \<Longrightarrow> P" for A B C D A' B' C' D'
  by argo

lemma ex2E: "\<exists>x y. P x y \<Longrightarrow> (\<And>x y. P x y \<Longrightarrow> Q) \<Longrightarrow> Q" by auto

lemma ex3E: "\<exists> x y z.  P x y z \<Longrightarrow> (\<And>x y z. P x y z \<Longrightarrow> Q) \<Longrightarrow> Q" by auto

lemma prod_elim: "P p \<Longrightarrow> (\<And> a b. p = (a,b) \<Longrightarrow> P p \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (metis prod.exhaust_sel)

lemma in_insertE: "y \<in> insert x X \<Longrightarrow> (x = y \<Longrightarrow> P x) \<Longrightarrow> (\<And> x. y \<in> X \<Longrightarrow> P y) \<Longrightarrow> P y"
  by auto

lemma in_insertE_pair: "y \<in> insert x X \<Longrightarrow> z \<in> insert x X \<Longrightarrow> y \<noteq> z \<Longrightarrow>
                       (y = x \<Longrightarrow> z \<in> X \<Longrightarrow> P) \<Longrightarrow>
                       (z = x \<Longrightarrow> y \<in> X \<Longrightarrow> P) \<Longrightarrow>
                       (y \<in> X \<Longrightarrow> z \<in> X \<Longrightarrow> P) \<Longrightarrow> P"
  by auto

lemma not_in_card_del: "x \<notin> A \<Longrightarrow> card (A - {x}) = card A"
  by force

lemma ball_cong:
"A = B \<Longrightarrow> (\<And> a. a \<in> A \<Longrightarrow> a \<in> B \<Longrightarrow> P a = Q a) \<Longrightarrow> (\<forall> a \<in> A. P a) \<longleftrightarrow> (\<forall> a \<in> B. Q a)" for B
  by simp


lemma finite_set_increase_by_1:"finite A \<Longrightarrow> x \<notin> A \<Longrightarrow> card (insert x A) = card A +1" 
  by force

lemma function_union:"{f x | x . x \<in> A \<union> B} = {f x | x . x \<in> A } \<union> {f x | x . x \<in>  B}"  by auto

lemma function_subset:" A \<subseteq> B \<Longrightarrow>  {f x | x . x \<in> A } \<subseteq> {f x | x . x \<in>  B}" by auto

lemma set_union_eq_cong: "A = B \<Longrightarrow> C = D \<Longrightarrow> A \<union> C = B \<union> D" for A B C D by simp

lemma elem_mono: "x \<in> A \<Longrightarrow> A \<subseteq> C \<Longrightarrow> x \<in> C"
  by auto

lemma finite_img: "finite X \<Longrightarrow> finite { y. \<exists> x. y = f x \<and> x \<in> X}"
  by force

lemma collapse_to_img: "{f x| x. x\<in> X} = f ` X"
  by blast

lemma set_img_extract: "{y. \<exists>x. x \<in> set xs \<and> y = f x} \<union> {f z} = 
                   {y. \<exists>x. x \<in> set (z#xs) \<and> y = f x}" 
  by auto

lemma set_extract_singleton: "x \<in> X \<Longrightarrow> X = (X - {x}) \<union> {x}"
  by blast

lemma inter_minus_distr: "Z \<inter> Y = {} \<Longrightarrow> (X - Y) \<union> Z = (X \<union> Z) -Y"
  by blast

lemma card_grteq_2: 
  assumes "finite A" "card A \<ge> 2"
  obtains x y where "x \<in> A \<and> y \<in> A \<and> x \<noteq> y" 
  by (meson assms(2) card_2_iff' obtain_subset_with_card_n subset_eq)

lemma inter_Big_union_distr_empt: "(\<And> C. C \<in> B \<Longrightarrow> A \<inter> C = {}) \<Longrightarrow> (A \<inter> \<Union> B) = {}" for A B by auto

lemma empty_trans: "A \<subseteq> B \<Longrightarrow> B ={} \<Longrightarrow> A = {}" for A B by simp

lemma set_minus_assoc:"A \<inter> B = {} \<Longrightarrow> (A \<union> C) - B = A \<union> (C - B)" for A B C by fast

lemma finite_BigU: "finite A \<Longrightarrow> (\<And> B. B \<in> A \<Longrightarrow> finite B) \<Longrightarrow> finite (\<Union> A)" for A by simp

lemma superset_inter_empty: "F1 \<subseteq> G1 \<Longrightarrow> F2 \<subseteq> G2 \<Longrightarrow> G1 \<inter> G2 = {} 
                               \<Longrightarrow> F1 \<inter> F2 = {}" for F1 F2 G1 G2 by auto

lemma single_diff_remove: "x \<notin> A \<Longrightarrow> A - {x} = A" by simp

lemma from_comprehension:
  assumes "fx \<in> {f x| x. P x}"
  obtains x where "P x" "f x = fx"
  using assms by auto

lemma  neg_neq:"(\<not> (a \<noteq> b) ) = (a = b)" for a b by simp

lemma  union_empt_cong: "A ={} \<Longrightarrow> A \<union> B = B" for A B by simp

lemma Big_union_single_img: "(\<Union> x \<in> {y}. f x )= f y" for x y f
  by auto

lemma P_of_ifI: "(b \<Longrightarrow> P a) \<Longrightarrow> (\<not> b \<Longrightarrow> P c) \<Longrightarrow> P (if b then a else c)" for P a b c by simp

lemma pair_set_subsetE: "{x, y} \<subseteq> A \<union> B \<Longrightarrow>
                (x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> P) \<Longrightarrow>
                (x \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow> P) \<Longrightarrow>
                (x \<in> B \<Longrightarrow> y \<in> A \<Longrightarrow> P) \<Longrightarrow>
                (x \<in> B \<Longrightarrow> y \<in> B \<Longrightarrow> P) \<Longrightarrow> P" for B
  by auto

lemma piar_setE: "X \<subseteq> {x, y} \<Longrightarrow> 
                  (X = {} \<Longrightarrow> P) \<Longrightarrow>
                  (X = {x} \<Longrightarrow> P) \<Longrightarrow>
                  (X = {y} \<Longrightarrow> P) \<Longrightarrow>
                  (X = {x, y} \<Longrightarrow> P) \<Longrightarrow> P"
  by auto

lemma set_union_subset_cong: "A \<subseteq> B \<Longrightarrow> C \<subseteq> D \<Longrightarrow> A \<union> C \<subseteq> B \<union> D" for A B C D by auto

lemma image_sigleton: "f ` {x} = {f x}" for f x by simp

lemma non_emptyE:"X \<noteq> {} \<Longrightarrow> (\<And> x. x \<in> X \<Longrightarrow> P) \<Longrightarrow>P" by auto


lemma all_to_meta_set: "\<forall> x \<in> X. P x \<Longrightarrow> (\<And>x. x\<in> X \<Longrightarrow> P x)" by simp

lemma allTurn: "(\<forall> x. P x) \<Longrightarrow> (\<And> x. P x)" by simp

lemma allTurnSet: "(\<forall> x \<in> S. P x) \<Longrightarrow> (\<And> x. x \<in> S \<Longrightarrow>P x)" by simp

lemma membershipE: "y \<in> {f x | x. P x } \<Longrightarrow> (\<And> x. y = f x \<Longrightarrow> P x \<Longrightarrow> Q) \<Longrightarrow>Q"
  by auto

lemma in_Union_of_pairs_E: "x \<in> \<Union> {{a,b} | a b. Q a b} \<Longrightarrow> 
                  (\<And> a b . Q a b \<Longrightarrow> x \<in> {a ,b} \<Longrightarrow> P) \<Longrightarrow> P"
  using UnionE by auto

lemma insert_with_P: "P x \<Longrightarrow> insert x {y \<in> S. P y} = { y \<in> insert x S. P y}"
                     "\<not> P x \<Longrightarrow>  {y \<in> S. P y} = { y \<in> insert x S. P y}"by auto

lemma Collect_cong_set: "(\<And>x. x \<in> S \<Longrightarrow> P x = Q x) \<Longrightarrow> {x \<in> S. P x} = {x \<in> S. Q x}"
  by auto
end