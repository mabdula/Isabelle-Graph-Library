theory List_Lemmas
  imports  "HOL-Library.Extended_Real" Main
begin
subsection \<open>Properties of Lists\<close>

lemma sum_list_map_filter_split: "sum_list (map (f::'s\<Rightarrow> real) xs) = sum_list (map f (filter P xs)) +
 sum_list (map f (filter (\<lambda> x. \<not> P x) xs))"
  by(induction xs)(auto simp add: algebra_simps)

lemma takeWhile_everything: "(\<And> x. x \<in> set xs \<Longrightarrow> P x) \<Longrightarrow> takeWhile P xs = xs"
  by(induction xs) auto

lemma dropWhile_nothing: "(\<And> x. x \<in> set xs \<Longrightarrow> \<not> P x) \<Longrightarrow> dropWhile P xs = xs"
  by(induction xs) auto

lemma foldr_plus_add_right:
 " (c::real)+ foldr (\<lambda>e. (+) (f e)) xs b =
    foldr (\<lambda>e. (+) (f e)) (xs) (c + b)"
  by(induction xs arbitrary: c b)
  (auto simp add: algebra_simps)

lemma bulast_subset: "set (butlast xs) \<subseteq> set xs" for xs 
  using in_set_butlastD by fastforce

lemma singleton_hd_last: "q \<noteq> [] \<Longrightarrow> tl q = [] \<Longrightarrow> hd q = last q"
  by (cases q) auto

lemma hd_last_same: "length xs = 1 \<Longrightarrow> hd xs = last xs" for xs 
  using singleton_hd_last[of xs] 
  by(cases xs) auto
       
lemma last_simp : "last (a#b#cs) = last (b#cs)" by simp

lemma list_triple_split_mid_distinct:
"length xs = n \<and> \<not> distinct xs
                 \<Longrightarrow> (\<exists> as bs cs x. xs = as@[x]@bs@[x]@cs \<and> distinct bs \<and> x \<notin> set bs)"
proof(induction arbitrary: xs rule: less_induct)
  case (less n)  
  then show ?case 
  proof(cases xs)
    case Nil
    then show ?thesis using less by auto
  next
    case (Cons x ys)
    then show ?thesis 
    proof(cases "x \<in> set ys")
      case True
      obtain gs fs where gf_def: "ys = gs@[x]@fs \<and> x \<notin> set gs" 
        using True  in_set_conv_decomp_first[of x ys] by auto
      then show ?thesis 
      proof(cases "distinct gs")
        case True
        hence "xs = []@[x]@gs@[x]@fs \<and> distinct gs"
          using  \<open>ys = gs @ [x] @ fs \<and> x \<notin> set gs\<close> local.Cons by auto
        then show ?thesis 
          using gf_def by blast
      next
        case False
        have "length gs < n" using less(2) Cons  gf_def by auto
        then obtain as bs cs s where "gs = as@[s]@bs@[s]@cs \<and> distinct bs \<and> s \<notin> set bs"
          using less(1)[of "length gs" gs] False by auto
        hence "xs = []@[x]@as@[s]@bs@[s]@cs@[x]@fs \<and> distinct bs \<and> s \<notin> set bs"
          using local.Cons  gf_def  by force
        then show ?thesis  
          by (metis append.assoc)
      qed
    next
      case False 
      hence "length ys < n "  "length ys = length ys \<and> \<not> distinct ys "
        using less.prems local.Cons False  by auto
      then obtain as bs cs s where "ys = as @ [s] @ bs @ [s] @ cs \<and> distinct bs \<and> s \<notin> set bs"
        using less(1)[of "length ys" ys] by auto
      then show ?thesis using Cons 
        by (metis append_Cons)
    qed
  qed
qed

lemma double_occur_non_dist: "set (xs) \<subseteq> X \<Longrightarrow> card X < length xs 
                                       \<Longrightarrow> finite X\<Longrightarrow> xs \<noteq> [] \<Longrightarrow> \<not> distinct xs"
  by(induction "card X" arbitrary: X xs, auto)
    (metis card_mono distinct_card linorder_not_less)

lemma subset_big_union_diff:
assumes "set C = (set D) - A " "A = set D - set C" "D \<in> CCC" "C \<notin> CCC" "C \<noteq> D"
        "(\<And> B E. B \<in> CCC \<Longrightarrow> E \<in> CCC \<Longrightarrow>B \<noteq> E \<Longrightarrow> set E \<inter> set B = {})"
  shows "(\<Union> {set B| B. B \<in> CCC}) - A = \<Union> {set B| B. B \<in> ((CCC - {D}) \<union> {C})}"
proof
  show "\<Union> {set B |B. B \<in> CCC} - A \<subseteq> \<Union> {set B |B. B \<in> CCC - {D} \<union> {C}}"
  proof
    fix x 
    assume "x \<in> \<Union> {set B |B. B \<in> CCC} - A"
    then obtain E where "x \<in> set E \<and> E \<in> CCC" by auto
    then show " x \<in> \<Union> {set B |B. B \<in> CCC - {D} \<union> {C}}"
      using \<open>x \<in> \<Union> {set B |B. B \<in> CCC} - A\<close> assms(1) by auto
  qed
  show "\<Union> {set B |B. B \<in> CCC - {D} \<union> {C}} \<subseteq> \<Union> {set B |B. B \<in> CCC} - A" 
  proof
    fix x
    assume " x \<in> \<Union> {set B |B. B \<in> CCC - {D} \<union> {C}}"
    then obtain E where E_def: "x \<in> set E \<and> E \<in> CCC - {D} \<union> {C}" by auto
    have "x \<in> set E \<Longrightarrow>x \<in> A \<Longrightarrow> set E \<inter> set D \<noteq> {}"
    using assms
    by blast 
    from E_def show "x \<in> \<Union> {set B |B. B \<in> CCC} - A"
      apply(cases "E = C")
      using \<open>x \<in> set E \<and> E \<in> CCC - {D} \<union> {C}\<close> assms(1) assms(3) apply auto[1]
      by (auto, metis Diff_iff Un_insert_right \<open>\<lbrakk>x \<in> set E; x \<in> A\<rbrakk> \<Longrightarrow> set E \<inter> set D \<noteq> {}\<close> 
                assms(3) assms(6) insert_iff sup_bot.right_neutral)
  qed
qed

lemma bing_union_split:
  assumes "set A = set BB \<union> set C"
  shows   "(\<Union> {set C'|C'. C' \<in> CCC \<union>{A}}) = (\<Union> {set C'|C'. C' \<in> CCC \<union>{BB, C}})"
proof
  show "\<Union> {set C' |C'. C' \<in> CCC \<union> {A}} \<subseteq> \<Union> {set C' |C'. C' \<in> CCC \<union> {BB, C}}"
  proof
    fix x
    assume "x \<in> \<Union> {set C' |C'. C' \<in> CCC \<union> {A}}"
    then obtain E where "E \<in> CCC  \<union> {A} \<and> x \<in> set E" by auto
    then show " x \<in> \<Union> {set C' |C'. C' \<in> CCC \<union> {BB, C}}"
    proof(cases "E = A")
      case True
      hence "x \<in> set BB \<or> x \<in> set C" 
        using \<open>E \<in> CCC \<union> {A} \<and> x \<in> set E\<close> assms by auto
      then show ?thesis by(cases "x \<in> set BB", auto)
    next
      case False
      hence "E \<in> CCC"
        using \<open>E \<in> CCC \<union> {A} \<and> x \<in> set E\<close> by fastforce
      then show ?thesis 
        using \<open>E \<in> CCC \<union> {A} \<and> x \<in> set E\<close> by blast
    qed
  qed
  show "\<Union> {set C' |C'. C' \<in> CCC \<union> {BB, C}} \<subseteq> \<Union> {set C' |C'. C' \<in> CCC \<union> {A}}"
  proof
    fix x
    assume " x \<in> \<Union> {set C' |C'. C' \<in> CCC \<union> {BB, C}}"
    then obtain E where "E \<in> CCC  \<union> {BB, C} \<and> x \<in> set E" by auto
    then show " x \<in> \<Union> {set C' |C'. C' \<in> CCC \<union> {A}}"
    proof(cases "E = BB \<or> E = C")
      case True
      then show ?thesis 
        using \<open>E \<in> CCC \<union> {BB, C} \<and> x \<in> set E\<close> assms by fastforce
    next
      case False
      then show ?thesis 
        using \<open>E \<in> CCC \<union> {BB, C} \<and> x \<in> set E\<close> by blast
    qed
  qed
qed

lemma distinct_hd: "distinct (x#xs) \<Longrightarrow> distinct xs" 
  by auto

lemma distinct_last: "distinct (xs@[x]) \<Longrightarrow> distinct xs" 
  by force

lemma distinct_split1: "distinct (xs@ys) \<Longrightarrow> distinct xs "  
  by auto

lemma distinct_split2: "distinct (xs@ys) \<Longrightarrow> distinct ys "   
  by auto

lemma distinct_inter: "distinct (xs@ys@zs) \<Longrightarrow> distinct (xs@zs)"
  by auto

lemma distinct_swap: "distinct (xs@ys@zs) \<Longrightarrow> distinct (xs@zs@ys)"
  by auto

lemma disjoint_lists_sublists:
  assumes "\<And> X Y. X \<in> XX \<Longrightarrow> Y \<in> XX \<Longrightarrow> X \<noteq> Y \<Longrightarrow> set X \<inter> set Y = {}"
          "A \<in> XX"
          "setA \<supseteq> set E \<union> set G"
          "setA = set A"
          "set E \<inter> set G = {}"
          "distinct A"
    shows "\<And> X Y. X \<in> XX-{A} \<union>{E,G} \<Longrightarrow> Y \<in> XX-{A} \<union>{E,G} \<Longrightarrow> X \<noteq> Y \<Longrightarrow> set X \<inter> set Y = {}"
proof-
  fix X Y
  assume "X \<in> XX - {A} \<union> {E, G} " " Y \<in> XX - {A} \<union> {E, G} " "X \<noteq> Y "
  then show "set X \<inter> set Y = {}"
  proof(cases "X = E")
    case True
    hence "X = E" by simp
    then show ?thesis 
    proof(cases "Y = G")
      case True
      then show ?thesis using assms 
        using \<open>X = E\<close> by force
    next
      case False
      hence "Y \<in> XX" 
        using True \<open>X \<noteq> Y\<close> \<open>Y \<in> XX - {A} \<union> {E, G}\<close> by blast 
      moreover have "set X \<subseteq> set A" 
        using True assms by auto
      ultimately show ?thesis using assms(1)[of Y A] 
        using True \<open>X \<noteq> Y\<close> \<open>Y \<in> XX - {A} \<union> {E, G}\<close> assms(2) assms by auto
    qed
  next
    case False
    hence "X \<noteq> E" by simp
    then show ?thesis
    proof(cases "X = G")
      case True
      hence "X = G" by simp
      then show ?thesis 
      proof(cases "Y = E")
      case True
       then show ?thesis using assms 
        using \<open>X = G\<close> by blast
      next
      case False
        hence "Y \<in> XX" 
        using True \<open>X \<noteq> Y\<close> \<open>Y \<in> XX - {A} \<union> {E, G}\<close> by blast 
      moreover have "set X \<subseteq> set A" 
        using True assms  by auto
      ultimately show ?thesis using assms(1)[of Y A] 
        using True \<open>X \<noteq> Y\<close> \<open>Y \<in> XX - {A} \<union> {E, G}\<close> assms(2) assms by auto
      qed
    next
      case False
      hence a: "X \<in> XX" 
        using \<open>X \<in> XX - {A} \<union> {E, G}\<close> \<open>X \<noteq> E\<close> by blast
      moreover have b: "X \<noteq> A" 
        using False \<open>X \<in> XX - {A} \<union> {E, G}\<close> \<open>X \<noteq> E\<close> by fastforce
      ultimately  show ?thesis 
        apply(cases "Y = E")
        using  assms(1)[of X A] a b assms(2) assms apply fast
        apply(cases "Y = G")
        using  assms(1)[of X A] a b assms(2) assms  \<open>Y \<in> XX - {A} \<union> {E, G}\<close>
               \<open>X \<noteq> Y\<close> \<open>Y \<in> XX - {A} \<union> {E, G}\<close> \<open>\<lbrakk>X \<in> XX; A \<in> XX; X \<noteq> A\<rbrakk> \<Longrightarrow> set X \<inter> set A = {}\<close> 
              assms(1)[of X Y ] assms(2) assms(3) assms(4) 
        by fastforce+
    qed
  qed
qed

lemma disjoint_lists_sublists':
  assumes "\<And> X Y. X \<in> XX \<Longrightarrow> Y \<in> XX \<Longrightarrow> X \<noteq> Y \<Longrightarrow> set X \<inter> set Y = {}"
          "A \<subseteq> XX"
          "setA \<supseteq> set E \<union> set G"
          "setA = (\<Union> {set H| H. H \<in> A})"
          "set E \<inter> set G = {}"
          "\<And> H. H \<in> A \<Longrightarrow> distinct H"
  shows   "\<And> X Y. 
           X \<in> XX-A \<union>{E,G} \<Longrightarrow> Y \<in> XX-A \<union>{E,G} \<Longrightarrow> X \<noteq> Y \<Longrightarrow> set X \<inter> set Y = {}"
proof-
  fix X Y
  assume "X \<in> XX - A \<union> {E, G} " " Y \<in> XX - A \<union> {E, G} " "X \<noteq> Y "
  then show "set X \<inter> set Y = {}"
  proof(cases "X = E")
    case True
    hence "X = E" by simp
    then show ?thesis 
    proof(cases "Y = G")
      case True
      then show ?thesis using assms 
        using \<open>X = E\<close> by force
    next
      case False
      hence "Y \<in> XX" 
        using True \<open>X \<noteq> Y\<close> \<open>Y \<in> XX - A \<union> {E, G}\<close> by blast 
      moreover have "set X \<subseteq> (\<Union> {set H| H. H \<in> A})" 
        using True assms by auto
      ultimately show ?thesis using assms(1)
        using True \<open>X \<noteq> Y\<close> \<open>Y \<in> XX - A \<union> {E, G}\<close> assms(2) assms by auto
    qed
  next
    case False
    hence "X \<noteq> E" by simp
    then show ?thesis
    proof(cases "X = G")
      case True
      hence "X = G" by simp
      then show ?thesis 
      proof(cases "Y = E")
      case True
       then show ?thesis using assms 
        using \<open>X = G\<close> by blast
      next
      case False
        hence "Y \<in> XX" 
        using True \<open>X \<noteq> Y\<close> \<open>Y \<in> XX - A \<union> {E, G}\<close> by blast 
      moreover have "set X \<subseteq> (\<Union> {set H| H. H \<in> A})" 
        using True assms  by auto
      ultimately show ?thesis using assms(1)
        using True \<open>X \<noteq> Y\<close> \<open>Y \<in> XX - A \<union> {E, G}\<close> assms(2) assms by auto
      qed
    next
      case False
      hence a: "X \<in> XX" 
        using \<open>X \<in> XX - A \<union> {E, G}\<close> \<open>X \<noteq> E\<close> by blast
      moreover have b: "X \<notin> A" 
        using False \<open>X \<in> XX - A \<union> {E, G}\<close> \<open>X \<noteq> E\<close> by fastforce
      ultimately  show ?thesis 
        apply(cases "Y = E")
        subgoal 
      proof-
        assume yassm:"X \<in> XX" "X \<notin> A" "Y = E"
        hence "set Y \<subseteq> setA" 
          using assms(3) by auto
        show "set X \<inter> set Y = {}"        
        proof(rule ccontr)
          assume "set X \<inter> set Y \<noteq> {}"
          then obtain y where "y \<in> set X \<inter> set Y " by auto
          hence "y \<in> \<Union> {set H |H. H \<in> A}" 
            using \<open>set Y \<subseteq> setA\<close> assms(4) by blast
          then obtain  Z where "Z \<in> A \<and> y \<in> set Z " by auto
          have "Z \<noteq> X" 
            using \<open>Z \<in> A \<and> y \<in> set Z\<close> b by blast
          moreover have "Z \<in> XX \<and> X \<in> XX" 
            using \<open>Z \<in> A \<and> y \<in> set Z\<close> a assms(2) by blast
          ultimately show False 
            using \<open>Z \<in> A \<and> y \<in> set Z\<close> \<open>y \<in> set X \<inter> set Y\<close> assms(1) by auto
        qed 
      qed
      apply(cases "Y = G")
        subgoal 
      proof-
        assume yassm:"X \<in> XX" "X \<notin> A" "Y = G"
        hence "set Y \<subseteq> setA" 
          using assms(3) by auto
        show "set X \<inter> set Y = {}"        
        proof(rule ccontr)
          assume "set X \<inter> set Y \<noteq> {}"
          then obtain y where "y \<in> set X \<inter> set Y " by auto
          hence "y \<in> \<Union> {set H |H. H \<in> A}" 
            using \<open>set Y \<subseteq> setA\<close> assms(4) by blast
          then obtain  Z where "Z \<in> A \<and> y \<in> set Z " by auto
          have "Z \<noteq> X" 
            using \<open>Z \<in> A \<and> y \<in> set Z\<close> b by blast
          moreover have "Z \<in> XX \<and> X \<in> XX" 
            using \<open>Z \<in> A \<and> y \<in> set Z\<close> a assms(2) by blast
          ultimately show False 
            using \<open>Z \<in> A \<and> y \<in> set Z\<close> \<open>y \<in> set X \<inter> set Y\<close> assms(1) by auto
        qed 
      qed
      using \<open>X \<noteq> Y\<close> \<open>Y \<in> XX - A \<union> {E, G}\<close> assms(1) by force
    qed
  qed
qed

lemma distinct_single_extract:
  assumes "distinct (xs@[x]@ys)" 
  shows   "set (xs@ys) = set (xs@[x]@ys) - {x}"
proof
  show "set (xs @ ys) \<subseteq> set (xs @ [x] @ ys) - {x}"
  proof
    fix y
    assume " y \<in> set (xs @ ys) "
    hence "y \<in> set xs \<or> y \<in> set ys" by simp
    have "y \<noteq> x" 
      using \<open>y \<in> set xs \<or> y \<in> set ys\<close> assms by auto
    then show "y \<in> set (xs @ [x] @ ys) - {x}" 
      using \<open>y \<in> set xs \<or> y \<in> set ys\<close> by auto
  qed
  show "set (xs @ [x] @ ys) - {x} \<subseteq> set (xs @ ys)" 
  proof
   fix y
   assume " y \<in> set (xs @ [x] @ ys) - {x}"
   hence "y \<noteq> x" by auto
   thus " y \<in> set (xs @ ys) " 
     using \<open>y \<in> set (xs @ [x] @ ys) - {x}\<close> by auto
 qed
qed

lemma set_append_swap: "set (xs@ys) = set (ys@xs)" by auto

lemma in_union_of_sets_append:"\<Union> {set xs| xs. xs \<in> xss \<union> {ys,zs}} = 
                                 \<Union> {set xs| xs. xs \<in> xss \<union> {ys@zs}}"
  by fastforce

lemma extract_first_x:
"x \<in> set xs \<Longrightarrow> P x \<Longrightarrow> \<exists> y ys zs. xs = ys@[y]@zs \<and> P y \<and>( \<nexists> z. z \<in> set ys \<and>  P z)"
  apply(induction xs, simp)
  subgoal for a xs
    apply(cases "P a") 
    apply fastforce
    by (metis append_Cons set_ConsD)
  done

lemma extract_last_x:
       "x \<in> set xs \<Longrightarrow> P x \<Longrightarrow> \<exists> y ys zs. xs = ys@[y]@zs \<and> P y \<and>( \<nexists> z. z \<in> set zs \<and>  P z)"
proof(induction xs arbitrary: x)
  case (Cons xx xs)
  then show ?case 
  proof(cases xs)
    case Nil
    then show ?thesis 
      using Cons.prems(1) Cons.prems(2) by fastforce
  next
    case (Cons a list)
    then show ?thesis 
    proof(cases "\<exists> z. z \<in> set list \<and> P z")
      case True
      then obtain y ys zs where "xs = ys@[y]@zs \<and> P y \<and>( \<nexists> z. z \<in> set zs \<and>  P z)" 
        by (metis Cons.IH list.set_intros(2) local.Cons)
      then show ?thesis 
        by (metis append_Cons)
    next
      case False
      hence "P a \<or> P x"
        using Cons.prems(2) by blast 
      then show ?thesis 
        apply (cases "P a")
        apply (metis False append.left_neutral append_Cons local.Cons)
        by    (metis Cons.prems(1) False append.left_neutral append_Cons local.Cons set_ConsD)
    qed
  qed
qed simp

text \<open>This lemma is a little bit more interesting: If there are list elements with a certain property,
then there are also a first and a last element satisfying that condition. 
Quite intuitive, but requires a formal proof.\<close>

lemma extract_first_and_last:
  assumes "x \<in> set xs"
          "y \<in> set xs"
          "P x"
          "P y"
          "x \<noteq> y"
    shows "\<exists> a b as bs cs. 
             xs = as @[a]@bs@[b]@cs \<and> P a \<and> P b 
             \<and> (\<nexists> z. z \<in> set as \<and> P z)
             \<and> (\<nexists> z. z \<in> set cs \<and> P z)"
proof-
  obtain as a rest where asarest:"xs = as@[a]@rest \<and> P a \<and> (\<nexists> z. z \<in> set as \<and> P z)" 
    by (metis assms(2) assms(4) extract_first_x)
  hence "\<exists> z. z \<in> set rest \<and> P z"
    using assms by auto
  then obtain bs b cs where bsdcs:"rest = bs@[b]@cs \<and> P b \<and> (\<nexists>z. z \<in> set cs \<and> P z)" 
    by (metis extract_last_x)
  thus ?thesis using asarest by force
qed

lemma map_hd: "xs \<noteq> [] \<Longrightarrow> hd (map f xs) = f (hd (xs))" 
  using list.map_sel(1) by auto

lemma map_last': "xs \<noteq> [] \<Longrightarrow>(\<And> x. g (f x) = h x) \<Longrightarrow>g (last (map f xs)) = h (last xs)"
  by (metis last_map)

lemma in_set_map: "y \<in> set (map f xs) \<Longrightarrow> \<exists> x. y = f x \<and> x \<in> set xs" by auto

lemma map_in_set: "x\<in> set xs \<Longrightarrow> f x \<in> set (map f xs)"
  by(induction xs) (auto simp add: list.set_intros(2) set_ConsD)

lemma single_in_append: "([a]@xs) = a#xs" by simp

lemma map_split_exists:"map f xs = ys@zs \<Longrightarrow> 
                           \<exists> ys' zs'. ys'@zs' = xs \<and> map f ys' = ys \<and> map f zs' = zs"
  by (metis append_eq_map_conv)

lemma map_sum_split: "foldr (\<lambda> x acc. f x + acc) (xs@ys) (0::real) = 
                      foldr (\<lambda> x acc. f x + acc) xs 0 +
                      foldr (\<lambda> x acc. f x + acc) ys 0"
  by(induction xs) simp+

lemma fold_sum_neg_neg_element:"foldr (\<lambda> x acc. f x + acc) xs (0::real) < 0 \<Longrightarrow> \<exists> x \<in> set xs. f x < 0"
  by(induction xs) force+

lemma butlast_tail: "xs \<noteq> [] \<Longrightarrow> butlast (x#xs) = x#butlast xs" for x xs by simp

lemma inter_distr_append: "(set (xs@ys) \<inter> set zs= {}) = 
                              (set (xs) \<inter> set zs= {} \<and> set (ys) \<inter> set zs= {})"for xs ys zs by auto

lemma in_append_split: "(z \<in> set (xs @ ys)) = (z \<in> set xs \<or> z \<in> set ys)" for z ys xs by simp  

lemma non_empt_elim:"xs \<noteq> [] \<Longrightarrow> (\<And> a list. xs = a#list \<Longrightarrow> P xs) \<Longrightarrow> P xs"
  by(cases xs, auto)

lemma non_empt_elim_triple:
 " (\<And> x. xs = [x] \<Longrightarrow> P xs) \<Longrightarrow> (\<And> x y ys. x#y#ys = xs \<Longrightarrow> P xs) \<Longrightarrow>xs \<noteq> [] \<Longrightarrow> P xs"
  apply(cases xs, force)
  subgoal for a list
    by(cases list, auto)
  done

lemma nth_append':"(xs@ys) ! i = (xs@ys) ! j \<Longrightarrow> i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> xs ! i =xs ! j"for xs ys j i
  by (metis nth_append)

lemma list_cases4:"(xs = [] \<Longrightarrow> P) \<Longrightarrow>
       (\<And> x. xs = [x] \<Longrightarrow> P) \<Longrightarrow>
       (\<And> x y. xs = x#y#[] \<Longrightarrow> P) \<Longrightarrow>
       (\<And> x y z zs. xs = x#y#z#zs \<Longrightarrow> P) \<Longrightarrow> P"
  by(cases xs, force, metis neq_Nil_conv)

lemma  set_singleton_list: "set [ x] = {x}" for x by simp

lemmas list_cases3 = remdups_adj.cases

lemma append_two: "[a]@[b] = [a,b]" for a b by simp

lemma list_induct3: "P Nil \<Longrightarrow> (\<And> x. P [x]) \<Longrightarrow> (\<And> x y xs. P (y#xs) \<Longrightarrow> P (x#y#xs)) \<Longrightarrow> P xs" for xs P
    by (metis list_nonempty_induct neq_Nil_conv)

lemma list_induct3_len_geq_2: "length xs \<ge> 2 \<Longrightarrow> (\<And> x y. P [x,y]) \<Longrightarrow> (\<And> x y xs. P (y#xs) \<Longrightarrow> P (x#y#xs)) \<Longrightarrow> P xs" for xs P
  apply(induction rule: list_induct3)
  using not_less_eq_eq by fastforce+

lemma list_induct2_len_geq_1: "length xs \<ge> 1 \<Longrightarrow>
 (\<And> x. P [x]) \<Longrightarrow> (\<And> x y xs. P (y#xs) \<Longrightarrow> P (x#y#xs)) \<Longrightarrow> P xs" for xs P
  by (metis One_nat_def length_greater_0_conv less_eq_Suc_le list.exhaust_sel list_nonempty_induct)

lemma snoc_eq_iff_butlast':
  "ys = xs @ [x] \<longleftrightarrow> (ys \<noteq> [] \<and> butlast ys = xs \<and> last ys = x)"
  by fastforce

lemma neq_Nil_conv_snoc: "xs \<noteq> [] \<longleftrightarrow> (\<exists>x ys. xs = ys @ [x])"
  by (meson snoc_eq_iff_butlast')

lemma list_cases_both_sides: 
"(xs = [] \<Longrightarrow> P ) \<Longrightarrow> (\<And> x. xs =[x] \<Longrightarrow> P ) \<Longrightarrow> (\<And> x y ys. xs =[x]@ys@[y] \<Longrightarrow> P ) \<Longrightarrow> P "
  by (metis neq_Nil_conv neq_Nil_conv_snoc single_in_append)

lemma append_butlast_last_cancel: "p \<noteq> [] \<Longrightarrow> butlast p @ last p # p' = p @ p'"
  by simp

lemma induct_list_length2: "length xs \<ge> 2 \<Longrightarrow> (\<And> x y. P [x,y]) 
\<Longrightarrow> (\<And> xs x y z. P (xs@[x,y]) \<Longrightarrow> P(xs@[x,y,z])) \<Longrightarrow> P xs"
proof(induction xs rule: rev_induct, simp)
  case (snoc z xs)
  note IH = this
  show ?case 
  proof(cases xs)
    case (Cons b list)
    note cons = this
    show ?thesis 
    proof(cases list)
      case (Cons b llist)
      then obtain ys x y where axs_subst:"xs = ys@[x,y]"
        by (metis append_Cons append_butlast_last_cancel cons list.distinct(1) neq_Nil_conv_snoc)
      show ?thesis
        using axs_subst IH(3,4) snoc.IH 
        by (fastforce intro: IH(4))
    next
      case Nil
      then show ?thesis
        using cons snoc.prems(2) by fastforce
    qed
    next
      case Nil
      then show ?thesis 
        using snoc.prems(1) by force
    qed
  qed

lemma list_cases_betw: "length xs \<ge> 2 \<Longrightarrow> (\<And> x y. xs = [x,y] \<Longrightarrow> P ) 
\<Longrightarrow> (\<And> ys x y. xs = [x]@ys@[y] ==> P) \<Longrightarrow> P"
  by(auto intro: list_cases_both_sides[of xs]) 

lemma get_longest_common_tail:
assumes "length p \<ge> 1" "length q \<ge> 1" "last p = last q"
obtains ys p' q' where "p = p'@ys" "q =q'@ys" 
                        "\<And> ys' p'' q''. p=p''@ys' \<Longrightarrow> q = q''@ys' \<Longrightarrow> length ys' \<le> length ys"
  using assms 
proof(induction "length p" arbitrary: p q thesis rule: less_induct)
  case less
  then obtain pa a where p_last:"p = pa@[a]"
    by (metis append_butlast_last_id list.size(3) not_one_le_zero)
  from less obtain qb b where q_last:"q = qb@[b]"
    by (metis append_butlast_last_id list.size(3) not_one_le_zero)
  have butlasts: "butlast p = pa" "butlast q = qb"
    by (auto simp add: p_last q_last)
  have last_q: "last q = a"
    using less.prems(4) p_last by auto
  show ?case
  proof(cases pa)
    case Nil
    then have "p = []@[a]" "q =qb@[a]" 
                        "\<And> ys' p'' q''. pa=p''@ys' \<Longrightarrow> qb = q''@ys' \<Longrightarrow> length ys' \<le> length [a]"
      using less.prems(4) p_last q_last  local.Nil by force+
    then show ?thesis 
      using less.prems(1) by fastforce
  next
    case (Cons x list)
    note cons = this
    show ?thesis
  proof(cases qb)
    case Nil
      then have "p = pa@[a]" "q =[]@[a]" 
                        "\<And> ys' p'' q''. p=p''@ys' \<Longrightarrow> q= q''@ys' \<Longrightarrow> length ys' \<le> length [a]"
        using less.prems(4) local.Nil p_last q_last apply(fastforce, fastforce)
        subgoal for ys' p'' q''
          using  local.Nil q_last by(cases ys') (auto simp add: Cons_eq_append_conv)
        done
      thus ?thesis     
        using less.prems(1) by force 
    next
      case (Cons y kist)
      show ?thesis
      proof(cases "last pa = last qb")
        case True
      obtain  p' q' ys  where IH_applied:"pa = p'@ys" "qb =q'@ys" 
                        "\<And> ys' p'' q''. pa=p''@ys' \<Longrightarrow> qb = q''@ys' \<Longrightarrow> length ys' \<le> length ys"
        using butlasts p_last cons Cons True 
        by (auto intro: less(1)[of "butlast p" qb, simplified butlasts(1)])
      hence "p = p'@ys@[a]" "q=q'@ys@[a]" 
                        "\<And> ys' p'' q''. p=p''@ys' \<Longrightarrow> q = q''@ys' \<Longrightarrow> length ys' \<le> length (ys@[a])"
        using IH_applied(2) last_q q_last apply(auto simp add: p_last)[2]
        subgoal for ys' p'' q''
          using last_q  p_last IH_applied(3)[of p'' "butlast ys'" q''] butlasts(2)
          by(cases ys' rule: rev_cases) (auto simp add: butlast_append)
        done
      then show ?thesis 
        using less.prems(1) by force
    next
      case False
      hence "p = pa@[a]" "q =qb@[a]" 
                        "\<And> ys' p'' q''. p=p''@ys' \<Longrightarrow> q = q''@ys' \<Longrightarrow> length ys' \<le> length [a]"
        using last_q q_last p_last apply auto[2]
        subgoal for ys' p'' q''
          apply(cases ys' rule: rev_cases, simp)
          using False  butlasts last_q p_last
          by (auto, metis append.assoc butlast_snoc last_appendR)
        done
      thus ?thesis
        using less.prems(1) by force
    qed
  qed
qed
qed

lemma inter_Big_union_distr_empt_list:
               "(\<And> C. C \<in> B \<Longrightarrow> A \<inter> set C = {}) \<Longrightarrow> (A \<inter> \<Union> { set C| C. C \<in> B}) = {}" for A B by auto

end