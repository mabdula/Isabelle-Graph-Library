theory More_Lists
  imports Main "HOL-Library.Extended_Real"
begin

lemma list_2_preds_aux:
  "\<lbrakk>x' \<in> set xs; P1 x'; \<And>xs1 x xs2. \<lbrakk>xs = xs1 @ [x] @ xs2; P1 x\<rbrakk> \<Longrightarrow>
      \<exists>ys1 y ys2. x # xs2 = ys1 @ [y] @ ys2 \<and> P2 y\<rbrakk> \<Longrightarrow> 
     \<exists> xs1 x xs2. xs = xs1 @ [x] @ xs2 \<and> P2 x \<and> (\<forall>y\<in>set xs2. \<not> P1 y)"
proof(goal_cases)
  case assms: 1
  define property 
       where "property xs =
                (\<forall>xs2 xs1 x. (xs = xs1 @ [x] @ xs2 \<and> P1 x) \<longrightarrow>
                   (\<exists>ys1 y ys2. x#xs2 = ys1 @ [y] @ ys2 \<and> P2 y))"
       for xs
  have propE: "\<lbrakk>property xs;
               (\<And>xs1 x xs2. \<lbrakk>xs = xs1 @ [x] @ xs2; P1 x\<rbrakk> \<Longrightarrow>
                  \<exists>ys1 y ys2. x#xs2 = ys1 @ [y] @ ys2 \<and> P2 y) \<Longrightarrow> P\<rbrakk>
              \<Longrightarrow> P" for xs P
    by(auto simp add: property_def)
  have property_append: "property (xs @ ys) \<Longrightarrow> property ys" for xs ys
    by(auto simp: property_def)
  have "property xs"
    using assms(3)
    by (force simp: property_def)
  thus  ?thesis
    using assms(1,2)
  proof(induction xs arbitrary: x')
    case Nil
    then show ?case 
      by auto
  next
    case (Cons a xs)
    hence "property xs" 
      by(auto intro: property_append[where xs = "[a]"])
    show ?case
    proof(cases "x' = a")
      case x_eq_a: True
      then obtain ys1 y ys2 where "x'#xs = ys1 @ [y] @ ys2" "P2 y"
        using \<open>property (a # xs)\<close> \<open>P1 x'\<close>
        apply(elim propE)
        by (auto 10 10)
      show ?thesis
      proof(cases "ys1 = []")
        case ys1_empty: True
        hence "xs = ys2"
          using \<open>x'#xs = ys1 @ [y] @ ys2\<close>
          by auto
        then show ?thesis
        proof(cases "\<exists>x\<in>set ys2. P1 x")
          case x_in_ys2: True
          then obtain x where "x \<in> set ys2" "P1 x"
            by auto
          hence "\<exists>xs1 x xs2. xs = xs1 @ [x] @ xs2 \<and> P2 x \<and> (\<forall>y\<in>set xs2. \<not> P1 y)"
            using \<open>property xs\<close> \<open>xs = ys2\<close> \<open>P2 y\<close>
            apply(intro Cons(1))
            by auto
          then obtain xs1 x xs2 where "(a # xs) = (a #xs1) @ [x] @ xs2 \<and> P2 x \<and> (\<forall>y\<in>set xs2. \<not> P1 y)"
            by auto
          then show ?thesis
            by metis
        next
          case x_notin_ys2: False
          hence "a # xs = a#ys2 \<and> P2 y \<and> (\<forall>y\<in>set ys2. \<not> P1 y)"
            using \<open>xs = ys2\<close> \<open>P2 y\<close>
            by auto
          then show ?thesis
            using \<open>x' # xs = ys1 @ [y] @ ys2\<close> x_eq_a
            by blast
        qed
      next
        case ys2_nempty: False
        then obtain ys1' where "xs = ys1' @ [y] @ ys2"
          using \<open>x'#xs = ys1 @ [y] @ ys2\<close>
          by (auto simp: neq_Nil_conv)
        show ?thesis
        proof(cases "\<exists>x\<in>set ys2. P1 x")
          case x_in_ys2: True
          then obtain x where "x \<in> set ys2" "P1 x"
            by auto
          hence "\<exists>xs1 x xs2. xs = xs1 @ [x] @ xs2 \<and> P2 x \<and> (\<forall>y\<in>set xs2. \<not> P1 y)"
            using \<open>property xs\<close> \<open>xs = ys1' @ [y] @ ys2\<close> \<open>P2 y\<close>
            apply(intro Cons(1))
            by auto
          then obtain xs1 x xs2 where "(a # xs) = (a #xs1) @ [x] @ xs2 \<and> P2 x \<and> (\<forall>y\<in>set xs2. \<not> P1 y)"
            by auto
          then show ?thesis
            by metis
        next
          case x_notin_ys2: False
          hence "a # xs = (a# ys1') @ [y] @ ys2 \<and> P2 y \<and> (\<forall>y\<in>set ys2. \<not> P1 y)"
            using \<open>xs = ys1' @ [y] @ ys2\<close> \<open>P2 y\<close>
            by auto
          then show ?thesis
            by metis
        qed
      qed
    next
      case x_neq_a: False
      hence "x' \<in> set xs"
        using Cons
        by auto
      then obtain xs1 x xs2 where "xs = xs1 @ [x] @ xs2" "P2 x" "(\<forall>y\<in>set xs2. \<not> P1 y)"
        using Cons \<open>property xs\<close>
        by blast
      hence "a # xs = (a # xs1) @ [x] @ xs2 \<and> P2 x \<and> (\<forall>y\<in>set xs2. \<not> P1 y)"
        by auto
      thus ?thesis
        by metis
    qed
  qed
qed

lemma list_2_preds:
  "\<lbrakk> x\<in>set xs; P1 x; 
     \<And>xs1 x xs2. \<lbrakk>xs = xs1 @ [x] @ xs2; P1 x\<rbrakk> \<Longrightarrow> \<exists>ys1 y ys2. x#xs2 = ys1 @ [y] @ ys2 \<and> P2 y\<rbrakk> 
   \<Longrightarrow>  \<exists> xs1 x xs2. xs = xs1 @ [x] @ xs2 \<and> P2 x \<and> (\<forall>y\<in>set xs2. \<not> P1 y \<and> \<not> P2 y)"
proof(goal_cases)
  case assms: 1
  hence "\<exists>xs1 x xs2. xs = xs1 @ [x] @ xs2 \<and> P2 x \<and> (\<forall>y\<in>set xs2. \<not> P1 y)"
    by (fastforce intro!: list_2_preds_aux)
  then obtain xs1 x xs2 where "xs = xs1 @ [x] @ xs2" "P2 x" "(\<forall>y\<in>set xs2. \<not> P1 y)"
    by auto
  hence "\<exists>ys1 y ys2. x # xs2 = ys1 @ [y] @ ys2 \<and> P2 y \<and> (\<forall>z\<in>set ys2. \<not> P2 z)"
    by (auto intro!: split_list_last_prop)
  then obtain ys1 y ys2 where "x # xs2 = ys1 @ [y] @ ys2" "P2 y" "(\<forall>z\<in>set ys2. \<not> P2 z)"
    by auto
  hence "(\<forall>z\<in>set ys2. \<not>P1 z \<and> \<not> P2 z)"
    using \<open>(\<forall>y\<in>set xs2. \<not> P1 y)\<close> \<open>P2 x\<close>
    by (metis Un_iff insert_iff list.simps(15) set_append)
  moreover have "xs = (xs1 @ ys1) @ [y] @ ys2"
    using \<open>xs = xs1 @ [x] @ xs2\<close> \<open>x # xs2 = ys1 @ [y] @ ys2\<close>
    by auto
  ultimately show ?case
    using \<open>P2 y\<close>
    by fastforce
qed

lemma list_inter_mem_iff: "set xs \<inter> s \<noteq> {} \<longleftrightarrow> (\<exists>xs1 x xs2. xs = xs1 @ [x] @ xs2 \<and> x \<in> s)"
  by (metis append.left_neutral append_Cons disjoint_iff in_set_conv_decomp)

lemma list_P_switch: 
  "\<lbrakk>x \<in> set xs; P x; y \<in> set xs; \<not> P y\<rbrakk>
   \<Longrightarrow> \<exists> p1 p2 x' y'. xs =p1@[x',y']@p2 \<and> ((P x' \<and> \<not> P y') \<or> (P y' \<and> \<not> P x'))"
proof(induction xs arbitrary: x y)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  note IH = this
  then show ?case 
  proof(cases xs)
    case Nil
    then show ?thesis 
      using Cons by simp
  next
    case (Cons b ys)
    then show ?thesis 
    proof(cases "((P a \<and> \<not> P b) \<or> (P b \<and> \<not> P a))")
      case True
      then show ?thesis 
        using Cons True by(auto intro: exI[of "\<lambda> p1. \<exists>p2 x' y'.  _ y' x' p2 p1" Nil] exI[of _ ys])
    next
      case False
      hence alt:"(P a \<and> P b) \<or> (\<not> P a \<and> \<not> P b)" by auto
      have "\<exists>p1 p2 x' y'. xs = p1 @ [x', y'] @ p2 \<and> (P x' \<and> \<not> P y' \<or> P y' \<and> \<not> P x')"   
        using IH Cons by (cases rule: disjE[OF alt]) force+
      then obtain p1 x' y' p2 where "xs = p1 @ [x', y'] @ p2 \<and> (P x' \<and> \<not> P y' \<or> P y' \<and> \<not> P x')"
        by auto
      then show ?thesis
        by(auto intro!: exI[of "\<lambda> p1. \<exists> p2 x' y'. _ p2 x' y' p1" "a#p1"])
    qed
  qed
qed

lemma sum_list_map_filter_split: 
"sum_list (map (f::'s\<Rightarrow> real) xs) = sum_list (map f (filter P xs)) +
 sum_list (map f (filter (\<lambda> x. \<not> P x) xs))"
  by(induction xs)(auto simp add: algebra_simps)

lemma takeWhile_everything: "(\<And> x. x \<in> set xs \<Longrightarrow> P x) \<Longrightarrow> takeWhile P xs = xs"
  by(induction xs) auto

lemma dropWhile_nothing: "(\<And> x. x \<in> set xs \<Longrightarrow> \<not> P x) \<Longrightarrow> dropWhile P xs = xs"
  by(induction xs) auto

lemma foldr_plus_add_right:
  "(c::real)+ foldr (\<lambda>e. (+) (f e)) xs b = foldr (\<lambda>e. (+) (f e)) (xs) (c + b)"
  by(induction xs arbitrary: c b)
  (auto simp add: algebra_simps)

lemma bulast_subset: "set (butlast xs) \<subseteq> set xs" for xs 
  using in_set_butlastD by fastforce

lemma singleton_hd_last: "\<lbrakk>q \<noteq> []; tl q = []\<rbrakk> \<Longrightarrow> hd q = last q"
  by (cases q) auto

lemma hd_last_same: "length xs = 1 \<Longrightarrow> hd xs = last xs" for xs 
  using singleton_hd_last[of xs] 
  by(cases xs) auto
       
lemma last_simp : "last (a#b#cs) = last (b#cs)" by simp

lemma list_triple_split_mid_distinct:
  "\<lbrakk>length xs = n; \<not> distinct xs\<rbrakk>
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

lemma double_occur_non_dist: 
  "\<lbrakk>set (xs) \<subseteq> X; card X < length xs; finite X; xs \<noteq> []\<rbrakk> \<Longrightarrow> \<not> distinct xs"
  by(induction "card X" arbitrary: X xs, auto)
    (metis card_mono distinct_card linorder_not_less)

lemma subset_big_union_diff:
assumes "set C = (set D) - A " "A = set D - set C" "D \<in> CCC" "C \<notin> CCC" "C \<noteq> D"
        "(\<And> B E. \<lbrakk>B \<in> CCC; E \<in> CCC; B \<noteq> E\<rbrakk> \<Longrightarrow> set E \<inter> set B = {})"
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
    have "\<lbrakk>x \<in> set E; x \<in> A\<rbrakk> \<Longrightarrow> set E \<inter> set D \<noteq> {}"
    using assms
    by blast 
    from E_def show "x \<in> \<Union> {set B |B. B \<in> CCC} - A"
      using \<open>x \<in> set E \<and> E \<in> CCC - {D} \<union> {C}\<close> assms(1,3,6)
            \<open>x \<in> set E \<Longrightarrow> x \<in> A \<Longrightarrow> set E \<inter> set D \<noteq> {}\<close> 
      by (cases "E = C")force+
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
  assumes "\<And> X Y. \<lbrakk>X \<in> XX; Y \<in> XX; X \<noteq> Y\<rbrakk> \<Longrightarrow> set X \<inter> set Y = {}"
          "A \<in> XX"
          "setA \<supseteq> set E \<union> set G"
          "setA = set A"
          "set E \<inter> set G = {}"
          "distinct A"
    shows "\<And> X Y. \<lbrakk>X \<in> XX-{A} \<union>{E,G}; Y \<in> XX-{A} \<union>{E,G}; X \<noteq> Y\<rbrakk> \<Longrightarrow> set X \<inter> set Y = {}"
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
      proof(cases "Y = E", goal_cases)
        case 1
        thus ?case
          using  assms(1)[of X A] a b assms(2) assms by fast
      next
        case 2
        thus ?case
        using  assms(1)[of X A] a b  assms  \<open>Y \<in> XX - {A} \<union> {E, G}\<close>
               \<open>X \<noteq> Y\<close> \<open>Y \<in> XX - {A} \<union> {E, G}\<close> \<open>\<lbrakk>X \<in> XX; A \<in> XX; X \<noteq> A\<rbrakk> \<Longrightarrow> set X \<inter> set A = {}\<close> 
              assms(1)[of X Y ] 
        by (cases "Y = G") fastforce+
     qed
    qed
  qed
qed

lemma disjoint_lists_sublists':
  assumes "\<And> X Y. \<lbrakk>X \<in> XX; Y \<in> XX; X \<noteq> Y\<rbrakk> \<Longrightarrow> set X \<inter> set Y = {}"
          "A \<subseteq> XX"
          "setA \<supseteq> set E \<union> set G"
          "setA = (\<Union> {set H| H. H \<in> A})"
          "set E \<inter> set G = {}"
          "\<And> H. H \<in> A \<Longrightarrow> distinct H"
  shows   "\<And> X Y. 
           \<lbrakk>X \<in> XX-A \<union>{E,G}; Y \<in> XX-A \<union>{E,G}; X \<noteq> Y\<rbrakk> \<Longrightarrow> set X \<inter> set Y = {}"
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
      proof(cases "Y = E", goal_cases)
        case 1
        note yassm = this
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
      next 
        case 2
        thus ?case
        proof(cases "Y = G", goal_cases)
          case 1
          note yassm = this
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
      next
        case 2
        thus ?case
          using \<open>X \<noteq> Y\<close> \<open>Y \<in> XX - A \<union> {E, G}\<close> assms(1) by force
      qed
    qed
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

lemma in_union_of_sets_append:
 "\<Union> {set xs| xs. xs \<in> xss \<union> {ys,zs}} = \<Union> {set xs| xs. xs \<in> xss \<union> {ys@zs}}"
  by fastforce

lemma extract_first_x:
  "\<lbrakk>x \<in> set xs; P x\<rbrakk> \<Longrightarrow> \<exists> y ys zs. xs = ys@[y]@zs \<and> P y \<and>( \<nexists> z. z \<in> set ys \<and>  P z)"
  apply(induction xs, simp)
  subgoal for a xs
    apply(cases "P a") 
    apply fastforce
    by (metis append_Cons set_ConsD)
  done

lemma extract_last_x:
  "\<lbrakk>x \<in> set xs; P x\<rbrakk> \<Longrightarrow> \<exists> y ys zs. xs = ys@[y]@zs \<and> P y \<and>( \<nexists> z. z \<in> set zs \<and>  P z)"
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
      proof(cases "P a", goal_cases)
        case 1
        thus ?case
          using False Cons
          by (auto intro!: exI[of _ a] intro: exI[of _ "[xx]"])
      next
        case 2
        thus ?case
          using Cons.prems(1) False local.Cons
          by(auto intro!: exI[of _ xx] intro: exI[of _  Nil])
      qed
    qed
  qed
qed simp

text \<open>This lemma is a little bit more interesting: If there are list elements with a certain property,
then there are also a first and a last element satisfying that condition. 
Quite intuitive, but requires a formal proof.\<close>

lemma extract_first_and_last:
  assumes "x \<in> set xs" "y \<in> set xs" "P x" "P y" "x \<noteq> y"
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

lemma map_last': "\<lbrakk>xs \<noteq> []; \<And> x. g (f x) = h x\<rbrakk> \<Longrightarrow>g (last (map f xs)) = h (last xs)"
  by (metis last_map)

lemma in_set_map: "y \<in> set (map f xs) \<Longrightarrow> \<exists> x. y = f x \<and> x \<in> set xs" by auto

lemma map_in_set: "x\<in> set xs \<Longrightarrow> f x \<in> set (map f xs)"
  by(induction xs) (auto simp add: list.set_intros(2) set_ConsD)

lemma single_in_append: "([a]@xs) = a#xs"
  by simp

lemma map_split_exists:
  "map f xs = ys@zs \<Longrightarrow> \<exists> ys' zs'. ys'@zs' = xs \<and> map f ys' = ys \<and> map f zs' = zs"
  by (metis append_eq_map_conv)

lemma map_sum_split: 
  "foldr (\<lambda> x acc. f x + acc) (xs@ys) (0::real) = 
   foldr (\<lambda> x acc. f x + acc) xs 0 + foldr (\<lambda> x acc. f x + acc) ys 0"
  by(induction xs) simp+

lemma fold_sum_neg_neg_element:
  "foldr (\<lambda> x acc. f x + acc) xs (0::real) < 0 \<Longrightarrow> \<exists> x \<in> set xs. f x < 0"
  by(induction xs) force+

lemma butlast_tail: 
  "xs \<noteq> [] \<Longrightarrow> butlast (x#xs) = x#butlast xs"
  by simp

lemma inter_distr_append: 
  "(set (xs@ys) \<inter> set zs= {}) = 
   (set (xs) \<inter> set zs= {} \<and> set (ys) \<inter> set zs= {})"
  by auto

lemma in_append_split: "(z \<in> set (xs @ ys)) = (z \<in> set xs \<or> z \<in> set ys)" 
  by simp  

lemma non_empt_elim:
  "\<lbrakk>xs \<noteq> []; \<And> a list. xs = a#list \<Longrightarrow> P xs\<rbrakk> \<Longrightarrow> P xs"
  by(cases xs, auto)

lemma non_empt_elim_triple:
 "\<lbrakk>\<And> x. xs = [x] \<Longrightarrow> P xs; \<And> x y ys. x#y#ys = xs \<Longrightarrow> P xs; xs \<noteq> []\<rbrakk> \<Longrightarrow> P xs"
  apply(cases xs, force)
  subgoal for a list
    by(cases list, auto)
  done

lemma nth_append':
  "\<lbrakk>(xs@ys) ! i = (xs@ys) ! j; i < length xs; j < length xs\<rbrakk> \<Longrightarrow> xs ! i =xs ! j"
  by (metis nth_append)

lemma list_cases4:
  "\<lbrakk>xs = [] \<Longrightarrow> P; \<And> x. xs = [x] \<Longrightarrow> P ;
    \<And> x y. xs = x#y#[] \<Longrightarrow> P; \<And> x y z zs. xs = x#y#z#zs \<Longrightarrow> P\<rbrakk>
    \<Longrightarrow> P"
  by(cases xs, force, metis neq_Nil_conv)

lemma  set_singleton_list: "set [ x] = {x}" for x by simp

lemmas list_cases3 = remdups_adj.cases

lemma append_two: "[a]@[b] = [a,b]" 
  by simp

lemma list_induct3: "\<lbrakk>P Nil; \<And> x. P [x]; \<And> x y xs. P (y#xs) \<Longrightarrow> P (x#y#xs)\<rbrakk> \<Longrightarrow> P xs"
  by (metis list_nonempty_induct neq_Nil_conv)

lemma list_induct3_len_geq_2: "length xs \<ge> 2 \<Longrightarrow> (\<And> x y. P [x,y]) \<Longrightarrow> (\<And> x y xs. P (y#xs) \<Longrightarrow> P (x#y#xs)) \<Longrightarrow> P xs" for xs P
  apply(induction rule: list_induct3)
  using not_less_eq_eq by fastforce+

lemma list_induct2_len_geq_1: 
  "\<lbrakk>length xs \<ge> 1; \<And> x. P [x]; \<And> x y xs. P (y#xs) \<Longrightarrow> P (x#y#xs)\<rbrakk> \<Longrightarrow> P xs" 
  by (metis One_nat_def length_greater_0_conv less_eq_Suc_le list.exhaust_sel list_nonempty_induct)

lemma snoc_eq_iff_butlast': "ys = xs @ [x] \<longleftrightarrow> (ys \<noteq> [] \<and> butlast ys = xs \<and> last ys = x)"
  by fastforce

lemma neq_Nil_conv_snoc: "xs \<noteq> [] \<longleftrightarrow> (\<exists>x ys. xs = ys @ [x])"
  by (meson snoc_eq_iff_butlast')

lemma list_cases_both_sides: 
"\<lbrakk>xs = [] \<Longrightarrow> P; \<And> x. xs =[x] \<Longrightarrow> P; \<And> x y ys. xs =[x]@ys@[y] \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P "
  by (metis neq_Nil_conv neq_Nil_conv_snoc single_in_append)

lemma append_butlast_last_cancel: "p \<noteq> [] \<Longrightarrow> butlast p @ last p # p' = p @ p'"
  by simp

lemma induct_list_length2: 
"\<lbrakk>length xs \<ge> 2; \<And> x y. P [x,y]; \<And> xs x y z. P (xs@[x,y]) \<Longrightarrow> P(xs@[x,y,z])\<rbrakk> \<Longrightarrow> P xs"
proof(induction xs rule: rev_induct)
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
  qed simp

lemma list_cases_betw: 
"\<lbrakk>length xs \<ge> 2; \<And> x y. xs = [x,y] \<Longrightarrow> P; \<And> ys x y. xs = [x]@ys@[y] \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto intro: list_cases_both_sides[of xs]) 

lemma get_longest_common_tail:
assumes "length p \<ge> 1" "length q \<ge> 1" "last p = last q"
obtains ys p' q' where "p = p'@ys" "q =q'@ys" 
                        "\<And> ys' p'' q''. \<lbrakk>p=p''@ys'; q = q''@ys'\<rbrakk> \<Longrightarrow> length ys' \<le> length ys"
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
        using less.prems(4) local.Nil p_last q_last by fastforce+
      moreover from this Nil
      have  "\<lbrakk>p=p''@ys'; q= q''@ys'\<rbrakk> \<Longrightarrow> length ys' \<le> length [a]" for ys' p'' q''
        using  local.Nil q_last by(cases ys') (auto simp add: Cons_eq_append_conv)
      ultimately show ?thesis     
        using less.prems(1) by force 
    next
      case (Cons y kist)
      show ?thesis
      proof(cases "last pa = last qb")
        case True
      obtain  p' q' ys  where IH_applied:"pa = p'@ys" "qb =q'@ys" 
                        "\<And> ys' p'' q''. \<lbrakk>pa=p''@ys'; qb = q''@ys'\<rbrakk> \<Longrightarrow> length ys' \<le> length ys"
        using butlasts p_last cons Cons True 
        by (auto intro: less(1)[of "butlast p" qb, simplified butlasts(1)])
      hence "p = p'@ys@[a]" "q=q'@ys@[a]" 
        using IH_applied(2) last_q q_last by(auto simp add: p_last)
      moreover have  "\<lbrakk>p=p''@ys'; q = q''@ys'\<rbrakk> \<Longrightarrow> length ys' \<le> length (ys@[a])" for ys' p'' q''
          using last_q q_last  p_last IH_applied(3)[of p'' "butlast ys'" q''] butlasts(2)
          by(cases ys' rule: rev_cases) (auto simp add: butlast_append)
      ultimately show ?thesis 
        using less.prems(1) by force
    next
      case False
      hence "p = pa@[a]" "q =qb@[a]" 
        using last_q q_last p_last by auto
      moreover have  "\<lbrakk>p=p''@ys'; q = q''@ys'\<rbrakk> \<Longrightarrow> length ys' \<le> length [a]" for ys' p'' q''
          using False butlasts last_q p_last
          by(cases ys' rule: rev_cases, simp)
            (auto simp add: butlast_snoc[of "_ @ _", simplified] 
                            last_append if_split[of _ "_ = Nil"])
      ultimately show ?thesis
        using less.prems(1) by force
    qed
  qed
qed
qed

lemma inter_Big_union_distr_empt_list:
  "(\<And> C. C \<in> B \<Longrightarrow> A \<inter> set C = {}) \<Longrightarrow> (A \<inter> \<Union> { set C| C. C \<in> B}) = {}" for A B by auto

lemma foldl_invar: 
 "\<lbrakk>inv x; \<And> y z. inv y \<Longrightarrow> inv (f y z)\<rbrakk> \<Longrightarrow> inv (foldl f x xs)" for inv
  by(induction xs arbitrary: x) auto

lemma foldr_invar: 
  "\<lbrakk>inv x; \<And> y z. inv y \<Longrightarrow> inv (f z y)\<rbrakk> \<Longrightarrow> inv (foldr f xs x)" for inv
  by(induction xs arbitrary: x) auto

lemma list_in_image_map: "set ys \<subseteq> f ` X \<Longrightarrow> \<exists> xs. map f xs = ys \<and> set xs \<subseteq> X"
proof(induction ys)
  case (Cons y ys)
  then obtain x where "x \<in> X" "f x = y"  by auto
  moreover obtain xs where "map f xs = ys" "set xs \<subseteq> X"
    using Cons by auto
  ultimately show ?case 
    by(auto intro!: exI[of _ "x#xs"])
qed simp

lemma rev_cases3: 
  "\<lbrakk>xs = Nil \<Longrightarrow> P; \<And> x. xs = [x] \<Longrightarrow> P; \<And> ys y x. xs=ys@[y,x] \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" 
  by (metis More_Lists.append_butlast_last_cancel append_Nil neq_Nil_conv_snoc)

fun itrev_aux :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"itrev_aux  [] ys = ys" |
"itrev_aux  (x #xs) ys = itrev_aux  xs (x #ys)"
definition "itrev xs = itrev_aux  xs Nil"

lemma itrev_rev_gen:"itrev_aux xs ys = rev xs @ ys"
  by(induction xs ys arbitrary: rule: itrev_aux.induct) auto

lemma itrev_is_rev[simp]: "itrev = rev"
  by(auto simp add: itrev_rev_gen[of _ Nil, simplified] itrev_def)

end