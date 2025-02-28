theory introduction_to_greedoids
  imports Main Complex_Main
begin                                                                                            

definition "set_system E F = (finite E \<and> (\<forall> X \<in> F. X \<subseteq> E))"

definition accessible where "accessible E F \<longleftrightarrow> set_system E F \<and> ({} \<in> F) \<and> (\<forall>X. (X \<in> F - {{}}) \<longrightarrow>
(\<exists>x \<in> X.  X - {x} \<in> F))"
definition closed_under_union where "closed_under_union F \<longleftrightarrow> (\<forall>X Y. X \<in> F \<and> Y \<in> F \<longrightarrow> X \<union> Y \<in> F)"


definition maximal where "maximal P Z \<longleftrightarrow> (P Z \<and> (\<nexists> X. X \<supset> Z \<and> P X))"



lemma accessible_property:
  assumes "accessible E F"
  assumes "X \<subseteq> E" "X \<in> F"
  shows "\<exists>l. set l = X \<and>  (\<forall>i. i \<le> length l \<longrightarrow> set (take i l) \<in> F) \<and> distinct l"
  using assms
proof -
  have "set_system E F" using assms(1) unfolding accessible_def by simp
  then have "finite E" unfolding set_system_def by simp
  then have "finite X" using finite_subset assms(2) by auto
  obtain k where "card X = k" using \<open>finite X\<close> by simp 
  then show ?thesis using assms(3)
  proof (induct k arbitrary: X rule: less_induct)
    case (less a)
    then have "card X = a" by simp
    have "X \<in> F" by (simp add: less.prems(2))
    then have "X \<subseteq> E" using \<open>set_system E F\<close> unfolding set_system_def by simp
    then have "finite X" using \<open>finite E\<close> finite_subset by auto
    then show ?case
    proof (cases "a = 0")
      case True
      then have "card X = 0" using \<open>card X = a\<close> by simp
      have "\<not>(infinite X)" using \<open>finite X\<close> by simp        
      then have "X = {}" using \<open>card X = 0\<close> by simp
      then obtain l where l_prop: "set l = X" "distinct l" using finite_distinct_list by auto
      then have "l = []" using l_prop \<open>X = {}\<close> by simp
      have "{} \<in> F" using assms(1) unfolding accessible_def by simp
      then have "\<forall>i. i \<le> length [] \<longrightarrow> set (take i l) \<in> F" using l_prop by simp
      then show ?thesis using \<open>l = []\<close> l_prop by simp
    next
      case False
      then have "X \<noteq> {}" using \<open>card X = a\<close> by auto
      then have "X \<in> F - {{}}" using \<open>X \<in> F\<close> by simp
      then obtain x where "x \<in> X" "X - {x} \<in> F" using \<open>X \<in> F\<close> assms(1) unfolding accessible_def by auto
      have "finite {x}" by simp
      then have factone: "finite (X - {x})" using \<open>finite X\<close> by simp
      have "(X - {x}) \<subset>  X" using \<open>x \<in> X\<close> by auto
      then have "card (X - {x}) < card (X)" by (meson \<open>finite X\<close> psubset_card_mono)
      then have "card (X - {x}) < a" using \<open>card X = a\<close> by simp
      then have "\<exists>l. set l = X - {x} \<and> (\<forall>i. i \<le> length l \<longrightarrow> set (take i l) \<in> F) \<and> distinct l" using \<open>X - {x} \<in> F\<close> 
        using less.hyps by blast 
      then obtain l where l_prop: "set l = X - {x} \<and> (\<forall>i. i \<le> length l \<longrightarrow> set (take i l) \<in> F) \<and> distinct l" by auto
      let ?l' = "l @ [x]"
      have conc1: "distinct ?l'" using l_prop by simp
      have l_prop2: "set l = X - {x}" using l_prop by simp
      have "(X - {x}) \<union> {x} = X" using \<open>x \<in> X\<close> by auto
      then have conc2: "(set ?l') = X" using l_prop2 by simp
      have prop2: "(\<forall>i. i < length ?l' \<longrightarrow> set (take i ?l') \<in> F)" using l_prop by simp
      have "set (take (length ?l') ?l') \<in> F" using \<open>set ?l' = X\<close> \<open>X \<in> F\<close> by simp
      then have "(\<forall>i. i \<le> length ?l' \<longrightarrow> set (take i ?l') \<in> F)" using prop2
        using antisym_conv2 by blast
       then show ?thesis using conc1 conc2 by fast
     qed
qed
qed



lemma exists_list_with_first_element:
  assumes "finite X" "x \<in> X"
  shows "\<exists>l. set l = X \<and> (nth l 0) = x \<and> distinct l"
proof -
  from `finite X` `x \<in> X` obtain l where "set l = X" "distinct l"
    by (metis finite_distinct_list)
  then have "x \<in> set l" using assms(2) by simp
  then obtain i where "i < length l" and "nth l i = x"
    by (meson in_set_conv_nth)

  then show ?thesis
  proof -
    let ?l' = "(x # (remove1 x l))"
    have "set ?l' = set l" 
  proof
    show "set ?l' \<subseteq> set l"
    proof
      fix y
      assume "y \<in> set ?l'"
      then show "y \<in> set l"
        using \<open>set l = X\<close> assms(2) by auto
    qed
    show "set l \<subseteq> set ?l'"
    proof
      fix y
      assume "y \<in> set l"
      then show "y \<in> set ?l'"
        by (cases "y = x") (auto)
    qed
  qed
  have 1: "distinct ?l'"
    using \<open>distinct l\<close> by force
  with `set l = X` have "set ?l' = X"
    using \<open>set (x # remove1 x l) = set l\<close> by fastforce
  moreover have "nth ?l' 0 = x" by simp
  ultimately show "\<exists>l. set l = X \<and> nth l 0 = x \<and> distinct l"
    using 1 by blast
qed
qed



lemma exists_maximal: assumes "set_system E F" "X \<in> F" "Y \<in> F" 
  shows "\<exists>Z. maximal (\<lambda> Z. Z \<supseteq> X \<and> Z \<subseteq> X \<union> Y \<and> Z \<in> F) Z"
proof -
  let ?S = "{Z. Z \<supseteq> X \<and> Z \<subseteq> X \<union> Y \<and> Z \<in> F}"
  have "finite E" using assms(1) unfolding set_system_def by simp
  then have "finite F" using assms(1) 
    by (meson Sup_le_iff finite_UnionD rev_finite_subset set_system_def)
  have "?S \<subseteq> F" by auto
  then have "finite ?S" using \<open>finite F\<close> finite_subset by auto
  have "X \<in> F \<and> X \<subseteq> X \<and> X \<subseteq> X \<union> Y" using assms(2) by simp
  then have "X \<in> ?S" by simp
  then have "?S \<noteq> {}" by auto
  have "\<forall>Z. Z \<in> ?S \<longrightarrow> Z \<in> F" by simp
  then have "\<forall>Z. Z \<in> ?S \<longrightarrow> Z \<subseteq> E" using assms(1) unfolding set_system_def by simp
  then have S_prop: "\<forall>Z. Z \<in> ?S \<longrightarrow> finite Z" using \<open>finite E\<close> finite_subset by (metis (mono_tags, lifting))
  let ?P = "{card Z | Z. Z \<supseteq> X \<and> Z \<subseteq> X \<union> Y \<and> Z \<in> F}"
  have "?P \<noteq> {} \<and> finite ?P" using \<open>finite ?S\<close> \<open>?S \<noteq> {}\<close> by simp
  then obtain x where "x = Max ?P" by simp
  then have "x \<in> ?P" using Max_in \<open>?P \<noteq> {} \<and> finite ?P\<close> by auto
  then have "\<exists>Z. Z \<in> F \<and> X \<subseteq> Z \<and> Z \<subseteq> X \<union> Y \<and> card Z = x" by auto
  then obtain Z where "Z \<in> F \<and> X \<subseteq> Z \<and> Z \<subseteq> X \<union> Y \<and> card Z = x" by auto
  have max_prop: "\<forall>z. z \<in> ?P \<longrightarrow> z \<le> x" using \<open>x = Max ?P\<close> \<open>?P \<noteq> {} \<and> finite ?P\<close> by simp
  have " maximal (\<lambda> Z. Z \<supseteq> X \<and> Z \<subseteq> X \<union> Y \<and> Z \<in> F) Z"
  proof (rule ccontr)
    assume "\<not> maximal (\<lambda>Z. X \<subseteq> Z \<and> Z \<subseteq> X \<union> Y \<and> Z \<in> F) Z" 
    then have "\<exists>Z'. Z' \<supset> Z \<and> X \<subseteq> Z' \<and> Z' \<subseteq> X \<union> Y \<and> Z' \<in> F" unfolding maximal_def 
      using \<open>Z \<in> F \<and> X \<subseteq> Z \<and> Z \<subseteq> X \<union> Y \<and> card Z = x\<close> by blast
    then obtain Z' where Z'_prop: "Z' \<supset> Z \<and> X \<subseteq> Z' \<and> Z' \<subseteq> X \<union> Y \<and> Z' \<in> F" by auto
    then have "Z' \<in> ?S" by simp
    then have "card Z' \<in> ?P" by auto
    have "finite Z'" using S_prop \<open>Z' \<in> ?S\<close> by simp 
    have "Z \<subset> Z'" using Z'_prop by simp
    then have "card Z < card Z'" using \<open>finite Z'\<close> psubset_card_mono by auto
    then show "False" using \<open>card Z' \<in> ?P\<close> max_prop 
      by (simp add: \<open>Z \<in> F \<and> X \<subseteq> Z \<and> Z \<subseteq> X \<union> Y \<and> card Z = x\<close> dual_order.strict_iff_not)
  qed
  then show ?thesis by auto
  qed



lemma first_element_set:
  assumes "l \<noteq> []"
  shows "{nth l 0} = set (take 1 l)"
proof -
  from assms obtain a l' where l_def: "l = a # l'"
    by (cases l) auto
  then have "nth l 0 = a" by simp
  moreover have "take 1 l = [a]" using l_def by simp
  ultimately show "{nth l 0} = set (take 1 l)" by simp
qed

lemma set_take_union_nth:
  assumes "i < length l"
  shows "set (take i l) \<union> {nth l i} = set (take (i + 1) l)"
proof -
  have "take (i + 1) l = take i l @ [nth l i]"
    using  take_Suc_conv_app_nth assms by simp
  then have "set (take (i + 1) l) = set (take i l @ [nth l i])"
    by simp
  also have "... = set (take i l) \<union> set [nth l i]"
    by simp
  finally show ?thesis
    by simp
qed



lemma subset_list_el:
  assumes "distinct l" "distinct k" "(nth l 0) = (nth k 0)" "l \<noteq> []" "set k \<subset> set l" "k \<noteq> []"
  shows "\<exists>i. i \<le> length k \<and>  set (take i l) \<subseteq> set k \<and> (nth l i) \<in> (set l) - (set k)"
proof -
  let ?set_diff = "((set l) - (set k))"
  let ?S = "{i. (nth l i) \<in> (set l) - (set k) \<and> i < length l}"
  have "length l > 0" using assms(4) by simp
  have "finite (set k)" by simp
  have "set l \<noteq> {}" using assms(4) by simp
  then have l_k_prop:"((set l) - (set k)) \<noteq> {}" using assms(5) by simp
  then have "\<exists>x. x \<in> ?set_diff" by auto
  then obtain x where "x \<in> ?set_diff" by auto
  have "finite ?set_diff" by simp
  have "\<forall>y. y \<in> ?set_diff \<longrightarrow> y \<in> set l" by simp
  then have "\<forall>y. y \<in> ?set_diff \<longrightarrow> List.member l y" using in_set_member \<open>length l > 0\<close> by fast
  then have "List.member l x" using \<open>x \<in> ?set_diff\<close> by simp
  then obtain i where "(nth l i) = x" "i < length l" 
    by (metis \<open>\<forall>y. y \<in> set l - set k \<longrightarrow> y \<in> set l\<close> \<open>x \<in> set l - set k\<close> in_set_conv_nth)
  then have "(nth l i) \<in> ?set_diff" using \<open>x \<in> ?set_diff\<close> by simp
  then have "i \<in> ?S" using \<open>i < length l\<close> by simp
  then have "?S \<noteq> {} \<and> finite ?S" by auto
  then obtain y where "y = Min ?S" by simp
  then have min_prop: "\<forall>p. p \<in> ?S \<longrightarrow> y \<le> p" by simp
  have 2: "set (take y l) \<subseteq> set k"
  proof (rule ccontr)
    assume "\<not> set (take y l) \<subseteq> set k"
    then have "\<exists>z. z \<in> (set (take y l)) \<and> z \<notin> set k" by auto
    then obtain z where z_prop:"z \<in> (set (take y l)) \<and> z \<notin> set k" by auto
    have "\<forall>X. X \<in> set (take y l) \<longrightarrow> X \<in> set l" 
      by (meson in_set_takeD)
    then have "z \<in> (set l)" using z_prop by auto
    then have "z \<notin> set k" using z_prop by simp
    then have "z \<in> ?set_diff" using \<open>z \<in> set l\<close> by simp
    have z_prop2: "z \<in> (set (take y l))" using z_prop by simp
    have "set (take y l) \<noteq> {}" using z_prop by force
    then have "(take y l) \<noteq> []" by simp
    then have "length (take y l) > 0" by simp
    then have "List.member (take y l) z" using in_set_member z_prop2
      by metis
    then have "\<exists>j. (nth (take y l) j) = z \<and> j < length (take y l)" 
      by (meson in_set_conv_nth z_prop2)
    then obtain j where j_prop: "(nth (take y l) j) = z \<and> j < length (take y l)" by auto
    have "y < length l" using \<open>y = Min ?S\<close> 
      using Min_in \<open>{i. l ! i \<in> set l - set k \<and> i < length l} \<noteq> {} \<and> finite {i. l ! i \<in> set l - set k \<and> i < length l}\<close> by blast
    have "j < length (take y l)" using j_prop by simp
    then have "j < y" by simp
    then have "j < length l" using \<open>y < length l\<close> by simp
    then have "(nth (take y l) j) = (nth l j)" 
      using \<open>j < y\<close> by auto
    then have "(nth l j) \<in> ?set_diff" using \<open>z \<in> ?set_diff\<close> j_prop by simp
    then have "j \<in> ?S" using \<open>j < length l\<close> by simp
    then show "False" using \<open>j < y\<close> min_prop by auto
  qed
  then have card_reln: "card (set (take y l)) \<le> card (set k)" using  \<open>finite (set k)\<close> card_mono by auto
  have k_reln: "card (set k) = length k" using assms(2) distinct_card by auto
  have "y < length l" using \<open>y = Min ?S\<close>  Min_in \<open>{i. l ! i \<in> set l - set k \<and> i < length l} \<noteq> {} \<and> finite {i. l ! i \<in> set l - set k \<and> i < length l}\<close> by blast
  then have "distinct (take y l)" using assms(1) by auto
  then have y_reln: "card (set (take y l)) = length (take y l)" using distinct_card by fast
  then have "length (take y l) = y" using length_take \<open>y < length l\<close> by auto
  then have "card (set (take y l)) = y" using y_reln by simp
  then have 1: "y \<le> length k" using card_reln k_reln by simp
  have "y \<in> ?S" using Min_in \<open>y = Min ?S\<close> \<open>?S \<noteq> {} \<and> finite ?S\<close> by fast
  then have 3: "(nth l y) \<in> ?set_diff" by simp
  then show ?thesis using 1 2 3 by auto
  qed


lemma closed_under_arbitrary_unions:
  assumes "closed_under_union F" "{} \<in> F" "set_system E F"
  shows "(finite A \<Longrightarrow> (A \<subseteq> F \<Longrightarrow> (\<Union>i \<in> A. i) \<in> F))"
proof (induction rule: finite_induct)
  case empty
  then show ?case using assms(2) by simp
next
  case (insert x B)
  then have "(insert x B) \<subseteq> F" by simp
  then have \<open>x \<in> F\<close> by simp
  have "B \<subseteq> F" using \<open>insert x B \<subseteq> F\<close> by simp
  then have "(\<Union>i\<in>B. i) \<in> F" using \<open>B \<subseteq> F \<Longrightarrow> (\<Union>i\<in>B. i) \<in> F\<close> by auto
  have "(\<Union>i \<in> (B \<union> {x}). i) = (\<Union>i \<in> B. i) \<union> x" by auto
  also have "... \<in> F" using \<open>(\<Union>i \<in> B. i) \<in> F\<close> \<open>x \<in> F\<close> assms(1) unfolding closed_under_union_def by simp
  finally have "(\<Union>i \<in> (B \<union> {x}). i) \<in> F" by simp
  then show ?case by simp
qed
  

locale greedoid =
  fixes E :: "'a set"
  fixes F :: "'a set set"
  assumes contains_empty_set: "{} \<in> F"
  assumes third_condition: "(X \<in> F) \<and> (Y \<in> F) \<and> (card X > card Y) \<Longrightarrow> \<exists>x \<in> X - Y.  Y \<union> {x} \<in> F"
  assumes ss_assum: "set_system E F"
       
 definition antimatroid where "antimatroid E F \<longleftrightarrow> accessible E F \<and> closed_under_union F"

context greedoid
begin

lemma greedoid_accessible: assumes "greedoid E F"
  shows "accessible E F" unfolding accessible_def
 proof
   show "set_system E F" using ss_assum assms by auto 
   show "{} \<in> F \<and> (\<forall>X. X \<in> F - {{}} \<longrightarrow> (\<exists>x\<in>X. X - {x} \<in> F))"
   proof
     show "{} \<in> F" using contains_empty_set by simp
     show "\<forall>X. X \<in> F - {{}} \<longrightarrow> (\<exists>x\<in>X. X - {x} \<in> F)"
     proof
       fix X
       show "X \<in> F - {{}} \<longrightarrow> (\<exists>x\<in>X. X - {x} \<in> F)"
       proof
         assume "X \<in> F - {{}}"
         then have "X \<subseteq> E" using ss_assum unfolding set_system_def by simp
         have "X \<noteq> {}" using \<open>X \<in> F - {{}}\<close> by simp
         have "finite E" using ss_assum unfolding set_system_def by simp
         then have "finite X" using \<open>X \<subseteq> E\<close> finite_subset by auto    
         have facttwo: "\<forall>i. i \<ge> 0 \<and> i < card X \<longrightarrow> (\<exists>x \<in> X. (\<exists>Y  Z. Y \<in> F \<and> Z \<in> F \<and> Y \<subseteq> X \<and> Z \<subset> Y \<and> card Y = i + 1 \<and> card Z = i \<and> (Y - Z) = {x} ))"
         proof 
           fix i
           show "i \<ge> 0 \<and> i < card X \<longrightarrow> (\<exists>x \<in> X. (\<exists>Y  Z. Y \<in> F \<and> Z \<in> F \<and> Y \<subseteq> X \<and> Z \<subset> Y \<and> card Y = i + 1 \<and> card Z = i \<and> (Y - Z) ={x} ))"
           proof
             assume assum2: "0 \<le> i \<and> i < card X"
             then show "(\<exists>x \<in> X. (\<exists>Y  Z. Y \<in> F \<and> Z \<in> F \<and> Y \<subseteq> X \<and> Z \<subset> Y \<and> card Y = i + 1 \<and> card Z = i \<and> (Y - Z) = {x} ))" using \<open>X \<in> F - {{}}\<close>
                 \<open>finite X\<close>
             proof (induct i arbitrary: X rule: less_induct)
               case (less i)
               then show ?case
               proof (cases "i = 0")
                 case True
                 have 1: "card {} = 0" by simp
                 have "X \<noteq> {}" using \<open>X \<in> F - {{}}\<close> by simp
                 then have "card X > card {}" using \<open>finite X\<close> by auto
                 then have "\<exists>x. x \<in> X - {} \<and> {} \<union> {x} \<in> F" using contains_empty_set \<open>X \<in> F - {{}}\<close> third_condition by blast
                 then obtain x where x_prop: "x \<in> X - {} \<and> {} \<union> {x} \<in> F" by auto
                 then have 2: "{x} \<in> F" by simp
                 have 3: "{x} \<subseteq> X" using x_prop by simp
                 have 4: "{} \<subset> {x}" by auto
                 have 5: "card {x} = 0 + 1" by simp
                 have "card ({x} - {}) = 1" by simp
                 then show ?thesis using 1 2 3 4 5 contains_empty_set x_prop True by blast
               next 
                 case False
                 then have "i > 0 \<and> i < card X" using \<open>i \<ge> 0 \<and> i < card X\<close> by simp
                 then have factone: "i - 1 < i" by simp
                 then have "i - 1 \<ge> 0 \<and> (i - 1) < card X" using \<open>i > 0 \<and> i < card X\<close> by auto
                 then have "(\<exists>x \<in> X. (\<exists>Y  Z. Y \<in> F \<and> Z \<in> F \<and> Y \<subseteq> X \<and> Z \<subset> Y \<and> card Y = (i - 1) + 1  \<and> card Z = i - 1 \<and> (Y - Z) = {x} ))"
                   using \<open>finite X\<close> \<open>X \<in> F - {{}}\<close> less.hyps factone by blast
                 then have "(\<exists>x \<in> X. (\<exists>Y  Z. Y \<in> F \<and> Z \<in> F \<and> Y \<subseteq> X \<and> Z \<subset> Y \<and> card Y = i \<and> card Z = i - 1 \<and> (Y - Z) = {x} ))"
                   using factone by simp
                 then obtain x Y Z where x_Y_Z_prop: "x \<in> X \<and> Y \<in> F \<and> Z \<in> F \<and> Y \<subseteq> X \<and> Z \<subset> Y \<and> card Y = i \<and> card Z = i - 1 \<and> (Y - Z) = {x}" by auto
                 then have "card Y < card X" using \<open>i > 0 \<and> i < card X\<close> by simp
                 have 2: "card Y = i" using x_Y_Z_prop by simp
                 have "Y \<in> F" using x_Y_Z_prop by simp
                 then have "\<exists>x. x \<in> X - Y \<and> Y \<union> {x} \<in> F" using third_condition \<open>X \<in> F - {{}}\<close> \<open>card Y < card X\<close> by auto
                 then obtain y where y_prop: "y \<in> X - Y \<and> Y \<union> {y} \<in> F" by auto
                 then have "y \<notin> Y" by simp
                 then have "card (Y \<union> {y}) = card Y + card {y}" using \<open>card Y = i\<close> 
                   by (metis Nat.add_0_right \<open>0 < i \<and> i < card X\<close> add_Suc_right card_1_singleton_iff card_gt_0_iff card_insert_disjoint insert_is_Un sup_commute)
                 then have 1: "card (Y \<union> {y}) = i + 1" using \<open>card Y = i\<close> by simp
                 have 3: "Y \<union> {y} \<subseteq> X" using y_prop x_Y_Z_prop by simp
                 have 4: "Y \<subset> Y \<union> {y}" using \<open>y \<notin> Y\<close> by auto
                 then have "((Y \<union> {y}) - Y) = {y}" by auto
                 then show ?thesis using 1 2 3 4 y_prop x_Y_Z_prop \<open>X \<in> F - {{}}\<close> \<open>finite X\<close>
                   by (metis Diff_iff)
               qed
             qed
           qed
         qed
         have "card X \<noteq> 0" using \<open>X \<noteq> {}\<close> \<open>finite X\<close> by simp
         then have "card X - 1 < card X" by simp
         have "card X - 1 \<ge> 0" by simp
         then have "(\<exists>x \<in> X. (\<exists>Y  Z. Y \<in> F \<and> Z \<in> F \<and> Y \<subseteq> X \<and> Z \<subset> Y \<and> card Y = (card X - 1) + 1 \<and> card Z = card X - 1 \<and> (Y - Z) = {x} ))"
           using \<open>card X - 1 < card X\<close> facttwo by blast
         then obtain x Y Z where x_Y_Z_prop: "x \<in> X \<and> Y \<in> F \<and> Z \<in> F \<and> Y \<subseteq> X \<and> Z \<subset> Y \<and> card Y = (card X - 1) + 1 \<and> card Z = card X - 1 \<and> (Y - Z) = {x}"
           by auto
         then have "card Y = card X" using \<open>card X - 1 < card X\<close> by simp
         have "Y \<subseteq> X" using x_Y_Z_prop by simp
         then have "Y = X" using x_Y_Z_prop \<open>finite X\<close> \<open>card Y = card X\<close> 
           using card_subset_eq by blast
         have "Y - {x} = Z" using x_Y_Z_prop by auto
         then have "X - {x} = Z" using \<open>Y = X\<close> by simp
         also have "... \<in> F" using x_Y_Z_prop by simp
         finally have "X - {x} \<in> F" by simp
         then show "\<exists>x\<in>X. X - {x} \<in> F" using x_Y_Z_prop by auto
       qed
     qed
   qed
 qed
 
end

  lemma antimatroid_greedoid: 
   assumes assum1: "antimatroid E F"
   shows "greedoid E F"

 proof (unfold_locales)

   have 1: "accessible E F \<and> closed_under_union F"
  proof -
    show "accessible E F \<and> closed_under_union F" 
      by (meson antimatroid_def assum1)
  qed

  show 2: "set_system E F"
  proof- 
    have "accessible E F" using 1 by simp
    then show "set_system E F" unfolding accessible_def by simp
  qed

  show 3: "{} \<in> F" using 1 accessible_def by force

  show 4: "\<And>X Y. X \<in> F \<and> Y \<in> F \<and> card Y < card X \<Longrightarrow> (\<exists>x \<in> X - Y.  Y \<union> {x} \<in> F)"
  proof -
    fix X
    show "\<And>Y. X \<in> F \<and> Y \<in> F \<and> card Y < card X \<Longrightarrow> (\<exists>x \<in> X - Y.  Y \<union> {x} \<in> F)"
    proof -
      fix Y
      assume assum5: "X \<in> F \<and> Y \<in> F \<and> card Y < card X"
      show "(\<exists>x \<in> X - Y.  Y \<union> {x} \<in> F)"
      proof -
        have "accessible E F" using 1 by auto
        have "closed_under_union F" using 1 by auto
      have "finite E" using 2 unfolding set_system_def by auto
      have "X \<in> F" "Y \<in> F" using assum5 by auto
      have "X \<subseteq> E" using \<open>X \<in> F\<close> 2 unfolding set_system_def by blast
      have "Y \<subseteq> E" using \<open>Y \<in> F\<close> \<open>set_system E F\<close> unfolding set_system_def by auto
      then have "finite Y" using \<open>finite E\<close> finite_subset by auto
      have "finite X" using \<open>finite E\<close> \<open>X \<subseteq> E\<close> finite_subset by auto
      have "X \<noteq> {}" using assum5 by auto 
      then have "\<exists> l. set l = X \<and> (\<forall>i. i \<le> length l \<longrightarrow> set (take i l) \<in> F) \<and> distinct l"  using \<open>X \<in> F\<close> \<open>accessible E F\<close> accessible_property \<open>X \<subseteq> E\<close> by auto
      then obtain l where l_prop: "set l = X \<and> (\<forall>i. i \<le> length l \<longrightarrow> set (take i l) \<in> F) \<and> distinct l" by auto
      show "\<exists>x\<in>X - Y. Y \<union> {x} \<in> F"
      proof (cases "X \<inter> Y = {}")
        case True
        have "set l = X" using l_prop by auto
        then have "nth l 0 \<in> X" 
          by (metis Int_lower1 True \<open>finite X\<close> assum5 card.empty card_length card_seteq gr_zeroI less_nat_zero_code nth_mem)
        then have "nth l 0 \<notin> Y" using True by blast
        then have "nth l 0 \<in> X - Y" using \<open>nth l 0 \<in> X\<close> by simp
        have "l \<noteq> []" using \<open>X \<noteq> {}\<close> \<open>set l = X\<close> by auto
        then have "length l > 0" by simp
        then have "length l \<ge> 1" using linorder_le_less_linear by auto
        then have "set (take 1 l) \<in> F" using l_prop \<open>set l = X\<close> by simp
        have "{nth l 0} = set (take 1 l)" using  first_element_set \<open>l \<noteq> []\<close> by simp
        have "Y \<union> set (take 1 l) \<in> F" using \<open>set (take 1 l) \<in> F\<close> \<open>Y \<in> F\<close> \<open>closed_under_union F\<close>
          unfolding closed_under_union_def by blast
        then have  "nth l 0 \<in> X - Y \<and> Y \<union> {nth l 0} \<in> F" using \<open>nth l 0 \<in> X - Y\<close> \<open>{nth l 0} = set (take 1 l)\<close> by auto
        then show ?thesis by auto
      next
        case False
        have "set l = X" using l_prop by simp
        have "X = (X \<inter> Y) \<union> (X - Y)" by auto
        then have X_element_prop: "\<forall>x. x \<in> X \<longrightarrow> x \<in> (X - Y) \<or> x \<in> (X \<inter> Y)" by simp
        show ?thesis
        proof (cases "(nth l 0) \<in> X - Y ")
          case True
          have "set l = X" using l_prop by auto
        then have "nth l 0 \<in> X - Y" using True  by simp
        have "l \<noteq> []" using \<open>X \<noteq> {}\<close> \<open>set l = X\<close> by auto
        then have "length l > 0" by simp
        then have "length l \<ge> 1" using linorder_le_less_linear by auto
        then have "set (take 1 l) \<in> F" using l_prop \<open>set l = X\<close> by simp
        have "{nth l 0} = set (take 1 l)" using  first_element_set \<open>l \<noteq> []\<close> by simp
        have "Y \<union> set (take 1 l) \<in> F" using \<open>set (take 1 l) \<in> F\<close> \<open>Y \<in> F\<close> \<open>closed_under_union F\<close>
          unfolding closed_under_union_def by blast
        then have  "nth l 0 \<in> X - Y \<and> Y \<union> {nth l 0} \<in> F" using \<open>nth l 0 \<in> X - Y\<close> \<open>{nth l 0} = set (take 1 l)\<close> by auto
        then show ?thesis by auto
        next
          case False
          have "l \<noteq> []" using \<open>X \<noteq> {}\<close> \<open>set l = X\<close> by auto
          have "List.member l (nth l 0)" using \<open>set l = X\<close>
            by (metis \<open>X \<noteq> {}\<close> in_set_member length_pos_if_in_set nth_mem subsetI subset_empty)
          then have "nth l 0 \<in> X" using \<open>set l = X\<close> in_set_member by fast
          then have "(nth l 0) \<in> X \<inter> Y" using X_element_prop False by simp
          have "finite (X \<inter> Y)" using \<open>finite X\<close> \<open>finite Y\<close> by simp
          then have "\<exists>k. set k = X \<inter> Y \<and> (nth k 0) = (nth l 0) \<and> distinct k" using exists_list_with_first_element \<open>(nth l 0) \<in> X \<inter> Y\<close> by fast
          then obtain k where k_prop: "set k = X \<inter> Y" "nth l 0 = nth k 0" "distinct k" by auto
          then have "k \<noteq> []" using \<open>X \<inter> Y \<noteq> {}\<close> by auto
          have fact_one: "{nth l 0} = {nth k 0}" using k_prop by simp
          have fact_two: "set (take 1 l) = {nth l 0}" using first_element_set \<open>l \<noteq> []\<close> by auto
          have "set (take 1 k) = {nth k 0}" using first_element_set \<open>k \<noteq> []\<close> by auto
          then have "set (take 1 l) = set (take 1 k)" using fact_one fact_two by simp
          have "distinct l" using l_prop by simp
          have "distinct k" using k_prop(3) by simp
          have "X \<inter> Y \<subset> X" using \<open>X \<inter> Y \<noteq> {}\<close>
            by (metis \<open>finite Y\<close> assum5 inf.cobounded1 inf.cobounded2 order.asym psubsetI psubset_card_mono)
          then have "(set k) \<subset> (set l)" using l_prop k_prop(1) by simp
          then have assum6: "\<exists>i. i \<le> length k \<and> set (take i l) \<subseteq> set k \<and> (nth l i) \<in> (set l) - (set k)" using subset_list_el 
              \<open>distinct l\<close> \<open>distinct k\<close> \<open>(nth l 0) = (nth k 0)\<close> \<open>l \<noteq> []\<close> \<open>set k \<subset> set l\<close> \<open>k \<noteq> []\<close> by metis
          then obtain i where i_prop: " i \<le> length k \<and> set (take i l) \<subseteq> set k \<and> (nth l i) \<in> (set l) - (set k)" by auto
          have "X - (X \<inter> Y) = X - Y" by auto
          then have "(set l) - (set k) = X - Y" using l_prop k_prop(1) by simp
          then have 1: "(nth l i) \<in> X - Y" using i_prop by simp
          then have "(nth l i) \<notin> Y" by simp
          have "card (set k) < card (set l)" using \<open>(set k) \<subset> (set l)\<close> by (simp add: \<open>finite X\<close> psubset_card_mono)
          then have "length k < length l" using l_prop k_prop(3)
                  by (metis distinct_card)
          then have "i < length l" using i_prop by simp
          then have "set (take i l) \<union> {nth l i} = set (take (i + 1) l)" using set_take_union_nth by simp
          have "set (take (i + 1) l) \<in> F" using l_prop \<open>i < length l\<close> by auto
          have "set (take i l) \<subseteq> set k"
            using i_prop by simp
          then have "set (take i l) \<subseteq> X \<inter> Y" using k_prop by simp
          then have "set (take i l) \<subseteq> Y" by simp
          then have "Y \<union> {nth l i} = Y \<union> set (take i l) \<union> {nth l i}" using \<open>(nth l i) \<notin> Y\<close> by auto
          also have "... = Y \<union> set (take (i + 1) l)" using \<open>set (take i l) \<union> {nth l i} = set (take (i + 1) l)\<close> by auto
          also have "... \<in> F" using \<open>closed_under_union F\<close> \<open>Y \<in> F\<close> \<open>set (take (i + 1) l) \<in> F\<close> unfolding closed_under_union_def by simp
          finally have 2: "Y \<union> {nth l i} \<in> F" by simp
          then show ?thesis using 1 2 by auto
        qed
  qed
qed
qed
qed
qed



locale greedoid_example  =
  fixes V :: "'a set"         (* Set of vertices *)
    and E :: "('a set) set"  (* Set of directed edges *) 
  assumes finite_assum_V: "finite V"

context greedoid_example
begin

definition undirected_graph::"'a set \<Rightarrow> ('a set) set \<Rightarrow> bool" where "undirected_graph F G \<longleftrightarrow> F \<subseteq> V \<and> (\<forall>e \<in> G. card e = 2 \<and> e \<subseteq> F)"

definition acyclic::"'a set \<Rightarrow> ('a set) set \<Rightarrow> bool" where "acyclic F G = ((G = {}) \<or> (\<forall>v \<in> F. \<not> (\<exists>p. p \<noteq> [] \<and> hd p = v \<and> last p = v \<and> (\<forall>i < length p - 1. {p ! i, p ! (i + 1)} \<in> G) \<and> length p \<ge> 4 \<and> distinct (butlast p))))"

definition connected::"'a set \<Rightarrow>  ('a set) set \<Rightarrow> bool" where " connected F G = ((G = {} \<and> card F = 1) \<or> (\<forall>u v. u \<in> F \<and> v \<in> F \<and> u \<noteq> v \<longrightarrow> (\<exists>p. p \<noteq> [] \<and> (hd p = v \<and> last p = u) \<and> (\<forall>i < length p - 1. {p ! i, p ! (i + 1)} \<in> G) \<and> length p \<ge> 2)))"

definition tree::"'a set \<Rightarrow> ('a set) set \<Rightarrow> bool" where "tree F G \<longleftrightarrow> undirected_graph F G \<and> acyclic F G \<and> connected F G \<and> (card G = card F - 1) "


lemma greedoid_graph_example: assumes "undirected_graph V E" "r \<in> V" 
  shows "greedoid E {Y. \<exists> X. X \<subseteq> V \<and> Y \<subseteq> E \<and> r \<in> X \<and> tree X Y}"
proof (unfold_locales)
  let ?F = "{Y. \<exists> X. X \<subseteq> V \<and> Y \<subseteq> E \<and> r \<in> X \<and> tree X Y}"
  show first_part: "{} \<in> {Y. \<exists> X. X \<subseteq> V \<and> Y \<subseteq> E \<and> r \<in> X \<and> tree X Y}"
  proof -
    have factone: "{r} \<subseteq> V" using assms(2) by simp
    have "tree {r} {}" unfolding tree_def
    proof 
      show "undirected_graph {r} {}" unfolding undirected_graph_def using assms by auto
      have 1: "acyclic {r} {}" unfolding acyclic_def by simp
        have 2: "connected {r} {}" unfolding connected_def by simp
        have 3: "card {} = card {} - 1" by simp
        then show "local.acyclic {r} {} \<and> local.connected {r} {} \<and> card {} = card {r} - 1" using 1 2 by simp
      qed
      then have "{r} \<subseteq> V \<and> {} \<subseteq> E \<and> r \<in> {r} \<and> tree {r} {}" using factone by simp
      then show ?thesis by blast
    qed

    show "set_system E ?F" unfolding set_system_def
    proof 
      show "finite E" 
      proof -
        have "\<forall>e \<in> E. e \<subseteq> V" using assms(1) unfolding undirected_graph_def by simp
        then show "finite E" using finite_assum_V 
          by (meson Sup_le_iff finite_UnionD rev_finite_subset)
      qed
      show "\<forall>Z\<in>?F. Z \<subseteq> E" by auto
    qed

    show "\<And>X Y. X \<in> ?F \<and>
           Y \<in> ?F \<and> card Y < card X \<Longrightarrow>
           \<exists>x\<in>X - Y. Y \<union> {x} \<in> ?F"
    proof -
      fix X Y
      assume assum2: "X \<in> ?F \<and>
           Y \<in> ?F \<and> card Y < card X"
      then obtain V1 where V1_prop: "V1 \<subseteq> V \<and>  X \<subseteq> E \<and> r \<in> V1 \<and> tree V1 X" by auto
      then have "tree V1 X" by simp
      then have V1_card: "card V1 - 1 = card X" unfolding tree_def by auto
      have "V1 \<noteq> {}" using V1_prop by auto
      have "finite V1" using V1_prop finite_assum_V finite_subset by auto
      then have "card V1 > 0" using \<open>V1 \<noteq> {}\<close> by auto
      then have factone: "card V1 = card X + 1" using V1_card by auto 
      obtain V2 where V2_prop: "V2 \<subseteq> V \<and>  Y \<subseteq> E \<and> r \<in> V2 \<and> tree V2 Y" using assum2 by auto
      then have "tree V2 Y" by simp
      then have V2_card: "card V2 - 1 = card Y" unfolding tree_def by auto  
      have "V2 \<noteq> {}" using V2_prop by auto
      have "finite V2" using V2_prop finite_assum_V finite_subset by auto
      then have "card V2 > 0" using \<open>V2 \<noteq> {}\<close> by auto
      then have facttwo: "card V2 = (card Y) + 1" using V2_card by auto
      have "card Y < card X" using assum2 by simp
      then have "card Y + 1 < card X + 1" by simp
      then have "card V2 < card V1" using factone facttwo by simp
      have "X = (X - Y) \<union> (X \<inter> Y)" by auto
      show "\<exists>x\<in>X - Y. Y \<union> {x} \<in> ?F"
      proof -
        have "V1 \<noteq> {}" using V1_prop by auto
          then have "V1 \<noteq> V2" using \<open>card V2 < card V1\<close> by auto
          then have "V1 - V2 \<noteq> {}" 
            by (metis \<open>card V2 < card V1\<close> \<open>finite V1\<close> \<open>finite V2\<close> bot.extremum_strict bot_nat_def card.empty card_less_sym_Diff)
          then obtain x where "x \<in> V1 - V2" by auto
          then have "x \<notin> V2" by simp
          have "x \<in> V1" using \<open>x \<in> V1 - V2\<close> by simp
          have "r \<in> V2" using V2_prop by simp
          then have "x \<noteq> r" using \<open>x \<notin> V2\<close> by auto
          have "X \<noteq> {}" 
            using \<open>card Y < card X\<close> card.empty by auto
          have "r \<in> V1" using V1_prop by simp
          have "tree V1 X" using V1_prop by simp
          then have "connected V1 X" unfolding tree_def by simp
          then have "(X = {} \<and> card V1 = 1) \<or> (\<forall>u v. u \<in> V1 \<and> v \<in> V1 \<and> u \<noteq> v \<longrightarrow> (\<exists>p. p \<noteq> [] \<and> (hd p = u \<and> last p = v ) \<and> (\<forall>i < length p - 1. ({p ! i, p ! (i + 1)} \<in> X)) \<and> length p \<ge> 2))" unfolding
              connected_def by auto
          then have "(\<forall>u v. u \<in> V1 \<and> v \<in> V1 \<and> u \<noteq> v \<longrightarrow> (\<exists>p. p \<noteq> [] \<and> (hd p = u \<and> last p = v) \<and> (\<forall>i < length p - 1. ({p ! i, p ! (i + 1)} \<in> X)) \<and> length p \<ge> 2))" using \<open>X \<noteq> {}\<close> by simp
          then have "(\<exists>p. p \<noteq> [] \<and> (hd p = r \<and> last p = x) \<and> (\<forall>i < length p - 1. ({p ! i, p ! (i + 1)} \<in> X)) \<and> length p \<ge> 2)" using \<open>r \<in> V1\<close> \<open>x \<in> V1\<close> \<open>x \<noteq> r\<close> \<open>X \<noteq> {}\<close> by simp
          then obtain p where p_prop: "(p \<noteq> [] \<and> (hd p = r \<and> last p = x) \<and> (\<forall>i < length p - 1. ({p ! i, p ! (i + 1)} \<in> X)) \<and> length p \<ge> 2)" by auto
          have "\<exists>v' w. v' \<in> V1 \<inter> V2 \<and> w \<in> V1 - V2 \<and> {v', w} \<in> X" 
          proof -
           have "last p = x" using p_prop by auto
          have "hd p = r" using p_prop by simp
          have "length p \<ge> 2" using p_prop by simp
          have p_prop2: "(\<forall>i < length p - 1. ({p ! i, p ! (i + 1)} \<in> X))" using p_prop by simp
          have "undirected_graph V1 X" using \<open>tree V1 X\<close> unfolding tree_def by simp
          then have X_prop1: "V1 \<subseteq> V \<and> (\<forall>e \<in> X. e \<subseteq> V1 \<and> card e = 2)" unfolding undirected_graph_def by simp
          have p_prop3: "\<forall>i \<le> length p - 1. (nth p i) \<in> V1" 
          proof (rule allI)
            fix i
            show "i \<le> length p - 1 \<longrightarrow> p ! i \<in> V1"
            proof (cases "i = length p - 1")
              case True
              then have "i \<noteq> 0" using \<open>length p \<ge> 2\<close> by simp
              then have "i - 1 = length p - 1 - 1" using True by simp
              then have "i = (i - 1) + 1" using \<open>i \<noteq> 0\<close> by simp
              then have "i - 1 < length p - 1" using \<open>length p \<ge> 2\<close> \<open>i - 1 = length p - 1 - 1\<close> by simp
              then have "{nth p (i - 1), (nth p i)} \<in> X" using p_prop \<open>i = (i - 1) + 1\<close> by auto
              then have "{nth p (i - 1), (nth p i)} \<subseteq> V1" using X_prop1 by auto
              then show ?thesis using True by auto
            next
              case False
              show "i \<le> length p - 1 \<longrightarrow> (nth p i) \<in> V1"
              proof
                assume "i \<le> length p - 1"
                then have "i < length p - 1" using \<open>length p \<ge> 2\<close> False by simp
                then have "{nth p i, (nth p (i + 1))} \<in> X " using p_prop by simp
                then have "{nth p i, (nth p (i + 1))} \<subseteq> V1" using X_prop1 by auto
                then show "(nth p i) \<in> V1" by simp
            qed
          qed
        qed
          have "V1 = (V1 \<inter> V2) \<union> (V1 - V2)" by auto
          then have V1_el_prop: "\<forall>v. v \<in> V1 \<longrightarrow> v \<in> (V1 - V2) \<or> v \<in> (V1 \<inter> V2)" by auto
          have "\<exists>i. i \<le> (length p) - 1 \<and> (nth p (i )) \<in> V1 - V2 \<and> (nth p (i - 1)) \<in> V1 \<inter> V2"
          proof (cases "\<forall>i < (length p) - 1. (nth p i) \<in> V1 \<inter> V2")
            case True
            have "((length p) - 1) - 1 < (length p) - 1" using \<open>length p \<ge> 2\<close> by simp 
            then have prop1: "(nth p ((length p) - 1 - 1)) \<in> V1 \<inter> V2" using True by simp
            have "(nth p (length p - 1)) = x" using \<open>last p = x\<close> 
              by (metis last_conv_nth p_prop)
            then have "(nth p (length p - 1)) \<in> V1 - V2" using \<open>x \<in> V1 - V2\<close> by simp
            then show ?thesis using prop1  \<open>length p - 1 - 1 < length p - 1\<close>  by auto
          next
            case False
            then have "\<exists>i < (length p) - 1. (nth p i) \<notin> V1 \<inter> V2" by auto
            then obtain i where i_prop: "i < (length p) - 1 \<and> (nth p i) \<notin> V1 \<inter> V2" by auto
            then have i_prop2: "(nth p i) \<notin> V1 \<inter> V2" by simp
            then have "i < length p - 1" using i_prop by simp
            then have "(nth p i) \<in> V1 - V2" using V1_el_prop i_prop2 p_prop3 by simp
            let ?A = "{j. j < length p - 1 \<and> (nth p j) \<in> V1 - V2}" 
            have "finite ?A" by simp
            have "i \<in> ?A" using \<open>i < length p - 1\<close> \<open>(nth p i) \<in> V1 - V2\<close> by simp
            then have "?A \<noteq> {}" by auto
            then have "Min ?A \<in> ?A" using \<open>finite ?A\<close> Min_in by blast
            let ?k = "Min ?A"
            have min_prop: "\<forall>j. j\<in> ?A \<longrightarrow> ?k \<le> j" by simp
            have k_prop: "?k < length p - 1 \<and> (nth p ?k) \<in> V1 - V2" using \<open>?k \<in> ?A\<close> by simp
            have "(nth p 0) = r" using p_prop hd_conv_nth by metis
            then have "(nth p 0) \<in> V1 \<inter> V2" using V1_prop V2_prop by simp
            have "(nth p ?k) \<in> V1 - V2" using k_prop by simp
            then have "?k \<noteq> 0" using \<open>(nth p 0) \<in> V1 \<inter> V2\<close> 
              by (metis DiffD2 \<open>p ! 0 = r\<close> \<open>r \<in> V2\<close>)
            then have "?k - 1 < ?k" by simp
            have "?k - 1 < length p - 1" using k_prop by auto
            have k_prop4: "(nth p (?k - 1)) \<in> V1 \<inter> V2"
            proof (rule ccontr)
              assume "(nth p (?k - 1)) \<notin> V1 \<inter> V2"
              then have "(nth p (?k - 1)) \<in> V1 - V2" using p_prop3 V1_el_prop i_prop2 \<open>?k - 1 < length p -1 \<close> by simp
              then have "?k - 1 < length p - 1" using \<open>?k - 1 < ?k\<close> k_prop by simp
              then have "?k - 1 \<in> ?A" using \<open>(nth p (?k - 1)) \<in> V1 - V2\<close> by simp
              then show "False" using min_prop \<open>?k - 1 < ?k\<close> 
                using less_le_not_le by blast
            qed
            then have k_prop3: "?k \<le> length p - 1 \<and> (nth p ?k) \<in> V1 - V2" using k_prop by simp
            then show ?thesis using k_prop4 by auto
          qed
          then obtain i where i_prop: "i \<le> (length p) - 1 \<and> (nth p i) \<in> V1 - V2 \<and> (nth p (i - 1)) \<in> V1 \<inter> V2" by auto
          then have "i - 1 < length p - 1" using p_prop by auto
          have "nth p 0 = r" using hd_conv_nth p_prop by metis
          then have "nth p 0 \<in> V1 \<inter> V2" using V1_prop V2_prop by simp
          have "i \<noteq> 0" 
          proof
            assume "i = 0"
            then have "nth p 0 \<in> V1 - V2" using i_prop by simp
            then show "False" using \<open>nth p 0 \<in> V1 \<inter> V2\<close> by simp
          qed
          then have "i - 1 + 1 = i" by simp
          then have factone: "{nth p (i - 1), nth p i} \<in> X" using p_prop \<open>i - 1 < length p - 1\<close> by auto
          have "i - 1 < length p" using \<open>i - 1 < length p - 1\<close> by simp 
          then show ?thesis using i_prop factone by auto
        qed
          then obtain v' w where v'_w_prop: "v' \<in> V1 \<inter> V2 \<and> w \<in> V1 - V2 \<and> ({v', w} \<in> X)" by auto
          let ?v = "v'"
          let ?w = "w"
          have "?v \<in> V1 \<inter> V2" using v'_w_prop by simp
          have "?w \<in> V1 - V2" using v'_w_prop by simp
          show "\<exists>x\<in>X - Y. Y \<union> {x} \<in> {Y. \<exists>X\<subseteq>V. Y \<subseteq> E \<and> r \<in> X \<and> tree X Y}"
          proof -
            have "{?v, ?w} \<in> X" using v'_w_prop by simp
          have "tree V2 Y" using V2_prop by simp
          then have "undirected_graph V2 Y" unfolding tree_def by simp
          then have Y_prop: "V2 \<subseteq> V \<and> (\<forall>e \<in> Y. e \<subseteq> V2 \<and> card e = 2)" unfolding undirected_graph_def by simp
          have "\<not> {?v, ?w} \<subseteq> V2" using \<open>?w \<in> V1 - V2\<close> by simp
          then have "{?v, ?w} \<notin> Y" using Y_prop by auto
          then have "{?v, ?w} \<in> X - Y" using \<open>{?v, ?w} \<in> X\<close> by simp
          have "connected V2 Y" using \<open>tree V2 Y\<close> unfolding tree_def by simp
          then have Y_connected: "(Y = {} \<and> card V2 = 1) \<or>(\<forall>u v. u \<in> V2 \<and> v \<in> V2 \<and> u \<noteq> v \<longrightarrow>
           (\<exists>p. p \<noteq> [] \<and>
                (hd p = v \<and> last p = u) \<and>
                (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y) \<and>
           2 \<le> length p))" 
            unfolding connected_def by simp
          have "undirected_graph V1 X" using \<open>tree V1 X\<close> unfolding tree_def by simp
          then have X_prop1: "V1 \<subseteq> V \<and> (\<forall>e \<in> X. e \<subseteq> V1 \<and> card e = 2)" unfolding undirected_graph_def by simp
          have "acyclic V2 Y" using \<open>tree V2 Y\<close> unfolding tree_def by auto
          then have Y_acyclic: "(Y = {}) \<or> (\<forall>v. v \<in> V2 \<longrightarrow> \<not>(\<exists>p. p \<noteq> [] \<and> hd p = v \<and> last p = v \<and> (\<forall>i < length p - 1. {nth p i, nth p (i + 1)} \<in> Y) \<and> length p \<ge> 4 \<and> distinct (butlast p)))"  unfolding acyclic_def by auto
          have w_el_prop: "(\<nexists>x. x \<in> V2 \<union> {?w} \<and> {x, ?w} \<in> Y \<union> {{?v, ?w}} \<and> x \<noteq> ?v)"
          proof 
            assume "\<exists>x. x \<in> V2 \<union> {w} \<and> {x, w} \<in> Y \<union> {{v', w}} \<and> x \<noteq> v'"
            then obtain y where y_prop: "y \<in> V2 \<union> {w} \<and> {y, w} \<in> Y \<union> {{v', w}} \<and> y \<noteq> v'" by auto
            then have "{y, ?w} \<in> Y \<union> {{?v, ?w}}" by simp
            then have "{y, ?w} \<in> Y" using y_prop by fast
            then have "{y, ?w} \<subseteq> V2" using Y_prop by auto
            then have "?w \<in> V2" by simp
            then show False using \<open>?w \<in> V1 - V2\<close> by simp
          qed
          
          have "undirected_graph (V2 \<union> {?w}) (Y \<union> {{?v, ?w}})"  unfolding undirected_graph_def
          proof
            show "V2 \<union> {?w} \<subseteq> V" using Y_prop \<open>?w \<in> V1 - V2\<close> X_prop1 by auto
            show "\<forall>e\<in>Y \<union> {{?v, ?w}}. card e = 2 \<and> e \<subseteq> V2 \<union> {?w}"
            proof 
              fix e
              show "e \<in> Y \<union> {{?v, ?w}} \<Longrightarrow> card e = 2 \<and> e \<subseteq> V2 \<union> {?w}"
              proof -
                assume "e \<in> Y \<union> {{?v, ?w}}"
                then show "card e = 2 \<and> e \<subseteq> V2 \<union> {?w}"
                proof (cases "e = {?v, ?w}")
                  case True
                  then have "{?v, ?w} \<subseteq> V2 \<union> {?w}" using \<open>?v \<in> V1 \<inter> V2\<close> by auto
                  then show ?thesis using True 
                    by (simp add: X_prop1 \<open>{v', w} \<in> X\<close>)
                next
                  case False
                  then have "e \<in> Y" using \<open>{?v, ?w} \<notin> Y\<close> \<open>e \<in> Y \<union> {{?v, ?w}}\<close> by simp
                  then show ?thesis using Y_prop by auto
                qed
              qed
            qed
          qed
          have "acyclic (V2 \<union> {?w}) (Y \<union> {{?v, ?w}})" unfolding acyclic_def
          proof -
            have "Y \<union> {{?v, ?w}} \<noteq> {}" by simp
            have "(\<forall>v\<in>V2 \<union> {w}.
        \<nexists>p. p \<noteq> [] \<and>
            hd p = v \<and>
            last p = v \<and>
            (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y \<union> {{v', w}}) \<and>
            4 \<le> length p \<and> distinct (butlast p))"
            proof 
              fix u
              show "u \<in> V2 \<union> {w} \<Longrightarrow>
         \<nexists>p. p \<noteq> [] \<and>
             hd p = u \<and>
             last p = u \<and>
             (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y \<union> {{v', w}}) \<and>
             4 \<le> length p \<and> distinct (butlast p)"
              proof -
                assume "u \<in> V2 \<union> {?w}" 
                show "\<nexists>p. p \<noteq> [] \<and>
             hd p = u \<and>
             last p = u \<and>
             (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y \<union> {{v', w}}) \<and>
             4 \<le> length p \<and> distinct (butlast p)"
                proof (cases "u = ?w")
                  case True
                  show ?thesis
                  proof 
                    assume "\<exists>p. p \<noteq> [] \<and>
        hd p = u \<and>
        last p = u \<and>
        (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y \<union> {{v', w}}) \<and>
        4 \<le> length p \<and> distinct (butlast p)"
                    then obtain pa where pa_prop: "pa \<noteq> [] \<and>
        hd pa = u \<and>
        last pa = u \<and>
        (\<forall>i<length pa - 1. {pa ! i, pa ! (i + 1)} \<in> Y \<union> {{v', w}}) \<and>
        4 \<le> length pa \<and> distinct (butlast pa)" by auto
                    then have "{(nth pa 0), (nth pa 1)} \<in> Y \<union> {{?v, ?w}}" by simp
                    then have "{(nth pa 0), nth pa 1} \<subseteq> V2 \<union> {?w}" using \<open>undirected_graph (V2 \<union> {?w}) ( Y \<union> {{?v, ?w}})\<close>
                      unfolding undirected_graph_def by auto
                    have "(nth pa 0) = ?w" using True hd_conv_nth pa_prop by fastforce
                    have 1: "(nth pa 1) = ?v"
                    proof (rule ccontr)
                      assume "nth pa 1 \<noteq> ?v"
                      then have "nth pa 1 \<noteq> ?w" using \<open>nth pa 0 = ?w\<close> p_prop 
                        by (metis Int_iff UnE Y_prop \<open>\<not> {v', w} \<subseteq> V2\<close> \<open>v' \<in> V1 \<inter> V2\<close> \<open>{pa ! 0, pa ! 1} \<in> Y \<union> {{v', w}}\<close> insert_subset singleton_iff singleton_insert_inj_eq)
                      then have "{nth pa 0, nth pa 1} \<in> Y \<union> {{?v, ?w}}" using pa_prop by simp
                      then show False using \<open>nth pa 1 \<noteq> ?v\<close> \<open>nth pa 0 = ?w\<close> w_el_prop 
                        by (metis \<open>{pa ! 0, pa ! 1} \<subseteq> V2 \<union> {w}\<close> insert_commute insert_subset)
                    qed
                    have "(nth pa (length pa - 1)) = ?w" using last_conv_nth pa_prop True  by fastforce
                    moreover have "length pa - 1 - 1 < length pa - 1" using pa_prop by auto
                    moreover have "length pa - 1 - 1 + 1 = length pa - 1" using pa_prop by auto
                    ultimately have facttwo: "{nth pa (length pa - 1 - 1), nth pa (length pa - 1)} \<in> Y \<union> {{?v, ?w}}" using pa_prop by fastforce
                    then have "{nth pa (length pa - 1 - 1), ?w} \<in> Y \<union> {{?v, ?w}}" using \<open>nth pa (length pa - 1) = ?w\<close> by simp
                    then have "{nth pa (length pa - 1 - 1), ?w} \<subseteq> V2 \<union> {?w}" using \<open>undirected_graph (V2 \<union> {?w}) (Y \<union> {{?v, ?w}})\<close> unfolding undirected_graph_def by auto
                    have 2: "nth pa (length pa - 1 - 1) = ?v"
                    proof (rule ccontr)
                      assume "nth pa (length pa - 1 - 1) \<noteq> ?v"
                      then have "nth pa (length pa - 1 - 1) \<noteq> ?w" using \<open>nth pa (length pa - 1) = ?w\<close> p_prop 
                        by (metis Int_iff UnE Y_prop \<open>\<not> {v', w} \<subseteq> V2\<close> \<open>v' \<in> V1 \<inter> V2\<close> \<open>{pa ! (length pa - 1 -1 ), pa ! (length pa - 1)} \<in> Y \<union> {{v', w}}\<close> insert_subset singleton_iff singleton_insert_inj_eq)
                      then show False using \<open>nth pa (length pa - 1 - 1) \<noteq> ?v\<close> \<open>nth pa (length pa - 1) = ?w\<close> w_el_prop 
                        using \<open>{pa ! (length pa - 1 - 1), w} \<in> Y \<union> {{v', w}}\<close> \<open>{pa ! (length pa - 1 - 1), w} \<subseteq> V2 \<union> {w}\<close> by blast
                    qed
                    have "distinct (butlast pa)" using pa_prop by simp
                    show False
                    proof -
                      have "1 < length (butlast pa)" using pa_prop by auto
                      moreover have "(length pa - 1 - 1) < length (butlast pa)" using pa_prop by auto
                      moreover have "1 \<noteq> length pa - 1 - 1" using pa_prop by auto
                      ultimately have "nth pa (length pa - 1 - 1) \<noteq> (nth pa 1)" using pa_prop  
                        by (metis \<open>distinct (butlast pa)\<close> nth_butlast nth_eq_iff_index_eq)
                      then show False using 1 2 by simp
                    qed
                  qed
                next
                  case False
                  then have "u \<in> V2" using \<open>u \<in> V2 \<union> {?w}\<close> \<open>?w \<in> V1 - V2\<close> by simp
                  show ?thesis
                  proof
                    assume " \<exists>p. p \<noteq> [] \<and>
        hd p = u \<and>
        last p = u \<and>
        (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y \<union> {{v', w}}) \<and>
        4 \<le> length p \<and> distinct (butlast p)"
                    then obtain pa where pa_prop: " pa \<noteq> [] \<and>
        hd pa = u \<and>
        last pa = u \<and>
        (\<forall>i<length pa - 1. {pa ! i, pa ! (i + 1)} \<in> Y \<union> {{v', w}}) \<and>
        4 \<le> length pa \<and> distinct (butlast pa)" by auto
                    then show False
                    proof (cases "u = ?v")
                      case True
                      then show ?thesis 
                      proof (cases "List.member pa ?w")
                        case True
                        then have "?w \<in> set pa" using in_set_member pa_prop by force
                        then obtain ia where ia_prop: "nth pa ia = ?w" "ia \<ge> 0 \<and> ia < length pa" using in_set_conv_nth 
                          by (metis bot_nat_0.extremum)
                        have "ia \<noteq> 0"
                        proof
                          assume "ia = 0"
                          then have "nth pa 0 = ?w" using ia_prop by simp
                          then have "hd pa = ?w" using hd_conv_nth pa_prop by fast
                          then show False using pa_prop \<open>u \<in> V2\<close> \<open>?w \<in> V1 - V2\<close> by simp
                        qed
                        have "ia \<noteq> length pa - 1"
                        proof
                          assume "ia = length pa - 1"
                          then have "nth pa (length pa - 1) = ?w" using ia_prop by simp
                          then have "last pa = ?w" using last_conv_nth pa_prop by fast
                          then show False using pa_prop \<open>u \<in> V2\<close> \<open>?w \<in> V1 - V2\<close> by simp
                        qed
                        show ?thesis 
                        proof (cases "ia = length pa - 1 - 1")
                          case True
                          have "length pa - 1 - 1 - 1 + 1 = length pa - 1 - 1" using pa_prop by auto
                          moreover have "length pa - 1 - 1 - 1 < length pa - 1" using pa_prop by auto
                          ultimately  have fact1: "{nth pa (length pa - 1 - 1 - 1), nth pa (length pa - 1 - 1 - 1 + 1)} \<in> Y\<union> {{?v, ?w}}" using pa_prop 
                            by blast
                          then have "{nth pa (length pa - 1 - 1 - 1), nth pa (length pa - 1 - 1)} \<subseteq> V2 \<union> {?w}" using \<open>undirected_graph (V2 \<union> {?w}) (Y \<union> {{?v, ?w}})\<close>
                            unfolding undirected_graph_def 
                            by (metis \<open>length pa - 1 - 1 - 1 + 1 = length pa - 1 - 1\<close>)
                          then have fact3: "{nth pa (length pa - 1 - 1 - 1), ?w} \<subseteq> V2 \<union> {?w}" using fact1 ia_prop True \<open>length pa - 1 -1 - 1 + 1 = length pa - 1 - 1\<close> by simp 
                          have fact2: "{nth pa (length pa - 1 - 1 - 1), ?w} \<in> Y \<union> {{?v, ?w}}" using fact1 True ia_prop \<open>length pa - 1 -1 - 1 + 1 = length pa - 1 - 1\<close> by simp 
                          have "nth pa (length pa - 1 - 1 - 1) = ?v"
                          proof (rule ccontr)
                            assume "nth pa (length pa - 1 - 1 - 1) \<noteq> ?v"
                            have "nth pa (length pa - 1 - 1 - 1) \<in> V2 \<union> {?w}" using fact3 by simp
                            have "nth pa (length pa - 1 - 1 - 1) \<noteq> ?w" 
                            proof
                              assume "nth pa (length pa - 1 - 1 - 1) = ?w"
                              have "length pa - 1 - 1 - 1 < length (butlast pa)" using pa_prop by auto
                              moreover have "length pa - 1 - 1 < length (butlast pa)" using pa_prop by auto
                              moreover have "nth pa (length pa - 1- 1 - 1) = nth pa (length pa - 1 - 1)" using ia_prop \<open>nth pa (length pa - 1 - 1 -1) = ?w\<close> True by simp
                              ultimately show False using pa_prop 
                                by (meson \<open>pa ! (length pa - 1 - 1 - 1) \<noteq> v'\<close> fact2 fact3 insert_subset w_el_prop) 
                            qed
                            then show False using fact2 w_el_prop \<open>nth pa (length pa - 1 - 1 -1) \<in> V2 \<union> {?w}\<close> \<open>nth pa (length pa - 1 - 1 - 1) \<noteq> ?v\<close> by auto
                          qed
                          moreover have "nth pa 0 = ?v" using \<open>u = ?v\<close> pa_prop hd_conv_nth by fastforce
                          moreover have "0 < length (butlast pa)" using pa_prop by simp
                          moreover have "(length pa - 1 - 1 - 1) < length (butlast pa)" using pa_prop by auto
                          ultimately show False using pa_prop  nth_butlast nth_eq_iff_index_eq 
                            by (smt (verit) add_diff_inverse_nat add_le_cancel_right add_le_same_cancel2 diff_diff_cancel diff_is_0_eq' le_numeral_extra(4) length_butlast less_iff_succ_less_eq linordered_nonzero_semiring_class.zero_le_one nat_1_add_1 nat_diff_split_asm not_one_le_zero numeral_Bit0 ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
                        next
                          case False
                          have "ia \<noteq> length pa - 1" 
                          proof 
                            assume "ia = length pa - 1"
                            then have "nth pa (length pa - 1) = ?w" using ia_prop by simp
                            then have "last pa = ?w" using last_conv_nth pa_prop by blast
                            then show False using pa_prop \<open>u \<in> V2\<close> \<open>?w \<in> V1 - V2\<close> by simp
                          qed
                          then have "ia < length pa - 1 - 1" using False ia_prop by simp
                          moreover have "length pa - 1 - 1 < length pa - 1 " using pa_prop by auto
                          ultimately have "ia < length pa - 1" by simp
                          have "ia + 1 < length pa - 1 " using \<open>ia < length pa - 1 - 1\<close> by simp
                          have "{nth pa (ia), nth pa (ia + 1)} \<in> Y \<union> {{?v, ?w}}" using pa_prop \<open>ia < length pa - 1\<close> by simp
                          then have "{?w, nth pa (ia + 1)} \<in> Y \<union> {{?v, ?w}}" using ia_prop by simp
                          then have "{?w, nth pa (ia + 1)} \<subseteq> V2 \<union> {?w}" using \<open>undirected_graph (V2 \<union> {?w}) (Y \<union> {{?v, ?w}})\<close> unfolding undirected_graph_def by auto
                          have "nth pa (ia + 1) = ?v"
                          proof (rule ccontr)
                            assume "nth pa (ia + 1) \<noteq> ?v"
                            have "nth pa (ia + 1) \<noteq> ?w" 
                            proof
                              assume "nth pa (ia + 1) = ?w"
                              then have "{?w, ?w} \<in> Y \<union> {{?v, ?w}}" using \<open>{?w, nth pa (ia + 1)} \<in> Y \<union> {{?v, ?w}}\<close> by simp
                              moreover have "?v \<noteq> ?w" using \<open>?v \<in> V1 \<inter> V2\<close> \<open>?w \<in> V1 - V2\<close> by auto
                              moreover have "?w \<in> V2 \<union> {?w}" by simp
                              ultimately show False using w_el_prop by auto
                            qed
                            have "nth pa (ia + 1) \<in> V2 \<union> {?w}" using \<open>{?w, nth pa (ia+ 1)} \<subseteq> V2 \<union> {?w}\<close> by simp
                            then show False using \<open>nth pa (ia + 1) \<noteq> ?v\<close> \<open>{?w, nth pa (ia+ 1)} \<in> Y \<union> {{?v, ?w}}\<close> w_el_prop 
                              by (metis insert_commute) 
                          qed
                          have "nth pa 0 = ?v" using \<open>u = ?v\<close> pa_prop hd_conv_nth by fastforce
                          have "(ia + 1) < length (butlast pa)" using \<open>ia + 1 < length pa - 1\<close> by simp
                          moreover have "0 < length (butlast pa)" using pa_prop by simp
                          moreover have "nth pa 0 = nth pa (ia + 1)" using \<open>nth pa 0 = ?v\<close> \<open>nth pa (ia + 1) = ?v\<close> by simp
                          ultimately show False using pa_prop nth_butlast  nth_eq_iff_index_eq 
                            by (smt (verit) add_diff_inverse_nat add_le_cancel_right add_le_same_cancel2 diff_diff_cancel diff_is_0_eq' le_numeral_extra(4) length_butlast less_iff_succ_less_eq linordered_nonzero_semiring_class.zero_le_one nat_1_add_1 nat_diff_split_asm not_one_le_zero numeral_Bit0 ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
                        qed
                      next
                        case False
                        have 1: "(\<forall>i<length pa - 1. {pa ! i, pa ! (i + 1)} \<in> Y)"
                        proof (rule ccontr)
                          assume "\<not> (\<forall>i<length pa - 1. {pa ! i, pa ! (i + 1)} \<in> Y)"
                          then have "(\<exists>i<length pa - 1. {pa ! i, pa ! (i + 1)} \<notin> Y)" by simp
                          then obtain ia where ia_prop: "ia<length pa - 1 \<and> {pa ! ia, pa ! (ia + 1)} \<notin> Y" by auto
                          then have "{nth pa ia, nth pa (ia + 1)} \<in> {{?v, ?w}}" using pa_prop by auto
                          then have "{nth pa ia, nth pa (ia + 1)} = {?v, ?w}" by auto
                          then have "nth pa ia = ?w \<or> nth pa (ia + 1) = ?w" 
                            by (meson doubleton_eq_iff)
                          then have "List.member pa ?w" using ia_prop 
                            by (metis add_lessD1 in_set_member less_diff_conv nth_mem)
                          then show False using False by simp
                        qed
                        show ?thesis 
                        proof (cases "Y = {}")
                          case True
                          then show False using 1 pa_prop by force
                        next
                          case False
                          then show False using \<open>u \<in> V2\<close> \<open>acyclic V2 Y\<close> 1  unfolding acyclic_def 
                            using pa_prop by blast
                        qed
                      qed
                    next
                      case False
                      show ?thesis 
                      proof(cases "List.member pa ?w")
                        case True
                        then have "?w \<in> set pa" using in_set_member pa_prop by force
                        then obtain ia where ia_prop: "nth pa ia = ?w" "ia \<ge> 0 \<and> ia < length pa" using in_set_conv_nth 
                          by (metis bot_nat_0.extremum)
                        have "ia \<noteq> 0"
                        proof
                          assume "ia = 0"
                          then have "nth pa 0 = ?w" using ia_prop by simp
                          then have "hd pa = ?w" using hd_conv_nth pa_prop by fast
                          then show False using pa_prop \<open>u \<in> V2\<close> \<open>?w \<in> V1 - V2\<close> by simp
                        qed
                        have "ia \<noteq> length pa - 1"
                        proof
                          assume "ia = length pa - 1"
                          then have "nth pa (length pa - 1) = ?w" using ia_prop by simp
                          then have "last pa = ?w" using last_conv_nth pa_prop by fast
                          then show False using pa_prop \<open>u \<in> V2\<close> \<open>?w \<in> V1 - V2\<close> by simp
                        qed
                        have "ia \<noteq> 1"
                        proof
                          assume "ia = 1"
                          have "{nth pa 0, nth pa 1} \<in> Y \<union> {{?v, ?w}}" using pa_prop by simp
                          then have "{hd pa, ?w} \<in> Y \<union> {{?v, ?w}}" using ia_prop hd_conv_nth pa_prop \<open>ia = 1\<close> by fastforce
                          then have "{u, ?w} \<in> Y \<union> {{?v, ?w}}" using pa_prop by simp
                          moreover have "u \<in> V2 \<union> {?w}" using \<open>u \<in> V2\<close> by simp
                          ultimately show False using w_el_prop \<open>u \<noteq> ?v\<close> by auto
                        qed
                        have not_w1: "nth pa 1 \<noteq> ?w" 
                        proof
                          assume "nth pa 1 = ?w"
                          moreover have "1 < length (butlast pa)" using pa_prop by auto
                          moreover have "ia < length (butlast pa)"
                          proof (rule ccontr)
                            assume "\<not>ia < length (butlast pa)"
                            then have "ia = length pa - 1" using ia_prop by simp
                            then have "nth pa (length pa - 1) = ?w" using ia_prop by simp
                            then show False using pa_prop last_conv_nth \<open>u \<in> V2\<close> \<open>?w \<in> V1 - V2\<close> by fastforce
                          qed
                          moreover have "nth pa ia = nth pa 1" using \<open>nth pa 1=  ?w\<close> ia_prop by simp
                          ultimately show False using nth_butlast pa_prop 
                            by (metis \<open>ia \<noteq> 1\<close> nth_eq_iff_index_eq)
                        qed
                        have "ia \<noteq> (length pa - 1 - 1)"
                        proof
                          assume "ia = length pa - 1 - 1"
                          have "length pa - 1 - 1 + 1 = length pa - 1" using pa_prop by auto
                          moreover have "length pa - 1 - 1 < length pa - 1" using pa_prop by auto
                          ultimately have "{nth pa (length pa - 1 - 1), nth pa (length pa - 1 -1 + 1)} \<in> Y \<union> {{?v, ?w}}" using pa_prop by blast
                          then have "{nth pa (length pa - 1 - 1), nth pa (length pa - 1)} \<in> Y \<union> {{?v, ?w}}" using \<open>length pa - 1 -1 + 1 = length pa - 1\<close> by simp
                          then have "{last pa, ?w} \<in> Y \<union> {{?v, ?w}}" using ia_prop last_conv_nth pa_prop \<open>ia = length pa - 1 - 1\<close> by (metis insert_commute)
                          then have "{u, ?w} \<in> Y \<union> {{?v, ?w}}" using pa_prop by simp
                          moreover have "u \<in> V2 \<union> {?w}" using \<open>u \<in> V2\<close> by simp
                          ultimately show False using w_el_prop \<open>u \<noteq> ?v\<close> by auto
                        qed
                        have len2_not_w: "nth pa (length pa - 1 - 1) \<noteq> ?w" 
                        proof
                          assume "nth pa (length pa - 1 - 1) = ?w"
                          moreover have "(length pa - 1 - 1) < length (butlast pa)" using pa_prop by auto
                          moreover have "ia < length (butlast pa)"
                          proof (rule ccontr)
                            assume "\<not>ia < length (butlast pa)"
                            then have "ia = length pa - 1" using ia_prop by simp
                            then have "nth pa (length pa - 1) = ?w" using ia_prop by simp
                            then show False using pa_prop last_conv_nth \<open>u \<in> V2\<close> \<open>?w \<in> V1 - V2\<close> by fastforce
                          qed
                          moreover have "nth pa ia = nth pa (length pa - 1 - 1)" using \<open>nth pa (length pa - 1 - 1)=  ?w\<close> ia_prop by simp
                          ultimately show False using nth_butlast pa_prop 
                            by (metis \<open>ia \<noteq> (length pa - 1 - 1)\<close> nth_eq_iff_index_eq)
                        qed
                        show ?thesis
                        proof (cases "length pa = 4")
                          case True
                          have fact0: "nth pa 0 \<noteq> ?w" using pa_prop hd_conv_nth \<open>u \<in> V2\<close> \<open>?w \<in> V1 - V2\<close> by fastforce
                          have fact3: "nth pa 3 \<noteq> ?w" using pa_prop last_conv_nth \<open>u \<in> V2\<close> \<open>?w \<in> V1 - V2\<close> True by fastforce
                          have fact1: "nth pa 1 \<noteq> ?w" using not_w1 by simp
                          have fact2: "nth pa 2 \<noteq> ?w" using True len2_not_w by simp
                          have "?w \<notin> set pa"
                          proof 
                            assume "?w \<in> set  pa"
                            then obtain ia' where ia'_prop: "nth pa ia' = ?w \<and> ia' \<ge> 0 \<and> ia' < length pa" using in_set_conv_nth 
                              by (metis bot_nat_0.extremum)  
                            then have "ia' \<in> {0, 1 ,2 ,3}" using True by auto
                            then show False
                            proof (elim insertE)
                              show "ia' = 0 \<Longrightarrow> False" using fact0 ia'_prop by simp
                              show "ia' = 1 \<Longrightarrow> False" using fact1 ia'_prop by simp
                              show "ia' = 2 \<Longrightarrow> False" using fact2 ia'_prop by simp
                              show "ia' = 3 \<Longrightarrow> False" using fact3 ia'_prop by simp
                              show "ia' \<in> {} \<Longrightarrow> False" using  ia'_prop by simp
                            qed
                          qed
                          then have "\<not> List.member pa ?w" using in_set_member pa_prop by force
                          then show ?thesis using \<open>List.member pa ?w\<close> by simp
                        next
                          case False
                          then have "length pa > 4" using pa_prop by simp 
                          have "ia < length pa -1 - 1" using ia_prop \<open>ia \<noteq> length pa - 1\<close> \<open>ia \<noteq> length pa - 1 -1\<close> by simp
                          then have "ia + 1 < length (butlast pa)" by simp
                          have f1: "{nth pa ia , nth pa (ia + 1)} \<in> Y \<union> {{?v, ?w}}" using pa_prop \<open>ia < length pa - 1 - 1\<close> by simp
                          then have "{?w , nth pa (ia + 1)} \<in> Y \<union> {{?v, ?w}}" using ia_prop by simp
                          then have "{nth pa ia , nth pa (ia + 1)} \<subseteq> V2 \<union> {?w}" using f1 \<open>undirected_graph (V2 \<union>{?w}) (Y \<union> {{?v, ?w}})\<close> unfolding undirected_graph_def by auto
                          have "nth pa (ia + 1) = ?v"
                          proof (rule ccontr)
                            assume "nth pa (ia + 1) \<noteq> ?v"
                            have "nth pa (ia + 1) \<noteq> ?w" 
                            proof
                              assume "nth pa (ia + 1) = ?w"
                              then have "{?w, ?w} \<in> Y \<union> {{?v, ?w}}" using \<open>{?w, nth pa (ia + 1)} \<in> Y \<union> {{?v, ?w}}\<close> by simp
                              moreover have "?v \<noteq> ?w" using \<open>?v \<in> V1 \<inter> V2\<close> \<open>?w \<in> V1 - V2\<close> by auto
                              moreover have "?w \<in> V2 \<union> {?w}" by simp
                              ultimately show False using w_el_prop by auto
                            qed
                            have "nth pa (ia + 1) \<in> V2 \<union> {?w}" using \<open>{nth pa ia, nth pa (ia+ 1)} \<subseteq> V2 \<union> {?w}\<close> by simp
                            then show False using \<open>nth pa (ia + 1) \<noteq> ?v\<close> \<open>{?w, nth pa (ia+ 1)} \<in> Y \<union> {{?v, ?w}}\<close> w_el_prop 
                              by (metis insert_commute) 
                          qed
                          have "ia > 1" using ia_prop \<open>ia \<noteq> 1\<close>
                            by (simp add: \<open>ia \<noteq> 0\<close> nat_neq_iff)
                          have "ia - 1 \<ge> 0" by simp
                          moreover have "ia - 1 < length (butlast pa)" using pa_prop ia_prop by auto
                          moreover have "ia - 1 < length pa - 1" using pa_prop ia_prop by auto
                          moreover have "ia - 1 + 1 = ia" using \<open>ia > 1\<close> by simp
                          ultimately have "{nth pa (ia - 1), nth pa ia} \<in> Y \<union> {{?v, ?w}}" using pa_prop by metis
                          then have "{nth pa (ia - 1), ?w} \<in> Y \<union> {{?v, ?w}}" using ia_prop by simp
                          then have "{nth pa (ia - 1) , ?w} \<subseteq> V2 \<union> {?w}" using \<open>undirected_graph (V2 \<union>{?w}) (Y \<union> {{?v, ?w}})\<close> unfolding undirected_graph_def by auto
                          have "nth pa (ia - 1) = ?v"
                          proof (rule ccontr)
                            assume "nth pa (ia - 1) \<noteq> ?v"
                            have "nth pa (ia - 1) \<noteq> ?w" 
                            proof
                              assume "nth pa (ia - 1) = ?w"
                              then have "{?w, ?w} \<in> Y \<union> {{?v, ?w}}" using \<open>{nth pa (ia - 1), ?w} \<in> Y \<union> {{?v, ?w}}\<close> by simp
                              moreover have "?v \<noteq> ?w" using \<open>?v \<in> V1 \<inter> V2\<close> \<open>?w \<in> V1 - V2\<close> by auto
                              moreover have "?w \<in> V2 \<union> {?w}" by simp
                              ultimately show False using w_el_prop by auto
                            qed
                            have "nth pa (ia - 1) \<in> V2 \<union> {?w}" using \<open>{nth pa (ia - 1), ?w} \<subseteq> V2 \<union> {?w}\<close> by simp
                            then show False using \<open>nth pa (ia - 1) \<noteq> ?v\<close> \<open>{nth pa (ia - 1), ?w} \<in> Y \<union> {{?v, ?w}}\<close> w_el_prop 
                              by (metis insert_commute) 
                          qed
                          then show ?thesis using \<open>ia - 1 < length (butlast pa)\<close> \<open>ia + 1 < length (butlast pa)\<close> \<open>nth pa (ia + 1) = ?v\<close> nth_butlast pa_prop
                              nth_eq_iff_index_eq  by (smt (verit) add_diff_inverse_nat add_le_cancel_right add_le_same_cancel2 diff_diff_cancel diff_is_0_eq' le_numeral_extra(4) length_butlast less_iff_succ_less_eq linordered_nonzero_semiring_class.zero_le_one nat_1_add_1 nat_diff_split_asm not_one_le_zero numeral_Bit0 ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
                        qed
                      next
                        case False
                        have 1: "(\<forall>i<length pa - 1. {pa ! i, pa ! (i + 1)} \<in> Y)"
                        proof (rule ccontr)
                          assume "\<not> (\<forall>i<length pa - 1. {pa ! i, pa ! (i + 1)} \<in> Y)"
                          then have "(\<exists>i<length pa - 1. {pa ! i, pa ! (i + 1)} \<notin> Y)" by simp
                          then obtain ia where ia_prop: "ia<length pa - 1 \<and> {pa ! ia, pa ! (ia + 1)} \<notin> Y" by auto
                          then have "{nth pa ia, nth pa (ia + 1)} \<in> {{?v, ?w}}" using pa_prop by auto
                          then have "{nth pa ia, nth pa (ia + 1)} = {?v, ?w}" by auto
                          then have "nth pa ia = ?w \<or> nth pa (ia + 1) = ?w" 
                            by (meson doubleton_eq_iff)
                          then have "List.member pa ?w" using ia_prop 
                            by (metis add_lessD1 in_set_member less_diff_conv nth_mem)
                          then show False using False by simp
                        qed
                        show ?thesis 
                        proof (cases "Y = {}")
                          case True
                          then show False using 1 pa_prop by force
                        next
                          case False
                          then show False using \<open>u \<in> V2\<close> \<open>acyclic V2 Y\<close> 1  unfolding acyclic_def 
                            using pa_prop by blast
                        qed
                        qed
                    qed
                  qed
                qed
              qed
            qed
            then show "Y \<union> {{v', w}} = {} \<or>
    (\<forall>v\<in>V2 \<union> {w}.
        \<nexists>p. p \<noteq> [] \<and>
            hd p = v \<and>
            last p = v \<and>
            (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y \<union> {{v', w}}) \<and>
            4 \<le> length p \<and> distinct (butlast p))" by simp
          qed
          have "connected (V2 \<union> {?w}) (Y \<union> {{?v, ?w}})" unfolding connected_def
          proof (cases "Y = {} \<and> card V2 = 1")
            case True
            then have "Y \<union> {{?v, ?w}} = {{?v, ?w}}" by simp
            have "V2 = {r}" using \<open>r \<in> V2\<close>  True card_1_singletonE by auto
            have "r \<in> V1 \<inter> V2" using \<open>r \<in> V1\<close> \<open>r \<in> V2\<close> by simp
            then have "?v = r" using \<open>r \<in> V1 \<inter> V2\<close> \<open>?v \<in> V1 \<inter> V2\<close> \<open>V2 = {r}\<close> by simp
            then have "V2 = {?v}" using \<open>V2 = {r}\<close> by simp
            then have "V2 \<union> {?w} = {?v, ?w}" by auto
            have "(\<forall>u v. u \<in> V2 \<union> {w} \<and> v \<in> V2 \<union> {w} \<and> u \<noteq> v \<longrightarrow>
           (\<exists>p. p \<noteq> [] \<and>
                (hd p = v \<and> last p = u) \<and>
                (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y \<union> {{v', w}}) \<and>
                2 \<le> length p))"
            proof (rule, rule)
              fix u v
              show " u \<in> V2 \<union> {w} \<and> v \<in> V2 \<union> {w} \<and> u \<noteq> v \<longrightarrow>
           (\<exists>p. p \<noteq> [] \<and>
                (hd p = v \<and> last p = u) \<and>
                (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y \<union> {{v', w}}) \<and>
                2 \<le> length p)"
              proof
                assume u_v_prop: "u \<in> V2 \<union> {w} \<and> v \<in> V2 \<union> {w} \<and> u \<noteq> v"
                show "\<exists>p. p \<noteq> [] \<and>
        (hd p = v \<and> last p = u) \<and>
        (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y \<union> {{v', w}}) \<and> 2 \<le> length p "
                proof (cases "u = ?v")
                  case True
                  then have "v = ?w" using u_v_prop \<open>V2 \<union> {?w} = {?v, ?w}\<close> by auto
                  let ?p = "[ ?w, ?v]"
                  have "?p \<noteq> []" by simp
                  moreover have "length ?p \<ge> 2" by simp
                  moreover have "hd ?p = ?w \<and> last ?p = ?v" using hd_conv_nth last_conv_nth by fastforce
                  moreover have "(\<forall>i<length ?p - 1. {?p ! i, ?p ! (i + 1)} \<in> Y \<union> {{v', w}})" using \<open>Y \<union> {{v', w}} = {{v', w}}\<close>
                    by auto
                  ultimately have "?p \<noteq> [] \<and> length ?p \<ge> 2 \<and> hd ?p = ?w \<and> last ?p = ?v \<and> (\<forall>i<length ?p - 1. {?p ! i, ?p ! (i + 1)} \<in> Y \<union> {{v', w}})" by simp
                  then show ?thesis using True \<open>v = ?w\<close> by blast
                next
                  case False
                  then have "u = ?w" using u_v_prop \<open>V2 \<union> {?w} = {?v, ?w}\<close> by auto
                  then have "v = ?v" using u_v_prop \<open>V2 \<union> {?w} = {?v, ?w}\<close> by auto
                  let ?p = "[?v, ?w]"
                  have "?p \<noteq> []" by simp
                  moreover have "length ?p \<ge> 2" by simp
                  moreover have "hd ?p = ?v \<and> last ?p = ?w" using hd_conv_nth last_conv_nth by fastforce
                  moreover have "(\<forall>i<length ?p - 1. {?p ! i, ?p ! (i + 1)} \<in> Y \<union> {{v', w}})" using \<open>Y \<union> {{v', w}} = {{v', w}}\<close>
                    by auto
                  ultimately have "?p \<noteq> [] \<and> length ?p \<ge> 2 \<and> hd ?p = ?v \<and> last ?p = ?w \<and> (\<forall>i<length ?p - 1. {?p ! i, ?p ! (i + 1)} \<in> Y \<union> {{v', w}})" by simp
                  then show ?thesis using \<open>u = ?w\<close> \<open>v = ?v\<close> by blast
                qed
              qed
            qed
            then show \<open>Y \<union> {{v', w}} = {} \<and> card (V2 \<union> {w}) = 1 \<or>
    (\<forall>u v. u \<in> V2 \<union> {w} \<and> v \<in> V2 \<union> {w} \<and> u \<noteq> v \<longrightarrow>
           (\<exists>p. p \<noteq> [] \<and>
                (hd p = v \<and> last p = u) \<and>
                (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y \<union> {{v', w}}) \<and>
                2 \<le> length p))\<close> by simp
          next
            case False
            then have Y_connected: "(\<forall>u v. u \<in> V2 \<and> v \<in> V2  \<and> u \<noteq> v \<longrightarrow>
           (\<exists>p. p \<noteq> [] \<and>
                (hd p = v \<and> last p = u) \<and>
                (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y) \<and>
                2 \<le> length p))" using \<open>connected V2 Y\<close> unfolding connected_def by auto
            have "(\<forall>u v. u \<in> V2 \<union> {w} \<and> v \<in> V2 \<union> {w} \<and> u \<noteq> v \<longrightarrow>
           (\<exists>p. p \<noteq> [] \<and>
                (hd p = v \<and> last p = u) \<and>
                (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y \<union> {{v', w}}) \<and>
                2 \<le> length p))"
            proof (rule, rule)
              fix u v
              show " u \<in> V2 \<union> {w} \<and> v \<in> V2 \<union> {w} \<and> u \<noteq> v \<longrightarrow>
           (\<exists>p. p \<noteq> [] \<and>
                (hd p = v \<and> last p = u) \<and>
                (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y \<union> {{v', w}}) \<and>
                2 \<le> length p)"
              proof
                assume u_v_prop: " u \<in> V2 \<union> {w} \<and> v \<in> V2 \<union> {w} \<and> u \<noteq> v"
                show "
           (\<exists>p. p \<noteq> [] \<and>
                (hd p = v \<and> last p = u) \<and>
                (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y \<union> {{v', w}}) \<and>
                2 \<le> length p)"
                proof (cases "u \<in> V2 \<and> v \<in> V2")
                  case True
                  then have "u \<noteq> ?w \<and> v \<noteq> ?w" using \<open>?w \<in> V1 - V2\<close> by auto
                  then have "(\<exists>p. p \<noteq> [] \<and>
                (hd p = v \<and> last p = u) \<and>
                (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y) \<and>
                2 \<le> length p)" using True Y_connected u_v_prop by simp
                  then show ?thesis by auto
                next
                  case False
                  then have "u \<notin> V2 \<or> v \<notin> V2" by simp
                  show ?thesis
                  proof (cases "u \<notin> V2")
                    case True
                    then have "u = ?w" using u_v_prop by simp
                    then have "v \<in> V2 " using u_v_prop by auto
                    show ?thesis
                    proof (cases "v = ?v")
                      case True
                      let ?p = "[?v, ?w]"
                      have "?p \<noteq> []" by simp
                      moreover have "length ?p \<ge> 2" by simp
                  moreover have "hd ?p = ?v \<and> last ?p = ?w" using hd_conv_nth last_conv_nth by fastforce
                  moreover have "(\<forall>i<length ?p - 1. {?p ! i, ?p ! (i + 1)} \<in> Y \<union> {{v', w}})" 
                    by auto
                  ultimately have "?p \<noteq> [] \<and> length ?p \<ge> 2 \<and> hd ?p = ?v \<and> last ?p = ?w \<and> (\<forall>i<length ?p - 1. {?p ! i, ?p ! (i + 1)} \<in> Y \<union> {{v', w}})" by simp
                  then show ?thesis using \<open>u = ?w\<close> \<open>v = ?v\<close> by blast
                    next
                      case False
                      then have "\<exists>p. p \<noteq> [] \<and>
        (hd p = v \<and> last p = ?v) \<and>
        (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y) \<and> 2 \<le> length p" using \<open>?v \<in> V1 \<inter> V2\<close>  \<open>v \<in> V2\<close> Y_connected by simp
                      then obtain pa where pa_prop: "pa \<noteq> [] \<and>
        (hd pa = v \<and> last pa = ?v) \<and>
        (\<forall>i<length pa - 1. {pa ! i, pa ! (i + 1)} \<in> Y) \<and> 2 \<le> length pa" by auto
                      let ?p = "pa @ [?w]"
                      have "?p \<noteq> []" by simp
                      have "hd ?p = v \<and> last ?p = ?w" using hd_conv_nth last_conv_nth pa_prop by fastforce
                      have "length ?p \<ge> 2"  using pa_prop by simp
                      then have "length ?p - 1- 1 < length ?p - 1" by simp
                      have "length ?p  - 1 = length pa" by simp
                      moreover have "(\<forall> i < length pa. nth pa i = nth ?p i)" 
                        by (simp add: nth_append)
                      ultimately have factone: "(\<forall> i < length ?p - 1. nth pa i = nth ?p i)" by simp
                      then have "(\<forall>i<length pa - 1. {?p ! i, ?p ! (i + 1)} \<in> Y )" using pa_prop by auto
                      then have "(\<forall>i<length ?p - 1 - 1. {?p ! i, ?p ! (i + 1)} \<in> Y )" using \<open>length ?p - 1 = length pa\<close> by simp
                      then have facttwo: "(\<forall>i<length ?p - 1 - 1. {?p ! i, ?p ! (i + 1)} \<in> Y \<union> {{?v, ?w}})" by simp
                      have "(\<forall>i<length ?p - 1. {?p ! i, ?p ! (i + 1)} \<in> Y \<union> {{?v, ?w}})"
                      proof - 
                        have "length ?p - 1 - 1 = length pa - 1" by simp
                        then have "nth ?p (length ?p - 1 - 1) = nth pa (length pa - 1)" using factone pa_prop by auto
                        also have "... = ?v" using pa_prop last_conv_nth by fastforce
                        finally have "nth ?p (length ?p - 1 - 1) = ?v" by simp
                        have "nth ?p (length ?p - 1) = ?w" by simp
                        have "length ?p - 1 - 1 + 1 = length ?p - 1" using \<open>length ?p \<ge> 2\<close> by simp
                        then have "{nth ?p (length ?p - 1 - 1), nth ?p (length ?p - 1 - 1 + 1)} = {?v, ?w}" using \<open>nth ?p (length ?p - 1) = ?w\<close> \<open>nth ?p (length ?p - 1 - 1) = ?v\<close> by simp
                        also have "... \<in> Y \<union> {{?v, ?w}}" by simp
                        finally have "{nth ?p (length ?p - 1 - 1), nth ?p (length ?p - 1 - 1 + 1)} \<in> Y \<union> {{?v, ?w}}" by simp
                        then show ?thesis using facttwo 
                          by (smt (verit, del_insts) \<open>length (pa @ [w]) - 1 - 1 + 1 = length (pa @ [w]) - 1\<close> add.commute diff_add_inverse2 less_iff_succ_less_eq nat_add_left_cancel_less nat_less_le)
                      qed
                      then show ?thesis using \<open>length ?p \<ge> 2\<close> \<open>?p \<noteq> []\<close> \<open>hd ?p = v \<and> last ?p = ?w\<close> \<open>u = ?w\<close> by blast
                    qed
                  next
                    case False
                    then have "v = ?w" using u_v_prop \<open>u \<notin> V2 \<or> v \<notin> V2\<close> by simp
                    then have "u \<in> V2 " using u_v_prop by auto
                    show ?thesis
                    proof (cases "u = ?v")
                      case True
                      let ?p = "[?w, ?v]"
                      have "?p \<noteq> []" by simp
                      moreover have "length ?p \<ge> 2" by simp
                  moreover have "hd ?p = ?w \<and> last ?p = ?v" using hd_conv_nth last_conv_nth by fastforce
                  moreover have "(\<forall>i<length ?p - 1. {?p ! i, ?p ! (i + 1)} \<in> Y \<union> {{v', w}})" 
                    by auto
                  ultimately have "?p \<noteq> [] \<and> length ?p \<ge> 2 \<and> hd ?p = ?w \<and> last ?p = ?v \<and> (\<forall>i<length ?p - 1. {?p ! i, ?p ! (i + 1)} \<in> Y \<union> {{v', w}})" by simp
                  then show ?thesis using \<open>u = ?v\<close> \<open>v = ?w\<close> by blast
                    next
                      case False
                      then have "\<exists>p. p \<noteq> [] \<and>
        (hd p = u \<and> last p = ?v) \<and>
        (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y) \<and> 2 \<le> length p" using \<open>?v \<in> V1 \<inter> V2\<close>  \<open>u \<in> V2\<close> Y_connected by simp
                      then obtain pa where pa_prop: "pa \<noteq> [] \<and>
        (hd pa = u \<and> last pa = ?v) \<and>
        (\<forall>i<length pa - 1. {pa ! i, pa ! (i + 1)} \<in> Y) \<and> 2 \<le> length pa" by auto
                      let ?p = "pa @ [?w]"
                      have "?p \<noteq> []" by simp
                      have "hd ?p = u \<and> last ?p = ?w" using hd_conv_nth last_conv_nth pa_prop by fastforce
                      have "length ?p \<ge> 2"  using pa_prop by simp
                      then have "length ?p - 1- 1 < length ?p - 1" by simp
                      have "length ?p  - 1 = length pa" by simp
                      moreover have "(\<forall> i < length pa. nth pa i = nth ?p i)" 
                        by (simp add: nth_append)
                      ultimately have factone: "(\<forall> i < length ?p - 1. nth pa i = nth ?p i)" by simp
                      then have "(\<forall>i<length pa - 1. {?p ! i, ?p ! (i + 1)} \<in> Y )" using pa_prop by auto
                      then have "(\<forall>i<length ?p - 1 - 1. {?p ! i, ?p ! (i + 1)} \<in> Y )" using \<open>length ?p - 1 = length pa\<close> by simp
                      then have facttwo: "(\<forall>i<length ?p - 1 - 1. {?p ! i, ?p ! (i + 1)} \<in> Y \<union> {{?v, ?w}})" by simp
                      have factthree:"(\<forall>i<length ?p - 1. {?p ! i, ?p ! (i + 1)} \<in> Y \<union> {{?v, ?w}})"
                      proof - 
                        have "length ?p - 1 - 1 = length pa - 1" by simp
                        then have "nth ?p (length ?p - 1 - 1) = nth pa (length pa - 1)" using factone pa_prop by auto
                        also have "... = ?v" using pa_prop last_conv_nth by fastforce
                        finally have "nth ?p (length ?p - 1 - 1) = ?v" by simp
                        have "nth ?p (length ?p - 1) = ?w" by simp
                        have "length ?p - 1 - 1 + 1 = length ?p - 1" using \<open>length ?p \<ge> 2\<close> by simp
                        then have "{nth ?p (length ?p - 1 - 1), nth ?p (length ?p - 1 - 1 + 1)} = {?v, ?w}" using \<open>nth ?p (length ?p - 1) = ?w\<close> \<open>nth ?p (length ?p - 1 - 1) = ?v\<close> by simp
                        also have "... \<in> Y \<union> {{?v, ?w}}" by simp
                        finally have "{nth ?p (length ?p - 1 - 1), nth ?p (length ?p - 1 - 1 + 1)} \<in> Y \<union> {{?v, ?w}}" by simp
                        then show ?thesis using facttwo 
                          by (smt (verit, del_insts) \<open>length (pa @ [w]) - 1 - 1 + 1 = length (pa @ [w]) - 1\<close> add.commute diff_add_inverse2 less_iff_succ_less_eq nat_add_left_cancel_less nat_less_le)
                      qed
                      let ?p' = "rev ?p"
                      have "?p' \<noteq> []" by simp
                      moreover have "length ?p' \<ge> 2" using \<open>length ?p \<ge> 2\<close> by simp
                      moreover have "hd ?p' = ?w \<and> last ?p' = u" using \<open>hd ?p = u \<and> last ?p = ?w\<close>  
                        by (metis hd_rev rev_rev_ident)
                      moreover have "(\<forall>i<length ?p' - 1. {?p' ! i, ?p' ! (i + 1)} \<in> Y \<union> {{?v, ?w}})" 
                      proof (rule allI impI)
                        fix i
                        show "i < length (rev (pa @ [w])) - 1 \<longrightarrow>
         {rev (pa @ [w]) ! i, rev (pa @ [w]) ! (i + 1)} \<in> Y \<union> {{v', w}} "
                        proof
                        assume "i < length (rev (pa @ [w])) - 1"
                        then have "length ?p' - 1 - 1 - i< length ?p' - 1" using \<open>i < length (?p') - 1\<close> by simp
                        then have "length ?p' - 1 - (i + 1) < length ?p' - 1" by simp
                        then have "length ?p' - 1 - (i + 1) + 1  = length ?p' - 1 - i" using \<open>length ?p' \<ge> 2\<close> 
                          using Suc_diff_Suc \<open>i < length (rev (pa @ [w])) - 1\<close> by presburger
                        then have "length ?p' - 1 - i < length ?p'" using \<open>length ?p' - 1 - (i + 1) < length ?p' - 1\<close> by auto 
                        have "length ?p' - 1 - (i + 1) < length ?p'" using \<open>length ?p' - 1 - (i + 1) < length ?p' - 1\<close> \<open>length ?p' \<ge> 2\<close> by simp
                        have f1: "length ?p' - 1 - (length ?p - 1 - (i + 1)) = i + 1" using \<open>length ?p' - 1 - (i + 1) < length ?p' - 1\<close> \<open>length ?p' \<ge> 2\<close>
                          using \<open>i < length (rev (pa @ [w])) - 1\<close> by fastforce
                        have f2: "length ?p' - 1 - (length ?p' - 1 - i) = i" using \<open>i < length ?p' - 1\<close> by fastforce
                        have "length ?p' - 1 - 1 - i< length ?p - 1" using \<open>length ?p' - 1 - 1 - i< length ?p' - 1\<close> by simp
                        then have f3: "{?p ! (length ?p' - 1 - (i + 1)), ?p ! (length ?p' - 1 - i)} \<in> Y \<union> {{?v, ?w}}" using \<open>length ?p' - 1 - (i + 1) + 1  = length ?p' - 1 - i\<close> factthree by fastforce
                        have "\<forall>i. i < length ?p \<longrightarrow> nth ?p i = nth ?p' (length ?p - 1 - i)" 
                          by (smt (verit, best) Nat.lessE Suc_diff_1 cancel_comm_monoid_add_class.diff_cancel diff_Suc_1' diff_Suc_Suc length_rev rev_nth rev_rev_ident zero_less_one)
                        then have "{?p ! (length ?p' - 1 - (i + 1)), ?p ! (length ?p' - 1 - i)} = {nth ?p' (i + 1), nth ?p' i}" using f1 f2 \<open>length ?p' - 1 - (i + 1) < length ?p' - 1\<close> 
                          \<open>length ?p' \<ge> 2\<close> 
                          by (metis \<open>length (rev (pa @ [w])) - 1 - (i + 1) < length (rev (pa @ [w]))\<close> \<open>length (rev (pa @ [w])) - 1 - i < length (rev (pa @ [w]))\<close> f1 f2 length_rev)
                        then show " {rev (pa @ [w]) ! i, rev (pa @ [w]) ! (i + 1)} \<in> Y \<union> {{v', w}}" using f3 insert_commute by metis
                      qed
                    qed
                      ultimately show ?thesis using \<open>v = ?w\<close> by blast
                    qed
                  qed
                qed
              qed
            qed
            then show "Y \<union> {{v', w}} = {} \<and> card (V2 \<union> {w}) = 1 \<or>
    (\<forall>u v. u \<in> V2 \<union> {w} \<and> v \<in> V2 \<union> {w} \<and> u \<noteq> v \<longrightarrow>
           (\<exists>p. p \<noteq> [] \<and>
                (hd p = v \<and> last p = u) \<and>
                (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y \<union> {{v', w}}) \<and>
                2 \<le> length p))" by simp
          qed
          have "finite Y" using Y_prop \<open>finite V2\<close>  by (meson Sup_le_iff finite_UnionD rev_finite_subset)
          then have "finite (Y \<union> {{?v, ?w}})" by simp
          have "card (V2 \<union> {?w}) = card (V2) + 1" using  \<open>?w \<in> V1 - V2\<close> \<open>finite V2\<close> by simp
           have  "card V2 + 1 = card Y + 1 + 1" using \<open>card V2 = card Y + 1\<close> by simp
           then have "card Y + 1 = card (Y \<union> {{?v, ?w}})" using \<open>{?v, ?w} \<notin> Y\<close> \<open>finite Y\<close> by simp
           then have "card Y + 1 + 1 = card (Y \<union> {{?v, ?w}}) + 1"  by simp 
           then have "card V2 +1 =  card (Y \<union> {{?v, ?w}}) + 1" using \<open>card V2 + 1 = card Y + 1 + 1\<close> by simp
           then have "card (V2 \<union> {?w}) = card (Y \<union> {{?v, ?w}}) + 1" using \<open>card (V2 \<union> {?w}) = card V2 + 1\<close> by simp
           then have "tree (V2 \<union> {?w}) (Y \<union> {{?v, ?w}})" using \<open>acyclic (V2 \<union> {?w}) (Y \<union> {{?v, ?w}})\<close>
\<open>connected (V2 \<union> {?w}) (Y \<union> {{?v, ?w}})\<close> \<open>undirected_graph (V2 \<union> {?w}) (Y \<union> {{?v, ?w}})\<close> unfolding tree_def by simp
           moreover have "V2 \<union> {?w} \<subseteq> V" using \<open>?w \<in> V1 - V2\<close> X_prop1 Y_prop by auto
           moreover have "{?v, ?w} \<in> X - Y" using \<open>{?v, ?w} \<in> X\<close> \<open>{?v, ?w} \<notin> Y\<close> by simp
           moreover have "r \<in> V2 \<union> {?w}" using \<open>r \<in> V2\<close> by simp
           moreover have "Y \<union> {{?v, ?w}} \<subseteq> E" using \<open>{?v, ?w} \<in> X\<close> V1_prop V2_prop by auto
           ultimately have "Y \<union> {{?v, ?w}} \<in> {Y. \<exists>X\<subseteq>V. Y \<subseteq> E \<and> r \<in> X \<and> tree X Y}" by blast 
           then show ?thesis using \<open>{?v, ?w} \<in> X - Y\<close> by auto
         qed
       qed
     qed
   qed
end

locale greedy_algorithm = greedoid +
  fixes orcl::"'a set \<Rightarrow> bool"
  fixes es
  assumes orcl_correct: "\<And> X. X \<subseteq> E \<Longrightarrow> orcl X \<longleftrightarrow> X \<in> F"
  assumes set_assum: "set es = E \<and> distinct es" 


context greedy_algorithm
begin

  definition valid_modular_weight_func::"('a set \<Rightarrow> real) \<Rightarrow> bool" where  "valid_modular_weight_func c = (c ({}) = 0 \<and> (\<forall>X l. X \<subseteq> E \<and> X \<noteq> {} \<and> l = {c {e} | e. e \<in> X} \<longrightarrow> c (X) = sum (\<lambda>x. x) l \<and> c X > 0))"

  definition "maximum_weight_set c X = (X \<in> F \<and> (\<forall> Y \<in> F. c X \<ge> c Y))"

  definition "find_best_candidate c F' = foldr (\<lambda> e acc. if e \<in> F' \<or> \<not> orcl (insert e F') then acc
                                                      else (case acc of None \<Rightarrow> Some e |
                                                               Some d \<Rightarrow> (if c {e} > c {d} then Some e
                                                                          else Some d))) es None"

(*Next two lemmas taken as facts: the best candidate for F' lies in es (list of E), and does not lie in F'.*)
lemma find_best_candidate_in_es: assumes "F' \<subseteq> E" "find_best_candidate c F' = Some x"
  shows "List.member es x"
  using assms
  unfolding find_best_candidate_def
  apply(induction es)
   apply auto
  by (smt (verit, best) member_rec(1) option.case_eq_if option.collapse option.inject)

lemma find_best_candidate_notin_F': assumes "F' \<subseteq> E" "find_best_candidate c F' = Some x"
  shows "x \<notin> F'"

  using assms
  unfolding find_best_candidate_def
apply(induction es)
   apply auto
  by (smt (verit, best) member_rec(1) option.case_eq_if option.collapse option.inject)


function (domintros) greedy_algorithm_greedoid::"'a set \<Rightarrow> ('a set \<Rightarrow> real) \<Rightarrow> 'a set" where "greedy_algorithm_greedoid F' c = (if (\<not>(F' \<subseteq> E \<and> F' \<in> F)) then undefined 
else  (case  (find_best_candidate c F') of Some e => greedy_algorithm_greedoid(F' \<union> {the (find_best_candidate c F')}) c | None => F'))"
  by pat_completeness auto

lemma greedy_algo_term: shows "All greedy_algorithm_greedoid_dom"
proof (relation "measure (\<lambda>(F', c). card (E - F'))")
  show " wf (measure (\<lambda>(F', c). card (E - F')))" by (rule wf_measure)
  show "\<And>F' c x2.
       \<not> \<not> (F' \<subseteq> E \<and> F' \<in> F) \<Longrightarrow>
       find_best_candidate c F' = Some x2 \<Longrightarrow>
       ((F' \<union> {the (find_best_candidate c F')}, c), F', c)
       \<in> measure (\<lambda>(F', c). card (E - F'))"
  proof -
    fix F' c x
    show "\<not> \<not> (F' \<subseteq> E \<and> F' \<in> F) \<Longrightarrow>
       find_best_candidate c F' = Some x \<Longrightarrow>
       ((F' \<union> {the (find_best_candidate c F')}, c), F', c)
       \<in> measure (\<lambda>(F', c). card (E - F'))"
    proof - 
      assume assum1: "\<not> \<not> (F' \<subseteq> E \<and> F' \<in> F)"
      show "find_best_candidate c F' = Some x \<Longrightarrow>
    ((F' \<union> {the (find_best_candidate c F')}, c), F', c)
    \<in> measure (\<lambda>(F', c). card (E - F'))"
      proof -
        assume assum2: "find_best_candidate c F' = Some x"
        then have "List.member es x" using find_best_candidate_in_es assum1 by auto
        then have "es \<noteq> []" 
          using member_rec(2) by force
        then have "length es > 0" using assum1 set_assum by auto
        then have "x \<in> set es" using in_set_member \<open>List.member es x\<close> assum1 by fast
        then have "x \<in> E" using set_assum by simp
        have "x \<notin> F'" using assum1 assum2 find_best_candidate_notin_F' by auto
        then have "x \<in> E - F'" using \<open>x \<in> E\<close> assum1 by simp
        then have "F' \<subset> F' \<union> {the (find_best_candidate c F')}" using \<open>x \<notin> F'\<close> assum2 by auto
        then have "E - (F' \<union> {the (find_best_candidate c F')}) \<subset> E - F'" 
          by (metis Diff_insert Diff_insert_absorb Un_empty_right Un_insert_right \<open>x \<in> E - F'\<close> assum2 mk_disjoint_insert option.sel psubsetI subset_insertI)
      have "finite E" using ss_assum unfolding set_system_def by simp
      then have "finite F'" using finite_subset assum1 by auto
      then have "finite (E - F')" using \<open>finite E\<close> by blast
      then have "card (E - (F' \<union> {the (find_best_candidate c F')})) < card (E - F')" 
        using \<open>E - (F' \<union> {the (find_best_candidate c F')}) \<subset> E - F'\<close> psubset_card_mono by auto
      then show ?thesis by auto
  qed
qed
qed
qed

end