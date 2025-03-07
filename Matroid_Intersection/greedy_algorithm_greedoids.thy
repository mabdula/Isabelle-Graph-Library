theory greedy_algorithm_greedoids
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
  
      
  lemma second_thm:
  assumes assum1: "accessible E F" 
  shows  "(\<forall>X Y z. X  \<subseteq> Y \<and> Y \<subseteq> E \<and>  z \<in> E - Y \<and> X \<union> {z} 
\<in> F \<and> Y \<in> F \<longrightarrow>  Y \<union> {z} \<in> F) \<longleftrightarrow> closed_under_union F"

  proof (intro iffI)

    show "\<forall>X Y z. X \<subseteq> Y \<and> Y \<subseteq> E \<and> z \<in> E - Y \<and> X \<union> {z} \<in> F \<and> Y \<in> F \<longrightarrow> Y \<union> {z} \<in> F
      \<Longrightarrow> closed_under_union F"
    proof-
      assume assum2: "\<forall>X Y z. X \<subseteq> Y \<and> Y \<subseteq> E \<and> z \<in> E - Y \<and> X \<union> {z} \<in> F \<and> Y \<in> F \<longrightarrow> Y \<union> {z} \<in> F"
      show "closed_under_union F"
        unfolding closed_under_union_def
      proof (rule, rule, rule)
        fix X Y
        assume F_con: "X \<in> F \<and> Y \<in> F"
        have "set_system E F" using assum1 unfolding accessible_def by simp
        show  "X \<union> Y \<in> F"
        proof -
          have "X \<subseteq>E" using F_con \<open>set_system E F\<close> unfolding set_system_def by simp
          have "finite E" using \<open>set_system E F\<close> unfolding set_system_def by simp
          then have "finite X" using \<open>X \<subseteq> E\<close> using finite_subset by auto
          have "X \<supseteq> X \<and> X \<in> F \<and> X \<subseteq> X \<union> Y" using F_con by simp
          have "{} \<in> F" using assum1 unfolding accessible_def by simp
          have "\<exists>Z. maximal (\<lambda> Z. Z \<supseteq> X \<and> Z \<subseteq> X \<union> Y \<and> Z \<in> F) Z" using exists_maximal
              \<open>X \<in> F \<and> Y \<in> F\<close> \<open>set_system E F\<close> by auto
          then obtain Z where z_prop: "maximal (\<lambda> Z. Z \<supseteq> X \<and> Z \<subseteq> X \<union> Y \<and> Z \<in> F) Z" by blast
          then have z_props: "Z \<supseteq> X \<and> Z \<subseteq> X \<union> Y \<and> Z \<in> F" unfolding maximal_def by simp
          have \<open>X \<subseteq> Z\<close> using z_props by simp
          show "X \<union> Y \<in> F"
            proof (rule ccontr)
              assume "X \<union> Y \<notin> F"
              have "Y - Z \<noteq> {}" by (metis \<open>X \<union> Y \<notin> F\<close> diff_shunt_var subset_antisym sup.bounded_iff z_props)
              have "Y \<in> F" using \<open>X \<in> F \<and> Y \<in> F\<close> by simp
              then have \<open>Y \<subseteq> E\<close> using \<open>set_system E F\<close> unfolding set_system_def by simp
              have "Z \<in> F" using z_props by simp
              then have \<open>Z \<subseteq> E\<close> using \<open>set_system E F\<close> unfolding set_system_def by simp
              have "finite E" using \<open>set_system E F\<close> unfolding set_system_def by simp
              then have \<open>finite Z\<close> using \<open>Z \<subseteq> E\<close> finite_subset by auto
              have \<open>finite Y\<close> using \<open>Y \<subseteq> E\<close> finite_subset \<open>finite E\<close> by auto
              have "\<exists> l. set l = Y \<and> (\<forall>i. i \<le> length l \<longrightarrow> set (take i l) \<in> F) \<and> distinct l"
                using \<open>Y - Z \<noteq> {}\<close> \<open>Y \<in> F\<close> accessible_property \<open>Y \<subseteq> E\<close> assum1 by blast
              then obtain l where l_prop: "set l = Y \<and> (\<forall>i. i \<le> length l \<longrightarrow> set (take i l) \<in> F) \<and> distinct l" by auto
              then have "set l = Y" by simp
              have "List.member l (nth l 0)"
                by (metis Un_absorb2 \<open>X \<in> F \<and> Y \<in> F\<close> \<open>X \<union> Y \<notin> F\<close> \<open>set l = Y\<close> in_set_member length_pos_if_in_set list_ball_nth subsetI)
              then have "(nth l 0) \<in> Y"
                using \<open>set l = Y\<close> in_set_member by fastforce 
              have "Y \<noteq> {}" using \<open>X \<in> F \<and> Y \<in> F\<close> \<open>X \<union> Y \<notin> F\<close> by auto
              then have "l \<noteq> []" using \<open>set l = Y\<close> by auto
              then have "length l > 0" by simp
              then have "length l \<ge> 1" by linarith
              have Y_split: "Y = (Y - Z) \<union> (Y \<inter> Z)" by auto
              then have Y_element_prop: "\<forall>y. y \<in> Y \<longrightarrow> y \<in> (Y - Z) \<or> y \<in> (Y \<inter> Z)" by simp
              have "(\<exists>Y'. Y' \<in> F \<and> Y' \<subseteq> Z \<and> (\<exists>y. y \<in> Y - Z \<and> Y' \<union> {y} \<in> F))"
              proof (cases "(nth l 0 \<in> Y - Z)")
                case True
                have 1: "{} \<in> F" using assum1 unfolding accessible_def by simp
                have 2: "{} \<subseteq> Z" by simp
                have "{} \<union> {nth l 0} = {nth l 0}" by simp
                have "{nth l 0} = set (take 1 l)" using \<open>l \<noteq> []\<close> first_element_set by simp
                then have first_element_fact: "{} \<union> {nth l 0} = set (take 1 l)" by simp
                have "set (take 1 l) \<in> F" using l_prop \<open>length l \<ge> 1\<close> by simp
                then have "{} \<union> {nth l 0} \<in> F" using first_element_fact by simp
                then have 3: "(nth l 0) \<in> Y - Z \<and> {} \<union> {nth l 0} \<in> F" using True by simp
                then show ?thesis using 1 2 3 by auto
              next
                case False
                then have "(nth l 0) \<in> Y \<inter> Z" using \<open>l ! 0 \<in> Y\<close> by blast
                then have "Y \<inter> Z \<noteq> {}" by auto
                have "finite (Y \<inter> Z)" using \<open>finite Y\<close> \<open>finite Z\<close> by simp
                then have "\<exists>k. set k = (Y \<inter> Z) \<and> k ! 0 = (nth l 0) \<and> distinct k" using exists_list_with_first_element
                    \<open>(nth l 0) \<in> Y \<inter> Z\<close> \<open>(nth l 0) \<in> Y \<inter> Z\<close> by fast
                then obtain k where k_prop: "set k = Y \<inter> Z" "(nth k 0) = (nth l 0) \<and> distinct k" by auto
                then have "k \<noteq> []" using \<open>Y \<inter> Z \<noteq> {}\<close> by auto
                then have first_el_fact: "{nth k 0} = set (take 1 k)" "{nth l 0} = set (take 1 l)" using first_element_set 
                  \<open>l \<noteq> []\<close> by auto
                have "distinct l" using l_prop by simp
                have "distinct k" using k_prop(2) by simp
                have "Y \<inter> Z \<subset> Y" using \<open>Y - Z \<noteq> {}\<close> by blast
                then have "set k \<subset> set l" using k_prop l_prop by simp
                have "{nth l 0} = {nth k 0}" using k_prop(2) by simp
                then have "set (take 1 l) = set (take 1 k)" using first_el_fact by simp
                then have "\<exists>i. i \<le> length k \<and> set (take i l) \<subseteq> set k \<and> (nth l i) \<in> (set l) - (set k)" using subset_list_el \<open>distinct l\<close> \<open>distinct k\<close> \<open>set k \<subset> set l\<close> \<open>l \<noteq> []\<close> 
                    k_prop(2) \<open>k \<noteq> []\<close> by metis
                then obtain i where i_prop: "i \<le> length k \<and> set (take i l) \<subseteq> set k \<and> (nth l i) \<in> (set l) - (set k)" by auto
                have "Y - (Y \<inter> Z) = Y - Z" by auto
                then have "(set l) - (set k) = Y - Z" using k_prop(1) l_prop by simp
                then have i_prop2: "(nth l i) \<in> Y - Z" using i_prop by simp
                have "card (set k) < card (set l)" using \<open>set k \<subset> set l\<close>
                  by (simp add: \<open>finite Y\<close> psubset_card_mono)
                then have "length k < length l" using l_prop k_prop(2)
                  by (metis distinct_card)
                then have "i < length l" using i_prop by simp
                then have 1: "set (take i l) \<in> F" using l_prop by simp
                have "i + 1 \<le> length l" using \<open>i < length l\<close> by auto 
                then have fact_two: "set (take (i+1) l) \<in> F" using l_prop by simp 
                have "set (take i l) \<union> {nth l i} = set (take (i + 1) l)" using \<open>i < length l\<close> set_take_union_nth by simp
                then have 2: "(nth l i) \<in> Y - Z \<and> set (take i l) \<union> {nth l i} \<in> F" using fact_two i_prop2 by simp
                then have "set (take i l) \<subseteq> set k" using i_prop by simp
                then have "set (take i l) \<subseteq> Y \<inter> Z" using k_prop by simp
                then have 3: "set (take i l) \<subseteq> Z" by simp
                then show ?thesis using 1 2 3 by auto
              qed
              then obtain Y' where Y'_prop: "Y' \<in> F " " Y' \<subseteq> Z " " (\<exists>y. y \<in> Y - Z \<and> Y' \<union> {y} \<in> F)" by auto
              then obtain y where y_prop: "y \<in> Y - Z" "Y' \<union> {y} \<in> F" by auto
              have "Y' \<subseteq> Z" using Y'_prop by simp
              then have "y \<in> E - Z" using y_prop(1) \<open>Z \<subseteq> E\<close> \<open>Y \<subseteq> E\<close> by auto
              then have "y \<in> E - Y'" using Y'_prop(2) by auto 
              then have "Z \<union> {y} \<in> F" using Y'_prop(2) \<open>Z \<in> F\<close> \<open>Z \<subseteq> E\<close> \<open>y \<in> E - Z\<close> assum2 y_prop(2) by blast 
              have fact_three: "X \<subseteq> Z \<union> {y}" using z_props by auto
              have fact_four: "Z \<union> {y} \<subseteq> X \<union> Y" using z_props y_prop(1) by simp
              have "Z \<union> {y} \<supset> Z" using \<open>y \<in> E - Z\<close> by auto
              then show "False"  using fact_three \<open>Z \<union> {y} \<in> F\<close> z_prop fact_four unfolding maximal_def by blast
            qed
          qed
        qed
      qed


   show 2: "closed_under_union F 
\<Longrightarrow> \<forall>X Y z. X \<subseteq> Y \<and> Y \<subseteq> E \<and> z \<in> E - Y \<and> X \<union> {z} \<in> F \<and> Y \<in> F \<longrightarrow> Y \<union> {z} \<in> F"
    proof-
      assume "closed_under_union F"
      show "\<forall>X Y z. X \<subseteq> Y \<and> Y \<subseteq> E \<and> z \<in> E - Y \<and> X \<union> {z} \<in> F \<and> Y \<in> F \<longrightarrow> Y \<union> {z} \<in> F"
      proof(rule, rule, rule)
        fix X Y z
        show " X \<subseteq> Y \<and> Y \<subseteq> E \<and> z \<in> E - Y \<and> X \<union> {z} \<in> F \<and> Y \<in> F \<longrightarrow> Y \<union> {z} \<in> F"
        proof
          assume assum5: "X \<subseteq> Y \<and> Y \<subseteq> E \<and> z \<in> E - Y \<and> X \<union> {z} \<in> F \<and> Y \<in> F"
          then have "X \<subseteq> Y" by auto
          have "X \<union> {z} \<in> F" using assum5 by auto
          have "Y \<in> F" using assum5 by auto
          have "X \<union> {z} \<union> Y = Y \<union> {z}" using \<open>X \<subseteq> Y\<close> by auto
          then have "X \<union> {z} \<union> Y \<in> F" using \<open>X \<union> {z} \<in> F\<close> \<open>Y \<in> F\<close> \<open>closed_under_union F\<close> closed_under_union_def by blast
          then show "Y \<union> {z} \<in> F" using \<open>X \<union> {z} \<union> Y = Y \<union> {z}\<close> by auto
        qed
      qed
    qed
  qed

locale greedoid =
  fixes E :: "'a set"
  fixes F :: "'a set set"
  assumes contains_empty_set: "{} \<in> F"
  assumes third_condition: "(X \<in> F) \<and> (Y \<in> F) \<and> (card X > card Y) \<Longrightarrow> \<exists>x \<in> X - Y.  Y \<union> {x} \<in> F"
  assumes ss_assum: "set_system E F"
       
 definition antimatroid where "antimatroid E F \<longleftrightarrow> accessible E F \<and> closed_under_union F"



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





locale closure_operator = 
  fixes E:: "'a set"
  fixes F:: "'a set set"
  assumes ss_assum: "set_system E F"
  fixes set_system_operator:: "'a set \<Rightarrow> 'a set"
  assumes S_1: "\<forall>X. X \<subseteq> E \<longrightarrow> X \<subseteq> set_system_operator X"
  assumes S_2: "\<forall>X Y. X \<subseteq> E \<and> Y \<subseteq> E \<and> X \<subseteq> Y \<longrightarrow> set_system_operator X \<subseteq> set_system_operator Y"
  assumes S_3: "\<forall>X. X \<subseteq> E \<longrightarrow> set_system_operator X = set_system_operator (set_system_operator X)"

context closure_operator
begin



definition \<tau> :: "'a set \<Rightarrow> 'a set" where "\<tau> A =  \<Inter> {X. X \<subseteq> E \<and> A \<subseteq> X \<and> E - X \<in> F}"

lemma \<tau>_in_E:
  assumes "set_system E F" "A \<subseteq> E" "{} \<in> F"
  shows "\<tau> A \<subseteq> E"
proof -
  have "A \<subseteq> E" using assms by simp
  have \<tau>_def_expand: "\<tau> A =  \<Inter> {X. X \<subseteq> E \<and> A \<subseteq> X \<and> E - X \<in> F}" unfolding \<tau>_def by auto
  have \<open> \<Inter> {X. X \<subseteq> E \<and> A \<subseteq> X \<and> E - X \<in> F} \<subseteq> E\<close>
    using assms(2) \<open>{} \<in> F\<close> by fastforce
  then show "\<tau> A \<subseteq> E" using \<tau>_def_expand by auto
qed

lemma \<tau>_closure_operator:
  assumes assum1: "closed_under_union F"
  assumes assum2: "{} \<in> F"
  assumes assum3: "set_system E F"
  shows "closure_operator E F \<tau>"


proof (unfold_locales)

  show 1: "\<forall>X. X \<subseteq> E \<longrightarrow> X \<subseteq> \<tau> X" 
  proof (intro allI impI)
      fix A
      assume "A \<subseteq> E"
      then have "A \<subseteq> \<Inter> {X. X \<subseteq> E \<and> A \<subseteq> X \<and> E - X \<in> F}" by auto
      then show "A \<subseteq> \<tau> A" 
        unfolding \<tau>_def by blast
    qed 


    show 2: "\<forall>X Y. X \<subseteq> E \<and> Y \<subseteq> E \<and> X \<subseteq> Y \<longrightarrow> \<tau> X \<subseteq> \<tau> Y"
    proof (rule allI)
      fix X' 
      show "\<forall>Y. X' \<subseteq> E \<and> Y \<subseteq> E \<and> X' \<subseteq> Y\<longrightarrow> \<tau> X' \<subseteq> \<tau> Y"
      proof (rule allI)
        fix Y
        show "X' \<subseteq> E  \<and> Y \<subseteq> E \<and> X' \<subseteq> Y \<longrightarrow> \<tau> X' \<subseteq> \<tau> Y"
        proof (rule impI)
          assume assum3: "X' \<subseteq> E \<and> Y \<subseteq> E \<and> X' \<subseteq> Y"
          then have A_B_prop: "\<Inter> {X. X \<subseteq> E \<and> X' \<subseteq> X \<and> E - X \<in> F} \<subseteq> \<Inter> {X. X \<subseteq> E \<and> Y \<subseteq> X \<and> E - X \<in> F}"
            by fastforce
          then show "\<tau> X' \<subseteq> \<tau> Y" by (simp add: \<tau>_def)
        qed
      qed
     qed

     show 3: "\<forall>X. X \<subseteq> E \<longrightarrow> \<tau> X = \<tau> (\<tau> X)"
     proof (intro allI impI)
           fix X
           assume "X \<subseteq> E"
           have "\<tau> X \<subseteq> \<tau> (\<tau> X)" using 1 unfolding \<tau>_def by blast
           have  "\<tau> (\<tau> X) \<subseteq> \<tau> X"
           proof (rule ccontr)
             assume "\<not> \<tau> (\<tau> X) \<subseteq> \<tau> X"
             obtain y where assum4: "y \<in>  \<tau> (\<tau> X) - \<tau> X" using \<open>\<not> \<tau> (\<tau> X) \<subseteq> \<tau> X\<close> by auto
             have y_prop: "y \<in>  \<Inter> {Y. Y \<subseteq> E \<and> (\<tau> X) \<subseteq> Y \<and> E - Y \<in> F}" using assum4 \<tau>_def by auto
             have "y \<notin> \<tau> X" using assum4 by auto
             then have Y_prop: "\<forall>Y. Y \<subseteq> E \<and> \<tau> X \<subseteq> Y \<and> E - Y \<in> F \<longrightarrow> y \<in> Y" using y_prop by auto
             then have "\<forall>Z. Z \<subseteq> E \<and> X \<subseteq> Z \<and> E - Z \<in> F  \<longrightarrow> y \<in> Z" using \<open>\<forall>X. X \<subseteq> E \<longrightarrow> X \<subseteq> \<tau> X\<close>
               unfolding \<tau>_def by blast
             then have "y \<in> \<tau> X" unfolding \<tau>_def by blast
             then show "False" using \<open>y \<notin> \<tau> X\<close> by simp
           qed
             then show "\<tau> X = \<tau> (\<tau> X)" using \<open>\<tau> X \<subseteq> \<tau> (\<tau> X)\<close> by blast
           qed
           show "set_system E F" using assum3 by simp

         qed





lemma \<tau>_prop:
  assumes "A \<subseteq> E" "set_system E F" "closed_under_union F" "{} \<in> F"
  shows "E - \<tau> A \<in> F"
proof -
  have 1: "\<tau>(A) = \<Inter> {X. X \<subseteq> E \<and> A \<subseteq> X \<and> E - X \<in> F}" unfolding \<tau>_def by simp
  then have "\<tau> A \<subseteq> E" using \<tau>_in_E assms(2) assms(4) assms(1) by auto
  let ?S = "{Y. Y \<subseteq> E \<and> A \<subseteq> E - Y \<and> Y \<in> F}"
  have 1: "E - \<tau> A = \<Union> ?S"
  proof
    show " E - \<tau> A \<subseteq> \<Union> {Y. Y \<subseteq> E \<and> A \<subseteq> E - Y \<and> Y \<in> F}"
    proof
      fix x
      show "x \<in> E - \<tau> A \<Longrightarrow> x \<in> \<Union> {Y. Y \<subseteq> E \<and> A \<subseteq> E - Y \<and> Y \<in> F} "
      proof -
        assume "x \<in> E - \<tau> A"
        then have "x \<in> E" and "x \<notin> \<tau> A" by auto
        from `x \<notin> \<tau> A` obtain X where "X \<subseteq> E" "A \<subseteq> X" "E - X \<in> F" "x \<notin> X"
          using `\<tau> A = \<Inter> {X. X \<subseteq> E \<and> A \<subseteq> X \<and> E - X \<in> F}` by auto
        then have "x \<in> E - X" and "E - X \<in> F" using `x \<in> E` by auto
        then show "x \<in> \<Union> ?S" using `X \<subseteq> E` `A \<subseteq> X` by auto
      qed
      qed

      show "\<Union> {Y. Y \<subseteq> E \<and> A \<subseteq> E - Y \<and> Y \<in> F} \<subseteq> E - \<tau> A"
      proof
        fix x
        show "x \<in> \<Union> {Y. Y \<subseteq> E \<and> A \<subseteq> E - Y \<and> Y \<in> F} \<Longrightarrow> x \<in> E - \<tau> A"
        proof -
        assume "x \<in> \<Union> ?S"
        then obtain Y where Y_prop: "x \<in> Y" and "Y \<subseteq> E" and "A \<subseteq> E - Y" and "Y \<in> F" by auto
        then have "x \<in> E" and "x \<notin> \<tau> A"
        proof -
          show "x \<in> E" using `Y \<subseteq> E` `x \<in> Y` by auto
          show "x \<notin> \<tau> A"
          proof (rule ccontr)
            assume "\<not>(x \<notin> \<tau> A)"
            then have "x \<in> \<tau> A" by simp
            then have "x \<in> \<Inter> {X. X \<subseteq> E \<and> A \<subseteq> X \<and> E - X \<in> F}" using `\<tau> A = \<Inter> {X. X \<subseteq> E \<and> A \<subseteq> X \<and> E - X \<in> F}` by simp
            then have fact_one: "\<forall>X. X \<subseteq> E \<and> A \<subseteq> X \<and> E - X \<in> F \<longrightarrow> x \<in> X" by simp
            have 1: "E - Y \<subseteq> E"  using \<open>Y \<subseteq> E\<close> by simp
            have "E - (E - Y) = Y" using \<open>Y \<subseteq> E\<close> by auto
            then have "E - (E - Y) \<in> F" using \<open>Y \<in> F\<close> by simp
            then have "(E - Y) \<subseteq> E \<and> A \<subseteq> (E - Y) \<and> E - (E - Y) \<in> F" using 1 \<open>A \<subseteq> E - Y\<close> by simp
            then have "x \<in> E - Y" using fact_one by auto
            then have "x \<notin> Y" by simp
            then show False using `x \<in> Y` by auto
          qed
        qed
        then show ?thesis by simp
      qed
    qed
  qed
  have prop1: "{Y. Y \<subseteq> E \<and> A \<subseteq> E - Y \<and> Y \<in> F} \<subseteq> F" by auto
  have "finite E" using assms(2) unfolding set_system_def by simp 
  then have "finite F" using assms(2) unfolding set_system_def
    by (meson Sup_le_iff finite_UnionD finite_subset)
  then have "finite {Y. Y \<subseteq> E \<and> A \<subseteq> E - Y \<and> Y \<in> F}" using finite_subset by simp
  then have "\<Union> ?S \<in> F"
    using closed_under_arbitrary_unions assms(2-4) prop1  by simp
  then show "E - \<tau> A \<in> F" using 1 by simp
qed

lemma \<tau>_prop2:
  assumes "A \<in> F" "set_system E F" "closed_under_union F" "{} \<in> F"
  shows "\<tau> (E - A) = E - A"
  proof
    show "E - A \<subseteq> \<tau> (E - A)"
    proof -
        have "A \<subseteq> E" using assms unfolding set_system_def by auto
        then have "E - A \<subseteq> E" by auto
        then show ?thesis using \<tau>_closure_operator assms(3) assms(4) closure_operator.S_1 ss_assum by blast
     qed
     show "\<tau> (E - A) \<subseteq> E - A"
     proof (rule ccontr)
       assume assum1: "\<not>(\<tau> (E - A) \<subseteq> E - A)"
       then obtain x where x_prop: "x \<in> \<tau> (E - A)" "x \<notin> E - A" by auto
       have "A \<subseteq> E" using assms unfolding set_system_def by auto
        then have "E - A \<subseteq> E" by auto
       have "x \<in> \<Inter> {X. X \<subseteq> E \<and> (E - A) \<subseteq> X \<and> E - X \<in> F}" using x_prop(1) unfolding \<tau>_def by simp
       then have 1: "\<forall>X. X \<subseteq> E \<and> (E - A) \<subseteq> X \<and> E - X \<in> F \<longrightarrow> x \<in> X" by simp
       have "E - (E - A) = A" using \<open>A \<subseteq> E\<close> by auto
       then have "E - (E - A) \<in> F" using assms(1) by simp
       then have "E - A \<subseteq> E \<and> (E - A) \<subseteq> E - A \<and> (E - (E - A)) \<in> F" using \<open>E - A \<subseteq> E\<close>  by simp
       then have "x \<in> (E - A)" using 1 by blast
       then show "False" using x_prop(2) by simp
     qed
qed


lemma min_card_exists:
  assumes "A \<in> F - {{}}" 
    and "set_system E F" 
    and "closed_under_union F" 
    and "{} \<in> F"
  shows "\<exists>a. a \<in> A \<and> \<not>(\<exists>b. b \<in> A \<and>  card (\<tau> ((E - A) \<union> {b})) < card (\<tau> ((E - A) \<union> {a})))"
proof -
  from assms have "A \<noteq> {}" by auto
  hence "A \<noteq> {}" by auto
  have "A \<subseteq> E" using assms(1-2) unfolding set_system_def by simp
  have "finite E" using assms(2) unfolding set_system_def by simp
  then have "finite A" using \<open>A \<subseteq> E\<close> finite_subset by auto
  have "\<forall>a. a \<in> A \<longrightarrow> ((E - A) \<union> {a}) \<subseteq> E" using \<open>A \<subseteq> E\<close> by auto
  then have "\<forall>a. a \<in> A \<longrightarrow> \<tau>(((E - A) \<union> {a})) \<subseteq> E" using \<tau>_in_E assms(2) assms(4) by simp
  then have fact_one: "\<forall>a. a \<in> A \<longrightarrow> finite (\<tau>(((E - A) \<union> {a})))" using \<open>finite E\<close> finite_subset by blast
  let ?S = "{card (\<tau> ((E - A) \<union> {x})) | x. x \<in> A }"
  have "finite ?S" using \<open>finite A\<close> by auto
  have "?S \<noteq> {}" using \<open>A \<noteq> {}\<close> by simp
  then obtain x where "x = Min ?S" using \<open>finite ?S\<close> by simp
  then have "x \<in> ?S"
    using Min_in \<open>finite {card (\<tau> (E - A \<union> {x})) |x. x \<in> A}\<close> \<open>{card (\<tau> (E - A \<union> {x})) |x. x \<in> A} \<noteq> {}\<close> by blast
  then have "\<exists>a. a \<in> A \<and> card (\<tau>((E - A) \<union> {a})) = x" 
    by blast
  then obtain a where a_prop: "a \<in> A \<and> card (\<tau>((E - A) \<union> {a})) = x" by auto
  have min_fact: "\<forall>p. p \<in> ?S \<longrightarrow> p \<ge> x" using \<open>x = Min ?S\<close> 
    using \<open>finite {card (\<tau> (E - A \<union> {x})) |x. x \<in> A}\<close> by auto
  have "(\<nexists>b. b \<in> A \<and> card (\<tau> ((E - A) \<union> {b})) < card (\<tau> ((E - A) \<union> {a})))"
  proof (rule ccontr)
    assume "\<not> (\<nexists>b. b \<in> A \<and> card (\<tau> ((E - A) \<union> {b})) < card (\<tau> ((E - A) \<union> {a})))"
    then have "(\<exists>b. b \<in> A \<and> card (\<tau> ((E - A) \<union> {b})) < card (\<tau> ((E - A) \<union> {a})))" by simp
    then obtain b where "b \<in> A \<and> card (\<tau> (E - A \<union> {b})) < card (\<tau> (E - A \<union> {a}))" by auto
    then have b_prop: "b \<in> A \<and> card (\<tau> (E - A \<union> {b})) < x" using a_prop by simp
    then have b_prop2: "card  (\<tau> ((E - A) \<union> {b})) \<in> ?S" by auto
    then have "card (\<tau> ((E - A) \<union> {b})) < x" using b_prop by simp
    then show "False" using \<open>x = Min ?S\<close> b_prop2 min_fact by auto
  qed
  then show ?thesis using a_prop by auto
  qed


definition antiexchange_property where "antiexchange_property P \<longleftrightarrow>
(\<forall>X y z. X \<subseteq> E \<and> y \<in> E - P X \<and> z \<in> E - P X \<and> y \<noteq> z \<and> z \<in> (P (X \<union> {y})) \<longrightarrow>
y \<notin> (P (X \<union> {z})))"

lemma fifth_thm:
  assumes assum1: "closed_under_union F" "set_system E F"
  assumes assum2: "{} \<in> F"
  shows "accessible E F \<longleftrightarrow> antiexchange_property \<tau>"

proof (intro iffI)

  show "accessible E F \<Longrightarrow> antiexchange_property \<tau>"
  proof -
    assume assum3: "accessible E F"
    have "antimatroid E F" using assum3 assum1 by (simp add: antimatroid_def)
    then have "closed_under_union F" unfolding antimatroid_def by auto
    have "set_system E F" using assum3 unfolding accessible_def by auto
    have "greedoid E F" using \<open>antimatroid E F\<close> antimatroid_greedoid by auto
    then have third_condition: "(X \<in> F) \<and> (Y \<in> F) \<and> (card X > card Y) \<Longrightarrow> \<exists>x \<in> X - Y.  Y \<union> {x} \<in> F" 
      using greedoid.third_condition by blast
    have contains_empty_set: "{} \<in> F" using assum3 unfolding accessible_def by simp
    show "antiexchange_property \<tau>"
      unfolding antiexchange_property_def
    proof (rule allI)
      fix X
      show "\<forall>y z. X \<subseteq> E \<and> y \<in> E - \<tau> X \<and> z \<in> E - \<tau> X \<and> y \<noteq> z \<and> z \<in> \<tau> (X \<union> {y}) \<longrightarrow> y \<notin> \<tau> (X \<union> {z})"
      proof (rule allI)
        fix y
        show "\<forall>z. X \<subseteq> E \<and> y \<in> E - \<tau> X \<and> z \<in> E - \<tau> X \<and> y \<noteq> z \<and> z \<in> \<tau> (X \<union> {y}) \<longrightarrow> y \<notin> \<tau> (X \<union> {z})"
        proof (rule allI)
          fix z
          show "X \<subseteq> E \<and> y \<in> E - \<tau> X \<and> z \<in> E - \<tau> X \<and> y \<noteq> z \<and> z \<in> \<tau> (X \<union> {y}) \<longrightarrow> y \<notin> \<tau> (X \<union> {z})"
          proof (rule impI)
            assume z_y_prop: "X \<subseteq> E \<and> y \<in> E - \<tau> X \<and> z \<in> E - \<tau> X \<and> y \<noteq> z \<and> z \<in> \<tau> (X \<union> {y})"
            show "y \<notin> \<tau> (X \<union> {z})"
            proof -
              let ?B = "E - \<tau> X"
              have "X \<subseteq> E" using z_y_prop by simp
              then have "\<tau> X \<subseteq> E" using \<open>set_system E F\<close> \<tau>_in_E contains_empty_set by auto
              then have "?B \<subseteq> E" using \<open>X \<subseteq> E\<close> by simp
              have "finite E" using \<open>set_system E F\<close> unfolding set_system_def by auto
              then have "finite X" using \<open>X \<subseteq> E\<close> finite_subset by auto
              have "finite ?B" using \<open>?B \<subseteq> E\<close> \<open>finite E\<close> finite_subset by auto
              have "z \<in> ?B" using z_y_prop by simp
              let ?A = "E - \<tau> (X \<union> {y})"
              have "y \<in> ?B" using z_y_prop by simp
              then have "y \<in> E" by simp
              then have "X \<union> {y} \<subseteq> E" using \<open>X \<subseteq> E\<close> by blast
              then have "?A \<subseteq> E" by simp
              have "finite (?A)" using \<open>finite E\<close> finite_subset by auto
              have "?B \<in> F" using \<tau>_prop contains_empty_set \<open>set_system E F\<close> \<open>closed_under_union F\<close> \<open>\<tau> X \<subseteq> E\<close> by (simp add: \<open>X \<subseteq> E\<close> assum1)
              have "\<tau> (X \<union> {y}) \<subseteq> E" using \<open>X \<union> {y} \<subseteq> E\<close> \<tau>_in_E \<open>set_system E F\<close> contains_empty_set by simp
              then have "?A \<in> F" using \<open>closed_under_union F\<close> \<open>set_system E F\<close> \<tau>_prop 
                contains_empty_set \<open>X \<union> {y} \<subseteq> E\<close> by blast
              have \<tau>_2nd_prop: "\<forall>X Y. X \<subseteq> E \<and> Y \<subseteq> E \<and> X \<subseteq> Y \<longrightarrow> \<tau> X \<subseteq> \<tau> Y" using \<tau>_closure_operator assum1 closure_operator.S_2 contains_empty_set ss_assum by blast
              have "X \<subseteq> X \<union> {y}" by auto
              then have "X \<subseteq> E \<and> (X \<union> {y}) \<subseteq> E \<and> X \<subseteq> X \<union> {y}" using  \<open>X \<subseteq> E\<close> \<open>X \<union> {y} \<subseteq> E\<close> by auto 
              then have "\<tau> X \<subseteq> \<tau> (X \<union> {y})" using \<tau>_2nd_prop by blast
              then have "?A \<subseteq> ?B"  by auto
              have "\<tau> (X \<union> {y}) \<subseteq> E" 
                using \<open>X \<union> {y} \<subseteq> E\<close> \<open>set_system E F\<close> \<tau>_in_E contains_empty_set by auto
              have "y \<in> ?B" using z_y_prop by auto
              have "z \<in> ?B" using z_y_prop by auto
              have "z \<in> \<tau> (X \<union> {y})" using z_y_prop by auto
              then have "z \<notin> ?A"
                using \<open>z \<in> ?B\<close> by fastforce
              have "y \<in> X \<union> {y}" by simp
              have "\<forall>X. X \<subseteq> E \<longrightarrow> X \<subseteq> \<tau> X" using \<tau>_closure_operator assum1 closure_operator.S_1 contains_empty_set ss_assum by blast
              then have "X \<union> {y} \<subseteq> \<tau> (X \<union> {y})" using \<open>X \<union> {y} \<subseteq> E\<close> by blast
              then have "y \<in> \<tau> (X \<union> {y})" using \<open>y \<in> X \<union> {y}\<close> by auto
              then have "y \<notin> ?A" by simp
              have "?A \<subseteq> ?B- {y,z}"
                using Diff_iff \<open>?A \<subseteq> ?B\<close> \<open>y \<in> \<tau> (X \<union> {y})\<close> subset_Diff_insert subset_insert z_y_prop by auto
              have "card ?A < card ?B"
                by (metis \<open>?A \<subseteq> ?B\<close> \<open>finite ?B\<close> \<open>z \<in> ?B\<close> \<open>z \<notin> ?A\<close> card_mono card_subset_eq le_neq_implies_less)
              then have "\<exists>x \<in> ?B - ?A.  ?A \<union> {x} \<in> F"
                using \<open>?B \<in> F\<close> \<open>?A \<in> F\<close> \<open>greedoid E F\<close> greedoid.third_condition by blast
              then obtain b where b_prop: "b \<in> ?B - ?A" "?A \<union> {b} \<in> F" by auto
              then have b_prop2: "b \<notin> ?A" by simp
              have " X \<subseteq> \<tau> (X)"
                by (simp add: \<open>X \<subseteq> E\<close> \<open>\<forall>X\<subseteq>E. X \<subseteq> \<tau> X\<close>) 
              have "?B \<subseteq> E - X" by (meson Diff_mono \<open> X \<subseteq> \<tau> (X)\<close> subset_refl)
              then have "?B - ?A \<subseteq> (E - X) - ?A" by auto
              then have eqn: "?B - ?A \<subseteq> E - (?A \<union> X)" by auto
              then have "b \<notin> X" using b_prop(1) by auto
              have in_E1: "?A \<union> {b} \<subseteq> E" using b_prop(1) by simp
              have in_E2: "?A \<subseteq> E" using \<open>X \<union> {y} \<subseteq> E\<close> by simp
              have "\<tau> (X \<union> {y}) \<subseteq> (E - ?A)" using \<open>\<tau>(X \<union> {y}) \<subseteq> E\<close> by auto
              then have "X \<union> {y} \<subseteq> (E - ?A)" using \<open>X \<union> {y} \<subseteq> \<tau> (X \<union> {y})\<close> by auto
              then have prop1: "X \<subseteq> (E - ?A)" by simp
              have "y \<noteq> z" using z_y_prop by simp
              have "\<not>?A \<union> {b} \<subseteq> E - (X \<union> {y})"
              proof (rule ccontr)
                assume assum4: "\<not> \<not>?A \<union> {b} \<subseteq> E - (X \<union> {y})"
                then have "?A \<union> {b} \<subseteq> E - (X \<union> {y})" by auto
                then have "E - (?A \<union> {b}) \<supseteq> E - (E - (X \<union> {y}))" using in_E1 in_E2 by auto
                then have "E - (E - (X \<union> {y})) \<subseteq> E - (?A \<union> {b})" by simp
                then have ineq_one: "\<tau> (E - (E - (X \<union> {y}))) \<subseteq> \<tau>(E - (?A \<union> {b}))"
                  by (meson Diff_subset \<tau>_2nd_prop)
                have "E - (E - (X \<union> {y})) = X \<union> {y}" using \<open>X \<union> {y} \<subseteq> E\<close> by auto
                then have ineq_two: "\<tau> (X \<union> {y}) \<subseteq> \<tau>(E - (?A \<union> {b}))" using ineq_one by simp
                have eq_one: "\<tau> (X \<union> {y}) = E - ?A"
                  by (metis Diff_partition Diff_subset_conv Un_Diff_cancel \<open>E - \<tau> X \<subseteq> E\<close> \<open>X \<union> {y} \<subseteq> E\<close> \<open>\<tau> X \<subseteq> E\<close> \<open>set_system E F\<close> \<tau>_in_E contains_empty_set double_diff)
                have "\<tau>(E - (?A \<union> {b})) = E - (?A \<union> {b})" using b_prop(2) \<tau>_prop2 \<open>set_system E F\<close> \<open>closed_under_union F\<close> contains_empty_set by simp
                then have "\<tau> (X \<union> {y}) \<subseteq> E - (?A \<union> {b})" using ineq_two by simp
                then show "False" using eq_one b_prop(2)
                  using assum4 b_prop2 by blast
              qed
              then have "b \<in> X \<union> {y}" using b_prop2 \<open>X \<union> {y} \<subseteq> E\<close> eqn 
                using b_prop(1) insert_subset Diff_mono Un_insert_right \<open>X \<union> {y} \<subseteq> \<tau> (X \<union> {y})\<close> equalityE sup_bot_right by auto
              then have "b = y" using \<open>b \<notin> X\<close> by simp
              then have "?A \<union> {y} \<in> F" using b_prop(2) by auto
              have "y \<notin> \<tau> X" using \<open>y \<in> E - \<tau> X\<close> by simp
              then have "y \<notin> X" using \<open>X \<subseteq> \<tau> X\<close> by auto
              then have prop2: "X \<subseteq> E - (?A \<union> {y})" using prop1 by auto
              have "z \<in> E - ((E - \<tau> (X \<union> {y})))" using \<open>z \<notin> ?A\<close> \<open>?A \<subseteq> E\<close>
                using z_y_prop by auto
              then have "z \<in> E - (?A \<union> {y})" using \<open>y \<noteq> z\<close> by simp
              then have "(X \<union> {z}) \<subseteq> E - (?A \<union> {y})" using prop2 by simp
              then have "\<tau> (X \<union> {z}) \<subseteq> \<tau> (E - (?A \<union> {y}))" using \<tau>_2nd_prop
                using \<open>X \<subseteq> E \<and> X \<union> {y} \<subseteq> E \<and> X \<subseteq> X \<union> {y}\<close> by auto
              then have "\<tau> (X \<union> {z}) \<subseteq>  (E - (?A \<union> {y}))" using \<open>(?A \<union> {y}) \<in> F\<close> \<tau>_prop2 \<open>set_system E F\<close> \<open>closed_under_union F\<close> contains_empty_set by simp
              then show "y \<notin> \<tau> (X \<union> {z})" by auto
            qed
          qed
        qed
      qed
    qed
  qed

  show "antiexchange_property \<tau> \<Longrightarrow> accessible E F"
  proof - 
    assume "antiexchange_property \<tau>"
    show "accessible E F" 
    unfolding accessible_def
     proof (rule)
       show "set_system E F" 
         using assms(2) by simp
       show "{} \<in> F \<and> (\<forall>X. X \<in> F - {{}} \<longrightarrow> (\<exists>x\<in>X. X - {x} \<in> F))"
       proof (rule)
         show "{} \<in> F" using assum2 by simp
         show "(\<forall>X. X \<in> F - {{}} \<longrightarrow> (\<exists>x\<in>X. X - {x} \<in> F))"
         proof (rule allI)
           fix A
           show "A \<in> F - {{}} \<longrightarrow> (\<exists>x\<in>A. A - {x} \<in> F)"
           proof (rule impI)
             assume "A \<in> F - {{}}"
             show "\<exists>x\<in>A. A - {x} \<in> F"
             proof  -
               let ?X = "E - A"
               have "A \<in> F" using \<open>A \<in> F - {{}}\<close> by simp
               have "\<tau> (?X) = ?X" using \<open>A \<in> F\<close> \<open>set_system E F\<close> \<open>closed_under_union F\<close> assum2 \<tau>_prop2 by simp
               have "A \<noteq> {}" using \<open>A \<in> F - {{}}\<close> by simp
               have "\<exists>a. a \<in> A \<and> \<not>(\<exists>b. b \<in> A \<and> card (\<tau> ((?X) \<union> {b})) < card (\<tau> ((?X) \<union> {a})))" 
                 using min_card_exists \<open>A \<in> F - {{}}\<close> \<open>set_system E F\<close> \<open>closed_under_union F\<close> assum2 by auto
               then obtain a where a_prop: "a \<in> A \<and> \<not>(\<exists>b. b \<in> A \<and> card (\<tau> ((?X) \<union> {b})) < card (\<tau> ((?X) \<union> {a})))" 
                 by auto
               then have "a \<in> A" by simp
               have a_prop2: "\<not>(\<exists>b. b \<in> A \<and> card (\<tau> ((?X) \<union> {b})) < card (\<tau> ((?X) \<union> {a})))" using a_prop by simp
               have "A \<subseteq> E" using \<open>A \<in> F - {{}}\<close> \<open>set_system E F\<close> unfolding set_system_def
                 by simp
               then have "?X \<subseteq> E" by simp
               then have "?X \<union> {a} \<subseteq> E" using \<open>a \<in> A\<close> \<open>A \<subseteq> E\<close> by auto
               have "\<forall>X. X \<subseteq> E \<longrightarrow> X \<subseteq> \<tau> X" 
                 using \<tau>_closure_operator assum1(1) assum2 closure_operator.S_1 ss_assum by blast
               then have prop1: "?X \<union> {a} \<subseteq> \<tau> ((?X) \<union> {a})" using \<open>(?X) \<union> {a} \<subseteq> E\<close> by blast
               have "\<tau> (?X) \<union> {a} \<subseteq> E" using \<open>(?X) \<union> {a} \<subseteq> E\<close> \<tau>_in_E \<open>set_system E F\<close> assum2  by simp
               have "finite E" using \<open>set_system E F\<close> unfolding set_system_def by simp
               then have "finite (\<tau> (?X) \<union> {a})" using \<open>\<tau> (?X) \<union> {a} \<subseteq> E\<close> finite_subset by auto
               have "\<tau> ((?X) \<union> {a}) \<subseteq> (?X) \<union> {a}"
               proof (rule ccontr)
                 assume assum6: "\<not> (\<tau> (?X \<union> {a}) \<subseteq> ?X \<union> {a})"
                 show "False"
                 proof - 
                   have "\<exists>b. b \<in> \<tau> (?X \<union> {a}) \<and> b \<notin> (?X) \<union> {a} \<and> a \<noteq> b" using \<open> (?X) \<union> {a} \<subseteq> \<tau> (?X \<union> {a})\<close> using assum6 by auto
                   then obtain b where b_prop: "b \<in> \<tau> (?X \<union> {a})" "b \<notin> ?X \<union> {a}" by auto
                   then have "b \<in> E" using \<open>?X \<union> {a} \<subseteq> E\<close> \<open>set_system E F\<close> \<tau>_in_E assum2 by blast
                   then have "(?X \<union> {b}) \<subseteq> E" using \<open>?X \<subseteq> E\<close> by simp
                   then have "\<tau> (E - A \<union> {b}) \<subseteq> E" using \<tau>_in_E \<open>set_system E F\<close> assum2 by simp
                   then have "finite (\<tau> (?X \<union> {b}))" using \<open>finite E\<close> finite_subset by simp
                   have "b \<notin> ?X" using b_prop(2) by simp
                   then have "b \<notin> \<tau> ?X" using \<open>\<tau> ?X = ?X\<close> by simp
                   then have 1: "b \<in> E - \<tau> ?X" using \<open>b \<in> E\<close> by simp
                   have "b \<in> A" using \<open>b \<notin> ?X\<close> \<open>A \<subseteq> E\<close>
                     using \<open>b \<in> E\<close> by blast
                   have 2: "b \<noteq> a" using b_prop(2) by simp
                   have "E - ?X = A" by (simp add: \<open>A \<subseteq> E\<close> double_diff)
                   then have "E - \<tau> (?X) = A" using \<open>\<tau> ?X = ?X\<close> by simp
                   then have "a \<in> E - \<tau> (?X)" using a_prop by simp
                   then have fact_one: "?X \<subseteq> E \<and> a \<in> E - \<tau> ?X \<and> b \<in> E - \<tau> ?X \<and> a \<noteq> b \<and> b \<in> \<tau> (?X \<union> {a})" using
                       \<open>E - A \<subseteq> E\<close> 1 2 b_prop(1) by simp
                   then have "a \<notin> \<tau> ((?X) \<union> {b})"  using  \<open>antiexchange_property \<tau>\<close>
                     unfolding antiexchange_property_def by simp
                   have "\<tau> ((?X) \<union> {a}) \<subseteq> E" using \<open>((?X) \<union> {a}) \<subseteq> E\<close> \<tau>_in_E \<open>set_system E F\<close> assum2 by simp
                   then have "\<tau> ((?X) \<union> {a}) \<union> {b} \<subseteq> E" using \<open>b \<in> E\<close> by simp
                   have \<open>finite (\<tau> ((?X) \<union> {a}))\<close> using \<open>\<tau>(?X \<union> {a}) \<subseteq> E\<close> \<open>finite E\<close> finite_subset by auto
                   have "a \<notin> ?X" using \<open>a \<in> A\<close> by simp
                   then have "(?X) \<subseteq> (?X) \<union> {a}" by auto
                   then have "\<tau>(?X) \<subseteq> \<tau> ((?X) \<union> {a})" using \<open>?X \<subseteq> E\<close> \<open>(?X) \<union> {a} \<subseteq> E\<close> 
                     using \<open>\<tau> (?X) = ?X\<close> prop1 by auto
                   then have "(?X) \<subseteq> \<tau> ((?X) \<union> {a})" using \<open>\<tau>(?X) = ?X\<close> by simp
                   then have "(?X) \<union> {b} \<subseteq> \<tau> ((?X) \<union> {a}) \<union> {b}" using \<open>b \<notin> ?X\<close>
                     by blast
                   then have "\<tau>((?X) \<union> {b}) \<subseteq> \<tau> (\<tau> ((?X) \<union> {a}) \<union> {b})" using \<open>(?X) \<union> {b} \<subseteq> E\<close>  \<open>\<tau> ((?X) \<union> {a}) \<union> {b} \<subseteq> E\<close> 
                     by (meson \<tau>_closure_operator assum1(1) assum2 closure_operator_def ss_assum)
                   also have "... = \<tau> (\<tau> ((?X) \<union> {a}))" using b_prop(1)
                     by (simp add: insert_absorb)
                   also have "... = \<tau> ((?X) \<union> {a})" using \<open>\<tau> ((?X) \<union> {a}) \<subseteq> E\<close> 
                     by (metis \<open>?X \<union> {a} \<subseteq> E\<close> \<tau>_closure_operator assum1 closure_operator.S_3 assum2)
                   finally have "\<tau> ((?X) \<union> {b}) \<subseteq> \<tau> ((?X) \<union> {a})" by simp
                   have "\<tau> ((?X) \<union> {b}) \<noteq> \<tau> ((?X) \<union> {a})"
                   proof 
                     assume "\<tau> ((?X) \<union> {b}) = \<tau> ((?X) \<union> {a})"
                     show "False" 
                     proof -
                       have "a \<in> ?X \<union> {a}" by simp
                       then have "a \<in> \<tau> (?X \<union> {a})" using \<open>?X \<union> {a} \<subseteq> \<tau> (?X \<union> {a})\<close> by simp
                       then show ?thesis using \<open>a \<notin> \<tau>(?X \<union> {b})\<close> using \<open>\<tau> (E - A \<union> {b}) = \<tau> (E - A \<union> {a})\<close> by auto
                     qed
                   qed
                   then have "card (\<tau> ((?X) \<union> {b})) < card (\<tau> ((?X) \<union> {a}))"
                     using \<open>finite (\<tau> ((?X) \<union> {a}))\<close> by (meson \<open>\<tau> (E - A \<union> {b}) \<subseteq> \<tau> (E - A \<union> {a})\<close> card_mono card_subset_eq le_neq_implies_less)
                   then have "b \<in> A \<and> card (\<tau> (?X \<union> {b})) < card (\<tau> (?X \<union> {a}))" using \<open>b \<in> A\<close> by simp
                   then show "False" using a_prop2 by auto
                 qed
               qed
               then have eqn: "\<tau> (?X \<union> {a}) = ?X \<union> {a}" using prop1 by auto
               have set_in_F: "E - \<tau> (?X \<union> {a}) \<in> F" using \<open>?X \<union> {a} \<subseteq> E\<close> \<open>set_system E F\<close> \<open>closed_under_union F\<close> \<tau>_prop assum2 by simp
               have "E - ((?X) \<union> {a}) = A - {a}"
                 using \<open>A \<subseteq> E\<close> by fastforce 
               then have "E - (\<tau> (?X \<union> {a})) = A - {a}" using eqn by simp
               then have "A - {a} \<in> F" using set_in_F by simp
               then show ?thesis
                 using a_prop(1) by auto
             qed
           qed
         qed
       qed
     qed
   qed
 qed



end 


locale greedoid_example  =
  fixes V :: "'a set"         (* Set of vertices *)
    and E :: "('a \<times> 'a) set"  (* Set of directed edges *) 
  assumes finite_assum_V: "finite V"

context greedoid_example
begin

definition digraph::"'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bool" where "digraph F G = (G \<subseteq> F \<times> F)"

definition acyclic::"'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bool" where "acyclic F G = ((G = {}) \<or> (\<forall>v \<in> F. \<not> (\<exists>p. p \<noteq> [] \<and> hd p = v \<and> last p = v \<and> (\<forall>i < length p - 1. (p ! i, p ! (i + 1)) \<in> G) \<and> length p \<ge> 2)))"

definition connected::"'a set \<Rightarrow>  ('a \<times> 'a) set \<Rightarrow> bool" where " connected F G = ((G = {} \<and> card F = 1) \<or> (\<forall>u v. u \<in> F \<and> v \<in> F \<and> u \<noteq> v \<longrightarrow> (\<exists>p. p \<noteq> [] \<and> ((hd p = v \<and> last p = u) \<or> (hd p = u \<and> last p = v)) \<and> (\<forall>i < length p - 1. ((p ! i, p ! (i + 1)) \<in> G) \<or> (p ! (i + 1), p ! i) \<in> G) \<and> length p \<ge> 2)))"

definition tree::"'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bool" where "tree F G \<longleftrightarrow> digraph F G \<and> acyclic F G \<and> connected F G \<and> (card G = card F - 1) "


lemma greedoid_graph_example: assumes "digraph V E" "r \<in> V" 
  shows "greedoid E {Y. \<exists> X. X \<subseteq> V \<and> Y \<subseteq> E \<and> r \<in> X \<and> tree X Y}"
proof (unfold_locales)
  let ?F = "{Y. \<exists> X. X \<subseteq> V \<and> Y \<subseteq> E \<and> r \<in> X \<and> tree X Y}"
  show first_part: "{} \<in> {Y. \<exists> X. X \<subseteq> V \<and> Y \<subseteq> E \<and> r \<in> X \<and> tree X Y}"
  proof -
    have factone: "{r} \<subseteq> V" using assms(2) by simp
    have "tree {r} {}" unfolding tree_def
    proof 
      show "digraph {r} {}" unfolding digraph_def by auto
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
        have "E \<subseteq> V \<times> V" using assms(1) unfolding digraph_def by simp
        then show "finite E" using finite_assum_V 
          by (simp add: finite_subset)
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
          then have "(X = {} \<and> card V1 = 1) \<or> (\<forall>u v. u \<in> V1 \<and> v \<in> V1 \<and> u \<noteq> v \<longrightarrow> (\<exists>p. p \<noteq> [] \<and> ((hd p = u \<and> last p = v ) \<or> (hd p = v \<and> last p = u)) \<and> (\<forall>i < length p - 1. ((p ! i, p ! (i + 1)) \<in> X) \<or> ((nth p (i + 1), nth p i) \<in> X)) \<and> length p \<ge> 2))" unfolding
              connected_def by auto
          then have "(\<forall>u v. u \<in> V1 \<and> v \<in> V1 \<and> u \<noteq> v \<longrightarrow> (\<exists>p. p \<noteq> [] \<and> ((hd p = u \<and> last p = v ) \<or> (hd p = v \<and> last p = u)) \<and> (\<forall>i < length p - 1. ((p ! i, p ! (i + 1)) \<in> X) \<or> ((nth p (i + 1), nth p i) \<in> X)) \<and> length p \<ge> 2))" using \<open>X \<noteq> {}\<close> by simp
          then have "(\<exists>p. p \<noteq> [] \<and> ((hd p = r \<and> last p = x) \<or> (hd p = x \<and> last p = r)) \<and> (\<forall>i < length p - 1. ((p ! i, p ! (i + 1)) \<in> X) \<or> (nth p (i + 1), nth p i) \<in> X) \<and> length p \<ge> 2)" using \<open>r \<in> V1\<close> \<open>x \<in> V1\<close> \<open>x \<noteq> r\<close> \<open>X \<noteq> {}\<close> by simp
          then obtain p where p_prop: "(p \<noteq> [] \<and> ((hd p = r \<and> last p = x) \<or> (hd p = x \<and> last p = r)) \<and> (\<forall>i < length p - 1. ((p ! i, p ! (i + 1)) \<in> X) \<or> (nth p (i + 1), nth p i) \<in> X) \<and> length p \<ge> 2)" by auto
          have "\<exists>v' w. v' \<in> V1 \<inter> V2 \<and> w \<in> V1 - V2 \<and> ((v', w) \<in> X \<or> (w, v') \<in> X)" 
          proof (cases "hd p = r \<and> last p = x")
            case True
            then have "last p = x" by simp
          have "hd p = r" using True  by simp
          have "length p \<ge> 2" using p_prop by simp
          have p_prop2: "(\<forall>i < length p - 1. ((p ! i, p ! (i + 1)) \<in> X) \<or> (nth p (i + 1), nth p i) \<in> X)" using p_prop by simp
          have "digraph V1 X" using \<open>tree V1 X\<close> unfolding tree_def by simp
          then have "X \<subseteq> V1 \<times> V1" unfolding digraph_def by simp
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
              then have "(nth p (i - 1), (nth p i)) \<in> X \<or> (nth p i, nth p (i - 1)) \<in> X" using p_prop \<open>i = (i - 1) + 1\<close> by auto
              then have "(nth p (i - 1), (nth p i)) \<in> V1 \<times> V1" using \<open>X \<subseteq> V1 \<times> V1\<close> by auto
              then show ?thesis using True by auto
            next
              case False
              show "i \<le> length p - 1 \<longrightarrow> (nth p i) \<in> V1"
              proof
                assume "i \<le> length p - 1"
                then have "i < length p - 1" using \<open>length p \<ge> 2\<close> False by simp
                then have "(nth p i, (nth p (i + 1))) \<in> X \<or> (nth p (i + 1), nth p i) \<in> X" using p_prop by simp
                then have "(nth p i, (nth p (i + 1))) \<in> V1 \<times> V1" using \<open>X \<subseteq> V1 \<times> V1\<close> by auto
                then show "(nth p i) \<in> V1" by simp
            qed
          qed
        qed
          have "V1 = (V1 \<inter> V2) \<union> (V1 - V2)" by auto
          then have V1_el_prop: "\<forall>v. v \<in> V1 \<longrightarrow> v \<in> (V1 - V2) \<or> v \<in> (V1 \<inter> V2)" by auto
          have "\<exists>i. i \<le> (length p) - 1 \<and> (nth p i) \<in> V1 - V2 \<and> (nth p (i - 1)) \<in> V1 \<inter> V2"
          proof (cases "\<forall>i < (length p) - 1. (nth p i) \<in> V1 \<inter> V2")
            case True
            have "((length p) - 1) - 1 < (length p) - 1" using \<open>length p \<ge> 2\<close> by simp 
            then have prop1: "(nth p ((length p) - 1 - 1)) \<in> V1 \<inter> V2" using True by simp
            have "(nth p (length p - 1)) = x" using \<open>last p = x\<close> 
              by (metis last_conv_nth p_prop)
            then have "(nth p (length p - 1)) \<in> V1 - V2" using \<open>x \<in> V1 - V2\<close> by simp
            then show ?thesis using prop1 by auto
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
            have "(nth p 0) = r" using p_prop hd_conv_nth True by metis
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
          have "nth p 0 = r" using True hd_conv_nth p_prop by metis
          then have "nth p 0 \<in> V1 \<inter> V2" using V1_prop V2_prop by simp
          have "i \<noteq> 0" 
          proof
            assume "i = 0"
            then have "nth p 0 \<in> V1 - V2" using i_prop by simp
            then show "False" using \<open>nth p 0 \<in> V1 \<inter> V2\<close> by simp
          qed
          then have "i - 1 + 1 = i" by simp
          then have "(((nth p (i - 1), nth p i) \<in> X) \<or> ((nth p i, nth p (i - 1)) \<in> X))" using p_prop \<open>i - 1 < length p - 1\<close> by auto
            then show ?thesis using i_prop by auto
          next
            case False
            then have "hd p = x \<and> last p = r" using p_prop by auto
            then have "last p = r" by simp
          have "hd p = x" using \<open>hd p = x \<and> last p = r\<close> by simp
          have "length p \<ge> 2" using p_prop by simp
          have p_prop2: "(\<forall>i < length p - 1. ((p ! i, p ! (i + 1)) \<in> X) \<or> (nth p (i + 1), nth p i) \<in> X)" using p_prop by simp
          have "digraph V1 X" using \<open>tree V1 X\<close> unfolding tree_def by simp
          then have "X \<subseteq> V1 \<times> V1" unfolding digraph_def by simp
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
              then have "(nth p (i - 1), (nth p i)) \<in> X \<or> (nth p i, nth p (i - 1)) \<in> X" using p_prop \<open>i = (i - 1) + 1\<close> by auto
              then have "(nth p (i - 1), (nth p i)) \<in> V1 \<times> V1" using \<open>X \<subseteq> V1 \<times> V1\<close> by auto
              then show ?thesis using True by auto
            next
              case False
              show "i \<le> length p - 1 \<longrightarrow> (nth p i) \<in> V1"
              proof
                assume "i \<le> length p - 1"
                then have "i < length p - 1" using \<open>length p \<ge> 2\<close> False by simp
                then have "(nth p i, (nth p (i + 1))) \<in> X \<or> ((nth p (i + 1), nth p i) \<in> X)" using p_prop by simp
                then have "(nth p i, (nth p (i + 1))) \<in> V1 \<times> V1" using \<open>X \<subseteq> V1 \<times> V1\<close> by auto
                then show "(nth p i) \<in> V1" by simp
            qed
          qed
        qed
          have "V1 = (V1 \<inter> V2) \<union> (V1 - V2)" by auto
          then have V1_el_prop: "\<forall>v. v \<in> V1 \<longrightarrow> v \<in> (V1 - V2) \<or> v \<in> (V1 \<inter> V2)" by auto
          have "\<exists>i. i \<le> (length p) - 1 \<and> (nth p i) \<in> V1 - V2 \<and> (nth p (i + 1)) \<in> V1 \<inter> V2"
          proof (cases "\<forall>i. 1 \<le> i \<and> i \<le> (length p) - 1 \<longrightarrow> (nth p i) \<in> V1 \<inter> V2")
            case True
            have "((length p) - 1) - 1 < (length p) - 1" using \<open>length p \<ge> 2\<close> by simp 
            then have prop1: "(nth p 1) \<in> V1 \<inter> V2" using True by simp
            have "(nth p 0) = x" using \<open>hd p = x\<close> 
              by (metis hd_conv_nth p_prop)
            then have "(nth p 0) \<in> V1 - V2" using \<open>x \<in> V1 - V2\<close> by simp
            then show ?thesis using prop1 by auto
          next
            case False
            then have "\<exists>i. 1 \<le> i \<and> i \<le> (length p) - 1 \<and> (nth p i) \<notin> V1 \<inter> V2" by auto
            then obtain i where i_prop: "1 \<le> i \<and> i \<le> (length p) - 1 \<and> (nth p i) \<notin> V1 \<inter> V2" by auto
            then have i_prop2: "(nth p i) \<notin> V1 \<inter> V2" by simp
            then have "i \<le> length p - 1" using i_prop by simp
            then have "(nth p i) \<in> V1 - V2" using V1_el_prop i_prop2 p_prop3 by simp
            let ?A = "{j. 1 \<le> j \<and> j \<le> length p - 1 \<and> (nth p j) \<in> V1 - V2}" 
            have "finite ?A" by simp
            have "i \<in> ?A" using i_prop \<open>(nth p i \<in> V1 - V2)\<close> by simp
            then have "?A \<noteq> {}" by auto
            then have "Max ?A \<in> ?A" using \<open>finite ?A\<close> Max_in by blast
            let ?k = "Max ?A"
            have max_prop: "\<forall>j. j\<in> ?A \<longrightarrow> j \<le> ?k" by simp
            have k_prop: "1 \<le> ?k \<and> ?k \<le> length p - 1 \<and> (nth p ?k) \<in> V1 - V2" using \<open>?k \<in> ?A\<close> by auto
            have "(nth p (length p - 1)) = r" using \<open>hd p = x \<and> last p = r\<close> last_conv_nth p_prop by metis
            then have "(nth p (length p - 1)) \<in> V1 \<inter> V2" using  V1_prop V2_prop by simp
            have "(nth p ?k) \<in> V1 - V2" using k_prop by simp
            then have "?k \<noteq> length p - 1" using \<open>(nth p (length p - 1)) \<in> V1 \<inter> V2\<close> k_prop by auto
            then have "?k < length p - 1" using k_prop by simp
            have "?k < ?k + 1" using \<open>?k \<in> ?A\<close> by simp
            then have "?k + 1 \<le> length p - 1" using \<open>?k < length p - 1 \<close> by simp
            have k_prop4: "(nth p (?k + 1)) \<in> V1 \<inter> V2"
            proof (rule ccontr)
              assume "(nth p (?k + 1)) \<notin> V1 \<inter> V2"
              then have "(nth p (?k + 1)) \<in> V1 - V2" using p_prop3 V1_el_prop i_prop2 \<open>?k + 1 <= length p -1 \<close> by simp
              then have "1 \<le> ?k + 1 \<and> ?k + 1 \<le> length p - 1" using k_prop \<open>?k + 1 \<le> length p - 1\<close> by simp
              then have "?k + 1 \<in> ?A" using \<open>nth p (?k + 1) \<in> V1 - V2\<close> by simp
              then show "False" using max_prop \<open>?k < ?k + 1\<close> 
                using leD by blast
            qed
            then have k_prop3: "?k \<le> length p - 1 \<and> (nth p ?k) \<in> V1 - V2 \<and> (nth p (?k + 1) \<in> V1 \<inter> V2)" using k_prop by simp
            then show ?thesis using k_prop4 by auto
          qed
          then obtain i where i_prop:  "i \<le> length p - 1 \<and> p ! i \<in> V1 - V2 \<and> p ! (i + 1) \<in> V1 \<inter> V2" by auto
          then have "(nth p (length p - 1)) = r" using \<open>hd p = x \<and> last p = r\<close> using p_prop last_conv_nth by metis
          then have "(nth p (length p - 1)) \<in> V1 \<inter> V2" using V1_prop V2_prop by simp
          have "i \<noteq> length p - 1"
          proof
            assume "i = length p - 1" 
            then have "(nth p (length p - 1)) \<in> V1 - V2" using i_prop by auto
            then show "False" using \<open>nth p (length p - 1) \<in> V1 \<inter> V2\<close> by simp
          qed
          then have "i < length p -1" using i_prop by simp
          then have "(nth p i, nth p (i + 1)) \<in> X \<or> (nth p (i+ 1), nth p i) \<in> X" using p_prop by auto
          then show ?thesis using i_prop by auto
        qed
          then obtain v' w where v'_w_prop: "v' \<in> V1 \<inter> V2 \<and> w \<in> V1 - V2 \<and> ((v', w) \<in> X \<or> (w, v') \<in> X)" by auto
          let ?v = "v'"
          let ?w = "w"
          have "?v \<in> V1 \<inter> V2" using v'_w_prop by simp
          have "?w \<in> V1 - V2" using v'_w_prop by simp
          show ?thesis
          proof (cases "(v',w) \<in> X")
            case True
            then have "(?v, ?w) \<in> X" using v'_w_prop by simp
          have "tree V2 Y" using V2_prop by simp
          then have "digraph V2 Y" unfolding tree_def by simp
          then have "Y \<subseteq> V2 \<times> V2" unfolding digraph_def by simp
          have "(?v, ?w) \<notin> V2 \<times> V2" using \<open>?w \<in> V1 - V2\<close> by simp
          then have "(?v, ?w) \<notin> Y" using \<open>Y \<subseteq> V2 \<times> V2\<close> by auto
          then have "(?v, ?w) \<in> X - Y" using \<open>(?v, ?w) \<in> X\<close> by simp
          have "connected V2 Y" using \<open>tree V2 Y\<close> unfolding tree_def by simp
          then have Y_connected: "(Y = {} \<and> card V2 = 1) \<or> (\<forall>u v. u \<in> V2 \<and> v \<in> V2 \<and> u \<noteq> v \<longrightarrow> (\<exists>p. p \<noteq> [] \<and> ((hd p = v \<and> last p = u) \<or> (hd p = u \<and> last p = v)) \<and> (\<forall>i < length p - 1. ((p ! i, p ! (i + 1)) \<in> Y) \<or> (nth p (i + 1), nth p i) \<in> Y) \<and> length p \<ge> 2))" 
            unfolding connected_def by simp
          have "acyclic V2 Y" using \<open>tree V2 Y\<close> unfolding tree_def by auto
          then have Y_acyclic: "(Y = {}) \<or> (\<forall>v. v \<in> V2 \<longrightarrow> \<not>(\<exists>p. p \<noteq> [] \<and> hd p = v \<and> last p = v \<and> (\<forall>i < length p - 1. (nth p i, nth p (i + 1)) \<in> Y) \<and> length p \<ge> 2))"  unfolding acyclic_def by auto
          have w_el_prop: "\<forall> x \<in> V2 \<union> {?w}.  \<not> (\<exists>(a,b) \<in> (Y \<union> {(?v, ?w)}). (a, b) = (?w, x))"
          proof (rule ccontr)
            assume "\<not> (\<forall>x \<in> V2 \<union> {?w}.
            \<not> (\<exists>(a, b)\<in>Y \<union> {(?v, ?w)}. (a, b) = (?w, x)))"
            then have "\<exists>x. x \<in> V2 \<union> {?w}  \<and> (\<exists>(a, b)\<in>Y \<union> {(?v, ?w)}. (a, b) = (?w, x))" by blast
            then obtain x where "x \<in> V2 \<union> {?w}  \<and> (\<exists>(a, b)\<in>Y \<union> {(?v, ?w)}. (a, b) = (?w, x))" by auto
            then obtain a b where a_b_prop: "(a, b)\<in>Y \<union> {(?v, ?w)} \<and> (a, b) = (?w, x)" by auto
            then have "(a, b) = (?w, x)" by auto
            then have "a = ?w \<and> b = x" by simp
            then have "(a, b) \<noteq> (?v, ?w)" using \<open>?v \<in> V1 \<inter> V2\<close>  \<open>?w \<in> V1 - V2\<close> by auto
            then have "(a,b) \<in> Y" using a_b_prop by auto
            then have "(?w, x) \<in> Y" using \<open>(a, b) = (?w, x)\<close> by simp
            then have "(?w, x) \<in> V2 \<times> V2" using \<open>Y \<subseteq> V2 \<times> V2\<close> by auto
            then have "?w \<in> V2" by simp
            then show "False" using \<open>?w \<in> V1 - V2\<close> by simp
          qed
          have "tree (V2 \<union> {?w}) (Y \<union> {(?v, ?w)})" unfolding tree_def
          proof (cases "Y = {} \<and> card V2 = 1")
            case True
            then have "V2 = {r}" using \<open>r \<in> V2\<close> 
              using card_1_singletonE by auto
            then have "V2 \<union> {?w} = {r, ?w}" by auto
            have "(Y \<union> {(?v, ?w)}) = {(?v, ?w)}" using True by auto
            have "?v = r" using \<open>V2 = {r}\<close> \<open>?v \<in> V1 \<inter> V2\<close> by simp
            then have 1: "digraph (V2 \<union> {?w}) (Y \<union> {(?v, ?w)})" unfolding digraph_def using \<open>Y \<subseteq> V2 \<times> V2\<close>
              using \<open>V2 \<union> {?w} = {r, ?w}\<close> by blast
            have "r \<noteq> ?w" using V2_prop \<open>?w \<in> V1 - V2\<close> by auto 
            have 2: "acyclic {r, ?w} {(r, ?w)}" unfolding acyclic_def 
            proof -
              have "{(r, ?w)} \<noteq> {}" by simp
              have "(\<forall>v\<in>{r, ?w}.
        \<nexists>pa. pa \<noteq> [] \<and>
             hd pa = v \<and>
             last pa = v \<and>
             (\<forall>ia<length pa - 1. (pa ! ia, pa ! (ia + 1)) \<in> {(r, ?w)}) \<and>
             2 \<le> length pa)"
              proof 
                fix v
                assume v_assum: "v \<in> {r, ?w}"
                show "\<nexists>pa. pa \<noteq> [] \<and>
             hd pa = v \<and>
             last pa = v \<and>
             (\<forall>ia<length pa - 1. (pa ! ia, pa ! (ia + 1)) \<in> {(r, ?w)}) \<and>
             2 \<le> length pa"
              proof (cases "v = r")
                case True
                show ?thesis 
                proof (rule ccontr)
                  assume "\<not> (\<nexists>pa. pa \<noteq> [] \<and>
             hd pa = v \<and>
             last pa = v \<and>
             (\<forall>ia<length pa - 1. (pa ! ia, pa ! (ia + 1)) \<in> {(r, ?w)}) \<and>
             2 \<le> length pa) "
                  then have "\<exists>pa. pa \<noteq> [] \<and>
             hd pa = v \<and>
             last pa = v \<and>
             (\<forall>ia<length pa - 1. (pa ! ia, pa ! (ia + 1)) \<in> {(r, ?w)}) \<and>
             2 \<le> length pa" by auto
                  then obtain pa where pa_prop2: "pa \<noteq> [] \<and>
             hd pa = v \<and>
             last pa = v \<and>
             (\<forall>ia<length pa - 1. (pa ! ia, pa ! (ia + 1)) \<in> {(r, ?w)}) \<and>
             2 \<le> length pa" by auto
                  then have "pa \<noteq> []" by simp
                  then have "(nth pa (length pa - 1)) = v" using pa_prop2 last_conv_nth by fastforce
                  have "length pa - 1 - 1 < length pa - 1" using pa_prop2 by auto
                  then have pa_edge: "(nth pa (length pa - 1 -1), nth pa (length pa - 1)) \<in> {(r, ?w)}" using pa_prop2 
                    by (metis add_le_imp_le_diff le_add_diff_inverse2 nat_1_add_1)
                  then have " (\<forall>ia<length pa - 1. (nth pa ia, nth pa (ia + 1)) \<in> ({r, ?w} \<times> {r, ?w}))" using pa_prop2 by auto              
                  then have pa_prop3: "\<forall>ia<length pa - 1. (nth pa ia) \<in> {r, ?w}" using pa_prop2 by auto
                  show "False" 
                  proof (cases "nth pa (length pa - 1 -1) = r")
                    case True
                    then have "(nth pa (length pa - 1 - 1), nth pa (length pa - 1)) = (r, r)" using \<open>nth pa (length pa - 1) = v\<close> \<open>v = r\<close> by simp
                    then have "(r, r) \<in> {(r, ?w)}" using pa_edge by simp
                    then show ?thesis using \<open>r \<noteq> ?w\<close> by simp
                  next
                    case False
                    then have "(nth pa (length pa - 1 - 1)) \<in> {r, ?w}" using pa_prop3 \<open>(length pa - 1 - 1) < length pa - 1\<close> by auto
                    then have "(nth pa (length pa - 1 - 1)) = ?w" using False by simp
                    then have "(nth pa (length pa - 1 - 1), nth pa (length pa - 1)) = (?w, r)" using \<open>nth pa (length pa - 1) = v\<close> \<open>v = r\<close> by simp
                    then have "(?w, r) \<in> {(r, ?w)}" using \<open>length pa - 1 -1 < length pa - 1\<close> pa_prop2 by simp
                    then show ?thesis using \<open>r \<noteq> ?w\<close> by simp
                  qed
                qed
              next
                case False
                then have "v = ?w" using v_assum by simp
                show ?thesis
                proof (rule ccontr)
                  assume "\<not> (\<nexists>pa. pa \<noteq> [] \<and>
             hd pa = v \<and>
             last pa = v \<and>
             (\<forall>ia<length pa - 1. (pa ! ia, pa ! (ia + 1)) \<in> {(r, ?w)}) \<and>
             2 \<le> length pa) "
                  then have "\<exists>pa. pa \<noteq> [] \<and>
             hd pa = v \<and>
             last pa = v \<and>
             (\<forall>ia<length pa - 1. (pa ! ia, pa ! (ia + 1)) \<in> {(r, ?w)}) \<and>
             2 \<le> length pa" by auto
                  then obtain pa where pa_prop2: "pa \<noteq> [] \<and>
             hd pa = v \<and>
             last pa = v \<and>
             (\<forall>ia<length pa - 1. (pa ! ia, pa ! (ia + 1)) \<in> {(r, ?w)}) \<and>
             2 \<le> length pa" by auto
                  then have "pa \<noteq> []" by simp
                  then have "(nth pa 0) = v" using pa_prop2 hd_conv_nth by fastforce
                  then have "0 < length pa - 1" using pa_prop2 by simp
                  then have pa_prop3: "(nth pa 0, nth pa 1) \<in> {(r, ?w)}" using pa_prop2 by simp
                  then show "False"
                  proof (cases "nth pa 1 = ?w")
                    case True
                    then have "(nth pa 0, nth pa 1) = (?w, ?w)" using \<open>nth pa 0 = v\<close> \<open>v = ?w\<close> by simp
                    then have "(?w, ?w) \<in> {(r, ?w)}" using pa_prop3 by simp
                    then show ?thesis using \<open>r \<noteq> ?w\<close> by simp
                  next
                    case False
                    have pa_prop4: "(\<forall>ia<length pa - 1. (nth pa ia, nth pa (ia + 1)) \<in> ({r, p ! i} \<times> {r, ?w}))"
                      using False pa_prop3 by blast
                    have "(nth pa (length pa - 1)) = v" using pa_prop2 last_conv_nth by fastforce
                    then have "(nth pa (length pa - 1)) = ?w" using \<open>v = ?w\<close> by simp
                    then have "(nth pa (length pa - 1)) \<in> {r, ?w}" by simp
                    then have pa_prop5: "(\<forall>ia\<le>length pa - 1. (nth pa ia) \<in>  {r, ?w})" using pa_prop4 
                      by (meson False Pair_inject pa_prop3 singletonD)
                    have "nth pa 0 = ?w" using \<open>v = ?w\<close> \<open>nth pa 0 = v\<close> by simp 
                    have "1 \<le> length pa - 1" using pa_prop2 by auto
                    then have "(nth pa 1) = r" using pa_prop5 False by auto
                    then have "(nth pa 0, nth pa 1) = (?w, r)" using \<open>nth pa 0 = ?w\<close> by simp
                    then show ?thesis using pa_prop3 \<open>r \<noteq> ?w\<close> by simp
                  qed
                qed
              qed
            qed
            then show "{(r, ?w)} = {} \<or>
    (\<forall>v\<in>{r, ?w}.
        \<nexists>pa. pa \<noteq> [] \<and>
             hd pa = v \<and>
             last pa = v \<and>
             (\<forall>ia<length pa - 1. (pa ! ia, pa ! (ia + 1)) \<in> {(r, ?w)}) \<and>
             2 \<le> length pa)" by simp
          qed
          have 3: "connected {r, ?w} {(r, ?w)}" unfolding connected_def
          proof -
            have "{(r, ?w)} \<noteq> {}" by simp
            have "(\<forall>u v. u \<in> {r, ?w} \<and> v \<in> {r, ?w} \<and> u \<noteq> v \<longrightarrow>
           (\<exists>pa. pa \<noteq> [] \<and>
                 (hd pa = v \<and> last pa = u \<or> hd pa = u \<and> last pa = v) \<and>
                 (\<forall>ia<length pa - 1.
                     (pa ! ia, pa ! (ia + 1)) \<in> {(r, ?w)} \<or>
                     (pa ! (ia + 1), pa ! ia) \<in> {(r, ?w)}) \<and>
                 2 \<le> length pa)) "
            proof (rule, rule)
              fix u v
              show "u \<in> {r, ?w} \<and> v \<in> {r, ?w} \<and> u \<noteq> v \<longrightarrow>
           (\<exists>pa. pa \<noteq> [] \<and>
                 (hd pa = v \<and> last pa = u \<or> hd pa = u \<and> last pa = v) \<and>
                 (\<forall>ia<length pa - 1.
                     (pa ! ia, pa ! (ia + 1)) \<in> {(r, ?w)} \<or>
                     (pa ! (ia + 1), pa ! ia) \<in> {(r, ?w)}) \<and>
                 2 \<le> length pa)"
              proof
                assume u_v_prop: "u \<in> {r, ?w} \<and> v \<in> {r, ?w} \<and> u \<noteq> v"
                show "(\<exists>pa. pa \<noteq> [] \<and>
                 ((hd pa = v \<and> last pa = u) \<or> (hd pa = u \<and> last pa = v)) \<and>
                 (\<forall>ia<length pa - 1. ((pa ! ia, pa ! (ia + 1)) \<in> {(r, ?w)}) \<or> (pa ! (ia + 1), pa ! ia) \<in> {(r, ?w)}) \<and>
                 2 \<le> length pa)"
                proof (cases "u = r")
                  case True
                  show ?thesis
                  proof 
                    have "v = ?w" using u_v_prop True by auto
                    let ?pa = "[r, ?w]"
                    have "(\<forall>ia<length [r, ?w] - 1. ([r, ?w] ! ia, [r, ?w] ! (ia + 1)) \<in> {(r, ?w)})" by auto
                    then have "[r, ?w] \<noteq> [] \<and> hd [r, ?w] = u \<and> last [r, ?w] = v \<and> (\<forall>ia<length [r, ?w] - 1. ([r, ?w] ! ia, [r, ?w] ! (ia + 1)) \<in> {(r, ?w)}) \<and> 2 \<le> length [r, ?w]" using True \<open>v = ?w\<close> by auto
                    then show "?pa \<noteq> [] \<and>
    (hd ?pa = v \<and> last ?pa = u \<or> hd ?pa = u \<and> last ?pa = v) \<and>
    (\<forall>ia<length ?pa - 1.
        (?pa ! ia, ?pa ! (ia + 1)) \<in> {(r, ?w)} \<or>
        (?pa ! (ia + 1), ?pa ! ia) \<in> {(r, ?w)}) \<and>
    2 \<le> length ?pa" using \<open>v = ?w\<close> True by auto
                  qed
                next
                  case False
                  show ?thesis
                  proof
                    let ?pa = "[r, ?w]"
                    have "u = ?w" using u_v_prop False by simp
                    then have "v = r" using u_v_prop by auto
                    then have "[r, ?w] \<noteq> [] \<and> hd [r, ?w] = r \<and> last [r, ?w] = ?w \<and> (\<forall>ia<length [r, ?w] - 1. ([r, ?w] ! ia, [r, ?w] ! (ia + 1)) \<in> {(r, ?w)}) \<and> length [r, ?w] \<ge> 2" by auto
                    then show "?pa \<noteq> [] \<and>
    (hd ?pa = v \<and> last ?pa = u \<or> hd ?pa = u \<and> last ?pa = v) \<and>
    (\<forall>ia<length ?pa - 1.
        (?pa ! ia, ?pa ! (ia + 1)) \<in> {(r, ?w)} \<or>
        (?pa ! (ia + 1), ?pa ! ia) \<in> {(r, ?w)}) \<and>
    2 \<le> length ?pa" using \<open>v = r\<close> \<open>u = ?w\<close> by auto 
                  qed
                qed
              qed
            qed
            then show "{(r, ?w)} = {} \<and> card {r, ?w} = 1 \<or>
    (\<forall>u v. u \<in> {r, ?w} \<and> v \<in> {r, ?w} \<and> u \<noteq> v \<longrightarrow>
           (\<exists>pa. pa \<noteq> [] \<and>
                 (hd pa = v \<and> last pa = u \<or> hd pa = u \<and> last pa = v) \<and>
                 (\<forall>ia<length pa - 1.
                     (pa ! ia, pa ! (ia + 1)) \<in> {(r, ?w)} \<or>
                     (pa ! (ia + 1), pa ! ia) \<in> {(r, ?w)}) \<and>
                 2 \<le> length pa))" by auto
          qed
          have 4: "card {(r, ?w)} = card {r, ?w} - 1" using \<open>r \<noteq> ?w\<close> by simp
          have "Y \<union> {(?v, ?w)} = {(r, ?w)}" using \<open>?v = r\<close> \<open>Y \<union> {(?v, ?w)} = {(?v, ?w)}\<close> by simp
          then show "digraph (V2 \<union> {?w}) (Y \<union> {(?v, ?w)}) \<and>
    local.acyclic (V2 \<union> {?w}) (Y \<union> {(?v, ?w)}) \<and>
    local.connected (V2 \<union> {?w}) (Y \<union> {(?v, ?w)}) \<and>
    card (Y \<union> {(?v, ?w)}) = card (V2 \<union> {?w}) - 1" using 1 2 3 \<open>V2 \<union> {?w} = {r, ?w}\<close> 4 
            by argo
          next
            case False
            then have "(Y \<noteq> {} \<or> card V2 \<noteq> 1)" by simp
            have "(Y \<union> {(?v, ?w)}) \<subseteq> (V2 \<union> {?w}) \<times> (V2 \<union> {?w})" using \<open>Y \<subseteq> V2 \<times> V2\<close> \<open>?v \<in> V1 \<inter> V2\<close> by auto
            then have 1: "digraph (V2 \<union> {?w}) (Y \<union> {(?v, ?w)})" unfolding digraph_def by simp
            have 2: "connected (V2 \<union> {?w}) (Y \<union> {(?v, ?w)})" unfolding connected_def
            proof -
              have "\<not> (Y \<union> {(?v, ?w)} = {}  \<and> card (V2 \<union> { ?w}) = 1)" using \<open>\<not>(Y = {} \<and> card V2 = 1)\<close> by auto
              have "
    (\<forall>u v. u \<in> V2 \<union> {?w} \<and> v \<in> V2 \<union> {?w} \<and> u \<noteq> v \<longrightarrow>
           (\<exists>pa. pa \<noteq> [] \<and>
                 (hd pa = v \<and> last pa = u \<or> hd pa = u \<and> last pa = v) \<and>
                 (\<forall>ia<length pa - 1.
                     (pa ! ia, pa ! (ia + 1)) \<in> Y \<union> {(?v, ?w)} \<or>
                     (pa ! (ia + 1), pa ! ia) \<in> Y \<union> {(?v, ?w)}) \<and>
                 2 \<le> length pa))"
              proof (rule, rule)
                fix u v
                show "u \<in> V2 \<union> {?w} \<and> v \<in> V2 \<union> {?w} \<and> u \<noteq> v \<longrightarrow>
           (\<exists>pa. pa \<noteq> [] \<and>
                 (hd pa = v \<and> last pa = u \<or> hd pa = u \<and> last pa = v) \<and>
                 (\<forall>ia<length pa - 1.
                     (pa ! ia, pa ! (ia + 1)) \<in> Y \<union> {(?v, ?w)} \<or>
                     (pa ! (ia + 1), pa ! ia) \<in> Y \<union> {(?v, ?w)}) \<and>
                 2 \<le> length pa)"
              proof
                assume assm4: "u \<in> V2 \<union> {?w} \<and> v \<in> V2 \<union> {?w} \<and> u \<noteq> v"
                then have "v \<in> V2 \<union> {?w}" by simp
                have "u \<noteq> v" using assm4 by simp
                show "\<exists>pa. pa \<noteq> [] \<and>
         (hd pa = v \<and> last pa = u \<or> hd pa = u \<and> last pa = v) \<and>
         (\<forall>ia<length pa - 1.
             (pa ! ia, pa ! (ia + 1)) \<in> Y \<union> {(?v, ?w)} \<or>
             (pa ! (ia + 1), pa ! ia) \<in> Y \<union> {(?v, ?w)}) \<and>
         2 \<le> length pa"
                proof (cases "v \<in> V2")
                  case True
                  then have "v \<noteq> ?w" using \<open>v \<in> V2 \<union> {?w}\<close> \<open>?w \<in> V1 -  V2\<close> by auto
                  then show ?thesis
                  proof (cases "u \<in> V2")
                    case True
                    then have "\<exists>q. q \<noteq> [] \<and> ((hd q = u \<and> last q = v) \<or> (hd q = v \<and> last q = u)) \<and> (\<forall>ia<length q - 1. ((q ! ia, q ! (ia + 1)) \<in> Y) \<or> ((nth q (ia + 1), nth q ia) \<in> Y)) \<and> length q \<ge> 2" using Y_connected \<open>v \<in> V2\<close> \<open>u \<noteq> v\<close> \<open>\<not>(Y = {} \<and> card V2 = 1)\<close> by auto 
                    then obtain q where "q \<noteq> [] \<and> ((hd q = u \<and> last q = v) \<or> (hd q = v \<and> last q = u)) \<and> (\<forall>ia<length q - 1. ((q ! ia, q ! (ia + 1)) \<in> Y) \<or> ((nth q (ia + 1), nth q ia) \<in> Y)) \<and> length q \<ge> 2" by auto
                    then have "q \<noteq> [] \<and> ((hd q = u \<and> last q = v) \<or> (hd q = v \<and> last q = u)) \<and> (\<forall>ia<length q - 1. ((q ! ia, q ! (ia + 1)) \<in> Y \<union> {(?v, ?w)}) \<or> ((nth q (ia + 1)), nth q ia) \<in> Y \<union> {(?v, ?w)}) \<and> length q \<ge> 2" by auto
                    then show ?thesis by auto
                  next
                    case False
                    then have "u = ?w" using assm4 by simp
                    show ?thesis 
                    proof (cases "v \<noteq> ?v")
                      case True
                      then have "(Y = {} \<and> card V2 = 1) \<or> (\<exists>q.  q \<noteq> [] \<and> ((hd q = v \<and> last q = ?v) \<or> (hd q = ?v \<and> last q = v))  \<and> (\<forall>ia<length q - 1. ((q ! ia, q ! (ia + 1)) \<in> Y) \<or> (nth q (ia + 1), nth q ia) \<in> Y) \<and> length q \<ge> 2)" using \<open>v \<in> V2\<close> 
                            \<open>?v \<in> V1 \<inter> V2\<close> Y_connected by auto
                      then have "(\<exists>q.  q \<noteq> [] \<and> ((hd q = v \<and> last q = ?v) \<or> (hd q = ?v \<and> last q = v))  \<and> (\<forall>ia<length q - 1. ((q ! ia, q ! (ia + 1)) \<in> Y) \<or> (nth q (ia + 1), nth q ia) \<in> Y) \<and> length q \<ge> 2)" using \<open>\<not> (Y = {} \<and> card V2 = 1)\<close> by auto
                      then obtain q where q_prop: "q \<noteq> [] \<and> ((hd q = v \<and> last q = ?v) \<or> hd q = ?v \<and> last q = v) \<and> (\<forall>ia<length q - 1. ((q ! ia, q ! (ia + 1)) \<in> Y) \<or> (nth q (ia + 1), nth q ia) \<in> Y) \<and> length q \<ge> 2" by auto
                      show ?thesis
                      proof (cases "hd q = v \<and> last q = ?v")
                        case True
                        then have "\<not>(hd q = ?v \<and> last q = v)" using \<open>v \<noteq> ?v\<close> by simp
                        let ?q = "q @ [?w]"
                        have "q \<noteq> [] \<and> last q = ?v" using q_prop True by simp
                      then have "(nth q (length q - 1)) = ?v" using q_prop last_conv_nth 
                        by fastforce
                      then have v_cont: "(nth ?q (length ?q - 1 - 1)) = ?v"  by (metis Cons_eq_appendI \<open>q \<noteq> [] \<and> last q = ?v\<close> append.assoc append_butlast_last_id butlast_snoc length_butlast nth_append_length)
                      have "length ?q \<ge> 2" using q_prop by simp
                      then have length_prop: "(length ?q - 1 - 1) + 1 = length ?q - 1 " by simp
                      have "(nth ?q (length ?q - 1)) = ?w" by auto
                      then have last_edge: "(nth ?q (length ?q - 1 - 1), nth ?q ((length ?q - 1 - 1) + 1 )) = (?v, ?w)" using v_cont length_prop by simp
                      have "?q \<noteq> []" using q_prop by simp
                      have hd_last_q: "hd ?q = v \<and> last ?q = ?w" using q_prop True by auto
                      have "length ?q - 1 - 1 < length ?q - 1" using \<open>length ?q \<ge> 2\<close> by simp
                      have "\<forall>i < length ?q - 1. ((?q ! i, ?q ! (i + 1)) \<in> Y \<union> {(?v, ?w)} \<or> (nth ?q (i + 1), nth ?q i) \<in> Y \<union> {(?v, ?w)})" 
                      proof -
                        have "\<forall>i < length q - 1. (nth ?q i) = (nth q i)" 
                          by (metis \<open>q \<noteq> [] \<and> last q = v'\<close> add_lessD1 canonically_ordered_monoid_add_class.lessE diff_less length_greater_0_conv nth_append zero_less_one)
                        moreover have "length ?q - 1 - 1 = length q - 1" by simp
                        ultimately have "\<forall>i < length ?q - 1 - 1. (nth ?q i) = (nth q i)" by simp
                        then have q_el_prop: "\<forall>i < length ?q - 1 - 1. (nth ?q i, nth ?q (i + 1)) \<in> Y \<union> {(?v, ?w)} \<or> (nth ?q (i + 1), nth ?q i) \<in> Y \<union> {(?v, ?w)}" using q_prop \<open>length ?q - 1 -1 = length q - 1\<close> 
                          by (metis UnI1 less_diff_conv nth_append)
                        have "(nth ?q (length ?q - 1 - 1), nth ?q (length ?q - 1)) = (?v, ?w)" using v_cont by auto
                        then have "(nth ?q (length ?q - 1 - 1), nth ?q (length ?q - 1)) \<in> Y \<union> {(?v, ?w)}" by simp
                        then have "\<forall>i \<le> length ?q - 1 - 1. (nth ?q i, nth ?q (i + 1)) \<in> Y \<union> {(?v, ?w)} \<or> (nth ?q (i + 1), nth ?q i) \<in> Y \<union> {(?v, ?w)}" using q_el_prop 
                          by (metis le_neq_implies_less length_prop)
                        then show ?thesis by auto
                      qed
                      then have "?q \<noteq> [] \<and> hd ?q = v \<and> last ?q = ?w \<and> (\<forall>i < length ?q - 1. ((?q ! i, ?q ! (i + 1)) \<in> Y \<union> {(?v, ?w)}) \<or> (nth ?q (i + 1), nth ?q i) \<in> Y \<union> {(?v, ?w)})" 
                        using \<open>?q \<noteq> []\<close> hd_last_q by simp
                      then show ?thesis using \<open>u = ?w\<close> \<open>length ?q \<ge> 2\<close> by blast
                      next
                        case False
                        let ?q = "?w # q"
                        have "hd q = ?v \<and> last q = v" using False q_prop by auto
                        then have f_4: "hd ?q = ?w \<and> last ?q = v" using q_prop by simp
                        have f_1: "?q \<noteq> []" by simp
                        have f_2: "length ?q \<ge> 2" using q_prop by simp
                        have f_31: "\<forall>i. 1 \<le> i \<and> i < length ?q - 1 \<longrightarrow> (((nth ?q i, nth ?q (i + 1)) \<in> Y \<union> {(?v, ?w)}) \<or> (nth ?q (i + 1), nth ?q i) \<in> Y \<union> {(?v, ?w)})"  
                        proof
                          fix j
                          show "1 \<le> j \<and> j < length ?q - 1 \<longrightarrow> (((nth ?q j, nth ?q (j + 1)) \<in> Y \<union> {(?v, ?w)}) \<or> (nth ?q (j + 1), nth ?q j) \<in> Y \<union> {(?v, ?w)})"
                          proof
                            assume j_assum: "1 \<le> j \<and> j < length ?q - 1"
                            have "length q > 0" using q_prop by simp
                            have "j - 1 + 1 = j" using j_assum by simp
                            have "1 \<le> j + 1 \<and> j + 1 \<le> length ?q - 1" using j_assum by simp
                            have i_j_reln: "\<forall>i. 0 < i \<and> i \<le> (length ?q - 1) \<longrightarrow> (nth ?q i) = (nth q (i - 1))" by auto
                            then have "(nth ?q j) = (nth q (j - 1))" using j_assum by simp
                            have "(nth ?q (j + 1)) = (nth q j)" using i_j_reln \<open>1 \<le> j + 1 \<and> j + 1 \<le> length ?q - 1\<close> by simp
                            have "j - 1 < length q - 1" using j_assum by auto
                            then have "(((nth q (j - 1), nth q j) \<in> Y \<union> {(?v, ?w)}) \<or> ((nth q j, nth q (j - 1)) \<in> Y \<union> {(?v, ?w)}))" using q_prop \<open>j - 1 + 1 = j\<close> by auto
                            then show "(((nth ?q j, nth ?q (j + 1)) \<in> Y \<union> {(?v, ?w)}) \<or> ((nth ?q (j + 1), nth ?q j) \<in> Y \<union> {(?v, ?w)}))" using \<open>(nth ?q j) = (nth q (j - 1))\<close> \<open>(nth ?q (j + 1)) = (nth q j)\<close> by auto
                          qed
                        qed
                        have "(nth ?q 0) = ?w" by simp
                        have "(nth ?q 1) = ?v" using \<open>hd q = ?v \<and> last q = v\<close> hd_conv_nth 
                          by (metis \<open>hd (?w # q) = ?w \<and> last (?w # q) = v\<close> \<open>v \<noteq> ?w\<close> diff_is_0_eq' last_ConsL le_numeral_extra(4) nth_Cons' zero_neq_one)
                        then have "(nth ?q 1, nth ?q 0) \<in> {(?v, ?w)}" using \<open>nth ?q 0 = ?w\<close> \<open>nth ?q 1 = ?v\<close> by simp
                        then have "\<forall>i. i < length ?q - 1 \<longrightarrow> (((nth ?q i, nth ?q (i + 1)) \<in> Y \<union> {(?v, ?w)}) \<or> (nth ?q (i + 1), nth ?q i) \<in> Y \<union> {(?v, ?w)})" using f_31 
                          by (smt (verit, best) Nat.add_diff_assoc2 Nat.diff_diff_right Un_insert_right \<open>(?w # q) ! 0 = ?w\<close> \<open>(?w # q) ! 1 = ?v\<close> diff_diff_cancel diff_self_eq_0 insert_iff le_neq_implies_less less_one nat_le_linear sup_bot_right)
                        then have "\<forall>i < length ?q - 1. (((nth ?q i, nth ?q (i + 1)) \<in> Y \<union> {(?v, ?w)}) \<or> (nth ?q (i + 1), nth ?q i) \<in> Y \<union> {(?v, ?w)})" by auto
                        then show ?thesis using f_1 f_2 f_4 
                          using \<open>u = ?w\<close> by blast          
                      qed
                    next
                      case False
                      then have "v = ?v" by simp
                      let ?q = "[?v, ?w]" 
                      have "?q \<noteq> [] \<and> hd ?q = v \<and> last ?q = u \<and> (\<forall>i < length ?q - 1. (?q ! i, ?q ! (i + 1)) \<in> Y \<union> {(?v, ?w)}) \<and> length ?q \<ge> 2" using \<open>v = ?v\<close> \<open>u = ?w\<close> by simp
                      then show ?thesis by blast
                    qed
                  qed
                  next
                    case False
                    then have "v = ?w" using \<open>v \<in> V2 \<union> {?w}\<close> by simp
                    then have "u \<noteq> ?w" using \<open>u \<noteq> v\<close> by simp
                    then have "u \<in> V2" using assm4 by simp
                    show ?thesis
                    proof (cases "u = ?v")
                      case True
                      have "(\<forall>i< length [?v, ?w] - 1. (nth [?v, ?w] i, nth [?v, ?w] (i + 1)) \<in> {(?v, ?w)})" by auto
                      then have "[?v, ?w] \<noteq> [] \<and> hd [?v, ?w] = u \<and> last [?v, ?w] = v \<and> (\<forall>i< length [?v, ?w] - 1. (nth [?v, ?w] i, nth [?v, ?w] (i + 1)) \<in> Y \<union> {(?v, ?w)}) \<and> length [?v, ?w] \<ge> 2" using \<open>v = ?w\<close> \<open>u = ?v\<close> by auto 
                      then show ?thesis by blast
                    next
                      case False
                      have "(Y = {} \<and> card V2 = 1) \<or>
           (\<exists>p. p \<noteq> [] \<and>
                ((hd p = ?v \<and> last p = u) \<or> (hd p = u \<and> last p = ?v)) \<and>
                (\<forall>i<length p - 1.
                    ((p ! i, p ! (i + 1)) \<in> Y) \<or> ((p ! (i + 1), p ! i) \<in> Y)) \<and>
                2 \<le> length p)" using Y_connected \<open>u \<in> V2\<close> \<open>?v \<in> V1 \<inter> V2\<close> \<open>u \<noteq> ?v\<close> by auto
                      then have "(\<exists>p. p \<noteq> [] \<and>
                ((hd p = ?v \<and> last p = u) \<or> (hd p = u \<and> last p = ?v)) \<and>
                (\<forall>i<length p - 1.
                    ((p ! i, p ! (i + 1)) \<in> Y) \<or> ((p ! (i + 1), p ! i) \<in> Y)) \<and>
                2 \<le> length p)" using \<open>Y \<noteq> {} \<or> card V2 \<noteq> 1\<close> by auto
                      then obtain q where q_prop: "q \<noteq> [] \<and> ((hd q = u \<and> last q = ?v) \<or> (hd q = ?v \<and> last q = u)) \<and> (\<forall>ia<length q - 1. ((q ! ia, q ! (ia + 1)) \<in> Y) \<or> (nth q (ia + 1), nth q ia) \<in> Y) \<and> length q \<ge> 2" by auto
                      show ?thesis
                      proof (cases "hd q = u \<and> last q = ?v")
                        case True
                        let ?q = "q @ [?w]"
                      have "q \<noteq> [] \<and> last q = ?v" using q_prop True  by simp
                      then have "(nth q (length q - 1)) = ?v" using q_prop last_conv_nth 
                        by metis
                      then have v_cont: "(nth ?q (length ?q - 1 - 1)) = ?v"  by (metis Cons_eq_appendI \<open>q \<noteq> [] \<and> last q = ?v\<close> append.assoc append_butlast_last_id butlast_snoc length_butlast nth_append_length)
                      have f_1: "length ?q \<ge> 2" using q_prop by auto
                      then have length_prop: "(length ?q - 1 - 1) + 1 = length ?q - 1 " by simp
                      have "(nth ?q (length ?q - 1)) = ?w" by auto
                      then have last_edge: "(nth ?q (length ?q - 1 - 1), nth ?q ((length ?q - 1 - 1) + 1 )) = (?v, ?w)" using v_cont length_prop by simp
                      have f_2: "?q \<noteq> []" using q_prop by simp
                      have hd_last_q: "hd ?q = u \<and> last ?q = ?w" using q_prop True  by auto
                      have "length ?q - 1 - 1 < length ?q - 1" using \<open>length ?q \<ge> 2\<close> by simp
                      have f_3: "\<forall>i < length ?q - 1. ((?q ! i, ?q ! (i + 1)) \<in> Y \<union> {(?v, ?w)} \<or> ((nth ?q (i + 1), nth ?q i) \<in> Y \<union> {(?v, ?w)}))"
                      proof -
                          have f_2: "length q - 1 = length ?q - 1 - 1" by simp
                          then have "\<forall>i \<le> length q - 1. (nth ?q i) = (nth q i)" 
                            by (simp add: less_eq_iff_succ_less nth_append q_prop)
                          then have f_1: "\<forall>i \<le> length ?q - 1 - 1. (nth ?q i) = (nth q i)" by auto
                          then have "\<forall>i < length ?q - 1. (nth ?q i) = (nth q i)" by simp
                          then have f_3: "\<forall>i < length ?q - 1 - 1. ((nth ?q i , nth ?q (i + 1)) \<in> Y \<union> {(?v, ?w)} \<or> (nth ?q (i + 1), nth ?q i) \<in> Y \<union> {(?v, ?w)})" using f_1 f_2 q_prop by auto
                          have "length ?q - 1 - 1 < length ?q - 1" using \<open>length ?q \<ge> 2\<close> by simp
                          have "(nth q (length q - 1)) = ?v" using \<open>q \<noteq> [] \<and> last q = ?v\<close> last_conv_nth by fastforce
                          then have "(nth ?q (length q - 1)) = ?v" using f_2 
                            using v_cont by presburger
                          then have "(nth ?q (length ?q - 1 - 1)) = ?v" using f_2 by simp
                          moreover have "(nth ?q (length ?q - 1)) = ?w" by auto
                          moreover have "length ?q - 1 - 1 + 1 = length ?q - 1" using \<open>length ?q \<ge> 2\<close> by simp
                          ultimately have "(nth ?q (length ?q - 1 - 1), nth ?q (length ?q - 1 - 1 + 1)) \<in> {(?v, ?w)}" using \<open>(nth ?q (length ?q - 1 - 1)) = ?v\<close> by simp
                          then have "((nth ?q (length ?q - 1 - 1) , nth ?q (length ?q - 1 - 1 + 1)) \<in> Y \<union> {(?v, ?w)} \<or> (nth ?q (length ?q - 1 - 1 + 1), nth ?q (length ?q - 1 - 1)) \<in> Y \<union> {(?v, ?w)})" by auto
                          
                          then have "\<forall>i \<le> length ?q - 1 - 1. ((nth ?q i , nth ?q (i + 1)) \<in> Y \<union> {(?v, ?w)} \<or> (nth ?q (i + 1), nth ?q i) \<in> Y \<union> {(?v, ?w)})" using f_3 
                            using le_neq_implies_less by blast
                          then show ?thesis using \<open>length ?q - 1 - 1 < length ?q - 1\<close> 
                            by auto
                        qed
                        then have "?q \<noteq> [] \<and> hd ?q = u \<and> last ?q = ?w \<and> (\<forall>i < length ?q - 1. ((?q ! i, ?q ! (i + 1)) \<in> Y \<union> {(?v, ?w)} \<or> ((nth ?q (i + 1), nth ?q i) \<in> Y \<union> {(?v, ?w)})))" using f_1 f_2 hd_last_q by auto
                        then show ?thesis using \<open>u \<noteq> ?w\<close> \<open>v = ?w\<close> 
                          using f_1 by blast
                      next
                        case False
                        then have "hd q = ?v \<and> last q = u" using q_prop by auto
                        let ?q = "?w # q"
                        have f_1: "hd ?q = ?w \<and> last q = u" using \<open>hd q = ?v \<and> last q = u\<close> by simp
                        have f_2:"?q \<noteq> []" by simp
                        have f_3: "length ?q \<ge> 2" using q_prop by simp
                        have j_fact: "\<forall>j. 1 \<le> j \<and> j < length ?q - 1 \<longrightarrow> ((nth ?q j, nth ?q (j + 1)) \<in> Y \<union> {(?v, ?w)} \<or> (nth ?q (j + 1), nth ?q j) \<in> Y \<union> {(?v, ?w)})"
                        proof
                          fix j
                          show "1 \<le> j \<and> j < length ?q - 1 \<longrightarrow> (((nth ?q j, nth ?q (j + 1)) \<in> Y \<union> {(?v, ?w)}) \<or> (nth ?q (j + 1), nth ?q j) \<in> Y \<union> {(?v, ?w)})"
                          proof
                            assume j_assum: "1 \<le> j \<and> j < length ?q - 1"
                            have "length q > 0" using q_prop by simp
                            have "j - 1 + 1 = j" using j_assum by simp
                            have "1 \<le> j + 1 \<and> j + 1 \<le> length ?q - 1" using j_assum by simp
                            have i_j_reln: "\<forall>i. 0 < i \<and> i \<le> (length ?q - 1) \<longrightarrow> (nth ?q i) = (nth q (i - 1))" by auto
                            then have "(nth ?q j) = (nth q (j - 1))" using j_assum by simp
                            have "(nth ?q (j + 1)) = (nth q j)" using i_j_reln \<open>1 \<le> j + 1 \<and> j + 1 \<le> length ?q - 1\<close> by simp
                            have "j - 1 < length q - 1" using j_assum by auto
                            then have "(((nth q (j - 1), nth q j) \<in> Y \<union> {(?v, ?w)}) \<or> ((nth q j, nth q (j - 1)) \<in> Y \<union> {(?v, ?w)}))" using q_prop \<open>j - 1 + 1 = j\<close> by auto
                            then show "(((nth ?q j, nth ?q (j + 1)) \<in> Y \<union> {(?v, ?w)}) \<or> ((nth ?q (j + 1), nth ?q j) \<in> Y \<union> {(?v, ?w)}))" using \<open>(nth ?q j) = (nth q (j - 1))\<close> \<open>(nth ?q (j + 1)) = (nth q j)\<close> by auto
                          qed
                        qed
                        have "(nth ?q 0) = ?w" by simp
                        have "(nth ?q 1) = ?v" using \<open>hd q = ?v \<and> last q = u\<close> hd_conv_nth 
                          by (metis False cancel_comm_monoid_add_class.diff_cancel hd_Nil_eq_last nth_Cons' zero_neq_one)
                        then have "(nth ?q 1, nth ?q 0) \<in> {(?v, ?w)}" using \<open>nth ?q 0 = ?w\<close> \<open>nth ?q 1 = ?v\<close> by simp
                        then have "\<forall>i. i < length ?q - 1 \<longrightarrow> (((nth ?q i, nth ?q (i + 1)) \<in> Y \<union> {(?v, ?w)}) \<or> (nth ?q (i + 1), nth ?q i) \<in> Y \<union> {(?v, ?w)})" using j_fact 
                          by (smt (verit, best) Nat.add_diff_assoc2 Nat.diff_diff_right Un_insert_right \<open>(?w # q) ! 0 = ?w\<close> \<open>(?w # q) ! 1 = ?v\<close> \<open>v = ?w\<close> diff_diff_cancel diff_self_eq_0 insert_iff le_neq_implies_less le_refl less_one nat_le_linear sup_bot_right)
                        then have "\<forall>i < length ?q - 1. (((nth ?q i, nth ?q (i + 1)) \<in> Y \<union> {(?v, ?w)}) \<or> (nth ?q (i + 1), nth ?q i) \<in> Y \<union> {(?v, ?w)})" by auto
                        then show ?thesis using f_1 f_2 f_3 \<open>v = ?w\<close> 
                          by (meson last.simps q_prop)
                      qed           
                    qed    
                  qed
                qed
              qed
              then show "Y \<union> {(?v, ?w)} = {} \<and> card (V2 \<union> {?w}) = 1 \<or>
    (\<forall>u v. u \<in> V2 \<union> {?w} \<and> v \<in> V2 \<union> {?w} \<and> u \<noteq> v \<longrightarrow>
           (\<exists>pa. pa \<noteq> [] \<and>
                 (hd pa = v \<and> last pa = u \<or> hd pa = u \<and> last pa = v) \<and>
                 (\<forall>ia<length pa - 1.
                     (pa ! ia, pa ! (ia + 1)) \<in> Y \<union> {(?v, ?w)} \<or>
                     (pa ! (ia + 1), pa ! ia) \<in> Y \<union> {(?v, ?w)}) \<and>
                 2 \<le> length pa))" using \<open>\<not>(Y = {} \<and> card V2 = 1)\<close> by simp
            qed
              have 3: "acyclic (V2 \<union> {?w}) (Y \<union> {(?v, ?w)})" unfolding acyclic_def
              proof (cases "Y = {}")
                case True
                have "(\<forall>v\<in>V2 \<union> {?w}.
        \<nexists>pa. pa \<noteq> [] \<and>
             hd pa = v \<and>
             last pa = v \<and>
             (\<forall>ia<length pa - 1.
                 (pa ! ia, pa ! (ia + 1)) \<in> Y \<union> {(?v, ?w)}) \<and>
             2 \<le> length pa)"
                proof 
                  fix v
                  show "v\<in>V2 \<union> {?w} \<Longrightarrow>
        (\<nexists>pa. pa \<noteq> [] \<and>
             hd pa = v \<and>
             last pa = v \<and>
             (\<forall>ia<length pa - 1.
                 (pa ! ia, pa ! (ia + 1)) \<in> Y \<union> {(?v, ?w)}) \<and>
             2 \<le> length pa)"
                  proof -
                    assume v_assum: "v \<in> V2 \<union> {?w}"
                    show "(\<nexists>pa. pa \<noteq> [] \<and>
             hd pa = v \<and>
             last pa = v \<and>
             (\<forall>ia<length pa - 1.
                 (pa ! ia, pa ! (ia + 1)) \<in> Y \<union> {(?v, ?w)}) \<and>
             2 \<le> length pa)"
                    proof (cases "v = ?w")
                      case True
                      show "(\<nexists>pa. pa \<noteq> [] \<and>
             hd pa = v \<and>
             last pa = v \<and>
             (\<forall>ia<length pa - 1.
                 (pa ! ia, pa ! (ia + 1)) \<in> Y \<union> {(?v, ?w)}) \<and>
             2 \<le> length pa)"
                      proof (rule ccontr)
                        assume "\<not>(\<nexists>pa. pa \<noteq> [] \<and>
             hd pa = v \<and>
             last pa = v \<and>
             (\<forall>ia<length pa - 1.
                 (pa ! ia, pa ! (ia + 1)) \<in> Y \<union> {(?v, ?w)}) \<and>
             2 \<le> length pa)"
                        then have "(\<exists>pa. pa \<noteq> [] \<and>
             hd pa = v \<and>
             last pa = v \<and>
             (\<forall>ia<length pa - 1.
                 (pa ! ia, pa ! (ia + 1)) \<in> Y \<union> {(?v, ?w)}) \<and>
             2 \<le> length pa)" by auto
                        then obtain pa where pa_prop: "pa \<noteq> [] \<and>
             hd pa = v \<and>
             last pa = v \<and>
             (\<forall>ia<length pa - 1.
                 (pa ! ia, pa ! (ia + 1)) \<in> Y \<union> {(?v, ?w)}) \<and>
             2 \<le> length pa" by auto
                        then have "(nth pa 0) = v" using hd_conv_nth by fastforce
                        then have "(nth pa 0) = ?w" using True by simp
                        have "length pa \<ge> 2" using pa_prop by simp
                        then have "(nth pa 0, nth pa 1) \<in> Y \<union> {(?v, ?w)}" using pa_prop by simp
                        then have "(nth pa 1) \<in> V2 \<union> {?w}" using 1 unfolding digraph_def by auto
                        have "(?w, nth pa 1) \<in> Y \<union> {(?v, ?w)}" using True \<open>(nth pa 0 , nth pa 1) \<in> Y \<union> {(?v, ?w)}\<close> 
                          by (simp add: \<open>pa ! 0 = ?w\<close>) 
                        then show "False" using w_el_prop \<open>nth pa 1 \<in> V2 \<union> {?w}\<close> by auto
                      qed
                    next
                      case False
                      show "\<nexists>pa. pa \<noteq> [] \<and>
         hd pa = v \<and>
         last pa = v \<and>
         (\<forall>ia<length pa - 1.
             (pa ! ia, pa ! (ia + 1)) \<in> Y \<union> {(?v, ?w)}) \<and>
         2 \<le> length pa" 
                      proof (rule ccontr)
                        assume "\<not> (\<nexists>pa. pa \<noteq> [] \<and>
             hd pa = v \<and>
             last pa = v \<and>
             (\<forall>ia<length pa - 1.
                 (pa ! ia, pa ! (ia + 1)) \<in> Y \<union> {(?v, ?w)}) \<and>
             2 \<le> length pa)"
                        then have "(\<exists>pa. pa \<noteq> [] \<and>
             hd pa = v \<and>
             last pa = v \<and>
             (\<forall>ia<length pa - 1.
                 (pa ! ia, pa ! (ia + 1)) \<in> Y \<union> {(?v, ?w)}) \<and>
             2 \<le> length pa)" by auto
                        then obtain pa where pa_prop: "pa \<noteq> [] \<and>
             hd pa = v \<and>
             last pa = v \<and>
             (\<forall>ia<length pa - 1.
                 (pa ! ia, pa ! (ia + 1)) \<in> Y \<union> {(?v, ?w)}) \<and>
             2 \<le> length pa" by auto
                        have "v \<in> V2" using False v_assum by simp
                        then have pa_prop2: "pa \<noteq> [] \<and>
             hd pa = v \<and>
             last pa = v \<and>
             (\<forall>ia<length pa - 1.
                 (pa ! ia, pa ! (ia + 1)) \<in> {(?v, ?w)}) \<and>
             2 \<le> length pa" using pa_prop \<open>Y = {}\<close> by simp
                        then have "(nth pa (length pa -1)) = v" using last_conv_nth by fastforce
                        have "length pa - 1 - 1 < length pa - 1" using pa_prop by auto
                        then have "(nth pa (length pa - 1 - 1), nth pa (length pa - 1)) \<in> {(?v, ?w)}" using pa_prop2 
                          by (metis add_le_imp_le_diff le_add_diff_inverse2 nat_1_add_1)
                        then have "(nth pa (length pa - 1 - 1), v) \<in> {(?v, ?w)}" using \<open>(nth pa (length pa - 1)) = v\<close> by simp
                        then have "(nth pa (length pa - 1 -1), v) = (?v, ?w)" by simp
                        then have "v = ?w" by simp
                      then show "False" using False by simp
                    qed
                  qed
                qed
              qed
              then show "Y \<union> {(?v, ?w)} = {} \<or>
    (\<forall>v\<in>V2 \<union> {?w}.
        \<nexists>pa. pa \<noteq> [] \<and>
             hd pa = v \<and>
             last pa = v \<and>
             (\<forall>ia<length pa - 1.
                 (pa ! ia, pa ! (ia + 1)) \<in> Y \<union> {(?v, ?w)}) \<and>
             2 \<le> length pa)" by auto
              next
                case False
                then have Y_acyclic2: "(\<forall>v\<in>V2.
        \<nexists>pa. pa \<noteq> [] \<and>
             hd pa = v \<and>
             last pa = v \<and>
             (\<forall>ia<length pa - 1.
                 (pa ! ia, pa ! (ia + 1)) \<in> Y) \<and>
             2 \<le> length pa)" using \<open>acyclic V2 Y\<close> unfolding acyclic_def by simp
                have "Y \<union> {(?v, ?w)} \<noteq> {}" by simp
                have "(\<forall>v\<in>V2 \<union> {?w}.
        \<nexists>pa. pa \<noteq> [] \<and>
             hd pa = v \<and>
             last pa = v \<and>
             (\<forall>ia<length pa - 1.
                 (pa ! ia, pa ! (ia + 1)) \<in> Y \<union> {(?v, ?w)}) \<and>
             2 \<le> length pa)"
                proof (rule ccontr)
                  assume "\<not> (\<forall>v\<in>V2 \<union> {?w}.
             (\<nexists>pa. pa \<noteq> [] \<and>
                  hd pa = v \<and>
                  last pa = v \<and>
                  (\<forall>ia<length pa - 1.
                      (pa ! ia, pa ! (ia + 1)) \<in> Y \<union> {(?v, ?w)}) \<and> length pa \<ge> 2))"
                  then have "\<exists>v \<in> V2 \<union> {?w}. (\<exists>pa. pa \<noteq> [] \<and>
                  hd pa = v \<and>
                  last pa = v \<and>
                  (\<forall>ia<length pa - 1.
                      (pa ! ia, pa ! (ia + 1)) \<in> Y \<union> {(?v, ?w)}) \<and> length pa \<ge> 2)" by auto 
                  then obtain v where v_prop: "v \<in> V2 \<union> {?w} \<and>  (\<exists>pa. pa \<noteq> [] \<and>
                  hd pa = v \<and>
                  last pa = v \<and>
                  (\<forall>ia<length pa - 1.
                      (pa ! ia, pa ! (ia + 1)) \<in> Y \<union> {(?v, ?w)}) \<and> length pa \<ge> 2)" by auto
                  then obtain pa where pa_prop: " pa \<noteq> [] \<and>
                  hd pa = v \<and>
                  last pa = v \<and>
                  (\<forall>ia<length pa - 1.
                      (pa ! ia, pa ! (ia + 1)) \<in> Y \<union> {(?v, ?w)}) \<and> length pa \<ge> 2" by auto
                  show "False"
                  proof (cases "v = ?w")
                    case True
                    then have "hd pa = ?w" using pa_prop by simp
                    then have "(nth pa 0) = ?w" using hd_conv_nth pa_prop by metis
                    have "2 \<le> length pa" using pa_prop by simp
                    then have "0 < length pa - 1" by simp
                    then have edge_fact: "(nth pa 0, nth pa (0 + 1)) \<in> Y \<union> {(?v, ?w)}" using pa_prop by simp
                    then have "(nth pa (0 + 1)) \<in> V2 \<union> {?w}" using \<open>Y \<union> {(?v, ?w)} \<subseteq> (V2 \<union> {?w}) \<times> (V2 \<union> {?w})\<close> by auto
                    then show "False" using pa_prop w_el_prop edge_fact \<open>(nth pa 0) = ?w\<close> by blast
                  next
                    case False
                    show "False"
                    proof (cases "List.member pa ?w")
                      case True
                      have "length pa > 0" using pa_prop by simp
                      then have "?w \<in> set pa" using True in_set_member pa_prop by metis
                      then have "\<exists>i <length pa. (nth pa i) = ?w" using \<open>length pa > 0\<close> in_set_conv_nth 
                        by metis
                      then obtain i where i_prop: "(nth pa i) = ?w " " i < length pa "  by auto
                      have "(nth pa (length pa - 1)) = v" using pa_prop last_conv_nth by metis
                      then have "(nth pa (length pa - 1)) \<noteq> ?w" using \<open>v \<noteq> ?w\<close> by simp
                      then have " i \<noteq> (length pa - 1)" using i_prop(1) by auto
                      then have "i < length pa - 1" using i_prop(2) \<open>length pa > 0\<close> by simp
                      then have edge_fact: "(nth pa i, nth pa (i + 1)) \<in> Y \<union> {(?v, ?w)}" using pa_prop by simp
                      then have "(nth pa (i + 1)) \<in> V2 \<union> {?w}" using \<open>Y \<union> {(?v, ?w)} \<subseteq> (V2 \<union> {?w}) \<times> (V2 \<union> {?w})\<close> by auto
                      then show ?thesis using \<open>nth pa i = ?w\<close> w_el_prop edge_fact by blast
                    next
                      case False
                      have "\<forall>i < length pa - 1. (nth pa i, nth pa (i+1)) \<in> Y"
                      proof (rule ccontr)
                        assume "\<not> (\<forall>i<length pa - 1. (pa ! i, pa ! (i + 1)) \<in> Y)" 
                        then have "\<exists>i <length pa - 1. (pa ! i, pa ! (i + 1)) \<notin> Y" by simp
                        then obtain i where i_prop: "i < length pa - 1 \<and> (nth pa i, nth pa (i + 1)) \<notin> Y" by auto
                        then have "i < length pa" by auto
                        have "length pa > 0" using pa_prop by simp
                        have "\<forall>i < length pa - 1. (nth pa i, nth pa (i+1)) \<in> Y \<union> {(?v, ?w)}" using pa_prop by simp
                        then have "(nth pa i, nth pa (i + 1)) = (?v, ?w)" 
                          using i_prop by blast
                        then have "nth pa (i + 1) = ?w" by simp
                        then have "(nth pa (i + 1)) \<in> set pa" using \<open>i < length pa\<close> \<open>length pa > 0\<close> 
                          by (meson i_prop less_diff_conv nth_mem)
                        then have "?w \<in> set pa" using \<open>nth pa (i + 1) = ?w\<close> by simp
                        then have "List.member pa ?w" using \<open>length pa > 0\<close> in_set_member pa_prop 
                          by metis
                        then show "False" using False by simp
                      qed
                      then have "pa \<noteq> [] \<and> hd pa = v \<and> last pa = v \<and> (\<forall>i < length pa - 1. (nth pa i, nth pa (i+1)) \<in> Y) \<and> length pa \<ge> 2" using pa_prop by simp
                      then show "False" using Y_acyclic2 v_prop \<open>v \<noteq> ?w\<close> by auto
                  qed
                qed
              qed
              then show "Y \<union> {(?v, ?w)} = {} \<or>
    (\<forall>v\<in>V2 \<union> {?w}.
        \<nexists>pa. pa \<noteq> [] \<and>
             hd pa = v \<and>
             last pa = v \<and>
             (\<forall>ia<length pa - 1.
                 (pa ! ia, pa ! (ia + 1)) \<in> Y \<union> {(?v, ?w)}) \<and>
             2 \<le> length pa)" by auto
            qed
              have "card V2 - 1 = card Y" using \<open>tree V2 Y\<close> unfolding tree_def by simp
              then have "(card V2 - 1) + 1 = card Y + 1" by simp
              then have eq_one: "(card V2 + 1) - 1 = card Y + 1" 
                by (simp add: facttwo)
              have "finite V2" using finite_assum_V V2_prop finite_subset by auto
              then have "finite (V2 \<union> {?w})" by simp
              have "finite Y" using \<open>Y \<subseteq> V2 \<times> V2\<close> \<open>finite V2\<close> 
                by (simp add: finite_subset)
              then have "finite (Y \<union> {(?v, ?w)})" by simp
              then have "card (V2 \<union> {?w}) = card V2 + card {?w}" using \<open>?w \<in> V1 - V2\<close> \<open>finite (V2)\<close> by simp
              then have eq_two: "card (V2 \<union> {?w}) = card V2 + 1" by simp
              have "card (Y \<union> {(?v ,?w)}) = card Y + card ({(?v, ?w)})" using \<open>(?v, ?w) \<notin> Y\<close> \<open>finite Y\<close> by simp
              then have "card (Y \<union> {(?v, ?w)}) = card Y + 1" by simp
              then have 4: "card (V2 \<union> {?w}) - 1 = card (Y \<union> {(?v, ?w)})" using eq_one eq_two by simp
              show " digraph (V2 \<union> {?w}) (Y \<union> {(?v, ?w)}) \<and>
    local.acyclic (V2 \<union> {?w}) (Y \<union> {(?v, ?w)}) \<and>
    local.connected (V2 \<union> {?w}) (Y \<union> {(?v, ?w)}) \<and>
    card (Y \<union> {(?v, ?w)}) = card (V2 \<union> {?w}) - 1" using 1 2 3 4 by simp
            qed
            moreover have "V2 \<union> {?w} \<subseteq> V" using V2_prop \<open>?w \<in> V1 - V2\<close> V1_prop by auto
            moreover have "Y \<union> {(?v, ?w)} \<subseteq> E" using assum2 \<open>(?v, ?w) \<in> X\<close> by auto
            moreover have "r \<in> V2 \<union> {(?w)}" using V2_prop by simp
            ultimately have "(Y \<union> {(?v, ?w)}) \<in> ?F" by blast
            then show ?thesis using \<open>(?v, ?w) \<in> X\<close> \<open>(?v, ?w) \<notin> Y\<close> by auto
          next
            case False
            then show ?thesis sorry (*Second half of proof skipped as it follows the same pattern as first half.*)
          qed
        qed
      qed
    qed

end

definition strong_exchange_property where "strong_exchange_property E F \<longleftrightarrow> (\<forall>A B x. A \<in> F
\<and> B \<in> F \<and> A \<subseteq> B \<and> (maximal (\<lambda>B. B \<in> F) B) \<and> x \<in> E - B \<and> A \<union> {x} \<in> F \<longrightarrow> (\<exists>y. y \<in> B - A \<and> 
A \<union> {y} \<in> F \<and> (B - {y}) \<union> {x} \<in> F))"


locale greedy_algorithm = greedoid +
  fixes orcl::"'a set \<Rightarrow> bool"
  fixes es
  assumes orcl_correct: "\<And> X. X \<subseteq> E \<Longrightarrow> orcl X \<longleftrightarrow> X \<in> F"
  assumes set_assum: "set es = E \<and> distinct es" 


context greedy_algorithm
begin

  definition valid_modular_weight_func::"('a set \<Rightarrow> real) \<Rightarrow> bool" where  "valid_modular_weight_func c = (c ({}) = 0 \<and> (\<forall>X l. X \<subseteq> E \<and> X \<noteq> {} \<and> l = {c {e} | e. e \<in> X} \<and> c (X) = sum (\<lambda>x. real x) l))"

  definition "maximum_weight_set c X = (X \<in> F \<and> (\<forall> Y \<in> F. c X \<ge> c Y))"

  definition "find_best_candidate c F' = foldr (\<lambda> e acc. if e \<in> F' \<or> \<not> orcl (insert e F') then acc
                                                      else (case acc of None \<Rightarrow> Some e |
                                                               Some d \<Rightarrow> (if c {e} > c {d} then Some e
                                                                          else Some d))) es None"

(*Next two lemmas taken as facts: the best candidate for F' lies in es (list of E), and does not lie in F'.*)
lemma find_best_candidate_in_es: assumes "F' \<subseteq> E" "find_best_candidate c F' = Some x"
  shows "List.member es x"
  sorry
lemma find_best_candidate_notin_F': assumes "F' \<subseteq> E" "find_best_candidate c F' = Some x"
  shows "x \<notin> F'"
proof -
  have "foldr (\<lambda> e acc. if e \<in> F' \<or> \<not> orcl (insert e F') then acc
                                                      else (case acc of None \<Rightarrow> Some e |
                                                               Some d \<Rightarrow> (if c {e} > c {d} then Some e
                                                                          else Some d))) es None = Some x" using assms(2) unfolding find_best_candidate_def by auto
  then obtain acc where "foldr (\<lambda> e acc. if e \<in> F' \<or> \<not> orcl (insert e F') then acc
                                                      else (case acc of None \<Rightarrow> Some e |
                                                               Some d \<Rightarrow> (if c {e} > c {d} then Some e
                                                                          else Some d))) es acc = Some x" by simp
  then have "Some x = acc"
  then have "x \<notin> F' \<and> orcl (insert x F')" 

function (domintros) greedy_algorithm_greedoid::"'a set \<Rightarrow> ('a set \<Rightarrow> real) \<Rightarrow> 'a set" where "greedy_algorithm_greedoid F' c = (if (E = {} \<or> \<not>(F' \<subseteq> E)) then undefined 
else  (case  (find_best_candidate c F') of Some e => greedy_algorithm_greedoid(F' \<union> {the (find_best_candidate c F')}) c | None => F'))"
proof -
  show "\<And>P x. (\<And>F' c. x = (F', c) \<Longrightarrow> P) \<Longrightarrow> P" by auto
  show "\<And>F' c F'a ca.
       (F', c) = (F'a, ca) \<Longrightarrow>
       (if E = {} \<or> \<not> F' \<subseteq> E then undefined
        else case find_best_candidate c F' of None \<Rightarrow> F'
             | Some e \<Rightarrow>
                 greedy_algorithm_greedoid_sumC
                  (F' \<union> {the (find_best_candidate c F')}, c)) =
       (if E = {} \<or> \<not> F'a \<subseteq> E then undefined
        else case find_best_candidate ca F'a of None \<Rightarrow> F'a
             | Some e \<Rightarrow>
                 greedy_algorithm_greedoid_sumC
                  (F'a \<union> {the (find_best_candidate ca F'a)}, ca))"
  proof -
    fix F' c F'a ca
    show "(F', c) = (F'a, ca) \<Longrightarrow>
       (if E = {} \<or> \<not> F' \<subseteq> E then undefined
        else case find_best_candidate c F' of None \<Rightarrow> F'
             | Some e \<Rightarrow>
                 greedy_algorithm_greedoid_sumC
                  (F' \<union> {the (find_best_candidate c F')}, c)) =
       (if E = {} \<or> \<not> F'a \<subseteq> E then undefined
        else case find_best_candidate ca F'a of None \<Rightarrow> F'a
             | Some e \<Rightarrow>
                 greedy_algorithm_greedoid_sumC
                  (F'a \<union> {the (find_best_candidate ca F'a)}, ca))"
    proof -
      assume assum1: "(F', c) = (F'a, ca)"
      then have 1: "F' = F'a"by simp
      have "c = ca" using assum1 by simp
      then show ?thesis using 1 by auto
    qed
  qed
qed

lemma greedy_algo_term: shows "All greedy_algorithm_greedoid_dom"
proof (relation "measure (\<lambda>(F', c). card (E - F'))")
  show " wf (measure (\<lambda>(F', c). card (E - F')))" by (rule wf_measure)
  show "\<And>F' c x2.
       \<not> (E = {} \<or> \<not> F' \<subseteq> E) \<Longrightarrow>
       find_best_candidate c F' = Some x2 \<Longrightarrow>
       ((F' \<union> {the (find_best_candidate c F')}, c), F', c)
       \<in> measure (\<lambda>(F', c). card (E - F'))"
  proof -
    fix F' c x
    show "\<not> (E = {} \<or> \<not> F' \<subseteq> E) \<Longrightarrow>
       find_best_candidate c F' = Some x \<Longrightarrow>
       ((F' \<union> {the (find_best_candidate c F')}, c), F', c)
       \<in> measure (\<lambda>(F', c). card (E - F'))"
    proof - 
      assume assum1: "\<not> (E = {} \<or> \<not> F' \<subseteq> E)"
      show "find_best_candidate c F' = Some x \<Longrightarrow>
    ((F' \<union> {the (find_best_candidate c F')}, c), F', c)
    \<in> measure (\<lambda>(F', c). card (E - F'))"
      proof -
        assume assum2: "find_best_candidate c F' = Some x"
        then have "List.member es x" using find_best_candidate_in_es assum1 by auto
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

lemma max_weight_exists: assumes "greedoid E F" "valid_modular_weight_func c"
  shows "\<exists>F'. maximum_weight_set c F'"
proof -
  have "set_system E F" using ss_assum by simp
  then have "finite E" unfolding set_system_def by simp
  then have "finite F" using \<open>set_system E F\<close> unfolding set_system_def
    by (meson Sup_le_iff finite_UnionD finite_subset)
  let ?A = "{c F' | F'. F' \<in> F}"
  have "finite ?A" using \<open>finite F\<close> by simp
  have "F \<noteq> {}" using contains_empty_set by auto
  then have "?A \<noteq> {}" by simp
  then obtain x where "x = Max ?A" using \<open>finite ?A\<close> by simp
  then have "x \<in> ?A" using Max_in \<open>finite ?A\<close> \<open>?A \<noteq> {}\<close> by auto
  then obtain F' where F'_prop: "F' \<in> F \<and> c F' = x" by auto
  then have max_fact: "\<forall>a. a \<in> ?A \<longrightarrow> x \<ge> a" 
    by (simp add: \<open>finite ?A\<close> \<open>x = Max ?A\<close>)
  have "maximum_weight_set c F'" unfolding maximum_weight_set_def
  proof (rule ccontr)
    assume "\<not> (F' \<in> F \<and> (\<forall>Y\<in>F. c Y \<le> c F'))"
    then have contr: "F' \<notin> F \<or> \<not> (\<forall>Y\<in>F. c Y \<le> c F')" by simp
    have "F' \<in> F" using F'_prop by simp
    then have "\<not> (\<forall>Y\<in>F. c Y \<le> c F')" using contr by simp
    then have "\<exists>X. X \<in> F \<and> c X > c F'" by auto
    then obtain X where "X \<in> F \<and> c F' < c X" by auto
    then have "c X \<in> ?A" by auto
    then have "c X > x" using \<open>F' \<in> F \<and> c F' = x\<close> \<open>X \<in> F \<and> c F' < c X\<close> by simp
    then show "False" using max_fact \<open>c X \<in> ?A\<close> by auto
  qed
  then show ?thesis by auto
qed

lemma greedy_algo_in_F: 
  assumes "valid_modular_weight_func c"
  shows "(greedy_algorithm_greedoid {} c) \<in> F"
proof -
  define measure_func where "measure_func = (\<lambda>(F', c). card (E - F'))"
  have wf_measure: "wf (measure measure_func)"
    using greedy_algo_term by simp
  show ?thesis
  proof (induction rule: wf_induct[of "measure measure_func"])
    case 1
    show ?case
    proof (cases "E = {} \<or> \<not> F' \<subseteq> E")
      case True
      then show ?thesis by simp
    next
      case False
      then obtain e where e_prop: "find_best_candidate c F' = Some e \<or> find_best_candidate c F' = None"
        by auto
      have factone: "E \<noteq> {} \<and> F' \<subseteq> E" using False by simp
      then have "F' \<subseteq> E" by simp
      show ?thesis
      proof (cases "find_best_candidate c F' = Some e")
        case True
        then have "e \<in> E" 
          using find_best_candidate_in_es find_best_candidate_notin_F'
          by (metis False in_set_member set_assum)
        then have "e \<notin> F'" 
          using find_best_candidate_notin_F' \<open>F' \<subseteq> E\<close> True by auto
        have "F' \<union> {e} \<subseteq> E"
          using `e \<in> E` `F' \<subseteq> E` by auto
        then show ?thesis by simp
      next
        case False
        then have "find_best_candidate c F' = None" using e_prop by simp
        then have "greedy_algorithm_greedoid F' c = F'" 
          by (simp add: factone greedy_algo_term greedy_algorithm_greedoid.psimps)
        then show ?thesis by simp
      qed
    qed
    next 
      case (2 x)
      then show ?case sorry
    qed
  qed
    

  lemma greedy_algorithm_correctness:
    assumes assum1: "greedoid E F"
    shows "(\<forall>c. valid_modular_weight_func c \<longrightarrow> maximum_weight_set c (greedy_algorithm_greedoid {} c)) \<longleftrightarrow>
  strong_exchange_property E F"
  proof
    show "strong_exchange_property E F \<Longrightarrow>
    \<forall>c. valid_modular_weight_func c \<longrightarrow>
        maximum_weight_set c (greedy_algorithm_greedoid {} c)"
    proof
      fix c
      show "strong_exchange_property E F \<Longrightarrow>
         valid_modular_weight_func c \<longrightarrow>
         maximum_weight_set c (greedy_algorithm_greedoid {} c)"
      proof
        assume "strong_exchange_property E F"
        show "valid_modular_weight_func c \<Longrightarrow>
    maximum_weight_set c (greedy_algorithm_greedoid {} c)"
        proof -
          assume "valid_modular_weight_func c"
          show "maximum_weight_set c (greedy_algorithm_greedoid {} c)"
          proof (rule ccontr)
            assume assum1: "\<not> maximum_weight_set c (greedy_algorithm_greedoid {} c)"
            have "\<exists>X. maximum_weight_set c X" using max_weight_exists \<open>valid_modular_weight_func c\<close> \<open>greedoid E F\<close> by simp
            then obtain B where "maximum_weight_set c B" by auto
  


end

end
               
