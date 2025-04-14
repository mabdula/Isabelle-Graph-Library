theory Greedoids
  imports Main Complex_Main
begin    

subsection \<open>Auxiliary Lemmas\<close>

lemma max_n: "(\<And> n. P n \<Longrightarrow> n \<le> bound) \<Longrightarrow> P (n::nat) \<Longrightarrow> (\<exists> nmax. P nmax \<and> (\<nexists> m. m > nmax \<and> P m))"
  by (metis bounded_Max_nat leD)

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

section \<open>Definitions \<close>

definition "set_system E F = (finite E \<and> (\<forall> X \<in> F. X \<subseteq> E))"

definition accessible where "accessible E F =
    (set_system E F \<and> ({} \<in> F) \<and> (\<forall>X. (X \<in> F - {{}}) \<longrightarrow> (\<exists>x \<in> X.  X - {x} \<in> F)))"

definition closed_under_union where "closed_under_union F =
             (\<forall>X Y. X \<in> F \<and> Y \<in> F \<longrightarrow> X \<union> Y \<in> F)"

definition basis_element where "basis_element P Z =
       (P Z \<and> (\<nexists> X. X \<supset> Z \<and> P X))"

definition strong_exchange_property where "strong_exchange_property E F \<longleftrightarrow> 
(\<forall>A B x. (A \<in> F \<and> B \<in> F \<and> A \<subseteq> B \<and> (basis_element (\<lambda>B. B \<in> F) B) \<and> x \<in> E - B \<and> A \<union> {x} \<in> F) 
      \<longrightarrow> (\<exists>y \<in> B - A. A \<union> {y} \<in> F \<and> (B - {y}) \<union> {x} \<in> F))"


lemma  strong_exchange_propertyE: 
 "strong_exchange_property E F \<Longrightarrow> 
  ((\<And> A B x. A \<in> F \<Longrightarrow> B \<in> F \<Longrightarrow> A \<subseteq> B \<Longrightarrow> (basis_element (\<lambda>B. B \<in> F) B) \<Longrightarrow> x \<in> E - B \<Longrightarrow> A \<union> {x} \<in> F 
      \<Longrightarrow> (\<exists>y \<in> B - A. A \<union> {y} \<in> F \<and> (B - {y}) \<union> {x} \<in> F))
 ==> P) \<Longrightarrow> P"
 by(auto simp add: strong_exchange_property_def)

section \<open>Basic Lemmas on Set Systems and Accessibility\<close>

lemma exists_maximal: 
  assumes "set_system E F" "X \<in> F" "Y \<in> F" 
  shows "\<exists>Z. basis_element (\<lambda> Z. Z \<supseteq> X \<and> Z \<subseteq> X \<union> Y \<and> Z \<in> F) Z"
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
  have "basis_element (\<lambda> Z. Z \<supseteq> X \<and> Z \<subseteq> X \<union> Y \<and> Z \<in> F) Z"
  proof (rule ccontr)
    assume "\<not> basis_element (\<lambda>Z. X \<subseteq> Z \<and> Z \<subseteq> X \<union> Y \<and> Z \<in> F) Z" 
    then have "\<exists>Z'. Z' \<supset> Z \<and> X \<subseteq> Z' \<and> Z' \<subseteq> X \<union> Y \<and> Z' \<in> F" unfolding basis_element_def 
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

lemma accessible_characterisation: 
  assumes "set_system E F" "{} \<in> F"
  shows "accessible E F \<longleftrightarrow> (\<forall>X. X \<in> F \<longrightarrow> (\<exists>l. set l = X \<and>  (\<forall>i. i \<le> length l \<longrightarrow> set (take i l) \<in> F) \<and> distinct l))"
proof 
  show "accessible E F \<Longrightarrow>
    \<forall>X. X \<in> F \<longrightarrow> (\<exists>l. set l = X \<and> (\<forall>i\<le>length l. set (take i l) \<in> F) \<and> distinct l)"
  proof -
    assume "accessible E F"
    show "\<forall>X. X \<in> F \<longrightarrow> (\<exists>l. set l = X \<and> (\<forall>i\<le>length l. set (take i l) \<in> F) \<and> distinct l)"
    proof
      fix X
      show "X \<in> F \<longrightarrow> (\<exists>l. set l = X \<and> (\<forall>i\<le>length l. set (take i l) \<in> F) \<and> distinct l)"
      proof
        assume "X \<in> F"
  have "set_system E F" using assms(1) unfolding accessible_def by simp
  then have "finite E" unfolding set_system_def by simp
  have "X \<subseteq> E" using assms \<open>X \<in> F\<close> unfolding set_system_def by auto
  then have "finite X" using finite_subset \<open>finite E\<close> by auto
  obtain k where "card X = k" using \<open>finite X\<close> by simp 
  then show "(\<exists>l. set l = X \<and> (\<forall>i\<le>length l. set (take i l) \<in> F) \<and> distinct l)" using assms \<open>X \<in> F\<close> \<open>X \<subseteq> E\<close>
  proof (induct k arbitrary: X rule: less_induct)
    case (less a)
    then have "card X = a" by simp
    have "X \<in> F" using \<open>X \<in> F\<close> by auto
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
      have "{} \<in> F" using assms \<open>accessible E F\<close> unfolding accessible_def by simp
      then have "\<forall>i. i \<le> length [] \<longrightarrow> set (take i l) \<in> F" using l_prop by simp
      then show ?thesis using \<open>l = []\<close> l_prop by simp
    next
      case False
      then have "X \<noteq> {}" using \<open>card X = a\<close> by auto
      then have "X \<in> F - {{}}" using \<open>X \<in> F\<close> by simp
      then obtain x where "x \<in> X" "X - {x} \<in> F" using \<open>X \<in> F\<close> \<open>accessible E F\<close> unfolding accessible_def by auto
      have "finite {x}" by simp
      then have factone: "finite (X - {x})" using \<open>finite X\<close> by simp
      have "(X - {x}) \<subset>  X" using \<open>x \<in> X\<close> by auto
      then have "card (X - {x}) < card (X)" by (meson \<open>finite X\<close> psubset_card_mono)
      then have "card (X - {x}) < a" using \<open>card X = a\<close> by simp 
      have "X - {x} \<subseteq> E" using \<open>X - {x} \<subset> X\<close> \<open>X \<subseteq> E\<close> by simp
      then have "\<exists>l. set l = X - {x} \<and> (\<forall>i. i \<le> length l \<longrightarrow> set (take i l) \<in> F) \<and> distinct l" using \<open>X - {x} \<in> F\<close> 
        using less.hyps \<open>X - {x} \<in> F\<close> \<open>card (X - {x}) < a\<close> assms by simp
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
qed
qed
  show "\<forall>X. X \<in> F \<longrightarrow>
        (\<exists>l. set l = X \<and> (\<forall>i\<le>length l. set (take i l) \<in> F) \<and> distinct l) \<Longrightarrow>
    accessible E F"
    unfolding accessible_def
  proof 
    show "\<forall>X. X \<in> F \<longrightarrow>
        (\<exists>l. set l = X \<and> (\<forall>i\<le>length l. set (take i l) \<in> F) \<and> distinct l) \<Longrightarrow>
    set_system E F" using assms by simp
    show "\<forall>X. X \<in> F \<longrightarrow>
        (\<exists>l. set l = X \<and> (\<forall>i\<le>length l. set (take i l) \<in> F) \<and> distinct l) \<Longrightarrow>
    {} \<in> F \<and> (\<forall>X. X \<in> F - {{}} \<longrightarrow> (\<exists>x\<in>X. X - {x} \<in> F))"
    proof 
      show "\<forall>X. X \<in> F \<longrightarrow>
        (\<exists>l. set l = X \<and> (\<forall>i\<le>length l. set (take i l) \<in> F) \<and> distinct l) \<Longrightarrow>
    {} \<in> F" using assms by simp
      show "\<forall>X. X \<in> F \<longrightarrow>
        (\<exists>l. set l = X \<and> (\<forall>i\<le>length l. set (take i l) \<in> F) \<and> distinct l) \<Longrightarrow>
    \<forall>X. X \<in> F - {{}} \<longrightarrow> (\<exists>x\<in>X. X - {x} \<in> F)"
      proof -
        assume assum1: "\<forall>X. X \<in> F \<longrightarrow>
        (\<exists>l. set l = X \<and> (\<forall>i\<le>length l. set (take i l) \<in> F) \<and> distinct l)"
        show "\<forall>X. X \<in> F - {{}} \<longrightarrow> (\<exists>x\<in>X. X - {x} \<in> F)"
        proof
          fix X
          show "X \<in> F - {{}} \<longrightarrow> (\<exists>x\<in>X. X - {x} \<in> F)"
          proof
            assume "X \<in> F - {{}}"
            then have "X \<noteq> {}" by simp
            then have "(\<exists>l. set l = X \<and> (\<forall>i\<le>length l. set (take i l) \<in> F) \<and> distinct l)" using assum1 \<open>X \<in> F - {{}}\<close> by simp
            then obtain l where l_prop: "set l = X \<and> (\<forall>i\<le>length l. set (take i l) \<in> F) \<and> distinct l" by auto
            then have "l \<noteq> []" using \<open>X \<noteq> {}\<close> by auto
            then obtain x where "(nth l (length l - 1)) = x" by simp
            then have "set (take (length l) l) \<in> F" using l_prop by auto
            have "length l > 0" using \<open>l \<noteq> []\<close> by simp
            then have "length l - 1 < length l" by simp
            then have factone: "(set (take (length l - 1) l)) \<union> {nth l (length l - 1)} = set (take (length l) l)" 
              using set_take_union_nth by fastforce
            have facttwo: "nth l (length l - 1) \<notin> set (take (length l - 1) l)" 
            proof
              assume assum2: "l ! (length l - 1) \<in> set (take (length l - 1) l)"
              then have "(take (length l - 1)  l) \<noteq> []" by auto
              then have assum3: "List.member (take (length l - 1) l) (nth l (length l - 1))" using in_set_member \<open>l \<noteq> []\<close>
                assum2 by fast
              have "l = (take (length l - 1) l) @ [nth l (length l - 1)]" using \<open>l \<noteq> []\<close> 
                by (metis Suc_diff_1 \<open>0 < length l\<close> \<open>length l - 1 < length l\<close> order_refl take_Suc_conv_app_nth take_all_iff)
              then have "\<not> (distinct l)"
                using assum2 distinct_take not_distinct_conv_prefix by blast
              then show False using l_prop by simp
            qed
            have "set (take (length l - 1) l) \<in> F" using l_prop by simp
            then have  "((set (take (length l) l)) - {nth l (length l - 1)}) \<in> F" using factone facttwo 
              by (metis Diff_insert_absorb Un_empty_right Un_insert_right)
            then have "X - {x} \<in> F" using l_prop \<open>nth l (length l - 1) = x\<close> by simp
            have "x \<in> X" using l_prop \<open>nth l (length l - 1) = x\<close> in_set_member \<open>l \<noteq> []\<close> by auto
            then show "\<exists>x\<in>X. X - {x} \<in> F" using \<open>X - {x} \<in> F\<close> by auto
          qed
        qed
      qed
    qed
  qed
qed

lemma list_from_accessible:
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
          have "\<exists>Z. basis_element (\<lambda> Z. Z \<supseteq> X \<and> Z \<subseteq> X \<union> Y \<and> Z \<in> F) Z" using exists_maximal
              \<open>X \<in> F \<and> Y \<in> F\<close> \<open>set_system E F\<close> by auto
          then obtain Z where z_prop: "basis_element (\<lambda> Z. Z \<supseteq> X \<and> Z \<subseteq> X \<union> Y \<and> Z \<in> F) Z" by blast
          then have z_props: "Z \<supseteq> X \<and> Z \<subseteq> X \<union> Y \<and> Z \<in> F" unfolding basis_element_def by simp
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
                using \<open>Y - Z \<noteq> {}\<close> \<open>Y \<in> F\<close> list_from_accessible \<open>Y \<subseteq> E\<close> assum1 by blast
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
              then show "False"  using fact_three \<open>Z \<union> {y} \<in> F\<close> z_prop fact_four unfolding basis_element_def by blast
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

section \<open>Greedoids\<close>

definition antimatroid where "antimatroid E F \<longleftrightarrow> accessible E F \<and> closed_under_union F"

locale greedoid =
  fixes E :: "'a set"
  fixes F :: "'a set set"
  assumes contains_empty_set: "{} \<in> F"
  assumes third_condition: "\<And> X Y. (X \<in> F) \<Longrightarrow> (Y \<in> F) \<Longrightarrow> (card X > card Y) \<Longrightarrow> \<exists>x \<in> X - Y.  Y \<union> {x} \<in> F"
  assumes ss_assum: "set_system E F"


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

  have 4: "\<And>X Y. X \<in> F \<and> Y \<in> F \<and> card Y < card X \<Longrightarrow> (\<exists>x \<in> X - Y.  Y \<union> {x} \<in> F)"
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
      then have "\<exists> l. set l = X \<and> (\<forall>i. i \<le> length l \<longrightarrow> set (take i l) \<in> F) \<and> distinct l"  using \<open>X \<in> F\<close> \<open>accessible E F\<close> list_from_accessible \<open>X \<subseteq> E\<close> by auto
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
  thus "\<And>X Y. X \<in> F \<Longrightarrow> Y \<in> F \<Longrightarrow> card Y < card X \<Longrightarrow> \<exists>x\<in>X - Y. Y \<union> {x} \<in> F"
    by simp
qed


context greedoid
begin

lemma greedoid_accessible: "accessible E F" 
  unfolding accessible_def
proof
    note assms = greedoid_axioms
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

section \<open>Closure Operator on Accessible Set Systems\<close>

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


end