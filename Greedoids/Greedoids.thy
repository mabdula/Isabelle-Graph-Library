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

definition "accessible E F =
    (set_system E F \<and> ({} \<in> F) \<and> (\<forall>X. (X \<in> F - {{}}) \<longrightarrow> (\<exists>x \<in> X.  X - {x} \<in> F)))"

definition "closed_under_union F = (\<forall>X Y. X \<in> F \<and> Y \<in> F \<longrightarrow> X \<union> Y \<in> F)"

definition "maximal P Z = (P Z \<and> (\<nexists> X. X \<supset> Z \<and> P X))"

definition "basis F Z = ( Z \<in> F \<and> (\<nexists> X. X \<supset> Z \<and>  X \<in> F))"

lemma basis_alt_def: "basis F Z = maximal (\<lambda> X. X \<in> F) Z"
  by(auto simp add:  basis_def maximal_def)

definition "antimatroid E F = ( accessible E F \<and> closed_under_union F)"

definition "valid_modular_weight_func E (c::'a set \<Rightarrow> real) = 
               (\<forall> X Y. X \<subseteq> E \<and> Y \<subseteq> E \<longrightarrow> c (X \<union> Y) = c X +  c Y - c (X \<inter> Y))"

definition "strong_exchange_property E F =
(\<forall>A B x. (A \<in> F \<and> B \<in> F \<and> A \<subseteq> B \<and> (basis F B) \<and> x \<in> E - B \<and> A \<union> {x} \<in> F) 
      \<longrightarrow> (\<exists>y \<in> B - A. A \<union> {y} \<in> F \<and> (B - {y}) \<union> {x} \<in> F))"

definition "empty_minimal E c = (\<forall> X \<subseteq> E. c X \<ge> c {})"

lemma  strong_exchange_propertyE: 
  "strong_exchange_property E F \<Longrightarrow> 
  ((\<And> A B x. A \<in> F \<Longrightarrow> B \<in> F \<Longrightarrow> A \<subseteq> B \<Longrightarrow> (basis F B) \<Longrightarrow> x \<in> E - B \<Longrightarrow> A \<union> {x} \<in> F 
      \<Longrightarrow> (\<exists>y \<in> B - A. A \<union> {y} \<in> F \<and> (B - {y}) \<union> {x} \<in> F))
 ==> P) \<Longrightarrow> P"
  by(auto simp add: strong_exchange_property_def)

lemma  strong_exchange_propertyI: 
  "(\<And> A B x. A \<in> F \<Longrightarrow> B \<in> F \<Longrightarrow> A \<subseteq> B \<Longrightarrow> (basis F B) \<Longrightarrow> x \<in> E - B \<Longrightarrow> A \<union> {x} \<in> F 
      \<Longrightarrow> (\<exists>y \<in> B - A. A \<union> {y} \<in> F \<and> (B - {y}) \<union> {x} \<in> F))
 ==> strong_exchange_property E F "
  by(auto simp add: strong_exchange_property_def)

locale greedoid =
  fixes E :: "'a set"
  fixes F :: "'a set set"
  assumes contains_empty_set: "{} \<in> F"
  assumes third_condition: "\<And> X Y. (X \<in> F) \<Longrightarrow> (Y \<in> F) \<Longrightarrow> (card X > card Y) \<Longrightarrow> \<exists>x \<in> X - Y.  Y \<union> {x} \<in> F"
  assumes ss_assum: "set_system E F"

lemma exists_maximal: 
  assumes "set_system E F" "X \<in> F" "Y \<in> F" 
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

section \<open>Greedoids\<close>
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
end