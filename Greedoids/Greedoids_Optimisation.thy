theory Greedoids_Optimisation
  imports Main Complex_Main Greedoids
begin

lemma max_n: "(\<And> n. P n \<Longrightarrow> n \<le> bound) \<Longrightarrow> P (n::nat) \<Longrightarrow> (\<exists> nmax. P nmax \<and> (\<nexists> m. m > nmax \<and> P m))"
  by (metis bounded_Max_nat leD)

definition accessible where "accessible E F \<longleftrightarrow> set_system E F \<and> ({} \<in> F) \<and> (\<forall>X. (X \<in> F - {{}}) \<longrightarrow>
(\<exists>x \<in> X.  X - {x} \<in> F))"
definition closed_under_union where "closed_under_union F \<longleftrightarrow> (\<forall>X Y. X \<in> F \<and> Y \<in> F \<longrightarrow> X \<union> Y \<in> F)"


definition maximal where "maximal P Z \<longleftrightarrow> (P Z \<and> (\<nexists> X. X \<supset> Z \<and> P X))"

definition strong_exchange_property where "strong_exchange_property E F \<longleftrightarrow> 
(\<forall>A B x. (A \<in> F \<and> B \<in> F \<and> A \<subseteq> B \<and> (maximal (\<lambda>B. B \<in> F) B) \<and> x \<in> E - B \<and> A \<union> {x} \<in> F) 
      \<longrightarrow> (\<exists>y \<in> B - A. A \<union> {y} \<in> F \<and> (B - {y}) \<union> {x} \<in> F))"

lemma  strong_exchange_propertyE: 
 "strong_exchange_property E F \<Longrightarrow> 
  ((\<And> A B x. A \<in> F \<Longrightarrow> B \<in> F \<Longrightarrow> A \<subseteq> B \<Longrightarrow> (maximal (\<lambda>B. B \<in> F) B) \<Longrightarrow> x \<in> E - B \<Longrightarrow> A \<union> {x} \<in> F 
      \<Longrightarrow> (\<exists>y \<in> B - A. A \<union> {y} \<in> F \<and> (B - {y}) \<union> {x} \<in> F))
 ==> P) \<Longrightarrow> P"
 by(auto simp add: strong_exchange_property_def)

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


lemma accessible_property: assumes "set_system E F" "{} \<in> F"
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




locale greedoid =
  fixes E :: "'a set"
  fixes F :: "'a set set"
  assumes contains_empty_set: "{} \<in> F"
  assumes third_condition: "(X \<in> F) \<and> (Y \<in> F) \<and> (card X > card Y) \<Longrightarrow> \<exists>x \<in> X - Y.  Y \<union> {x} \<in> F"
  assumes ss_assum: "set_system E F"
  assumes finite_E: "finite E"
context greedoid
begin

lemma greedoid_accessible: 
  shows "accessible E F" unfolding accessible_def
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
  

locale greedy_algorithm = greedoid +
  fixes orcl::"'a \<Rightarrow> 'a set \<Rightarrow> bool"
  assumes orcl_correct: "\<And> X x. X \<subseteq> E \<Longrightarrow> x \<in> E - X \<Longrightarrow> X \<in> F \<Longrightarrow> orcl x X \<longleftrightarrow> insert x X \<in> F"
begin

definition "valid_modular_weight_func (c::'a set \<Rightarrow> real) = 
               (\<forall> X Y. X \<subseteq> E \<and> Y \<subseteq> E \<longrightarrow> c (X \<union> Y) = c X +  c Y - c (X \<inter> Y))"

lemma modular_weightE: "valid_modular_weight_func c \<Longrightarrow> 
               ((\<And> X Y. X \<subseteq> E \<Longrightarrow> Y \<subseteq> E \<Longrightarrow> c (X \<union> Y) = c X +  c Y - c (X \<inter> Y)) \<Longrightarrow> P ) \<Longrightarrow> P"
  by(auto simp add: valid_modular_weight_func_def)

lemma modular_weightI: "(\<And> X Y. X \<subseteq> E \<Longrightarrow> Y \<subseteq> E \<Longrightarrow> c (X \<union> Y) = c X +  c Y - c (X \<inter> Y)) 
                    \<Longrightarrow> valid_modular_weight_func c"
  by(auto simp add: valid_modular_weight_func_def)

lemma modular_weight_split: "valid_modular_weight_func c \<Longrightarrow> 
                X \<subseteq> E \<Longrightarrow> Y \<subseteq> E \<Longrightarrow> c (X \<union> Y) = c X +  c Y - c (X \<inter> Y)"
  by(auto simp add: valid_modular_weight_func_def)

lemma modular_function_single_costs:
  assumes "valid_modular_weight_func c"  "X \<subseteq> E" 
    shows "c X = sum (\<lambda> x. c {x}) X - (real (card X) - 1) * c {}"
proof-
  have "finite X"
    using assms(2) finite_E rev_finite_subset by blast
  moreover have " finite X \<Longrightarrow> X \<subseteq> E \<Longrightarrow> ?thesis"
  proof(induction X rule: finite_induct)
    case empty
    then show ?case by simp 
  next
    case (insert x F)
    hence sets_in_E: "F \<subseteq> E" "{x} \<subseteq> E" "F \<inter> {x} = {}" by auto
    show ?case 
      apply(subst modular_weight_split[OF assms(1) sets_in_E(1,2), simplified])
      apply(subst insert(3)[OF sets_in_E(1)])
      apply(subst sets_in_E(3))
      apply(subst comm_monoid_add_class.sum.insert[OF _ insert(2)])
      by (auto simp add: card_insert_disjoint[OF  _ insert(2)] insert.hyps(1)  algebra_simps)
  qed
  ultimately show ?thesis
    using assms(2) by simp
qed

lemma sum_is_modular: "valid_modular_weight_func (\<lambda> X. sum f X)"
  by(auto intro: modular_weightI sum_Un rev_finite_subset[OF finite_E])

definition "single_costs c X = c {} + sum (\<lambda> x. c {x} - c {}) X"
definition "elements_costs c x = c {x} - c {}"

definition "empty_minimal c = (\<forall> X \<subseteq> E. c X \<ge> c {})"

lemma real_distrib_sum:"real (sum f X) = sum (real o f) X"
  by auto

lemma modular_function_elements_costs:
  assumes "valid_modular_weight_func c"  "X \<subseteq> E" 
  shows "c X = sum (elements_costs c) X + c {}"
  apply(subst modular_function_single_costs[OF assms])
  unfolding elements_costs_def 
  apply(auto simp add: algebra_simps) 
  apply(subst card_eq_sum[of X])
  apply(subst real_distrib_sum)+
  apply(subst o_def)+
  apply(subst semiring_0_class.sum_distrib_left)+
  apply(subst comm_monoid_add_class.sum.distrib[symmetric])
  by simp
(*
lemma empty_minimal_monotone:
  assumes "valid_modular_weight_func c" "empty_minimal c" "A \<subseteq> E" "B \<subseteq> A"
  shows "c B \<le> c A"
  apply(subst modular_function_single_costs[OF assms(1,3)]) 
  apply(subst modular_function_single_costs[OF assms(1) order.trans[OF assms(4,3)]])
  apply (auto simp add: algebra_simps)
  apply(subst card_eq_sum[of A])
  apply(subst card_eq_sum[of B])
  apply(subst real_distrib_sum)+
  apply(subst o_def)+
  apply(subst semiring_0_class.sum_distrib_left)+
  sorry*)
  
  find_theorems "_ * sum _ _ = sum (\<lambda>_. _ * _ ) _"

(*
lemma assumes "valid_modular_weight_func c" "(\<And> X. X \<subseteq> E \<Longrightarrow> c X \<ge> 0)" "X \<subseteq> E" "X \<subseteq> Y" "Y \<subseteq> E"
  shows "c Y \<ge> c X"
  apply(subst modular_function_single_costs[OF assms(1,3)])
  apply(subst modular_function_single_costs[OF assms(1,5)])
  apply(auto simp add: algebra_simps)
*)

definition "maximum_weight_set c X = (X \<in> F \<and> (\<forall> Y \<in> F. c X \<ge> c Y))"

named_theorems algorithm_context

definition "opt_solution (c::'a set \<Rightarrow> real) X = (maximal (\<lambda> X. X \<in> F) X \<and>
                              (\<forall> Y. maximal (\<lambda> X. X \<in> F) Y \<longrightarrow> c X \<ge> c Y))"

lemma has_max_superset:  assumes "A \<in> F"
  obtains Xmax where "maximal (\<lambda> X. X \<in> F) Xmax" "Xmax \<supseteq> A"
  proof(goal_cases)
    case 1
    have finiteF:"finite F" 
    using Sup_least finite_UnionD finite_subset[of _ "Pow E"] ss_assum
    by(fastforce simp add: set_system_def)
    have "card A \<in> {card  X | X. X \<in> F \<and> X \<supseteq> A}"
      using assms by blast
    moreover have finite_cards: "finite { card X | X. X \<in> F \<and> X \<supseteq> A}"
      by (simp add: finiteF)
    ultimately have "(Max { card X | X. X \<in> F \<and> X \<supseteq> A}) \<in> { card X | X. X \<in> F \<and> X \<supseteq> A}"
      using Max_in by auto
    then obtain X where X_prop: "X \<in> F" "X \<supseteq> A" "card X = (Max { card X | X. X \<in> F \<and> X \<supseteq> A})" by auto
    hence X_best:"Y \<in> F \<Longrightarrow> Y \<supseteq> A \<Longrightarrow>card Y \<le> card X" for Y
      using Max_ge[OF finite_cards,  of "card Y"] by auto
    have " maximal (\<lambda> X. X \<in> F) X" 
    proof(rule ccontr, goal_cases)
      case 1
      then obtain Y where Y_prop: "Y \<in> F" "Y \<supset> X" 
        using X_prop(1) by(auto simp add: maximal_def)
      moreover hence "card Y > card X" 
        using infinite_super[of Y E] psubset_card_mono[of Y X]  ss_assum
        by(auto simp add: set_system_def)
      ultimately show ?case 
        using X_best[of Y]  X_prop(2) linorder_not_le by blast
    qed
    thus ?case 
      using  X_prop(1,2) by(auto intro!: 1[of X] exI[of _ X])
  qed


lemma opt_solution_exists: "Ex (opt_solution c)"
proof-
  have finiteF:"finite F" 
    using Sup_least finite_UnionD finite_subset[of _ "Pow E"] ss_assum
    by(fastforce simp add: set_system_def)
  hence fini:"finite {c X | X. X \<in> F \<and> maximal (\<lambda> X. X \<in> F) X}"
    by simp
  moreover obtain Xmax where non_empty:"c Xmax \<in> {c X | X. X \<in> F \<and> maximal (\<lambda> X. X \<in> F) X}"
  proof(goal_cases)
    case 1
    have "card {} \<in> {card  X | X. X \<in> F}"
      using contains_empty_set 
      by force
    moreover have finite_cards: "finite { card X | X. X \<in> F}"
      using finiteF by simp
    ultimately have "(Max { card X | X. X \<in> F}) \<in> { card X | X. X \<in> F}"
      using Max_in by auto
    then obtain X where X_prop: "X \<in> F" "card X = (Max { card X | X. X \<in> F})" by auto
    hence X_best:"Y \<in> F \<Longrightarrow> card Y \<le> card X" for Y
      using Max_ge finite_cards by auto
    have " maximal (\<lambda> X. X \<in> F) X" 
    proof(rule ccontr, goal_cases)
      case 1
      then obtain Y where "Y \<in> F" "Y \<supset> X" 
        using X_prop(1) by(auto simp add: maximal_def)
      moreover hence "card Y > card X" 
        using infinite_super[of Y E] psubset_card_mono[of Y X]  ss_assum
        by(auto simp add: set_system_def)
      ultimately show ?case using X_best by force
    qed
    thus ?case 
      using  X_prop(1) by(auto intro!: 1[of X] exI[of _ X])
  qed
  ultimately have "(Max {c X | X. X \<in> F \<and> maximal (\<lambda> X. X \<in> F) X}) 
                  \<in> {c X | X. X \<in> F \<and> maximal (\<lambda> X. X \<in> F) X}"
    using Max_in by auto
  then obtain X where "c X = Max {c X | X. X \<in> F \<and> maximal (\<lambda> X. X \<in> F) X}" "X \<in> F" "maximal (\<lambda> X. X \<in> F) X"
    by auto
  moreover hence "c X \<ge> c Y"  if "Y \<in> F" "maximal (\<lambda> X. X \<in> F) Y"for Y
    using Max_ge fini that by auto
  ultimately have "opt_solution c X"
   by(auto simp add: opt_solution_def maximal_def)
  thus ?thesis by auto
qed

context 
  fixes es::"'a list"
begin

definition "find_best_candidate c F' = 
           foldr (\<lambda> e acc. if e \<in> F' \<or> \<not> (orcl e F') then acc
                                                      else (case acc of None \<Rightarrow> Some e |
                                                            Some d \<Rightarrow>
                (if elements_costs c e > elements_costs c d then Some e
                             else Some d))) es None"

function (domintros) greedy_algorithm::"('a set \<Rightarrow> real) \<Rightarrow> 'a list \<Rightarrow> 'a list"  where
 "greedy_algorithm c xs = 
 (case  (find_best_candidate c (set xs)) of 
      Some e \<Rightarrow> greedy_algorithm c (e#xs) 
    | None \<Rightarrow> xs)"
  by pat_completeness auto

definition "invar_find_best_cand c xs = (\<forall> i < length xs. 
                        Some (xs ! i) = find_best_candidate c (set (drop (i+1) xs)))"

lemma invar_find_best_candI: "(\<And>i.  i < length xs \<Longrightarrow>
                        Some (xs ! i) = find_best_candidate c (set (drop (i+1) xs)))
         \<Longrightarrow> invar_find_best_cand c xs"
  by(auto simp add: invar_find_best_cand_def)

definition "invar_tails_indep xs = (\<forall> i \<le> length xs. set (drop i xs) \<in> F)"

lemma invar_tails_indepI: "(\<And> i. i \<le> length xs \<Longrightarrow> set (drop i xs) \<in> F) \<Longrightarrow> invar_tails_indep xs"
  by(auto simp add: invar_tails_indep_def)

context
  assumes set_assum: "set es = E" "distinct es" 
begin

lemma find_best_candidate_some_props:
  assumes "X \<subseteq> E" "find_best_candidate (c::'a set \<Rightarrow> real) X = Some x" "X \<in> F"
  shows "\<exists> es1 es2. es = es1@[x]@es2 \<and> x \<notin> X \<and> (insert x X) \<in> F \<and>
          (\<forall> y \<in> E - X. (insert y X) \<in> F \<longrightarrow> elements_costs c y \<le> elements_costs c x)
          \<and> \<not> (\<exists> y \<in> set es2. y \<notin> X \<and> (insert y X) \<in> F  \<and> elements_costs c y \<ge> elements_costs c x)"
proof-
  let ?iteration = " (\<lambda>e acc.
         if e \<in> X \<or> \<not> orcl e X then acc
         else case acc of None \<Rightarrow> Some e | Some d \<Rightarrow> if elements_costs c d < elements_costs c e then Some e else Some d)"
  have none_no_solution:"foldr ?iteration xs None = None \<Longrightarrow> \<not> ( \<exists> x \<in> set xs. x \<notin> X \<and> orcl x X)"
    for xs
    by(induction xs)
       (auto simp add: option.case_eq_if, meson option.discI, smt (verit, best) not_Some_eq option.simps(5))
  have "set es \<subseteq> E"
    by (simp add: set_assum(1))
  hence "\<exists> es1 es2. es = es1@[x]@es2 \<and> x \<notin> X \<and> (insert x X) \<in> F \<and>
          (\<forall> y \<in> set es - X. (insert y X) \<in> F \<longrightarrow> elements_costs c y \<le> elements_costs c x)
          \<and> \<not> (\<exists> y \<in> set es2. y \<notin> X \<and> (insert y X) \<in> F  \<and> elements_costs c y \<ge> elements_costs c x)"
    using assms(1,2) set_assum(2)
    unfolding find_best_candidate_def
  proof(induction es arbitrary: x)
    case Nil
    then show ?case
      by simp
  next
    case (Cons a es)
    show ?case 
    proof(cases "a \<in> X \<or> \<not> orcl a X")
      case True
      hence "foldr ?iteration (a # es) None =  foldr ?iteration es None "
        by simp
      hence "\<exists>es1 es2.
        es = es1 @ [x] @ es2 \<and>
        x \<notin> X \<and>
        insert x X \<in> F \<and>
        (\<forall>y\<in>set es - X. insert y X \<in> F \<longrightarrow> elements_costs c x \<ge> elements_costs c y) \<and>
        \<not> (\<exists>y\<in>set es2. y \<notin> X \<and> insert y X \<in> F \<and> elements_costs c y \<ge>elements_costs c x)"
        using Cons.prems(1,3,4)  assms(1) by(intro Cons(1)[of x]) auto
      then obtain es1 es2 where es1es2_prop: "es = es1 @ [x] @ es2"
        "x \<notin> X"
        "insert x X \<in> F"
        "(\<forall>y\<in>set es - X. insert y X \<in> F \<longrightarrow>elements_costs c x \<ge>elements_costs c y)"
         "\<not> (\<exists>y\<in>set es2. y \<notin> X \<and> insert y X \<in> F \<and> elements_costs c y \<ge>elements_costs c x)" by auto
      moreover hence "a#es = (a#es1) @ [x] @ es2"
        using True by simp
      moreover have  "(\<forall>y\<in>set (a#es) - X. insert y X \<in> F \<longrightarrow> elements_costs c x \<ge> elements_costs c y)"  
        using True es1es2_prop(4) orcl_correct[OF assms(1) _ assms(3), of a] Cons.prems(1) by auto
      moreover have 
         "\<not> (\<exists>y\<in>set (es2). y \<notin> X \<and> insert y X \<in> F \<and> elements_costs c y \<ge> elements_costs c x)"
        using True es1es2_prop(5) orcl_correct[OF assms(1) _ assms(3), of a] Cons.prems(1) by auto
      ultimately show ?thesis by blast
    next
      case False
      show ?thesis
      proof(cases "foldr ?iteration es None")
        case None
        hence x_is_a:"x = a"
          using Cons.prems(3) False by force
        hence  "a # es = [x] @ es" by simp
        moreover have "x \<notin> X" 
          using False x_is_a by auto
        moreover have "insert x X \<in> F"
          using Cons.prems(1) False assms(1) assms(3) orcl_correct x_is_a by auto
        moreover have "(\<forall>y\<in>set (a # es) - X. insert y X \<in> F \<longrightarrow> elements_costs c x \<ge>elements_costs c y)"
          using x_is_a  none_no_solution[OF None] orcl_correct[OF assms(1) _ assms(3)]
                Cons.prems(1) by fastforce+
        moreover have  "\<not> (\<exists>y\<in>set es. y \<notin> X \<and> insert y X \<in> F \<and> elements_costs c y \<ge> elements_costs c x)" 
          using x_is_a  none_no_solution[OF None] orcl_correct[OF assms(1) _ assms(3)]
                Cons.prems(1) by auto
        ultimately show ?thesis  by force
      next
        case (Some y)
        obtain es1 es2 where es1_es2_prop: "es = es1 @ [y] @ es2" "y \<notin> X" "insert y X \<in> F"
            "(\<forall>ya\<in>set es - X. insert ya X \<in> F \<longrightarrow> elements_costs c y \<ge> elements_costs c ya)"
            "\<not> (\<exists>ya\<in>set es2. ya \<notin> X \<and> insert ya X \<in> F \<and> elements_costs c ya \<ge> elements_costs c y)"
          using Cons(1)[OF _ _ Some]  Cons.prems(1,4) assms(1) by auto
        have "elements_costs c y \<ge> elements_costs c a \<Longrightarrow>  (a#es) = (a#es1) @ [y] @ es2"
          by (simp add: es1_es2_prop(1))
        moreover have "elements_costs c y \<ge>elements_costs  c a \<Longrightarrow> x = y"
          using  Cons.prems(3) Some False by auto
        moreover have "elements_costs c y < elements_costs c a \<Longrightarrow> (a#es) = []@[x]@es"
          using Cons.prems(3) False Some by simp
        moreover have  "x \<notin> X"
          using Cons.prems(3) Some es1_es2_prop(2) False
          by(auto split: option.split if_split intro: case_split[of "elements_costs c y < elements_costs c a"])
        moreover have "insert x X \<in> F"
          using Cons.prems(1,3) Some es1_es2_prop(3,4) False  assms(1,3) orcl_correct
          by (fastforce intro:  case_split[of "elements_costs c y <elements_costs c a"])
        moreover have  "(\<forall>ya\<in>set (a#es) - X. insert ya X \<in> F \<longrightarrow> elements_costs c x \<ge> elements_costs c ya)"
          using es1_es2_prop(4) False  Cons.prems Some
          by (cases "elements_costs c y <elements_costs c a") auto
        moreover have  "elements_costs c y \<ge> elements_costs c a \<Longrightarrow> 
                \<not> (\<exists>ya\<in>set (es2). ya \<notin> X \<and> insert ya X \<in> F \<and> elements_costs c ya \<ge> elements_costs c y)"
          by (simp add: es1_es2_prop(5))
        moreover have  "elements_costs c y < elements_costs c a \<Longrightarrow> 
                \<not> (\<exists>ya\<in>set es. ya \<notin> X \<and> insert ya X \<in> F \<and> elements_costs c ya \<ge> elements_costs c a)"
          using es1_es2_prop(4) by fastforce
        ultimately show ?thesis
          by(cases "elements_costs c y < elements_costs c a")
            (auto intro: exI[of "\<lambda> xs. \<exists>es2. _ xs es2" "a#es1"] exI[of _ "es2"])
      qed     
    qed
  qed
  thus ?thesis 
    using set_assum(1) by force
qed

lemma find_best_candidate_none:
  assumes "X \<subseteq> E" "find_best_candidate (c::'a set \<Rightarrow> real) X = None" "X \<in> F"
  shows "\<nexists> x. x \<in> E - X \<and> insert x X \<in> F"
proof-
  let ?iteration = " (\<lambda>e acc.
         if e \<in> X \<or> \<not> orcl e X then acc
         else case acc of None \<Rightarrow> Some e | Some d \<Rightarrow> if elements_costs c d < elements_costs c e then Some e else Some d)"
  have es_in_E: "set es \<subseteq> E" 
    by (simp add: set_assum)
  show ?thesis
    apply(subst set_assum(1)[symmetric])
    using assms(2) es_in_E
    unfolding find_best_candidate_def 
proof(induction es)
  case Nil
  then show ?case by simp
next
  case (Cons a es)
  show ?case
  proof(cases "a \<in> X \<or> \<not> orcl a X")
    case True
    then show ?thesis 
      using orcl_correct[OF assms(1) _ assms(3), of a]
             Cons.IH Cons.prems(1) Cons.prems(2) by auto
  next
    case False
    have if_None:"(if A then Some B else Some C) = None  \<Longrightarrow> P" for A B C  P
      by(cases A) auto
    from False show ?thesis 
      using orcl_correct[OF assms(1) _ assms(3), of a]
             Cons.prems(1) Cons.prems(2)
       by(cases "foldr ?iteration es None")
         (auto split: if_split intro: if_None)
  qed
qed
qed

(*Invariants: solution in E, solution independent, solution distinct, solution elements are best candidates*)

named_theorems loop_props

lemma solution_remains_independent[loop_props]:
  assumes "greedy_algorithm_dom (c, xs)" "set xs \<in> F"
  shows "set (greedy_algorithm c xs) \<in> F"
  using assms(2)
proof(induction rule: greedy_algorithm.pinduct[OF assms(1)])
  case (1  c xs)
  note IH = this
  have xs_in_E:"set xs \<subseteq> E"
    using "1.prems" ss_assum by(auto simp add: set_system_def )
  show ?case
  proof(subst greedy_algorithm.psimps[OF 1(1)], cases "find_best_candidate c (set xs)", goal_cases)
    case 1
    then show ?case by(simp add: IH(3))
  next
    case (2 x)
    then show ?case 
      using find_best_candidate_some_props[OF xs_in_E 2 IH(3)] 
      by (auto intro!: IH(2)[OF 2])
  qed
qed

lemma solution_distinct[loop_props]:
  assumes "greedy_algorithm_dom (c ,xs)" "set xs \<in> F" "distinct xs"
  shows "distinct (greedy_algorithm c xs) "
  using assms(2,3)
proof(induction rule: greedy_algorithm.pinduct[OF assms(1)])
  case (1 c xs)
  note IH = this
  have xs_in_E:"set xs \<subseteq> E"
    using "1.prems" ss_assum by(auto simp add: set_system_def )
  show ?case
  proof(subst greedy_algorithm.psimps[OF 1(1)], cases "find_best_candidate c (set xs)", goal_cases)
    case 1
    then show ?case by(simp add: IH(4))
  next
    case (2 x)
    then show ?case 
      using find_best_candidate_some_props[OF xs_in_E 2 IH(3)] IH(4)
      by (simp, intro IH(2)[OF 2]) auto
  qed
qed

lemma greedy_algo_term[loop_props]:
  assumes "set xs \<in> F" "n = card E - card (set xs)" "distinct xs"
  shows "greedy_algorithm_dom (c, xs)"
  using assms
proof(induction n arbitrary: xs)
  case 0
  have xs_in_E:"set xs \<subseteq> E"
   using "0.prems" ss_assum by(auto simp add: set_system_def )
  show ?case 
  proof(rule greedy_algorithm.domintros, goal_cases)
    case (1 x)
    have "insert x (set xs) \<in> F" "x \<notin> set xs"
      using find_best_candidate_some_props[OF xs_in_E 1 0(1)] by auto
    hence "set xs \<subset> E"
      using set_system_def ss_assum xs_in_E by fastforce
    hence "card E - card (set xs) > 0"
      using card_Diff_subset set_assum(1) by fastforce
    thus ?case 
      using 0(2) by simp
  qed
next
  case (Suc n)
  have xs_in_E:"set xs \<subseteq> E"
   using "Suc.prems" ss_assum by(auto simp add: set_system_def )
  show ?case
  proof(rule greedy_algorithm.domintros, goal_cases)
    case (1 x)
    have "insert x (set xs) \<in> F" "x \<notin> set xs" "distinct (x#xs)"
      using find_best_candidate_some_props[OF xs_in_E 1 Suc(2)] Suc(4) by auto
    moreover hence "set xs \<subset> E"
      using set_system_def ss_assum xs_in_E by fastforce
    moreover hence "card E - card (set xs) > 0"
      using card_Diff_subset set_assum(1) by fastforce
    moreover have "n = card E - card (set (x # xs))" 
      using Suc.prems(2) calculation(2) by force
    ultimately show ?case 
      by(auto intro: Suc(1)[of "x#xs"])
  qed
qed
                                                                        

lemma find_best_candidate_order[loop_props]:
  assumes "greedy_algorithm_dom (c, xs)" "set xs \<in> F" "distinct xs" "invar_find_best_cand c xs" 
  shows "invar_find_best_cand c  (greedy_algorithm c xs)"
  using assms(2,3,4)
proof(induction rule: greedy_algorithm.pinduct[OF assms(1)])
  case (1 c xs)
  note IH = this
  have xs_in_E:"set xs \<subseteq> E"
    using "1.prems" ss_assum by(auto simp add: set_system_def)
  show ?case
  proof(subst greedy_algorithm.psimps[OF 1(1)], cases "find_best_candidate c (set xs)", goal_cases)
    case 1
    then show ?case by(simp add: IH(5))
  next
    case (2 x)
    note two = this
    have xs_in_E:"set xs \<subseteq> E"
      using "IH" ss_assum by(auto simp add: set_system_def )
    have x_added: "insert x (set xs) \<in> F" "x \<notin> set xs" "distinct (x#xs)"
      using find_best_candidate_some_props[OF xs_in_E 2 IH(3)] IH(4) by auto
    have invar_next: "invar_find_best_cand c (x # xs)"
    proof(rule invar_find_best_candI, goal_cases)
      case (1 i)
      show ?case 
      proof(insert 1, cases i, goal_cases)
        case 1
        then show ?case 
          by(simp add: 2)
      next
        case (2 nat)
        then show ?case 
          using  x_added  find_best_candidate_some_props[OF xs_in_E two IH(3)]  IH(5) 
         by(auto simp add: invar_find_best_cand_def)
      qed
    qed
   from 2 show ?case 
     using x_added IH(5) by(auto intro: IH(2)[OF 2] simp add: invar_next)
  qed
qed

lemma final_candidate_none[loop_props]:
  assumes "greedy_algorithm_dom (c, xs)" "set xs \<in> F" "distinct xs"
  shows "find_best_candidate c (set (greedy_algorithm c xs))  = None"
  using assms(2,3)
proof(induction rule: greedy_algorithm.pinduct[OF assms(1)])
  case (1 c xs)
  note IH = this
  have xs_in_E:"set xs \<subseteq> E"
    using "1.prems" ss_assum by(auto simp add: set_system_def)
  show ?case
  proof(subst greedy_algorithm.psimps[OF IH(1)], cases "find_best_candidate c (set xs)", goal_cases)
    case 1
    then show ?case by simp
  next
    case (2 x)
    then show ?case 
      using find_best_candidate_some_props[OF xs_in_E 2 IH(3)] IH(4) 
      by (simp, intro IH(2)[OF 2]) auto
  qed
qed

lemma intermediate_solutions_indep[loop_props]:
  assumes "greedy_algorithm_dom (c, xs)" "set xs \<in> F" "invar_tails_indep xs"
  shows "invar_tails_indep (local.greedy_algorithm c xs)"
  using assms(2,3)
proof(induction rule: greedy_algorithm.pinduct[OF assms(1)])
  case (1 c xs)
  note IH = this
  have xs_in_E:"set xs \<subseteq> E"
    using "1.prems" ss_assum by(auto simp add: set_system_def)
  show ?case
  proof(subst greedy_algorithm.psimps[OF 1(1)], cases "find_best_candidate c (set xs)", goal_cases)
    case 1
    then show ?case by(simp add: IH(4))
  next
    case (2 x)
    note two = this
    have xs_in_E:"set xs \<subseteq> E"
      using "IH" ss_assum by(auto simp add: set_system_def )
    have x_added: "insert x (set xs) \<in> F" 
      using find_best_candidate_some_props[OF xs_in_E 2 IH(3)] by auto
    have invar_next: "invar_tails_indep  (x # xs)"
    proof(rule invar_tails_indepI, goal_cases)
      case (1 i)
      show ?case 
      proof(insert 1, cases i, goal_cases)
        case 1
        then show ?case 
          by(simp add: x_added)
      next
        case (2 nat)
        then show ?case 
         using  x_added  find_best_candidate_some_props[OF xs_in_E two IH(3)]  IH(4) 
         by(auto simp add: invar_tails_indep_def)
      qed
    qed
   from 2 show ?case 
     using x_added IH(4) by(auto intro: IH(2)[OF 2] simp add: invar_next)
  qed
qed

lemma initial_props: "set Nil \<in> F" "card E = card E - card (set Nil)" "distinct Nil"
                      "invar_find_best_cand c Nil" "invar_tails_indep Nil"
  by(auto simp add: contains_empty_set intro: invar_find_best_candI invar_tails_indepI)

lemmas result_props =
      loop_props(3)[OF initial_props(1-3), of ] 
      loop_props(1)[OF loop_props(3)[OF initial_props(1-3)] initial_props(1), of ]
      loop_props(2)[OF loop_props(3)[OF initial_props(1-3)] initial_props(1,3), of ]
      loop_props(4)[OF loop_props(3)[OF initial_props(1-3)] initial_props(1,3,4)]
      loop_props(5)[OF loop_props(3)[OF initial_props(1-3)] initial_props(1,3), of ]
      loop_props(6)[OF loop_props(3)[OF initial_props(1-3)] initial_props(1,5), of ]

lemma algorithm_computes_basis:
  "maximal (\<lambda> X. X \<in> F) (set (greedy_algorithm c Nil))"
proof(rule ccontr, goal_cases)
  case 1
  note result_props = result_props(2,5)[of c]
  have alg_inF: "(set (local.greedy_algorithm c [])) \<in> F"
    using result_props(1) by auto
  then obtain X where X_prop:"X \<supset> set (local.greedy_algorithm c [])" "X \<in> F" 
    using 1 by(auto simp add: maximal_def)
  hence XinE: "X \<subseteq> E"
    using ss_assum by(auto simp add: set_system_def)
  hence "card X > card (set (local.greedy_algorithm c []))"
     using  finite_subset psubset_card_mono set_assum(1)  X_prop(1) by blast
  then obtain y where y_prop:"y \<in> X - set (local.greedy_algorithm c [])" 
                         "insert y (set (local.greedy_algorithm c [])) \<in> F"
     using  result_props(1) third_condition  X_prop(2) by auto
  moreover hence "y \<in> E - set (local.greedy_algorithm c []) "
    using XinE by fastforce
  moreover have "\<nexists>x. x \<in> E - set (local.greedy_algorithm c []) \<and> insert x (set (local.greedy_algorithm c [])) \<in> F"
    using   result_props(2) alg_inF ss_assum
    by (intro find_best_candidate_none[OF _ result_props(2)])
       (auto simp add: set_system_def)
  ultimately show False
       by blast
qed


lemma strong_exchange_max_modular_weight:
  assumes "valid_modular_weight_func c" "strong_exchange_property E F"  "empty_minimal c"
    shows "opt_solution c (set (greedy_algorithm c Nil))"
proof-
  note result_props = result_props[of c]
  define max_P where "max_P = (\<lambda> n. n \<le> length (greedy_algorithm c Nil) \<and>
                               (\<exists> B. opt_solution c B 
                               \<and> set (take n ( rev (greedy_algorithm c Nil))) \<subseteq> B))"
  have "\<exists>nmax. max_P nmax \<and> \<not> (\<exists>m>nmax. max_P m)"
    by(fastforce intro:  max_n[of max_P "length (greedy_algorithm c Nil)" 0] 
              simp add: max_P_def opt_solution_exists)
  then obtain k where k_prop: "max_P k" "\<not> (\<exists>m>k. max_P m)" by auto
  then obtain B where B_prop: "opt_solution c B" "set (take k ( rev (greedy_algorithm c Nil))) \<subseteq> B"
    using max_P_def by blast
  hence B_unfolded: "B \<in> F" "B \<subseteq> E" "maximal (\<lambda> B. B \<in> F) B"
    using  ss_assum
    by(auto simp add: opt_solution_def set_system_def maximal_def) 
  have k_length_less:"k \<le> length (greedy_algorithm c Nil)"
    using k_prop by(auto simp add: max_P_def) 
  moreover have "k < length (greedy_algorithm c Nil) \<Longrightarrow> False"
  proof(goal_cases)
    case 1
    note one = this
    hence length_non_zero: "length (local.greedy_algorithm c []) > 0" by auto
    define B' where "B' = B - (set (take k ( rev (greedy_algorithm c Nil))))"
    have a3: "set (take k (rev (local.greedy_algorithm c []))) \<subseteq> B" 
      by (simp add: B_prop(2))
        have a4: "maximal (\<lambda>B. B \<in> F) B"
          by (simp add: B_unfolded(3))
        have a5:"rev (local.greedy_algorithm c []) ! k \<in> E" 
        proof-
          have "set  (local.greedy_algorithm c []) \<in> F"
            using result_props(6) one by(auto simp add: invar_tails_indep_def)
          hence "set (local.greedy_algorithm c []) \<subseteq> E"
            using ss_assum by(auto simp add: set_system_def)
          moreover have "rev (local.greedy_algorithm c []) ! k \<in> set (local.greedy_algorithm c [])" 
            by (metis length_rev nth_mem one set_rev)
          ultimately show ?thesis by auto
        qed
        have a6: "rev (local.greedy_algorithm c []) ! k \<notin> B" 
        proof(rule ccontr, goal_cases 1)
          case 1
          hence "rev (local.greedy_algorithm c []) ! k \<in> B" by simp
          hence "set (take (k+1) ( rev (greedy_algorithm c Nil))) \<subseteq> B" 
            using  a3  one set_take_union_nth[of k "rev (greedy_algorithm c Nil)", symmetric] 
            by simp
          hence "max_P (k+1)"
            using B_prop(1) less_iff_succ_less_eq max_P_def one by blast
          thus False 
            using k_prop(2) by force
        qed
    have "\<exists> y \<in> B'. insert y (set (take k (rev (greedy_algorithm c Nil)))) \<in> F \<and> 
                    (B - {y}) \<union> {(rev (greedy_algorithm c Nil)) ! k} \<in> F"
      proof(rule strong_exchange_propertyE[OF assms(2)], goal_cases)
        case 1
        have a1: "set (take k (rev (local.greedy_algorithm c []))) \<in> F" 
          using diff_le_self[of ]  result_props(6) set_rev take_rev[of k "local.greedy_algorithm c []"]
          by(simp add: invar_tails_indep_def)
        have a2: "B \<in> F" 
          using B_prop by (auto simp add: opt_solution_def maximal_def)
        have a4: "maximal (\<lambda>B. B \<in> F) B"
          by (simp add: B_unfolded(3))
        have a7: "insert (rev (local.greedy_algorithm c []) ! k) 
                         (set (take k (rev (local.greedy_algorithm c [])))) \<in> F"
          using HOL.spec[OF result_props(6)[simplified invar_tails_indep_def], 
                          of "length (local.greedy_algorithm c []) - (k+1)"]
           one rev_rev_ident[of "greedy_algorithm c []"] 
               rev_take[of "k+1" "rev (greedy_algorithm c [])"] 
                  set_take_union_nth[of k "(rev (local.greedy_algorithm c []))"]
          by (auto ,metis set_rev)         
        show ?case 
          using a1 a2 a3 a4 a5 a6 a7 
          by(auto intro!: 1[of "set (take k (rev (local.greedy_algorithm c [])))" B
                           "rev (local.greedy_algorithm c []) ! k", simplified] simp add: B'_def)
      qed
      then obtain y where y_props: " insert y (set (take k (rev (local.greedy_algorithm c [])))) \<in> F"
                                   "B - {y} \<union> {rev (local.greedy_algorithm c []) ! k} \<in> F" "y \<in> B'" by auto
      have ak_better_costs_than_y:
         "elements_costs c ((rev (local.greedy_algorithm c [])) ! (k)) \<ge> elements_costs c y"
      proof-
        have cand_is: "Some (rev (local.greedy_algorithm c []) ! (k )) = 
             find_best_candidate c (set (take k (rev (local.greedy_algorithm c []))))"
          using HOL.spec[OF result_props(4)[simplified invar_find_best_cand_def], 
                    of "length (local.greedy_algorithm c []) - Suc k"]
                 Suc_diff_Suc[of k "length (local.greedy_algorithm c [])"]  one 
          by (fastforce simp add: rev_nth[OF one] take_rev)
       have take_k_in_F:"set (take k (rev (local.greedy_algorithm c []))) \<in> F"
          using result_props(6) 
          by(simp add: invar_tails_indep_def take_rev)
       hence take_k_in_E:"set (take k (rev (local.greedy_algorithm c []))) \<subseteq> E"
         using B_prop(2) B_unfolded(2) by blast
       have from_condidate_props:"(\<And> y. y\<in>E - set (take k (rev (local.greedy_algorithm c []))) \<Longrightarrow>
             insert y (set (take k (rev (local.greedy_algorithm c [])))) \<in> F \<Longrightarrow>
            elements_costs c y \<le> elements_costs c (rev (local.greedy_algorithm c []) ! k))"
         using find_best_candidate_some_props[OF take_k_in_E cand_is[symmetric] take_k_in_F] by auto
       show ?thesis
         using y_props(3) B_unfolded(2) 
         by(auto intro: from_condidate_props[OF _ y_props(1)] simp add: B'_def)
     qed
     have new_b_better:"c (B - {y} \<union> {rev (local.greedy_algorithm c []) ! k}) \<ge>  c B"
     proof-
       have "c B = c ((B-{y}) \<union> {y})"
         using B'_def insert_Diff y_props(3) by fastforce
       also have "... = c(B - {y}) + c {y} - c {}"
         using B_unfolded y_props(3) 
         by (subst modular_weight_split[OF assms(1)])(auto simp add: B'_def)
       also have "... =  c (B - {y}) +  elements_costs c y"
         by (simp add: elements_costs_def)
       also have "... \<le> c (B - {y}) + elements_costs c (rev (local.greedy_algorithm c []) ! k)"
         by (simp add: ak_better_costs_than_y)
       also have "... = c (B - {y}) + c {(rev (local.greedy_algorithm c []) ! k)} - c {}"
         by (simp add: elements_costs_def)
       also have "... = c (B - {y} \<union>  {(rev (local.greedy_algorithm c []) ! k)})"
         using B_unfolded(2)  ss_assum y_props(2)  a6  
         by (subst modular_weight_split[OF assms(1)]) (fastforce simp add: set_system_def )+
       finally show ?thesis by simp
     qed
     obtain newB where newB: "maximal (\<lambda> X. X \<in> F) newB" 
          "(B - {y} \<union>  {(rev (local.greedy_algorithm c []) ! k)}) \<subseteq> newB"
       using  y_props(2) by(force intro:has_max_superset)
     have newB_empty: "((newB - insert (rev (local.greedy_algorithm c []) ! k) (B - {y})) \<inter> (B - {y})) =  {}"
       using Diff_disjoint Diff_insert2 Int_commute 
          by metis
     have newB_even_better: "c newB \<ge> c (B - {y} \<union> {rev (local.greedy_algorithm c []) ! k})"
     proof-
       have "c newB = c ((newB - (B - {y} \<union>  {(rev (local.greedy_algorithm c []) ! k)}))
                \<union> (B - {y} \<union>  {(rev (local.greedy_algorithm c []) ! k)}))"
         using newB 
         by (metis Un_Diff_cancel2 sup_absorb1)
       also have "... = c ((newB - (B - {y} \<union>  {(rev (local.greedy_algorithm c []) ! k)}))) 
                        + c (B - {y} \<union>  {(rev (local.greedy_algorithm c []) ! k)}) - c{}"
         using  newB(1)  ss_assum  B_unfolded(2) a5
         by (subst modular_weight_split[OF assms(1)])(auto simp add:  set_system_def maximal_def newB_empty)
       also have  "... = c ((newB - (B - {y} \<union>  {(rev (local.greedy_algorithm c []) ! k)}))) 
                        + (c (B - {y} \<union>  {(rev (local.greedy_algorithm c []) ! k)}) - c{})" by simp
       also have  "... \<ge> c (( (B - {y} \<union>  {(rev (local.greedy_algorithm c []) ! k)}))) 
                       " 
         using   newB(1)  ss_assum y_props(3)
         by(auto intro!: mp[OF HOL.spec[OF assms(3)[simplified empty_minimal_def]]] 
               simp add: B'_def set_system_def maximal_def)
       finally show ?thesis by simp
     qed
     have "(k+1) \<le> length (greedy_algorithm c Nil)"
       using one by auto
     moreover have " opt_solution c newB"
       using B_prop(1) newB(1) newB_even_better new_b_better by (force simp add:  opt_solution_def)
     moreover have "set (take (k+1) ( rev (greedy_algorithm c Nil))) \<subseteq> newB"
       using one  B'_def a3 newB(2) y_props(3) by (subst set_take_union_nth[symmetric])(auto simp add: B'_def)
     ultimately have "max_P (k+1)"
       by(auto simp add: max_P_def)
     thus False
       using k_prop(2) by auto
   qed
   ultimately have "k = length (local.greedy_algorithm c [])" by force
   hence inB:"set (local.greedy_algorithm c []) \<subseteq> B" 
     using B_prop(2) by simp
   moreover have "set (local.greedy_algorithm c []) \<subset> B \<Longrightarrow> False"
   proof(goal_cases)
     case 1
     hence "card B > card (set (local.greedy_algorithm c []))"
       using B_unfolded(2) finite_subset psubset_card_mono set_assum(1) by blast
     then obtain y where y_prop:"y \<in> B - set (local.greedy_algorithm c [])" 
                         "insert y (set (local.greedy_algorithm c [])) \<in> F"
       using B_unfolded(1) result_props(2) third_condition by auto
     moreover hence "y \<in> E - set (local.greedy_algorithm c []) "
       using B_unfolded(2) by blast
     moreover have "\<nexists>x. x \<in> E - set (local.greedy_algorithm c []) \<and> insert x (set (local.greedy_algorithm c [])) \<in> F"
       using B_unfolded inB  result_props(2) 
       by (intro find_best_candidate_none[OF _ result_props(5)]) auto
     ultimately show False
       by blast
   qed
   ultimately have "B = set (local.greedy_algorithm c [])"
     by blast
   thus ?thesis
     using B_prop(1) by auto
 qed
end
end

context
  assumes no_strong_exchange: "\<not> strong_exchange_property E F"
begin

thm no_strong_exchange[simplified strong_exchange_property_def]

lemma no_strong_exchange_applied: 
  obtains A B x where
    "A \<in> F" "B \<in> F" "A \<subseteq> B" "Greedoids_Optimisation.maximal (\<lambda>B. B \<in> F) B" "x \<in> E - B" 
    "A \<union> {x} \<in> F"  "(\<And> y. y\<in>B - A \<Longrightarrow> A \<union> {y} \<in> F \<Longrightarrow> B - {y} \<union> {x} \<notin> F)"
  using no_strong_exchange by (auto simp add: strong_exchange_property_def)

definition "A = (SOME A. \<exists> B x. 
                  A \<in> F \<and> B \<in> F \<and> A \<subseteq> B \<and> Greedoids_Optimisation.maximal (\<lambda>B. B \<in> F) B \<and>  x \<in> E - B \<and>
                  A \<union> {x} \<in> F  \<and> (\<forall>  y\<in>B - A. A \<union> {y} \<in> F \<longrightarrow> B - {y} \<union> {x} \<notin> F))"

lemma there_is_A: "\<exists> A. (\<exists> B x. 
                  A \<in> F \<and> B \<in> F \<and> A \<subseteq> B \<and> Greedoids_Optimisation.maximal (\<lambda>B. B \<in> F) B \<and>  x \<in> E - B \<and>
                  A \<union> {x} \<in> F  \<and> (\<forall>  y\<in>B - A. A \<union> {y} \<in> F \<longrightarrow> B - {y} \<union> {x} \<notin> F))"
  using no_strong_exchange by (auto simp add: strong_exchange_property_def)

lemma A_props: "\<exists>B x. A \<in> F \<and> B \<in> F \<and> A \<subseteq> B \<and> Greedoids_Optimisation.maximal (\<lambda>B. B \<in> F) B \<and>  x \<in> E - B \<and>
                  A \<union> {x} \<in> F  \<and> (\<forall>  y\<in>B - A. A \<union> {y} \<in> F \<longrightarrow> B - {y} \<union> {x} \<notin> F)"
  by(unfold A_def )(rule someI_ex[OF there_is_A])

definition "B = (SOME B. \<exists> x. 
                  A \<in> F \<and> B \<in> F \<and> A \<subseteq> B \<and> Greedoids_Optimisation.maximal (\<lambda>B. B \<in> F) B \<and>  x \<in> E - B \<and>
                  A \<union> {x} \<in> F  \<and> (\<forall>  y\<in>B - A. A \<union> {y} \<in> F \<longrightarrow> B - {y} \<union> {x} \<notin> F))"

lemma B_props: "\<exists> x. A \<in> F \<and> B \<in> F \<and> A \<subseteq> B \<and> Greedoids_Optimisation.maximal (\<lambda>B. B \<in> F) B \<and>  x \<in> E - B \<and>
                  A \<union> {x} \<in> F  \<and> (\<forall>  y\<in>B - A. A \<union> {y} \<in> F \<longrightarrow> B - {y} \<union> {x} \<notin> F)"
  by(unfold B_def )(rule someI_ex[OF A_props])

definition "x = (SOME x. 
                  A \<in> F \<and> B \<in> F \<and> A \<subseteq> B \<and> Greedoids_Optimisation.maximal (\<lambda>B. B \<in> F) B \<and>  x \<in> E - B \<and>
                  A \<union> {x} \<in> F  \<and> (\<forall>  y\<in>B - A. A \<union> {y} \<in> F \<longrightarrow> B - {y} \<union> {x} \<notin> F))"

lemma x_props: "A \<in> F \<and> B \<in> F \<and> A \<subseteq> B \<and> Greedoids_Optimisation.maximal (\<lambda>B. B \<in> F) B \<and>  x \<in> E - B \<and>
                  A \<union> {x} \<in> F  \<and> (\<forall>  y\<in>B - A. A \<union> {y} \<in> F \<longrightarrow> B - {y} \<union> {x} \<notin> F)"
  by(unfold x_def )(rule someI_ex[OF B_props])

lemma ABx_props: "A \<in> F" "B \<in> F" "A \<subseteq> B" "Greedoids_Optimisation.maximal (\<lambda>B. B \<in> F) B" "x \<in> E - B" 
    "A \<union> {x} \<in> F"  "(\<And> y. y\<in>B - A \<Longrightarrow> A \<union> {y} \<in> F \<Longrightarrow> B - {y} \<union> {x} \<notin> F)"
  using x_props by auto

definition "Y = {y | y. y \<in> B - A \<and> insert y A \<in> F}"

lemma Y_in_B_without_A: "Y \<subseteq> B -  A"
  using Y_def by blast

lemma there_is_A_list: "(\<exists>l. set l = A \<and> (\<forall>i\<le>length l. set (take i l) \<in> F) \<and> distinct l)"
  using  accessible_property  contains_empty_set greedoid_accessible ss_assum x_props by blast

definition "A_list = (SOME l. set l = A \<and> (\<forall>i\<le>length l. set (take i l) \<in> F) \<and> distinct l)"

lemma A_list_props: "set A_list = A" "(\<forall>i\<le>length A_list. set (take i A_list) \<in> F)" "distinct A_list"
                     "(\<And> i. i\<le>length A_list \<Longrightarrow> set (take i A_list) \<in> F)"
  by (smt (verit, del_insts) A_list_def someI_ex there_is_A_list)+

lemma finites: "finite A" "finite B" "finite Y"
  using  finite_Diff finite_subset[of _ E] ss_assum x_props 
  by(auto simp add: Y_def set_system_def)

lemma B_without_Y_without_A: "\<exists> l. set l = B - Y - A \<and> distinct l"
  by (auto intro: finite_distinct_list simp add: finites)

definition "BYA_list = (SOME l. set l = B - Y - A \<and> distinct l)"

lemma BYA_list_props: "set BYA_list = B - Y - A" "distinct BYA_list"
  using  someI_ex[OF B_without_Y_without_A] 
  by(auto simp add: BYA_list_def)

lemma B_without_A_without_Y_is: " B - Y - A = {y |y. y \<in> B - A \<and> \<not> insert y A \<in> F}"
  by(auto simp add: Y_def)

lemma Y_list_exists: "\<exists> l. set l = Y \<and> distinct l"
  by (auto intro: finite_distinct_list simp add: finites)

definition "Y_list = (SOME l. set l = Y \<and> distinct l)"

lemma Y_list_props: "set Y_list = Y" "distinct Y_list"
  using  someI_ex[OF Y_list_exists] 
  by(auto simp add: Y_list_def)

lemma E_without_W_without_x: "\<exists> l. set l = E - B - {x} \<and> distinct l"
  by (auto intro: finite_distinct_list simp add: finites finite_E)

definition "EWx_list = (SOME l. set l = E - B - {x} \<and> distinct l)"

lemma EWx_list_props: "set EWx_list = E - B - {x}" "distinct EWx_list"
  using  someI_ex[OF E_without_W_without_x] 
  by(auto simp add: EWx_list_def)

definition "es = EWx_list@Y_list@[x]@BYA_list@rev A_list"

lemma all_in_E: "A \<subseteq> E" "B \<subseteq> E" "Y \<subseteq> E" 
  using  ABx_props(1,2,3) ss_assum Y_in_B_without_A by(auto simp add: set_system_def)

lemma es_prop: "set es = E" "distinct es"
  using EWx_list_props BYA_list_props  ABx_props(1-3,5) Y_in_B_without_A all_in_E A_list_props(1,3) Y_list_props 
  by(auto simp add:  es_def) 

definition "c y =
           (if y \<in> B - Y then (2::real)
            else if y \<in> insert x Y then (1::real)
            else if y \<in> E - B - {x} then 0
            else undefined)"

lemma costs_are:
      "y \<in> A ==> c y = 2"
      "y \<in> B - Y - A \<Longrightarrow> c y = 2"
      "y \<in> B - Y\<Longrightarrow> c y = 2"
      "c x = 1"
      "y \<in> Y \<Longrightarrow> c y = 1"
      "y \<in> E - B - {x} \<Longrightarrow> c y = 0"
      "y \<in> E \<Longrightarrow> c y \<le> 2"
  using ABx_props(5,3) all_in_E Y_in_B_without_A by(auto simp add: c_def split: if_split)

definition "costs X = sum c X"

lemma costs_modular: "valid_modular_weight_func costs"
  using  sum_is_modular 
  by (fastforce simp add: valid_modular_weight_func_def costs_def)

lemmas result_props_specialised = result_props[OF es_prop, of costs]

definition "unique P = (\<forall> x y. P x \<longrightarrow> P y \<longrightarrow> x = y)"

lemma injective_predicate_unique_split:
      "distinct xs \<Longrightarrow> unique P \<Longrightarrow> xs = xs11@[xx]@xs12 \<Longrightarrow> xs = xs21@[yy]@xs22
         \<Longrightarrow> P xx \<Longrightarrow> P yy \<Longrightarrow> xs11=xs21 \<and> xx = yy \<and> xs12 = xs22"
  by (smt (verit, del_insts) Cons_eq_appendI append.left_neutral append_Cons_eq_iff distinct.simps(2)
 distinct_append in_set_conv_decomp unique_def inj_on_eq_iff not_distinct_conv_prefix)

definition "last_in_list P xs y = (y \<in> set xs \<and> P y \<and> (\<nexists> xs1 xs2 z. xs = xs1@[y]@xs2 \<and> z \<in> set xs2 \<and> P z))"

lemma last_in_list_unique: "unique (last_in_list P xs)"
  by (auto simp add: unique_def last_in_list_def  )(smt (verit, del_insts) Un_iff append.assoc append_Cons in_set_conv_decomp_first insert_iff list.set(2) set_append)

lemma "(\<And> i. i < length l \<Longrightarrow> Some (l ! i) =
         find_best_candidate es costs (set (drop (i + 1) l)))
       \<Longrightarrow> (\<And> i. i < length l \<Longrightarrow> set (drop (i+1) l) \<in> F)
       \<Longrightarrow> length l \<le> length A_list \<Longrightarrow> l = rev (take (length l) A_list)"
proof(induction l)
  case Nil
  then show ?case by simp
next
  case (Cons x l)
  note IH = this
  show ?case 
  proof(cases A_list)
    case Nil
    then show ?thesis 
      using IH(4) by simp
  next
    case (Cons a arest)
    hence a1: "length A_list - Suc (length l) < length A_list"
      by auto
    have a2: " Suc (length l) \<le> length A_list"
      using Cons  IH(4) by simp
    have l_is:"l = rev (take (length l) A_list)"
      using IH(4) by (auto intro!: IH(1) IH(2)[of "_ + 1", simplified] IH(3)[of "Suc _", simplified])
    have split_off_first:"take ( length (x # l)) A_list = 
           take ( length l) A_list @[A_list ! ( (length l))]"
      using IH(4)
      by (simp add: take_Suc_conv_app_nth)
    have new_elem_in_es: "A_list ! ( (length l)) \<in> set es"
      using A_list_props(1) a2 all_in_E(1) es_prop(1) by auto
    thm IH(2)[of 0, simplified]
    have "x =  A_list ! (length l)"
    proof-
      have l_in_F:"set l \<in> F" 
        using IH(3)[of 0, simplified]  by simp
      hence l_in_E: "set l \<subseteq> E" 
        using ss_assum by(simp add:  set_system_def)
      have x_is_best_candidate:"find_best_candidate es costs (set l) = Some x"
        using IH(2)[of 0, simplified] by simp
      obtain es1 es2 where es_split:" es = es1 @ [x] @ es2" "x \<notin> set l"
            "insert x (set l) \<in> F"
            "(\<And> y. y\<in>E - set l \<Longrightarrow> insert y (set l) \<in> F \<Longrightarrow> elements_costs costs y \<le> elements_costs costs x)"
            "\<not> (\<exists>y\<in>set es2. y \<notin> set l \<and> insert y (set l) \<in> F \<and> elements_costs costs x \<le> elements_costs costs y)"
        using find_best_candidate_some_props[OF es_prop l_in_E x_is_best_candidate l_in_F] by auto 

      define P where "P =(\<lambda> x. (\<exists>es1 es2.
     es = es1 @ [x] @ es2 \<and> x \<notin> set l \<and> insert x (set l) \<in> F \<and>
     (\<forall>y\<in>E - set l. insert y (set l) \<in> F \<longrightarrow> elements_costs costs y \<le> elements_costs costs x)))"
      have x_last_P: "last_in_list P es x"
        using es_split
        by (auto simp add: last_in_list_def P_def )
           (metis DiffI append_Cons_eq_iff 
                distinct_append es_prop(1) es_prop(2) in_set_conv_decomp not_distinct_conv_prefix)
      have insert_new_element_is:"insert (A_list ! length l) (set (take (length l) A_list)) = (set (take (Suc (length l)) A_list))"
        using split_off_first by auto
      have " (A_list ! length l) \<in> set A_list" 
        using a2 by auto
      hence costs_of_new:"c (A_list ! length l) = 2 " 
        by(auto intro!: costs_are(1)simp add: A_list_props(1))   
      have A_last_P: "last_in_list P es ( A_list !  (length l))"
        unfolding P_def last_in_list_def
      proof(goal_cases)
        case 1
        define index where "index = length l"
        hence index_valid:"index < length A_list"
          by (simp add: a2 less_eq_Suc_le)
        have "A_list ! length l \<in> set es"
          using new_elem_in_es by auto
        moreover have es_split: "es = (take  (length es - index - 1) es) @ [A_list ! index]
                    @ rev (take index (A_list))"
          using index_valid
          by(unfold es_def append.assoc[symmetric], subst take_append, simp,
              subst rev_append[of  _ "[_]", simplified rev.simps(2)[of _ Nil]
                              rev.simps(1) append.left_neutral append_Cons[of _ Nil], symmetric]
               ,simp add:  take_Suc_conv_app_nth[OF index_valid, symmetric] rev_take)
        moreover have "A_list ! index \<notin> set l" 
          using  distinct_take[OF A_list_props(3)] l_is not_distinct_conv_prefix[of "take _ A_list"] 
                split_off_first
          by(unfold index_def[symmetric]) auto
        moreover have "insert (A_list ! index) (set l) \<in> F"
          using A_list_props(4)[OF  a2] IH(4) index_def insert_new_element_is l_is
          by(unfold index_def[symmetric]) simp 
        moreover have " (\<forall>y\<in>E - set l.
            insert y (set l) \<in> F \<longrightarrow> elements_costs costs y \<le> elements_costs costs (A_list ! length l))"  
        by (auto simp add:  elements_costs_def costs_of_new costs_def intro: costs_are(7))
      moreover have "(\<nexists>xs1 xs2 z.
        es = xs1 @ [A_list ! length l] @ xs2 \<and>
        z \<in> set xs2 \<and>
        (\<exists>es1 es2.
            es = es1 @ [z] @ es2 \<and>
            z \<notin> set l \<and>
            insert z (set l) \<in> F \<and>
            (\<forall>y\<in>E - set l. insert y (set l) \<in> F \<longrightarrow> elements_costs costs y \<le> elements_costs costs z)))"
      proof(rule ccontr, goal_cases)
        case 1
        then obtain xs1 xs2 z where  es_split2:
         "es = xs1 @ [A_list ! length l] @ xs2" "z \<in> set xs2""z \<notin> set l"
          by metis
        have "xs2 = rev (take index (A_list))"
          using  injective_predicate_unique_split[OF es_prop(2) _ es_split es_split2(1),
             of "\<lambda> x.  x = A_list ! index"]
          by(auto simp add: index_def[symmetric] unique_def) 
        moreover have "rev (take index (A_list)) =  l"
          using l_is by(simp add: index_def[symmetric])
        ultimately show False 
          using es_split2(2,3) by simp
      qed
      ultimately show ?case by(auto simp add: index_def)
    qed
    show "x = A_list ! length l" 
      using  A_last_P last_in_list_unique x_last_P
      by(force simp add: unique_def)
  qed 
  thus ?thesis 
    using l_is split_off_first by force
 qed
qed

lemma solution_looks_like:
"\<exists> others. greedy_algorithm es costs Nil = others @ [x] @ rev A_list"
  sorry


(*properties of the result*)

lemmas properties_of_result = initial_props[OF es_prop] result_props[OF es_prop]
                              algorithm_computes_basis[OF es_prop]

lemma no_opt_solution: "\<not> opt_solution costs (set (greedy_algorithm es costs Nil))"
proof-



