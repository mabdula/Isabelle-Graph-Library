theory Greedois_Optimisation
  imports Main Complex_Main Greedoids
begin

lemma max_n: "(\<And> n. P n \<Longrightarrow> n \<le> bound) \<Longrightarrow> P (n::nat) \<Longrightarrow> (\<exists> nmax. P nmax \<and> (\<nexists> m. m > nmax \<and> P m))"
  by (metis bounded_Max_nat leD)

definition accessible where "accessible E F \<longleftrightarrow> set_system E F \<and> ({} \<in> F) \<and> (\<forall>X. (X \<in> F - {{}}) \<longrightarrow>
(\<exists>x \<in> X.  X - {x} \<in> F))"
definition closed_under_union where "closed_under_union F \<longleftrightarrow> (\<forall>X Y. X \<in> F \<and> Y \<in> F \<longrightarrow> X \<union> Y \<in> F)"


definition maximal where "maximal P Z \<longleftrightarrow> (P Z \<and> (\<nexists> X. X \<supset> Z \<and> P X))"

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

definition strong_exchange_property where "strong_exchange_property E F \<longleftrightarrow> 
(\<forall>A B x. (A \<in> F \<and> B \<in> F \<and> A \<subseteq> B \<and> (maximal (\<lambda>B. B \<in> F) B) \<and> x \<in> E - B \<and> A \<union> {x} \<in> F) 
      \<longrightarrow> (\<exists>y \<in> B - A. A \<union> {y} \<in> F \<and> (B - {y}) \<union> {x} \<in> F))"

lemma  strong_exchange_propertyE: 
 "strong_exchange_property E F \<Longrightarrow> 
  ((\<And> A B x. A \<in> F \<Longrightarrow> B \<in> F \<Longrightarrow> A \<subseteq> B \<Longrightarrow> (maximal (\<lambda>B. B \<in> F) B) \<Longrightarrow> x \<in> E - B \<Longrightarrow> A \<union> {x} \<in> F 
      \<Longrightarrow> (\<exists>y \<in> B - A. A \<union> {y} \<in> F \<and> (B - {y}) \<union> {x} \<in> F))
 ==> P) \<Longrightarrow> P"
 by(auto simp add: strong_exchange_property_def)
  

locale greedy_algorithm = greedoid +
  fixes orcl::"'a \<Rightarrow> 'a set \<Rightarrow> bool"
  fixes es
  assumes orcl_correct: "\<And> X x. X \<subseteq> E \<Longrightarrow> x \<in> E - X \<Longrightarrow> X \<in> F \<Longrightarrow> orcl x X \<longleftrightarrow> insert x X \<in> F"
  assumes set_assum: "set es = E" "distinct es" 
begin

definition "valid_modular_weight_func (c::'a set \<Rightarrow> real) = 
               (\<forall> X Y. X \<subseteq> E \<and> Y \<subseteq> E \<longrightarrow> c (X \<union> Y) = c X +  c Y - c (X \<inter> Y))"

lemma modular_weightE: "valid_modular_weight_func c \<Longrightarrow> 
               ((\<And> X Y. X \<subseteq> E \<Longrightarrow> Y \<subseteq> E \<Longrightarrow> c (X \<union> Y) = c X +  c Y - c (X \<inter> Y)) \<Longrightarrow> P ) \<Longrightarrow> P"
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

definition "find_best_candidate c F' = 
           foldr (\<lambda> e acc. if e \<in> F' \<or> \<not> (orcl e F') then acc
                                                      else (case acc of None \<Rightarrow> Some e |
                                                            Some d \<Rightarrow>
                (if elements_costs c e > elements_costs c d then Some e
                             else Some d))) es None"

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

function (domintros) greedy_algorithm::"'a list \<Rightarrow> ('a set \<Rightarrow> real) \<Rightarrow> 'a list"  where
 "greedy_algorithm xs c = 
 (case  (find_best_candidate c (set xs)) of 
      Some e \<Rightarrow> greedy_algorithm (e#xs) c 
    | None \<Rightarrow> xs)"
  by pat_completeness auto

(*Invariants: solution in E, solution independent, solution distinct, solution elements are best candidates*)

named_theorems loop_props

lemma solution_remains_independent[loop_props]:
  assumes "greedy_algorithm_dom (xs, c)" "set xs \<in> F"
  shows "set (greedy_algorithm xs c) \<in> F"
  using assms(2)
proof(induction rule: greedy_algorithm.pinduct[OF assms(1)])
  case (1 xs c)
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
  assumes "greedy_algorithm_dom (xs, c)" "set xs \<in> F" "distinct xs"
  shows "distinct (greedy_algorithm xs c) "
  using assms(2,3)
proof(induction rule: greedy_algorithm.pinduct[OF assms(1)])
  case (1 xs c)
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
  shows "greedy_algorithm_dom (xs, c)"
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
                                                                         
definition "invar_find_best_cand c xs = (\<forall> i < length xs. 
                        Some (xs ! i) = find_best_candidate c (set (drop (i+1) xs)))"

lemma invar_find_best_candI: "(\<And>i.  i < length xs \<Longrightarrow>
                        Some (xs ! i) = find_best_candidate c (set (drop (i+1) xs)))
         \<Longrightarrow> invar_find_best_cand c xs"
  by(auto simp add: invar_find_best_cand_def)

lemma find_best_candidate_order[loop_props]:
  assumes "greedy_algorithm_dom (xs, c)" "set xs \<in> F" "distinct xs" "invar_find_best_cand c xs" 
  shows "invar_find_best_cand c  (greedy_algorithm xs c)"
  using assms(2,3,4)
proof(induction rule: greedy_algorithm.pinduct[OF assms(1)])
  case (1 xs c)
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
  assumes "greedy_algorithm_dom (xs, c)" "set xs \<in> F" "distinct xs"
  shows "find_best_candidate c (set (greedy_algorithm xs c))  = None"
  using assms(2,3)
proof(induction rule: greedy_algorithm.pinduct[OF assms(1)])
  case (1 xs c)
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

definition "invar_tails_indep xs = (\<forall> i \<le> length xs. set (drop i xs) \<in> F)"

lemma invar_tails_indepI: "(\<And> i. i \<le> length xs \<Longrightarrow> set (drop i xs) \<in> F) \<Longrightarrow> invar_tails_indep xs"
  by(auto simp add: invar_tails_indep_def)

lemma intermediate_solutions_indep[loop_props]:
  assumes "greedy_algorithm_dom (xs, c)" "set xs \<in> F" "invar_tails_indep xs"
  shows "invar_tails_indep (local.greedy_algorithm xs c)"
  using assms(2,3)
proof(induction rule: greedy_algorithm.pinduct[OF assms(1)])
  case (1 xs c)
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

lemma strong_exchange_max_modular_weight:
  assumes "valid_modular_weight_func c" "strong_exchange_property E F"  "empty_minimal c"
    shows "opt_solution c (set (greedy_algorithm Nil c))"
proof-
  have initial_props: "set Nil \<in> F" "card E = card E - card (set Nil)" "distinct Nil"
                      "invar_find_best_cand c Nil" "invar_tails_indep Nil"
    by(auto simp add: contains_empty_set intro: invar_find_best_candI invar_tails_indepI)
  note result_props =
      loop_props(3)[OF initial_props(1-3), of c] 
      loop_props(1)[OF loop_props(3)[OF initial_props(1-3)] initial_props(1), of c]
      loop_props(2)[OF loop_props(3)[OF initial_props(1-3)] initial_props(1,3), of c]
      loop_props(4)[OF loop_props(3)[OF initial_props(1-3)] initial_props(1,3,4)]
      loop_props(5)[OF loop_props(3)[OF initial_props(1-3)] initial_props(1,3), of c]
      loop_props(6)[OF loop_props(3)[OF initial_props(1-3)] initial_props(1,5), of c]
  define max_P where "max_P = (\<lambda> n. n \<le> length (greedy_algorithm Nil c) \<and>
                               (\<exists> B. opt_solution c B 
                               \<and> set (take n ( rev (greedy_algorithm Nil c))) \<subseteq> B))"
  have "\<exists>nmax. max_P nmax \<and> \<not> (\<exists>m>nmax. max_P m)"
    by(fastforce intro:  max_n[of max_P "length (greedy_algorithm Nil c)" 0] 
              simp add: max_P_def opt_solution_exists)
  then obtain k where k_prop: "max_P k" "\<not> (\<exists>m>k. max_P m)" by auto
  then obtain B where B_prop: "opt_solution c B" "set (take k ( rev (greedy_algorithm Nil c))) \<subseteq> B"
    using max_P_def by blast
  hence B_unfolded: "B \<in> F" "B \<subseteq> E" "maximal (\<lambda> B. B \<in> F) B"
    using  ss_assum
    by(auto simp add: opt_solution_def set_system_def maximal_def) 
  have k_length_less:"k \<le> length (greedy_algorithm Nil c)"
    using k_prop by(auto simp add: max_P_def) 
  moreover have "k < length (greedy_algorithm Nil c) \<Longrightarrow> False"
  proof(goal_cases)
    case 1
    note one = this
    hence length_non_zero: "length (local.greedy_algorithm [] c) > 0" by auto
    define B' where "B' = B - (set (take k ( rev (greedy_algorithm Nil c))))"
    have a3: "set (take k (rev (local.greedy_algorithm [] c))) \<subseteq> B" 
      by (simp add: B_prop(2))
        have a4: "maximal (\<lambda>B. B \<in> F) B"
          by (simp add: B_unfolded(3))
        have a5:"rev (local.greedy_algorithm [] c) ! k \<in> E" 
        proof-
          have "set  (local.greedy_algorithm [] c) \<in> F"
            using result_props(6) one by(auto simp add: invar_tails_indep_def)
          hence "set (local.greedy_algorithm [] c) \<subseteq> E"
            using ss_assum by(auto simp add: set_system_def)
          moreover have "rev (local.greedy_algorithm [] c) ! k \<in> set (local.greedy_algorithm [] c)" 
            by (metis length_rev nth_mem one set_rev)
          ultimately show ?thesis by auto
        qed
        have a6: "rev (local.greedy_algorithm [] c) ! k \<notin> B" 
        proof(rule ccontr, goal_cases 1)
          case 1
          hence "rev (local.greedy_algorithm [] c) ! k \<in> B" by simp
          hence "set (take (k+1) ( rev (greedy_algorithm Nil c))) \<subseteq> B" 
            using  a3  one set_take_union_nth[of k "rev (greedy_algorithm Nil c)", symmetric] 
            by simp
          hence "max_P (k+1)"
            using B_prop(1) less_iff_succ_less_eq max_P_def one by blast
          thus False 
            using k_prop(2) by force
        qed
    have "\<exists> y \<in> B'. insert y (set (take k (rev (greedy_algorithm Nil c)))) \<in> F \<and> 
                    (B - {y}) \<union> {(rev (greedy_algorithm Nil c)) ! k} \<in> F"
      proof(rule strong_exchange_propertyE[OF assms(2)], goal_cases)
        case 1
        have a1: "set (take k (rev (local.greedy_algorithm [] c))) \<in> F" 
          using diff_le_self[of ]  result_props(6) set_rev take_rev[of k "local.greedy_algorithm [] c"]
          by(simp add: invar_tails_indep_def)
        have a2: "B \<in> F" 
          using B_prop by (auto simp add: opt_solution_def maximal_def)
        have a4: "maximal (\<lambda>B. B \<in> F) B"
          by (simp add: B_unfolded(3))
        have a7: "insert (rev (local.greedy_algorithm [] c) ! k) 
                         (set (take k (rev (local.greedy_algorithm [] c)))) \<in> F"
          using HOL.spec[OF result_props(6)[simplified invar_tails_indep_def], 
                          of "length (local.greedy_algorithm [] c) - (k+1)"]
           one rev_rev_ident[of "greedy_algorithm [] c"] 
               rev_take[of "k+1" "rev (greedy_algorithm [] c)"] 
                  set_take_union_nth[of k "(rev (local.greedy_algorithm [] c))"]
          by (auto ,metis set_rev)         
        show ?case 
          using a1 a2 a3 a4 a5 a6 a7 
          by(auto intro!: 1[of "set (take k (rev (local.greedy_algorithm [] c)))" B
                           "rev (local.greedy_algorithm [] c) ! k", simplified] simp add: B'_def)
      qed
      then obtain y where y_props: " insert y (set (take k (rev (local.greedy_algorithm [] c)))) \<in> F"
                                   "B - {y} \<union> {rev (local.greedy_algorithm [] c) ! k} \<in> F" "y \<in> B'" by auto
      have ak_better_costs_than_y:
         "elements_costs c ((rev (local.greedy_algorithm [] c)) ! (k)) \<ge> elements_costs c y"
      proof-
        have cand_is: "Some (rev (local.greedy_algorithm [] c) ! (k )) = 
             find_best_candidate c (set (take k (rev (local.greedy_algorithm [] c))))"
          using HOL.spec[OF result_props(4)[simplified invar_find_best_cand_def], 
                    of "length (local.greedy_algorithm [] c) - Suc k"]
                 Suc_diff_Suc[of k "length (local.greedy_algorithm [] c)"]  one 
          by (fastforce simp add: rev_nth[OF one] take_rev)
       have take_k_in_F:"set (take k (rev (local.greedy_algorithm [] c))) \<in> F"
          using result_props(6) 
          by(simp add: invar_tails_indep_def take_rev)
       hence take_k_in_E:"set (take k (rev (local.greedy_algorithm [] c))) \<subseteq> E"
         using B_prop(2) B_unfolded(2) by blast
       have from_condidate_props:"(\<And> y. y\<in>E - set (take k (rev (local.greedy_algorithm [] c))) \<Longrightarrow>
             insert y (set (take k (rev (local.greedy_algorithm [] c)))) \<in> F \<Longrightarrow>
            elements_costs c y \<le> elements_costs c (rev (local.greedy_algorithm [] c) ! k))"
         using find_best_candidate_some_props[OF take_k_in_E cand_is[symmetric] take_k_in_F] by auto
       show ?thesis
         using y_props(3) B_unfolded(2) 
         by(auto intro: from_condidate_props[OF _ y_props(1)] simp add: B'_def)
     qed
     have new_b_better:"c (B - {y} \<union> {rev (local.greedy_algorithm [] c) ! k}) \<ge>  c B"
     proof-
       have "c B = c ((B-{y}) \<union> {y})"
         using B'_def insert_Diff y_props(3) by fastforce
       also have "... = c(B - {y}) + c {y} - c {}"
         using B_unfolded y_props(3) 
         by (subst modular_weight_split[OF assms(1)])(auto simp add: B'_def)
       also have "... =  c (B - {y}) +  elements_costs c y"
         by (simp add: elements_costs_def)
       also have "... \<le> c (B - {y}) + elements_costs c (rev (local.greedy_algorithm [] c) ! k)"
         by (simp add: ak_better_costs_than_y)
       also have "... = c (B - {y}) + c {(rev (local.greedy_algorithm [] c) ! k)} - c {}"
         by (simp add: elements_costs_def)
       also have "... = c (B - {y} \<union>  {(rev (local.greedy_algorithm [] c) ! k)})"
         using B_unfolded(2)  ss_assum y_props(2)  a6  
         by (subst modular_weight_split[OF assms(1)]) (fastforce simp add: set_system_def )+
       finally show ?thesis by simp
     qed
     obtain newB where newB: "maximal (\<lambda> X. X \<in> F) newB" 
          "(B - {y} \<union>  {(rev (local.greedy_algorithm [] c) ! k)}) \<subseteq> newB"
       using  y_props(2) by(force intro:has_max_superset)
     have newB_empty: "((newB - insert (rev (local.greedy_algorithm [] c) ! k) (B - {y})) \<inter> (B - {y})) =  {}"
       using Diff_disjoint Diff_insert2 Int_commute 
          by metis
     have newB_even_better: "c newB \<ge> c (B - {y} \<union> {rev (local.greedy_algorithm [] c) ! k})"
     proof-
       have "c newB = c ((newB - (B - {y} \<union>  {(rev (local.greedy_algorithm [] c) ! k)}))
                \<union> (B - {y} \<union>  {(rev (local.greedy_algorithm [] c) ! k)}))"
         using newB 
         by (metis Un_Diff_cancel2 sup_absorb1)
       also have "... = c ((newB - (B - {y} \<union>  {(rev (local.greedy_algorithm [] c) ! k)}))) 
                        + c (B - {y} \<union>  {(rev (local.greedy_algorithm [] c) ! k)}) - c{}"
         using  newB(1)  ss_assum  B_unfolded(2) a5
         by (subst modular_weight_split[OF assms(1)])(auto simp add:  set_system_def maximal_def newB_empty)
       also have  "... = c ((newB - (B - {y} \<union>  {(rev (local.greedy_algorithm [] c) ! k)}))) 
                        + (c (B - {y} \<union>  {(rev (local.greedy_algorithm [] c) ! k)}) - c{})" by simp
       also have  "... \<ge> c (( (B - {y} \<union>  {(rev (local.greedy_algorithm [] c) ! k)}))) 
                       " 
         using   newB(1)  ss_assum y_props(3)
         by(auto intro!: mp[OF HOL.spec[OF assms(3)[simplified empty_minimal_def]]] 
               simp add: B'_def set_system_def maximal_def)
       finally show ?thesis by simp
     qed
     have "(k+1) \<le> length (greedy_algorithm Nil c)"
       using one by auto
     moreover have " opt_solution c newB"
       using B_prop(1) newB(1) newB_even_better new_b_better by (force simp add:  opt_solution_def)
     moreover have "set (take (k+1) ( rev (greedy_algorithm Nil c))) \<subseteq> newB"
       using one  B'_def a3 newB(2) y_props(3) by (subst set_take_union_nth[symmetric])(auto simp add: B'_def)
     ultimately have "max_P (k+1)"
       by(auto simp add: max_P_def)
     thus False
       using k_prop(2) by auto
   qed
   ultimately have "k = length (local.greedy_algorithm [] c)" by force
   hence inB:"set (local.greedy_algorithm [] c) \<subseteq> B" 
     using B_prop(2) by simp
   moreover have "set (local.greedy_algorithm [] c) \<subset> B \<Longrightarrow> False"
   proof(goal_cases)
     case 1
     hence "card B > card (set (local.greedy_algorithm [] c))"
       using B_unfolded(2) finite_subset psubset_card_mono set_assum(1) by blast
     then obtain y where y_prop:"y \<in> B - set (local.greedy_algorithm [] c)" 
                         "insert y (set (local.greedy_algorithm [] c)) \<in> F"
       using B_unfolded(1) result_props(2) third_condition by auto
     moreover hence "y \<in> E - set (local.greedy_algorithm [] c) "
       using B_unfolded(2) by blast
     moreover have "\<nexists>x. x \<in> E - set (local.greedy_algorithm [] c) \<and> insert x (set (local.greedy_algorithm [] c)) \<in> F"
       using B_unfolded inB  result_props(2) 
       by (intro find_best_candidate_none[OF _ result_props(5)]) auto
     ultimately show False
       by blast
   qed
   ultimately have "B = set (local.greedy_algorithm [] c)"
     by blast
   thus ?thesis
     using B_prop(1) by auto
 qed



 











(*remove superflous E' subset of E, follows from E' in F*)
lemma greedy_algo_best_candidate: assumes "valid_modular_weight_func c" "E' \<subseteq> E" "E' \<in> F"
  shows "find_best_candidate c (greedy_algorithm_greedoid E' c) = None"
proof-
  have in_dom: " greedy_algorithm_greedoid_dom (E', c)"   by (simp add: greedy_algo_term)

  show ?thesis
    using assms
  proof(induction rule: greedy_algorithm_greedoid.pinduct[OF in_dom])
    case (1 F' c)
    show ?case 
    apply(subst greedy_algorithm_greedoid.psimps[OF 1(1)])
      apply(subst if_not_P)
      apply (simp add: "1.prems"(2) "1.prems"(3))
    proof(cases "find_best_candidate c F'", goal_cases)
      case 1
      then show ?case by simp
    next
      case (2 e)
      show ?case 
        apply (simp add: 2)
        apply(subst option.sel[of e, simplified 2[symmetric], symmetric])
        apply(rule 1(2)[simplified])
            apply (simp add: "1.prems"(2) "1.prems"(3))
           apply(rule 2)
          apply (simp add: "1.prems"(1))
         apply (metis "1.prems"(2) "2" find_best_candidate_in_es in_set_member option.sel set_assum)
      
        by (metis "1.prems"(2) "2" Diff_iff find_best_candidate_in_es find_best_candidate_nexists
 find_best_candidate_notin_F' in_set_member option.collapse order_refl set_assum)
     
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

thm "local.greedy_algorithm_greedoid.psimps"

lemma greedy_algo_in_F_general: 
  assumes "valid_modular_weight_func c" "E' \<in> F"
  shows "(greedy_algorithm_greedoid E' c) \<in> F"
proof-
  have in_dom: " greedy_algorithm_greedoid_dom (E', c)"   by (simp add: greedy_algo_term)
  show ?thesis
    using assms
  proof(induction rule: greedy_algorithm_greedoid.pinduct[OF in_dom])
    case (1 F' c)
    note IH = this
    show ?case 
      apply(subst greedy_algorithm_greedoid.psimps[OF 1(1)])
      apply(subst if_not_P)
       apply (metis "1.prems"(2) set_system_def ss_assum)
    proof(cases "find_best_candidate c F'", goal_cases)
      case 1
      then show ?case 
        by (simp add: "1.prems"(2))
    next
      case (2 e)
      show ?case
        apply(simp add: 2)
        apply(rule IH(2)[simplified  option.sel[of e, simplified 2[symmetric]], simplified])
           apply (metis IH(4) set_system_def ss_assum)
          apply(rule 2)
         apply (simp add: IH(3))
        using  find_best_candidate_indep[OF IH(4)  2] by simp
    qed
  qed
qed


lemma greedy_algo_in_F: 
  assumes "valid_modular_weight_func c"
  shows "(greedy_algorithm_greedoid {} c) \<in> F"
  by (simp add: assms contains_empty_set greedy_algo_in_F_general)
(*
proof (cases "find_best_candidate c {} = None")
  case True
  then have "greedy_algorithm_greedoid {} c = {}" using greedy_algorithm_greedoid.psimps greedy_algo_term contains_empty_set  by simp
  then show ?thesis using contains_empty_set by simp
next
  case False
  then obtain e where "find_best_candidate c {} = Some e" by auto
  define greedy_in_F::"'a set \<Rightarrow> ('a set \<Rightarrow> real) \<Rightarrow> bool" where "greedy_in_F = (\<lambda>F' c'. (greedy_algorithm_greedoid F' c') \<in> F)"
  have "greedy_algorithm_greedoid_dom ({}, c)" using greedy_algo_term by simp
  then have "greedy_algorithm_greedoid_dom ({}, c) \<Longrightarrow> (\<And>F' c.
    greedy_algorithm_greedoid_dom (F', c) \<Longrightarrow>
    (\<And>x2. \<not> \<not> F' \<subseteq> E \<and> F' \<in> F \<Longrightarrow>
           find_best_candidate c F' = Some x2 \<Longrightarrow>
           (greedy_in_F (F' \<union> {the (find_best_candidate c F')})) c) \<Longrightarrow>
    greedy_in_F F' c) \<Longrightarrow> greedy_in_F {} c" using greedy_algorithm_greedoid.pinduct using \<open>greedy_in_F = (\<lambda>F' c'. (greedy_algorithm_greedoid F' c') \<in> F)\<close> by metis
  then have "(\<And>F' c.
    greedy_algorithm_greedoid_dom (F', c) \<Longrightarrow>
    (\<And>x2. \<not> \<not> F' \<subseteq> E \<and> F' \<in> F \<Longrightarrow>
           find_best_candidate c F' = Some x2 \<Longrightarrow>
           (greedy_in_F (F' \<union> {the (find_best_candidate c F')})) c) \<Longrightarrow>
    greedy_in_F F' c) \<Longrightarrow> greedy_in_F {} c" using \<open>greedy_algorithm_greedoid_dom({}, c)\<close> by simp
  have "(\<And>F' c.
    greedy_algorithm_greedoid_dom (F', c) \<Longrightarrow>
    (\<And>x2. \<not> \<not> F' \<subseteq> E \<and> F' \<in> F \<Longrightarrow>
           find_best_candidate c F' = Some x2 \<Longrightarrow>
           (greedy_in_F (F' \<union> {the (find_best_candidate c F')})) c) \<Longrightarrow>
    greedy_in_F F' c)"
  proof -
    fix F' c
    show "greedy_algorithm_greedoid_dom (F', c) \<Longrightarrow>
    (\<And>x2. \<not> \<not> F' \<subseteq> E \<and> F' \<in> F \<Longrightarrow>
           find_best_candidate c F' = Some x2 \<Longrightarrow>
           (greedy_in_F (F' \<union> {the (find_best_candidate c F')})) c) \<Longrightarrow>
    greedy_in_F F' c"
    proof -
      assume "greedy_algorithm_greedoid_dom(F', c)"
      show "(\<And>x2. \<not> \<not> F' \<subseteq> E \<and> F' \<in> F \<Longrightarrow>
           find_best_candidate c F' = Some x2 \<Longrightarrow>
           (greedy_in_F (F' \<union> {the (find_best_candidate c F')})) c) \<Longrightarrow>
    greedy_in_F F' c"
      proof -
        assume "(\<And>x2. \<not> \<not> F' \<subseteq> E \<and> F' \<in> F \<Longrightarrow>
           find_best_candidate c F' = Some x2 \<Longrightarrow>
           (greedy_in_F (F' \<union> {the (find_best_candidate c F')})) c)"
        have 2: "greedy_algorithm_greedoid F' c = (if \<not> (F' \<subseteq> E \<and> F' \<in> F) then undefined
 else case find_best_candidate c F' of None \<Rightarrow> F'
      | Some e \<Rightarrow>
          greedy_algorithm_greedoid (F' \<union> {the (find_best_candidate c F')}) c)" using \<open>greedy_algorithm_greedoid_dom(F', c)\<close> greedy_algorithm_greedoid.psimps by simp
        show ?thesis
        proof (cases "F' \<subseteq> E \<and> F' \<in> F")
          case True
          then show ?thesis
          proof (cases "find_best_candidate c F' = None")
            case True
            then have "greedy_algorithm_greedoid F' c = F'" using 2 True \<open>greedy_algorithm_greedoid_dom(F', c)\<close> 
            then show ?thesis sorry
          next
            case False
            then show ?thesis sorry
          qed
        next
          case False
          then show ?thesis using 2 sorry
        qed
    
  then show ?thesis 
qed
    
  qed
qed
*)
lemma valid_weight_prop: assumes "X \<subset> Y" "valid_modular_weight_func c" "Y \<noteq> {}" "X \<in> F"
"Y \<in> F"
  shows "c Y > c X"
proof (cases "X = {}")
  case True
  then have "c X = 0" using assms unfolding valid_modular_weight_func_def by fast
  have "Y \<subseteq> E" using assms ss_assum unfolding set_system_def by simp
  have "finite E" using ss_assum unfolding set_system_def by simp
  then have "finite Y" using finite_subset \<open>Y \<subseteq> E\<close> by auto
  let ?l1 = "{c {e} | e. e \<in> Y}"
  have "finite ?l1" using \<open>finite Y\<close> assms(2) unfolding valid_modular_weight_func_def by fast
  then have "c Y = sum (\<lambda>x. x) ?l1 \<and> c Y > 0" using assms \<open>Y \<subseteq> E\<close> unfolding valid_modular_weight_func_def by blast
  then show ?thesis using \<open>c X = 0\<close> unfolding valid_modular_weight_func_def by metis
next
  case False
   have "X \<subseteq> E" using assms ss_assum unfolding set_system_def by simp
  have "finite E" using ss_assum unfolding set_system_def by simp
  then have "finite X" using finite_subset \<open>X \<subseteq> E\<close> by auto
  let ?l2 = "{c {e} | e. e \<in> X}"
  have "finite ?l2" using \<open>finite X\<close> assms(2) unfolding valid_modular_weight_func_def by fast
  then have "c X = sum (\<lambda>x. x) ?l2 \<and> c X > 0" using assms \<open>X \<subseteq> E\<close> False unfolding valid_modular_weight_func_def by blast
   have "Y \<subseteq> E" using assms ss_assum unfolding set_system_def by simp
  have "finite E" using ss_assum unfolding set_system_def by simp
  then have "finite Y" using finite_subset \<open>Y \<subseteq> E\<close> by auto
  let ?l1 = "{c {e} | e. e \<in> Y}"
  have "finite ?l1" using \<open>finite Y\<close> assms(2) unfolding valid_modular_weight_func_def by fast
  then have "c Y = sum (\<lambda>x. x) ?l1 \<and> c Y > 0" using assms \<open>Y \<subseteq> E\<close> unfolding valid_modular_weight_func_def by blast
  let ?l3 = "{c {e} | e. e \<in> Y - X}"
  have "Y - X \<noteq> {}" using assms False by simp
  then have "?l3 \<noteq> {}" using assms unfolding valid_modular_weight_func_def by fast
  have "(Y - X) \<subseteq> E" using \<open>Y \<subseteq> E\<close> by auto
  then have "finite (Y - X)" using \<open>finite Y\<close> finite_subset by auto
  (*then have "finite ?l3" using assms(2) \<open>Y - X \<noteq> {}\<close> \<open>(Y - X) \<subseteq> E\<close> unfolding valid_modular_weight_func_def by blast *)
  have "?l1 = ?l2 \<union> ?l3" using assms by auto
  then have "sum (\<lambda>x. x) ?l1 = sum (\<lambda>x. x) (?l2 \<union> ?l3)" by simp
  also have "... = sum (\<lambda>x. x) ?l2 + sum (\<lambda>x. x) ?l3" sorry
    show ?thesis sorry
(*    oops
    
    using assms unfolding valid_modular_weight_func_def by auto
  finally have prop_one: "sum (\<lambda>x. x) ?l2 = sum (\<lambda>x. x) ?l1 + sum (\<lambda>x. x) ?l3" by simp
  have "sum (\<lambda>x. x) ?l3 > 0" using \<open>finite ?l3\<close> \<open>?l3 \<noteq> {}\<close>  assms unfolding valid_modular_weight_func_def by auto
  then have "sum (\<lambda>x. x) ?l2 > sum (\<lambda>x. x) ?l1" using assms unfolding valid_modular_weight_func_def by auto
  then show ?thesis using X_val Y_val by simp*)
qed

lemma maximum_weight_prop: assumes "valid_modular_weight_func c" "maximum_weight_set c X" "X \<noteq> {}"
  shows "maximal (\<lambda>X. X \<in> F) X"
  unfolding maximal_def
proof
  show "X \<in> F" using assms unfolding maximum_weight_set_def by simp
  show "\<nexists>Xa. X \<subset> Xa \<and> Xa \<in> F"
  proof
    assume "\<exists>Xa. X \<subset> Xa \<and> Xa \<in> F"
    then obtain Y where Y_prop: "X \<subset> Y \<and> Y \<in> F" by auto
    then have "Y \<noteq> {}" using assms(3) by auto
    then have "c Y > c X" using valid_weight_prop assms(1) assms(3) Y_prop \<open>X \<in> F\<close> by auto
    then show False using assms(2) Y_prop unfolding maximum_weight_set_def by auto
  qed
qed



lemma greedy_algo_maximal: assumes "valid_modular_weight_func c" 
"maximum_weight_set c B " " (greedy_algorithm_greedoid {} c) \<inter> B \<noteq> {}" 
shows "\<not> ((greedy_algorithm_greedoid {} c) \<subset> B)"
proof
  assume assum1: "greedy_algorithm_greedoid {} c \<subset> B"
  let ?A = "greedy_algorithm_greedoid {} c"
  have "B \<in> F" using assms unfolding maximum_weight_set_def by auto
  have "?A \<in> F" using assms(1) greedy_algo_in_F by simp
  have "finite E" using ss_assum unfolding set_system_def by simp
  have "B \<subseteq> E" using \<open>B \<in> F\<close> using ss_assum unfolding set_system_def by simp
  then have "finite B" using \<open>finite E\<close> finite_subset by auto
  have "B \<noteq> {}" using assms by auto
  then have "card ?A < card B" using \<open>finite B\<close> assum1 psubset_card_mono by auto
  then have "\<exists>y \<in> B - ?A. ?A \<union> {y} \<in> F" using third_condition \<open>?A \<in> F\<close> \<open>B \<in> F\<close> by simp
  then obtain y where y_prop: "y \<in> B - ?A" "?A \<union> {y} \<in> F" by auto
    let ?Y = "{y | y. y \<in> B - ?A \<and> ?A \<union> {y} \<in> F}"
    have "y \<in> ?Y" using y_prop by simp
    have "finite ?Y" using \<open>finite B\<close> by simp
    have "?Y \<noteq> {}" using \<open>y \<in> ?Y\<close> by auto
    let ?l1 = "{c {e} | e. e \<in> ?Y}"
    have "finite ?l1" using assms(1) unfolding valid_modular_weight_func_def sorry
    have "?l1 \<noteq> {}" using assms(1) unfolding valid_modular_weight_func_def sorry
    then have "Max ?l1 \<in> ?l1" using Max_in \<open>finite ?l1\<close> by auto
    then have "\<forall>x. x\<in> ?l1 \<longrightarrow> x \<le> Max ?l1" using \<open>finite ?l1\<close> by auto
    then obtain e where "e \<in> ?Y" "c {e} = Max ?l1" using \<open>finite ?l1\<close> \<open>finite ?Y\<close> \<open>Max ?l1 \<in> ?l1\<close>
      by auto
    have "find_best_candidate c ?A = Some e" unfolding find_best_candidate_def
      sorry
    then show False using greedy_algo_best_candidate assms by auto
  qed


lemma weight_func_empty: assumes "X \<in> F" "valid_modular_weight_func c" "X \<noteq> {}"
  shows "c X > c {}" 
proof -
  have "c {} = 0" using assms unfolding valid_modular_weight_func_def try0
  have "X \<subseteq> E" using assms ss_assum unfolding set_system_def by simp
  let ?l = "{c {e}| e. e \<in> X}"
  have "c X = sum (\<lambda>x. x) ?l \<and> c X > 0" using assms \<open>X \<subseteq> E\<close> unfolding valid_modular_weight_func_def by blast
  then show ?thesis using \<open>c {} = 0\<close> by simp
qed

lemma greedy_algo_nonempty: assumes "valid_modular_weight_func c" "X \<in> F" "X \<noteq> {}"
  shows "greedy_algorithm_greedoid {} c \<noteq> {}"
  sorry


lemma set_union_ineq: assumes "valid_modular_weight_func c" "e \<in> E" "f \<in> E" "c {e} \<ge> c {f}" "Z \<subseteq> E"
"{e} \<union> Z \<in> F" "{f} \<union> Z \<in> F"
shows "c ({e} \<union> Z) \<ge> c ({f} \<union> Z)"
  sorry



lemma exists_maximal_weight_set: assumes "\<not> maximum_weight_set c (greedy_algorithm_greedoid {} c)" 
"valid_modular_weight_func c" "greedoid E F"
shows "\<exists>l. set l = (greedy_algorithm_greedoid {} c) \<and>  (\<forall>i. i \<le> length l \<longrightarrow> (set (take i l) \<in> F \<and> (\<forall>y. y \<in> E \<and> set (take (i - 1) l) \<union> {y} \<in> F \<longrightarrow> c {nth l i} \<ge> c {y}))) \<and> 
distinct l \<and> (\<exists>X. maximum_weight_set c X \<and> (\<exists>i. i < length l \<and> set (take i l) \<subseteq> X \<and> (\<nexists>j. j > i \<and> j \<le> length l \<and> (set (take j l)) \<subseteq> X) \<and> 
(\<forall>Y. maximum_weight_set c Y \<longrightarrow> (\<exists>k. set (take k l) \<subseteq> Y \<and> k < length l \<and> (\<nexists>j. j > k \<and> j \<le> length l \<and> (set (take j l)) \<subseteq> Y) \<and> k \<le> i))))" 
proof -
  let ?A = "greedy_algorithm_greedoid {} c"
  have "accessible E F" using assms(3) greedoid_accessible by simp
  then have "set_system E F" unfolding accessible_def by simp
  have "?A \<in> F" using greedy_algo_in_F assms(2) by simp
  then have "?A \<subseteq> E" using ss_assum unfolding set_system_def by simp
  then have "\<exists>l. set l = (greedy_algorithm_greedoid {} c) \<and>  (\<forall>i. i \<le> length l \<longrightarrow> set (take i l) \<in> F) \<and> distinct l" using 
accessible_property \<open>accessible E F\<close> \<open>?A \<in> F\<close> \<open>set_system E F\<close> contains_empty_set by blast
  then obtain l where l_prop: "set l = (greedy_algorithm_greedoid {} c) \<and>  (\<forall>i. i \<le> length l \<longrightarrow> set (take i l) \<in> F) \<and> distinct l" by auto
  have "\<exists>X. maximum_weight_set c X" using max_weight_exists assms(2-3) by simp
  then obtain B where "maximum_weight_set c B" by auto
  have fact1: "(\<exists>i. i < length l \<and> set (take i l) \<subseteq> B \<and> (\<nexists>j. j > i \<and> j \<le> length l \<and> (set (take j l)) \<subseteq> B) \<and> 
(\<forall>Y. maximum_weight_set c Y \<longrightarrow> (\<exists>k. set (take k l) \<subseteq> Y \<and> k < length l \<and> (\<nexists>j. j > k \<and> j \<le> length l \<and> (set (take j l)) \<subseteq> Y) \<and> k \<le> i)))"
  proof (cases "\<forall>i. i \<le> length l \<and> B \<inter> set (take i l) = {}")
    case True
    then show ?thesis sorry
  next
    case False   
    then show ?thesis sorry
  qed
  have fact2: "\<forall>i. i \<le> length l \<longrightarrow> (\<forall>y. y \<in> E \<and> set (take (i - 1) l) \<union> {y} \<in> F \<longrightarrow> c {nth l i} \<ge> c {y})" sorry
  then show ?thesis using l_prop \<open>maximum_weight_set c B\<close> fact1 
      by (smt (verit))
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
        assume assum2: "strong_exchange_property E F"
        show "valid_modular_weight_func c \<Longrightarrow>
    maximum_weight_set c (greedy_algorithm_greedoid {} c)"
        proof -
          assume assum3: "valid_modular_weight_func c"
          show "maximum_weight_set c (greedy_algorithm_greedoid {} c)"
          proof (rule ccontr)
            assume assum4: "\<not> maximum_weight_set c (greedy_algorithm_greedoid {} c)"
            let ?A = "greedy_algorithm_greedoid {} c"
            have "accessible E F" using assms greedoid_accessible by auto 
            have "?A \<in> F" using greedy_algo_in_F using assum3 by simp
            then have "\<exists>l. set l = (greedy_algorithm_greedoid {} c) \<and>  (\<forall>i. i \<le> length l \<longrightarrow> (set (take i l) \<in> F \<and> (\<forall>y. y \<in> E \<and> set (take (i - 1) l) \<union> {y} \<in> F \<longrightarrow> c {nth l i} \<ge> c {y}))) \<and> 
distinct l \<and> (\<exists>X. maximum_weight_set c X \<and> (\<exists>i. i < length l \<and> set (take i l) \<subseteq> X \<and> (\<nexists>j. j > i \<and> j \<le> length l \<and> (set (take j l)) \<subseteq> X) \<and> 
(\<forall>Y. maximum_weight_set c Y \<longrightarrow> (\<exists>k. set (take k l) \<subseteq> Y \<and> k < length l \<and> (\<nexists>j. j > k \<and> j \<le> length l \<and> (set (take j l)) \<subseteq> Y) \<and> k \<le> i))))"
              using assum3  exists_maximal_weight_set assum4 assms by auto
            then obtain l where l_prop: "set l = (greedy_algorithm_greedoid {} c) \<and>  (\<forall>i. i \<le> length l \<longrightarrow> (set (take i l) \<in> F \<and> (\<forall>y. y \<in> E \<and> set (take (i - 1) l) \<union> {y} \<in> F \<longrightarrow> c {nth l i} \<ge> c {y}))) \<and> 
distinct l \<and> (\<exists>X. maximum_weight_set c X \<and> (\<exists>i. i < length l \<and> set (take i l) \<subseteq> X \<and> (\<nexists>j. j > i \<and> j \<le> length l \<and> (set (take j l)) \<subseteq> X) \<and> 
(\<forall>Y. maximum_weight_set c Y \<longrightarrow> (\<exists>k. set (take k l) \<subseteq> Y \<and> k < length l \<and> (\<nexists>j. j > k \<and> j \<le> length l \<and> (set (take j l)) \<subseteq> Y) \<and> k \<le> i))))"
              by auto
            then obtain B where B_prop: "maximum_weight_set c B \<and> (\<exists>i. i < length l \<and> set (take i l) \<subseteq> B \<and> (\<nexists>j. j > i \<and> j \<le> length l \<and> (set (take j l)) \<subseteq> B) \<and> 
(\<forall>Y. maximum_weight_set c Y \<longrightarrow> (\<exists>k. set (take k l) \<subseteq> Y \<and> k < length l \<and> (\<nexists>j. j > k \<and> j \<le> length l \<and> (set (take j l)) \<subseteq> Y) \<and> k \<le> i)))" by auto
            then obtain k where k_prop: "k < length l \<and> set (take k l) \<subseteq> B \<and> (\<nexists>j. j > k \<and> j \<le> length l \<and>  (set (take j l)) \<subseteq> B) \<and> (\<forall>Y. maximum_weight_set c Y \<longrightarrow> (\<exists>i. set (take i l) \<subseteq> Y \<and> i < length l \<and> ((\<nexists>j. j > i \<and> j \<le> length l \<and> (set (take j l)) \<subseteq> Y))  \<and> i \<le> k))" by auto
            have "B \<in> F" using B_prop unfolding maximum_weight_set_def by simp
            then have "B \<subseteq> E" using ss_assum unfolding set_system_def by simp
            have "B \<noteq> ?A" using assum4 B_prop by auto
            have "?A \<subseteq> E" using \<open>?A \<in> F\<close> ss_assum unfolding set_system_def by auto
            show False
            proof (cases "B = {}")
              case True
              then have "?A \<noteq> {}" using \<open>B \<noteq> ?A\<close> by simp
              then have "c ?A > c B" using assum3 weight_func_empty \<open>?A \<in> F\<close> True by simp
              then show ?thesis using B_prop unfolding maximum_weight_set_def using \<open>?A \<in> F\<close> by auto
            next
              case False
              then have "?A \<noteq> {}" using assum3 \<open>B \<in> F\<close> greedy_algo_nonempty by simp
              have "l \<noteq> []" using l_prop False by auto
              show ?thesis
              proof -
                have "set l = ?A" using l_prop by simp
                have "l \<noteq> []" using \<open>?A \<noteq> {}\<close> l_prop by auto
                have "(nth l k) \<notin> B"
                proof
                  assume assum5: "(nth l k) \<in> B"
                  have set_prop1: "(set (take k l)) \<union> {nth l (k)} = set (take (k+1) l)" using set_take_union_nth k_prop by auto
                  have "set (take k l) \<union> {nth l k} \<subseteq> B" using k_prop assum5 by simp
                  then have set_prop2: "set (take (k+1) l) \<subseteq> B" using set_prop1 by blast
                  have "k + 1 > k" by simp
                  have "k + 1 \<noteq> length l"
                  proof
                    assume "k + 1 = length l"
                    then have "set (take (length l) l) \<subseteq> B" using set_prop2 by simp
                    show False
                    proof (cases "set (take (length l) l) = B")
                      case True
                      then have "?A = B" using \<open>set l = ?A\<close> by simp
                      then show ?thesis using B_prop assum4 by simp
                    next
                      case False
                      then have "set (take (length l) l) \<subset> B" using set_prop2 \<open>k + 1 = length l\<close> by fastforce
                      then have "?A \<subset> B" using \<open>set l = ?A\<close> by simp
                      then have "?A \<inter> B \<noteq> {}" using \<open>?A \<noteq> {}\<close> \<open>B \<noteq> {}\<close> by auto 
                      then show ?thesis using greedy_algo_maximal assum3 B_prop \<open>?A \<subset> B\<close> by auto
                    qed
                  qed
                  then have "k + 1 < length l" using k_prop by simp
                  then show False using set_prop2 k_prop by simp
                qed
                let ?x = "nth l k"
                have "?x \<in> ?A" using \<open>l \<noteq> []\<close> \<open>set l = ?A\<close> 
                  by (metis k_prop nth_mem)
                have "?x \<in> E" using \<open>(nth l k) \<in> ?A\<close> \<open>?A \<subseteq> E\<close> by auto
                then have "?x \<in> E - B" using \<open>?x \<notin> B\<close> by simp
                have set_prop1: "(set (take k l)) \<union> {?x} = set (take (k+1) l)" using set_take_union_nth k_prop by auto
                also have "... \<in> F" using k_prop l_prop by simp
                finally have "(set (take k l)) \<union> {?x} \<in> F" by simp 
                have "maximal (\<lambda>Z. Z \<in> F) B" using maximum_weight_prop assum3 \<open>B \<noteq> {}\<close> B_prop by simp
                have "set (take k l) \<in> F" using l_prop k_prop by simp
                then have "(\<exists>y. y \<in> B - (set (take k l)) \<and> set (take k l) \<union> {y} \<in> F \<and> (B - {y}) \<union> {?x} \<in> F)" using assum2 
                  unfolding strong_exchange_property_def using  \<open>B \<in> F\<close> \<open>?x \<in> E - B\<close>
                    \<open>maximal (\<lambda>Z. Z \<in> F) B\<close> k_prop \<open>set (take k l) \<union> {?x} \<in> F\<close> by blast
                then obtain y where y_prop: "y \<in> B - set (take k l) \<and> (set (take k l)) \<union> {y} \<in> F \<and> (B - {y}) \<union> {?x} \<in> F" by auto
                then have "y \<in> E" using \<open>B \<subseteq> E\<close> by auto
                have "y \<in> B" using y_prop by simp
                have "B - {y} \<subseteq> E" using \<open>B \<subseteq> E\<close> by auto
                have "(B - {y}) \<union> {?x} \<in> F" using y_prop by simp
                have l_prop2: "(\<forall>i \<le> length l. (\<forall>y \<in> E. set (take (i - 1) l) \<union> {y} \<in> F \<longrightarrow> c {nth l i} \<ge> c {y}))"
                  using l_prop by simp
                have "k + 1 - 1 = k" by simp
                have "set (take k l) \<union> {y} \<in> F"  using y_prop by simp
                then have "set (take ((k + 1) - 1) l) \<union> {y} \<in> F" using \<open>(k + 1) - 1 = k\<close> by fastforce
                then have "{y} \<union> set (take ((k + 1) - 1) l) \<in> F" by simp
                then have "k + 1 \<le> length l" using k_prop by simp
                then have " c {?x} \<ge> c {y}" 
                proof-

                  using \<open>y \<in> E\<close> l_prop2 \<open>set (take ((k + 1) - 1) l) \<union> {y} \<in> F\<close>
(*No proof for above line! It is quite direct*)
                have "{?x} \<union> (B - {y}) \<in> F" using y_prop by simp
                have "(B - {y}) \<union> {y} = B" using \<open>y \<in> B\<close> by auto
                then have "(B - {y}) \<union> {y} \<in> F" using \<open>B \<in> F\<close> by simp 
                then have "c ({?x} \<union> (B - {y})) \<ge> c ({y} \<union> (B - {y}))" using
                      set_union_ineq assum3 \<open>c {?x} \<ge> c {y}\<close> \<open>y \<in> E\<close> \<open>?x \<in> E\<close> \<open>(B - {y}) \<subseteq> E\<close> \<open>{?x} \<union> (B - {y}) \<in> F\<close>  
                  by (metis sup_commute)
                then have set_prop: "c ({?x} \<union> (B - {y})) \<ge> c B" using \<open>y \<in> B\<close> 
                  by (simp add: insert_absorb)
                have "maximum_weight_set c ({?x} \<union> (B - {y}))"
                proof (cases "c ({?x} \<union> (B - {y})) = c B")
                  case True
                  then show ?thesis using B_prop \<open>(B - {y}) \<union> {?x} \<in> F\<close> unfolding maximum_weight_set_def by simp
                next
                  case False
                  then have "c ({?x} \<union> (B - {y})) > c B" using set_prop by simp
                  show ?thesis 
                  proof (rule ccontr)
                    assume "\<not> maximum_weight_set c ({?x} \<union> (B - {y}))"
                    then have "c ({?x} \<union> (B - {y})) \<le> c B" using B_prop \<open>(B - {y}) \<union> {?x} \<in> F\<close> unfolding maximum_weight_set_def by auto
                    then show False using \<open>c ({?x} \<union> (B - {y})) > c B\<close> by simp
                  qed
                qed
                let ?Y = "{?x} \<union> (B - {y})"
                have "(\<exists>i. set (take i l) \<subseteq> ?Y \<and> i < length l \<and> ((\<nexists>j. j > i \<and> j \<le> length l \<and> (set (take j l)) \<subseteq> ?Y))  \<and> i \<le> k)"
                  using k_prop \<open>maximum_weight_set c ?Y\<close> by simp
                then obtain i where i_prop: "set (take i l) \<subseteq> ?Y \<and> i < length l \<and> ((\<nexists>j. j > i \<and> j \<le> length l \<and> (set (take j l)) \<subseteq> ?Y))  \<and> i \<le> k" by auto
                have "set (take k l) \<subseteq> B - {y}" using k_prop y_prop by auto
                then have "set (take k l) \<subseteq> {?x} \<union> (B - {y})" by auto
                  have set_prop3: "set (take (k+1) l) \<subseteq> ?Y"
                  proof
                    fix x
                    show "x \<in> set (take (k + 1) l) \<Longrightarrow> x \<in> {l ! k} \<union> (B - {y})"
                    proof -
                      assume x_assum: "x \<in> set (take (k + 1) l)"
                      show "x \<in> {l ! k} \<union> (B - {y})"
                      proof (cases "x \<in> set (take k l)")
                        case True
                        then show ?thesis using \<open>set (take k l) \<subseteq> {?x} \<union> (B - {y})\<close> by auto
                      next
                        case False
                        then have "x \<in> {?x}" using \<open>(set (take k l)) \<union> {?x} = set (take (k + 1) l)\<close> using x_assum by auto
                        then show ?thesis by simp
                      qed
                    qed
                  qed
                  have "i < k + 1" using i_prop by simp
                  then show False using set_prop3 i_prop \<open>k + 1 \<le> length l\<close> by simp
                qed
              qed
            qed
          qed
        qed
      qed
      show "\<forall>c. valid_modular_weight_func c \<longrightarrow>
        maximum_weight_set c (greedy_algorithm_greedoid {} c) \<Longrightarrow>
    strong_exchange_property E F "
      proof -
        assume assum6: "\<forall>c. valid_modular_weight_func c \<longrightarrow>
        maximum_weight_set c (greedy_algorithm_greedoid {} c)"
        show "strong_exchange_property E F"
        proof (rule ccontr)
          assume "\<not> strong_exchange_property E F"
          then have "\<exists>A B x. A \<in> F \<and> maximal (\<lambda>B. B \<in> F) B \<and> A \<subseteq> B \<and> x \<in> E - B \<and> A \<union> {x} \<in> F \<and> 
        (\<forall>y \<in> B - A. \<not> (A \<union> {y} \<in> F \<and> (B - {y}) \<union> {x} \<in> F))" unfolding strong_exchange_property_def by auto
          then obtain A B x where A_B_x_prop: "A \<in> F \<and> maximal (\<lambda>B. B \<in> F) B \<and> A \<subseteq> B \<and> x \<in> E - B \<and> A \<union> {x} \<in> F \<and> 
        (\<forall>y \<in> B - A. \<not> (A \<union> {y} \<in> F \<and> (B - {y}) \<union> {x} \<in> F))" by auto
          show False
          proof (cases "B = {}")
            case True
            then have "A = {}" using A_B_x_prop by simp
            have "maximal (\<lambda>B. B \<in> F) B" using A_B_x_prop by simp
            then have B_prop: "B \<in> F \<and> (\<nexists>X. X \<in> F \<and> B \<subset> X)" unfolding maximal_def by auto
            have "{x} \<in> F" using \<open>A = {}\<close> A_B_x_prop by simp
            have "B \<subset> {x}" using True by auto
            then show ?thesis using B_prop \<open>{x} \<in> F\<close> by simp
          next
            case False
            then show ?thesis
            proof (cases "B = A")
              case True
              then have "maximal (\<lambda>B. B \<in> F) A" using A_B_x_prop by simp
              then have A_prop: "A \<in> F \<and> (\<nexists>X. X \<in> F \<and> A \<subset> X)" unfolding maximal_def by auto
              have "x \<notin> A" using A_B_x_prop by auto
              then have "A \<subset> A \<union> {x}" by auto
              then show ?thesis using A_prop A_B_x_prop by simp
            next
              case False
              then have "A \<subset> B" using A_B_x_prop by auto
              have B_prop: "B \<in> F \<and> (\<nexists>X. X \<in> F \<and> B \<subset> X)" using A_B_x_prop unfolding maximal_def by auto
              then have "B \<subseteq> E" using ss_assum unfolding set_system_def by simp
              have "finite E" using ss_assum unfolding set_system_def by simp
              then have "finite B" using \<open>B \<subseteq> E\<close> finite_subset by auto
              then have "card A < card B" using \<open>A \<subset> B\<close> psubset_card_mono by auto
              then have "\<exists>y \<in> B - A. A \<union> {y} \<in> F"using B_prop A_B_x_prop third_condition by auto
              then obtain y where y_prop: "A \<union> {y} \<in> F" "y \<in> B - A" by auto
              then have "(B - {y})\<union> {x} \<notin> F" using A_B_x_prop by simp
              let ?Y = "{y | y. y \<in> B - A \<and> A \<union> {y} \<in> F }"
              have "finite ?Y" using \<open>finite B\<close> by simp
              have "?Y \<noteq> {}" using y_prop by auto
              define c::"'a set \<Rightarrow> real" where "c S = (if (S \<subseteq> B - ?Y \<and> S \<noteq> {}) then (card S * 2) else if (S \<subseteq> ?Y \<union> {x} \<and> S \<noteq> {}) then (card S) else 0)"
              have "valid_modular_weight_func c"
                unfolding valid_modular_weight_func_def
              proof
                show "c {} = 0" 
                  by (simp add: \<open>c \<equiv> \<lambda>S. real (if S \<subseteq> B - {y |y. y \<in> B - A \<and> A \<union> {y} \<in> F} \<and> S \<noteq> {} then card S * 2 else if S \<subseteq> {y |y. y \<in> B - A \<and> A \<union> {y} \<in> F} \<union> {x} \<and> S \<noteq> {} then card S else 0)\<close>)
                show "\<forall>X l. X \<subseteq> E \<and> X \<noteq> {} \<and> l = {c {e} |e. e \<in> X} \<longrightarrow> c X = \<Sum> l \<and> 0 < c X"
                proof (rule, rule)
                  fix X l
                  show "X \<subseteq> E \<and> X \<noteq> {} \<and> l = {c {e} |e. e \<in> X} \<longrightarrow> c X = \<Sum> l \<and> 0 < c X"
                  proof
                    assume X_assum: "X \<subseteq> E \<and> X \<noteq> {} \<and> l = {c {e} |e. e \<in> X}"
                    then show "c X = \<Sum> l \<and> 0 < c X" using \<open>c \<equiv> \<lambda>S. real (if S \<subseteq> B - {y |y. y \<in> B - A \<and> A \<union> {y} \<in> F} \<and> S \<noteq> {} then card S * 2 else if S \<subseteq> {y |y. y \<in> B - A \<and> A \<union> {y} \<in> F} \<union> {x} \<and> S \<noteq> {} then card S else 0)\<close>
                    proof (cases "X \<subseteq> B - ?Y")
                      case True
                      then have "finite X" using \<open>finite B\<close> finite_subset by auto
                      have "c X = card X * 2" using \<open>c \<equiv> \<lambda>S. real (if S \<subseteq> B - {y |y. y \<in> B - A \<and> A \<union> {y} \<in> F} \<and> S \<noteq> {} then card S * 2 else if S \<subseteq> {y |y. y \<in> B - A \<and> A \<union> {y} \<in> F} \<union> {x} \<and> S \<noteq> {} then card S else 0)\<close> True by simp
                      have "finite l" using X_assum \<open>finite X\<close> by simp
                      have "\<forall>e. e\<in> X \<longrightarrow> c {e} = 2"
                      proof 
                        fix e
                        show "e \<in> X \<longrightarrow> c {e} = 2"
                        proof
                          assume "e \<in> X"
                          then have "{e} \<subseteq> B - ?Y" using True by auto
                          then have "c {e} = (card {e}) * 2 " using \<open>c \<equiv> \<lambda>S. real (if S \<subseteq> B - {y |y. y \<in> B - A \<and> A \<union> {y} \<in> F} \<and> S \<noteq> {} then card S * 2 else if S \<subseteq> {y |y. y \<in> B - A \<and> A \<union> {y} \<in> F} \<union> {x} \<and> S \<noteq> {} then card S else 0)\<close> by simp
                          then show "c {e} = 2" by simp
                        qed
                      qed
                      then have 2: "\<forall>x. x \<in> l \<longrightarrow> x = 2" using X_assum by auto
                      have "card l = card X"
                      proof -
                         have 1: "\<forall>e. e \<in> X \<longrightarrow> c {e} \<in> l" using X_assum by auto
                         then have "\<forall>x. x \<in> l \<longrightarrow> (\<exists>e. e \<in> X \<and> c {e} = x)" using X_assum by auto
                         then show "card l = card X" using 1 sorry
                       qed
                      then have "\<Sum> l = card X * 2" using X_assum \<open>finite X\<close> by blast

                      then show ?thesis sorry
                    next
                      case False
                      then show ?thesis sorry
                    qed


              then show ?thesis sorry
            qed
          qed
        qed
      qed
    qed


end

end
