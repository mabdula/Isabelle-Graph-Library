theory Indep_System_Matroids_Specs
  imports Matroids_Theory "HOL-Data_Structures.Set_Specs" "HOL-Data_Structures.Map_Specs"
begin


locale Custom_Set = Set2 
  where empty = empty for empty :: "'s" +
  fixes subseteq :: "'s \<Rightarrow> 's \<Rightarrow> bool"
  fixes cardinality :: "'s \<Rightarrow> nat"
  assumes set_subseteq: "invar X \<Longrightarrow> invar Y \<Longrightarrow> (subseteq X Y) = (set X \<subseteq> set Y)"
  assumes set_cardinality: "invar X \<Longrightarrow> cardinality X = card (set X)"
begin

bundle automation =
  set_empty[simp] set_isin[simp] set_insert[simp] set_delete[simp]
  invar_empty[simp] invar_insert[simp] invar_delete[simp]
  set_union[simp] set_inter[simp] set_diff[simp]
  invar_union[simp] invar_inter[simp] invar_diff[simp]
  set_subseteq[simp] set_cardinality[simp]

end

locale Indep_System_Specs = 
  set: Custom_Set where 
    empty = set_empty and insert = set_insert and delete = set_delete and isin = set_isin and 
    set = to_set and invar = set_inv and union = union and inter = inter and diff = diff and
    subseteq = subseteq and cardinality = cardinality
+ set_of_sets: Set where 
    empty = set_of_sets_empty and insert = set_of_sets_insert and delete = set_of_sets_delete and 
    isin = set_of_sets_isin and set = to_set_of_sets and invar = set_of_sets_inv
  for set_empty :: "'s" and
      set_insert :: "('a::linorder) \<Rightarrow> 's \<Rightarrow> 's" and
      set_delete :: "'a \<Rightarrow> 's \<Rightarrow> 's" and
      set_isin :: "'s \<Rightarrow> 'a \<Rightarrow> bool" and
      to_set :: "'s \<Rightarrow> 'a set" and 
      set_inv :: "'s \<Rightarrow> bool" and
      union :: "'s \<Rightarrow> 's \<Rightarrow> 's" and
      inter :: "'s \<Rightarrow> 's \<Rightarrow> 's" and
      diff :: "'s \<Rightarrow> 's \<Rightarrow> 's" and
      subseteq :: "'s \<Rightarrow> 's \<Rightarrow> bool" and
      cardinality :: "'s \<Rightarrow> nat" and
      set_of_sets_empty :: "'t" and
      set_of_sets_insert :: "'s \<Rightarrow> 't \<Rightarrow> 't" and
      set_of_sets_delete :: "'s \<Rightarrow> 't \<Rightarrow> 't" and
      set_of_sets_isin :: "'t \<Rightarrow> 's \<Rightarrow> bool" and
      to_set_of_sets :: "'t \<Rightarrow> 's set" and 
      set_of_sets_inv :: "'t \<Rightarrow> bool"
begin

fun insert_elements :: "'a list \<Rightarrow> 's" where
  "insert_elements [] = set_empty" |
  "insert_elements (x # xs) = set_insert x (insert_elements xs)"

definition from_set :: "'a set \<Rightarrow> 's" where
  "from_set S = insert_elements (sorted_list_of_set S)"


lemma invar_insert_elements:
  "set_inv (insert_elements l)"
  apply (induction l)
  apply (simp add: set.invar_empty)
  apply (simp add: set.invar_insert)
  done

lemma invar_from_set:
  "set_inv (from_set S)"
  unfolding from_set_def using invar_insert_elements by blast


lemma set_correct_insert_elements:
  "to_set (insert_elements l) = set l"
  apply (induction l)
  apply (simp add: set.set_empty)
  using set.invar_insert set.set_insert invar_insert_elements by force

lemma from_set_correct:
  assumes "finite S"
  shows "to_set (from_set S) = S"
  unfolding from_set_def using set_correct_insert_elements set_sorted_list_of_set[OF assms]
  by blast

definition "finite_sets \<equiv> (\<forall>X. finite (to_set X))"


definition indep :: "'t \<Rightarrow> 's \<Rightarrow> bool" where
  "indep indep_set X = (set_of_sets_isin indep_set X)"


definition carrier_abs where
  "carrier_abs carrier = to_set carrier"

definition to_function :: "'t \<Rightarrow> ('a set \<Rightarrow> bool)" where
  "to_function set_of_sets = (\<lambda>S. if finite S then set_of_sets_isin set_of_sets (from_set S) else False)"

definition indep_abs where 
  "indep_abs indep_set = (to_function indep_set)"


lemma indep_abs_finite:
  "indep_abs indep_set S \<Longrightarrow> finite S"
  unfolding indep_abs_def to_function_def by presburger

lemma indep_abs_infinite:
  "(\<not>(finite S)) \<Longrightarrow> (\<not>(indep_abs indep_set S))"
  unfolding indep_abs_def to_function_def by simp



definition invar where
  "invar carrier indep_set =
    (set_inv carrier \<and> set_of_sets_inv indep_set \<and>
    (\<forall>X Y. set_inv X \<longrightarrow> set_inv Y \<longrightarrow> to_set X = to_set Y \<longrightarrow> 
      indep indep_set X = indep indep_set Y))"


lemma invarE[elim]: 
  "invar carrier indep_set \<Longrightarrow> 
    (\<lbrakk>set_inv carrier; set_of_sets_inv indep_set;
    (\<And>X Y. set_inv X \<Longrightarrow> set_inv Y \<Longrightarrow> to_set X = to_set Y \<Longrightarrow> 
      indep indep_set X = indep indep_set Y)\<rbrakk> 
    \<Longrightarrow> P) \<Longrightarrow> P"
  using invar_def by blast


lemma invarI[intro]: 
  "\<lbrakk>set_inv carrier; set_of_sets_inv indep_set;
    (\<And>X Y. set_inv X \<Longrightarrow> set_inv Y \<Longrightarrow> to_set X = to_set Y \<Longrightarrow> 
      indep indep_set X = indep indep_set Y)\<rbrakk> 
   \<Longrightarrow> invar carrier indep_set"
  using invar_def by blast


lemma finite_setsE[elim]: 
  "finite_sets \<Longrightarrow> ((\<And>X. finite (to_set X)) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: finite_sets_def)

lemma finite_setsI[intro]: 
  "(\<And>X. finite (to_set X)) \<Longrightarrow> finite_sets"
  by (auto simp: finite_sets_def)

lemma invar_indep_impl_correct:
  "invar carrier indep_set \<Longrightarrow> set_inv X \<Longrightarrow> set_inv Y \<Longrightarrow> to_set X = to_set Y \<Longrightarrow> 
    indep indep_set X = indep indep_set Y"
  by blast

lemma finite_indep_abs_expr:
  "finite S \<Longrightarrow> indep_abs indep_set S = indep indep_set (from_set S)"
  by (simp add: indep_abs_def indep_def to_function_def)



definition indep_system_axioms where
  "indep_system_axioms carrier indep_set \<equiv>
    (\<forall>X. set_inv X \<longrightarrow> indep indep_set X \<longrightarrow> subseteq X carrier) \<and>
    (\<exists>X. set_inv X \<and> indep indep_set X) \<and>
    (\<forall>X Y. set_inv X \<longrightarrow> set_inv Y \<longrightarrow> indep indep_set X \<longrightarrow> subseteq Y X \<longrightarrow> indep indep_set Y)"

context
  includes set.automation
  fixes carrier :: 's and indep_set :: 't
  assumes invar: "invar carrier indep_set" and
          finite_sets: "finite_sets"
begin

lemma indep_impl_to_abs:
  "set_inv X \<Longrightarrow> indep indep_set X \<Longrightarrow> indep_abs indep_set (to_set X)"
  by (meson finite_indep_abs_expr finite_sets finite_sets_def from_set_correct invar invarE invar_from_set)

lemma indep_abs_to_impl:
  "set_inv X \<Longrightarrow> indep_abs indep_set (to_set X) \<Longrightarrow> indep indep_set X"
  by (meson finite_indep_abs_expr from_set_correct indep_abs_finite invar invarE invar_from_set)

lemma indep_abs_equiv:
  "set_inv X \<Longrightarrow> indep indep_set X = indep_abs indep_set (to_set X)"
  using indep_abs_to_impl indep_impl_to_abs by blast


lemma indep_ex_impl_to_abs:
  "(\<exists>X. set_inv X \<and> indep indep_set X) \<Longrightarrow> (\<exists>S. indep_abs indep_set S)"
  using indep_impl_to_abs by blast

lemma indep_ex_abs_to_impl:
  "(\<exists>S. indep_abs indep_set S) \<Longrightarrow> (\<exists>X. set_inv X \<and> indep indep_set X)"
  using indep_abs_finite invar_from_set finite_indep_abs_expr by blast

lemma indep_ex_abs_equiv:
  "(\<exists>X. set_inv X \<and> indep indep_set X) = (\<exists>S. indep_abs indep_set S)"
  using indep_ex_abs_to_impl indep_ex_impl_to_abs by blast


lemma indep_subset_carrier_impl_to_abs:
  "(\<forall>X. set_inv X \<longrightarrow> indep indep_set X \<longrightarrow> subseteq X carrier) \<Longrightarrow>
   (\<forall>S. indep_abs indep_set S \<longrightarrow> S \<subseteq> carrier_abs carrier)"
  by (metis carrier_abs_def finite_indep_abs_expr from_set_correct indep_abs_finite invar invarE invar_from_set set.set_subseteq)

lemma indep_subset_carrier_abs_to_impl:
  "(\<forall>S. indep_abs indep_set S \<longrightarrow> S \<subseteq> carrier_abs carrier) \<Longrightarrow>
   (\<forall>X. set_inv X \<longrightarrow> indep indep_set X \<longrightarrow> subseteq X carrier)"
  by (metis carrier_abs_def indep_impl_to_abs invar invarE set.set_subseteq)

lemma indep_subset_carrier_abs_equiv:
  "(\<forall>X. set_inv X \<longrightarrow> indep indep_set X \<longrightarrow> subseteq X carrier) = 
   (\<forall>S. indep_abs indep_set S \<longrightarrow> S \<subseteq> carrier_abs carrier)"
  using indep_subset_carrier_abs_to_impl indep_subset_carrier_impl_to_abs by blast


lemma indep_subset_impl_to_abs:
  "(\<forall>X Y. set_inv X \<longrightarrow> set_inv Y \<longrightarrow> indep indep_set X \<longrightarrow> subseteq Y X \<longrightarrow> indep indep_set Y) \<Longrightarrow>
   (\<forall>S T. indep_abs indep_set S \<longrightarrow> T \<subseteq> S \<longrightarrow> indep_abs indep_set T)"
  by (metis from_set_correct indep_abs_finite invar_from_set rev_finite_subset set.set_subseteq finite_indep_abs_expr)

lemma indep_subset_abs_to_impl:
  "(\<forall>S T. indep_abs indep_set S \<longrightarrow> T \<subseteq> S \<longrightarrow> indep_abs indep_set T) \<Longrightarrow>
   (\<forall>X Y. set_inv X \<longrightarrow> set_inv Y \<longrightarrow> indep indep_set X \<longrightarrow> subseteq Y X \<longrightarrow> indep indep_set Y)"
  using indep_abs_equiv set.set_subseteq by presburger

lemma indep_subset_abs_equiv:
  "(\<forall>X Y. set_inv X \<longrightarrow> set_inv Y \<longrightarrow> indep indep_set X \<longrightarrow> subseteq Y X \<longrightarrow> indep indep_set Y) = 
   (\<forall>S T. indep_abs indep_set S \<longrightarrow> T \<subseteq> S \<longrightarrow> indep_abs indep_set T)"
  by (meson indep_subset_abs_to_impl indep_subset_impl_to_abs)


lemma carrier_abs_finite:
  "finite (carrier_abs carrier)"
  using carrier_abs_def finite_sets finite_sets_def by auto

lemma indep_system_impl_to_abs:
  "indep_system_axioms carrier indep_set \<Longrightarrow> indep_system (carrier_abs carrier) (indep_abs indep_set)"
  unfolding indep_system_axioms_def indep_system_def
  using carrier_abs_finite indep_ex_abs_equiv indep_subset_abs_equiv indep_subset_carrier_abs_equiv by fast

lemma indep_system_abs_to_impl:
  "indep_system (carrier_abs carrier) (indep_abs indep_set) \<Longrightarrow> indep_system_axioms carrier indep_set"
  unfolding indep_system_axioms_def indep_system_def
  using indep_ex_abs_to_impl indep_subset_abs_equiv indep_subset_carrier_abs_equiv by fast

lemma indep_system_abs_equiv:
  "indep_system_axioms carrier indep_set = indep_system (carrier_abs carrier) (indep_abs indep_set)"
  using indep_system_abs_to_impl indep_system_impl_to_abs by blast

end

end

locale Matroid_Specs = Indep_System_Specs
  where set_empty = set_empty and to_set = to_set and set_of_sets_empty = set_of_sets_empty
  for set_empty :: 's and to_set :: "'s \<Rightarrow> ('a::linorder) set" and set_of_sets_empty :: 't
begin


definition matroid_axioms where
  "matroid_axioms carrier indep_set \<equiv> indep_system_axioms carrier indep_set \<and>
    (\<forall>X Y. set_inv X \<longrightarrow> set_inv Y \<longrightarrow> indep indep_set X \<longrightarrow> indep indep_set Y \<longrightarrow> 
      cardinality X = Suc (cardinality Y) \<longrightarrow> (\<exists>x. set_isin (diff X Y) x \<and> indep indep_set (set_insert x Y)))"

context
  includes set.automation
  fixes carrier :: 's and indep_set :: 't
  assumes invar: "invar carrier indep_set" and
          finite_sets: "finite_sets"
begin

lemma augment_impl_to_abs:
  "(\<forall>X Y. set_inv X \<longrightarrow> set_inv Y \<longrightarrow> indep indep_set X \<longrightarrow> indep indep_set Y \<longrightarrow> 
      cardinality X = Suc (cardinality Y) \<longrightarrow> (\<exists>x. set_isin (diff X Y) x \<and> indep indep_set (set_insert x Y)))
    \<Longrightarrow>
    (\<forall>S T. indep_abs indep_set S \<longrightarrow> indep_abs indep_set T \<longrightarrow> card S = Suc (card T) \<longrightarrow>
      (\<exists>e. e \<in> (S - T) \<and> indep_abs indep_set (Set.insert e T)))"
proof (rule, rule, rule, rule, rule)
  fix S T
  assume
    "\<forall>X Y. set_inv X \<longrightarrow> set_inv Y \<longrightarrow> indep indep_set X \<longrightarrow> indep indep_set Y \<longrightarrow> 
      cardinality X = Suc (cardinality Y) \<longrightarrow> (\<exists>x. set_isin (diff X Y) x \<and> indep indep_set (set_insert x Y))" 
    "indep_abs indep_set S" "indep_abs indep_set T" "card S = Suc (card T)"
  from \<open>indep_abs indep_set S\<close> have "indep indep_set (from_set S)" using indep_abs_def
    using indep_abs_finite finite_indep_abs_expr by blast
  from \<open>indep_abs indep_set T\<close> have "indep indep_set (from_set T)" using indep_abs_def 
    using indep_abs_finite finite_indep_abs_expr by blast

  from invar_from_set have "set_inv (from_set S)" by simp
  from invar_from_set have "set_inv (from_set T)" by simp
  from \<open>card S = Suc (card T)\<close> set.set_cardinality[OF \<open>set_inv (from_set S)\<close>]
    set.set_cardinality[OF \<open>set_inv (from_set T)\<close>]
    have "cardinality (from_set S) = Suc (cardinality (from_set T))"
    using from_set_correct
    by (metis \<open>indep_abs indep_set S\<close> \<open>indep_abs indep_set T\<close> indep_abs_infinite)

  from \<open>set_inv (from_set S)\<close> \<open>set_inv (from_set T)\<close> \<open>indep indep_set (from_set S)\<close> \<open>indep indep_set (from_set T)\<close>
    \<open>cardinality (from_set S) = Suc (cardinality (from_set T))\<close>
    have "\<exists>x. set_isin (diff (from_set S) (from_set T)) x \<and> indep indep_set (set_insert x (from_set T))"
    using \<open>\<forall>X Y. set_inv X \<longrightarrow> set_inv Y \<longrightarrow> indep indep_set X \<longrightarrow> indep indep_set Y \<longrightarrow> 
      cardinality X = Suc (cardinality Y) \<longrightarrow> (\<exists>x. set_isin (diff X Y) x \<and> indep indep_set (set_insert x Y))\<close> 
    by blast
  then obtain x where "set_isin (diff (from_set S) (from_set T)) x" "indep indep_set (set_insert x (from_set T))" by blast
  
  from Set2.invar_diff[OF set.Set2_axioms \<open>set_inv (from_set S)\<close> \<open>set_inv (from_set T)\<close>]
    have "set_inv (diff (from_set S) (from_set T))" .

  from Set.set_isin[OF set.Set_axioms this] \<open>set_isin (diff (from_set S) (from_set T)) x\<close> have 
    "x \<in> to_set (diff (from_set S) (from_set T))"
    by blast

  from Set2.set_diff[OF set.Set2_axioms \<open>set_inv (from_set S)\<close> \<open>set_inv (from_set T)\<close>]
    have "to_set (diff (from_set S) (from_set T)) = to_set (from_set S) - to_set (from_set T)"
    by blast
  then have 
    "to_set (diff (from_set S) (from_set T)) = S - T"
    using from_set_correct
    using \<open>indep_abs indep_set S\<close> \<open>indep_abs indep_set T\<close> indep_abs_finite by presburger
  with \<open>x \<in> to_set (diff (from_set S) (from_set T))\<close>
    have "x \<in> S - T" by auto


  from Set.invar_insert[OF set.Set_axioms \<open>set_inv (from_set T)\<close>]
    have "set_inv (set_insert x (from_set T))" by blast

  from Set.set_insert[OF set.Set_axioms \<open>set_inv (from_set T)\<close>]
    have "to_set (set_insert x (from_set T)) = to_set (from_set T) \<union> {x}"
    by blast
  then have "to_set (set_insert x (from_set T)) = T \<union> {x}"
    using from_set_correct \<open>indep_abs indep_set T\<close> indep_abs_finite by presburger
  then have "to_set (set_insert x (from_set T)) = Set.insert x T"
    by simp
  then have "to_set (set_insert x (from_set T)) = to_set (from_set (Set.insert x T))"
    using from_set_correct
    using \<open>indep_abs indep_set T\<close> indep_abs_finite by auto
  
  from invar_from_set have "set_inv (from_set (Set.insert x T))" by auto

  from \<open>set_inv (set_insert x (from_set T))\<close> this
    \<open>to_set (set_insert x (from_set T)) = to_set (from_set (Set.insert x T))\<close>
    have "indep indep_set (set_insert x (from_set T)) = indep indep_set (from_set (Set.insert x T))"
    using \<open>invar carrier indep_set\<close> by blast
  with \<open>indep indep_set (set_insert x (from_set T))\<close>
    have "indep indep_set (from_set (Set.insert x T))" by blast
  then have "indep_abs indep_set (Set.insert x T)"
    by (metis \<open>finite_sets\<close> \<open>to_set (set_insert x (from_set T)) = insert x T\<close> finite_setsE finite_indep_abs_expr)

  from \<open>x \<in> S - T\<close> \<open>indep_abs indep_set (Set.insert x T)\<close>
    show "\<exists>e. e \<in> S - T \<and> indep_abs indep_set (Set.insert e T)" by auto
qed

lemma augment_abs_to_impl:
  "(\<forall>S T. indep_abs indep_set S \<longrightarrow> indep_abs indep_set T \<longrightarrow> card S = Suc (card T) \<longrightarrow>
      (\<exists>e. e \<in> (S - T) \<and> indep_abs indep_set (Set.insert e T)))
    \<Longrightarrow>
    (\<forall>X Y. set_inv X \<longrightarrow> set_inv Y \<longrightarrow> indep indep_set X \<longrightarrow> indep indep_set Y \<longrightarrow> 
      cardinality X = Suc (cardinality Y) \<longrightarrow> (\<exists>x. set_isin (diff X Y) x \<and> indep indep_set (set_insert x Y)))"
proof (rule, rule, rule, rule, rule, rule, rule)
  fix X Y
  assume "set_inv X" "set_inv Y" "indep indep_set X" "indep indep_set Y"
    "(\<forall>S T. indep_abs indep_set S \<longrightarrow> indep_abs indep_set T \<longrightarrow> card S = Suc (card T) \<longrightarrow>
      (\<exists>e. e \<in> (S - T) \<and> indep_abs indep_set (Set.insert e T)))"
    "cardinality X = Suc (cardinality Y)"
  from \<open>indep indep_set X\<close>
    have "indep_abs indep_set (to_set X)" 
    using indep_abs_equiv[OF \<open>invar carrier indep_set\<close> \<open>finite_sets\<close> \<open>set_inv X\<close>] by blast
  from \<open>indep indep_set Y\<close>
    have "indep_abs indep_set (to_set Y)"
    using indep_abs_equiv[OF \<open>invar carrier indep_set\<close> \<open>finite_sets\<close> \<open>set_inv Y\<close>] by blast

  from set.set_cardinality[OF \<open>set_inv X\<close>] set.set_cardinality[OF \<open>set_inv Y\<close>]
    \<open>cardinality X = Suc (cardinality Y)\<close>
  have "card (to_set X) = Suc (card (to_set Y))" by auto

  with \<open>(\<forall>S T. indep_abs indep_set S \<longrightarrow> indep_abs indep_set T \<longrightarrow> card S = Suc (card T) \<longrightarrow>
      (\<exists>e. e \<in> (S - T) \<and> indep_abs indep_set (Set.insert e T)))\<close>
    \<open>indep_abs indep_set (to_set X)\<close> \<open>indep_abs indep_set (to_set Y)\<close>
    have "\<exists>e. e \<in> (to_set X) - (to_set Y) \<and> indep_abs indep_set (Set.insert e (to_set Y))" by blast
  then obtain e where "e \<in> (to_set X) - (to_set Y)" "indep_abs indep_set (Set.insert e (to_set Y))" by blast

  from Set2.invar_diff[OF set.Set2_axioms \<open>set_inv X\<close> \<open>set_inv Y\<close>]
    have "set_inv (diff X Y)" .

  from Set2.set_diff[OF set.Set2_axioms \<open>set_inv X\<close> \<open>set_inv Y\<close>]
    have "to_set (diff X Y) = to_set X - to_set Y" by auto

  with \<open>e \<in> (to_set X) - (to_set Y)\<close>
    have "e \<in> to_set (diff X Y)" by blast

  with Set.set_isin[OF set.Set_axioms \<open>set_inv (diff X Y)\<close>] 
    have "set_isin (diff X Y) e" by blast


  from Set.invar_insert[OF set.Set_axioms \<open>set_inv Y\<close>]
    have "set_inv (set_insert e Y)" by simp

  from Set.set_insert[OF set.Set_axioms \<open>set_inv Y\<close>]
    have "Set.insert e (to_set Y) = to_set (set_insert e Y)" by auto

  with \<open>indep_abs indep_set (Set.insert e (to_set Y))\<close>
    have "indep_abs indep_set (to_set (set_insert e Y))" by auto

  then have "indep indep_set (from_set (to_set (set_insert e Y)))"
    using indep_abs_finite finite_indep_abs_expr by blast

  have "to_set (from_set (to_set (set_insert e Y))) = to_set (set_insert e Y)"
    using from_set_correct \<open>finite_sets\<close> finite_sets_def by presburger

  from invar_from_set
    have "set_inv (from_set (to_set (set_insert e Y)))" by auto

  from \<open>set_inv (from_set (to_set (set_insert e Y)))\<close> \<open>set_inv (set_insert e Y)\<close>
    \<open>to_set (from_set (to_set (set_insert e Y))) = to_set (set_insert e Y)\<close>  
    have "indep indep_set (from_set (to_set (set_insert e Y))) = indep indep_set (set_insert e Y)"
    unfolding invar_def using \<open>invar carrier indep_set\<close> by blast

  with \<open>indep indep_set (from_set (to_set (set_insert e Y)))\<close>
    have "indep indep_set (set_insert e Y)" by simp

  from \<open>set_isin (diff X Y) e\<close> \<open>indep indep_set (set_insert e Y)\<close>
    show "(\<exists>x. set_isin (diff X Y) x \<and> indep indep_set (set_insert x Y))" by auto
qed


lemma augment_abs_equiv:
  "(\<forall>X Y. set_inv X \<longrightarrow> set_inv Y \<longrightarrow> indep indep_set X \<longrightarrow> indep indep_set Y \<longrightarrow> 
      cardinality X = Suc (cardinality Y) \<longrightarrow> (\<exists>x. set_isin (diff X Y) x \<and> indep indep_set (set_insert x Y))) =
    (\<forall>S T. indep_abs indep_set S \<longrightarrow> indep_abs indep_set T \<longrightarrow> card S = Suc (card T) \<longrightarrow>
      (\<exists>e. e \<in> (S - T) \<and> indep_abs indep_set (Set.insert e T)))"
  using augment_impl_to_abs augment_abs_to_impl by blast


lemma matroid_impl_to_abs:
  "matroid_axioms carrier indep_set \<Longrightarrow> matroid (carrier_abs carrier) (indep_abs indep_set)"
  unfolding matroid_axioms_def matroid_def Matroid.matroid_axioms_def
  using augment_abs_equiv finite_sets indep_system_abs_equiv invar by blast

lemma matroid_abs_to_impl:
  "matroid (carrier_abs carrier) (indep_abs indep_set) \<Longrightarrow> matroid_axioms carrier indep_set"
  unfolding matroid_axioms_def matroid_def Matroid.matroid_axioms_def
  using augment_abs_equiv finite_sets indep_system_abs_equiv invar by blast

lemma matroid_abs_equiv:
  "matroid_axioms carrier indep_set = matroid (carrier_abs carrier) (indep_abs indep_set)"
  using matroid_abs_to_impl matroid_impl_to_abs by blast

end

end




end