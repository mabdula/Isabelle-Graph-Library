theory Best_In_Greedy
  imports Main Indep_System_Matroids_Specs
begin

record ('a, 's) best_in_greedy_state = carrier_list :: "'a list" result :: 's

named_theorems call_cond_elims
named_theorems call_cond_intros
named_theorems ret_holds_intros
named_theorems invar_props_intros
named_theorems invar_props_elims
named_theorems invar_holds_intros

locale Best_In_Greedy = matroid: Matroid_Specs 
  where set_empty = set_empty and set_of_sets_empty = set_of_sets_empty for set_empty :: "'s" and 
    set_of_sets_empty :: "'t" +
  fixes carrier :: "'s" and indep_set :: "'t" and
    (* c :: "'a \<Rightarrow> rat" and *) sort_desc :: "('a \<Rightarrow> rat) \<Rightarrow> 'a list \<Rightarrow> 'a list" 

begin



definition "sort_desc_axioms \<equiv>
  (\<forall>c order. sorted_wrt (\<lambda>x1 x2. c x1 \<ge> c x2) (sort_desc c order) \<and>
  set order = set (sort_desc c order) \<and> length order = length (sort_desc c order) \<and>
  (\<forall>k. filter (\<lambda>y. c y = k) (sort_desc c order) = filter (\<lambda>y. c y = k) order))"

definition "BestInGreedy_axioms \<equiv>
  matroid.invar carrier indep_set \<and> matroid.finite_sets"

abbreviation "indep' \<equiv> matroid.indep indep_set"


function (domintros) BestInGreedy :: 
  "('a, 's) best_in_greedy_state \<Rightarrow> ('a, 's) best_in_greedy_state" where
  "BestInGreedy best_in_greedy_state = 
    (case (carrier_list best_in_greedy_state) of
      [] \<Rightarrow> best_in_greedy_state
    | (x # xs) \<Rightarrow> 
        (if indep' (set_insert x (result best_in_greedy_state)) then
          let
            new_result = (set_insert x (result best_in_greedy_state))
          in
            BestInGreedy (best_in_greedy_state \<lparr>carrier_list := xs, result := new_result\<rparr>)
        else
          BestInGreedy (best_in_greedy_state \<lparr>carrier_list := xs\<rparr>)
        )
    )"
  by pat_completeness auto


definition "BestInGreedy_call_1_conds best_in_greedy_state \<equiv>
    (case (carrier_list best_in_greedy_state) of
      [] \<Rightarrow> False
    | (x # xs) \<Rightarrow> 
        (if indep' (set_insert x (result best_in_greedy_state)) then
          True
        else
          False
        )
    )"


lemma BestInGreedy_call_1_conds[call_cond_elims]: 
  "BestInGreedy_call_1_conds best_in_greedy_state \<Longrightarrow> 
   \<lbrakk>\<lbrakk>\<exists>x xs. carrier_list best_in_greedy_state = x # xs;
    indep' (set_insert (hd (carrier_list best_in_greedy_state)) (result best_in_greedy_state))\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> 
   P"
  by(auto simp: BestInGreedy_call_1_conds_def split: list.splits if_splits)


definition "BestInGreedy_upd1 best_in_greedy_state \<equiv> (
  let
    x = hd (carrier_list best_in_greedy_state);
    xs = tl (carrier_list best_in_greedy_state);
    new_result = (set_insert x (result best_in_greedy_state))
  in
    best_in_greedy_state \<lparr>carrier_list := xs, result := new_result\<rparr>
  )"


definition "BestInGreedy_call_2_conds best_in_greedy_state \<equiv>
    (case (carrier_list best_in_greedy_state) of
      [] \<Rightarrow> False
    | (x # xs) \<Rightarrow> 
        (if indep' (set_insert x (result best_in_greedy_state)) then
          False
        else
          True
        )
    )"


lemma BestInGreedy_call_2_conds[call_cond_elims]: 
  "BestInGreedy_call_2_conds best_in_greedy_state \<Longrightarrow> 
   \<lbrakk>\<lbrakk>\<exists>x xs. carrier_list best_in_greedy_state = x # xs;
    \<not>(indep' (set_insert (hd (carrier_list best_in_greedy_state)) (result best_in_greedy_state)))\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> 
   P"
  by(auto simp: BestInGreedy_call_2_conds_def split: list.splits if_splits)


definition "BestInGreedy_upd2 best_in_greedy_state \<equiv> (
  let
    xs = tl (carrier_list best_in_greedy_state)
  in
    best_in_greedy_state \<lparr>carrier_list := xs\<rparr>
  )"



definition "BestInGreedy_ret_1_conds best_in_greedy_state \<equiv>
    (case (carrier_list best_in_greedy_state) of
      [] \<Rightarrow> True
    | (x # xs) \<Rightarrow> 
        (if indep' (set_insert x (result best_in_greedy_state)) then
          False
        else
          False
        )
    )"


lemma BestInGreedy_ret_1_conds[call_cond_elims]:
  "BestInGreedy_ret_1_conds best_in_greedy_state \<Longrightarrow> 
   \<lbrakk>\<lbrakk>carrier_list best_in_greedy_state = []\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> 
   P"
  by(auto simp: BestInGreedy_ret_1_conds_def split: list.splits if_splits)


lemma BestInGreedy_ret_1_condsI[call_cond_intros]:
  "\<lbrakk>carrier_list best_in_greedy_state = []\<rbrakk> \<Longrightarrow> BestInGreedy_ret_1_conds best_in_greedy_state"
  by(auto simp: BestInGreedy_ret_1_conds_def split: list.splits if_splits)

definition "BestInGreedy_ret1 best_in_greedy_state \<equiv> best_in_greedy_state"


lemma BestInGreedy_cases:
  assumes "BestInGreedy_call_1_conds best_in_greedy_state \<Longrightarrow> P"
      "BestInGreedy_call_2_conds best_in_greedy_state \<Longrightarrow> P"
      "BestInGreedy_ret_1_conds best_in_greedy_state \<Longrightarrow> P"
  shows "P"
proof-
  have "BestInGreedy_call_1_conds best_in_greedy_state \<or> BestInGreedy_call_2_conds best_in_greedy_state \<or>
        BestInGreedy_ret_1_conds best_in_greedy_state"
    by (auto simp add: BestInGreedy_call_1_conds_def BestInGreedy_call_2_conds_def
        BestInGreedy_ret_1_conds_def split: list.split_asm if_splits)
  then show ?thesis
    using assms
    by auto
qed


lemma BestInGreedy_simps:
  assumes "BestInGreedy_dom best_in_greedy_state" 
  shows"BestInGreedy_call_1_conds best_in_greedy_state \<Longrightarrow> 
          BestInGreedy best_in_greedy_state = BestInGreedy (BestInGreedy_upd1 best_in_greedy_state)"
      "BestInGreedy_call_2_conds best_in_greedy_state \<Longrightarrow> 
          BestInGreedy best_in_greedy_state = BestInGreedy (BestInGreedy_upd2 best_in_greedy_state)"
      "BestInGreedy_ret_1_conds best_in_greedy_state \<Longrightarrow> 
          BestInGreedy best_in_greedy_state = BestInGreedy_ret1 best_in_greedy_state"
  by (auto simp add: BestInGreedy.psimps[OF assms] Let_def
      BestInGreedy_call_1_conds_def BestInGreedy_upd1_def BestInGreedy_call_2_conds_def BestInGreedy_upd2_def
      BestInGreedy_ret_1_conds_def BestInGreedy_ret1_def split: list.splits if_splits)


lemma BestInGreedy_induct:
  assumes "BestInGreedy_dom best_in_greedy_state"
  assumes "\<And>best_in_greedy_state. \<lbrakk>BestInGreedy_dom best_in_greedy_state;
    BestInGreedy_call_1_conds best_in_greedy_state \<Longrightarrow> P (BestInGreedy_upd1 best_in_greedy_state);
    BestInGreedy_call_2_conds best_in_greedy_state \<Longrightarrow> P (BestInGreedy_upd2 best_in_greedy_state)\<rbrakk> \<Longrightarrow> 
      P best_in_greedy_state"
  shows "P best_in_greedy_state"
  apply(rule BestInGreedy.pinduct[OF assms(1)])
  apply(rule assms(2)[simplified BestInGreedy_call_1_conds_def BestInGreedy_upd1_def BestInGreedy_call_2_conds_def BestInGreedy_upd2_def])
  by (auto simp: Let_def split: list.splits if_splits)


lemma BestInGreedy_domintros: 
  assumes "BestInGreedy_call_1_conds best_in_greedy_state \<Longrightarrow> BestInGreedy_dom (BestInGreedy_upd1 best_in_greedy_state)"
  assumes "BestInGreedy_call_2_conds best_in_greedy_state \<Longrightarrow> BestInGreedy_dom (BestInGreedy_upd2 best_in_greedy_state)"
  shows "BestInGreedy_dom best_in_greedy_state"  
proof(rule BestInGreedy.domintros, goal_cases)
  case (1 x21 x22)
  then show ?case
    using assms(1)[simplified BestInGreedy_call_1_conds_def BestInGreedy_upd1_def]
    by (force simp: Let_def split: list.splits if_splits)
next
  case (2 x21 x22)
  then show ?case
    using assms(2)[simplified BestInGreedy_call_2_conds_def BestInGreedy_upd2_def]
    by (force split: list.splits if_splits)
qed


definition "call_measure best_in_greedy_state \<equiv> length (carrier_list best_in_greedy_state)"

definition "BestInGreedy_term_rel' \<equiv> call_measure <*mlex*> {}"

definition "initial_state c order \<equiv> \<lparr>carrier_list = (sort_desc c order), result = set_empty\<rparr>"


definition "nonnegative (c::('a \<Rightarrow> rat)) \<equiv> (\<forall>x. set_isin carrier x \<longrightarrow> c x \<ge> 0)"

definition "valid_order order \<equiv> to_set carrier = set order \<and> cardinality carrier = length order"



definition
  "num_iter c order best_in_greedy_state \<equiv> (length (sort_desc c order) - length (carrier_list best_in_greedy_state))"

definition
  "carrier_pref c order j \<equiv> set (take j (sort_desc c order))"

definition
  "pref c order S j \<equiv> S \<inter> (carrier_pref c order j)"

definition "invar_1 best_in_greedy_state \<equiv> set_inv (result best_in_greedy_state)"

definition "invar_2 c order best_in_greedy_state \<equiv>
  (carrier_list best_in_greedy_state) = (drop (num_iter c order best_in_greedy_state) (sort_desc c order))"

definition "invar_3 c order best_in_greedy_state \<equiv>
  to_set (result best_in_greedy_state) \<subseteq> (carrier_pref c order (num_iter c order best_in_greedy_state))"

definition "invar_4 c order best_in_greedy_state \<equiv> 
  \<forall>j \<in> {0..(num_iter c order best_in_greedy_state)}.
  (indep_system.basis_in (matroid.indep_abs indep_set)
  (carrier_pref c order j)
  (pref c order (to_set (result best_in_greedy_state)) j))"

definition "c_set c S \<equiv> sum c S"

definition "c_diff c order n j \<equiv>
  (if j < n then c ((sort_desc c order) ! (j - 1)) - c ((sort_desc c order) ! j) 
  else c ((sort_desc c order) ! (j - 1)))"

definition "valid_solution X \<equiv>
  set_inv X \<and> subseteq X carrier \<and> indep' X"

context
  includes matroid.set.custom_automation
  assumes BestInGreedy_axioms sort_desc_axioms "matroid.indep_system_axioms carrier indep_set"
begin

lemma matroid_inv:
  "matroid.invar carrier indep_set"
  "matroid.finite_sets"
  using \<open>BestInGreedy_axioms\<close>
  by (auto simp: BestInGreedy_axioms_def) 

lemma indep_system_axioms_abs:
  "indep_system (matroid.carrier_abs carrier) (matroid.indep_abs indep_set)"
  using matroid.indep_system_impl_to_abs[OF matroid_inv(1) matroid_inv(2)]
    \<open>matroid.indep_system_axioms carrier indep_set\<close> by simp

lemma set_inv_carrier:
  "set_inv carrier"
  using \<open>BestInGreedy_axioms\<close> BestInGreedy_axioms_def by auto

lemmas simps[simp] = matroid.indep_abs_equiv[OF matroid_inv(1) matroid_inv(2)]

context
  fixes c :: "'a \<Rightarrow> rat" and order :: "'a list"
  assumes "nonnegative c" "valid_order order"
begin

abbreviation "carrier_sorted \<equiv> sort_desc c order"

lemma cost_nonnegative:
  "set_isin carrier x \<Longrightarrow> c x \<ge> 0"
  using \<open>nonnegative c\<close>
  by (auto simp: nonnegative_def) 

lemma valid_solution_c_set_nonnegative:
  "valid_solution X \<Longrightarrow> c_set c (to_set X) \<ge> 0"
proof-
  assume "valid_solution X"
  from \<open>valid_solution X\<close> valid_solution_def set_inv_carrier
    have "(to_set X) \<subseteq> (to_set carrier)"
    by force
  with set_inv_carrier \<open>nonnegative c\<close> nonnegative_def have
    "\<forall>x \<in> (to_set X). c x \<ge> 0"
    by auto
  then show "c_set c (to_set X) \<ge> 0"
    unfolding c_set_def by (simp add: sum_nonneg)
qed


lemma carrier_sorted_sorted_desc:
  "sorted_wrt (\<lambda>x1 x2. c x1 \<ge> c x2) (carrier_sorted)"
  using \<open>sort_desc_axioms\<close>
  by (auto simp: sort_desc_axioms_def) 

lemma sort_desc_stable:
  "filter (\<lambda>y. c y = k) carrier_sorted = filter (\<lambda>y. c y = k) order"
  using \<open>sort_desc_axioms\<close> sort_desc_axioms_def by auto

lemma carrier_sorted_set:
  "to_set carrier = set (carrier_sorted)"
  using \<open>sort_desc_axioms\<close> \<open>valid_order order\<close>
  by (auto simp: sort_desc_axioms_def valid_order_def)

lemma length_carrier_sorted:
  "cardinality carrier = length (carrier_sorted)"
  using \<open>sort_desc_axioms\<close> \<open>valid_order order\<close>
  by (auto simp: sort_desc_axioms_def valid_order_def)

lemma carrier_sorted_distinct:
  "distinct (carrier_sorted)"
  unfolding sort_desc_axioms_def using card_distinct set_inv_carrier matroid.set.set_cardinality 
  by (metis carrier_sorted_set length_carrier_sorted) 



lemma invar_1_props[invar_props_elims]:
  "invar_1 best_in_greedy_state \<Longrightarrow>
    (\<lbrakk>set_inv (result best_in_greedy_state)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
    P"
  by (auto simp: invar_1_def)

lemma invar_1_intro[invar_props_intros]:
  "\<lbrakk>set_inv (result best_in_greedy_state)\<rbrakk> \<Longrightarrow> invar_1 best_in_greedy_state"
  by (auto simp: invar_1_def)

lemma invar_1_holds_upd1[invar_holds_intros]:
  "\<lbrakk>BestInGreedy_call_1_conds best_in_greedy_state; invar_1 best_in_greedy_state\<rbrakk> \<Longrightarrow> 
    invar_1 (BestInGreedy_upd1 best_in_greedy_state)"
  by (auto simp: Let_def BestInGreedy_upd1_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_1_holds_upd2[invar_holds_intros]:
  "\<lbrakk>BestInGreedy_call_2_conds best_in_greedy_state; invar_1 best_in_greedy_state\<rbrakk> \<Longrightarrow>
    invar_1 (BestInGreedy_upd2 best_in_greedy_state)"
  by (auto simp: BestInGreedy_upd2_def elim!: invar_props_elims intro: invar_props_intros)

lemma invar_1_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BestInGreedy_ret_1_conds best_in_greedy_state; invar_1 best_in_greedy_state\<rbrakk> \<Longrightarrow>
    invar_1 (BestInGreedy_ret1 best_in_greedy_state)"
  by (auto simp: BestInGreedy_ret1_def)

lemma invar_1_holds[invar_holds_intros]: 
   assumes "BestInGreedy_dom best_in_greedy_state" "invar_1 best_in_greedy_state"
   shows "invar_1 (BestInGreedy best_in_greedy_state)"
  using assms(2)
proof(induction rule: BestInGreedy_induct[OF assms(1)])
  case IH: (1 best_in_greedy_state)
  show ?case
    apply(rule BestInGreedy_cases[where best_in_greedy_state = best_in_greedy_state])
    by (auto intro!: IH(2-4) invar_holds_intros simp: BestInGreedy_simps[OF IH(1)])
qed


lemma invar_2_props[invar_props_elims]:
  "invar_2 c order best_in_greedy_state \<Longrightarrow>
    (\<lbrakk>carrier_list best_in_greedy_state = drop (num_iter c order best_in_greedy_state) (carrier_sorted)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
    P"
  by (auto simp: invar_2_def)

lemma invar_2_intro[invar_props_intros]:
  "\<lbrakk>carrier_list best_in_greedy_state = drop (num_iter c order best_in_greedy_state) (carrier_sorted)\<rbrakk> \<Longrightarrow> invar_2 c order best_in_greedy_state"
  by (auto simp: invar_2_def)

lemma invar_2_holds_upd1[invar_holds_intros]:
  "\<lbrakk>BestInGreedy_call_1_conds best_in_greedy_state; invar_2 c order best_in_greedy_state\<rbrakk> \<Longrightarrow> 
    invar_2 c order(BestInGreedy_upd1 best_in_greedy_state)"
proof (intro invar_props_intros, goal_cases)
  case 1
  have "length (carrier_list (BestInGreedy_upd1 best_in_greedy_state)) =
    length (carrier_list best_in_greedy_state) - 1"
    using \<open>BestInGreedy_call_1_conds best_in_greedy_state\<close> 
    by (auto simp add: BestInGreedy_upd1_def Let_def elim!: call_cond_elims)
  moreover have "length (carrier_list best_in_greedy_state) \<ge> 1"
    using \<open>BestInGreedy_call_1_conds best_in_greedy_state\<close> 
    by (auto elim!: call_cond_elims)
  ultimately have "num_iter c order (BestInGreedy_upd1 best_in_greedy_state) =
    1 + (num_iter c order best_in_greedy_state)"
    unfolding num_iter_def 
    using \<open>invar_2 c order best_in_greedy_state\<close> by (fastforce elim!: invar_props_elims)
  then show ?case
    using \<open>invar_2 c order best_in_greedy_state\<close>
    by (auto simp add: drop_Suc tl_drop BestInGreedy_upd1_def Let_def elim!: invar_props_elims)
qed

lemma invar_2_holds_upd2[invar_holds_intros]:
  "\<lbrakk>BestInGreedy_call_2_conds best_in_greedy_state; invar_2 c order best_in_greedy_state\<rbrakk> \<Longrightarrow> 
    invar_2 c order (BestInGreedy_upd2 best_in_greedy_state)"
proof (intro invar_props_intros, goal_cases)
  case 1
  have "length (carrier_list (BestInGreedy_upd2 best_in_greedy_state)) =
    length (carrier_list best_in_greedy_state) - 1"
    using \<open>BestInGreedy_call_2_conds best_in_greedy_state\<close> 
    by (auto simp add: BestInGreedy_upd2_def Let_def elim!: call_cond_elims)
  moreover have "length (carrier_list best_in_greedy_state) \<ge> 1"
    using \<open>BestInGreedy_call_2_conds best_in_greedy_state\<close> 
    by (auto elim!: call_cond_elims)
  ultimately have "num_iter c order (BestInGreedy_upd2 best_in_greedy_state) =
    1 + (num_iter c order best_in_greedy_state)"
    unfolding num_iter_def 
    using \<open>invar_2 c order best_in_greedy_state\<close> by (fastforce elim!: invar_props_elims)
  then show ?case
    using \<open>invar_2 c order best_in_greedy_state\<close>
    by (auto simp add: drop_Suc tl_drop BestInGreedy_upd2_def Let_def elim!: invar_props_elims)
qed

lemma invar_2_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BestInGreedy_ret_1_conds best_in_greedy_state; invar_2 c order best_in_greedy_state\<rbrakk> \<Longrightarrow>
    invar_2 c order (BestInGreedy_ret1 best_in_greedy_state)"
  by (auto simp: BestInGreedy_ret1_def)

lemma invar_2_holds[invar_holds_intros]: 
   assumes "BestInGreedy_dom best_in_greedy_state" "invar_2 c order best_in_greedy_state"
   shows "invar_2 c order (BestInGreedy best_in_greedy_state)"
  using assms(2)
proof(induction rule: BestInGreedy_induct[OF assms(1)])
  case IH: (1 best_in_greedy_state)
  show ?case
    apply(rule BestInGreedy_cases[where best_in_greedy_state = best_in_greedy_state])
    by (auto intro!: IH(2-4) invar_holds_intros simp: BestInGreedy_simps[OF IH(1)])
qed


lemma invar_3_props[invar_props_elims]:
  "invar_3 c order best_in_greedy_state \<Longrightarrow>
    (\<lbrakk>to_set (result best_in_greedy_state) \<subseteq> (carrier_pref c order (num_iter c order best_in_greedy_state))\<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
    P"
  by (auto simp: invar_3_def)

lemma invar_3_intro[invar_props_intros]:
  "\<lbrakk>to_set (result best_in_greedy_state) \<subseteq> (carrier_pref c order (num_iter c order best_in_greedy_state))\<rbrakk> \<Longrightarrow> invar_3 c order best_in_greedy_state"
  by (auto simp: invar_3_def)

lemma invar_3_holds_upd1[invar_holds_intros]:
  "\<lbrakk>BestInGreedy_call_1_conds best_in_greedy_state; invar_1 best_in_greedy_state; invar_2 c order best_in_greedy_state; 
    invar_3 c order best_in_greedy_state\<rbrakk> \<Longrightarrow> invar_3 c order (BestInGreedy_upd1 best_in_greedy_state)"
proof (intro invar_props_intros, goal_cases)
  case 1

  have carrier_pref_expr: "carrier_pref c order (num_iter c order (BestInGreedy_upd1 best_in_greedy_state)) = 
    insert (hd (carrier_list best_in_greedy_state)) (carrier_pref c order (num_iter c order best_in_greedy_state))"
    apply (simp add: BestInGreedy_upd1_def carrier_pref_def Let_def num_iter_def)
    using \<open>BestInGreedy_call_1_conds best_in_greedy_state\<close> \<open>invar_2 c order best_in_greedy_state\<close>
    apply (clarsimp elim!: invar_props_elims call_cond_elims)
    by (metis drop_Suc length_drop num_iter_def set_take_aux_lemma tl_drop)

  show "to_set (result (BestInGreedy_upd1 best_in_greedy_state)) \<subseteq>
    carrier_pref c order (num_iter c order (BestInGreedy_upd1 best_in_greedy_state))"
    using carrier_pref_expr \<open>invar_1 best_in_greedy_state\<close> \<open>invar_3 c order best_in_greedy_state\<close>
    by (auto simp add: BestInGreedy_upd1_def elim!: invar_props_elims)
qed

lemma invar_3_holds_upd2[invar_holds_intros]:
  "\<lbrakk>BestInGreedy_call_2_conds best_in_greedy_state; invar_2 c order best_in_greedy_state;
    invar_3 c order best_in_greedy_state\<rbrakk> \<Longrightarrow> invar_3 c order (BestInGreedy_upd2 best_in_greedy_state)"
proof (intro invar_props_intros, goal_cases)
  case 1

  have carrier_pref_expr: "carrier_pref c order (num_iter c order (BestInGreedy_upd2 best_in_greedy_state)) = 
    insert (hd (carrier_list best_in_greedy_state)) (carrier_pref c order (num_iter c order best_in_greedy_state))"
    apply (simp add: BestInGreedy_upd2_def carrier_pref_def Let_def num_iter_def 1)
    using \<open>BestInGreedy_call_2_conds best_in_greedy_state\<close> \<open>invar_2 c order best_in_greedy_state\<close>
    apply (clarsimp elim!: invar_props_elims call_cond_elims)
    by (metis drop_Suc length_drop num_iter_def set_take_aux_lemma tl_drop)

  show "to_set (result (BestInGreedy_upd2 best_in_greedy_state)) \<subseteq> 
    carrier_pref c order (num_iter c order (BestInGreedy_upd2 best_in_greedy_state))"
    using carrier_pref_expr \<open>invar_3 c order best_in_greedy_state\<close>
    by (auto simp add: BestInGreedy_upd2_def elim!: invar_props_elims)
qed

lemma invar_3_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BestInGreedy_ret_1_conds best_in_greedy_state; invar_3 c order best_in_greedy_state\<rbrakk> \<Longrightarrow>
    invar_3 c order (BestInGreedy_ret1 best_in_greedy_state)"
  by (auto simp: BestInGreedy_ret1_def)

lemma invar_3_holds[invar_holds_intros]: 
   assumes "BestInGreedy_dom best_in_greedy_state" "invar_1 best_in_greedy_state" "invar_2 c order best_in_greedy_state"
     "invar_3 c order best_in_greedy_state"
   shows "invar_3 c order (BestInGreedy best_in_greedy_state)"
  using assms(2-)
proof(induction rule: BestInGreedy_induct[OF assms(1)])
  case IH: (1 best_in_greedy_state)
  show ?case
    apply(rule BestInGreedy_cases[where best_in_greedy_state = best_in_greedy_state])
    by (auto intro!: IH(2-) invar_holds_intros simp: BestInGreedy_simps[OF IH(1)])
qed



lemma invar_4_props[invar_props_elims]:
  "invar_4 c order best_in_greedy_state \<Longrightarrow>
    (\<lbrakk>\<And>j. j \<in> {0..(num_iter c order best_in_greedy_state)} \<Longrightarrow>
      (indep_system.basis_in (matroid.indep_abs indep_set) (carrier_pref c order j)
      (pref c order (to_set (result best_in_greedy_state)) j))\<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
    P"
  by (auto simp: invar_4_def)

lemma invar_4_intro[invar_props_intros]:
  "\<lbrakk>\<And>j. j \<in> {0..(num_iter c order best_in_greedy_state)} \<Longrightarrow>
    (indep_system.basis_in (matroid.indep_abs indep_set) (carrier_pref c order j)
    (pref c order (to_set (result best_in_greedy_state)) j))\<rbrakk> \<Longrightarrow> invar_4 c order best_in_greedy_state"
  by (auto simp: invar_4_def)

lemma invar_4_holds_upd1[invar_holds_intros]:
  "\<lbrakk>BestInGreedy_call_1_conds best_in_greedy_state; invar_1 best_in_greedy_state; invar_2 c order best_in_greedy_state;
    invar_3 c order best_in_greedy_state; invar_4 c order best_in_greedy_state\<rbrakk> \<Longrightarrow> invar_4 c order (BestInGreedy_upd1 best_in_greedy_state)"
proof(rule invar_props_intros, goal_cases)
  case (1 j)

  show ?case
    
  proof (cases "j \<le> (num_iter c order best_in_greedy_state)")
    case True

    have "set (carrier_list best_in_greedy_state) \<inter> (carrier_pref c order j) = {}"
      unfolding carrier_pref_def using set_take_disj_set_drop_if_distinct[OF carrier_sorted_distinct True]
      \<open>invar_2 c order best_in_greedy_state\<close>
      by (fastforce elim!: invar_props_elims)
    then have "hd (carrier_list best_in_greedy_state) \<notin> (carrier_pref c order j)"
      using \<open>BestInGreedy_call_1_conds best_in_greedy_state\<close>
      by (auto elim!: call_cond_elims)
    then have "(pref c order (insert (hd (carrier_list best_in_greedy_state)) (to_set (result best_in_greedy_state))) j)
      = (pref c order (to_set (result best_in_greedy_state)) j)"
      unfolding pref_def by auto

    then have "indep_system.basis_in (matroid.indep_abs indep_set) (carrier_pref c order j)
     (pref c order (insert (hd (carrier_list best_in_greedy_state)) (to_set (result best_in_greedy_state))) j)"
      using \<open>invar_4 c order best_in_greedy_state\<close> True by (auto elim!: invar_props_elims)

    then show "indep_system.basis_in (matroid.indep_abs indep_set) (carrier_pref c order j)
      (pref c order (to_set (result (BestInGreedy_upd1 best_in_greedy_state))) j)"
      using \<open>invar_1 best_in_greedy_state\<close>
      by (auto simp add: Let_def BestInGreedy_upd1_def elim!: invar_props_elims)
  next
    case False

    have "length (carrier_list (BestInGreedy_upd1 best_in_greedy_state)) =
      length (carrier_list best_in_greedy_state) - 1"
      using \<open>BestInGreedy_call_1_conds best_in_greedy_state\<close> 
      by (auto simp add: BestInGreedy_upd1_def Let_def elim!: call_cond_elims)
    moreover have "length (carrier_list best_in_greedy_state) \<ge> 1"
      using \<open>BestInGreedy_call_1_conds best_in_greedy_state\<close> 
      by (auto elim!: call_cond_elims)
    ultimately have "num_iter c order (BestInGreedy_upd1 best_in_greedy_state) =
      1 + (num_iter c order best_in_greedy_state)"
      unfolding num_iter_def 
      using \<open>invar_2 c order best_in_greedy_state\<close> by (fastforce elim!: invar_props_elims)
    with 1(6) False have j_expr: "j = num_iter c order (BestInGreedy_upd1 best_in_greedy_state)" by auto
    
    have carrier_pref_expr:
      "carrier_pref c order (num_iter c order (BestInGreedy_upd1 best_in_greedy_state)) = 
      insert (hd (carrier_list best_in_greedy_state)) (carrier_pref c order (num_iter c order best_in_greedy_state))"
      apply (simp add: BestInGreedy_upd1_def carrier_pref_def Let_def num_iter_def)
        using \<open>BestInGreedy_call_1_conds best_in_greedy_state\<close> \<open>invar_2 c order best_in_greedy_state\<close>
        apply (clarsimp elim!: invar_props_elims call_cond_elims)
      by (metis drop_Suc length_drop num_iter_def set_take_aux_lemma tl_drop)

    have
      "insert (hd (carrier_list best_in_greedy_state)) (carrier_pref c order (num_iter c order best_in_greedy_state))
      \<subseteq> set (carrier_sorted)"
      using carrier_pref_def set_take_subset by (metis carrier_pref_expr)
    then have insert_subset_carrier:
      "insert (hd (carrier_list best_in_greedy_state)) (carrier_pref c order (num_iter c order best_in_greedy_state))
      \<subseteq> matroid.carrier_abs carrier"
      using matroid.carrier_abs_def carrier_sorted_set by simp


    have "(pref c order (to_set (result best_in_greedy_state)) (num_iter c order best_in_greedy_state)) =
      to_set (result best_in_greedy_state)"
      using \<open>invar_3 c order best_in_greedy_state\<close> 
      by (auto simp: pref_def elim: invar_3_props)

    then have indep_abs: "matroid.indep_abs indep_set (insert (hd (carrier_list best_in_greedy_state))
      (pref c order (to_set (result best_in_greedy_state)) (num_iter c order best_in_greedy_state)))"
      using \<open>invar_1 best_in_greedy_state\<close> \<open>BestInGreedy_call_1_conds best_in_greedy_state\<close> 
      by (auto elim!: invar_props_elims call_cond_elims)

    from indep_system.basis_in_preserved_indep[OF indep_system_axioms_abs insert_subset_carrier] indep_abs
      have "indep_system.basis_in (matroid.indep_abs indep_set)
   (insert (hd (carrier_list best_in_greedy_state)) (carrier_pref c order (num_iter c order best_in_greedy_state)))
   (insert (hd (carrier_list best_in_greedy_state)) (pref c order (to_set (result best_in_greedy_state)) (num_iter c order best_in_greedy_state)))"
      using \<open>invar_4 c order best_in_greedy_state\<close>
      by (auto elim!: invar_props_elims)

    moreover have "(insert (hd (carrier_list best_in_greedy_state)) (pref c order (to_set (result best_in_greedy_state))
        (num_iter c order best_in_greedy_state))) =
      (pref c order (insert (hd (carrier_list best_in_greedy_state)) (to_set (result best_in_greedy_state))) 
        (num_iter c order (BestInGreedy_upd1 best_in_greedy_state)))"
      unfolding pref_def using carrier_pref_expr by simp

    ultimately have "indep_system.basis_in (matroid.indep_abs indep_set) (carrier_pref c order j)
      (pref c order (insert (hd (carrier_list best_in_greedy_state)) (to_set (result best_in_greedy_state))) j)"
      using carrier_pref_expr j_expr by auto

    then show "indep_system.basis_in (matroid.indep_abs indep_set) (carrier_pref c order j)
      (pref c order (to_set (result (BestInGreedy_upd1 best_in_greedy_state))) j)"
      using \<open>invar_1 best_in_greedy_state\<close>
      by (auto simp add: Let_def BestInGreedy_upd1_def elim!: invar_props_elims)
  qed 
qed


lemma invar_4_holds_upd2[invar_holds_intros]:
  "\<lbrakk>BestInGreedy_call_2_conds best_in_greedy_state; invar_1 best_in_greedy_state; invar_2 c order best_in_greedy_state;
    invar_3 c order best_in_greedy_state; invar_4 c order best_in_greedy_state\<rbrakk> \<Longrightarrow> invar_4 c order (BestInGreedy_upd2 best_in_greedy_state)"
proof(rule invar_props_intros, goal_cases)
  case (1 j)

  show ?case
  proof (cases "j \<le> (num_iter c order best_in_greedy_state)") 
    case True
    show "indep_system.basis_in (matroid.indep_abs indep_set) (carrier_pref c order j)
      (pref c order (to_set (result (BestInGreedy_upd2 best_in_greedy_state))) j)"
      using \<open>invar_4 c order best_in_greedy_state\<close>
      by (auto simp add: True Let_def BestInGreedy_upd2_def elim!: invar_props_elims)
  next
    case False

    have "length (carrier_list (BestInGreedy_upd2 best_in_greedy_state)) =
      length (carrier_list best_in_greedy_state) - 1"
      using \<open>BestInGreedy_call_2_conds best_in_greedy_state\<close> 
      by (auto simp add: BestInGreedy_upd2_def Let_def elim!: call_cond_elims)
    moreover have "length (carrier_list best_in_greedy_state) \<ge> 1"
      using \<open>BestInGreedy_call_2_conds best_in_greedy_state\<close> 
      by (auto elim!: call_cond_elims)
    ultimately have "num_iter c order (BestInGreedy_upd2 best_in_greedy_state) =
      1 + (num_iter c order best_in_greedy_state)"
      unfolding num_iter_def 
      using \<open>invar_2 c order best_in_greedy_state\<close> by (fastforce elim!: invar_props_elims)
    with 1(6) False have j_expr: "j = num_iter c order (BestInGreedy_upd2 best_in_greedy_state)" by auto
   
    have carrier_pref_expr:
      "carrier_pref c order (num_iter c order (BestInGreedy_upd2 best_in_greedy_state)) = 
      insert (hd (carrier_list best_in_greedy_state)) (carrier_pref c order (num_iter c order best_in_greedy_state))"
      apply (simp add: BestInGreedy_upd2_def carrier_pref_def Let_def num_iter_def)
      using \<open>BestInGreedy_call_2_conds best_in_greedy_state\<close> \<open>invar_2 c order best_in_greedy_state\<close>
        apply (clarsimp elim!: invar_props_elims call_cond_elims)
      by (metis drop_Suc length_drop num_iter_def set_take_aux_lemma tl_drop)

    have
      "insert (hd (carrier_list best_in_greedy_state)) (carrier_pref c order (num_iter c order best_in_greedy_state))
      \<subseteq> set (carrier_sorted)"
      using carrier_pref_def set_take_subset by (metis carrier_pref_expr)

    then have insert_subset_carrier:
      "insert (hd (carrier_list best_in_greedy_state)) (carrier_pref c order (num_iter c order best_in_greedy_state))
      \<subseteq> matroid.carrier_abs carrier"
      using matroid.carrier_abs_def carrier_sorted_set by simp
      
    have "(pref c order (to_set (result best_in_greedy_state)) (num_iter c order best_in_greedy_state)) =
      to_set (result best_in_greedy_state)"
      using \<open>invar_3 c order best_in_greedy_state\<close> 
      by (auto simp: pref_def elim: invar_3_props)

    then
      have indep_abs: "\<not>matroid.indep_abs indep_set (insert (hd (carrier_list best_in_greedy_state))
      (pref c order (to_set (result best_in_greedy_state)) (num_iter c order best_in_greedy_state)))"
      using \<open>invar_1 best_in_greedy_state\<close> \<open>BestInGreedy_call_2_conds best_in_greedy_state\<close> 
      by (auto elim!: invar_props_elims call_cond_elims)

    from indep_system.basis_in_preserved_not_indep[OF indep_system_axioms_abs insert_subset_carrier] indep_abs
      have "indep_system.basis_in (matroid.indep_abs indep_set)
   (insert (hd (carrier_list best_in_greedy_state)) (carrier_pref c order (num_iter c order best_in_greedy_state)))
   (pref c order (to_set (result best_in_greedy_state)) (num_iter c order best_in_greedy_state))"
      using \<open>invar_4 c order best_in_greedy_state\<close> by (auto elim!: invar_props_elims)

    moreover 
      have "(pref c order (to_set (result best_in_greedy_state))) (num_iter c order (BestInGreedy_upd2 best_in_greedy_state)) =
            (pref c order (to_set (result best_in_greedy_state))) (num_iter c order best_in_greedy_state)"
      unfolding pref_def using carrier_pref_expr \<open>invar_3 c order best_in_greedy_state\<close> invar_3_def by fastforce

    ultimately have "indep_system.basis_in (matroid.indep_abs indep_set) (carrier_pref c order j)
      (pref c order ((to_set (result best_in_greedy_state))) j)"
      using carrier_pref_expr j_expr by auto

    then show "indep_system.basis_in (matroid.indep_abs indep_set) (carrier_pref c order j)
      (pref c order (to_set (result (BestInGreedy_upd2 best_in_greedy_state))) j)"
      by (simp add: Let_def BestInGreedy_upd2_def)
  qed 
qed


lemma invar_4_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BestInGreedy_ret_1_conds best_in_greedy_state; invar_4 c order best_in_greedy_state\<rbrakk> \<Longrightarrow>
    invar_4 c order (BestInGreedy_ret1 best_in_greedy_state)"
  by (auto simp: BestInGreedy_ret1_def)

lemma invar_4_holds[invar_holds_intros]: 
   assumes "BestInGreedy_dom best_in_greedy_state" "invar_1 best_in_greedy_state" "invar_2 c order best_in_greedy_state"
     "invar_3 c order best_in_greedy_state" "invar_4 c order best_in_greedy_state"
   shows "invar_4 c order (BestInGreedy best_in_greedy_state)"
  using assms(2-)
proof(induction rule: BestInGreedy_induct[OF assms(1)])
  case IH: (1 best_in_greedy_state)
  show ?case
    apply(rule BestInGreedy_cases[where best_in_greedy_state = best_in_greedy_state])
    by (auto intro!: IH(2-) invar_holds_intros simp: BestInGreedy_simps[OF IH(1)])
qed


lemma BestInGreedy_ret_1[ret_holds_intros]:
  "BestInGreedy_ret_1_conds (best_in_greedy_state) \<Longrightarrow> BestInGreedy_ret_1_conds (BestInGreedy_ret1 best_in_greedy_state)"
  by (auto simp: BestInGreedy_ret1_def elim!: call_cond_elims intro!: call_cond_intros)

lemma ret1_holds[ret_holds_intros]:
   assumes "BestInGreedy_dom best_in_greedy_state" 
   shows "BestInGreedy_ret_1_conds (BestInGreedy best_in_greedy_state)" 
proof(induction rule: BestInGreedy_induct[OF assms(1)])
  case IH: (1 best_in_greedy_state)
  show ?case
    apply(rule BestInGreedy_cases[where best_in_greedy_state = best_in_greedy_state])
    by (auto intro: ret_holds_intros intro!: IH(2-)
             simp: BestInGreedy_simps[OF IH(1)])
qed


lemma BestInGreedy_correct_1_ret_1:
  "\<lbrakk> BestInGreedy_ret_1_conds best_in_greedy_state ; invar_1 best_in_greedy_state ; 
    invar_3 c order best_in_greedy_state ; invar_4 c order best_in_greedy_state \<rbrakk> \<Longrightarrow> 
    valid_solution (result best_in_greedy_state)"
proof-
  assume "BestInGreedy_ret_1_conds best_in_greedy_state" "invar_1 best_in_greedy_state"
    "invar_3 c order best_in_greedy_state" "invar_4 c order best_in_greedy_state"

  have "carrier_pref c order (num_iter c order best_in_greedy_state) \<subseteq> set (carrier_sorted)"
    using set_take_subset carrier_pref_def by fastforce
  then have result_subset: "subseteq (result best_in_greedy_state) carrier"
    using \<open>invar_1 best_in_greedy_state\<close> \<open>invar_3 c order best_in_greedy_state\<close>
    by (auto simp add: carrier_sorted_set set_inv_carrier elim!: invar_props_elims)

  have "\<And>X. indep_system.basis_in (matroid.indep_abs indep_set) (carrier_pref c order (num_iter c order best_in_greedy_state)) X \<Longrightarrow> 
    (matroid.indep_abs indep_set) X" 
    using \<open>carrier_pref c order (num_iter c order best_in_greedy_state) \<subseteq> set (carrier_sorted)\<close>
      indep_system.basis_in_indep_in[OF indep_system_axioms_abs]
      indep_system.indep_in_indep[OF indep_system_axioms_abs] 
      by (metis carrier_sorted_set matroid.carrier_abs_def)
  moreover have "pref c order (to_set (result best_in_greedy_state)) (num_iter c order best_in_greedy_state) = (to_set (result best_in_greedy_state))"
    unfolding pref_def using \<open>invar_3 c order best_in_greedy_state\<close> by (auto elim!: invar_props_elims)
  ultimately have result_indep: "indep' (result best_in_greedy_state)"
    using \<open>invar_1 best_in_greedy_state\<close> \<open>invar_4 c order best_in_greedy_state\<close>
    by (auto elim!: invar_props_elims)

  from result_subset result_indep show "valid_solution (result best_in_greedy_state)"
    unfolding valid_solution_def using \<open>invar_1 best_in_greedy_state\<close>
    by (auto elim!: invar_props_elims)
qed


lemma BestInGreedy_correct_2_ret_1: 
  "\<lbrakk> invar_3 c order best_in_greedy_state; invar_4 c order best_in_greedy_state ;
      BestInGreedy_ret_1_conds best_in_greedy_state ; valid_solution X \<rbrakk> \<Longrightarrow> 
      c_set c (to_set (result best_in_greedy_state)) \<ge> 
      indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_set) * 
      c_set c (to_set X)"
proof-
  assume "invar_3 c order best_in_greedy_state" "invar_4 c order best_in_greedy_state"
    "BestInGreedy_ret_1_conds best_in_greedy_state" "valid_solution X"
  let ?n = "length (carrier_sorted)"
  let ?G = "to_set (result best_in_greedy_state)"

  let ?d = "c_diff c order ?n"

  have n: "?n = length (carrier_sorted)" by auto
  have set_carrier_sorted: "set (carrier_sorted) = to_set carrier"
    using carrier_sorted_set by auto 
  have length_carrier_sorted: "length (carrier_sorted) = card (to_set carrier)"
    using length_carrier_sorted set_inv_carrier by auto  

  have "set (take (num_iter c order best_in_greedy_state) (carrier_sorted)) \<subseteq> to_set carrier"
    using set_take_subset set_carrier_sorted by fastforce
  then have greedy_subset_carrier: "?G \<subseteq> to_set carrier"
    using \<open>invar_3 c order best_in_greedy_state\<close> carrier_pref_def invar_3_def by blast
  have X_subset_carrier: "(to_set X) \<subseteq> to_set carrier"
    using \<open>valid_solution X\<close> valid_solution_def set_inv_carrier by auto

  have X_indep: "(matroid.indep_abs indep_set) (to_set X)"
    using \<open>valid_solution X\<close> valid_solution_def by auto

  have g_pos: "\<forall>j \<in> {0..?n}. rat_of_nat (card (pref c order ?G j)) \<ge> 0"
    by simp

  from set_carrier_sorted nth_mem have
    "\<forall>j \<in> {1..?n}. (carrier_sorted) ! (j - 1) \<in> to_set carrier" by fastforce
  then have c_carrier_sorted_nonneg: "\<forall>j \<in> {1..?n}. c ((carrier_sorted) ! (j - 1)) \<ge> 0"
    using cost_nonnegative set_inv_carrier by simp

  have g_zero: "rat_of_nat (card (pref c order ?G 0)) = 0"
    unfolding pref_def carrier_pref_def by simp
  have g_leq: "\<forall>j \<in> {1..?n}. card (pref c order ?G (j - 1)) \<le> card (pref c order ?G j)"
    unfolding pref_def carrier_pref_def 
    by (meson Int_mono List.finite_set card_mono diff_le_self finite_Int order_eq_refl set_take_subset_set_take)

  have "num_iter c order best_in_greedy_state = ?n"
    using \<open>BestInGreedy_ret_1_conds best_in_greedy_state\<close>
    by (auto simp add: num_iter_def elim!: call_cond_elims)
  moreover have carrier_pref_subseteq_carrier: "\<forall>j \<in> {1..?n}. (carrier_pref c order j) \<subseteq> (matroid.carrier_abs carrier)"
    unfolding carrier_pref_def matroid.carrier_abs_def using set_take_subset set_carrier_sorted by fastforce
  ultimately have G_j_geq_lower_rank_E_j:
    "\<forall>j \<in> {1..?n}. rat_of_nat (card (pref c order ?G j)) \<ge> 
       rat_of_nat (indep_system.lower_rank_of (matroid.indep_abs indep_set) (carrier_pref c order j))"
    using \<open>invar_4 c order best_in_greedy_state\<close> indep_system.lower_rank_of_leq_card_basis_in[OF indep_system_axioms_abs]
    by (auto elim!: invar_props_elims)
  
  have d_geq_0: "\<forall>j \<in> {1..?n}. ?d j \<ge> 0"
    unfolding c_diff_def using sorted_wrt_iff_nth_less
    by (smt (verit, ccfv_SIG) c_carrier_sorted_nonneg carrier_sorted_sorted_desc diff_ge_0_iff_ge
    diff_le_self dual_order.refl nat_less_le)
  
  from G_j_geq_lower_rank_E_j d_geq_0 have G_j_prod_geq_lower_rank_E_j_prod:
    "\<forall>j \<in> {1..?n}. rat_of_nat (card (pref c order ?G j)) * (?d j) \<ge>
    rat_of_nat (indep_system.lower_rank_of (matroid.indep_abs indep_set) (carrier_pref c order j)) * (?d j)"
    using mult_right_mono by blast

  from indep_system.lower_rank_geq_rank_quotient_prod_rank[OF indep_system_axioms_abs]
    carrier_pref_subseteq_carrier have rank_quotient_ineq:
    "\<forall>j \<in> {1..?n}. rat_of_nat (indep_system.lower_rank_of (matroid.indep_abs indep_set) (carrier_pref c order j)) \<ge>
    indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_set) * 
    rat_of_nat (indep_system.rank (matroid.indep_abs indep_set) (carrier_pref c order j))"
    by simp
  then have rank_quotient_prod_ineq:
    "\<forall>j \<in> {1..?n}. rat_of_nat (indep_system.lower_rank_of (matroid.indep_abs indep_set) (carrier_pref c order j)) * (?d j) \<ge>
    indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_set) * 
    rat_of_nat (indep_system.rank (matroid.indep_abs indep_set) (carrier_pref c order j)) * (?d j)"
    using d_geq_0 mult_right_mono by blast

  from indep_system.rank_quotient_geq_0[OF indep_system_axioms_abs]
    have rank_quotient_geq_0:
    "indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_set) \<ge> 0" .

  from indep_system.indep_subset[OF indep_system_axioms_abs X_indep] pref_def
    have "\<forall>j \<in> {1..?n}. indep_system.indep_in (matroid.indep_abs indep_set) (carrier_pref c order j) (pref c order (to_set X) j)"
    by (metis Int_lower1 Int_lower2 indep_system.indep_in_def indep_system_axioms_abs)
  with carrier_pref_subseteq_carrier indep_system.rank_geq_card_indep_in[OF indep_system_axioms_abs]
    have rank_E_j_geq_X_j:
    "\<forall>j \<in> {1..?n}. card (pref c order (to_set X) j) \<le> indep_system.rank (matroid.indep_abs indep_set) (carrier_pref c order j)"
    by auto
  then have rank_E_j_prod_geq_X_j_prod:
    "\<forall>j \<in> {1..?n}. rat_of_nat (indep_system.rank (matroid.indep_abs indep_set) (carrier_pref c order j)) * (?d j) \<ge>
    rat_of_nat (card (pref c order (to_set X) j)) * (?d j)" using d_geq_0 by (meson mult_right_mono of_nat_mono)

  have pref_X_pos: "\<forall>j \<in> {0..?n}. rat_of_nat (card (pref c order (to_set X) j)) \<ge> 0"
    by simp
  have pref_X_zero: "rat_of_nat (card (pref c order (to_set X) 0)) = 0"
    unfolding pref_def carrier_pref_def by simp
  have pref_X_leq: "\<forall>j \<in> {1..?n}. card (pref c order (to_set X) (j - 1)) \<le> card (pref c order (to_set X) j)"
    unfolding pref_def carrier_pref_def
    by (meson Int_mono List.finite_set card_mono diff_le_self finite_Int order_eq_refl set_take_subset_set_take)


  
  (* Main chain of inequalities *)

  have "c_set c ?G = 
    (\<Sum>j = 1..?n. rat_of_nat (card (pref c order ?G j) - card (pref c order ?G (j - 1))) * c ((carrier_sorted) ! (j - 1)))"
    using sum_set_union_expr[OF n set_carrier_sorted length_carrier_sorted greedy_subset_carrier] c_set_def[of c]
    carrier_pref_def[of c] pref_def[of c] by simp
  moreover have "(\<Sum>j = 1..?n. rat_of_nat (card (pref c order ?G j) - card (pref c order ?G (j - 1))) * c ((carrier_sorted) ! (j - 1))) = 
    (\<Sum>j = 1..?n. rat_of_nat (card (pref c order ?G j)) * (?d j))"
    using sum_diff_mult_distr[OF g_pos c_carrier_sorted_nonneg g_zero] semiring_1_cancel_class.of_nat_diff g_leq c_diff_def
    by (smt (verit) sum.cong)
  moreover have "(\<Sum>j = 1..?n. rat_of_nat (card (pref c order ?G j)) * (?d j)) \<ge> 
    (\<Sum>j = 1..?n. rat_of_nat (indep_system.lower_rank_of (matroid.indep_abs indep_set) (carrier_pref c order j)) * (?d j))"
    using G_j_prod_geq_lower_rank_E_j_prod sum_mono by fastforce 
  moreover have "(\<Sum>j = 1..?n. rat_of_nat (indep_system.lower_rank_of (matroid.indep_abs indep_set) (carrier_pref c order j)) * (?d j)) \<ge>  
    indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_set) *
    (\<Sum>j = 1..?n. rat_of_nat (indep_system.rank (matroid.indep_abs indep_set) (carrier_pref c order j)) * (?d j))"
    using rank_quotient_prod_ineq sum_distrib_left sum_mono
    by (smt (verit, del_insts) ab_semigroup_mult_class.mult_ac(1))
  moreover have "indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_set) *
    (\<Sum>j = 1..?n. rat_of_nat (indep_system.rank (matroid.indep_abs indep_set) (carrier_pref c order j)) * (?d j)) \<ge>
    indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_set) *
    (\<Sum>j = 1..?n. rat_of_nat (card (pref c order (to_set X) j)) * (?d j))"
    using rank_E_j_prod_geq_X_j_prod sum_mono rank_quotient_geq_0
    by (smt (verit) mult_left_mono)
  moreover have "indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_set) *
    (\<Sum>j = 1..?n. rat_of_nat (card (pref c order (to_set X) j)) * (?d j)) \<ge> 
    indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_set) *
    (\<Sum>j = 1..?n. rat_of_nat (card (pref c order (to_set X) j) - card (pref c order (to_set X) (j - 1))) * c ((carrier_sorted) ! (j - 1)))"
    using sum_diff_mult_distr[OF pref_X_pos c_carrier_sorted_nonneg pref_X_zero] semiring_1_cancel_class.of_nat_diff
    pref_X_leq c_diff_def rank_quotient_geq_0 mult_left_mono 
    by (smt (verit, best) order.refl sum.cong)
  moreover have "indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_set) *
    (\<Sum>j = 1..?n. rat_of_nat (card (pref c order (to_set X) j) - card (pref c order (to_set X) (j - 1))) * c ((carrier_sorted) ! (j - 1))) = 
    indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_set) *
    c_set c (to_set X)"
    using sum_set_union_expr[OF n set_carrier_sorted length_carrier_sorted X_subset_carrier]
    c_set_def[of c] carrier_pref_def[of c] pref_def[of c] by simp

  ultimately show
    "c_set c ?G \<ge> indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_set) *
    c_set c (to_set X)" by auto
qed


lemma BestInGreedy_correct_3_ret_1:
  "\<lbrakk> BestInGreedy_ret_1_conds best_in_greedy_state ; invar_1 best_in_greedy_state ; 
    invar_3 c order best_in_greedy_state ; invar_4 c order best_in_greedy_state \<rbrakk> \<Longrightarrow> 
    indep_system.basis_in (matroid.indep_abs indep_set)
    (matroid.carrier_abs carrier)
    (to_set (result best_in_greedy_state))"
proof-
  assume "BestInGreedy_ret_1_conds best_in_greedy_state" "invar_1 best_in_greedy_state"
    "invar_3 c order best_in_greedy_state" "invar_4 c order best_in_greedy_state"
  then have num_iter: "num_iter c order best_in_greedy_state = length (sort_desc c order)"
    by (auto simp add: num_iter_def elim!: call_cond_elims)
  then have "carrier_pref c order (num_iter c order best_in_greedy_state) = to_set carrier"
    unfolding carrier_pref_def using carrier_sorted_set by simp
  moreover then
    have "(pref c order (to_set (result best_in_greedy_state)) (num_iter c order best_in_greedy_state)) = 
      (to_set (result best_in_greedy_state))"
    unfolding pref_def using \<open>invar_3 c order best_in_greedy_state\<close>
    by (auto elim!: invar_props_elims)
  ultimately show "indep_system.basis_in (matroid.indep_abs indep_set)
    (matroid.carrier_abs carrier) (to_set (result best_in_greedy_state))"
    using \<open>invar_4 c order best_in_greedy_state\<close>
    by (auto simp add: matroid.carrier_abs_def elim!: invar_props_elims)
qed


subsection \<open>Termination\<close>

named_theorems termination_intros

declare termination_intros

lemma in_prod_relI[intro!,termination_intros]:
  "\<lbrakk>f1 a = f1 a'; (a, a') \<in> f2 <*mlex*> r\<rbrakk> \<Longrightarrow> (a,a') \<in> (f1 <*mlex*> f2 <*mlex*> r)"
   by (simp add: mlex_iff)+

definition "less_rel \<equiv> {(x::nat, y::nat). x < y}"

lemma wf_less_rel[intro!]: "wf less_rel"
  by(auto simp: less_rel_def wf_less)


lemma call_measure_nonsym[simp]: "(call_measure dfs_state, call_measure dfs_state) \<notin> less_rel"
  by (auto simp: less_rel_def)

lemma call_1_terminates[termination_intros]:
  "\<lbrakk>BestInGreedy_call_1_conds best_in_greedy_state\<rbrakk> \<Longrightarrow>
     (BestInGreedy_upd1 best_in_greedy_state, best_in_greedy_state) \<in> call_measure <*mlex*> r"
  by (fastforce elim!: call_cond_elims
      simp add: BestInGreedy_upd1_def call_measure_def Let_def 
      intro!: mlex_less psubset_card_mono)

lemma call_2_terminates[termination_intros]:
  "\<lbrakk>BestInGreedy_call_2_conds best_in_greedy_state\<rbrakk> \<Longrightarrow>
     (BestInGreedy_upd2 best_in_greedy_state, best_in_greedy_state) \<in> call_measure <*mlex*> r"
  by (fastforce elim!: call_cond_elims
      simp add: BestInGreedy_upd2_def call_measure_def Let_def 
      intro!: mlex_less psubset_card_mono)

lemma wf_term_rel: "wf BestInGreedy_term_rel'"
  by (auto simp: wf_mlex BestInGreedy_term_rel'_def)

lemma in_BestInGreedy_term_rel'[termination_intros]:
  "\<lbrakk>BestInGreedy_call_1_conds best_in_greedy_state\<rbrakk> \<Longrightarrow>
     (BestInGreedy_upd1 best_in_greedy_state, best_in_greedy_state) \<in> BestInGreedy_term_rel'" 
  "\<lbrakk>BestInGreedy_call_2_conds best_in_greedy_state\<rbrakk> \<Longrightarrow>
     (BestInGreedy_upd2 best_in_greedy_state, best_in_greedy_state) \<in> BestInGreedy_term_rel'"
  by (simp add: BestInGreedy_term_rel'_def termination_intros)+

lemma BestInGreedy_terminates[termination_intros]:
  assumes "invar_1 dfs_state"
  shows "BestInGreedy_dom dfs_state"
  using wf_term_rel assms
proof(induction rule: wf_induct_rule)
  case (less x)
  show ?case
    by (rule BestInGreedy_domintros) (auto intro!: invar_holds_intros less in_BestInGreedy_term_rel')
qed

lemma initial_state_props[invar_holds_intros, termination_intros]:
  "invar_1 (initial_state c order)" "invar_2 c order (initial_state c order)" "invar_3 c order (initial_state c order)"
  "invar_4 c order (initial_state c order)"
  "BestInGreedy_dom (initial_state c order)"
  by (auto simp: initial_state_def num_iter_def carrier_pref_def pref_def 
           intro!: termination_intros invar_props_intros indep_system.basis_inI[OF indep_system_axioms_abs]
           indep_system.indep_inI[OF indep_system_axioms_abs] indep_system.indep_empty[OF indep_system_axioms_abs])


lemma BestInGreedy_correct_1:
  "valid_solution (result (BestInGreedy (initial_state c order)))"
  apply (intro BestInGreedy_correct_1_ret_1[where best_in_greedy_state = "BestInGreedy (initial_state c order)"])
  by (auto intro: invar_holds_intros ret_holds_intros)

lemma BestInGreedy_correct_2:
  "\<lbrakk> valid_solution X \<rbrakk> \<Longrightarrow> c_set c (to_set (result (BestInGreedy (initial_state c order)))) \<ge> 
     indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_set) * 
     c_set c (to_set X)"
  apply (intro BestInGreedy_correct_2_ret_1[where best_in_greedy_state = "BestInGreedy (initial_state c order)"])
  by (auto intro: invar_holds_intros ret_holds_intros)

lemma BestInGreedy_correct_3:
  "indep_system.basis_in (matroid.indep_abs indep_set) (matroid.carrier_abs carrier) (to_set (result (BestInGreedy (initial_state c order))))"
  apply (intro BestInGreedy_correct_3_ret_1[where best_in_greedy_state = "BestInGreedy (initial_state c order)"])
  by (auto intro: invar_holds_intros ret_holds_intros)


end


context
  includes matroid.set.custom_automation
begin

lemma BestInGreedy_bound_tight_aux:
  "\<exists>F B1 B2 c order X.
  F \<subseteq> (matroid.carrier_abs carrier) \<and> (indep_system.basis_in (matroid.indep_abs indep_set) F B1) \<and>
  (indep_system.basis_in (matroid.indep_abs indep_set) F B2) \<and> nonnegative c \<and> valid_order order \<and> valid_solution X \<and> 
  c_set c (to_set (result (BestInGreedy (initial_state c order)))) = rat_of_nat (card B1) \<and>
  c_set c (to_set X) = rat_of_nat (card B2) \<and> card B1 \<le> card B2 \<and>
  indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_set) =
  Frac (int (card B1)) (int (card B2))"
proof-
  let ?carrier_abs = "(matroid.carrier_abs carrier)"

  from indep_system.carrier_finite[OF indep_system_axioms_abs]
    have "finite ?carrier_abs" by simp

  from indep_system.ex_rank_quotient_frac[OF indep_system_axioms_abs]
    have "\<exists>F B1 B2. F \<subseteq> (matroid.carrier_abs carrier) \<and>
    indep_system.basis_in (matroid.indep_abs indep_set) F B1 \<and>
    indep_system.basis_in (matroid.indep_abs indep_set) F B2 \<and>
    card B1 \<le> card B2 \<and>
    indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_set) = Frac (int (card B1)) (int (card B2))" by metis
  then obtain F B1 B2 where "F \<subseteq> (matroid.carrier_abs carrier)"
    "indep_system.basis_in (matroid.indep_abs indep_set) F B1"
    "indep_system.basis_in (matroid.indep_abs indep_set) F B2"
    "card B1 \<le> card B2"
    "indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_set) = Frac (int (card B1)) (int (card B2))"
    by blast

  from indep_system.basis_in_subset_carrier[OF indep_system_axioms_abs \<open>F \<subseteq> (matroid.carrier_abs carrier)\<close>
    \<open>indep_system.basis_in (matroid.indep_abs indep_set) F B1\<close>]
    have "B1 \<subseteq> F" .
  from indep_system.indep_in_indep[OF indep_system_axioms_abs
    indep_system.basis_in_indep_in[OF indep_system_axioms_abs \<open>F \<subseteq> (matroid.carrier_abs carrier)\<close>
    \<open>indep_system.basis_in (matroid.indep_abs indep_set) F B1\<close>]]
    have "(matroid.indep_abs indep_set) B1" .
    
  from indep_system.basis_in_subset_carrier[OF indep_system_axioms_abs \<open>F \<subseteq> (matroid.carrier_abs carrier)\<close>
    \<open>indep_system.basis_in (matroid.indep_abs indep_set) F B2\<close>]
    have "B2 \<subseteq> F" .

  from indep_system.basis_in_finite[OF indep_system_axioms_abs \<open>F \<subseteq> (matroid.carrier_abs carrier)\<close>
    \<open>indep_system.basis_in (matroid.indep_abs indep_set) F B1\<close>]
    have "finite B1" .
  from indep_system.carrier_finite[OF indep_system_axioms_abs] \<open>F \<subseteq> (matroid.carrier_abs carrier)\<close>
    finite_subset have "finite (F - B1)" by blast
  from indep_system.carrier_finite[OF indep_system_axioms_abs]
    finite_subset have "finite (?carrier_abs - F)" by blast

  let ?l_B1 = "sorted_list_of_set B1"
  have "length ?l_B1 = card B1" by simp
  from \<open>finite B1\<close> have "set ?l_B1 = B1" by simp

  let ?l_F_not_B1 = "sorted_list_of_set (F - B1)"
  have "length ?l_F_not_B1 = card (F - B1)" by simp
  from \<open>finite (F - B1)\<close> have "set ?l_F_not_B1 = (F - B1)" by simp

  let ?l_not_F = "sorted_list_of_set (?carrier_abs - F)"
  have "length ?l_not_F = card (?carrier_abs - F)" by simp
  from \<open>finite (?carrier_abs - F)\<close> have "set ?l_not_F = (?carrier_abs - F)" by simp

  let ?order = "?l_B1 @ ?l_F_not_B1 @ ?l_not_F"

  let ?l_F = "?l_B1 @ ?l_F_not_B1"

  from \<open>length ?l_B1 = card B1\<close> \<open>length ?l_F_not_B1 = card (F - B1)\<close>
    have "length ?l_F = card F" 
    by (metis Diff_disjoint Int_Diff_Un \<open>B1 \<subseteq> F\<close> \<open>finite (F - B1)\<close> \<open>finite B1\<close> card_Un_disjoint
    inf.absorb_iff2 length_append)
  from \<open>set ?l_B1 = B1\<close> \<open>set ?l_F_not_B1 = (F - B1)\<close> set_append[of ?l_B1 ?l_F_not_B1] \<open>B1 \<subseteq> F\<close>
    have "set ?l_F = F" by auto

  let ?l_not_B1 = "?l_F_not_B1 @ ?l_not_F"

  from \<open>length ?l_F_not_B1 = card (F - B1)\<close> \<open>length ?l_not_F = card (?carrier_abs - F)\<close>
    have "length ?l_not_B1 = card (?carrier_abs - B1)" 
    by (smt (verit) \<open>B1 \<subseteq> F\<close> \<open>F \<subseteq> matroid.carrier_abs carrier\<close> \<open>finite (matroid.carrier_abs carrier)\<close>
    card_Diff_subset card_mono dual_order.trans finite_subset le_add_diff_inverse length_append
    ordered_cancel_comm_monoid_diff_class.add_diff_assoc2)
  from \<open>set ?l_F_not_B1 = (F - B1)\<close> \<open>set ?l_not_F = (?carrier_abs - F)\<close> set_append[of ?l_F_not_B1 ?l_not_F]
    \<open>B1 \<subseteq> F\<close> \<open>F \<subseteq> matroid.carrier_abs carrier\<close>
    have "set ?l_not_B1 = (?carrier_abs - B1)"
    by auto

  from \<open>set ?l_B1 = B1\<close> \<open>set ?l_not_B1 = (?carrier_abs - B1)\<close>
    have "set ?l_B1 \<inter> set ?l_not_B1 = {}" by blast

  have order_expr1: "?order = ?l_F @ ?l_not_F" by simp
  have order_expr2: "?order = ?l_B1 @ ?l_not_B1" by simp

  from \<open>length ?l_F = card F\<close> \<open>length ?l_not_F = card (?carrier_abs - F)\<close> order_expr1
    have "length ?order = card ?carrier_abs"
    by (metis Diff_partition \<open>F \<subseteq> ?carrier_abs\<close> \<open>length ?l_not_B1 = card (?carrier_abs - B1)\<close>
      \<open>set ?l_not_B1 = ?carrier_abs - B1\<close> \<open>set ?l_not_F = ?carrier_abs - F\<close>
      \<open>set ?l_F = F\<close> \<open>set ?l_B1 \<inter> set ?l_not_B1 = {}\<close>
      card_distinct distinct_append distinct_card set_append)
  from \<open>set ?l_F = F\<close> \<open>set ?l_not_F = (?carrier_abs - F)\<close> order_expr1
    have "set ?order = ?carrier_abs"
    using \<open>F \<subseteq> matroid.carrier_abs carrier\<close> by auto

  from \<open>length ?order = card ?carrier_abs\<close> \<open>set ?order = ?carrier_abs\<close> 
    have "valid_order ?order" unfolding valid_order_def
    by (simp add: matroid.carrier_abs_def set_inv_carrier)
  then have "distinct ?order" unfolding valid_order_def using set_inv_carrier card_distinct
    by (metis matroid.set.set_cardinality)

  let ?c = "\<lambda>(x::'a). if x \<in> F then (1::rat) else 0"
  have "nonnegative ?c" using nonnegative_def by simp

  have "\<And>x. x \<in> F \<longleftrightarrow> ?c x = 1" by simp
  have "\<And>x. x \<notin> F \<longleftrightarrow> ?c x = 0" by simp
  have "\<And>x. ?c x = 1 \<longleftrightarrow> ?c x \<noteq> 0" by simp
  have "\<forall>x. ?c x = 1 \<or> ?c x = 0" by simp 

  have "(\<And>x. x \<in> set ?order \<Longrightarrow> (?c x = 1 \<longleftrightarrow> x \<in> set ?l_F))"
  proof (rule iffI, rule ccontr, goal_cases)
    case (1 x)
    with \<open>?order = ?l_F @ ?l_not_F\<close> have "x \<in> set ?l_not_F" by simp
    with \<open>set ?l_not_F = (?carrier_abs - F)\<close> have "?c x = 0" by simp
    with 1 show ?case by simp
  next
    case (2 x)
    with \<open>set ?l_F = F\<close> show ?case by auto
  qed
    
  with sorted_aux3[OF \<open>distinct ?order\<close> \<open>?order = ?l_F @ ?l_not_F\<close>]
    have "?l_F = filter (\<lambda>y. ?c y = 1) ?order" by presburger

  with \<open>?order = ?l_F @ ?l_not_F\<close>
    have "?order = (filter (\<lambda>y. ?c y = 1) ?order) @ ?l_not_F" by auto

  from sorted_aux4[OF \<open>distinct ?order\<close> this]
    have "?l_not_F = (filter (\<lambda>y. ?c y \<noteq> 1) ?order)" .
  with \<open>\<And>x. ?c x = 1 \<longleftrightarrow> ?c x \<noteq> 0\<close>
    have "?l_not_F = (filter (\<lambda>y. ?c y = 0) ?order)" by simp

  from \<open>?l_F = filter (\<lambda>y. ?c y = 1) ?order\<close>
    have "length (filter (\<lambda>y. ?c y = 1) ?order) = card F"
    using \<open>length ?l_F = card F\<close> by simp
  then have "length (filter (\<lambda>y. ?c y = 1) (sort_desc ?c ?order)) = card F"
    using sort_desc_stable[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>] by auto

  from carrier_sorted_distinct[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>]
    have "distinct (sort_desc ?c ?order)" by simp

  from \<open>length ?order = card ?carrier_abs\<close> order_expr1 \<open>length ?l_F = card F\<close>
    have "card F \<le> card ?carrier_abs"
    using \<open>F \<subseteq> matroid.carrier_abs carrier\<close> \<open>finite (matroid.carrier_abs carrier)\<close> card_mono by blast
  with length_carrier_sorted[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>]
    have "card F \<le> length (sort_desc ?c ?order)"
    using set_inv_carrier \<open>length ?order = card (matroid.carrier_abs carrier)\<close> \<open>sort_desc_axioms\<close> sort_desc_axioms_def
    by presburger
  from sorted_aux5[OF \<open>distinct (sort_desc ?c ?order)\<close> carrier_sorted_sorted_desc[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>] \<open>\<forall>x. ?c x = 1 \<or> ?c x = 0\<close>
    \<open>length (filter (\<lambda>y. ?c y = 1) (sort_desc ?c ?order)) = card F\<close> \<open>card F \<le> length (sort_desc ?c ?order)\<close>]
    have "sort_desc ?c ?order = (filter (\<lambda>y. ?c y = 1) (sort_desc ?c ?order)) @
    (filter (\<lambda>y. ?c y \<noteq> 1) (sort_desc ?c ?order))" .
  with \<open>\<And>x. ?c x = 1 \<longleftrightarrow> ?c x \<noteq> 0\<close>
    have "sort_desc ?c ?order = (filter (\<lambda>y. ?c y = 1) (sort_desc ?c ?order)) @
    (filter (\<lambda>y. ?c y = 0) (sort_desc ?c ?order))"
    by simp
  with sort_desc_stable[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>]
    have "sort_desc ?c ?order = (filter (\<lambda>y. ?c y = 1) ?order) @ (filter (\<lambda>y. ?c y = 0) ?order)"
    by simp

  with \<open>?l_F = filter (\<lambda>y. ?c y = 1) ?order\<close> \<open>?l_not_F = (filter (\<lambda>y. ?c y = 0) ?order)\<close>
    have carrier_sorted_expr: "sort_desc ?c ?order = ?l_B1 @ ?l_not_B1" by fastforce


  have num_iter_in_B1: "\<And>best_in_greedy_state. length (carrier_list best_in_greedy_state) \<ge> 1 \<Longrightarrow>
    (carrier_list best_in_greedy_state) = drop (num_iter ?c ?order best_in_greedy_state) (sort_desc ?c ?order) \<Longrightarrow>
    hd (carrier_list best_in_greedy_state) \<in> B1 \<Longrightarrow> num_iter ?c ?order best_in_greedy_state < length ?l_B1"
    using carrier_sorted_expr \<open>set ?l_B1 \<inter> set ?l_not_B1 = {}\<close> \<open>set ?l_B1 = B1\<close>
    by (smt (verit) append_Nil disjoint_iff_not_equal drop_all drop_append in_set_dropD length_greater_0_conv
    less_numeral_extra(1) linorder_le_less_linear list.set_sel(1) order_less_le_trans)
  have num_iter_not_in_B1: "\<And>best_in_greedy_state. hd (carrier_list best_in_greedy_state) \<notin> B1 \<Longrightarrow>
    (carrier_list best_in_greedy_state) = drop (num_iter ?c ?order best_in_greedy_state) (sort_desc ?c ?order) \<Longrightarrow>
    num_iter ?c ?order best_in_greedy_state \<ge> length ?l_B1"
    by (metis \<open>set ?l_B1 = B1\<close> carrier_sorted_expr drop_append drop_eq_Nil hd_append2 in_set_dropD list.set_sel(1))

  let ?prop = "\<lambda>best_in_greedy_state.
    (set (take (num_iter ?c ?order best_in_greedy_state) ?l_B1) \<subseteq> to_set (result (best_in_greedy_state))) \<and>
    (to_set (result (best_in_greedy_state)) \<subseteq> (matroid.carrier_abs carrier) - (F - B1))"


  have prop_holds_upd1:
    "\<And>best_in_greedy_state.
      BestInGreedy_call_1_conds best_in_greedy_state \<Longrightarrow> invar_1 best_in_greedy_state \<Longrightarrow>
      invar_2 ?c ?order best_in_greedy_state \<Longrightarrow> ?prop best_in_greedy_state \<Longrightarrow>
      ?prop (BestInGreedy_upd1 best_in_greedy_state)"
  proof-
    fix best_in_greedy_state::"('a, 's, 'b) best_in_greedy_state_scheme"
    assume "BestInGreedy_call_1_conds best_in_greedy_state" "invar_1 best_in_greedy_state"
      "invar_2 ?c ?order best_in_greedy_state" "?prop best_in_greedy_state"

    have "length (carrier_list (BestInGreedy_upd1 best_in_greedy_state)) =
      length (carrier_list best_in_greedy_state) - 1"
      using \<open>BestInGreedy_call_1_conds best_in_greedy_state\<close> 
      by (auto simp add: BestInGreedy_upd1_def Let_def elim!: call_cond_elims)
    moreover have "length (carrier_list best_in_greedy_state) \<ge> 1"
      using \<open>BestInGreedy_call_1_conds best_in_greedy_state\<close> 
      by (auto elim!: call_cond_elims)
    ultimately have num_iter_upd: "num_iter ?c ?order (BestInGreedy_upd1 best_in_greedy_state) =
      1 + (num_iter ?c ?order best_in_greedy_state)"
      unfolding num_iter_def 
      using \<open>invar_2 ?c ?order best_in_greedy_state\<close> \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>
      by (fastforce elim!: invar_2_props)




    have "hd (carrier_list best_in_greedy_state) \<notin> F - B1"
    proof (rule ccontr, goal_cases)
      case 1
      then have "hd (carrier_list best_in_greedy_state) \<in> F - B1" by simp

      with num_iter_not_in_B1 have "num_iter ?c ?order best_in_greedy_state \<ge> length ?l_B1"
        using \<open>invar_2 ?c ?order best_in_greedy_state\<close>
        by (auto elim!: invar_2_props[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>])
      
      with \<open>?prop best_in_greedy_state\<close> \<open>set ?l_B1 = B1\<close>
        have "B1 \<subseteq> to_set (result (best_in_greedy_state))"
        by simp 

      with \<open>?prop best_in_greedy_state\<close>
        have "to_set (result (best_in_greedy_state)) \<subseteq> (matroid.carrier_abs carrier) - (F - B1)"
        by blast

      from aux[OF \<open>F \<subseteq> (matroid.carrier_abs carrier)\<close> \<open>B1 \<subseteq> F\<close> \<open>B1 \<subseteq> to_set (result (best_in_greedy_state))\<close> this]
        have "\<exists>Y. to_set (result best_in_greedy_state) = Y \<union> B1 \<and> Y \<subseteq> matroid.carrier_abs carrier - F" .
      then obtain Y where "to_set (result best_in_greedy_state) = Y \<union> B1" "Y \<subseteq> matroid.carrier_abs carrier - F"
        by blast

      from indep_system.basis_in_max_indep_in[OF indep_system_axioms_abs \<open>F \<subseteq> (matroid.carrier_abs carrier)\<close>
        \<open>indep_system.basis_in (matroid.indep_abs indep_set) F B1\<close>]
      have "\<forall>x \<in> F - B1. \<not>(matroid.indep_abs indep_set) (insert x B1)"
        using indep_system.indep_in_def[OF indep_system_axioms_abs]
        by (metis DiffD1 \<open>F \<subseteq> matroid.carrier_abs carrier\<close> \<open>indep_system.basis_in (matroid.indep_abs indep_set) F B1\<close>
        indep_system.basis_in_indep_in indep_system_axioms_abs insert_subset)
      moreover have "\<forall>x \<in> F - B1. insert x B1 \<subseteq> insert x (B1 \<union> Y)" by blast
      ultimately have "\<forall>x \<in> F - B1. \<not>(matroid.indep_abs indep_set) (insert x (B1 \<union> Y))"
        using indep_system.indep_subset[OF indep_system_axioms_abs] by metis
      then have "\<forall>x \<in> F - B1. \<not>(matroid.indep_abs indep_set)
        (insert x (to_set (result best_in_greedy_state)))"
        using \<open>to_set (result best_in_greedy_state) = Y \<union> B1\<close>
        by (simp add: Un_commute)

      with \<open>hd (carrier_list best_in_greedy_state) \<in> F - B1\<close> 
        have "\<not>(indep' (set_insert (hd (carrier_list best_in_greedy_state)) (result best_in_greedy_state)))"
        using \<open>invar_1 best_in_greedy_state\<close>
        by (metis insert_is_Un invar_1_def matroid.indep_impl_to_abs matroid.set.invar_insert matroid.set.set_insert matroid_inv(1) matroid_inv(2) sup.commute)

      then show ?case
        using \<open>BestInGreedy_call_1_conds best_in_greedy_state\<close>
        by (auto elim!: call_cond_elims)
    qed

    moreover have "hd (carrier_list best_in_greedy_state) \<in> (matroid.carrier_abs carrier)"
      using \<open>invar_2 ?c ?order best_in_greedy_state\<close> \<open>BestInGreedy_call_1_conds best_in_greedy_state\<close>
      by (metis BestInGreedy_call_1_conds carrier_sorted_set[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>] in_set_dropD
        invar_2_props[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>] list.set_sel(1) list.simps(3) matroid.carrier_abs_def)
    ultimately have 
      "hd (carrier_list best_in_greedy_state) \<in> (matroid.carrier_abs carrier) - (F - B1)" by auto
      
    have to_set_upd: "to_set (result (BestInGreedy_upd1 best_in_greedy_state)) =
      insert (hd (carrier_list best_in_greedy_state)) (to_set (result best_in_greedy_state))"
      using \<open>invar_1 best_in_greedy_state\<close>
      by (auto simp add: BestInGreedy_upd1_def elim!: invar_1_props[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>])

    from \<open>hd (carrier_list best_in_greedy_state) \<in> (matroid.carrier_abs carrier) - (F - B1)\<close>
      \<open>B1 \<subseteq> F\<close> \<open>F \<subseteq> (matroid.carrier_abs carrier)\<close> indep_system.carrier_finite[OF indep_system_axioms_abs]
      consider "hd (carrier_list best_in_greedy_state) \<in> B1" |
      "hd (carrier_list best_in_greedy_state) \<in> (matroid.carrier_abs carrier) - F" by blast
    then have 
      prop1: "set (take (num_iter ?c ?order (BestInGreedy_upd1 best_in_greedy_state)) ?l_B1) \<subseteq>
      to_set (result (BestInGreedy_upd1 best_in_greedy_state))"
    proof (cases)
      case 1
      with num_iter_in_B1 have "num_iter ?c ?order best_in_greedy_state < length ?l_B1"
        using \<open>1 \<le> length (carrier_list best_in_greedy_state)\<close>
        \<open>invar_2 ?c ?order best_in_greedy_state\<close> 
        by (auto elim!: invar_2_props[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>])
      with carrier_sorted_expr have "num_iter ?c ?order best_in_greedy_state < length (sort_desc ?c ?order)" by auto 
      
      then have "set (take (num_iter ?c ?order (BestInGreedy_upd1 best_in_greedy_state)) (sort_desc ?c ?order)) =
        insert (hd (drop (num_iter ?c ?order best_in_greedy_state) (sort_desc ?c ?order)))
        (set (take (num_iter ?c ?order best_in_greedy_state) (sort_desc ?c ?order)))"
        apply (simp add: num_iter_upd)
        by (metis list.set(2) rotate1.simps(2) set_rotate1 take_hd_drop)
      then have "set (take (num_iter ?c ?order (BestInGreedy_upd1 best_in_greedy_state)) (sort_desc ?c ?order)) =
        insert (hd (carrier_list best_in_greedy_state))
        (set (take (num_iter ?c ?order best_in_greedy_state) (sort_desc ?c ?order)))"
        using \<open>invar_2 ?c ?order best_in_greedy_state\<close> 
        by (simp add: invar_2_def)
      
      moreover have
        "take (num_iter ?c ?order (BestInGreedy_upd1 best_in_greedy_state)) (sort_desc ?c ?order) =
          take (num_iter ?c ?order (BestInGreedy_upd1 best_in_greedy_state)) ?l_B1"
        using \<open>num_iter ?c ?order best_in_greedy_state < length ?l_B1\<close> num_iter_upd carrier_sorted_expr by simp
      moreover have
        "take (num_iter ?c ?order best_in_greedy_state) (sort_desc ?c ?order) =
          take (num_iter ?c ?order best_in_greedy_state) ?l_B1"
        using \<open>num_iter ?c ?order best_in_greedy_state < length ?l_B1\<close> carrier_sorted_expr by simp
      ultimately have "set (take (num_iter ?c ?order (BestInGreedy_upd1 best_in_greedy_state)) ?l_B1) =
        insert (hd (carrier_list best_in_greedy_state))
        (set (take (num_iter ?c ?order best_in_greedy_state) ?l_B1))" by auto   

      with \<open>?prop best_in_greedy_state\<close> to_set_upd 
        show ?thesis by blast
    next
      case 2
      with \<open>B1 \<subseteq> F\<close> num_iter_not_in_B1 have "num_iter ?c ?order best_in_greedy_state \<ge> length ?l_B1"
        using \<open>invar_2 ?c ?order best_in_greedy_state\<close>
        by (auto elim!: invar_2_props[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>]) 

      then have "set (take (num_iter ?c ?order (BestInGreedy_upd1 best_in_greedy_state)) ?l_B1) =
        set (take (num_iter ?c ?order best_in_greedy_state) ?l_B1)" using num_iter_upd by auto
      with \<open>?prop best_in_greedy_state\<close> to_set_upd 
        show ?thesis by blast
    qed

    with \<open>hd (carrier_list best_in_greedy_state) \<in> (matroid.carrier_abs carrier) - (F - B1)\<close>
      \<open>?prop best_in_greedy_state\<close>
      have "insert (hd (carrier_list best_in_greedy_state)) (to_set (result best_in_greedy_state))
        \<subseteq> matroid.carrier_abs carrier - (F - B1)"
      by blast

    then have prop2:
      "to_set (result (BestInGreedy_upd1 best_in_greedy_state)) \<subseteq> (matroid.carrier_abs carrier) - (F - B1)"
      using \<open>invar_1 best_in_greedy_state\<close>
      by (auto simp add: BestInGreedy_upd1_def elim!: invar_1_props[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>])

    from prop1 prop2 show
      "?prop (BestInGreedy_upd1 best_in_greedy_state)" by blast
  qed

  have prop_holds_upd2:
    "\<And>best_in_greedy_state.
      BestInGreedy_call_2_conds best_in_greedy_state \<Longrightarrow> invar_1 best_in_greedy_state \<Longrightarrow>
      invar_2 ?c ?order best_in_greedy_state \<Longrightarrow> invar_3 ?c ?order best_in_greedy_state \<Longrightarrow> ?prop best_in_greedy_state \<Longrightarrow>
      ?prop (BestInGreedy_upd2 best_in_greedy_state)"
  proof-
    fix best_in_greedy_state::"('a, 's, 'b) best_in_greedy_state_scheme"
    assume "BestInGreedy_call_2_conds best_in_greedy_state" "invar_1 best_in_greedy_state"
      "invar_2 ?c ?order best_in_greedy_state" "invar_3 ?c ?order best_in_greedy_state" "?prop best_in_greedy_state"


    have "length (carrier_list (BestInGreedy_upd2 best_in_greedy_state)) =
      length (carrier_list best_in_greedy_state) - 1"
      using \<open>BestInGreedy_call_2_conds best_in_greedy_state\<close> 
      by (auto simp add: BestInGreedy_upd2_def Let_def elim!: call_cond_elims)
    moreover have "length (carrier_list best_in_greedy_state) \<ge> 1"
      using \<open>BestInGreedy_call_2_conds best_in_greedy_state\<close> 
      by (auto elim!: call_cond_elims)
    ultimately have num_iter_upd: "num_iter ?c ?order (BestInGreedy_upd2 best_in_greedy_state) =
      1 + (num_iter ?c ?order best_in_greedy_state)"
      unfolding num_iter_def 
      using \<open>invar_2 ?c ?order best_in_greedy_state\<close>
      by (fastforce elim!: invar_2_props[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>])


    have "hd (carrier_list best_in_greedy_state) \<notin> B1"
    proof (rule ccontr, goal_cases)
      case 1
      then have "hd (carrier_list best_in_greedy_state) \<in> B1" by blast
      
      with num_iter_in_B1 have "num_iter ?c ?order best_in_greedy_state < length ?l_B1"
        using \<open>1 \<le> length (carrier_list best_in_greedy_state)\<close>
        \<open>invar_2 ?c ?order best_in_greedy_state\<close> 
        by (auto elim!: invar_2_props[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>])

      have "(to_set (result best_in_greedy_state)) \<subseteq> 
        set (take (num_iter ?c ?order best_in_greedy_state) (?l_B1 @ ?l_not_B1))"
        using \<open>invar_3 ?c ?order best_in_greedy_state\<close>
        by (auto simp add: carrier_pref_def carrier_sorted_expr elim!: invar_3_props[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>])
      with \<open>num_iter ?c ?order best_in_greedy_state < length ?l_B1\<close> \<open>set ?l_B1 = B1\<close> set_take_subset
        have "(to_set (result best_in_greedy_state)) \<subseteq> B1"
        by force

      with \<open>hd (carrier_list best_in_greedy_state) \<in> B1\<close>
        have "insert (hd (carrier_list best_in_greedy_state)) (to_set (result best_in_greedy_state)) \<subseteq> B1"
        by auto

      from indep_system.indep_subset[OF indep_system_axioms_abs \<open>(matroid.indep_abs (indep_set)) B1\<close> this]
        have "matroid.indep_abs indep_set (insert (hd (carrier_list best_in_greedy_state))
          (to_set (result best_in_greedy_state)))" .

      show ?case
        using \<open>invar_1 best_in_greedy_state\<close> \<open>BestInGreedy_call_2_conds best_in_greedy_state\<close>
        by (metis BestInGreedy_call_2_conds\<open>matroid.indep_abs indep_set (insert (hd (carrier_list best_in_greedy_state))
          (to_set (result best_in_greedy_state)))\<close> inf_sup_aci(5) insert_is_Un invar_1_def local.simps matroid.set.invar_insert
          matroid.set.set_insert)
    qed

    with num_iter_not_in_B1 have "num_iter ?c ?order best_in_greedy_state \<ge> length ?l_B1"
      using \<open>invar_2 ?c ?order best_in_greedy_state\<close>
      by (auto elim!: invar_2_props[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>])

    then have "set (take (num_iter ?c ?order (BestInGreedy_upd2 best_in_greedy_state)) ?l_B1) =
      set (take (num_iter ?c ?order best_in_greedy_state) ?l_B1)" using num_iter_upd by auto
    with \<open>?prop best_in_greedy_state\<close>
      have prop1: "set (take (num_iter ?c ?order (BestInGreedy_upd2 best_in_greedy_state)) ?l_B1) \<subseteq>
        to_set (result (BestInGreedy_upd2 best_in_greedy_state))"
      using \<open>BestInGreedy_call_2_conds best_in_greedy_state\<close>
      by (auto simp add: BestInGreedy_upd2_def elim!: call_cond_elims)

    with \<open>?prop best_in_greedy_state\<close>
      have prop2: "to_set (result (BestInGreedy_upd2 best_in_greedy_state)) \<subseteq> (matroid.carrier_abs carrier) - (F - B1)"
      by (auto simp add: BestInGreedy_upd2_def)

    from prop1 prop2 show "?prop (BestInGreedy_upd2 best_in_greedy_state)" by blast
  qed

  have prop_holds: "(\<And>best_in_greedy_state. 
    BestInGreedy_dom best_in_greedy_state \<Longrightarrow> invar_1 best_in_greedy_state \<Longrightarrow>
      invar_2 ?c ?order best_in_greedy_state \<Longrightarrow> invar_3 ?c ?order best_in_greedy_state \<Longrightarrow>
       ?prop best_in_greedy_state \<Longrightarrow> ?prop (BestInGreedy best_in_greedy_state))"
  proof-
    fix best_in_greedy_state
    assume assms: "BestInGreedy_dom best_in_greedy_state" "invar_1 best_in_greedy_state"
      "invar_2 ?c ?order best_in_greedy_state" "invar_3 ?c ?order best_in_greedy_state"
      "?prop best_in_greedy_state"

    show "?prop (BestInGreedy best_in_greedy_state)"
      using \<open>invar_1 best_in_greedy_state\<close> \<open>invar_2 ?c ?order best_in_greedy_state\<close>
      \<open>invar_3 ?c ?order best_in_greedy_state\<close> \<open>?prop best_in_greedy_state\<close>
    proof (induction rule: BestInGreedy_induct[OF \<open>BestInGreedy_dom best_in_greedy_state\<close>])
      case IH: (1 best_in_greedy_state)
      show ?case
        apply(rule BestInGreedy_cases[where best_in_greedy_state = best_in_greedy_state])
        subgoal
          apply(simp add: BestInGreedy_simps(1)[OF IH(1)])
          apply(rule IH(2))
          apply(assumption)
          apply (fastforce intro!: IH(4-) invar_1_holds_upd1[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>])
          apply (fastforce intro!: IH(4-) invar_2_holds_upd1[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>])
          apply (fastforce intro!: IH(4-) invar_3_holds_upd1[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>])
          using prop_holds_upd1 IH(4-) by fastforce
        subgoal
          apply(simp add: BestInGreedy_simps(2)[OF IH(1)])
          apply(rule IH(3))
          apply(assumption)
          apply (fastforce intro!: IH(4-) invar_1_holds_upd2[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>])
          apply (fastforce intro!: IH(4-) invar_2_holds_upd2[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>])
          apply (fastforce intro!: IH(4-) invar_3_holds_upd2[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>])
          using prop_holds_upd2 IH(4-) by fastforce
        subgoal
          apply(simp add: BestInGreedy_simps(3)[OF IH(1)])
          using IH(7) by (simp add: BestInGreedy_ret1_def)
        done
    qed
  qed

  have "?prop (initial_state ?c ?order)"
    unfolding num_iter_def initial_state_def by auto
  with prop_holds initial_state_props[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>]
    have "?prop (BestInGreedy (initial_state ?c ?order))" by blast


  have "length ?order = length (sort_desc ?c ?order)"
    using \<open>sort_desc_axioms\<close> sort_desc_axioms_def by blast

  have "\<And>best_in_greedy_state. BestInGreedy_dom best_in_greedy_state \<Longrightarrow> 
    carrier_list (BestInGreedy best_in_greedy_state) = []"
  proof-
    fix best_in_greedy_state
    assume "BestInGreedy_dom best_in_greedy_state"
    show "carrier_list (BestInGreedy best_in_greedy_state) = []"
    proof (induction rule: BestInGreedy_induct[OF \<open>BestInGreedy_dom best_in_greedy_state\<close>])
      case IH: (1 best_in_greedy_state)
      show ?case 
        apply(rule BestInGreedy_cases[where best_in_greedy_state = best_in_greedy_state])
        by (auto simp add: IH BestInGreedy_ret1_def BestInGreedy_simps[OF \<open>BestInGreedy_dom best_in_greedy_state\<close>] 
          elim!: BestInGreedy_ret_1_conds)
    qed
  qed

  with initial_state_props[OF \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>]
    have "num_iter ?c ?order (BestInGreedy (initial_state ?c ?order)) = length (sort_desc ?c ?order)"
    unfolding num_iter_def by auto
  with order_expr2 \<open>length ?order = length (sort_desc ?c ?order)\<close>
    have "num_iter ?c ?order (BestInGreedy (initial_state ?c ?order)) \<ge> length ?l_B1" by simp

  with \<open>?prop (BestInGreedy (initial_state ?c ?order))\<close> \<open>set ?l_B1 = B1\<close> 
    have "B1 \<subseteq> to_set (result (BestInGreedy (initial_state ?c ?order)))" by simp
  from \<open>?prop (BestInGreedy (initial_state ?c ?order))\<close>
    have "to_set (result (BestInGreedy (initial_state ?c ?order))) \<subseteq> (matroid.carrier_abs carrier) - (F - B1)"
    by blast

  from aux[OF \<open>F \<subseteq> (matroid.carrier_abs carrier)\<close> \<open>B1 \<subseteq> F\<close> \<open>B1 \<subseteq> to_set (result (BestInGreedy (initial_state ?c ?order)))\<close>
    \<open>to_set (result (BestInGreedy (initial_state ?c ?order))) \<subseteq> (matroid.carrier_abs carrier) - (F - B1)\<close>]
  have "\<exists>X. to_set (result (BestInGreedy (initial_state ?c ?order))) = X \<union> B1 \<and>
    X \<subseteq> (matroid.carrier_abs carrier) - F"
    by simp
  then obtain X where 
    "to_set (result (BestInGreedy (initial_state ?c ?order))) = X \<union> B1" "X \<subseteq> (matroid.carrier_abs carrier) - F"
    by blast
  with \<open>B1 \<subseteq> F\<close> have "X \<inter> B1 = {}" by blast

  (* Cost of greedy solution *)
  from \<open>X \<subseteq> (matroid.carrier_abs carrier) - F\<close> indep_system.carrier_finite[OF indep_system_axioms_abs]
    finite_subset
    have "finite X" by auto
  from \<open>B1 \<subseteq> F\<close> \<open>F \<subseteq> (matroid.carrier_abs carrier)\<close> indep_system.carrier_finite[OF indep_system_axioms_abs]
    finite_subset
    have "finite B1" by metis

  from sum.union_disjoint[OF \<open>finite X\<close> \<open>finite B1\<close> \<open>X \<inter> B1 = {}\<close>] 
    \<open>to_set (result (BestInGreedy (initial_state ?c ?order))) = X \<union> B1\<close>
    have "sum ?c (to_set (result (BestInGreedy (initial_state ?c ?order)))) = sum ?c X + sum ?c B1" by auto
  also have "... = sum ?c B1" using \<open>X \<subseteq> (matroid.carrier_abs carrier) - F\<close>
    using in_mono by fastforce
  also have "... = rat_of_nat (card B1)"
    using in_mono \<open>B1 \<subseteq> F\<close> by fastforce
  finally have "sum ?c (to_set (result (BestInGreedy (initial_state ?c ?order)))) = rat_of_nat (card B1)" .
  then have "c_set ?c (to_set (result (BestInGreedy (initial_state ?c ?order)))) = rat_of_nat (card B1)"
    using c_set_def by metis

  (* Cost of B2 solution *)
  have "\<exists>X_B2. set_inv X_B2 \<and> to_set X_B2 = B2"
    by (metis \<open>B2 \<subseteq> F\<close> \<open>F \<subseteq> matroid.carrier_abs carrier\<close> indep_system_axioms_abs indep_system_def
    matroid.from_set_correct matroid.invar_from_set rev_finite_subset)
  then obtain X_B2 where "set_inv X_B2" "to_set X_B2 = B2" by blast
  then have "sum ?c (to_set X_B2) = rat_of_nat (card B2)"
    using in_mono \<open>B2 \<subseteq> F\<close> by fastforce
  then have "c_set ?c (to_set X_B2) = rat_of_nat (card B2)"
    using c_set_def by metis

  (* B2 solution is valid *)
  from \<open>B2 \<subseteq> F\<close> \<open>F \<subseteq> (matroid.carrier_abs carrier)\<close> set_inv_carrier matroid.carrier_abs_def \<open>to_set X_B2 = B2\<close>
    have "subseteq X_B2 carrier"
    using Best_In_Greedy.set_inv_carrier Best_In_Greedy_axioms \<open>set_inv X_B2\<close> by force

  from indep_system.basis_in_indep_in[OF indep_system_axioms_abs \<open>F \<subseteq> (matroid.carrier_abs carrier)\<close>
    \<open>indep_system.basis_in (matroid.indep_abs indep_set) F B2\<close>]
    indep_system.indep_in_def[OF indep_system_axioms_abs] \<open>to_set X_B2 = B2\<close> \<open>set_inv X_B2\<close>
    have "indep' X_B2" by simp

  from \<open>set_inv X_B2\<close> \<open>subseteq X_B2 carrier\<close> \<open>indep' X_B2\<close> valid_solution_def 
    have "valid_solution X_B2" by simp

  from \<open>F \<subseteq> matroid.carrier_abs carrier\<close> \<open>indep_system.basis_in (matroid.indep_abs indep_set) F B1\<close>
    \<open>indep_system.basis_in (matroid.indep_abs indep_set) F B2\<close> \<open>nonnegative ?c\<close> \<open>valid_order ?order\<close>
    \<open>valid_solution X_B2\<close> \<open>c_set ?c (to_set (result (BestInGreedy (initial_state ?c ?order)))) = rat_of_nat (card B1)\<close>
    \<open>c_set ?c (to_set X_B2) = rat_of_nat (card B2)\<close> \<open>card B1 \<le> card B2\<close>
    \<open>indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_set) = Frac (int (card B1)) (int (card B2))\<close>
  show ?thesis by blast
qed

lemma BestInGreedy_bound_tight:
  "(\<exists>c. nonnegative c \<and> (\<exists>order. valid_order order \<and> (\<exists>X. valid_solution X \<and> 
     c_set c (to_set (result (BestInGreedy (initial_state c order)))) = 
     indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_set) * 
     c_set c (to_set X))))"
  using BestInGreedy_bound_tight_aux Frac_of_int_leq_quotient by fastforce

lemma BestInGreedy_matroid_iff_opt:
  "(matroid.matroid_axioms carrier indep_set) = 
    (\<forall>c. nonnegative c \<longrightarrow> (\<forall>order. valid_order order \<longrightarrow> (\<forall>X. valid_solution X \<longrightarrow>
    c_set c (to_set (result (BestInGreedy (initial_state c order)))) \<ge> c_set c (to_set X))))"
proof-

  have greedy_opt_iff_rq_eq_1: "(\<forall>c. nonnegative c \<longrightarrow> (\<forall>order. valid_order order \<longrightarrow> (\<forall>X. valid_solution X \<longrightarrow>
    c_set c (to_set (result (BestInGreedy (initial_state c order)))) \<ge> c_set c (to_set X)))) = 
    (indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_set) = 1)"
  proof (rule iffI, erule HOL.contrapos_pp)
    assume "indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_set) \<noteq> 1"
    with indep_system.rank_quotient_leq_1[OF indep_system_axioms_abs]
      have rq_less_1: "indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_set) < 1" 
      by simp

    from BestInGreedy_bound_tight_aux obtain F B1 B2 c order X 
      where bound_tight: 
      "F \<subseteq> (matroid.carrier_abs carrier)" "(indep_system.basis_in (matroid.indep_abs indep_set) F B1)"
      "(indep_system.basis_in (matroid.indep_abs indep_set) F B2)" "nonnegative c" "valid_order order" "valid_solution X"
      "c_set c (to_set (result (BestInGreedy (initial_state c order)))) = rat_of_nat (card B1)"
      "c_set c (to_set X) = rat_of_nat (card B2)" "card B1 \<le> card B2"
      "indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_set) =
      Frac (int (card B1)) (int (card B2))" by blast

    have
      c_greedy_nonneg: "c_set c (to_set (result (BestInGreedy (initial_state c order)))) \<ge> 0"
      using valid_solution_c_set_nonnegative[OF \<open>nonnegative c\<close> \<open>valid_order order\<close> BestInGreedy_correct_1[OF \<open>nonnegative c\<close> \<open>valid_order order\<close>]]
      by simp
    have
      c_X_nonneg: "c_set c (to_set X) \<ge> 0"
      using valid_solution_c_set_nonnegative[OF \<open>nonnegative c\<close> \<open>valid_order order\<close> \<open>valid_solution X\<close>] by simp

    from rq_less_1 Frac_def bound_tight
      have "card B1 \<noteq> card B2" by auto
    with bound_tight Frac_def have
      "indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_set) =
      Fract (int (card B1)) (int (card B2))" by auto
      
    from bound_tight Frac_of_int_leq_quotient \<open>card B1 \<le> card B2\<close> have rank_quotient_prod:
      "c_set c (to_set (result (BestInGreedy (initial_state c order)))) =
      indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_set) * c_set c (to_set X)"
      by simp
    
    have c_X_pos: "c_set c (to_set X) > 0"
    proof (rule ccontr, goal_cases)
      case 1
      with c_X_nonneg have "c_set c (to_set X) = 0" by simp
      with \<open>c_set c (to_set X) = rat_of_nat (card B2)\<close>
        have "card B2 = 0" by simp
      
      with \<open>card B1 \<le> card B2\<close> have "card B1 = 0" by simp

      from \<open>card B1 = 0\<close> \<open>card B2 = 0\<close>
        \<open>indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_set) =
        Frac (int (card B1)) (int (card B2))\<close>
      have "indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_set) = 1"
        using Frac_def by auto

      with rq_less_1 show ?case by simp
    qed

    from c_greedy_nonneg c_X_pos rank_quotient_prod rq_less_1
      have "c_set c (to_set (result (BestInGreedy (initial_state c order)))) < c_set c (to_set X)"
      by auto
    with \<open>nonnegative c\<close> \<open>valid_order order\<close> \<open>valid_solution X\<close>
      show "\<not>(\<forall>c. nonnegative c \<longrightarrow> (\<forall>order. valid_order order \<longrightarrow> (\<forall>X. valid_solution X \<longrightarrow>
      c_set c (to_set (result (BestInGreedy (initial_state c order)))) \<ge> c_set c (to_set X))))"
      by force
  next
    assume "(indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_set) = 1)"
    then show "(\<forall>c. nonnegative c \<longrightarrow> (\<forall>order. valid_order order \<longrightarrow> (\<forall>X. valid_solution X \<longrightarrow>
      c_set c (to_set (result (BestInGreedy (initial_state c order)))) \<ge> c_set c (to_set X))))"
    using BestInGreedy_correct_2 by simp
  qed

  from indep_system.matroid_iff_rq_eq_1[OF indep_system_axioms_abs] greedy_opt_iff_rq_eq_1
  show ?thesis 
    using BestInGreedy_axioms_def matroid.matroid_abs_equiv \<open>BestInGreedy_axioms\<close> by presburger
qed
  
end

end


end

end