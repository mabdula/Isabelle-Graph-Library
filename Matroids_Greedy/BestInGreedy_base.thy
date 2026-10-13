theory BestInGreedy_base
  imports Main Indep_System_Matroids_Specs
begin

section \<open>The Best-In-Greedy Algorithm for Matroids\<close>

record ('a, 's) best_in_greedy_state = carrier_list :: "'a list" result :: 's

named_theorems call_cond_elims
named_theorems call_cond_intros
named_theorems ret_holds_intros
named_theorems invar_props_intros
named_theorems invar_props_elims
named_theorems invar_holds_intros

definition "sort_desc_axioms sort_desc =(
  (\<forall>c order. sorted_wrt (\<lambda>x1 x2. c x1 \<ge> c x2) (sort_desc c order) \<and>
  set order = set (sort_desc c order) \<and> length order = length (sort_desc c order)))"
abbreviation "sort_desc_axioms' == sort_desc_axioms"
hide_const sort_desc_axioms

locale BestInGreedy_base = matroid: Matroid_Specs 
  where set_empty = set_empty for set_empty :: "'s" +
  fixes carrier :: "'s" and indep_fn :: "'s \<Rightarrow> bool" and
    sort_desc :: "('a \<Rightarrow> rat) \<Rightarrow> 'a list \<Rightarrow> 'a list" 

begin



abbreviation "sort_desc_axioms \<equiv> sort_desc_axioms' sort_desc"

lemma sort_desc_axioms_def: "sort_desc_axioms =(
  (\<forall>c order. sorted_wrt (\<lambda>x1 x2. c x1 \<ge> c x2) (sort_desc c order) \<and>
  set order = set (sort_desc c order) \<and> length order = length (sort_desc c order)))"
  using sort_desc_axioms_def by blast

definition "BestInGreedy_base_axioms =
  (matroid.invar carrier indep_fn \<and> matroid.finite_sets)"

abbreviation "indep' \<equiv> indep_fn"

function (domintros) BestInGreedy_base :: 
  "('a, 's) best_in_greedy_state \<Rightarrow> ('a, 's) best_in_greedy_state" where
  "BestInGreedy_base best_in_greedy_state = 
    (case (carrier_list best_in_greedy_state) of
      [] \<Rightarrow> best_in_greedy_state
    | (x # xs) \<Rightarrow> 
        (if indep' (set_insert x (result best_in_greedy_state)) then
          let
            new_result = (set_insert x (result best_in_greedy_state))
          in
            BestInGreedy_base (best_in_greedy_state \<lparr>carrier_list := xs, result := new_result\<rparr>)
        else
          BestInGreedy_base (best_in_greedy_state \<lparr>carrier_list := xs\<rparr>)
        )
    )"
  by pat_completeness auto


definition "BestInGreedy_base_call_1_conds best_in_greedy_state =
    (case (carrier_list best_in_greedy_state) of
      [] \<Rightarrow> False
    | (x # xs) \<Rightarrow> 
        (if indep' (set_insert x (result best_in_greedy_state)) then
          True
        else
          False
        )
    )"


lemma BestInGreedy_base_call_1_conds[call_cond_elims]: 
  "BestInGreedy_base_call_1_conds best_in_greedy_state \<Longrightarrow> 
   \<lbrakk>\<lbrakk>\<exists>x xs. carrier_list best_in_greedy_state = x # xs;
    indep' (set_insert (hd (carrier_list best_in_greedy_state)) (result best_in_greedy_state))\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> 
   P"
  by(auto simp: BestInGreedy_base_call_1_conds_def split: list.splits if_splits)


definition "BestInGreedy_base_upd1 best_in_greedy_state = (
  let
    x = hd (carrier_list best_in_greedy_state);
    xs = tl (carrier_list best_in_greedy_state);
    new_result = (set_insert x (result best_in_greedy_state))
  in
    best_in_greedy_state \<lparr>carrier_list := xs, result := new_result\<rparr>
  )"


definition "BestInGreedy_base_call_2_conds best_in_greedy_state =
    (case (carrier_list best_in_greedy_state) of
      [] \<Rightarrow> False
    | (x # xs) \<Rightarrow> 
        (if indep' (set_insert x (result best_in_greedy_state)) then
          False
        else
          True
        )
    )"


lemma BestInGreedy_base_call_2_conds[call_cond_elims]: 
  "BestInGreedy_base_call_2_conds best_in_greedy_state \<Longrightarrow> 
   \<lbrakk>\<lbrakk>\<exists>x xs. carrier_list best_in_greedy_state = x # xs;
    \<not>(indep' (set_insert (hd (carrier_list best_in_greedy_state)) (result best_in_greedy_state)))\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> 
   P"
  by(auto simp: BestInGreedy_base_call_2_conds_def split: list.splits if_splits)


definition "BestInGreedy_base_upd2 best_in_greedy_state = (
  let
    xs = tl (carrier_list best_in_greedy_state)
  in
    best_in_greedy_state \<lparr>carrier_list := xs\<rparr>
  )"



definition "BestInGreedy_base_ret_1_conds best_in_greedy_state =
    (case (carrier_list best_in_greedy_state) of
      [] \<Rightarrow> True
    | (x # xs) \<Rightarrow> 
        (if indep' (set_insert x (result best_in_greedy_state)) then
          False
        else
          False
        )
    )"


lemma BestInGreedy_base_ret_1_conds[call_cond_elims]:
  "BestInGreedy_base_ret_1_conds best_in_greedy_state \<Longrightarrow> 
   \<lbrakk>\<lbrakk>carrier_list best_in_greedy_state = []\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> 
   P"
  by(auto simp: BestInGreedy_base_ret_1_conds_def split: list.splits if_splits)


lemma BestInGreedy_base_ret_1_condsI[call_cond_intros]:
  "\<lbrakk>carrier_list best_in_greedy_state = []\<rbrakk> \<Longrightarrow> BestInGreedy_base_ret_1_conds best_in_greedy_state"
  by(auto simp: BestInGreedy_base_ret_1_conds_def split: list.splits if_splits)

definition "BestInGreedy_base_ret1 best_in_greedy_state = best_in_greedy_state"


lemma BestInGreedy_base_cases:
  assumes "BestInGreedy_base_call_1_conds best_in_greedy_state \<Longrightarrow> P"
    "BestInGreedy_base_call_2_conds best_in_greedy_state \<Longrightarrow> P"
    "BestInGreedy_base_ret_1_conds best_in_greedy_state \<Longrightarrow> P"
  shows "P"
proof-
  have "BestInGreedy_base_call_1_conds best_in_greedy_state \<or> BestInGreedy_base_call_2_conds best_in_greedy_state \<or>
        BestInGreedy_base_ret_1_conds best_in_greedy_state"
    by (auto simp add: BestInGreedy_base_call_1_conds_def BestInGreedy_base_call_2_conds_def
        BestInGreedy_base_ret_1_conds_def split: list.split_asm if_splits)
  then show ?thesis
    using assms
    by auto
qed


lemma BestInGreedy_base_simps:
  assumes "BestInGreedy_base_dom best_in_greedy_state" 
  shows"BestInGreedy_base_call_1_conds best_in_greedy_state \<Longrightarrow> 
          BestInGreedy_base best_in_greedy_state = BestInGreedy_base (BestInGreedy_base_upd1 best_in_greedy_state)"
    "BestInGreedy_base_call_2_conds best_in_greedy_state \<Longrightarrow> 
          BestInGreedy_base best_in_greedy_state = BestInGreedy_base (BestInGreedy_base_upd2 best_in_greedy_state)"
    "BestInGreedy_base_ret_1_conds best_in_greedy_state \<Longrightarrow> 
          BestInGreedy_base best_in_greedy_state = BestInGreedy_base_ret1 best_in_greedy_state"
  by (auto simp add: BestInGreedy_base.psimps[OF assms] Let_def
      BestInGreedy_base_call_1_conds_def BestInGreedy_base_upd1_def BestInGreedy_base_call_2_conds_def BestInGreedy_base_upd2_def
      BestInGreedy_base_ret_1_conds_def BestInGreedy_base_ret1_def split: list.splits if_splits)


lemma BestInGreedy_base_induct:
  assumes "BestInGreedy_base_dom best_in_greedy_state"
  assumes "\<And>best_in_greedy_state. \<lbrakk>BestInGreedy_base_dom best_in_greedy_state;
    BestInGreedy_base_call_1_conds best_in_greedy_state \<Longrightarrow> P (BestInGreedy_base_upd1 best_in_greedy_state);
    BestInGreedy_base_call_2_conds best_in_greedy_state \<Longrightarrow> P (BestInGreedy_base_upd2 best_in_greedy_state)\<rbrakk> \<Longrightarrow> 
      P best_in_greedy_state"
  shows "P best_in_greedy_state"
  apply(rule BestInGreedy_base.pinduct[OF assms(1)])
  apply(rule assms(2)[simplified BestInGreedy_base_call_1_conds_def BestInGreedy_base_upd1_def BestInGreedy_base_call_2_conds_def BestInGreedy_base_upd2_def])
  by (auto simp: Let_def split: list.splits if_splits)


lemma BestInGreedy_base_domintros: 
  assumes "BestInGreedy_base_call_1_conds best_in_greedy_state \<Longrightarrow> BestInGreedy_base_dom (BestInGreedy_base_upd1 best_in_greedy_state)"
  assumes "BestInGreedy_base_call_2_conds best_in_greedy_state \<Longrightarrow> BestInGreedy_base_dom (BestInGreedy_base_upd2 best_in_greedy_state)"
  shows "BestInGreedy_base_dom best_in_greedy_state"  
proof(rule BestInGreedy_base.domintros, goal_cases)
  case (1 x21 x22)
  then show ?case
    using assms(1)[simplified BestInGreedy_base_call_1_conds_def BestInGreedy_base_upd1_def]
    by (force simp: Let_def split: list.splits if_splits)
next
  case (2 x21 x22)
  then show ?case
    using assms(2)[simplified BestInGreedy_base_call_2_conds_def BestInGreedy_base_upd2_def]
    by (force split: list.splits if_splits)
qed


definition "call_measure best_in_greedy_state = length (carrier_list best_in_greedy_state)"

definition "BestInGreedy_base_term_rel' = call_measure <*mlex*> {}"

definition "initial_state c order = \<lparr>carrier_list = (sort_desc c order), result = set_empty\<rparr>"


definition "nonnegative (c::('a \<Rightarrow> rat)) = (\<forall>x. set_isin carrier x \<longrightarrow> c x \<ge> 0)"

definition "valid_order order =( to_set carrier = set order \<and> cardinality carrier = length order)"


abbreviation "subseteq \<equiv> matroid.set.subseteq"

definition
  "num_iter c order best_in_greedy_state = (length (sort_desc c order) - length (carrier_list best_in_greedy_state))"

definition
  "carrier_pref c order j = set (take j (sort_desc c order))"

definition
  "pref c order S j = S \<inter> (carrier_pref c order j)"

definition "invar_1 best_in_greedy_state = set_inv (result best_in_greedy_state)"

definition "invar_2 c order best_in_greedy_state =
  ((carrier_list best_in_greedy_state) = (drop (num_iter c order best_in_greedy_state) (sort_desc c order)))"

definition "invar_3 c order best_in_greedy_state =
  (to_set (result best_in_greedy_state) \<subseteq> (carrier_pref c order (num_iter c order best_in_greedy_state)))"

definition "invar_4 c order best_in_greedy_state =
  (\<forall>j \<in> {0..(num_iter c order best_in_greedy_state)}.
  (indep_system.basis_in (matroid.indep_abs indep_fn)
  (carrier_pref c order j)
  (pref c order (to_set (result best_in_greedy_state)) j)))"

definition "c_set c S = sum c S"

definition "c_diff c order n j =
  (if j < n then c ((sort_desc c order) ! (j - 1)) - c ((sort_desc c order) ! j) 
  else c ((sort_desc c order) ! (j - 1)))"

definition "valid_solution X =
  (set_inv X \<and> subseteq X carrier \<and> indep' X)"

context
  includes matroid.set.custom_automation
  assumes BestInGreedy_base_axioms sort_desc_axioms "matroid.indep_system_axioms carrier indep_fn"
begin

lemma matroid_inv:
  "matroid.invar carrier indep_fn"
  "matroid.finite_sets"
  using \<open>BestInGreedy_base_axioms\<close>
  by (auto simp: BestInGreedy_base_axioms_def) 

lemma indep_system_axioms_abs:
  "indep_system (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn)"
  using matroid.indep_system_impl_to_abs[OF matroid_inv(1) matroid_inv(2)]
    \<open>matroid.indep_system_axioms carrier indep_fn\<close> by simp

lemma set_inv_carrier:
  "set_inv carrier"
  using \<open>BestInGreedy_base_axioms\<close> BestInGreedy_base_axioms_def by auto

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
  "\<lbrakk>BestInGreedy_base_call_1_conds best_in_greedy_state; invar_1 best_in_greedy_state\<rbrakk> \<Longrightarrow> 
    invar_1 (BestInGreedy_base_upd1 best_in_greedy_state)"
  by (auto simp: Let_def BestInGreedy_base_upd1_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_1_holds_upd2[invar_holds_intros]:
  "\<lbrakk>BestInGreedy_base_call_2_conds best_in_greedy_state; invar_1 best_in_greedy_state\<rbrakk> \<Longrightarrow>
    invar_1 (BestInGreedy_base_upd2 best_in_greedy_state)"
  by (auto simp: BestInGreedy_base_upd2_def elim!: invar_props_elims intro: invar_props_intros)

lemma invar_1_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BestInGreedy_base_ret_1_conds best_in_greedy_state; invar_1 best_in_greedy_state\<rbrakk> \<Longrightarrow>
    invar_1 (BestInGreedy_base_ret1 best_in_greedy_state)"
  by (auto simp: BestInGreedy_base_ret1_def)

lemma invar_1_holds[invar_holds_intros]: 
  assumes "BestInGreedy_base_dom best_in_greedy_state" "invar_1 best_in_greedy_state"
  shows "invar_1 (BestInGreedy_base best_in_greedy_state)"
  using assms(2)
proof(induction rule: BestInGreedy_base_induct[OF assms(1)])
  case IH: (1 best_in_greedy_state)
  show ?case
    apply(rule BestInGreedy_base_cases[where best_in_greedy_state = best_in_greedy_state])
    by (auto intro!: IH(2-4) invar_holds_intros simp: BestInGreedy_base_simps[OF IH(1)])
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
  "\<lbrakk>BestInGreedy_base_call_1_conds best_in_greedy_state; invar_2 c order best_in_greedy_state\<rbrakk> \<Longrightarrow> 
    invar_2 c order(BestInGreedy_base_upd1 best_in_greedy_state)"
proof (intro invar_props_intros, goal_cases)
  case 1
  have "length (carrier_list (BestInGreedy_base_upd1 best_in_greedy_state)) =
    length (carrier_list best_in_greedy_state) - 1"
    using \<open>BestInGreedy_base_call_1_conds best_in_greedy_state\<close> 
    by (auto simp add: BestInGreedy_base_upd1_def Let_def elim!: call_cond_elims)
  moreover have "length (carrier_list best_in_greedy_state) \<ge> 1"
    using \<open>BestInGreedy_base_call_1_conds best_in_greedy_state\<close> 
    by (auto elim!: call_cond_elims)
  ultimately have "num_iter c order (BestInGreedy_base_upd1 best_in_greedy_state) =
    1 + (num_iter c order best_in_greedy_state)"
    unfolding num_iter_def 
    using \<open>invar_2 c order best_in_greedy_state\<close> by (fastforce elim!: invar_props_elims)
  then show ?case
    using \<open>invar_2 c order best_in_greedy_state\<close>
    by (auto simp add: drop_Suc tl_drop BestInGreedy_base_upd1_def Let_def elim!: invar_props_elims)
qed

lemma invar_2_holds_upd2[invar_holds_intros]:
  "\<lbrakk>BestInGreedy_base_call_2_conds best_in_greedy_state; invar_2 c order best_in_greedy_state\<rbrakk> \<Longrightarrow> 
    invar_2 c order (BestInGreedy_base_upd2 best_in_greedy_state)"
proof (intro invar_props_intros, goal_cases)
  case 1
  have "length (carrier_list (BestInGreedy_base_upd2 best_in_greedy_state)) =
    length (carrier_list best_in_greedy_state) - 1"
    using \<open>BestInGreedy_base_call_2_conds best_in_greedy_state\<close> 
    by (auto simp add: BestInGreedy_base_upd2_def Let_def elim!: call_cond_elims)
  moreover have "length (carrier_list best_in_greedy_state) \<ge> 1"
    using \<open>BestInGreedy_base_call_2_conds best_in_greedy_state\<close> 
    by (auto elim!: call_cond_elims)
  ultimately have "num_iter c order (BestInGreedy_base_upd2 best_in_greedy_state) =
    1 + (num_iter c order best_in_greedy_state)"
    unfolding num_iter_def 
    using \<open>invar_2 c order best_in_greedy_state\<close> by (fastforce elim!: invar_props_elims)
  then show ?case
    using \<open>invar_2 c order best_in_greedy_state\<close>
    by (auto simp add: drop_Suc tl_drop BestInGreedy_base_upd2_def Let_def elim!: invar_props_elims)
qed

lemma invar_2_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BestInGreedy_base_ret_1_conds best_in_greedy_state; invar_2 c order best_in_greedy_state\<rbrakk> \<Longrightarrow>
    invar_2 c order (BestInGreedy_base_ret1 best_in_greedy_state)"
  by (auto simp: BestInGreedy_base_ret1_def)

lemma invar_2_holds[invar_holds_intros]: 
  assumes "BestInGreedy_base_dom best_in_greedy_state" "invar_2 c order best_in_greedy_state"
  shows "invar_2 c order (BestInGreedy_base best_in_greedy_state)"
  using assms(2)
proof(induction rule: BestInGreedy_base_induct[OF assms(1)])
  case IH: (1 best_in_greedy_state)
  show ?case
    apply(rule BestInGreedy_base_cases[where best_in_greedy_state = best_in_greedy_state])
    by (auto intro!: IH(2-4) invar_holds_intros simp: BestInGreedy_base_simps[OF IH(1)])
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
  "\<lbrakk>BestInGreedy_base_call_1_conds best_in_greedy_state; invar_1 best_in_greedy_state; invar_2 c order best_in_greedy_state; 
    invar_3 c order best_in_greedy_state\<rbrakk> \<Longrightarrow> invar_3 c order (BestInGreedy_base_upd1 best_in_greedy_state)"
proof (intro invar_props_intros, goal_cases)
  case 1

  have carrier_pref_expr: "carrier_pref c order (num_iter c order (BestInGreedy_base_upd1 best_in_greedy_state)) = 
    insert (hd (carrier_list best_in_greedy_state)) (carrier_pref c order (num_iter c order best_in_greedy_state))"
    apply (simp add: BestInGreedy_base_upd1_def carrier_pref_def Let_def num_iter_def)
    using \<open>BestInGreedy_base_call_1_conds best_in_greedy_state\<close> \<open>invar_2 c order best_in_greedy_state\<close>
    apply (clarsimp elim!: invar_props_elims call_cond_elims)
    by (metis drop_Suc length_drop num_iter_def set_take_aux_lemma tl_drop)

  show "to_set (result (BestInGreedy_base_upd1 best_in_greedy_state)) \<subseteq>
    carrier_pref c order (num_iter c order (BestInGreedy_base_upd1 best_in_greedy_state))"
    using carrier_pref_expr \<open>invar_1 best_in_greedy_state\<close> \<open>invar_3 c order best_in_greedy_state\<close>
    by (auto simp add: BestInGreedy_base_upd1_def elim!: invar_props_elims)
qed

lemma invar_3_holds_upd2[invar_holds_intros]:
  "\<lbrakk>BestInGreedy_base_call_2_conds best_in_greedy_state; invar_2 c order best_in_greedy_state;
    invar_3 c order best_in_greedy_state\<rbrakk> \<Longrightarrow> invar_3 c order (BestInGreedy_base_upd2 best_in_greedy_state)"
proof (intro invar_props_intros, goal_cases)
  case 1

  have carrier_pref_expr: "carrier_pref c order (num_iter c order (BestInGreedy_base_upd2 best_in_greedy_state)) = 
    insert (hd (carrier_list best_in_greedy_state)) (carrier_pref c order (num_iter c order best_in_greedy_state))"
    apply (simp add: BestInGreedy_base_upd2_def carrier_pref_def Let_def num_iter_def 1)
    using \<open>BestInGreedy_base_call_2_conds best_in_greedy_state\<close> \<open>invar_2 c order best_in_greedy_state\<close>
    apply (clarsimp elim!: invar_props_elims call_cond_elims)
    by (metis drop_Suc length_drop num_iter_def set_take_aux_lemma tl_drop)

  show "to_set (result (BestInGreedy_base_upd2 best_in_greedy_state)) \<subseteq> 
    carrier_pref c order (num_iter c order (BestInGreedy_base_upd2 best_in_greedy_state))"
    using carrier_pref_expr \<open>invar_3 c order best_in_greedy_state\<close>
    by (auto simp add: BestInGreedy_base_upd2_def elim!: invar_props_elims)
qed

lemma invar_3_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BestInGreedy_base_ret_1_conds best_in_greedy_state; invar_3 c order best_in_greedy_state\<rbrakk> \<Longrightarrow>
    invar_3 c order (BestInGreedy_base_ret1 best_in_greedy_state)"
  by (auto simp: BestInGreedy_base_ret1_def)

lemma invar_3_holds[invar_holds_intros]: 
  assumes "BestInGreedy_base_dom best_in_greedy_state" "invar_1 best_in_greedy_state" "invar_2 c order best_in_greedy_state"
    "invar_3 c order best_in_greedy_state"
  shows "invar_3 c order (BestInGreedy_base best_in_greedy_state)"
  using assms(2-)
proof(induction rule: BestInGreedy_base_induct[OF assms(1)])
  case IH: (1 best_in_greedy_state)
  show ?case
    apply(rule BestInGreedy_base_cases[where best_in_greedy_state = best_in_greedy_state])
    by (auto intro!: IH(2-) invar_holds_intros simp: BestInGreedy_base_simps[OF IH(1)])
qed



lemma invar_4_props[invar_props_elims]:
  "invar_4 c order best_in_greedy_state \<Longrightarrow>
    (\<lbrakk>\<And>j. j \<in> {0..(num_iter c order best_in_greedy_state)} \<Longrightarrow>
      (indep_system.basis_in (matroid.indep_abs indep_fn) (carrier_pref c order j)
      (pref c order (to_set (result best_in_greedy_state)) j))\<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
    P"
  by (auto simp: invar_4_def)

lemma invar_4_intro[invar_props_intros]:
  "\<lbrakk>\<And>j. j \<in> {0..(num_iter c order best_in_greedy_state)} \<Longrightarrow>
    (indep_system.basis_in (matroid.indep_abs indep_fn) (carrier_pref c order j)
    (pref c order (to_set (result best_in_greedy_state)) j))\<rbrakk> \<Longrightarrow> invar_4 c order best_in_greedy_state"
  by (auto simp: invar_4_def)

lemma invar_4_holds_upd1[invar_holds_intros]:
  "\<lbrakk>BestInGreedy_base_call_1_conds best_in_greedy_state; invar_1 best_in_greedy_state; invar_2 c order best_in_greedy_state;
    invar_3 c order best_in_greedy_state; invar_4 c order best_in_greedy_state\<rbrakk> \<Longrightarrow> invar_4 c order (BestInGreedy_base_upd1 best_in_greedy_state)"
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
      using \<open>BestInGreedy_base_call_1_conds best_in_greedy_state\<close>
      by (auto elim!: call_cond_elims)
    then have "(pref c order (insert (hd (carrier_list best_in_greedy_state)) (to_set (result best_in_greedy_state))) j)
      = (pref c order (to_set (result best_in_greedy_state)) j)"
      unfolding pref_def by auto

    then have "indep_system.basis_in (matroid.indep_abs indep_fn) (carrier_pref c order j)
     (pref c order (insert (hd (carrier_list best_in_greedy_state)) (to_set (result best_in_greedy_state))) j)"
      using \<open>invar_4 c order best_in_greedy_state\<close> True by (auto elim!: invar_props_elims)

    then show "indep_system.basis_in (matroid.indep_abs indep_fn) (carrier_pref c order j)
      (pref c order (to_set (result (BestInGreedy_base_upd1 best_in_greedy_state))) j)"
      using \<open>invar_1 best_in_greedy_state\<close>
      by (auto simp add: Let_def BestInGreedy_base_upd1_def elim!: invar_props_elims)
  next
    case False

    have "length (carrier_list (BestInGreedy_base_upd1 best_in_greedy_state)) =
      length (carrier_list best_in_greedy_state) - 1"
      using \<open>BestInGreedy_base_call_1_conds best_in_greedy_state\<close> 
      by (auto simp add: BestInGreedy_base_upd1_def Let_def elim!: call_cond_elims)
    moreover have "length (carrier_list best_in_greedy_state) \<ge> 1"
      using \<open>BestInGreedy_base_call_1_conds best_in_greedy_state\<close> 
      by (auto elim!: call_cond_elims)
    ultimately have "num_iter c order (BestInGreedy_base_upd1 best_in_greedy_state) =
      1 + (num_iter c order best_in_greedy_state)"
      unfolding num_iter_def 
      using \<open>invar_2 c order best_in_greedy_state\<close> by (fastforce elim!: invar_props_elims)
    with 1(6) False have j_expr: "j = num_iter c order (BestInGreedy_base_upd1 best_in_greedy_state)" by auto

    have carrier_pref_expr:
      "carrier_pref c order (num_iter c order (BestInGreedy_base_upd1 best_in_greedy_state)) = 
      insert (hd (carrier_list best_in_greedy_state)) (carrier_pref c order (num_iter c order best_in_greedy_state))"
      apply (simp add: BestInGreedy_base_upd1_def carrier_pref_def Let_def num_iter_def)
      using \<open>BestInGreedy_base_call_1_conds best_in_greedy_state\<close> \<open>invar_2 c order best_in_greedy_state\<close>
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

    then have indep_abs: "matroid.indep_abs indep_fn (insert (hd (carrier_list best_in_greedy_state))
      (pref c order (to_set (result best_in_greedy_state)) (num_iter c order best_in_greedy_state)))"
      using \<open>invar_1 best_in_greedy_state\<close> \<open>BestInGreedy_base_call_1_conds best_in_greedy_state\<close> 
      by (auto elim!: invar_props_elims call_cond_elims)

    from indep_system.basis_in_preserved_indep[OF indep_system_axioms_abs insert_subset_carrier] indep_abs
    have "indep_system.basis_in (matroid.indep_abs indep_fn)
   (insert (hd (carrier_list best_in_greedy_state)) (carrier_pref c order (num_iter c order best_in_greedy_state)))
   (insert (hd (carrier_list best_in_greedy_state)) (pref c order (to_set (result best_in_greedy_state)) (num_iter c order best_in_greedy_state)))"
      using \<open>invar_4 c order best_in_greedy_state\<close>
      by (auto elim!: invar_props_elims)

    moreover have "(insert (hd (carrier_list best_in_greedy_state)) (pref c order (to_set (result best_in_greedy_state))
        (num_iter c order best_in_greedy_state))) =
      (pref c order (insert (hd (carrier_list best_in_greedy_state)) (to_set (result best_in_greedy_state))) 
        (num_iter c order (BestInGreedy_base_upd1 best_in_greedy_state)))"
      unfolding pref_def using carrier_pref_expr by simp

    ultimately have "indep_system.basis_in (matroid.indep_abs indep_fn) (carrier_pref c order j)
      (pref c order (insert (hd (carrier_list best_in_greedy_state)) (to_set (result best_in_greedy_state))) j)"
      using carrier_pref_expr j_expr by auto

    then show "indep_system.basis_in (matroid.indep_abs indep_fn) (carrier_pref c order j)
      (pref c order (to_set (result (BestInGreedy_base_upd1 best_in_greedy_state))) j)"
      using \<open>invar_1 best_in_greedy_state\<close>
      by (auto simp add: Let_def BestInGreedy_base_upd1_def elim!: invar_props_elims)
  qed 
qed


lemma invar_4_holds_upd2[invar_holds_intros]:
  "\<lbrakk>BestInGreedy_base_call_2_conds best_in_greedy_state; invar_1 best_in_greedy_state; invar_2 c order best_in_greedy_state;
    invar_3 c order best_in_greedy_state; invar_4 c order best_in_greedy_state\<rbrakk> \<Longrightarrow> invar_4 c order (BestInGreedy_base_upd2 best_in_greedy_state)"
proof(rule invar_props_intros, goal_cases)
  case (1 j)

  show ?case
  proof (cases "j \<le> (num_iter c order best_in_greedy_state)") 
    case True
    show "indep_system.basis_in (matroid.indep_abs indep_fn) (carrier_pref c order j)
      (pref c order (to_set (result (BestInGreedy_base_upd2 best_in_greedy_state))) j)"
      using \<open>invar_4 c order best_in_greedy_state\<close>
      by (auto simp add: True Let_def BestInGreedy_base_upd2_def elim!: invar_props_elims)
  next
    case False

    have "length (carrier_list (BestInGreedy_base_upd2 best_in_greedy_state)) =
      length (carrier_list best_in_greedy_state) - 1"
      using \<open>BestInGreedy_base_call_2_conds best_in_greedy_state\<close> 
      by (auto simp add: BestInGreedy_base_upd2_def Let_def elim!: call_cond_elims)
    moreover have "length (carrier_list best_in_greedy_state) \<ge> 1"
      using \<open>BestInGreedy_base_call_2_conds best_in_greedy_state\<close> 
      by (auto elim!: call_cond_elims)
    ultimately have "num_iter c order (BestInGreedy_base_upd2 best_in_greedy_state) =
      1 + (num_iter c order best_in_greedy_state)"
      unfolding num_iter_def 
      using \<open>invar_2 c order best_in_greedy_state\<close> by (fastforce elim!: invar_props_elims)
    with 1(6) False have j_expr: "j = num_iter c order (BestInGreedy_base_upd2 best_in_greedy_state)" by auto

    have carrier_pref_expr:
      "carrier_pref c order (num_iter c order (BestInGreedy_base_upd2 best_in_greedy_state)) = 
      insert (hd (carrier_list best_in_greedy_state)) (carrier_pref c order (num_iter c order best_in_greedy_state))"
      apply (simp add: BestInGreedy_base_upd2_def carrier_pref_def Let_def num_iter_def)
      using \<open>BestInGreedy_base_call_2_conds best_in_greedy_state\<close> \<open>invar_2 c order best_in_greedy_state\<close>
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
    have indep_abs: "\<not>matroid.indep_abs indep_fn (insert (hd (carrier_list best_in_greedy_state))
      (pref c order (to_set (result best_in_greedy_state)) (num_iter c order best_in_greedy_state)))"
      using \<open>invar_1 best_in_greedy_state\<close> \<open>BestInGreedy_base_call_2_conds best_in_greedy_state\<close> 
      by (auto elim!: invar_props_elims call_cond_elims)

    from indep_system.basis_in_preserved_not_indep[OF indep_system_axioms_abs insert_subset_carrier] indep_abs
    have "indep_system.basis_in (matroid.indep_abs indep_fn)
   (insert (hd (carrier_list best_in_greedy_state)) (carrier_pref c order (num_iter c order best_in_greedy_state)))
   (pref c order (to_set (result best_in_greedy_state)) (num_iter c order best_in_greedy_state))"
      using \<open>invar_4 c order best_in_greedy_state\<close> by (auto elim!: invar_props_elims)

    moreover 
    have "(pref c order (to_set (result best_in_greedy_state))) (num_iter c order (BestInGreedy_base_upd2 best_in_greedy_state)) =
            (pref c order (to_set (result best_in_greedy_state))) (num_iter c order best_in_greedy_state)"
      unfolding pref_def using carrier_pref_expr \<open>invar_3 c order best_in_greedy_state\<close> invar_3_def by fastforce

    ultimately have "indep_system.basis_in (matroid.indep_abs indep_fn) (carrier_pref c order j)
      (pref c order ((to_set (result best_in_greedy_state))) j)"
      using carrier_pref_expr j_expr by auto

    then show "indep_system.basis_in (matroid.indep_abs indep_fn) (carrier_pref c order j)
      (pref c order (to_set (result (BestInGreedy_base_upd2 best_in_greedy_state))) j)"
      by (simp add: Let_def BestInGreedy_base_upd2_def)
  qed 
qed


lemma invar_4_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BestInGreedy_base_ret_1_conds best_in_greedy_state; invar_4 c order best_in_greedy_state\<rbrakk> \<Longrightarrow>
    invar_4 c order (BestInGreedy_base_ret1 best_in_greedy_state)"
  by (auto simp: BestInGreedy_base_ret1_def)

lemma invar_4_holds[invar_holds_intros]: 
  assumes "BestInGreedy_base_dom best_in_greedy_state" "invar_1 best_in_greedy_state" "invar_2 c order best_in_greedy_state"
    "invar_3 c order best_in_greedy_state" "invar_4 c order best_in_greedy_state"
  shows "invar_4 c order (BestInGreedy_base best_in_greedy_state)"
  using assms(2-)
proof(induction rule: BestInGreedy_base_induct[OF assms(1)])
  case IH: (1 best_in_greedy_state)
  show ?case
    apply(rule BestInGreedy_base_cases[where best_in_greedy_state = best_in_greedy_state])
    by (auto intro!: IH(2-) invar_holds_intros simp: BestInGreedy_base_simps[OF IH(1)])
qed


lemma BestInGreedy_base_ret_1[ret_holds_intros]:
  "BestInGreedy_base_ret_1_conds (best_in_greedy_state) \<Longrightarrow> BestInGreedy_base_ret_1_conds (BestInGreedy_base_ret1 best_in_greedy_state)"
  by (auto simp: BestInGreedy_base_ret1_def elim!: call_cond_elims intro!: call_cond_intros)

lemma ret1_holds[ret_holds_intros]:
  assumes "BestInGreedy_base_dom best_in_greedy_state" 
  shows "BestInGreedy_base_ret_1_conds (BestInGreedy_base best_in_greedy_state)" 
proof(induction rule: BestInGreedy_base_induct[OF assms(1)])
  case IH: (1 best_in_greedy_state)
  show ?case
    apply(rule BestInGreedy_base_cases[where best_in_greedy_state = best_in_greedy_state])
    by (auto intro: ret_holds_intros intro!: IH(2-)
        simp: BestInGreedy_base_simps[OF IH(1)])
qed


lemma BestInGreedy_base_correct_1_ret_1:
  "\<lbrakk> BestInGreedy_base_ret_1_conds best_in_greedy_state ; invar_1 best_in_greedy_state ; 
    invar_3 c order best_in_greedy_state ; invar_4 c order best_in_greedy_state \<rbrakk> \<Longrightarrow> 
    valid_solution (result best_in_greedy_state)"
proof-
  assume "BestInGreedy_base_ret_1_conds best_in_greedy_state" "invar_1 best_in_greedy_state"
    "invar_3 c order best_in_greedy_state" "invar_4 c order best_in_greedy_state"

  have "carrier_pref c order (num_iter c order best_in_greedy_state) \<subseteq> set (carrier_sorted)"
    using set_take_subset carrier_pref_def by fastforce
  then have result_subset: "subseteq (result best_in_greedy_state) carrier"
    using \<open>invar_1 best_in_greedy_state\<close> \<open>invar_3 c order best_in_greedy_state\<close>
    by (auto simp add: carrier_sorted_set set_inv_carrier elim!: invar_props_elims)

  have "\<And>X. indep_system.basis_in (matroid.indep_abs indep_fn) (carrier_pref c order (num_iter c order best_in_greedy_state)) X \<Longrightarrow> 
    (matroid.indep_abs indep_fn) X" 
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


lemma BestInGreedy_base_correct_2_ret_1: 
  "\<lbrakk> invar_3 c order best_in_greedy_state; invar_4 c order best_in_greedy_state ;
      BestInGreedy_base_ret_1_conds best_in_greedy_state ; valid_solution X \<rbrakk> \<Longrightarrow> 
      c_set c (to_set (result best_in_greedy_state)) \<ge> 
      indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) * 
      c_set c (to_set X)"
proof-
  assume "invar_3 c order best_in_greedy_state" "invar_4 c order best_in_greedy_state"
    "BestInGreedy_base_ret_1_conds best_in_greedy_state" "valid_solution X"
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

  have X_indep: "(matroid.indep_abs indep_fn) (to_set X)"
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
    using \<open>BestInGreedy_base_ret_1_conds best_in_greedy_state\<close>
    by (auto simp add: num_iter_def elim!: call_cond_elims)
  moreover have carrier_pref_subseteq_carrier: "\<forall>j \<in> {1..?n}. (carrier_pref c order j) \<subseteq> (matroid.carrier_abs carrier)"
    unfolding carrier_pref_def matroid.carrier_abs_def using set_take_subset set_carrier_sorted by fastforce
  ultimately have G_j_geq_lower_rank_E_j:
    "\<forall>j \<in> {1..?n}. rat_of_nat (card (pref c order ?G j)) \<ge> 
       rat_of_nat (indep_system.lower_rank_of (matroid.indep_abs indep_fn) (carrier_pref c order j))"
    using \<open>invar_4 c order best_in_greedy_state\<close> indep_system.lower_rank_of_leq_card_basis_in[OF indep_system_axioms_abs]
    by (auto elim!: invar_props_elims)

  have d_geq_0: "\<forall>j \<in> {1..?n}. ?d j \<ge> 0"
    unfolding c_diff_def using sorted_wrt_iff_nth_less
    by (smt (verit, ccfv_SIG) c_carrier_sorted_nonneg carrier_sorted_sorted_desc diff_ge_0_iff_ge
        diff_le_self dual_order.refl nat_less_le)

  from G_j_geq_lower_rank_E_j d_geq_0 have G_j_prod_geq_lower_rank_E_j_prod:
    "\<forall>j \<in> {1..?n}. rat_of_nat (card (pref c order ?G j)) * (?d j) \<ge>
    rat_of_nat (indep_system.lower_rank_of (matroid.indep_abs indep_fn) (carrier_pref c order j)) * (?d j)"
    using mult_right_mono by blast

  from indep_system.lower_rank_geq_rank_quotient_prod_rank[OF indep_system_axioms_abs]
    carrier_pref_subseteq_carrier have rank_quotient_ineq:
    "\<forall>j \<in> {1..?n}. rat_of_nat (indep_system.lower_rank_of (matroid.indep_abs indep_fn) (carrier_pref c order j)) \<ge>
    indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) * 
    rat_of_nat (indep_system.rank (matroid.indep_abs indep_fn) (carrier_pref c order j))"
    by simp
  then have rank_quotient_prod_ineq:
    "\<forall>j \<in> {1..?n}. rat_of_nat (indep_system.lower_rank_of (matroid.indep_abs indep_fn) (carrier_pref c order j)) * (?d j) \<ge>
    indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) * 
    rat_of_nat (indep_system.rank (matroid.indep_abs indep_fn) (carrier_pref c order j)) * (?d j)"
    using d_geq_0 mult_right_mono by blast

  from indep_system.rank_quotient_geq_0[OF indep_system_axioms_abs]
  have rank_quotient_geq_0:
    "indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) \<ge> 0" .

  from indep_system.indep_subset[OF indep_system_axioms_abs X_indep] pref_def
  have "\<forall>j \<in> {1..?n}. indep_system.indep_in (matroid.indep_abs indep_fn) (carrier_pref c order j) (pref c order (to_set X) j)"
    by (metis Int_lower1 Int_lower2 indep_system.indep_in_def indep_system_axioms_abs)
  with carrier_pref_subseteq_carrier indep_system.rank_geq_card_indep_in[OF indep_system_axioms_abs]
  have rank_E_j_geq_X_j:
    "\<forall>j \<in> {1..?n}. card (pref c order (to_set X) j) \<le> indep_system.rank (matroid.indep_abs indep_fn) (carrier_pref c order j)"
    by auto
  then have rank_E_j_prod_geq_X_j_prod:
    "\<forall>j \<in> {1..?n}. rat_of_nat (indep_system.rank (matroid.indep_abs indep_fn) (carrier_pref c order j)) * (?d j) \<ge>
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
    (\<Sum>j = 1..?n. rat_of_nat (indep_system.lower_rank_of (matroid.indep_abs indep_fn) (carrier_pref c order j)) * (?d j))"
    using G_j_prod_geq_lower_rank_E_j_prod sum_mono by fastforce 
  moreover have "(\<Sum>j = 1..?n. rat_of_nat (indep_system.lower_rank_of (matroid.indep_abs indep_fn) (carrier_pref c order j)) * (?d j)) \<ge>  
    indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) *
    (\<Sum>j = 1..?n. rat_of_nat (indep_system.rank (matroid.indep_abs indep_fn) (carrier_pref c order j)) * (?d j))"
    using rank_quotient_prod_ineq sum_distrib_left sum_mono
    by (smt (verit, del_insts) ab_semigroup_mult_class.mult_ac(1))
  moreover have "indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) *
    (\<Sum>j = 1..?n. rat_of_nat (indep_system.rank (matroid.indep_abs indep_fn) (carrier_pref c order j)) * (?d j)) \<ge>
    indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) *
    (\<Sum>j = 1..?n. rat_of_nat (card (pref c order (to_set X) j)) * (?d j))"
    using rank_E_j_prod_geq_X_j_prod sum_mono rank_quotient_geq_0
    by (smt (verit) mult_left_mono)
  moreover have "indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) *
    (\<Sum>j = 1..?n. rat_of_nat (card (pref c order (to_set X) j)) * (?d j)) \<ge> 
    indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) *
    (\<Sum>j = 1..?n. rat_of_nat (card (pref c order (to_set X) j) - card (pref c order (to_set X) (j - 1))) * c ((carrier_sorted) ! (j - 1)))"
    using sum_diff_mult_distr[OF pref_X_pos c_carrier_sorted_nonneg pref_X_zero] semiring_1_cancel_class.of_nat_diff
      pref_X_leq c_diff_def rank_quotient_geq_0 mult_left_mono 
    by (smt (verit, best) order.refl sum.cong)
  moreover have "indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) *
    (\<Sum>j = 1..?n. rat_of_nat (card (pref c order (to_set X) j) - card (pref c order (to_set X) (j - 1))) * c ((carrier_sorted) ! (j - 1))) = 
    indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) *
    c_set c (to_set X)"
    using sum_set_union_expr[OF n set_carrier_sorted length_carrier_sorted X_subset_carrier]
      c_set_def[of c] carrier_pref_def[of c] pref_def[of c] by simp

  ultimately show
    "c_set c ?G \<ge> indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) *
    c_set c (to_set X)" by auto
qed


lemma BestInGreedy_base_correct_3_ret_1:
  "\<lbrakk> BestInGreedy_base_ret_1_conds best_in_greedy_state ; invar_1 best_in_greedy_state ; 
    invar_3 c order best_in_greedy_state ; invar_4 c order best_in_greedy_state \<rbrakk> \<Longrightarrow> 
    indep_system.basis_in (matroid.indep_abs indep_fn)
    (matroid.carrier_abs carrier)
    (to_set (result best_in_greedy_state))"
proof-
  assume "BestInGreedy_base_ret_1_conds best_in_greedy_state" "invar_1 best_in_greedy_state"
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
  ultimately show "indep_system.basis_in (matroid.indep_abs indep_fn)
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

definition "less_rel = {(x::nat, y::nat). x < y}"

lemma wf_less_rel[intro!]: "wf less_rel"
  by(auto simp: less_rel_def wf_less)


lemma call_measure_nonsym[simp]: "(call_measure best_in_greedy_state, call_measure best_in_greedy_state) \<notin> less_rel"
  by (auto simp: less_rel_def)

lemma call_1_terminates[termination_intros]:
  "\<lbrakk>BestInGreedy_base_call_1_conds best_in_greedy_state\<rbrakk> \<Longrightarrow>
     (BestInGreedy_base_upd1 best_in_greedy_state, best_in_greedy_state) \<in> call_measure <*mlex*> r"
  by (fastforce elim!: call_cond_elims
      simp add: BestInGreedy_base_upd1_def call_measure_def Let_def 
      intro!: mlex_less psubset_card_mono)

lemma call_2_terminates[termination_intros]:
  "\<lbrakk>BestInGreedy_base_call_2_conds best_in_greedy_state\<rbrakk> \<Longrightarrow>
     (BestInGreedy_base_upd2 best_in_greedy_state, best_in_greedy_state) \<in> call_measure <*mlex*> r"
  by (fastforce elim!: call_cond_elims
      simp add: BestInGreedy_base_upd2_def call_measure_def Let_def 
      intro!: mlex_less psubset_card_mono)

lemma wf_term_rel: "wf BestInGreedy_base_term_rel'"
  by (auto simp: wf_mlex BestInGreedy_base_term_rel'_def)

lemma in_BestInGreedy_base_term_rel'[termination_intros]:
  "\<lbrakk>BestInGreedy_base_call_1_conds best_in_greedy_state\<rbrakk> \<Longrightarrow>
     (BestInGreedy_base_upd1 best_in_greedy_state, best_in_greedy_state) \<in> BestInGreedy_base_term_rel'" 
  "\<lbrakk>BestInGreedy_base_call_2_conds best_in_greedy_state\<rbrakk> \<Longrightarrow>
     (BestInGreedy_base_upd2 best_in_greedy_state, best_in_greedy_state) \<in> BestInGreedy_base_term_rel'"
  by (simp add: BestInGreedy_base_term_rel'_def termination_intros)+

lemma BestInGreedy_base_terminates[termination_intros]:
  assumes "invar_1 best_in_greedy_state"
  shows "BestInGreedy_base_dom best_in_greedy_state"
  using wf_term_rel assms
proof(induction rule: wf_induct_rule)
  case (less x)
  show ?case
    by (rule BestInGreedy_base_domintros) (auto intro!: invar_holds_intros less in_BestInGreedy_base_term_rel')
qed

lemma initial_state_props[invar_holds_intros, termination_intros]:
  "invar_1 (initial_state c order)" "invar_2 c order (initial_state c order)" "invar_3 c order (initial_state c order)"
  "invar_4 c order (initial_state c order)"
  "BestInGreedy_base_dom (initial_state c order)"
  by (auto simp: initial_state_def num_iter_def carrier_pref_def pref_def 
      intro!: termination_intros invar_props_intros indep_system.basis_inI[OF indep_system_axioms_abs]
      indep_system.indep_inI[OF indep_system_axioms_abs] indep_system.indep_empty[OF indep_system_axioms_abs])


lemma BestInGreedy_base_correct_1:
  "valid_solution (result (BestInGreedy_base (initial_state c order)))"
  apply (intro BestInGreedy_base_correct_1_ret_1[where best_in_greedy_state = "BestInGreedy_base (initial_state c order)"])
  by (auto intro: invar_holds_intros ret_holds_intros)

lemma BestInGreedy_base_correct_2:
  "\<lbrakk> valid_solution X \<rbrakk> \<Longrightarrow> c_set c (to_set (result (BestInGreedy_base (initial_state c order)))) \<ge> 
     indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) * 
     c_set c (to_set X)"
  apply (intro BestInGreedy_base_correct_2_ret_1[where best_in_greedy_state = "BestInGreedy_base (initial_state c order)"])
  by (auto intro: invar_holds_intros ret_holds_intros)

lemma BestInGreedy_base_correct_3:
  "indep_system.basis_in (matroid.indep_abs indep_fn) (matroid.carrier_abs carrier) (to_set (result (BestInGreedy_base (initial_state c order))))"
  apply (intro BestInGreedy_base_correct_3_ret_1[where best_in_greedy_state = "BestInGreedy_base (initial_state c order)"])
  by (auto intro: invar_holds_intros ret_holds_intros)


end

end

lemma BestInGreedy_base_correct_matroid:
  "\<lbrakk> BestInGreedy_base_axioms ; sort_desc_axioms ; matroid.matroid_axioms carrier indep_fn ;
     nonnegative c ; valid_order order ; valid_solution X \<rbrakk> \<Longrightarrow>
    c_set c (to_set (result (BestInGreedy_base (initial_state c order)))) \<ge> c_set c (to_set X)"
proof-
  fix c order X
  assume "BestInGreedy_base_axioms" "sort_desc_axioms" "matroid.matroid_axioms carrier indep_fn" "nonnegative c" "valid_order order" "valid_solution X"
  from \<open>matroid.matroid_axioms carrier indep_fn\<close> have "matroid.indep_system_axioms carrier indep_fn"
    using matroid.matroid_axioms_def by blast
  have "indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) = 1"
    using indep_system.matroid_iff_rq_eq_1[OF indep_system_axioms_abs[OF \<open>BestInGreedy_base_axioms\<close> \<open>sort_desc_axioms\<close> \<open>matroid.indep_system_axioms carrier indep_fn\<close>]]
      matroid.matroid_abs_equiv \<open>BestInGreedy_base_axioms\<close> BestInGreedy_base_axioms_def \<open>matroid.matroid_axioms carrier indep_fn\<close>
    by presburger
  then show "c_set c (to_set (result (BestInGreedy_base (initial_state c order)))) \<ge> c_set c (to_set X)"
    using BestInGreedy_base_correct_2[OF \<open>BestInGreedy_base_axioms\<close> \<open>sort_desc_axioms\<close> \<open>matroid.indep_system_axioms carrier indep_fn\<close>
      \<open>nonnegative c\<close> \<open>valid_order order\<close> \<open>valid_solution X\<close>] 
    by simp
qed

end


end
