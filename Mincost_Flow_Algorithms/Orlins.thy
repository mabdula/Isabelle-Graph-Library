section \<open>Top Loop of Orlin's Algorithm\<close>
 
theory Orlins
  imports Maintain_Forest Send_Flow
begin
subsection \<open>Setup\<close>
locale orlins_spec = 
send_flow_spec where fst = fst and flow_empty = flow_empty 
  and bal_empty = bal_empty and rep_comp_empty = rep_comp_empty
  and not_blocked_empty = not_blocked_empty
  and conv_empty = conv_empty+
maintain_forest_spec where fst = fst  and flow_empty = flow_empty
  and bal_empty=bal_empty and rep_comp_empty = rep_comp_empty
  and not_blocked_empty = not_blocked_empty
  and conv_empty = conv_empty
for fst::"'edge_type \<Rightarrow> 'a" and flow_empty::'e and bal_empty::'f
    and rep_comp_empty::'g and not_blocked_empty::'i
     and conv_empty::'h+
  fixes init_flow :: "'e"
    and init_bal :: "'f"
    and init_rep_card :: "'g"
    and init_not_blocked :: "'i"
begin

definition "new_\<gamma> state = (let f = current_flow state;
                      b = balance state;
                      \<gamma> = current_\<gamma> state;
                      E' = actives state
                      in (if are_all (\<lambda> e. (abstract_flow_map f e) = (0::real)) E' then
                             min (\<gamma> / 2) (get_max (\<lambda> x bx. \<bar> bx \<bar>) b)
                             else (\<gamma> / 2)))"

function (domintros) orlins::"('e, 'f, 'c,'h, 'd, 'g, 'i) Algo_state 
\<Rightarrow> ('e, 'f, 'c,'h, 'd, 'g, 'i) Algo_state" where
"orlins state = (if return state = success then state 
                 else if return state= failure then state
                 else (let 
                      \<gamma>' = new_\<gamma> state;
                      state' = maintain_forest (state \<lparr>current_\<gamma> := \<gamma>' \<rparr>);
                      state'' = send_flow state' 
                      in orlins state''))"
  by pat_completeness auto

partial_function (tailrec) orlins_impl::"('e, 'f, 'c,'h, 'd, 'g, 'i) Algo_state 
\<Rightarrow> ('e, 'f, 'c,'h, 'd, 'g, 'i) Algo_state" where
"orlins_impl state = (if return state = success then state 
                 else if return state= failure then state
                 else (let 
                      \<gamma>' = new_\<gamma> state;
                      state' = maintain_forest_impl (state \<lparr>current_\<gamma> := \<gamma>' \<rparr>);
                      state'' = send_flow_impl state' 
                      in orlins_impl state''))"

definition "initial = \<lparr> current_flow = flow_update_all (\<lambda> e fe. 0) init_flow, 
                             balance = init_bal,  \<FF> = empty_forest,
                             conv_to_rdg = conv_empty,
                             actives = filter (\<lambda> e. fst e \<noteq> snd e) \<E>_impl,
                             return = notyetterm, 
                             current_\<gamma> = (get_max (\<lambda> x bx. \<bar> bx \<bar>) init_bal),
                             representative_comp_card = rep_comp_update_all (\<lambda> x val. (x, 1)) init_rep_card, 
                             not_blocked = not_blocked_update_all 
                                (\<lambda> e b . if fst e \<noteq> snd e then True else False) init_not_blocked\<rparr>"

lemmas [code] = orlins_impl.simps initial_def new_\<gamma>_def

definition "important state v = ( v\<in> \<V> \<and> ( \<bar>a_balance state v \<bar> > (1 - \<epsilon>)*new_\<gamma> state ))"

lemma importantE:
"important state v \<Longrightarrow> 
(v\<in> \<V> \<Longrightarrow> ( \<bar>a_balance state v \<bar> > (1 - \<epsilon>)*new_\<gamma> state ) \<Longrightarrow> P)
\<Longrightarrow> P"
and importantI:
"v\<in> \<V> \<Longrightarrow> ( \<bar>a_balance state v \<bar> > (1 - \<epsilon>)*new_\<gamma> state ) \<Longrightarrow> important state v"
  by(auto simp add: important_def)

definition orlins_one_step::"('e, 'f, 'c,'h, 'd, 'g, 'i) Algo_state 
\<Rightarrow> ('e, 'f, 'c,'h, 'd, 'g, 'i) Algo_state" where
"orlins_one_step state =(  (let 
                      \<gamma>' = new_\<gamma> state;
                      state' = maintain_forest (state \<lparr>current_\<gamma> := \<gamma>' \<rparr>);
                      state'' = send_flow state' in
                      state''))"

definition orlins_one_step_check::"('e, 'f, 'c,'h, 'd, 'g, 'i) Algo_state 
\<Rightarrow> ('e, 'f, 'c,'h, 'd, 'g, 'i) Algo_state" where
"orlins_one_step_check state =(  if return state = success then state
                                 else if return state = failure then state
                                 else orlins_one_step state)"

definition "orlins_upd_impl state =
                     (let \<gamma>' = new_\<gamma> state;
                      state' = maintain_forest_impl (state \<lparr>current_\<gamma> := \<gamma>' \<rparr>);
                      state'' = send_flow_impl state' 
                      in state'')"

definition "orlins_upd_impl_check state =
                     (if return state = success then state
                      else if return state = failure then state
                      else orlins_upd_impl state)"

lemma notyetterm_no_change:"return state \<noteq> notyetterm \<Longrightarrow> 
       compow k (orlins_one_step_check) state =  state"
  apply(induction k arbitrary: state) 
  unfolding orlins_one_step_check_def 
  using return.exhaust by auto

lemma iterated_orlins_one_step_check_mono:
      "return ((compow k orlins_one_step_check) state) \<noteq> notyetterm 
          \<Longrightarrow> return ((compow (k+l) orlins_one_step_check) state) \<noteq> notyetterm"
  apply(induction k arbitrary: l state)
  subgoal for l state 
    using notyetterm_no_change[of state l] by simp
  subgoal for k l state
    by(subst add_Suc, subst funpow_Suc_right, subst (asm) funpow_Suc_right, simp)
  done

lemma succ_fail_not_changes: " return state' = success \<or> return state' = failure  \<Longrightarrow>
     compow k orlins_one_step_check state' = state'"
  apply(induction k, simp)
  subgoal for k
    apply(subst funpow_Suc_right[of k orlins_one_step_check], simp)
    unfolding orlins_one_step_check_def
    by(auto split: if_split)
  done

lemma succ_fail_term_same_dom:
"compow (Suc k) orlins_one_step_check state = state' \<Longrightarrow>
       return state' = success \<or> return state' = failure \<Longrightarrow> 
         orlins_dom state"
proof(induction k arbitrary: state)
  case 0
  have A: "orlins_dom state"
  proof(rule orlins.domintros, goal_cases)
    case 1
    have "send_flow (maintain_forest
         (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)) =
          state'"
      using 0[simplified] 1
      by(auto simp add: orlins_one_step_def orlins_one_step_check_def Let_def)
    thus ?case 
      using 0(2)
      by(auto intro: orlins.domintros)
  qed
   then show ?case  by simp
next
  case (Suc k)
    have aa:"(orlins_one_step_check ^^ (Suc (Suc k))) state =
          (orlins_one_step_check ^^ Suc k) (orlins_one_step_check state)" 
      using funpow_Suc_right[of "Suc k" orlins_one_step_check] by simp
    show ?case 
    proof(cases "return (orlins_one_step_check state)")
      case success
      note Success = this
      hence same_state:"(orlins_one_step_check ^^ Suc k) (orlins_one_step_check state) = 
                       orlins_one_step_check state"
        using succ_fail_not_changes by fast
      have A:"orlins_dom state"
      proof(rule orlins.domintros, goal_cases)
        case 1
        then show ?case 
           using success(1) 1
           by(auto intro: orlins.domintros 
           simp add: orlins_one_step_def Let_def orlins_one_step_check_def)
       qed
      then show ?thesis by simp
    next
      case failure
      note Failure = this
      hence same_state:"(orlins_one_step_check ^^ Suc k) (orlins_one_step_check state) = 
                       orlins_one_step_check state"
        using succ_fail_not_changes by fast
      have A:"orlins_dom state"
      proof(rule orlins.domintros, goal_cases)
        case 1
        then show ?case 
           using failure(1) 1 
           by(auto intro: orlins.domintros 
                simp add: orlins_one_step_def Let_def orlins_one_step_check_def)
       qed
      then show ?thesis by simp
    next
      case notyetterm
      hence 11:"(orlins_one_step_check ^^  k) (orlins_one_step_check (orlins_one_step_check state)) = 
             (orlins_one_step_check ^^  k) (orlins_one_step (orlins_one_step_check state))"
        unfolding orlins_one_step_check_def by simp
      have 12:"orlins_dom (orlins_one_step_check state)" 
        using 11 aa Suc by auto
      have A:"orlins_dom state"
      proof(rule orlins.domintros, goal_cases)
        case 1
        then show ?case 
          using 12(1) 
          by(auto simp add: orlins_one_step_check_def orlins_one_step_def Let_def)
      qed
      then show ?thesis by simp
    qed
  qed

lemma succ_fail_term_same:
  assumes "compow (Suc k) orlins_one_step_check state = state'"
          "return state' = success \<or> return state' = failure"
    shows "orlins state = state'"
  using assms
proof(induction arbitrary:  k rule:
 orlins.pinduct[OF succ_fail_term_same_dom, of k  state state'])
  case (3 state)
  note IH=this
  show ?case
  proof(insert 3(1, 3, 4), 
        subst orlins.psimps, (rule succ_fail_term_same_dom;auto), 
        subst (asm)  funpow_Suc_right, subst (asm) o_apply, 
        subst (asm) orlins_one_step_check_def, subst (asm) orlins_one_step_def, 
        cases "return state", goal_cases)
    case 3
    show ?case 
    proof(insert 3, subst if_not_P, goal_cases)
      case 1
      thus ?case by simp
    next
      case 2
      thus ?case
      proof(subst if_not_P, goal_cases)
      case 1 
      thus ?case by simp
    next
      case 2
      thus ?case
      proof( subst (asm)  if_not_P, goal_cases)
        case 1
        thus ?case by simp
      next
        case 2 thus ?case
          proof(subst (asm) if_not_P, goal_cases)
        case 1
        thus ?case by simp
      next
        case 2
        thus ?case
        proof(cases k, goal_cases)
          case 1
          thus ?case
          unfolding Let_def
          by(subst orlins.psimps, auto intro: orlins.domintros)
      next
        case (2 nat)
        thus ?case 
          unfolding Let_def
        by(intro IH(2)[where k9 = "k-1"], auto simp add: algebra_simps)
    qed
  qed qed qed qed
  qed (auto simp add: notyetterm_no_change)
next
  case 1
  show ?case
    by(rule assms)
qed (rule assms) 

lemma succ_fail_term_same_check:
       "compow k orlins_one_step_check state = state' \<Longrightarrow> return state = notyetterm \<Longrightarrow>
       return state' = success \<or> return state' = failure \<Longrightarrow>
       orlins_dom state \<and> orlins state = state'"
 by(induction k, auto intro!: succ_fail_term_same succ_fail_term_same_dom)
end

subsection \<open>Single Step Proofs\<close>

locale orlins = 
maintain_forest +
send_flow_reasoning+
orlins_spec+
assumes  get_max: "\<And> b f. \<lbrakk> bal_invar b; dom (bal_lookup b) \<noteq> {}\<rbrakk>
           \<Longrightarrow> get_max f b = Max {f y (the (bal_lookup b y)) | y. y \<in> dom (bal_lookup b)}"
  assumes init_flow: "flow_invar init_flow" "flow_domain init_flow = \<E>"
  assumes init_bal: "bal_invar init_bal" "bal_domain init_bal = \<V>" 
                    "\<And> x. x \<in> \<V> \<Longrightarrow> the (bal_lookup init_bal x) = \<b> x"
  assumes init_rep_card: "rep_comp_invar init_rep_card" "rep_comp_domain init_rep_card = \<V>"
  assumes init_not_blocked: "not_blocked_invar init_not_blocked" "not_blocked_dom init_not_blocked = \<E>"
            "\<And> e. e \<in> not_blocked_dom init_not_blocked \<Longrightarrow> the (not_blocked_lookup init_not_blocked e) = False"
begin

lemma new_gamma_is:
  assumes "implementation_invar state" "aux_invar state"
  shows "new_\<gamma> state = 
              (if \<forall> e \<in> to_set (actives state). a_current_flow state e = 0 
               then min (current_\<gamma> state / 2) (Max {\<bar>a_balance state v\<bar> | v. v \<in> \<V>})
               else (current_\<gamma> state / 2))" (is ?thesis1)
  and "{\<bar>the (bal_lookup (balance state) y)\<bar> |y. y \<in> bal_domain (balance state)} =
       {\<bar>a_balance state v\<bar> |v. v \<in> \<V>}" (is ?thesis2)
and "get_max (\<lambda>x. abs) (balance state) = Max {\<bar>a_balance state v\<bar> |v. v \<in> \<V>}" (is ?thesis3)
and "are_all (\<lambda>e. a_current_flow state e = 0) (actives state) = 
     (\<forall> e \<in> to_set (actives state). a_current_flow state e = 0)" (is ?thesis4)
and "new_\<gamma> state \<le> (current_\<gamma> state / 2)" (is ?thesis5)
and "\<And> v. \<lbrakk> v \<in> \<V> ; \<bar>a_balance state v\<bar> \<le> (1 - \<epsilon>) * current_\<gamma> state; current_\<gamma> state\<ge> 0\<rbrakk>
          \<Longrightarrow> \<bar> a_balance state v \<bar> \<le> 2* new_\<gamma> state"
and "invar_non_zero_b state \<Longrightarrow> invar_gamma state \<Longrightarrow> invar_gamma (state\<lparr>current_\<gamma> :=new_\<gamma> state\<rparr>)"
proof-
  show thesis2: ?thesis2
  proof(unfold Setcompr_eq_image, rule image_cong, goal_cases)
    case 1
    then show ?case 
      by(rule implementation_invarE[OF assms(1)]) auto
  next
    case (2 x)
    show ?case
      apply(rule implementation_invarE[OF assms(1)])
      apply(subst  abstract_real_map_in_dom_the[of x "bal_lookup (balance state)"])
      using 2 by auto
  qed  
  show thesis3:?thesis3
    using assms(1)V_non_empt  thesis2 by (subst get_max) auto
  show thesis4: ?thesis4
    using assms(2) from_aux_invar'(17) 
    by (auto simp add: are_all)
  show thesis1: ?thesis1
    by(auto simp add: new_\<gamma>_def Let_def  thesis3 thesis4)
  thus thesis5: ?thesis5
    by argo
 show "\<bar> a_balance state v \<bar> \<le> 2* new_\<gamma> state" 
    if "v \<in> \<V>" "\<bar>a_balance state v\<bar> \<le> (1 - \<epsilon>) * current_\<gamma> state"
       "current_\<gamma> state \<ge> 0"
     for v
  proof-
    have "\<bar>a_balance state v\<bar> \<le> current_\<gamma> state"
      using that(2,3) \<epsilon>_axiom(1) mult_nonneg_nonneg[of \<epsilon> "current_\<gamma> state"] by argo
    moreover have "\<bar>a_balance state v\<bar> \<le> Max {\<bar>a_balance state v\<bar> |v. v \<in> \<V>} * 2"
      apply(rule order.trans)
      apply(rule Max.coboundedI[of "{\<bar>a_balance state v\<bar> |v. v \<in> \<V>}" "\<bar>a_balance state v\<bar>"])
      using  \<V>_finite that(1) 
      by (subst linorder_class.Max_ge_iff |
          auto intro!:  ordered_semiring_class.mult_left_mono[of 
             "1::real" 2, simplified monoid_mult_class.mult_1_right])+
    ultimately show ?thesis
      by(auto simp add: thesis1)
  qed
  show  "invar_non_zero_b state \<Longrightarrow> invar_gamma state \<Longrightarrow> 
              invar_gamma (state\<lparr>current_\<gamma> :=new_\<gamma> state\<rparr>)"
    by(auto intro!: invar_gammaI Max_lower_bound 
          simp add: thesis1 \<V>_finite
             elim!: invar_gammaE invar_non_zero_bE)
qed

lemma gamma_upd_invar_non_zero_b_pres:
  assumes "invar_non_zero_b state"
  shows "invar_non_zero_b (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
  using assms
  by(auto intro!: invar_non_zero_bI elim: invar_non_zero_bE)

lemma gamma_upd_aux_invar_pres:
  assumes "invar_gamma state" "invar_non_zero_b state"
          "aux_invar state" "implementation_invar state"
  shows "invar_gamma (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
  using Max_lower_bound[OF \<V>_finite V_non_empt , of _ 0 "\<lambda> v. \<bar>a_balance state v\<bar>"]
  by(auto elim!: invar_gammaE[OF assms(1)] invar_non_zero_bE'[OF assms(2)]
       simp add: invar_gammaD[OF assms(1)] new_gamma_is[OF assms(4,3)]
          intro: invar_gammaI )

lemma new_gamma_changes: 
"\<FF> ( (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)) = \<FF> state"
"conv_to_rdg ( (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)) = conv_to_rdg state"
"actives ( (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)) = actives state"
"representative_comp_card ( (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)) = representative_comp_card state"
"\<F> ( (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)) = \<F> state"
"\<F>_redges ( (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)) = \<F>_redges state"
"not_blocked ( (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)) = not_blocked state"
"balance ( (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)) = balance state"
"current_flow ( (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)) = current_flow state"
  by(auto simp add: Let_def \<Phi>_def F_def F_redges_def)

lemma is_multiple_multiple: "(\<exists> n::nat.  y = (real n) * x) \<Longrightarrow>
                             (\<exists> n::nat. y*2 = (real n) * x )"
  by (metis distrib_left mult.commute mult_2_right of_nat_add)

lemma minE: "((a::real) \<le> b \<Longrightarrow> P a) \<Longrightarrow> (b \<le> a \<Longrightarrow> P b) \<Longrightarrow> P (min a b)"
  by linarith

lemma Phi_init:
      assumes "orlins_entry state" "invar_non_zero_b state"
              "invar_gamma state" "implementation_invar state"
              "aux_invar state"
        shows "\<Phi> (state\<lparr>current_\<gamma> := new_\<gamma> state \<rparr>) \<le> N"
          and "\<And> x. x \<in> \<V> \<Longrightarrow> \<lceil> \<bar> a_balance state x\<bar> / (new_\<gamma> state) - (1 - \<epsilon>)\<rceil> \<le> 1" 
          and "\<And>x. x \<in> \<V> \<Longrightarrow> \<lceil>\<bar>a_balance state x\<bar> / new_\<gamma> state - (1 - \<epsilon>)\<rceil> \<ge> 0" 
proof-
  have gamma_0: "current_\<gamma> state > 0" using assms unfolding invar_gamma_def by simp
  obtain v where v_prop:"\<bar>a_balance (state\<lparr>current_\<gamma> := new_\<gamma> state \<rparr>) v\<bar> =
                  (Max { \<bar> a_balance (state\<lparr>current_\<gamma> := new_\<gamma> state \<rparr>) v\<bar> | v. v \<in> \<V>})" "v \<in> \<V>"
    using obtain_Max[OF \<V>_finite V_non_empt, of "\<lambda> v. \<bar> a_balance (state\<lparr>current_\<gamma> := new_\<gamma> state \<rparr>) v\<bar>"] 
    by auto
  hence gtr_0:"\<bar>a_balance (state\<lparr>current_\<gamma> := new_\<gamma> state \<rparr>) v\<bar> > 0" 
    using assms(2)[simplified invar_non_zero_b_def]
         Max_lower_bound[OF \<V>_finite V_non_empt,
           of _ 0 "\<lambda> v. \<bar> a_balance (state\<lparr>current_\<gamma> := new_\<gamma> state \<rparr>) v\<bar>"] by auto
  have grst:"x \<in> \<V> \<Longrightarrow>
    \<bar>a_balance (state\<lparr>current_\<gamma> := new_\<gamma> state \<rparr>) v\<bar> \<ge> \<bar>a_balance (state\<lparr>current_\<gamma> := new_\<gamma> state \<rparr>) x\<bar>"
    for x
    using v_prop Max_ge[of "{\<bar>a_balance (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>) v\<bar> |v. v \<in> \<V>}" ] \<V>_finite
    by fastforce
  have balance_eps:"x \<in> \<V>  \<Longrightarrow> \<bar> a_balance state x\<bar> / new_\<gamma> state  \<le> 2 * (1-\<epsilon>)" for x
    unfolding  new_gamma_is[OF assms(4,5)] Let_def
    apply(subst sym[OF v_prop(1)[simplified]], rule P_of_ifI)
    apply(rule minE, simp, thin_tac \<open>\<forall>e\<in> to_set (actives state). a_current_flow state e = 0\<close>,
                              thin_tac \<open>current_\<gamma> state \<le> \<bar>a_balance state v\<bar> * 2\<close>)
    subgoal ast
      using assms(1)[simplified orlins_entry_def] \<epsilon>_axiom  gamma_0 
      by (smt (verit, best) diff_divide_eq_iff mult_imp_le_div_pos mult_minus_left)
    apply(rule order.trans[of _ 1])
    using \<epsilon>_axiom grst[simplified, of x] gamma_0 
    apply (metis abs_0_eq divide_le_eq_1 zero_less_abs_iff)
    using \<epsilon>_axiom ast by auto
  have "x \<in> \<V> \<Longrightarrow> \<lceil> \<bar> a_balance state x\<bar> / (new_\<gamma> state) - (1 - \<epsilon>)\<rceil> \<le> 1" for x
    using balance_eps[of x] \<epsilon>_axiom(1,2)
    by (smt (verit, del_insts)  ceiling_le_one gamma_0 le_divide_eq_1_pos mult_le_cancel_right1 )
  thus "\<And>x. x \<in> \<V> \<Longrightarrow> \<lceil>\<bar>a_balance state x\<bar> / new_\<gamma> state - (1 - \<epsilon>)\<rceil> \<le> 1" by simp
  thus "\<Phi> (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>) \<le> int N" unfolding \<Phi>_def N_def
    using sum_bounded_above[of \<V> "\<lambda> x. \<lceil>\<bar>a_balance state x\<bar> / new_\<gamma> state - (1 - \<epsilon>)\<rceil>" 1] by simp
  have "new_\<gamma> state > 0"
    unfolding  new_gamma_is[OF assms(4,5)] Let_def
    apply(subst sym[OF v_prop(1)[simplified]], rule P_of_ifI)
    apply(rule minE, simp, thin_tac \<open>\<forall>e\<in>to_set (actives state). a_current_flow state e = 0\<close>,
                              thin_tac \<open>current_\<gamma> state \<le> \<bar>a_balance state v\<bar> * 2\<close>)
    subgoal ast
      using assms(1)[simplified orlins_entry_def] \<epsilon>_axiom  gamma_0 
      by (smt (verit, best) diff_divide_eq_iff mult_imp_le_div_pos mult_minus_left)
    using gtr_0 
    by (auto simp add: gamma_0)
  thus "\<And>x. x \<in> \<V> \<Longrightarrow> \<lceil>\<bar>a_balance state x\<bar> / new_\<gamma> state - (1 - \<epsilon>)\<rceil> \<ge> 0" 
    by (smt (verit) \<epsilon>_axiom(1) ceiling_less_zero divide_nonneg_nonneg)
qed

lemma invar_integral_gamma_upd:
  assumes "aux_invar state"
          "implementation_invar state"
          "invar_integral state"
    shows "invar_integral (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
proof(unfold  new_gamma_is(1)[OF assms(2,1)],
      rule invar_integralI, rule P_of_ifI, goal_cases)
  case (1 e)
  then show ?case by simp
next
  case (2 e)
  then obtain x where "a_current_flow state e = real x * current_\<gamma> state"
    using invar_integralD[OF assms(3), of e] 
    by auto
  then show ?case 
    by(auto intro: exI[of _ "2* x"])
qed

lemma invars_pres_orlins_one_step:
  assumes "aux_invar state"
          "invar_gamma state"
          "implementation_invar state"
          "invar_non_zero_b state"
          "orlins_entry state"
          "invar_forest state"
          "invar_integral state"
          "invar_isOptflow state"
    shows "aux_invar  (orlins_one_step state)"
          "invar_gamma  (orlins_one_step state)"
          "implementation_invar (orlins_one_step state)"
          "return (orlins_one_step state) = notyetterm
            \<Longrightarrow> orlins_entry (orlins_one_step state)"
          "invar_forest (orlins_one_step state)"
          "invar_integral (orlins_one_step state)"  
          "invar_isOptflow (orlins_one_step state)"
          "return (orlins_one_step state) = success \<Longrightarrow>
           is_Opt \<b> (a_current_flow (orlins_one_step state))"
          "return (orlins_one_step state) = failure \<Longrightarrow>
           \<nexists> f. f is \<b> flow"
          "\<And> x. x \<in> \<V> \<Longrightarrow> \<bar> a_balance state x \<bar>\<le> 2*new_\<gamma> state"
          "return (orlins_one_step state) = notyetterm \<Longrightarrow>
           invar_non_zero_b (orlins_one_step state)"
           "orlins_dom state \<Longrightarrow> return state = notyetterm \<Longrightarrow>
            orlins state = orlins (orlins_upd_impl state)"
           "current_\<gamma> (orlins_one_step state) = new_\<gamma> state"
           "send_flow_impl (maintain_forest_impl (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)) =
            send_flow (maintain_forest (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
    and  invars_after_maintain_forest:
          "aux_invar  (maintain_forest (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
          "invar_gamma  (maintain_forest (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
          "implementation_invar  (maintain_forest (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
          "send_flow_entryF (maintain_forest (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
          "invar_integral  (maintain_forest (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
          "invar_isOptflow  (maintain_forest (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
          "invarA_2 (8 * real N * new_\<gamma> state) (2 * new_\<gamma> state)
               (local.maintain_forest (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
           "invar_above_6Ngamma (maintain_forest (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
           "invarA_1 (2 * new_\<gamma> state) (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
         " (maintain_forest_dom (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
        "send_flow_dom (local.maintain_forest (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
proof-
  have aux_invar_gamma_upd: "aux_invar (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
    by(auto intro: aux_invar_gamma simp add: assms)
  have invar_gamma_gamma_upd: "invar_gamma (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
    by (simp add: assms(1,2,3,4) gamma_upd_aux_invar_pres)
  hence new_gamma_0: "new_\<gamma> state > 0" by(auto elim!: invar_gammaE)
  have implementation_invar_gamma_upd:"implementation_invar (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)" 
    by(auto intro!: implementation_invar_gamm_upd assms(3))
  show maintain_forest_dom: "maintain_forest_dom (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
    using aux_invar_gamma_upd implementation_invar_gamma_upd termination_of_maintain_forest'
    by blast
  have maintain_forest_entry: "maintain_forest_entry (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
    using new_gamma_is(5)[OF assms(3,1)] N_gtr_0
    by(force simp add: algebra_simps  new_gamma_changes
              intro: invar_forestE[OF assms(6)]
              intro!: order.strict_trans1[of "real N * (8 * new_\<gamma> state)"
                                  "current_\<gamma> state * (real N * 4)"]
                      maintain_forest_entryI)
  have component_card_gtr_0: "v \<in> \<V> \<Longrightarrow> (card (connected_component (to_graph (\<FF> state)) v)) > 0"
   and  component_card_geq_0: "v \<in> \<V> \<Longrightarrow> (card (connected_component (to_graph (\<FF> state)) v)) \<ge> 1"for v
    using finite_subset[OF _ \<V>_finite] from_aux_invar'(10)[OF assms(1)]
    by(auto simp add: card_gt_0_iff connected_component_non_empt leI)
  show invar_A1: "invarA_1 (2 * new_\<gamma> state) (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
  proof(rule invarA_1I, goal_cases)
    case (1 v)
    have "\<bar>a_balance state v\<bar> \<le> 2 * new_\<gamma> state"
      using new_gamma_is(5)[OF assms(3,1)]  orlins_entryD[OF assms(5) 1] new_gamma_is(6)[OF assms(3,1) 1] new_gamma_0
      by auto
    also have "... \<le> 2 * new_\<gamma> state * real (card (connected_component (to_graph (\<FF> state)) v))"
      using component_card_geq_0[OF 1]  new_gamma_0
      by auto
    finally show ?case  by auto
  qed
  have invarA_2: "invarA_2 (8 * real N * new_\<gamma> state) 
               (2 * new_\<gamma> state) (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
  proof(rule invarA_2I, goal_cases)
    case (1 e)
    hence fst_in_V:"fst e \<in> \<V>"
      using aux_invar_gamma_upd from_aux_invar'(3) fst_E_V by blast
    have "8 * real N * new_\<gamma> state -
        2 * new_\<gamma> state * real (card (connected_component (to_graph (\<FF> state)) (fst e)))
       \<le> 8 * real N * new_\<gamma> state"
      using  component_card_geq_0[OF fst_in_V]  new_gamma_0 by auto
    also have "... \<le> 4 * real N * current_\<gamma> state "
      using  new_gamma_is(5)[OF assms(3,1)]  N_gtr_0 by auto
    also have "... < a_current_flow state e"
      using invar_forestD[OF assms(6), of e] 1
      by(auto simp add: new_gamma_changes)
    finally show ?case 
      by(auto simp add: new_gamma_changes) 
  qed
  have invar_integral_upd: "invar_integral (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
    by (simp add: assms(1,3,7) invar_integral_gamma_upd)
  have invar_isOptflow_upd:"invar_isOptflow (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
    by (simp add: assms(8) invar_isOpt_gamma_change)
  show invars_after_maintain_forest:
          "aux_invar  (maintain_forest (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
          "invar_gamma  (maintain_forest (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
          "implementation_invar  (maintain_forest (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
          "send_flow_entryF (maintain_forest (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
          "invar_integral  (maintain_forest (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
          "invar_isOptflow  (maintain_forest (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
          "invarA_2 (8 * real N * new_\<gamma> state) (2 * new_\<gamma> state)
               (local.maintain_forest (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
    using new_gamma_0
    apply(auto intro!: maintain_forest_invar_aux_pres maintain_forest_invar_gamma_pres
                       maintain_forest_implementation_invar_pres send_flow_entryF
                       maintain_forest_invar_integral_pres
                       flow_optimatlity_pres[OF _ _  invar_A1 _ _ refl]
                       invarA2_pres[OF _ _ invar_A1 invarA_2]
               simp add: maintain_forest_dom aux_invar_gamma_upd 
                         implementation_invar_gamma_upd invar_gamma_gamma_upd
                         maintain_forest_entry invar_A1 invarA_2 invar_integral_upd
                         invar_isOptflow_upd )
    done
  have Phi_increase_bound: "\<Phi> (local.maintain_forest (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))
                  \<le> \<Phi> (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>) + int N"
    by(auto intro!: Phi_increase_below_N 
          simp add:  aux_invar_gamma_upd invar_gamma_gamma_upd implementation_invar_gamma_upd)
  have new_phi_nonneg: "0 \<le> \<Phi> (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
    by(auto intro: Phi_nonneg simp add:  invar_gamma_gamma_upd)
  have new_phi_less_N: "\<Phi> (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>) \<le> N" 
    by (simp add: Phi_init(1) assms(1,2,3,4,5))
  have Phi_after_forest_leq_2N:
       "real_of_int (\<Phi> (local.maintain_forest (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))) \<le> 2*N"
      using Phi_increase_bound new_phi_less_N by simp
  show invar_above_6Ngamma:
     "invar_above_6Ngamma (maintain_forest (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
  proof(rule invar_above_6NgammaI, goal_cases)
    case (1 e)
    have "(2 * real N - real_of_int (\<Phi> (local.maintain_forest (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)))) *
                 new_\<gamma> state \<ge> 0" 
      using  Phi_after_forest_leq_2N  new_gamma_0 by auto
    thus ?case 
      using send_flow_entryFD[OF invars_after_maintain_forest(4) 1]
      by(auto simp add: gamma_pres[OF aux_invar_gamma_upd implementation_invar_gamma_upd])
  qed
  show send_flow_dom: "send_flow_dom (local.maintain_forest (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
    by(auto intro!: send_flow_termination
          simp add: invars_after_maintain_forest invar_above_6Ngamma)
  have invar_above_6Ngamma_finally:
     "invar_above_6Ngamma (send_flow (local.maintain_forest (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)))"
    by(auto intro!: send_flow_invars_pres(6)
          simp add: send_flow_dom invars_after_maintain_forest invar_above_6Ngamma)
  have invar_forest_after_send_flow:
      "invar_forest (send_flow (local.maintain_forest (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)))"
    using Phi_after_forest_leq_2N 
    by(auto intro!: send_flow_invar_forest
          simp add: invars_after_maintain_forest invar_above_6Ngamma )
  show  "aux_invar  (orlins_one_step state)"
         "invar_gamma  (orlins_one_step state)"
          "implementation_invar (orlins_one_step state)"
          "return (orlins_one_step state) = notyetterm
           \<Longrightarrow> orlins_entry (orlins_one_step state)"
          "invar_forest (orlins_one_step state)"
          "invar_integral (orlins_one_step state)"  
          "invar_isOptflow (orlins_one_step state)"
           "return (orlins_one_step state) = notyetterm 
           \<Longrightarrow> invar_non_zero_b (orlins_one_step state)"
           "return (orlins_one_step state) = success 
                \<Longrightarrow> is_Opt \<b> (a_current_flow (orlins_one_step state))"
            "current_\<gamma> (orlins_one_step state) = new_\<gamma> state"
        using Phi_increase_bound new_phi_less_N
        by(auto intro!: send_flow_invar_aux_pres
                        send_flow_invar_gamma_pres
                        send_flow_implementation_invar_pres
                        orlins_entry_after_send_flow
                        send_flow_invar_integral_pres
                        send_flow_invar_isOpt_pres
                        remaining_balance_after_send_flow
                        send_flow_correctness
              simp add: orlins_one_step_def send_flow_dom invars_after_maintain_forest
                        invar_above_6Ngamma invar_forest_after_send_flow
                        send_flow_changes_current_\<gamma> gamma_pres implementation_invar_gamma_upd
                        aux_invar_gamma_upd) 
     show "return (orlins_one_step state) = failure \<Longrightarrow> \<nexists>f. f is \<b> flow" 
      using Phi_increase_bound new_phi_less_N send_flow_completeness
      by(intro send_flow_completeness)
        (auto simp add: orlins_one_step_def send_flow_dom invars_after_maintain_forest
                        invar_above_6Ngamma invar_forest_after_send_flow)
    show "x \<in> \<V> \<Longrightarrow> \<bar>a_balance state x\<bar> \<le> 2 * new_\<gamma> state" for x 
      using assms(1,2,3,5) new_gamma_is(6) orlins_entryD 
      by (force elim: invar_gammaE)
    show "orlins_dom state \<Longrightarrow> return state = notyetterm \<Longrightarrow>
            orlins state = orlins (orlins_upd_impl state)"
      by(subst orlins.psimps)
        (auto intro!: cong[OF refl, of _ _ orlins] send_flow_dom_impl_cong[symmetric]
                      maintain_forest_dom_impl_same
            simp add: send_flow_dom maintain_forest_dom
                      orlins_upd_impl_def Let_def orlins_upd_impl_check_def)
    show "send_flow_impl (maintain_forest_impl (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)) =
            send_flow (maintain_forest (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
      by(auto intro!: send_flow_dom_impl_cong maintain_forest_dom_impl_same
              simp add: send_flow_dom maintain_forest_dom)
  qed

lemma invars_pres_orlins_one_step_check:
  assumes "aux_invar state"
          "invar_gamma state"
          "implementation_invar state"
          "invar_non_zero_b state"
          "orlins_entry state"
          "invar_forest state"
          "invar_integral state"
          "invar_isOptflow state"
    shows "aux_invar  (orlins_one_step_check state)"
          "invar_gamma  (orlins_one_step_check state)"
          "implementation_invar (orlins_one_step_check state)"
          "return (orlins_one_step_check state) = notyetterm
            \<Longrightarrow> orlins_entry (orlins_one_step_check state)"
          "invar_forest (orlins_one_step_check state)"
          "invar_integral (orlins_one_step_check state)"  
          "invar_isOptflow (orlins_one_step_check state)"
          "return (orlins_one_step_check state) = notyetterm \<Longrightarrow>
           invar_non_zero_b (orlins_one_step_check state)" 
           "return (orlins_one_step_check state) = notyetterm \<Longrightarrow>
           invar_non_zero_b (orlins_one_step_check state)"
   by(auto simp add: orlins_one_step_check_def assms
           intro!: invars_pres_orlins_one_step)

lemma aux_invar_pres_orlins_one_step:
  assumes "aux_invar state" "invar_gamma state" "invar_non_zero_b state"
          "implementation_invar state"
          "orlins_entry state"
          "invar_forest state"
          "invar_integral state"
          "invar_isOptflow state"
  shows "aux_invar (orlins_one_step state)"
  by (simp add: assms(1,2,3,4,5,6,7,8) invars_pres_orlins_one_step(1))

lemma invar_gamma_pres_orlins_one_step:
  assumes "aux_invar state" "invar_gamma state" "invar_non_zero_b state"
          "implementation_invar state"
          "orlins_entry state"
          "invar_forest state"
          "invar_integral state"
          "invar_isOptflow state"
  shows "invar_gamma (orlins_one_step state)"
  using assms(1,2,3,4,5,6,7,8) invars_pres_orlins_one_step(2) by blast

lemma balance_less_new_gamma:
  assumes "aux_invar state"
          "invar_gamma state"
          "implementation_invar state"
          "invar_non_zero_b state"
          "orlins_entry state"
          "x \<in> \<V>"
    shows "\<bar>a_balance state x \<bar>\<le> 2*new_\<gamma> state"
 using assms(1,2,3,5,6,4) new_gamma_is(6) orlins_entryD 
 by (force elim: invar_gammaE)

lemma new_gamma_below_half_gamma: "new_\<gamma> state \<le> current_\<gamma> state / 2"
  by(auto simp add: new_\<gamma>_def Let_def)

lemma invar_forest_pres_orlins_one_step_check:
  assumes "aux_invar state"
          "invar_gamma state"
          "implementation_invar state"
          "invar_non_zero_b state"
          "orlins_entry state"
          "invar_forest state"
          "invar_integral state"
          "invar_isOptflow state"
        shows   "invar_forest (orlins_one_step_check state)"
  by (simp add: assms(1,2,3,4,5,6,7,8) invars_pres_orlins_one_step(5)
      orlins_one_step_check_def)

lemma invar_forest_pres_orlins_one_step:
  assumes "aux_invar state"
          "invar_gamma state"
          "implementation_invar state"
          "invar_non_zero_b state"
          "orlins_entry state"
          "invar_forest state"
          "invar_integral state"
          "invar_isOptflow state"
  shows   "invar_forest (orlins_one_step state)"
  by (simp add: assms(1,2,3,4,5,6,7,8) invars_pres_orlins_one_step(5))

lemma invar_integral_pres_orlins_one_step_check:
  assumes "aux_invar state"
          "invar_gamma state"
          "implementation_invar state"
          "invar_non_zero_b state"
          "orlins_entry state"
          "invar_forest state"
          "invar_integral state"
          "invar_isOptflow state"       
  shows   "invar_integral (orlins_one_step_check state)"
  by (simp add: assms(1,2,3,4,5,6,7,8) invars_pres_orlins_one_step(6)
      orlins_one_step_check_def)

lemma invar_integral_pres_orlins_one_step:
  assumes "aux_invar state"
          "invar_gamma state"
          "implementation_invar state"
          "invar_non_zero_b state"
          "orlins_entry state"
          "invar_forest state"
          "invar_integral state"
          "invar_isOptflow state"
  shows   "invar_integral (orlins_one_step state)"
  by (simp add: assms(1,2,3,4,5,6,7,8) invars_pres_orlins_one_step(6))

lemma orlins_entry_ofter_one_step:
  assumes "aux_invar state"
          "invar_gamma state"
          "implementation_invar state"
          "invar_non_zero_b state"
          "orlins_entry state"
          "invar_forest state"
          "invar_integral state"
          "invar_isOptflow state"
        "return (orlins_one_step state) = notyetterm"
  shows "orlins_entry (orlins_one_step state)"
  using assms(1,2,3,4,5,6,7,8,9) invars_pres_orlins_one_step(4) by blast

lemma 
  assumes "aux_invar state"
          "invar_gamma state"
          "implementation_invar state"
          "invar_non_zero_b state"
          "orlins_entry state"
          "invar_forest state"
          "invar_integral state"
          "invar_isOptflow state"
  shows optimality_pres_orlins_one_step_check:
          "invar_isOptflow (orlins_one_step_check state)"
          "return (orlins_one_step_check state) = success \<Longrightarrow>
           return state = notyetterm \<Longrightarrow>
           is_Opt \<b> (a_current_flow (orlins_one_step_check state))"
          "return (orlins_one_step_check state) = failure \<Longrightarrow> 
           return state = notyetterm \<Longrightarrow>
           \<nexists> f. f is \<b> flow"
    and optimality_pres_orlins_one_step:
         "invar_isOptflow (orlins_one_step state)"
          "return (orlins_one_step state) = success \<Longrightarrow>
           is_Opt \<b> (a_current_flow (orlins_one_step state))"
          "return (orlins_one_step state) = failure \<Longrightarrow>
           \<nexists> f. f is \<b> flow"
  using invars_pres_orlins_one_step(9)[OF assms]
  by(auto simp add: assms(1,2,3,4,5,6,7,8) invars_pres_orlins_one_step(7,8)
      orlins_one_step_check_def)
  
lemma some_balance_after_one_step:
  assumes "return (orlins_one_step state) = notyetterm" "aux_invar state" "invar_gamma state"
          "invar_non_zero_b state"
          "implementation_invar state"
          "orlins_entry state"
          "invar_forest state"
          "invar_integral state"
          "invar_isOptflow state"
 shows    "invar_non_zero_b (orlins_one_step state)" 
  using assms
  by(auto intro!: invars_pres_orlins_one_step(11))

subsection \<open>Inductive Proofs\<close>

lemma no_important_no_merge_gamma:
  assumes "\<And> k' state'. k' \<le> k \<Longrightarrow> state' = (compow k' orlins_one_step_check state) \<Longrightarrow>
                \<nexists> v. important state' v" 
          "(\<And> k' state'. k' \<le> k \<Longrightarrow> state' = (compow k' orlins_one_step_check state) \<Longrightarrow>
                          card (comps \<V> (to_graph (\<FF> state'))) = card (comps \<V> (to_graph (\<FF> state))))"
          "state' = (compow k orlins_one_step_check state)"
          "return state' =notyetterm"
          "aux_invar state"
          "invar_gamma state"
          "implementation_invar state"
          "invar_non_zero_b state"
          "orlins_entry state"
          "invar_forest state"
          "invar_integral state"
          "invar_isOptflow state"
    shows "current_\<gamma> state' = (1/2)^k * current_\<gamma> state \<and> 
            state'\<lparr> current_\<gamma> := current_\<gamma> state\<rparr> = state"
  using assms
proof(induction k arbitrary: state)
  case 0
  have "current_\<gamma> state' = (1 / 2) ^ 0 * current_\<gamma> state"
    by(subst 0(3), simp)
  moreover have "state'\<lparr>current_\<gamma> := current_\<gamma> state\<rparr> = state"
    by(subst 0(3),simp)
  ultimately show ?case by simp
next
  case (Suc k)
     have returnValue:"return state = notyetterm"
      apply(rule ccontr)
      using succ_fail_not_changes[of state "Suc k"] Suc
      by (metis (full_types) return.exhaust)     
    hence send_flow_unfold:"(orlins_one_step_check^^Suc k') state = 
           (orlins_one_step_check^^ k') (orlins_one_step state)" for k'
      apply(subst funpow_Suc_right, simp)
      unfolding orlins_one_step_check_def using returnValue 
      by(auto split: if_split)
    hence send_flow_unfold':"(orlins_one_step_check^^Suc k') state = 
           (orlins_one_step_check^^ k') (orlins_one_step_check state)" for k'
      by(subst funpow_Suc_right, simp)      
    have returnValue':"return (orlins_one_step_check state) = notyetterm"
      apply(rule ccontr)
       using succ_fail_not_changes[of "orlins_one_step_check state" "k"] send_flow_unfold'[of k]
       Suc(4-)
       by (metis (full_types) orlins_one_step_check_def return.exhaust)
     hence returnValue'':"return (orlins_one_step state) = notyetterm"
       unfolding orlins_one_step_check_def 
       by (simp add: returnValue)
     have card_Same:"card (comps \<V> (to_graph (\<FF> (orlins_one_step state)))) =
          card (comps \<V> (to_graph (\<FF> state)))" 
      apply(rule Suc(3)[of 1], simp+)
      unfolding orlins_one_step_check_def orlins_one_step_def Let_def
      using returnValue by simp
    have balance_oneStep:"invar_non_zero_b (orlins_one_step state)"
       apply(rule some_balance_after_one_step)
       using  Suc(4-) returnValue'' by auto      
   have afterIH:"current_\<gamma> state' = (1 / 2) ^ k * current_\<gamma> ((orlins_one_step state)) \<and>
          state'\<lparr>current_\<gamma> := current_\<gamma> (orlins_one_step state)\<rparr> = (orlins_one_step state)"
      apply(rule  Suc(1))
      using Suc(2) send_flow_unfold apply fastforce 
      using card_Same  send_flow_unfold[of k] Suc balance_oneStep sym[OF send_flow_unfold]
      by (auto intro!: Suc(3)[of "Suc _"]  invars_pres_orlins_one_step
            simp add: returnValue'')
  have new_gamma:"new_\<gamma> state \<noteq> current_\<gamma> state / 2 \<Longrightarrow> False"
  proof(goal_cases)
   case 1
   hence 11:"\<forall> e \<in> to_set (actives state). a_current_flow state e = 0"   
     using 1 unfolding new_gamma_is(1)[OF Suc.prems(7,5)] 
     by presburger
   hence alt_11: "(Max { \<bar> a_balance state v\<bar> | v. v \<in> \<V>}) = new_\<gamma> state"
     using 1 by(simp add: new_gamma_is(1)[OF Suc.prems(7,5)])
   obtain v where v_prop:"(\<bar> a_balance state v\<bar> =
                    Max { \<bar> a_balance state v\<bar> | v. v \<in> \<V>})" "v \<in> \<V>"
     using obtain_Max[of \<V> "\<lambda> v. \<bar> a_balance state v\<bar>"]  V_non_empt \<V>_finite by blast
   have "\<bar> a_balance state v\<bar> > 0"
     apply(rule bexE[OF Suc(9)[simplified invar_non_zero_b_def, simplified]])
     unfolding v_prop
     by(subst Max_gr_iff[of "{\<bar>a_balance state v\<bar> |v. v \<in> \<V>}" 0])
       ( auto simp add: \<V>_finite V_non_empt )
   hence "v \<in> \<V> \<and> (1 - \<epsilon>) * new_\<gamma> state < \<bar>a_balance state v\<bar>" 
     using v_prop(2)  \<epsilon>_axiom(1) 
     by (force simp add:  sym[OF alt_11] sym[OF v_prop(1)])
   hence "\<exists> v. important state v"
     by(auto simp add: important_def)
   then show ?case 
     using Suc(2)[of 0, OF _ refl] by simp
  qed

  hence gamma_halved:"current_\<gamma> ((orlins_one_step state)) = (1/2) * current_\<gamma> state"
    by(auto simp add: invars_pres_orlins_one_step(13) Suc.prems)
   
  have not_call_cond_maintain_forest: "maintain_forest_call_cond (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>) \<Longrightarrow> False"
  proof(goal_cases)
    case 1
    have "card (comps \<V> (to_graph (\<FF> (maintain_forest (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))))) <
              card (comps \<V> (to_graph (\<FF> (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))))"
      using Suc 1
      by(fastforce intro!: card_strict_decrease[of "state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>"] 
                      termination_of_maintain_forest aux_invar_gamma
                      implementation_invar_gamm_upd)
    moreover have "card (comps \<V> (to_graph (\<FF> (maintain_forest (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))))) = 
                   card (comps \<V> (to_graph (\<FF> (send_flow (maintain_forest (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))))))"
          using Suc
          by(subst send_flow_changes_\<FF>)
            (auto intro!: send_flow_termination invars_pres_orlins_one_step(14-))
        ultimately have "card (comps \<V> (to_graph (\<FF> (orlins_one_step_check state)))) < 
                             card (comps \<V> (to_graph (\<FF> state)))"
          using returnValue 
          by (simp add: orlins_one_step_check_def orlins_one_step_def)
    thus False
      using Suc(3)[of 1, OF _ refl] by simp
  qed
  hence maintain_forest_no_change:"maintain_forest (state  \<lparr>current_\<gamma> := new_\<gamma> state \<rparr>) = state \<lparr>current_\<gamma> := new_\<gamma> state \<rparr>"
    by (cases rule: maintain_forest_cases)(auto simp add: maintain_forest_simps(2))
  have same_state:"(orlins_one_step state) \<lparr> current_\<gamma> := current_\<gamma> state \<rparr> = state"
    apply(unfold orlins_one_step_def Let_def)
    apply(subst maintain_forest_no_change)
    apply(subst send_flow_nothing_done)
    using Suc.prems(1)[of 0, OF _ refl] returnValue
    by(auto intro: invar_non_zero_bE[OF  Suc.prems(8)] dest: importantI
           simp add: send_flow_nothing_done implementation_invar_gamm_upd Suc.prems(5-8) gamma_upd_aux_invar_pres)   
  show ?case 
      apply rule
      subgoal
      apply(subst conjunct1[OF afterIH])
        using gamma_halved by simp
      subgoal
        apply(rule trans[of _ "(state'\<lparr>current_\<gamma> := current_\<gamma> (orlins_one_step state)\<rparr>)\<lparr>current_\<gamma> := current_\<gamma> state\<rparr>"], simp)
        using conjunct2[OF afterIH] same_state by simp
      done
  qed

lemma invar_aux_to_invar_aux1: "aux_invar state \<Longrightarrow> invar_aux1 state"
  by(auto simp add: aux_invar_def)
 
lemma forest_increase_orlins_one_step:
  assumes "aux_invar state" "invar_gamma state" "invar_non_zero_b state"
          "implementation_invar state"
          "orlins_entry state"
          "invar_forest state"
          "invar_integral state"
          "invar_isOptflow state"
  shows" to_graph (\<FF> (orlins_one_step state)) \<supseteq> to_graph (\<FF> state)"
  apply(unfold orlins_one_step_def Let_def) 
  apply(rule ord_eq_le_trans[of _ "to_graph (\<FF> (state \<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"])
  apply simp
  apply(rule order.trans, rule forest_increase)
  by (auto simp add: send_flow_changes_\<FF>
          assms invars_after_maintain_forest(10,11) implementation_invar_gamm_upd
          aux_invar_gamma)

lemma forest_increase_orlins_one_step_check:
  assumes "aux_invar state" "invar_gamma state" "invar_non_zero_b state"
          "implementation_invar state"
          "orlins_entry state"
          "invar_forest state"
          "invar_integral state"
          "invar_isOptflow state"
        shows" to_graph (\<FF> (orlins_one_step_check state)) \<supseteq> to_graph (\<FF> state)"
  using assms forest_increase_orlins_one_step 
  by(auto simp add: orlins_one_step_check_def)

lemma card_decrease_orlins_one_step:
  assumes "aux_invar state" "invar_gamma state" "invar_non_zero_b state"
          "implementation_invar state"
          "orlins_entry state"
          "invar_forest state"
          "invar_integral state"
          "invar_isOptflow state"
  shows"card (comps \<V> (to_graph (\<FF> (orlins_one_step state)))) \<le>
            card (comps \<V> (to_graph (\<FF> state)))"
  using assms(1)
  by(auto intro: number_of_comps_anti_mono[OF forest_increase_orlins_one_step[OF assms]] 
           elim: aux_invarE invar_aux5E)

lemma orlins_some_steps_forest_increase:
  assumes "state' = (orlins_one_step_check ^^ k) state"
              "aux_invar state" "invar_gamma state" "invar_non_zero_b  state"
               "implementation_invar state"
              "orlins_entry state"
              "invar_forest state"
              "invar_integral state"
             "invar_isOptflow state"
  shows " to_graph (\<FF> state') \<supseteq> to_graph (\<FF> state)"
  using assms
proof(induction k arbitrary: state state')
  case (Suc k)
  have unfold:"(orlins_one_step_check ^^ Suc k) state = 
        (orlins_one_step_check ^^ k) (orlins_one_step_check state)"
    by (metis (mono_tags, lifting) funpow_simps_right(2) o_apply)
  show ?case 
  proof(cases "return state = notyetterm")
    case True
    hence one_step:"(orlins_one_step_check state)  = orlins_one_step state"
      by(auto simp add: orlins_one_step_check_def)
    show ?thesis
    proof(cases "return (orlins_one_step state) = notyetterm")
      case True
      hence True': "return (orlins_one_step_check state) = notyetterm"
        using one_step by(auto simp add: orlins_one_step_check_def) 
      have balance_after_one_step:"invar_non_zero_b (orlins_one_step state) "
        using True Suc by (intro some_balance_after_one_step)
      show ?thesis 
      apply(subst Suc(2))
      apply(subst unfold)
        apply(rule order.trans[of _ "to_graph (\<FF> ((orlins_one_step_check  state)))", OF _ Suc(1)]) 
        apply(rule  forest_increase_orlins_one_step_check)
        by(auto simp add: Suc(3-) True True'
                  intro!:  forest_increase_orlins_one_step_check invars_pres_orlins_one_step_check)  
    next
      case False
      hence False': "return (orlins_one_step_check state) \<noteq> notyetterm"
        using one_step by argo
      show ?thesis 
        apply(subst  Suc(2), unfold  unfold notyetterm_no_change[OF False'])
        by(intro forest_increase_orlins_one_step_check)(auto simp add: Suc(2-))
    qed
  next
    case False
    hence one_step_no_change:"(orlins_one_step_check state) = state" 
      using return.exhaust by (auto simp add: orlins_one_step_check_def)
    show ?thesis 
      apply(subst Suc(2))
      apply(subst unfold)
      apply(rule order.trans[of _ "to_graph (\<FF> ((orlins_one_step_check  state)))", rotated])
      subgoal
        by(intro Suc(1))(auto simp add: one_step_no_change Suc)
      subgoal
        using False return.exhaust 
        by (auto simp add: orlins_one_step_check_def[of state])
      done
  qed
qed simp

lemma orlins_some_steps_card_decrease:
  assumes "state' = (orlins_one_step_check ^^ k) state"
         "aux_invar state" "invar_gamma state" "invar_non_zero_b  state"
          "implementation_invar state"
          "orlins_entry state"
          "invar_forest state"
          "invar_integral state"
          "invar_isOptflow state"
   shows "card (comps \<V> (to_graph (\<FF> state'))) \<le> card (comps \<V> (to_graph (\<FF> state)))"
  using assms(2) 
  by(auto intro: number_of_comps_anti_mono[OF orlins_some_steps_forest_increase[OF assms]] 
           elim: aux_invarE invar_aux5E)

lemma orlins_compow_aux_invar_pres:
  assumes "aux_invar state"
          "invar_gamma state"
          "invar_non_zero_b state"
          "implementation_invar state"
          "orlins_entry state"
          "invar_forest state"
          "invar_integral state"
          "invar_isOptflow state"
    shows "aux_invar ((orlins_one_step_check ^^ k) state)"
  using assms
proof(induction k arbitrary: state)
  case (Suc k)
  show ?case
  proof(subst funpow_Suc_right, simp, subst orlins_one_step_check_def,
         cases "return state", goal_cases)
    case 3
    then show ?case 
    proof(cases "return (orlins_one_step state)", goal_cases)
      case 1
      thus ?case
         by(auto intro!: invars_pres_orlins_one_step 
            simp add: Suc(2-) notyetterm_no_change[of "orlins_one_step state" k])
     next
      case 2
      thus ?case
         by(auto intro: invars_pres_orlins_one_step simp add: Suc(2-) notyetterm_no_change)
     next
       case 3
       thus ?case
         by(auto intro!:  Suc(1) invars_pres_orlins_one_step simp add: Suc(2-))
     qed
  qed (simp add: Suc)+
qed simp

lemma orlins_compow_invar_gamma_pres:
  assumes "aux_invar state"
          "invar_gamma state"
          "invar_non_zero_b state"
          "implementation_invar state"
          "orlins_entry state"
          "invar_forest state"
          "invar_integral state"
          "invar_isOptflow state"
    shows "invar_gamma ((orlins_one_step_check ^^ k) state)"
  using assms
proof(induction k arbitrary: state)
  case (Suc k)
  show ?case
  proof(subst funpow_Suc_right, simp, subst orlins_one_step_check_def,
         cases "return state", goal_cases)
    case 3
    then show ?case 
    proof(cases "return (orlins_one_step state)", goal_cases)
      case 1
      thus ?case
         by(auto intro!: invars_pres_orlins_one_step 
            simp add: Suc(2-) notyetterm_no_change[of "orlins_one_step state" k])
     next
      case 2
      thus ?case
         by(auto intro: invars_pres_orlins_one_step simp add: Suc(2-) notyetterm_no_change)
     next
       case 3
       thus ?case
         by(auto intro!:  Suc(1) invars_pres_orlins_one_step simp add: Suc(2-))
     qed
  qed (simp add: Suc)+
qed simp

lemma orlins_compow_implementation_invar_pres:
  assumes "aux_invar state"
          "invar_gamma state"
          "invar_non_zero_b state"
          "implementation_invar state"
          "orlins_entry state"
          "invar_forest state"
          "invar_integral state"
          "invar_isOptflow state"
    shows "implementation_invar ((orlins_one_step_check ^^ k) state)"
  using assms
proof(induction k arbitrary: state)
  case (Suc k)
  show ?case
  proof(subst funpow_Suc_right, simp, subst orlins_one_step_check_def,
         cases "return state", goal_cases)
    case 3
    then show ?case 
    proof(cases "return (orlins_one_step state)", goal_cases)
      case 1
      thus ?case
         by(auto intro!: invars_pres_orlins_one_step 
            simp add: Suc(2-) notyetterm_no_change[of "orlins_one_step state" k])
     next
      case 2
      thus ?case
         by(auto intro: invars_pres_orlins_one_step simp add: Suc(2-) notyetterm_no_change)
     next
       case 3
       thus ?case
         by(auto intro!:  Suc(1) invars_pres_orlins_one_step simp add: Suc(2-))
     qed
  qed (simp add: Suc)+
qed simp

lemma orlins_compow_invar_integral_pres:
  assumes "aux_invar state"
          "invar_gamma state"
          "invar_non_zero_b state"
          "implementation_invar state"
          "orlins_entry state"
          "invar_forest state"
          "invar_integral state"
          "invar_isOptflow state"
    shows "invar_integral ((orlins_one_step_check ^^ k) state)"
  using assms
proof(induction k arbitrary: state)
  case (Suc k)
  show ?case
  proof(subst funpow_Suc_right, simp, subst orlins_one_step_check_def,
         cases "return state", goal_cases)
    case 3
    then show ?case 
    proof(cases "return (orlins_one_step state)", goal_cases)
      case 1
      thus ?case
         by(auto intro!: invars_pres_orlins_one_step 
            simp add: Suc(2-) notyetterm_no_change[of "orlins_one_step state" k])
     next
      case 2
      thus ?case
         by(auto intro: invars_pres_orlins_one_step simp add: Suc(2-) notyetterm_no_change)
     next
       case 3
       thus ?case
         by(auto intro!:  Suc(1) invars_pres_orlins_one_step simp add: Suc(2-))
     qed
  qed (simp add: Suc)+
qed simp

lemma orlins_compow_invar_isOptflow_pres:
  assumes "aux_invar state"
          "invar_gamma state"
          "invar_non_zero_b state"
          "implementation_invar state"
          "orlins_entry state"
          "invar_forest state"
          "invar_integral state"
          "invar_isOptflow state"
    shows "invar_isOptflow ((orlins_one_step_check ^^ k) state)"
  using assms
proof(induction k arbitrary: state)
  case (Suc k)
  show ?case
  proof(subst funpow_Suc_right, simp, subst orlins_one_step_check_def,
         cases "return state", goal_cases)
    case 3
    then show ?case 
    proof(cases "return (orlins_one_step state)", goal_cases)
      case 1
      thus ?case
         by(auto intro!: invars_pres_orlins_one_step 
            simp add: Suc(2-) notyetterm_no_change[of "orlins_one_step state" k])
     next
      case 2
      thus ?case
         by(auto intro: invars_pres_orlins_one_step simp add: Suc(2-) notyetterm_no_change)
     next
       case 3
       thus ?case
         by(auto intro!:  Suc(1) invars_pres_orlins_one_step simp add: Suc(2-))
     qed
  qed (simp add: Suc)+
qed simp 

lemma orlins_compow_invar_forest_pres:
  assumes "aux_invar state"
          "invar_gamma state"
          "invar_non_zero_b state"
          "implementation_invar state"
          "orlins_entry state"
          "invar_forest state"
          "invar_integral state"
          "invar_isOptflow state"
    shows "invar_forest ((orlins_one_step_check ^^ k) state)"
  using assms
proof(induction k arbitrary: state)
  case (Suc k)
  show ?case
  proof(subst funpow_Suc_right, simp, subst orlins_one_step_check_def,
         cases "return state", goal_cases)
    case 3
    then show ?case 
    proof(cases "return (orlins_one_step state)", goal_cases)
      case 1
      thus ?case
         by(auto intro!: invars_pres_orlins_one_step 
            simp add: Suc(2-) notyetterm_no_change[of "orlins_one_step state" k])
     next
      case 2
      thus ?case
         by(auto intro: invars_pres_orlins_one_step simp add: Suc(2-) notyetterm_no_change)
     next
       case 3
       thus ?case
         by(auto intro!:  Suc(1) invars_pres_orlins_one_step simp add: Suc(2-))
     qed
  qed (simp add: Suc)+
qed simp 

lemma
  assumes "return ((compow k orlins_one_step_check) state) = notyetterm" 
          "aux_invar state" "invar_gamma state"
          "invar_non_zero_b state"
          "implementation_invar state"
          "orlins_entry state"
          "invar_forest state"
          "invar_integral state"
          "invar_isOptflow state"
shows    some_balance_after_k_steps:
     "invar_non_zero_b ((compow k orlins_one_step_check) state) "
and  orlins_entry_after_k_steps:
 "orlins_entry ((compow k orlins_one_step_check) state) "
proof-
  have   "invar_non_zero_b ((compow k orlins_one_step_check) state) \<and>
          orlins_entry ((compow k orlins_one_step_check) state) "
  using assms
proof(induction k arbitrary: state)
  case 0
  then show ?case by simp
next
  case (Suc k)
  show ?case 
  proof( cases "return ((orlins_one_step_check ^^ k) state)", goal_cases)
    case 1
    then show ?thesis 
      using Suc(2-) 
      by(unfold orlins_one_step_check_def funpow.simps(2)) simp
  next
    case failure
    then show ?thesis 
      using Suc(2-) 
      by(unfold orlins_one_step_check_def funpow.simps(2)) simp
  next
    case notyetterm
    show ?thesis 
      using Suc.prems(1)
      by(auto intro!: invars_pres_orlins_one_step_check orlins_compow_aux_invar_pres
                      orlins_compow_invar_gamma_pres orlins_compow_implementation_invar_pres
                      conjunct1[OF Suc.IH] conjunct2[OF Suc.IH] orlins_compow_invar_integral_pres
                      orlins_compow_invar_isOptflow_pres orlins_compow_invar_forest_pres
            simp add: Suc(2-) notyetterm funpow.simps(2) o_apply)
  qed
qed
  thus "invar_non_zero_b ((orlins_one_step_check ^^ k) state)"
       " orlins_entry ((orlins_one_step_check ^^ k) state)"
    by auto
qed

lemma orlins_entry_after_compow:
  assumes 
        "aux_invar state" "invar_gamma state" "invar_non_zero_b state"
        "return ((compow k orlins_one_step_check) state) = notyetterm"
        "orlins_entry state"
         "implementation_invar state"
          "invar_forest state"
          "invar_integral state"
          "invar_isOptflow state"
   shows "orlins_entry ((compow k orlins_one_step_check) state)"
  using assms by(auto intro:  orlins_entry_after_k_steps)

lemma important_or_merge_or_termination:
  assumes "invar_gamma state"
          "aux_invar state"
          "invar_non_zero_b state"
          "invar_integral state"
          "implementation_invar state"
          "orlins_entry state"
          "invar_forest state"
          "invar_isOptflow state"
          "\<k> =  nat (\<lceil>log 2 N \<rceil> + 3)"
  shows   "\<exists> k \<le> \<k>+1. return ((compow k orlins_one_step_check) state) \<noteq> notyetterm \<or>
                    (\<exists> v. important (compow k (orlins_one_step_check) state) v \<and>
                          return ((compow k orlins_one_step_check) state) = notyetterm) \<or>
                    (card (comps \<V> (to_graph (\<FF> (compow k (orlins_one_step_check) state)))) 
                          < card (comps \<V> (to_graph (\<FF> state))) \<and>
                      return ((compow k orlins_one_step_check) state) = notyetterm)"
proof-
  have gamma_0: "current_\<gamma> state > 0" 
    using assms(1) invar_gamma_def by auto
  have isuflow: "isuflow (a_current_flow state)"
    using assms(8)
    by(auto elim!: invar_isOptflowE is_OptE isbflowE)
  have last_chance_merge:
       " (\<And> k. k \<le> \<k>  \<Longrightarrow> return (compow k (orlins_one_step_check) state) = notyetterm) \<Longrightarrow>
         (\<And> k. k \<le> \<k>  \<Longrightarrow> (\<nexists> v. important (compow k (orlins_one_step_check) state) v)) \<Longrightarrow>
         (\<And> k. k \<le> \<k>  \<Longrightarrow> \<not> card (comps \<V> (to_graph (\<FF> (compow k (orlins_one_step_check) state)))) 
                                   < card (comps \<V> (to_graph (\<FF> state)))) \<Longrightarrow>
         card (comps \<V> (to_graph (\<FF> ((orlins_one_step_check ^^ (Suc \<k>)) state)))) < 
         card (comps \<V> (to_graph (\<FF> state)))"
  proof(goal_cases)
    case 1 
    note note1= this
    have cards:"k \<le> \<k> \<Longrightarrow>
     card (comps \<V> (to_graph (\<FF> ((orlins_one_step_check ^^ k) state)))) = 
               card (comps \<V> (to_graph (\<FF> state)))" for k   
      using  orlins_some_steps_card_decrease[OF refl assms(2,1,3,5,6,7,4,8), of k]
             1(3)[of k, simplified not_less] by simp
    have gamma_after_k:
         "current_\<gamma> ((orlins_one_step_check ^^ (\<k>)) state) = (1 / 2) ^ (\<k>) * current_\<gamma> state"
         "((orlins_one_step_check ^^ (\<k>)) state)\<lparr>current_\<gamma> := current_\<gamma> state\<rparr> = state"
      using cards  1 assms no_important_no_merge_gamma[of "\<k>" state, OF _ _refl] 
      by auto
    have gamma_after_k_minus1:
         "current_\<gamma> ((orlins_one_step_check ^^ (\<k>-1)) state) = (1 / 2) ^ (\<k>-1) * current_\<gamma> state"
         "(orlins_one_step_check ^^ (\<k>-1)) state\<lparr>current_\<gamma> := current_\<gamma> state\<rparr> = state"
      using cards  1 assms no_important_no_merge_gamma[of "\<k>-1" state, OF _ _refl] 
      by auto
 have new_gamma:"\<forall> e \<in> to_set (actives state). a_current_flow state e = 0 \<Longrightarrow> False"
   proof(goal_cases)
   case 1
   hence 11: "min (current_\<gamma> state / 2) (Max { \<bar> a_balance state v\<bar> | v. v \<in> \<V>}) = new_\<gamma> state"
     using assms new_gamma_is(1) by auto
   obtain v where v_prop:"(\<bar> a_balance state v\<bar> =
                    Max { \<bar> a_balance state v\<bar> | v. v \<in> \<V>})" "v \<in> \<V>"
     using obtain_Max[of \<V> "\<lambda> v. \<bar> a_balance state v\<bar>"]  V_non_empt \<V>_finite by blast
   have "\<bar> a_balance state v\<bar> > 0"
     apply(rule bexE[OF assms(3)[simplified invar_non_zero_b_def, simplified]])
       unfolding v_prop
       apply(subst Max_gr_iff[of "{\<bar>a_balance state v\<bar> |v. v \<in> \<V>}" 0])
       by( auto simp add: \<V>_finite V_non_empt)
     hence "v \<in> \<V> \<and> (1 - \<epsilon>) * new_\<gamma> state < \<bar>a_balance state v\<bar>" 
     unfolding sym[OF 11] sym[OF v_prop(1)]
     using v_prop(2)  \<epsilon>_axiom(1)
     by (smt (verit, best) assms(1) divide_pos_pos invar_gamma_def mult_le_cancel_right1)
   hence "\<exists> v. important state v"
     unfolding important_def  by auto
   then show ?case using note1(2)[of 0] by simp
 qed
  then obtain e where e_prop:"e \<in> to_set (actives state)" "a_current_flow state e > 0"
    using assms(4) assms(2) isuflow  
    by(force elim: invar_aux1E isuflowE aux_invarE)
  have e_flow_gamma:"a_current_flow state e \<ge>  current_\<gamma> state" 
    apply(rule exE[OF bspec[OF assms(4)[simplified invar_integral_def] e_prop(1)]])
    using e_prop(2)
    by (smt (verit, ccfv_SIG) less_one linorder_neq_iff mult_le_cancel_right1 of_nat_0_less_iff 
           of_nat_1 of_nat_less_imp_less split_mult_neg_le)
  have gamma_k:"current_\<gamma> state \<ge> 8 * N * (1 / 2) ^ \<k> * current_\<gamma> state"
    apply(subst mult.commute[of "8 * N * (1 / 2) ^ \<k> "], subst assms(9),
          rule mult_right_le_one_le)
    using assms(1) invar_gamma_def apply force
    by(simp, rule leq_mul_swap[of _ _ "2 ^ nat (\<lceil>log 2 (real N)\<rceil> + 3)"],
       subst mult.assoc, subst cancel_power_denominator, simp, simp,subst sym[OF log_le_cancel_iff[of 2]],
       (subst log_mult log283| simp add: N_gtr_0  | linarith)+)
  have e_gamma_k:"8*N * new_\<gamma> ((orlins_one_step_check ^^ \<k>) state) < a_current_flow state e"
    unfolding new_\<gamma>_def Let_def
    apply(rule order.strict_trans1[of _ "8*N*(current_\<gamma> ((orlins_one_step_check ^^ \<k> ) state) / 2)"])
    subgoal
      by(rule P_of_ifI, rule mult_left_mono, auto)
    subgoal
      apply(subst gamma_after_k)
      using gamma_k e_flow_gamma gamma_0 by linarith
    done
  have same_actives: "actives ((orlins_one_step_check ^^ \<k>) state) = actives state"
    by(rule sym, subst sym[OF gamma_after_k(2)], simp)
  have same_flow: "current_flow ((orlins_one_step_check ^^ \<k>) state) = current_flow state"
    by(rule sym, subst sym[OF gamma_after_k(2)], simp)
  have "\<exists> d. get_from_set
     (\<lambda>e. 8 * real N * new_\<gamma> ((orlins_one_step_check ^^ \<k>) state) < a_current_flow state e)
     (actives state) =
    Some d"
    using e_gamma_k e_prop(1) 
    by (auto intro: set_get(1) simp add: assms(2) from_aux_invar'(17))
  then obtain d where "get_from_set
     (\<lambda>e. 8 * real N * new_\<gamma> ((orlins_one_step_check ^^ \<k>) state) < a_current_flow state e)
     (actives state) =
    Some d" by auto
  hence call_cond:"maintain_forest_call_cond 
     ((orlins_one_step_check ^^ \<k>) state\<lparr>current_\<gamma> := new_\<gamma> ((orlins_one_step_check ^^ \<k>) state)\<rparr>)"
    using same_actives subst same_flow 
    by(intro maintain_forest_call_condI[OF refl refl refl refl, of _ d]) auto
  have return_state:"return ((orlins_one_step_check ^^ \<k>) state) = notyetterm"
    using 1(1)[of \<k>] by simp 
  have send_flow_dom_now: "send_flow_dom
     (local.maintain_forest
       ((orlins_one_step_check ^^ \<k>) state
        \<lparr>current_\<gamma> := new_\<gamma> ((orlins_one_step_check ^^ \<k>) state)\<rparr>))"
    using assms return_state
      by(auto intro!: send_flow_termination maintain_forest_invar_gamma_pres
                      aux_invar_gamma orlins_compow_aux_invar_pres
                      gamma_upd_aux_invar_pres orlins_compow_invar_gamma_pres
                      some_balance_after_k_steps invars_after_maintain_forest
                      orlins_compow_implementation_invar_pres orlins_entry_after_compow
                      orlins_compow_invar_forest_pres orlins_compow_invar_integral_pres
                      orlins_compow_invar_isOptflow_pres implementation_invar_gamm_upd)
  have "card (comps \<V> (to_graph (\<FF> ((orlins_one_step_check ^^ (Suc \<k>)) state)))) < 
        card (comps \<V> (to_graph (\<FF> ((orlins_one_step_check ^^ \<k>) state))))"
    apply(simp, subst orlins_one_step_check_def[of "(orlins_one_step_check ^^ \<k>) state"],simp add: return_state)
    unfolding orlins_one_step_def Let_def send_flow_changes_\<FF>[OF send_flow_dom_now]  
    using assms(9) call_cond
    by(auto intro!: order.strict_trans2[OF card_strict_decrease] 
                    termination_of_maintain_forest' aux_invar_gamma orlins_compow_aux_invar_pres
                    implementation_invar_gamm_upd orlins_compow_implementation_invar_pres
          simp add: assms )
  hence "card (comps \<V> (to_graph (\<FF> ((orlins_one_step_check ^^ (Suc \<k>)) state)))) < 
        card (comps \<V> (to_graph (\<FF> state)))"
    using cards[of \<k>] by simp
  thus ?case by simp
 qed
 thus ?thesis by force
qed
 
lemma no_merge_gamma:
  assumes "state' = (compow k orlins_one_step_check state)"
          "return state' =notyetterm"
          "invar_gamma state"
          "aux_invar state"
          "invar_non_zero_b state"
          "invar_integral state"
          "implementation_invar state"
          "orlins_entry state"
          "invar_forest state"
          "invar_isOptflow state"
    shows "current_\<gamma> state' \<le> (1/2)^k * current_\<gamma> state"
  using assms
proof(induction k arbitrary: state)
  case 0
  have "current_\<gamma> state' = (1 / 2) ^ 0 * current_\<gamma> state"
    by(subst 0(1), simp)
  moreover have "state'\<lparr>current_\<gamma> := current_\<gamma> state,
                        current_flow := current_flow state,
                        balance:= balance state\<rparr> = state"
    by(subst 0(1),simp)
  ultimately show ?case by simp
next
  case (Suc k)
     have returnValue:"return state = notyetterm"
      apply(rule ccontr)
       using succ_fail_not_changes[of state "Suc k"] Suc
       by(auto intro: return.exhaust[of "return state"])   
    hence send_flow_unfold:"(orlins_one_step_check^^Suc k') state = 
           (orlins_one_step_check^^ k') (orlins_one_step state)" for k'
      using returnValue 
      by(subst funpow_Suc_right)(auto split: if_split simp add: orlins_one_step_check_def)
    hence send_flow_unfold':"(orlins_one_step_check^^Suc k') state = 
           (orlins_one_step_check^^ k') (orlins_one_step_check state)" for k'
      by(subst funpow_Suc_right, simp)      
    have returnValue':"return (orlins_one_step_check state) = notyetterm"
      apply(rule ccontr)
       using succ_fail_not_changes[of "orlins_one_step_check state" "k"] send_flow_unfold'[of k]
       Suc(2-)
       by (metis (full_types) orlins_one_step_check_def return.exhaust)
     hence returnValue'':"return (orlins_one_step state) = notyetterm"
       by (simp add: returnValue orlins_one_step_check_def)
    have balance_oneStep:"invar_non_zero_b (orlins_one_step state)"
       using  Suc(4-) returnValue'' by (auto intro: some_balance_after_one_step)    
   have afterIH:"current_\<gamma> state' \<le> (1 / 2) ^ k * current_\<gamma> ((orlins_one_step state))"
     using Suc(2-) send_flow_unfold  send_flow_unfold[of k]
           balance_oneStep sym[OF send_flow_unfold] returnValue''
      by(intro Suc(1))(auto intro: invars_pres_orlins_one_step) 
    have new_gamma:"new_\<gamma> state \<le> current_\<gamma> state / 2"
      unfolding new_\<gamma>_def Let_def by(auto split: if_split)
    hence gamma_halved:"current_\<gamma> ((orlins_one_step state)) \<le> (1/2) * current_\<gamma> state"
      by(auto simp add: invars_pres_orlins_one_step(13) Suc(2-))
    have invar_gamma: "invar_gamma (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
      using Suc.prems(3,4,5,7) gamma_upd_aux_invar_pres by blast
    show ?case 
        using   afterIH  gamma_halved 
        by (smt (verit, ccfv_SIG) One_nat_def ab_semigroup_mult_class.mult_ac(1) mult.commute 
                 ordered_comm_semiring_class.comm_mult_left_mono plus_1_eq_Suc
                 power_Suc0_right power_add zero_le_divide_1_iff zero_le_power)
  qed

lemma invar_gamma_non_zero_balance_set:
  assumes "aux_invar state" and
   bs_def: "bs = {v | v. v \<in> connected_component (to_graph (\<FF> state)) z \<and> a_balance state v \<noteq> 0}" and "z \<in> \<V>"
 shows "bs = {} \<or> (\<exists> x. {x} = bs)"
proof-
  have "x \<in> bs \<Longrightarrow> y \<in> bs \<Longrightarrow> x \<noteq> y \<Longrightarrow> False" for x y
  proof(goal_cases)
    case 1
    hence prps:"x \<in> connected_component (to_graph (\<FF> state)) z" "a_balance state x \<noteq> 0"
          "y \<in> connected_component (to_graph (\<FF> state)) z" "a_balance state y \<noteq> 0" 
      by(auto simp add: bs_def)
    have in_V:"x \<in> \<V>" "y \<in> \<V>"
      using 1 assms by(auto elim!: aux_invarE invar_aux10E)
    hence "representative state x = x" "representative state y = y" 
      using assms(1) prps by(auto elim!: aux_invarE invar_aux12E)
    moreover have "representative state x = representative state y"
      using prps  assms(1) unfolding aux_invar_def invar_aux7_def 
      by (metis in_connected_componentE)
    ultimately show ?case
      using 1 by simp
  qed
  thus ?thesis by fast
qed

definition "M = card \<E>"

lemma M_gtr_zero: "M > 0" 
  by (simp add: E_not_empty M_def card_gt_0_iff finite_E)

abbreviation  "cp \<equiv> connected_component"

lemma one_step_current_gamma_new_gamma:
  assumes "return state =notyetterm" "aux_invar state" "invar_gamma state" 
          "invar_non_zero_b state" "implementation_invar state"
          "orlins_entry state" "invar_forest state" "invar_integral state"
          " invar_isOptflow state"
    shows "current_\<gamma> (orlins_one_step_check state) = new_\<gamma> state"
proof-
  have "send_flow_dom (local.maintain_forest (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
    using assms by(auto intro!: invars_after_maintain_forest(11))
  thus ?thesis
    using assms 
    by(auto simp add: gamma_pres[OF  aux_invar_gamma implementation_invar_gamm_upd] 
                      send_flow_changes_current_\<gamma> orlins_one_step_check_def orlins_one_step_def)
qed

lemma if_important_then_comp_increase_or_termination:
  assumes "invar_gamma state"
          "aux_invar state"
          "invar_non_zero_b state"
          "invar_integral state"
          "important state z"
          "\<l> =  nat (\<lceil> log 2 (4*M*N + (1 - \<epsilon>)) - log 2 \<epsilon>\<rceil>) + 1"
          "invar_forest state"
          "orlins_entry state"
          "invar_isOptflow state"
          "implementation_invar state"
  shows   "\<exists> k \<le> \<l> + 1. return ((compow k orlins_one_step_check) state) \<noteq> notyetterm \<or>
                      connected_component (to_graph (\<FF> (compow k (orlins_one_step_check) state))) z \<supset>
                      connected_component (to_graph (\<FF> state)) z"
proof-
  have gamma_0: "current_\<gamma> state > 0" 
    using assms(1) invar_gamma_def by auto
  have last_chance_merge:
       " (\<And> k. k \<le> \<l>  \<Longrightarrow> return (compow k (orlins_one_step_check) state) = notyetterm) \<Longrightarrow>
         (\<And> k. k \<le> \<l>  \<Longrightarrow> \<not> 
                    connected_component (to_graph (\<FF> (compow k (orlins_one_step_check) state))) z \<supset>
                      connected_component (to_graph (\<FF> state)) z) \<Longrightarrow>
                      connected_component (to_graph (\<FF> (compow (Suc \<l>) (orlins_one_step_check) state))) z \<supset>
                      connected_component (to_graph (\<FF> state)) z"
  proof(goal_cases)
    case 1 
    note note1= this
    have l_0:"\<l> > 0" using assms by simp
    have connected_compt_subs: "connected_component (to_graph (\<FF> ((orlins_one_step_check ^^ \<l>) state))) z \<supseteq> 
                     connected_component (to_graph (\<FF> state)) z"
      using assms by(intro con_comp_subset  orlins_some_steps_forest_increase[OF refl]) auto
     hence same_forst: "connected_component (to_graph (\<FF> ((orlins_one_step_check ^^ \<l>) state))) z = 
                     connected_component (to_graph (\<FF> state)) z" 
      using 1(2)[of \<l>] by simp 
    have gamma_after_k:
         "current_\<gamma> ((orlins_one_step_check ^^ \<l>) state) \<le> (1 / 2) ^ \<l> * current_\<gamma> state"
      using  assms 1(1)[of \<l>]  no_merge_gamma[OF refl, of \<l> state] by simp
    define state1 where "state1 = orlins_one_step_check state"
    have l_minus1_after1: "(orlins_one_step_check ^^ (\<l> - 1)) state1 = 
                           (orlins_one_step_check ^^ \<l>) state" 
      using l_0  funpow_Suc_right[of "\<l>-1" orlins_one_step_check] 
      by(simp add: state1_def)
    have props_after1: "invar_gamma state1" "aux_invar state1" "invar_non_zero_b state1"
                       "invar_integral state1" "implementation_invar state1"
                       "orlins_entry state1" "invar_forest state1" "invar_isOptflow state1"
      using 1(1)[of 1] l_0 
      by(auto simp add: state1_def assms
                intro!: some_balance_after_k_steps[of 1, simplified]
                        invars_pres_orlins_one_step_check)
   have gamma_after_k_minus1:
         "current_\<gamma> ((orlins_one_step_check ^^ (\<l>-1)) state1) \<le> (1 / 2) ^ (\<l>-1) * current_\<gamma> state1 "
     using  l_minus1_after1 no_merge_gamma[ OF  refl, of "\<l>-1" state1]
     by(auto simp add:  1(1)[of "\<l>"] props_after1)
   hence gamma_after_k_minus1': " 2^(\<l> - 1) * current_\<gamma> ((orlins_one_step_check ^^ (\<l> - 1)) state1) 
                                   \<le>  current_\<gamma> state1"
     apply(subst sym[OF mult_le_cancel_left_pos, of "(1 / 2) ^ (\<l> - 1)"], simp) 
     by(subst real_mul_assoc, subst cancel_power_denominator, simp, simp)
   have current_gamma_new_gamma:"current_\<gamma> state1 = new_\<gamma> state"
     using 1(1)[of 0]  
     by(auto intro!:  one_step_current_gamma_new_gamma simp add: assms state1_def)
    define Z  where "Z = connected_component (to_graph (\<FF> state)) z"
    have same_comp:"Z = connected_component (to_graph (\<FF> ((orlins_one_step_check ^^ \<l>) state))) z"
      using  same_forst by(simp add: Z_def)
    have outgoing_active:"e \<in> \<E> \<Longrightarrow> fst e \<in> Z \<Longrightarrow> snd e \<notin> Z \<Longrightarrow> e \<in> to_set (actives state)" for e
      using assms(2) unfolding aux_invar_def Z_def invar_aux13_def 
      using connected_components_member_sym[of "fst e" "to_graph (\<FF> state)" z] 
            connected_components_member_sym[of z "to_graph (\<FF> state)" "snd e"] by auto
    have ingoing_active:"e \<in> \<E> \<Longrightarrow> snd e \<in> Z \<Longrightarrow> fst e \<notin> Z \<Longrightarrow> e \<in> to_set (actives state)" for e
      using assms(2) unfolding aux_invar_def Z_def invar_aux13_def 
      using connected_components_member_sym[of "snd e" "to_graph (\<FF> state)" z] 
            connected_components_member_sym[of z "to_graph (\<FF> state)" "fst e"] by auto
    have new_gamma_less: "new_\<gamma> state \<le> current_\<gamma> state / 2"
      by(rule new_gamma_below_half_gamma)
    have new_gamma_0: "new_\<gamma> state > 0"
      using current_gamma_new_gamma  props_after1(1) by (auto elim: invar_gammaE)
    have balance_z_non_zero: "a_balance state z \<noteq> 0" and z_in_V: "z \<in> \<V>"
      using assms(1, 5) new_gamma_0 \<epsilon>_axiom unfolding important_def 
      by (smt (verit, ccfv_threshold) divide_less_eq_1 mul_zero_cancel, simp)
    hence "representative state z = z"
      using assms(2) z_in_V by(auto elim: aux_invarE invar_aux12E)
    moreover hence "x \<in> Z \<Longrightarrow> representative state x = z" for x
      using assms(2) z_in_V unfolding aux_invar_def Z_def invar_aux7_def 
      by (metis in_connected_componentE)
    moreover have Z_inV:"Z \<subseteq> \<V>"
          using assms(2) z_in_V by(simp add: aux_invar_def Z_def invar_aux10_def)
    ultimately have Z_balance:"x \<in> Z \<Longrightarrow> a_balance state x \<noteq> 0 \<Longrightarrow> x = z" for x
      using assms(2) by(auto simp add: aux_invar_def invar_aux12_def)
    have flow_value1: "sum (\<b> - a_balance state) Z = 
                       sum (a_current_flow state) (\<Delta>\<^sup>+ Z) - sum (a_current_flow state) (\<Delta>\<^sup>- Z)"
      by(intro flow_value[of "a_current_flow state" "\<b> - a_balance state" Z], auto
      simp add: assms(9)[simplified invar_isOptflow_def is_Opt_def] Z_inV)
    have out_mult1:"\<exists> n::int. n*current_\<gamma> state = sum (a_current_flow state) (\<Delta>\<^sup>+ Z)"
      apply(rule sum_integer_multiple)
      using  Delta_plus_def rev_finite_subset[OF finite_E , of "\<Delta>\<^sup>+ Z"] apply force
      subgoal for e
      apply(rule ballE[OF assms(4)[simplified invar_integral_def], of e], metis of_int_of_nat_eq)
        using outgoing_active[of e]  by(auto simp add: Delta_plus_def)
      done
   have ing_mul1:"\<exists> n::int. n*current_\<gamma> state = sum (a_current_flow state) (\<Delta>\<^sup>- Z)"
      apply(rule sum_integer_multiple)
      using  Delta_minus_def rev_finite_subset[OF finite_E , of "\<Delta>\<^sup>- Z"] apply force
      subgoal for e
      apply(rule ballE[OF assms(4)[simplified invar_integral_def], of e], metis of_int_of_nat_eq)
        using ingoing_active[of e] by(auto simp add: Delta_minus_def)
      done
    have cross_mult1:
        "\<exists> n::int. n * current_\<gamma> state = 
               sum (a_current_flow state) (\<Delta>\<^sup>+ Z) - sum (a_current_flow state) (\<Delta>\<^sup>- Z)"
      using  integer_multiple_sub ing_mul1 out_mult1 by metis
    have "sum (\<b> - a_balance state) Z = sum \<b> Z - sum (a_balance state) Z"
      apply(subst diff_conv_add_uminus, subst sym[OF sum_negf])
      using sum.distrib[of \<b> "- a_balance state" Z, simplified] by simp
    also have "... = sum \<b> Z - (sum (a_balance state) (Z - {z}) + sum (a_balance state) {z})"
      apply(subst (2)sum.subset_diff[of "{z}" Z ])
      using Z_def Z_inV \<V>_finite connected_component_def rev_finite_subset by fastforce+
    also have "... = sum \<b> Z - a_balance state z" 
      using Z_balance sum.neutral[of "Z-{z}" "a_balance state"] by fastforce
    finally have balance_sum:"sum (\<b> - a_balance state) Z = sum \<b> Z - a_balance state z " by simp
    have cal21:"\<epsilon> * new_\<gamma> state \<le> (1-\<epsilon>) * new_\<gamma> state"
      using \<epsilon>_axiom new_gamma_0 
      by (auto intro!: mult_right_mono)
    also have cal22:"... < \<bar> a_balance state z \<bar>" using assms(5) 
      by(auto elim: importantE)
    also have cal23:"... \<le> (1-\<epsilon>) * current_\<gamma> state"
      using assms(8) z_in_V by(auto elim: orlins_entryE)
    also have cal24:"... < current_\<gamma> state - \<epsilon> * new_\<gamma> state"
      using mult_less_cancel_left_pos gamma_0 new_gamma_less new_gamma_0 \<epsilon>_axiom
      by (auto simp add: left_diff_distrib)
    have sum_b_Z_above_eps_gam:"\<bar> sum \<b> Z \<bar> > \<epsilon> * new_\<gamma> state"
    proof(rule ccontr, goal_cases)
      case 1
      hence asm:"\<bar>sum \<b> Z\<bar> \<le> \<epsilon> * new_\<gamma> state" by simp
      have " sum \<b> Z - a_balance state z \<le> \<bar>sum \<b> Z - a_balance state z\<bar>" by simp
      also have "... \<le> \<bar> sum \<b> Z\<bar> + \<bar> a_balance state z\<bar>" by simp
      also have "... <  current_\<gamma> state "
        using cal23 cal24 asm by simp
      finally have less_curr_gamma:"sum \<b> Z - a_balance state z < current_\<gamma> state" by simp
      have " sum \<b> Z - a_balance state z \<ge> - \<bar>sum \<b> Z - a_balance state z\<bar>" by simp
      have "- \<bar>sum \<b> Z - a_balance state z\<bar> \<ge> -\<bar> sum \<b> Z\<bar> -\<bar> a_balance state z\<bar>" by simp
      have gtr_minus_curr_gamma:"sum \<b> Z - a_balance state z > - current_\<gamma> state" 
        using  cal23 cal24 asm by simp
      have a1:" \<bar> sum \<b> Z - a_balance state z \<bar>  =  \<bar> a_balance state z - sum \<b> Z  \<bar> " by simp
       have a2:"... \<ge> \<bar> \<bar>a_balance state z\<bar> - \<bar>sum \<b> Z \<bar>\<bar>" by simp
       have a3:"\<bar> \<bar>a_balance state z\<bar> - \<bar>sum \<b> Z \<bar>\<bar> > 0 "
        apply(subst zero_less_abs_iff, rule not_sym, rule order.strict_implies_not_eq)        
        using cal22 asm new_gamma_0 \<epsilon>_axiom(4) cal21 by linarith
       have "\<bar> sum \<b> Z - a_balance state z \<bar> > 0" using a2 a3 by simp
      moreover have "sum \<b> Z - a_balance state z = 0"
        apply(rule exE[OF cross_mult1[simplified sym[OF flow_value1] balance_sum]])
          using gtr_minus_curr_gamma less_curr_gamma gamma_0
          by (smt (verit, ccfv_threshold) int_less_real_le mult_le_cancel_right1 mult_minus_left  
                                          of_int_0_less_iff of_int_less_0_iff)
       ultimately show ?case by simp
     qed
     define state' where "state' = (orlins_one_step_check ^^ \<l>) state"
     have aux_invar_state': "aux_invar state'" 
      and invar_gamma_state': "invar_gamma state'"
      and invar_integral_state': "invar_integral state'"
      and invar_isOptflow_state': "invar_isOptflow state'"
      and implementation_invar_state': "implementation_invar state'"
       using assms(1-4,7-)
       by(auto intro!: orlins_compow_aux_invar_pres orlins_compow_invar_gamma_pres 
                       orlins_compow_invar_integral_pres orlins_compow_invar_isOptflow_pres
                       orlins_compow_implementation_invar_pres
             simp add:  state'_def)
     have orlins_entry_after: "orlins_entry state'" 
       using 1(1)[of \<l>] by(auto intro!: orlins_entry_after_compow simp add: state'_def  assms(1-4,7-) )
     have remaining_balance_after: "invar_non_zero_b state'"
        by(auto intro!: some_balance_after_k_steps[OF 1(1)[of \<l>, OF order.refl]] simp add: state'_def  assms(1-4,7-) )
      have new_gamma_state'_0:"new_\<gamma> state' > 0"
        using remaining_balance_after  gamma_upd_aux_invar_pres[OF invar_gamma_state' 
            remaining_balance_after aux_invar_state' implementation_invar_state']
       by(auto elim: invar_gammaE)
      have e_flow_gr_0:"\<And> e. e \<in> \<E> \<Longrightarrow> a_current_flow state' e \<ge> 0"
        using invar_isOptflow_state' 
        by(auto elim!: invar_isOptflowE is_OptE isbflowE isuflowE)
     have flow_value2: "sum (\<b> - a_balance state') Z = 
                       sum (a_current_flow state') (\<Delta>\<^sup>+ Z) - sum (a_current_flow state') (\<Delta>\<^sup>- Z)"    
      by(intro flow_value[of "a_current_flow state'" "\<b> - a_balance state'" Z], auto
      simp add: invar_isOptflow_state'[simplified invar_isOptflow_def is_Opt_def] Z_inV)
    have sumb_split:"sum (\<b> - a_balance state') Z = sum \<b> Z - sum (a_balance state') Z"
      apply(subst diff_conv_add_uminus, subst sym[OF sum_negf])
      using sum.distrib[of \<b> "- a_balance state'" Z, simplified] by simp
    have sumZ_below:"\<bar>sum (a_balance state') Z \<bar>\<le> (1- \<epsilon>) * current_\<gamma> state'"
    proof(cases rule: disjE[OF invar_gamma_non_zero_balance_set[OF aux_invar_state' refl z_in_V]])
      case 1
      hence "sum (a_balance state') Z = 0" using same_comp
        by(simp add: Z_def state'_def)
      moreover have "(1 - \<epsilon>) * current_\<gamma> state' > 0" using invar_gamma_state' \<epsilon>_axiom(4)
        by(auto elim!: invar_gammaE)
      ultimately show ?thesis by simp
    next
      case 2
      then obtain x where x_prop: 
           "{x} = {v |v. v \<in> connected_component (to_graph (\<FF> state')) z \<and> a_balance state' v \<noteq> 0} " by auto
      hence x_in_V:"x \<in> \<V>" using same_comp state'_def Z_def Z_inV by auto
      have "sum (a_balance state') Z = (a_balance state') x" 
        apply(subst  sum_filter_zero[OF rev_finite_subset[OF \<V>_finite Z_inV], 
                 of "a_balance state'"])
        apply(subst  (2) sym[OF sum_singleton[where f = "\<lambda> x. a_balance state' x"]])
        apply(subst  x_prop)
        apply(subst same_comp)
        unfolding state'_def by simp      
      moreover have "\<bar> (a_balance state') x \<bar> \<le> (1-\<epsilon>) * current_\<gamma> state'"
        using orlins_entry_after x_in_V by(auto elim: orlins_entryE)
      finally show ?thesis
        by simp
    qed
    have "sum (\<lambda> e. a_current_flow state' e) (\<Delta>\<^sup>+ Z \<union> \<Delta>\<^sup>- Z) = 
          sum (\<lambda> e. \<bar> a_current_flow state' e\<bar>) (\<Delta>\<^sup>+ Z \<union> \<Delta>\<^sup>- Z)"
      using e_flow_gr_0 by(auto intro: sum_cong[of ] simp add: Delta_plus_def Delta_minus_def)
    moreover have "sum (\<lambda> e. \<bar> a_current_flow state' e\<bar>) (\<Delta>\<^sup>+ Z \<union> \<Delta>\<^sup>- Z) = 
         sum (\<lambda> e. \<bar> a_current_flow state' e\<bar>) (\<Delta>\<^sup>+ Z) + 
             sum ((\<lambda> e. \<bar> a_current_flow state' e\<bar>)) (\<Delta>\<^sup>- Z)"
      using rev_finite_subset[OF finite_E , of "\<Delta>\<^sup>+ Z"] rev_finite_subset[OF finite_E , of "\<Delta>\<^sup>- Z"] 
      by(auto intro:  sum.union_disjoint simp add: Delta_plus_def Delta_minus_def)
    moreover have "sum (\<lambda> e. \<bar> a_current_flow state' e\<bar>) (\<Delta>\<^sup>+ Z) + 
             sum ((\<lambda> e. \<bar> a_current_flow state' e\<bar>)) (\<Delta>\<^sup>- Z) \<ge>
          \<bar> sum (a_current_flow state') (\<Delta>\<^sup>+ Z) - sum (a_current_flow state') (\<Delta>\<^sup>- Z) \<bar>"
      using sum_abs[of "a_current_flow state'" "\<Delta>\<^sup>+ Z"] sum_abs[of "a_current_flow state'" "\<Delta>\<^sup>- Z"] 
      by linarith
    moreover have "\<bar> sum (a_current_flow state') (\<Delta>\<^sup>+ Z) - sum (a_current_flow state') (\<Delta>\<^sup>- Z) \<bar>
                    = \<bar>sum \<b> Z - sum (a_balance state') Z \<bar>"
      using sumb_split flow_value2 by simp
    moreover have "... \<ge> \<bar>sum \<b> Z\<bar> - \<bar>sum (a_balance state') Z \<bar>"
      by simp
    moreover have "\<bar>sum \<b> Z\<bar> - \<bar>sum (a_balance state') Z \<bar> > 
                   \<epsilon> * new_\<gamma> state - (1 - \<epsilon>) * current_\<gamma> state'"
      using sum_b_Z_above_eps_gam sumZ_below by simp
    moreover have "\<epsilon> * new_\<gamma> state - (1 - \<epsilon>) * current_\<gamma> state' \<ge>
                  \<epsilon> * 2^(\<l>-1) * current_\<gamma> state' - (1 - \<epsilon>) * current_\<gamma> state'"
      using gamma_after_k_minus1'[simplified l_minus1_after1 current_gamma_new_gamma
                        sym[OF state'_def]] \<epsilon>_axiom by simp
    moreover have "\<epsilon> * 2^(\<l>-1) * current_\<gamma> state' - (1 - \<epsilon>) * current_\<gamma> state' \<ge>
                   M * (8 * real N * current_\<gamma> state' / 2)" apply simp
      using invar_gamma_state'[simplified invar_gamma_def] 
      apply(subst mult.commute[of "current_\<gamma> _"], simp)
      apply(subst real_mul_assoc[of 4], subst real_mul_assoc)
      apply(subst sym[OF left_diff_distrib], simp)
      apply(subst le_diff_eq)
      apply(subst sym[OF log_le_cancel_iff, of 2, simplified])
      using M_gtr_zero N_gtr_0 \<epsilon>_axiom(2)
      apply (smt (verit, del_insts) le_divide_eq_1_pos mul_zero_cancel of_nat_0_less_iff)
      using \<epsilon>_axiom apply simp
      apply(subst log_mult[of _  _ "2 ^ _", simplified])
      apply(subst if_P)
      using \<epsilon>_axiom
      apply( simp add: \<epsilon>_axiom, simp)
      unfolding assms(6) apply simp
      apply(subst add.commute[of "log 2 _"])
      apply(subst sym[OF diff_le_eq]) 
      apply(rule ord_eq_le_trans[OF _ real_nat_ceiling_ge]) 
      by argo
    moreover have " M * (8 * real N * current_\<gamma> state' / 2) \<ge>
                    M * (8 * real N * new_\<gamma> state')" 
      using N_gtr_0 M_gtr_zero  new_gamma_below_half_gamma[of state'] by simp
    ultimately have final_sum_chain:"sum (\<lambda> e. a_current_flow state' e) (\<Delta>\<^sup>+ Z \<union> \<Delta>\<^sup>- Z)  > 
              M * (8 * real N * new_\<gamma> state')" by argo
    have card_Delta_M:"card (\<Delta>\<^sup>+ Z \<union> \<Delta>\<^sup>- Z) \<le> M"
      unfolding M_def Delta_minus_def Delta_plus_def
      by(auto intro: card_mono[OF finite_E] )
    have "\<exists> e \<in> \<Delta>\<^sup>+ Z \<union> \<Delta>\<^sup>- Z. a_current_flow state' e > 8 * real N * new_\<gamma> state'"
    proof(rule ccontr, goal_cases)
      case 1
      hence asm:"\<And> e. e \<in> \<Delta>\<^sup>+ Z \<union> \<Delta>\<^sup>- Z \<Longrightarrow> a_current_flow state' e \<le> 8 * real N * new_\<gamma> state'" by force
      have "sum (a_current_flow state') (\<Delta>\<^sup>+ Z \<union> \<Delta>\<^sup>- Z) 
           \<le> real M * (8 * real N * new_\<gamma> state')"
        apply(rule order.trans, rule sum_bounded_above[OF asm, of "\<Delta>\<^sup>+ Z \<union> \<Delta>\<^sup>- Z" id, simplified])
        using  card_Delta_M  M_gtr_zero N_gtr_0 new_gamma_state'_0 by simp
      thus?case using final_sum_chain by simp
    qed
    then obtain e where e_prop:"e \<in> \<Delta>\<^sup>+ Z \<union> \<Delta>\<^sup>- Z " " 8 * real N * new_\<gamma> state' < a_current_flow state' e"
      by auto
    hence e_E:"e \<in> \<E>"
      unfolding Delta_plus_def Delta_minus_def by auto
    have e_comps_neq:"connected_component (to_graph (\<FF> state')) (fst e) \<noteq>
         connected_component (to_graph (\<FF> state')) (snd e)" 
      using e_prop(1) same_comp connected_components_member_sym
      by (simp add: Z_def state'_def Delta_plus_def Delta_minus_def  same_comp) fast
    hence e_active: "e \<in> to_set (actives state')"
      using aux_invar_state' e_E by(auto elim: aux_invarE invar_aux13E)
    have "\<exists> d. get_from_set
     (\<lambda>e. 8 * real N * new_\<gamma> state' < a_current_flow state' e)
       (actives state') =
       Some d"
    using  e_prop(1,2)  e_active
    by (auto intro!: set_get(1)[OF _ exI, of _ e] from_aux_invar'(17)[OF aux_invar_state']
           simp add: Delta_plus_def Delta_minus_def outgoing_active ) 
  then obtain d where d_prop:"get_from_set
     (\<lambda>e. 8 * real N * new_\<gamma> state' < a_current_flow state' e)
     (actives state') =
    Some d" by auto
    hence call_cond: "maintain_forest_call_cond (state' \<lparr> current_\<gamma> := new_\<gamma> state'\<rparr>)"
      by(auto intro: maintain_forest_call_condI[OF refl refl refl refl ])
  have e_comps:"connected_component (to_graph (\<FF> (maintain_forest (state'\<lparr>current_\<gamma> := new_\<gamma> state'\<rparr>)))) (fst e) =
                connected_component (to_graph (\<FF> (maintain_forest (state'\<lparr>current_\<gamma> := new_\<gamma> state'\<rparr>)))) (snd e)"
    by(rule component_strict_increase)
      (auto intro!: termination_of_maintain_forest aux_invar_gamma
                    implementation_invar_gamm_upd
          simp add: e_active e_prop(2) call_cond  aux_invar_state' implementation_invar_state')
  have fst_snd_e_comp_Z:"Z = connected_component (to_graph (\<FF> state')) (fst e) \<or>
                                Z = connected_component (to_graph (\<FF> state')) (snd e)"
    using e_prop(1) same_comp[simplified sym[OF state'_def]]
    unfolding Delta_plus_def Delta_minus_def 
    using  connected_components_member_eq[of "fst e" "to_graph (\<FF> state')" z] 
           connected_components_member_eq[of "snd e" "to_graph (\<FF> state')" z] by auto
  have z_same_e:"connected_component (to_graph (\<FF> (maintain_forest (state'\<lparr>current_\<gamma> := new_\<gamma> state'\<rparr>)))) z =
        connected_component (to_graph (\<FF> (maintain_forest (state'\<lparr>current_\<gamma> := new_\<gamma> state'\<rparr>)))) (fst e)"
  proof(cases rule: disjE[OF fst_snd_e_comp_Z])
    case 1
    show ?thesis 
     using same_comp[simplified sym[OF state'_def]]  1
     by(intro same_component_set_mono[OF  forest_increase,
                        of "state'\<lparr>current_\<gamma> := new_\<gamma> state'\<rparr>" z])
       (auto intro!: termination_of_maintain_forest aux_invar_gamma 
                     implementation_invar_gamm_upd
          simp add:  aux_invar_state' implementation_invar_state')
 next 
   case 2
   have "connected_component (to_graph (\<FF> (local.maintain_forest
                          (state'\<lparr>current_\<gamma> := new_\<gamma> state'\<rparr>)))) z =
          connected_component (to_graph (\<FF> (local.maintain_forest 
                          (state'\<lparr>current_\<gamma> := new_\<gamma> state'\<rparr>)))) (snd e)"
     using same_comp[simplified sym[OF state'_def]]  2
     by(intro same_component_set_mono[OF  forest_increase,
                        of "state'\<lparr>current_\<gamma> := new_\<gamma> state'\<rparr>" z])
       (auto intro!: termination_of_maintain_forest aux_invar_gamma 
                     implementation_invar_gamm_upd
          simp add:  aux_invar_state' implementation_invar_state')
   thus ?thesis
     using e_comps by simp
 qed
  have comps_monotone: 
    " connected_component (to_graph (\<FF> (state'\<lparr>current_\<gamma> := new_\<gamma> state'\<rparr>))) u
    \<subseteq> connected_component (to_graph (\<FF> (maintain_forest (state'\<lparr>current_\<gamma> := new_\<gamma> state'\<rparr>)))) u" for u
    apply(rule con_comp_subset, rule forest_increase)
    by(auto intro!: termination_of_maintain_forest aux_invar_gamma
                    implementation_invar_gamm_upd
          simp add: aux_invar_state' implementation_invar_state')
   have disjoint_F_comps: 
       "connected_component (to_graph (\<FF> state')) (fst e) \<inter> 
              connected_component (to_graph (\<FF> state')) (snd e) = {}"
     using dVsI'(2)[of "make_pair e" "make_pair ` \<E>"] e_E 
           e_comps_neq unequal_components_disjoint [of _ "fst e" "snd e"]
           fst_E_V make_pair[OF refl refl] by auto
   have comp_strict_suubst_z:"connected_component (to_graph (\<FF> state')) z
    \<subset> connected_component (to_graph (\<FF> (maintain_forest (state'\<lparr>current_\<gamma> := new_\<gamma> state'\<rparr>)))) z"
      apply(rule disjE[OF fst_snd_e_comp_Z])
     using z_same_e same_comp[simplified sym[OF state'_def]] fst_snd_e_comp_Z
           e_comps comps_monotone[of "fst e", simplified] comps_monotone[of "snd e", simplified]
           connected_component_non_empt[of "to_graph (\<FF> state')" "(snd e)"] 
           connected_component_non_empt[of "to_graph (\<FF> state')" "(fst e)"]disjoint_F_comps 
     by auto
   have dom_send_flow: "send_flow_dom (local.maintain_forest
       ((orlins_one_step_check ^^ \<l>) 
             state\<lparr>current_\<gamma> := new_\<gamma> ((orlins_one_step_check ^^ \<l>) state)\<rparr>))"   
     using assms(1,10,2,3,4,7,8,9) aux_invar_state' implementation_invar_state' invar_gamma_state'
       invar_integral_state' invar_isOptflow_state' invars_after_maintain_forest(11)
       orlins_compow_invar_forest_pres orlins_entry_after remaining_balance_after 
     by (auto simp add: state'_def)
  have "connected_component (to_graph (\<FF> ((orlins_one_step_check ^^ (Suc \<l>)) state))) z \<supset> 
        connected_component (to_graph (\<FF> ((orlins_one_step_check ^^ \<l>) state))) z"
    apply(simp, subst orlins_one_step_check_def[of "(orlins_one_step_check ^^ \<l>) state"],simp add: 1(1)[of \<l>])
    unfolding orlins_one_step_def Let_def
    apply(subst send_flow_changes_\<FF>[OF dom_send_flow])
    using comp_strict_suubst_z 
    by (simp add: sym[OF new_\<gamma>_def[simplified  Let_def]] sym[OF state'_def] )
  thus ?case 
    using connected_compt_subs by simp
 qed
  thus ?thesis 
    by (metis Suc_eq_plus1 le_Suc_eq)
qed

lemma if_important_then_merge_or_termination:
  assumes "invar_gamma state"
          "aux_invar state"
          "invar_non_zero_b state"
          "invar_integral state"
          "important state z"
          "\<l> =  nat (\<lceil> log 2 ((4*M*N) + (1 - \<epsilon>)) - log 2 \<epsilon>\<rceil>) + 1"
          "invar_forest state"
          "orlins_entry state"
          "invar_isOptflow state"
          "implementation_invar state"
  shows   "\<exists> k \<le> \<l> + 1. (return ((compow k orlins_one_step_check) state) \<noteq> notyetterm) \<or>
                      card (comps \<V> (to_graph (\<FF> state))) >
                      card (comps \<V> (to_graph (\<FF> (compow k (orlins_one_step_check) state))))"
proof(rule exE[OF if_important_then_comp_increase_or_termination[OF assms]], goal_cases)
  case (1 k)
  thus ?case
    using orlins_some_steps_forest_increase[OF refl assms(2,1,3,10,8,7,4,9)] 
          assms(5)[simplified important_def] 
          orlins_compow_aux_invar_pres[OF assms(2,1,3,10,8,7,4,9),
             simplified aux_invar_def invar_aux15_def invar_aux5_def, of k] 
          number_of_comps_anti_mono_strict[of _ _ z] 
    by meson
qed

theorem finally_termination:
  assumes "\<l> =  nat (\<lceil> log 2 (4*M*N + (1 - \<epsilon>)) - log 2 \<epsilon>\<rceil>) + 1"
          "\<k> =  nat (\<lceil>log 2 N \<rceil> + 3)"
          "invar_gamma state"
          "aux_invar state"
          "invar_non_zero_b state"
          "invar_integral state"
          "invar_forest state"
          "orlins_entry state"
          "invar_isOptflow state"
          "I = card (comps \<V> (to_graph (\<FF> state)))"
          "implementation_invar state"
    shows "return ((orlins_one_step_check ^^ (I * (\<l> + \<k> + 2))) state) \<noteq> notyetterm"
  using assms(3-)
proof(induction I arbitrary: state rule: less_induct)
  case (less F)
  hence uflow: "isuflow (a_current_flow state)"
    by(auto elim!: invar_isOptflowE is_OptE isbflowE)
  have F_1: "F \<ge> 1"
    using less(9) V_non_empt \<V>_finite card_image_le[of \<V> "connected_component (to_graph (\<FF> state))"] 
          image_is_empty[of "connected_component (to_graph (\<FF> state))" \<V>]
    unfolding comps_def 
    by (metis One_nat_def card_gt_0_iff finite_imageI less_Suc_eq_le linorder_not_le)
  obtain k where k_prop: "k \<le> \<k> + 1" "return ((orlins_one_step_check ^^ k) state) \<noteq> notyetterm \<or>
                  (\<exists>v. important ((orlins_one_step_check ^^ k) state) v) \<or>
                  card (comps \<V> (to_graph (\<FF> ((orlins_one_step_check ^^ k) state)))) 
                              < card (comps \<V> (to_graph (\<FF> state)))"
    using important_or_merge_or_termination[OF less(2,3,4,5,10,7,6,8) assms(2)] by auto 
  define state1 where "state1 = (orlins_one_step_check ^^ k) state"
  have invar_gamma_state1:"invar_gamma state1"
   and aux_invar_state1: "aux_invar state1"
   and invar_integral_state1: "invar_integral state1"
   and invar_forest_state1: "invar_forest state1"
   and invar_isOptflow_state1: "invar_isOptflow state1"
   and implementation_invar_state1: "implementation_invar state1"
       using less(2-)
       by(auto intro!: orlins_compow_aux_invar_pres orlins_compow_invar_gamma_pres 
                       orlins_compow_invar_integral_pres orlins_compow_invar_isOptflow_pres
                       orlins_compow_implementation_invar_pres orlins_compow_invar_forest_pres
             simp add:  state1_def)
  show ?case 
  proof(cases rule: triple_or_strictE[OF k_prop(2)])
    case 1
    have "F * (\<l> + \<k> + 2) \<ge> k"
      using F_1 k_prop(1) 
      by (smt (verit, ccfv_threshold) add.assoc add_leD2 le_add1 le_trans mult.commute 
        mult_le_mono2 mult_numeral_1_right numeral_One one_add_one)
    then show ?thesis 
      using iterated_orlins_one_step_check_mono[OF 1 , of "F * (\<l> + \<k> + 2) - k"] 1 by simp
  next
    case 2
    hence 2: "\<exists>v. important ((orlins_one_step_check ^^ k) state) v"
             "return ((orlins_one_step_check ^^ k) state) = notyetterm" by auto
    note case2=this
    then obtain v where v_prop:"important state1 v" by(auto simp add:state1_def)
    have remaining_balance: "invar_non_zero_b state1"
      using some_balance_after_k_steps[OF 2(2) less(3,2,4,10,7,6,5,8)] by(simp add: state1_def)
    have orlins_entry_after_k: "orlins_entry state1"
      using orlins_entry_after_compow[OF less(3,2,4) 2(2) less(7,10,6,5,8)] 
      by(simp add: state1_def)
   obtain l where l_prop:"l \<le> \<l> + 1" "return ((orlins_one_step_check ^^ l) state1) \<noteq> notyetterm \<or>
         card (comps \<V> (to_graph (\<FF> ((orlins_one_step_check ^^ l) state1)))) 
               < card (comps \<V> (to_graph (\<FF> state1)))"
     using if_important_then_merge_or_termination[OF
                 invar_gamma_state1 aux_invar_state1 remaining_balance invar_integral_state1 
                 v_prop assms(1) invar_forest_state1 orlins_entry_after_k invar_isOptflow_state1 
                 implementation_invar_state1]
     by auto

   show ?thesis 
   proof(cases rule: double_or_strictE[OF l_prop(2)])
     case 1
     have F_gtr:"F * (\<l> + \<k> + 2) \<ge> k + l"
       apply(subst (2) sym[OF mult_1_right], subst mult.commute)
       apply(rule mult_le_mono)
      using F_1 k_prop(1) l_prop(1) by simp+     
     hence "return ((orlins_one_step_check ^^ (l+k)) state) \<noteq> notyetterm" 
       using 1
       by(subst funpow_add, simp add: state1_def)
     hence "return ((orlins_one_step_check ^^ (F * (\<l> + \<k> + 2))) state) \<noteq> notyetterm"
       using iterated_orlins_one_step_check_mono[of "l+k" state "F * (\<l> + \<k> + 2) - (l + k)"] F_gtr
       by simp
     thus ?thesis by simp
   next
     case 2
     hence 2: "card (comps \<V> (to_graph (\<FF> ((orlins_one_step_check ^^ l) state1))))
                     < card (comps \<V> (to_graph (\<FF> state1)))"
              "return ((orlins_one_step_check ^^ l) state1) = notyetterm" by simp+
     define state2 where "state2 = (orlins_one_step_check ^^ l) state1"
     define G where "G = card (comps \<V> (to_graph (\<FF> state2)))"
     have G_less_F:"G < F" using G_def state2_def 2(1) 
           orlins_some_steps_card_decrease[OF state1_def ] less by simp
     have orlins_entry_state1: "orlins_entry state1"
      and invar_non_zero_b_state1: "invar_non_zero_b state1"
       using less(2-) case2(2)
       by(auto intro!: orlins_entry_after_k_steps some_balance_after_k_steps
             simp add:  state1_def)
     have invar_gamma_state2:"invar_gamma state2" 
      and aux_invar_state2: "aux_invar state2"
      and invar_integral_state2: "invar_integral state2"
      and invar_forest_state2: "invar_forest state2"
      and invar_isOptflow_state2: "invar_isOptflow state2"
      and remaining_balance_state2: "invar_non_zero_b state2"
      and orlins_entry_after_l: "orlins_entry state2"
      and implementation_invar_state2: "implementation_invar state2"
       using 2(2)  
        by(auto intro!: orlins_compow_aux_invar_pres orlins_compow_invar_gamma_pres 
                        orlins_compow_invar_integral_pres orlins_compow_invar_isOptflow_pres
                        orlins_compow_implementation_invar_pres orlins_compow_invar_forest_pres
                        orlins_entry_after_k_steps some_balance_after_k_steps
              simp add: state2_def invar_gamma_state1  aux_invar_state1 
                       remaining_balance implementation_invar_state1 orlins_entry_state1
                       invar_forest_state1  invar_integral_state1 invar_isOptflow_state1)
    have "return ((orlins_one_step_check ^^ (G * (\<l> + \<k> + 2))) state2) \<noteq> notyetterm"
      using less(1)[OF G_less_F invar_gamma_state2 aux_invar_state2 remaining_balance_state2
                   invar_integral_state2 invar_forest_state2 orlins_entry_after_l 
                   invar_isOptflow_state2 G_def implementation_invar_state2]
      by simp
    hence "return ((orlins_one_step_check ^^ (G * (\<l> + \<k> + 2) + l + k)) state) \<noteq> notyetterm"
      unfolding  state2_def state1_def 
      by(subst funpow_add, simp, subst funpow_add, simp)
    moreover have "G * (\<l> + \<k> + 2) + l + k \<le> F * (\<l> + \<k> + 2)"
      apply(rule order.trans[of _ "G * (\<l> + \<k> + 2) + (\<l> + \<k> + 2)"])
      using G_less_F l_prop(1) k_prop(1) F_1 apply simp
      apply(subst (12) sym[OF mult_1])
      apply(subst semiring_normalization_rules(1))
      apply(rule mult_le_mono1)
      using G_less_F by simp
    ultimately show ?thesis 
      using iterated_orlins_one_step_check_mono[of "G * (\<l> + \<k> + 2) + l + k" state
                                                   "F * (\<l> + \<k> + 2) - (G * (\<l> + \<k> + 2) + l + k)"]
      by simp
   qed
  next 
    case 3
    hence 3: "card (comps \<V> (to_graph (\<FF> ((orlins_one_step_check ^^ k) state)))) 
            < card (comps \<V> (to_graph (\<FF> state)))"
             "return ((orlins_one_step_check ^^ k) state) = notyetterm" by simp+
    have remaining_balance: "invar_non_zero_b state1"
      using some_balance_after_k_steps[OF 3(2) less(3,2,4,10,7,6,5,8)] by(simp add: state1_def)
    have orlins_entry_after_k: "orlins_entry state1"
     using orlins_entry_after_compow[OF less(3,2,4) 3(2) less(7,10,6,5,8)] state1_def by(simp add: state1_def)
    define G where "G = card (comps \<V> (to_graph (\<FF> state1)))"
    have G_less_F: "G < F" using 3 G_def less(9) by(simp add: state1_def)
    have "return ((orlins_one_step_check ^^ (G * (\<l> + \<k> + 2))) state1) \<noteq> notyetterm"
      using less(1)[OF G_less_F invar_gamma_state1 aux_invar_state1 remaining_balance invar_integral_state1
                   invar_forest_state1 orlins_entry_after_k invar_isOptflow_state1 G_def implementation_invar_state1]
       by simp
    hence "return ((orlins_one_step_check ^^ (G * (\<l> + \<k> + 2) + k)) state) \<noteq> notyetterm"
      unfolding  state1_def 
      by(subst funpow_add, simp)
    moreover have "G * (\<l> + \<k> + 2) + k \<le> F * (\<l> + \<k> + 2)"
      apply(rule order.trans[of _ "G * (\<l> + \<k> + 2) + (\<l> + \<k> + 2)"])
      using G_less_F  k_prop(1) F_1 apply simp
      apply(subst (12) sym[OF mult_1])
      apply(subst semiring_normalization_rules(1))
      apply(rule mult_le_mono1)
      using G_less_F by simp
    ultimately show ?thesis 
      using iterated_orlins_one_step_check_mono[of "G * (\<l> + \<k> + 2) + k" state
                                                   "F * (\<l> + \<k> + 2) - (G * (\<l> + \<k> + 2)  + k)"]
      by simp
  qed
qed

theorem compow_correctness:
  assumes "invar_gamma state"
          "aux_invar state"
          "invar_non_zero_b state"
          "invar_integral state"
          "invar_forest state"
          "orlins_entry state"
          "invar_isOptflow state"
          "implementation_invar state"
          "return state = notyetterm"
          "state' = (orlins_one_step_check ^^ (Suc k)) state"
    shows "return state' = success \<Longrightarrow> is_Opt \<b> (a_current_flow state')"
  unfolding assms
  using assms(1-9)
proof(induction k arbitrary: state)
  case 0
  show ?case 
    using  optimality_pres_orlins_one_step_check(2)[OF 0(3,2,9,4,7,6,5,8)] 0(1,10)
    by(auto simp add: orlins_one_step_check_def ) 
next
  case (Suc k)
  have no_changes_at_end:
       "return ((orlins_one_step_check ^^ k) state) = success \<Longrightarrow>
        (orlins_one_step_check ^^ Suc k) state = (orlins_one_step_check ^^ k) state"
       "return ((orlins_one_step_check ^^ k) state) = failure \<Longrightarrow>
        (orlins_one_step_check ^^ Suc k) state = (orlins_one_step_check ^^ k) state"
    by(auto simp add: orlins_one_step_check_def)
  show ?case 
  proof(cases "return ((orlins_one_step_check ^^ Suc k) state)", goal_cases)
    case 1
    hence alt_1:"return ((orlins_one_step_check ^^ Suc k) state) = success"
      by simp
    show ?case 
       using  Suc(1)[OF alt_1 Suc(3-11)]
       apply(simp, subst orlins_one_step_check_def)
       using "1" no_changes_at_end 
       by (auto simp add: orlins_one_step_check_def)
  next
    case 2
    then show ?case 
      using Suc.prems(1) return.simps(2)
            succ_fail_term_same_check[OF refl Suc.prems(10)] 
      by metis
  next
    case 3
    show ?case 

      apply(subst funpow.simps(2), subst o_apply)
      apply(rule optimality_pres_orlins_one_step_check(2))
      using Suc(2) 
      by(intro orlins_compow_invar_gamma_pres orlins_compow_aux_invar_pres Suc(2-) 
               orlins_compow_invar_integral_pres orlins_compow_implementation_invar_pres
               some_balance_after_k_steps 3 orlins_entry_after_k_steps
               orlins_compow_invar_forest_pres orlins_compow_invar_isOptflow_pres | simp)+
  qed
qed

corollary compow_correctness_gtr0:
  assumes "invar_gamma state"
          "aux_invar state"
          "invar_non_zero_b state"
          "invar_integral state"
          "invar_forest state"
          "orlins_entry state"
          "invar_isOptflow state"
          "return state = notyetterm"
          "state' = (orlins_one_step_check ^^ k) state"
          "k > 0" "implementation_invar state"
          "return state' = success"
        shows "is_Opt \<b> (a_current_flow state')"
proof-
  obtain k' where k': "k = Suc k'"
    using assms by(cases k) auto
  show ?thesis
   unfolding k' assms
   apply(rule compow_correctness[OF _ _ _ _ _ _ _ _ _ refl])
   using assms 
   by(auto simp add: k')
qed

theorem compow_completeness:
  assumes "invar_gamma state"
          "aux_invar state"
          "invar_non_zero_b state"
          "invar_integral state"
          "invar_forest state"
          "orlins_entry state"
          "invar_isOptflow state"
          "implementation_invar state"
          "return state = notyetterm"
          "state' = (orlins_one_step_check ^^ (Suc k)) state"
        shows "return state' = failure \<Longrightarrow> \<nexists> f. f is \<b> flow"
  unfolding assms
  using assms(1-9)
proof(induction k arbitrary: state)
  case 0
  show ?case 
    using  optimality_pres_orlins_one_step_check(3)[OF 0(3,2,9,4,7,6,5,8)] 0(1,10)
    by(auto simp add: orlins_one_step_check_def ) 
next
  case (Suc k)
  have no_changes_at_end:
       "return ((orlins_one_step_check ^^ k) state) = success \<Longrightarrow>
        (orlins_one_step_check ^^ Suc k) state = (orlins_one_step_check ^^ k) state"
       "return ((orlins_one_step_check ^^ k) state) = failure \<Longrightarrow>
        (orlins_one_step_check ^^ Suc k) state = (orlins_one_step_check ^^ k) state"
    by(auto simp add: orlins_one_step_check_def)
  show ?case 
  proof(cases "return ((orlins_one_step_check ^^ Suc k) state)", goal_cases)
    case 1
    hence alt_1:"return ((orlins_one_step_check ^^ Suc k) state) = success"
      by simp
    show ?case
      by (metis Suc.prems(1) alt_1 return.simps(2) succ_fail_term_same)
  next
    case 2
    hence alt_2:"return ((orlins_one_step_check ^^ Suc k) state) = failure"
      by simp
     show ?case 
       using  Suc(1)[OF alt_2 Suc(3-11)]  "2" no_changes_at_end 
       by (auto simp add: orlins_one_step_check_def)
  next
    case 3
    show ?case
      using Suc(2) 
      by(intro  optimality_pres_orlins_one_step_check(3)[of " ((orlins_one_step_check ^^ (Suc k)) state)"]
               orlins_compow_invar_gamma_pres orlins_compow_aux_invar_pres Suc(2-) 
               orlins_compow_invar_integral_pres orlins_compow_implementation_invar_pres
               some_balance_after_k_steps 3 orlins_entry_after_k_steps
               orlins_compow_invar_forest_pres orlins_compow_invar_isOptflow_pres | simp)+
  qed
qed

corollary compow_completeness_gtr0:
  assumes "invar_gamma state"
          "aux_invar state"
          "invar_non_zero_b state"
          "invar_integral state"
          "invar_forest state"
          "orlins_entry state"
          "invar_isOptflow state"
          "implementation_invar state"
          "return state = notyetterm"
          "state' = (orlins_one_step_check ^^ k) state"
          "k > 0" "return state' = failure"
        shows "\<nexists> f. f is \<b> flow"
proof-
  obtain k' where k': "k = Suc k'"
    using assms by(cases k) auto
  show ?thesis
   unfolding k' assms
   apply(rule compow_completeness[OF _ _ _ _ _ _ _ _ _ refl])
   using assms 
   by(auto simp add: k')
qed

lemma l_k_gtr_0: "(nat \<lceil>log 2 (real (4 * M * N) + (1 - \<epsilon>)) - log 2 \<epsilon>\<rceil> + 
                                      1 + nat (\<lceil>log 2 (real N)\<rceil> + 3) + 2) > 0"
  using M_def N_def finite_E \<V>_finite E_not_empty V_non_empt by simp

lemma number_of_comps_0: "card (comps \<V> X) > 0"
  unfolding comps_def
  using \<V>_finite V_non_empt by auto

lemma orlins_dom_impl_same:
  assumes "orlins_dom state"
          "aux_invar state"
          "invar_gamma state"
          "implementation_invar state"
          "invar_non_zero_b state"
          "orlins_entry state"
          "invar_forest state"
          "invar_integral state"
          "invar_isOptflow state"
          "state' = state"
    shows "orlins_impl state' = orlins state"
  using assms(2-)
proof(induction arbitrary: state' rule: orlins.pinduct[OF assms(1)])
  case (1 state)
  note IH = this
  define state2 where 
      "state2 = send_flow (maintain_forest (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
  show ?case 
    apply(subst orlins_impl.simps)
    apply(subst orlins.psimps[OF IH(1)])
  proof(cases "return state2  = notyetterm", goal_cases)
    case 1
    then show ?case 
    by(auto intro!: IH(2)[OF _ _ refl refl refl]
                    invars_pres_orlins_one_step[simplified orlins_one_step_def Let_def]
          simp add: IH(3-) state2_def)
next
  case 2
  have olrins_dom_state2:"orlins_dom state2"
    using 2 
    by(auto simp add: state2_def intro:  orlins.domintros return.exhaust)
  have same_state:"send_flow_impl (maintain_forest_impl (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)) =
    send_flow (local.maintain_forest (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
    using invars_pres_orlins_one_step(14)[simplified orlins_one_step_def Let_def, of state] 
          IH(3-)
    by auto
  thus ?case
    using 2 
    by(auto simp add: orlins_impl.simps orlins.psimps[OF olrins_dom_state2[simplified state2_def]] state2_def 
                      IH(11)
               intro: return.exhaust)
  qed
qed
  
theorem orlins_dom_and_results:
  assumes "return state = notyetterm"
          "invar_gamma state"
          "aux_invar state"
          "invar_non_zero_b state"
          "invar_integral state"
          "invar_forest state"
          "orlins_entry state"
          "invar_isOptflow state"
          "implementation_invar state"
          "state' = orlins state"
    shows "orlins_dom state"
          "return state' = success \<Longrightarrow> is_Opt \<b> (a_current_flow state')"
          "return state' = failure \<Longrightarrow> \<nexists> f. f is \<b> flow"
          "return state' = notyetterm \<Longrightarrow> False"
          "orlins_impl state = state'"
proof-
  obtain k where k_term:
         "return ((orlins_one_step_check ^^ k) state) \<noteq> notyetterm" "0 < k"
    using finally_termination[OF refl refl assms(2-8) refl assms(9)]  assms(1) by force
  have orlins_dom:"orlins_dom state" 
   and orlins_it: "local.orlins state = (orlins_one_step_check ^^ k) state"
    using  succ_fail_term_same_check[OF refl assms(1), of k] k_term 
    by(auto intro: return.exhaust)
  thus "orlins_dom state" by simp
  thus "orlins_impl state = state'"
    by(auto intro!: orlins_dom_impl_same simp add: assms)
  show "return state' = success \<Longrightarrow> is_Opt \<b> (a_current_flow state')"
    by(auto intro!: compow_correctness_gtr0 simp add: assms orlins_it k_term(2))
  show "return state' = failure \<Longrightarrow> \<nexists> f. f is \<b> flow"
    by(intro compow_completeness_gtr0)(auto simp add: assms orlins_it k_term(2))
  show "return state' = notyetterm \<Longrightarrow> False"
    by(auto simp add: orlins_it assms k_term)
qed

lemma init_rep_comp: 
  assumes "init_rep_comp' = rep_comp_update_all (\<lambda> x val. (x, 1)) init_rep_card"
  shows   "rep_comp_invar init_rep_comp'"
          "rep_comp_domain init_rep_comp'= \<V>"
          "abstract_rep_map init_rep_comp' = id"
          "abstract_comp_map init_rep_comp' = (\<lambda> x. 1)"
  using init_rep_card rep_comp_update_all(3,4)
         abstract_rep_map_rep_comp_update_all  not_in_dom_id 
        abstract_comp_map_rep_comp_update_all not_in_dom_1
  by (auto simp add: assms)

lemma actives_init:
  assumes "actives_init = (filter (\<lambda>e. fst e \<noteq> snd e) \<E>_impl)"
  shows   "set_invar actives_init"
          "to_set actives_init = {e | e. e \<in> \<E> \<and> fst e \<noteq> snd e}"
  using \<E>_impl_meaning invar_filter 
  by (auto simp add: assms  local.set_filter(1))

lemma not_blocked_init:
  assumes "not_blocked_init = (not_blocked_update_all
             (\<lambda>e b. if fst e \<noteq> snd e then True else False) init_not_blocked)"
  shows "not_blocked_invar not_blocked_init"
        "not_blocked_dom not_blocked_init = \<E>"
        "abstract_not_blocked_map not_blocked_init = 
         (\<lambda> e. if fst e \<noteq> snd e \<and> e \<in> \<E> then True else False)"
    apply (auto simp add: assms init_not_blocked(1) not_blocked_update_all(3)
                          not_blocked_update_all(4) init_not_blocked(1,2) 
                          not_blocket_update_all_abstract_not_blocked_map[OF init_not_blocked(1)])
  using abstract_not_blocked_map_def init_not_blocked(2) by auto

lemma aux_invar_initial: "aux_invar initial" 
proof(rule aux_invarI, goal_cases)
  case 1
  thus ?case
    using initial_def \<E>_impl_meaning set_filter(1)
          set_filter(1)[OF  \<E>_impl_meaning(2), simplified \<E>_impl_meaning(1)]
    by (intro invar_aux1I)auto
next
  case 2
  thus ?case
    by(auto intro!: invar_aux2I simp add: initial_def empty_forest_empty)
next
  case 3
  thus?case
    by(auto intro!:  invar_aux3I simp add: \<F>_def initial_def empty_forest_empty)
next
  case 4
  thus ?case
    by(auto intro!:  invar_aux4I simp add: \<F>_def initial_def empty_forest_empty)
next
  case 5
  thus ?case
    by(auto intro!: invar_aux6I simp add:  initial_def empty_forest_empty)
next
  case 6
  thus ?case
    by(auto intro!: invar_aux8I simp add: initial_def init_rep_comp) 
next
  case 7
  thus ?case
    using not_reachable_empt
    by(force intro!: invar_aux7I simp add: initial_def init_rep_comp empty_forest_empty)
next
  case 8
  thus ?case
    by(auto intro!: invar_aux9I simp add: initial_def init_rep_comp empty_forest_empty)
next
  case 9
  thus ?case
    by(auto intro!: invar_aux5I simp add: initial_def empty_forest_empty)
next
  case 10
  thus ?case
    by(auto intro!: invar_aux10I simp add: initial_def empty_forest_empty  Vs_def
           dest!: in_connected_component_in_edges)
 next
  case 11
  thus ?case
    by(auto intro!: invar_aux11I 
          simp add: initial_def empty_forest_empty actives_init 
                    connected_component_empty_edges_is_self)
next
  case 12
  thus ?case
    by(auto intro!: invar_aux12I simp add: initial_def init_rep_comp)
next
  case 13
  thus ?case
    by(auto intro!: invar_aux13I 
         simp add: initial_def empty_forest_empty 
                   connected_component_empty_edges_is_self actives_init)
next
  case 14
  thus ?case
    by(auto intro!: invar_aux14I validFI 
             simp add: initial_def empty_forest_empty  dblton_graph_def Vs_def)
next
  case 15
  thus ?case
    by(auto intro!: invar_aux15I simp add: initial_def empty_forest_empty Vs_def)
next
  case 16
  thus ?case    
    by(auto intro!: invar_aux16I 
          simp add: initial_def init_rep_comp empty_forest_empty 
                    connected_component_empty_edges_is_self)
next
  case 17
  thus ?case
    using invar_filter \<E>_impl_meaning
    by(auto intro!: invar_aux17I simp add:  initial_def) 
next
  case 18
  thus ?case
    by(auto intro!: invar_aux18I'' empty_forest_good_graph simp add: initial_def)
next
  case 19
  thus ?case
    by(auto intro!: invar_aux20I symmetric_digraphI 
          simp add: empty_forest_empty initial_def)
next
  case 20   
  thus ?case
    by(auto intro!: invar_aux22I 
             simp add: initial_def \<F>_def  empty_forest_empty not_blocked_init actives_init)
qed

lemma init_gamma:
"get_max (\<lambda>x. abs) init_bal = Max {\<bar>\<b> v\<bar> |v. v \<in> \<V>}"
  by(subst get_max)
    (auto simp add: init_bal E_not_empty Setcompr_eq_image)
    
lemma invar_gamma_initial: "\<not> (\<forall> v \<in> \<V>. \<b> v = 0) \<Longrightarrow> invar_gamma initial"
  apply(rule bexE, simp)
  subgoal for x
    using Max_ge[of "{\<bar>\<b> v\<bar> |v. v \<in> \<V>}" "\<bar> \<b> x \<bar>"] \<V>_finite
    by (fastforce simp add: init_gamma invar_gamma_def initial_def)
  done

lemma invar_non_zero_b_initial: "\<not> (\<forall> v \<in> \<V>. \<b> v = 0) \<Longrightarrow> invar_non_zero_b initial"
  by (simp add: abstract_real_map_in_dom_the init_bal(2,3) initial_def
      invar_non_zero_b_def)

lemma init_flow':
  assumes "init_flow' = flow_update_all (\<lambda>e fe. 0) init_flow"
  shows   "abstract_flow_map init_flow' = (\<lambda> e. 0)"
          "flow_invar init_flow'"
          "flow_domain init_flow' = \<E>" 
  subgoal
    apply(rule ext)
    subgoal for x
      using flow_update_all(1)[OF init_flow(1), of x  "\<lambda> e fe . 0"]
            flow_update_all(4)[OF init_flow(1), of "\<lambda> e fe . 0"]
      by(force intro!: ext split: option.split simp add: assms  abstract_real_map_def)
    done
  by(auto simp add:  flow_update_all(4)[OF init_flow(1), of "\<lambda> e fe . 0"] 
                abstract_real_map_def assms flow_update_all(3) init_flow )
      
lemma invar_forest_initial: "invar_forest initial"
  by(auto intro!: invar_forestI simp add: initial_def \<F>_def empty_forest_empty)

lemma invar_integral_initial: "invar_integral initial"
  by(auto intro!: invar_integralI simp add: initial_def init_flow')

lemma no_augcycle_at_beginning:
   "\<nexists> C. augcycle (\<lambda> e. 0) C"
proof(rule ccontr)
  assume "\<not> (\<nexists>C. augcycle (\<lambda>e. 0) C)"
  then obtain C where C_prop:"augcycle (\<lambda> e. 0) C" by auto
  hence aa:"closed_w (make_pair ` \<E>) (map to_vertex_pair C)"
        "foldr (\<lambda> e acc. acc + \<cc> e) C 0 = 
         foldr (\<lambda> e acc. acc + \<c> e) (map oedge C) 0"
    by(rule augcycle_to_closed_w, simp)+
  have "foldr (\<lambda> e acc. acc + \<cc> e) C 0 < 0"
    using C_prop unfolding augcycle_def \<CC>_def using distinct_sum[of C \<cc>] by simp
  hence "foldr (\<lambda> e acc. acc + \<c> e) (map oedge C) 0 < 0" using aa by simp
  moreover have "map to_vertex_pair C = map make_pair (map oedge C)"
  proof-
    have "e \<in> set C \<Longrightarrow> to_vertex_pair e = make_pair (oedge e)" for e
    proof(goal_cases)
      case 1
      hence "rcap (\<lambda> e. 0) e > 0" 
        using C_prop by(auto simp add: augcycle_def intro: augpath_rcap_pos_strict')
      then obtain ee where "e = F ee" by (cases e) auto
      then show ?case by simp
    qed
    thus "map to_vertex_pair C = map make_pair (map oedge C)" 
      by simp
  qed
  moreover have "set (map oedge C) \<subseteq> \<E> " 
    using C_prop  
    by (auto simp add: image_def augcycle_def \<EE>_def)
  ultimately show False using conservative_weights aa(1)
    by metis  
qed

lemma abstract_bal_map_init_is:
"abstract_bal_map init_bal = (\<lambda> v. if  v \<in> \<V> then \<b> v else 0)"
  using init_bal(2)[symmetric] init_bal(3)
  by(fastforce simp add: abstract_real_map_def 
                split: option.split)

lemma invar_isOptflow_initial: "invar_isOptflow initial"
  using u_non_neg   no_augcycle_at_beginning 
  by(auto intro!: invar_isOptflowI no_augcycle_min_cost_flow isbflowI isuflowI 
             simp add: init_flow' initial_def zero_ereal_def ex_def 
                       abstract_bal_map_init_is
                split: option.split)

lemma \<Phi>_initial: "invar_non_zero_b initial\<Longrightarrow> \<Phi> initial \<le> N"
  unfolding initial_def \<Phi>_def N_def apply simp
  apply(subst card_eq_sum, subst int_sum)
  apply(rule sum_mono)
  subgoal for v
    apply(rule exE[OF obtain_Max[OF \<V>_finite V_non_empt , of "\<lambda> x. \<bar> \<b> x \<bar>"]], simp)
    subgoal for x
      apply(rule invar_non_zero_bE, simp)
      apply(rule bexE[of \<V>  "\<lambda> v. \<b> v \<noteq> 0"], 
                simp add: abstract_real_map_in_dom_the init_bal(2,3))
      subgoal for y
        apply(subst sym[OF one_add_one],rule add_mono, subst divide_le_eq_1_pos)
        using \<V>_finite \<epsilon>_axiom 
          by(auto simp add: init_gamma abstract_bal_map_init_is
                    intro!: order.strict_trans2[of 0  "\<bar> \<b> y \<bar>" "Max _"] 
                            Max_ge[of " {\<bar>\<b> x\<bar> |x. x \<in> \<V>}" "\<bar> \<b> y \<bar>"] 
                            Max_ge[of " {\<bar>\<b> x\<bar> |x. x \<in> \<V>}" ])
      done
    done
  done

lemma send_flow_entry_initial: "send_flow_entryF initial"
  by(auto intro!: send_flow_entryFI simp add: \<F>_def initial_def empty_forest_empty)

lemma implementation_invar_initial:
   "implementation_invar initial"
proof(rule implementation_invarI, goal_cases)
  case 1
  then show ?case
    using init_flow'(3)
    by(auto simp add: initial_def flow_update_all(1) init_flow(1,2))
next
  case 2
  then show ?case 
    using init_flow'(2)
    by(auto simp add: initial_def)
next
  case 3
  then show ?case 
    by(auto simp add: initial_def domD init_bal(2))
next
  case 4
  then show ?case 
    by(auto simp add: initial_def init_bal(1))
next
  case 5
  then show ?case
    by(auto simp add: initial_def empty_forest_empty conv_map.map_empty)
next
  case 6
  then show ?case 
    by(auto simp add: initial_def conv_map.invar_empty)
next
  case 7
  then show ?case 
    using init_rep_comp(2)[OF refl]
    by(auto simp add: initial_def) 
next
  case 8
  then show ?case
    by(auto simp add: initial_def  init_rep_card(1) rep_comp_update_all(3))
next
  case 9
  then show ?case 
    using not_blocked_init(1)
    by(auto simp add: initial_def) 
next
  case 10
  then show ?case 
    using not_blocked_init(2)[OF refl]
    by(auto simp add: initial_def) 
qed

lemma invar_above_6Ngamma_initial: "invar_above_6Ngamma initial"
  by(auto intro!: invar_above_6NgammaI simp add: initial_def \<F>_def empty_forest_empty)

lemma phi_initial_leq_2N:
      "\<not> (\<forall> v \<in> \<V> . \<b> v = 0) \<Longrightarrow> \<Phi> initial \<le> 2 * int N"
     using \<Phi>_initial[OF invar_non_zero_bI] abstract_bal_map_init_is 
     by(auto simp add: initial_def)

theorem initial_state_orlins_dom_and_results:
  assumes "state' = orlins (send_flow initial)"
    shows "orlins_dom (send_flow initial)"
          "return state' = success \<Longrightarrow> is_Opt \<b> (a_current_flow state')"
          "return state' = failure \<Longrightarrow> \<nexists> f. f is \<b> flow"
          "return state' = notyetterm \<Longrightarrow> False"
          "send_flow_dom initial"
          "orlins_impl (send_flow_impl initial) = state'"
proof-
  show send_flow_dom:"send_flow_dom initial"
  proof(cases "(\<forall>v\<in>\<V>. \<b> v = 0)")
    case True
    then show ?thesis 
      using implementation_invar_initial[simplified initial_def]
      by(auto intro!: all_bal_zero_send_flow_dom
                  simp add:  abstract_bal_map_init_is initial_def)
  next
    case False
    thus ?thesis
      by(auto intro!: send_flow_termination invar_gamma_initial
                      implementation_invar_initial  aux_invar_initial  invar_integral_initial
                      invar_isOptflow_initial invar_above_6Ngamma_initial
            simp add: aux_invar_initial )
  qed
  hence after_send_flow_same:"send_flow_impl initial = send_flow initial"
    using send_flow_dom_impl_cong by blast

  have  "orlins_dom (send_flow initial) \<and>
         (return state' = success \<longrightarrow> is_Opt \<b> (a_current_flow state'))\<and>
          (return state' = failure \<longrightarrow> (\<nexists> f. f is \<b> flow)) \<and>
          (return state' = notyetterm \<longrightarrow> False) \<and>
          orlins_impl (send_flow_impl initial) = state'"
proof(cases "return (send_flow initial)")
  case success
  have orlins_dom:"orlins_dom (send_flow initial)"
    by(auto intro: orlins.domintros simp add: success)
  moreover have "is_Opt \<b> (a_current_flow state')"
  proof(cases "\<forall>v\<in>\<V>. \<b> v = 0")
    case True
    then show ?thesis 
     unfolding assms orlins.psimps[OF orlins_dom] success
     apply(subst send_flow_simps(1)[OF send_flow_dom])
     apply(rule all_bal_zero_send_flow_dom(2)[OF implementation_invar_initial])
     by (auto intro: all_bal_zero_send_flow_dom(2)[OF implementation_invar_initial]
           simp add: abstract_bal_map_init_is initial_def send_flow_succ_upd_def
                     init_flow'(1) ex_def infinite_u isbflowI isuflowI
                     no_augcycle_at_beginning no_augcycle_min_cost_flow)
 next
   case False
   moreover hence "\<Phi> initial \<le> 2 * int N"
     using \<Phi>_initial[OF invar_non_zero_bI] abstract_bal_map_init_is 
     by(auto simp add: initial_def)
   ultimately show ?thesis
    by(auto intro!: send_flow_correctness
                      invar_gamma_initial send_flow_entry_initial
                      implementation_invar_initial  aux_invar_initial  invar_integral_initial
                      invar_isOptflow_initial invar_above_6Ngamma_initial success 
         simp add: assms orlins.psimps[OF orlins_dom] success )
qed
  moreover have "return (local.orlins (send_flow initial)) = success"
    by(auto  simp add: assms orlins.psimps[OF orlins_dom] success)
  moreover have "orlins_impl (send_flow_impl initial) = local.orlins (send_flow initial)"
    using success  after_send_flow_same 
    by(auto  simp add: assms orlins.psimps[OF orlins_dom] success
        orlins_impl.simps[of "send_flow initial"])
   ultimately show ?thesis 
     using success
     by(auto simp add: assms)
next
  case failure
  have orlins_dom:"orlins_dom (send_flow initial)"
    by(auto intro: orlins.domintros simp add: failure)
  moreover have "orlins_impl (send_flow_impl initial) = local.orlins (send_flow initial)"
    using failure after_send_flow_same 
    by(auto  simp add: assms orlins.psimps[OF orlins_dom] 
        orlins_impl.simps[of "send_flow initial"])
  moreover have "(\<nexists>f. f is \<b> flow)" if "return state' = failure"
proof(cases "\<forall>v\<in>\<V>. \<b> v = 0")
  case True
  hence send_flow_succ_cond:"send_flow_succ_cond initial"
     using  all_bal_zero_send_flow_dom(2)[OF implementation_invar_initial]
       by(auto simp add: abstract_bal_map_init_is initial_def)
  hence "return (send_flow initial) = success" 
    by(auto simp add: send_flow_simps(1)[OF send_flow_dom send_flow_succ_cond] 
                       send_flow_succ_upd_def)
   then show ?thesis 
     using failure by simp
 next
   case False
   then show ?thesis
    by(intro send_flow_completeness)
      (auto intro!: invar_gamma_initial send_flow_entry_initial
                      implementation_invar_initial  aux_invar_initial  invar_integral_initial
                      invar_isOptflow_initial invar_above_6Ngamma_initial failure phi_initial_leq_2N
         simp add: assms orlins.psimps[OF orlins_dom] failure)
qed
  ultimately show ?thesis 
    by (auto simp add: assms orlins.psimps[OF orlins_dom] failure)
next
  case notyetterm
  have not_all_zero: "\<forall>v\<in>\<V>. \<b> v = 0 \<Longrightarrow> False"
  proof(goal_cases)
    case 1
    hence send_flow_succ_cond:"send_flow_succ_cond initial"
     using  all_bal_zero_send_flow_dom(2)[OF implementation_invar_initial]
       by(auto simp add: abstract_bal_map_init_is initial_def)
    hence "return (send_flow initial) = success" 
      by(auto simp add: send_flow_simps(1)[OF send_flow_dom send_flow_succ_cond] 
                       send_flow_succ_upd_def)
   then show ?thesis 
     using notyetterm by simp
 qed
  have init_phi_bound:"real_of_int (\<Phi> initial) \<le> 2 * real N"
    using \<Phi>_initial[OF invar_non_zero_bI] not_all_zero
            abstract_bal_map_init_is initial_def by fastforce
  have intermediate_invars:
       "invar_gamma (send_flow initial)"
       "aux_invar (send_flow initial)"
       "invar_non_zero_b (send_flow initial)"
       "invar_integral (send_flow initial)"
       "invar_forest (send_flow initial)"
       "orlins_entry (send_flow initial)"
       "invar_isOptflow (send_flow initial)"
       "implementation_invar (send_flow initial)"
    by(auto intro!: send_flow_invar_gamma_pres send_flow_dom invar_gamma_initial not_all_zero
                    send_flow_invar_isOpt_pres aux_invar_initial send_flow_invar_integral_pres
                    send_flow_implementation_invar_pres remaining_balance_after_send_flow
                    implementation_invar_initial invar_integral_initial invar_isOptflow_initial
                    invar_above_6Ngamma_initial send_flow_invar_aux_pres orlins_entry_after_send_flow
                    notyetterm send_flow_invar_forest init_phi_bound)
   
  have "orlins_dom (send_flow initial)"
    by(auto intro!: orlins_dom_and_results(1) notyetterm intermediate_invars)
  moreover have "return state' = success \<Longrightarrow> is_Opt \<b> (a_current_flow state')"
    by(auto intro!: orlins_dom_and_results(2)  intermediate_invars 
          simp add: assms notyetterm)
  moreover have "return state' = failure \<Longrightarrow> (\<nexists>f. f is \<b> flow)"
    by(intro orlins_dom_and_results(3))
      (auto simp add:  intermediate_invars assms notyetterm)
  moreover have "return state' = notyetterm \<Longrightarrow> False"
    by(auto intro!: orlins_dom_and_results(4)[OF notyetterm]
          simp add: assms  intermediate_invars)
  moreover have "orlins_impl (send_flow_impl initial) = state'"
    by(auto intro!: orlins_dom_and_results 
         simp add: assms  intermediate_invars after_send_flow_same notyetterm)
 ultimately show ?thesis by blast
 qed
  thus  "orlins_dom (send_flow initial)"
        "return state' = success \<Longrightarrow> is_Opt \<b> (a_current_flow state')"
        "return state' = failure \<Longrightarrow> \<nexists> f. f is \<b> flow"
        "return state' = notyetterm \<Longrightarrow> False"
        "orlins_impl (send_flow_impl initial) = state'"
    by auto
qed

definition "orlins_ret1_cond state =  (if return state = success then True
                 else if return state= failure then False
                 else (let  \<gamma>' = new_\<gamma> state;
                      state' = maintain_forest (state \<lparr>current_\<gamma> := \<gamma>' \<rparr>);
                      state'' = send_flow state'  
                      in False))"

lemma orlins_ret1_condE: "orlins_ret1_cond state \<Longrightarrow>
                 \<lbrakk> return state = success \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  unfolding orlins_ret1_cond_def by presburger

lemma orlins_ret1_condI: " return state = success \<Longrightarrow> orlins_ret1_cond state"
  unfolding  orlins_ret1_cond_def by presburger

definition "orlins_call_cond state = (if return state = success then False
                 else if return state= failure then False
                 else (let  \<gamma>' = new_\<gamma> state;
                      state' = maintain_forest (state \<lparr>current_\<gamma> := \<gamma>' \<rparr>);
                      state'' = send_flow state' 
                      in True))"

lemma orlins_call_condE: "orlins_call_cond state \<Longrightarrow>
                 \<lbrakk> \<And>  \<gamma>' state' state''. return state = notyetterm \<Longrightarrow>
                      \<gamma>' = new_\<gamma> state \<Longrightarrow>
                      state' = maintain_forest (state \<lparr>current_\<gamma> := \<gamma>' \<rparr>) \<Longrightarrow>
                      state'' = send_flow state' \<Longrightarrow>
                      state' = maintain_forest (state \<lparr>current_\<gamma> := \<gamma>' \<rparr>) \<Longrightarrow>
                      state'' = send_flow state'
                  \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  unfolding orlins_call_cond_def  Let_def 
  by(rule return.exhaust[of "return state"], simp, simp, simp)

lemma orlins_call_condI: " \<And>  \<gamma>' state' state''. return state = notyetterm \<Longrightarrow>
                      \<gamma>' = new_\<gamma> state \<Longrightarrow>
                      state' = maintain_forest (state \<lparr>current_\<gamma> := \<gamma>' \<rparr>) \<Longrightarrow>
                      state'' = send_flow state' \<Longrightarrow>
                      state' = maintain_forest (state \<lparr>current_\<gamma> := \<gamma>' \<rparr>) \<Longrightarrow>
                      state'' = send_flow state'
                  \<Longrightarrow> orlins_call_cond state"
  unfolding  orlins_call_cond_def Let_def by force

definition "orlins_ret2_cond state = (if return state = success then False
                 else if return state= failure then True
                 else False)"

lemma if_PQ:"if P then False else if Q then False else True \<Longrightarrow> \<not> P \<and> \<not> Q"
  by metis

lemma if_PQ_E: "if P then False else if Q then False else True \<Longrightarrow> (\<not> P \<and> \<not> Q \<Longrightarrow> R) \<Longrightarrow> R"
  by metis

lemma orlins_ret2_condE: "orlins_ret2_cond state \<Longrightarrow>
                 \<lbrakk>  return state = failure \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  unfolding orlins_ret2_cond_def Let_def by meson

lemma orlins_ret2_condI: " return state = failure
                  \<Longrightarrow> orlins_ret2_cond state"
  unfolding  orlins_ret2_cond_def Let_def by force

lemma orlins_cases:
  assumes
   "orlins_ret1_cond state \<Longrightarrow> P"
   "orlins_ret2_cond state \<Longrightarrow> P"
   "orlins_call_cond state \<Longrightarrow> P"
 shows P
proof-
  have "orlins_ret1_cond state  \<or> orlins_call_cond state \<or>
        orlins_ret2_cond state "
    by (auto simp add: orlins_ret2_cond_def orlins_ret1_cond_def orlins_call_cond_def
                       Let_def
           split: list.split_asm option.split_asm if_splits)
  then show ?thesis
    using assms
    by auto
qed

definition "orlins_upd state = (let f = current_flow state;
                      \<gamma>' = new_\<gamma> state;
                      state' = maintain_forest (state \<lparr>current_\<gamma> := \<gamma>' \<rparr>);
                      state'' = send_flow state' 
                      in state'')"

lemma orlins_simps:
  assumes "orlins_dom state" 
  shows"orlins_call_cond state \<Longrightarrow> orlins state = orlins (orlins_upd state)"
       "orlins_ret1_cond state \<Longrightarrow> orlins state = state"
       "orlins_ret2_cond state \<Longrightarrow> orlins state =  state"
  subgoal  
    apply(rule orlins_call_condE, simp)
    apply(subst orlins.psimps[OF assms])
    unfolding orlins_upd_def Let_def
    apply(auto split: option.splits if_splits)
    done    
  by (auto simp add: orlins.psimps[OF assms]
                     orlins_ret2_cond_def orlins_ret1_cond_def orlins_call_cond_def
                     orlins_upd_def
                      Let_def
            split: list.splits option.splits if_splits)

lemma orlins_induct: 
  assumes "orlins_dom state"
  assumes "\<And>state. \<lbrakk>orlins_dom state;
                     orlins_call_cond state \<Longrightarrow> P (orlins_upd state)\<rbrakk> \<Longrightarrow> P state"
  shows "P state"
  apply(rule orlins.pinduct)
   subgoal using assms(1) .
   apply(rule assms(2))
   unfolding orlins_upd_def Let_def 
   by (fastforce elim!: orlins_call_condE)+

theorem initial_send_flow:
    shows "orlins_dom (send_flow initial)"
          "send_flow_dom initial"
  using initial_state_orlins_dom_and_results by auto

lemma current_gamma_initial:
"current_\<gamma> initial = Max {\<bar>a_balance initial v\<bar> |v. v \<in> \<V>}"
  using new_gamma_is(3)[OF implementation_invar_initial aux_invar_initial]
  by(simp add: initial_def)

lemma balance_initial:
"v \<in> \<V> \<Longrightarrow> a_balance initial v = \<b> v" 
  by (simp add: abstract_bal_map_init_is initial_def)

lemma F_initial_empty:
"\<F> initial = {}" "\<F>_redges initial = {}"
  by(auto simp add: \<F>_def \<F>_redges_def initial_def empty_forest_empty(1))

(*lemma final_flow_domain: "flow_domain (current_flow_impl (orlins_impl (send_flow_impl initial_impl))) = \<E>"
  using final_implementation_invar
  by(simp add: implementation_invar_def)*)
end
end