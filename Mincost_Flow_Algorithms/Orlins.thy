section \<open>Top Loop of Orlin's Algorithm\<close>

theory Orlins
  imports LoopA LoopB
begin

locale orlins_spec = 
loopB_spec where fst = fst + loopA_spec where fst = fst
for fst::"'edge_type \<Rightarrow> 'a"

locale orlins = 
loopB_Reasoning where fst = fst and empty_forest = "empty_forest::'c"+ loopA where fst = fst
for fst::"'edge_type \<Rightarrow> 'a"+
fixes norma::"'a \<times> 'a \<Rightarrow> 'a \<times> 'a "
assumes norma_axioms: "\<And> x y. norma (x, y) = (x,y) \<or> norma (x, y) = (y,x)"
                      "\<And> x y. norma (x, y) = norma (y, x)"
begin 

function (domintros) orlins::"('a, 'd, 'c, 'edge_type) Algo_state \<Rightarrow> ('a, 'd, 'c, 'edge_type) Algo_state" where
"orlins state = (if return state = success then state 
                 else if return state= failure then state
                 else (let f = current_flow state;
                      b = balance state;
                      \<gamma> = current_\<gamma> state;
                      E' = actives state;
                      \<gamma>' = (if \<forall> e \<in> to_set E'. f e = 0 then
                             min (\<gamma> / 2) (Max { \<bar> b v\<bar> | v. v \<in> \<V>})
                           else (\<gamma> / 2));
                      state' = loopA (state \<lparr>current_\<gamma> := \<gamma>' \<rparr>);
                      state'' = loopB state' 
                      in orlins state'')
)"
  by auto

definition "new_\<gamma> state = (let f = current_flow state;
                      b = balance state;
                      \<gamma> = current_\<gamma> state;
                      E' = actives state
                      in (if \<forall> e \<in> to_set E'. f e = 0 then
                             min (\<gamma> / 2) (Max { \<bar> b v\<bar> | v. v \<in> \<V>})
                           else (\<gamma> / 2)))"

definition "important state v \<equiv> v\<in> \<V> \<and> ( \<bar>balance state v \<bar> > (1 - \<epsilon>)*new_\<gamma> state )"

definition orlins_one_step::"('a, 'd, 'c, 'edge_type) Algo_state \<Rightarrow> ('a, 'd, 'c, 'edge_type) Algo_state" where
"orlins_one_step state =(  (let f = current_flow state;
                      b = balance state;
                      \<gamma> = current_\<gamma> state;
                      E' = actives state;
                      \<gamma>' = (if \<forall> e \<in> to_set E'. f e = 0 then
                             min (\<gamma> / 2) (Max { \<bar> b v\<bar> | v. v \<in> \<V>})
                           else (\<gamma> / 2));
                      state' = loopA (state \<lparr>current_\<gamma> := \<gamma>' \<rparr>);
                      state'' = loopB state' in
                      state''
))"


definition orlins_one_step_check::"('a, 'd, 'c, 'edge_type) Algo_state \<Rightarrow> ('a, 'd, 'c, 'edge_type) Algo_state" where
"orlins_one_step_check state =(  if return state = success then state
                                 else if return state = failure then state
                                 else orlins_one_step state)"

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
    have "loopB (loopA
         (state\<lparr>current_\<gamma> := min (current_\<gamma> state / 2) (Max {\<bar>balance state v\<bar> |v. v \<in> \<V>})\<rparr>)) =
          state'"
      using 0[simplified] 1
      unfolding orlins_one_step_def orlins_one_step_check_def Let_def by simp
    thus ?case 
      using 0(2)
      by(auto intro: orlins.domintros)
  next
    case (2 e)
    have "(loopB (loopA (state\<lparr>current_\<gamma> := current_\<gamma> state / 2\<rparr>))) = state'"
      using 0[simplified] 2
      unfolding orlins_one_step_def orlins_one_step_check_def Let_def by auto
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
           unfolding orlins_one_step_def Let_def orlins_one_step_check_def 
           by(auto intro: orlins.domintros)
      next
        case (2 e)
        then show ?case
          using 2 success
          unfolding orlins_one_step_def Let_def orlins_one_step_check_def 
          apply(subst (asm) if_not_P, simp)
          apply(subst (asm) if_not_P, simp) 
          apply(subst (asm) if_not_P, fast) 
          by(auto intro: orlins.domintros)       
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
           unfolding orlins_one_step_def Let_def orlins_one_step_check_def 
           by(auto intro: orlins.domintros)
      next
        case (2 e)
        then show ?case
          using 2 failure
          unfolding orlins_one_step_def Let_def orlins_one_step_check_def 
          apply(subst (asm) if_not_P, simp)
          apply(subst (asm) if_not_P, simp) 
          apply(subst (asm) if_not_P, fast) 
          by(auto intro: orlins.domintros)       
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
          unfolding orlins_one_step_check_def orlins_one_step_def Let_def by simp
      next
        case (2 e)
        then show ?case 
          using 12(1)
          unfolding orlins_one_step_check_def orlins_one_step_def Let_def 
         (*The explicit if-rewrite is due to witness vertices a and b from case 2*)
          apply(subst (asm) (3) if_not_P)
          by auto
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
      proof(insert 3, subst if_not_P, simp, subst if_not_P, simp, 
            subst (asm)  if_not_P, simp, subst (asm)  if_not_P, simp, 
             cases k, goal_cases)
        case 1
        thus ?case
          unfolding Let_def
          by(subst orlins.psimps, auto intro: orlins.domintros)
      next
        case (2 nat)
        thus ?case 
          unfolding Let_def
        by(intro IH(2)[where k41 = "k-1"], auto simp add: algebra_simps)
    qed
  qed (auto simp add: notyetterm_no_change)
next
  case 1
  show ?case
    by(rule assms)
  qed (rule assms)

lemma succ_fail_term_same_check:
       "compow k orlins_one_step_check state = state' \<Longrightarrow> return state = notyetterm \<Longrightarrow>
       return state' = success \<or> return state' = failure \<Longrightarrow> \<not> (\<forall> v \<in> \<V>. balance state v = 0) \<Longrightarrow>
       orlins_dom state \<and> orlins state = state'"
 by(induction k, auto intro!: succ_fail_term_same succ_fail_term_same_dom)

lemma gamma_upd_aux_invar_pres: "invar_gamma state \<Longrightarrow> invar_non_zero_b state
                                 \<Longrightarrow>invar_gamma (state\<lparr>current_\<gamma> :=
         if \<forall>e\<in> to_set (actives state). current_flow state e = 0
         then min (current_\<gamma> state / 2) (Max {\<bar>balance state v\<bar> |v. v \<in> \<V>}) else current_\<gamma> state / 2\<rparr>)"
  using Max_lower_bound[OF \<V>_finite V_non_empt , of _ 0 "\<lambda> v. \<bar>balance state v\<bar>"] 
  unfolding invar_gamma_def invar_non_zero_b_def
  by(auto split: if_split simp add: algebra_simps)

lemma aux_invar_pres_orlins_one_step:
  assumes "aux_invar state" "invar_gamma state" "invar_non_zero_b state"
  shows "aux_invar (orlins_one_step state)"
  unfolding orlins_one_step_def Let_def
  apply(rule loopB_invar_aux_pres)
    apply(rule loopB_termination)
  subgoal invar_gammaA
    apply(rule loopA_invar_gamma_pres)
     apply(rule aux_invar_gamma)
    using assms apply simp
    apply(rule gamma_upd_aux_invar_pres[of state])
    using assms by auto
  subgoal aux_invar
    apply(rule loopA_invar_aux_pres)
    subgoal
      apply(rule termination_of_loopA[OF _ refl])
      apply(rule aux_invarE)
      using assms aux_invar_def 
      by (auto  intro: aux_invar_gamma)
    using assms 
    by (auto intro: aux_invar_gamma)
    subgoal
      using invar_gammaA by simp
    done

lemma invar_gamma_pres_orlins_one_step:
  assumes "aux_invar state" "invar_gamma state" "invar_non_zero_b state"
  shows "invar_gamma (orlins_one_step state)"
  unfolding orlins_one_step_def Let_def
  using assms
   by (fastforce intro!: loopB_invar_gamma_pres loopB_termination loopA_invar_gamma_pres 
                         aux_invar_gamma gamma_upd_aux_invar_pres)

lemma is_multiple_multiple: "(\<exists> n::nat.  y = (real n) * x) \<Longrightarrow>
                             (\<exists> n::nat. y*2 = (real n) * x )"
  by (metis distrib_left mult.commute mult_2_right of_nat_add)

lemma minE: "((a::real) \<le> b \<Longrightarrow> P a) \<Longrightarrow> (b \<le> a \<Longrightarrow> P b) \<Longrightarrow> P (min a b)"
  by linarith

lemma Phi_init:
      assumes "orlins_entry state" "invar_non_zero_b state"
              "invar_gamma state"
        shows "\<Phi> (state\<lparr>current_\<gamma> := new_\<gamma> state \<rparr>) \<le> N"
          and "\<And> x. x \<in> \<V> \<Longrightarrow> \<lceil> \<bar> balance state x\<bar> / (new_\<gamma> state) - (1 - \<epsilon>)\<rceil> \<le> 1" 
          and "\<And>x. x \<in> \<V> \<Longrightarrow> \<lceil>\<bar>balance state x\<bar> / new_\<gamma> state - (1 - \<epsilon>)\<rceil> \<ge> 0" 
proof-
  have gamma_0: "current_\<gamma> state > 0" using assms unfolding invar_gamma_def by simp
  obtain v where v_prop:"\<bar>balance (state\<lparr>current_\<gamma> := new_\<gamma> state \<rparr>) v\<bar> =
                  (Max { \<bar> balance (state\<lparr>current_\<gamma> := new_\<gamma> state \<rparr>) v\<bar> | v. v \<in> \<V>})" "v \<in> \<V>"
    using obtain_Max[OF \<V>_finite V_non_empt, of "\<lambda> v. \<bar> balance (state\<lparr>current_\<gamma> := new_\<gamma> state \<rparr>) v\<bar>"] 
    by auto
  hence gtr_0:"\<bar>balance (state\<lparr>current_\<gamma> := new_\<gamma> state \<rparr>) v\<bar> > 0" 
    using assms(2)[simplified invar_non_zero_b_def]
         Max_lower_bound[OF \<V>_finite V_non_empt,
           of _ 0 "\<lambda> v. \<bar> balance (state\<lparr>current_\<gamma> := new_\<gamma> state \<rparr>) v\<bar>"] by auto
  have grst:"x \<in> \<V> \<Longrightarrow>
    \<bar>balance (state\<lparr>current_\<gamma> := new_\<gamma> state \<rparr>) v\<bar> \<ge> \<bar>balance (state\<lparr>current_\<gamma> := new_\<gamma> state \<rparr>) x\<bar>"
    for x
    using v_prop Max_ge[of "{\<bar>balance (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>) v\<bar> |v. v \<in> \<V>}" ] \<V>_finite
    by fastforce
  have balance_eps:"x \<in> \<V>  \<Longrightarrow> \<bar> balance state x\<bar> / new_\<gamma> state  \<le> 2 * (1-\<epsilon>)" for x
    unfolding new_\<gamma>_def Let_def
    apply(subst sym[OF v_prop(1)[simplified]], rule P_of_ifI)
    apply(rule minE, simp, thin_tac \<open>\<forall>e\<in> to_set (actives state). current_flow state e = 0\<close>,
                              thin_tac \<open>current_\<gamma> state \<le> \<bar>balance state v\<bar> * 2\<close>)
    subgoal ast
      using assms(1)[simplified orlins_entry_def] \<epsilon>_axiom  gamma_0 
      by (smt (verit, best) diff_divide_eq_iff mult_imp_le_div_pos mult_minus_left)
    apply(rule order.trans[of _ 1])
    using \<epsilon>_axiom grst[simplified, of x] gamma_0 
    apply (metis abs_0_eq divide_le_eq_1 zero_less_abs_iff)
    using \<epsilon>_axiom ast by auto
  have "x \<in> \<V> \<Longrightarrow> \<lceil> \<bar> balance state x\<bar> / (new_\<gamma> state) - (1 - \<epsilon>)\<rceil> \<le> 1" for x
    using balance_eps[of x] \<epsilon>_axiom(1,2)
    by (smt (verit, del_insts)  ceiling_le_one gamma_0 le_divide_eq_1_pos mult_le_cancel_right1 )
  thus "\<And>x. x \<in> \<V> \<Longrightarrow> \<lceil>\<bar>balance state x\<bar> / new_\<gamma> state - (1 - \<epsilon>)\<rceil> \<le> 1" by simp
  thus "\<Phi> (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>) \<le> int N" unfolding \<Phi>_def N_def
    using sum_bounded_above[of \<V> "\<lambda> x. \<lceil>\<bar>balance state x\<bar> / new_\<gamma> state - (1 - \<epsilon>)\<rceil>" 1] by simp
  have "new_\<gamma> state > 0"
    unfolding new_\<gamma>_def Let_def
    apply(subst sym[OF v_prop(1)[simplified]], rule P_of_ifI)
    apply(rule minE, simp, thin_tac \<open>\<forall>e\<in>to_set (actives state). current_flow state e = 0\<close>,
                              thin_tac \<open>current_\<gamma> state \<le> \<bar>balance state v\<bar> * 2\<close>)
    subgoal ast
      using assms(1)[simplified orlins_entry_def] \<epsilon>_axiom  gamma_0 
      by (smt (verit, best) diff_divide_eq_iff mult_imp_le_div_pos mult_minus_left)
    using gtr_0 
    by (auto simp add: gamma_0)
  thus "\<And>x. x \<in> \<V> \<Longrightarrow> \<lceil>\<bar>balance state x\<bar> / new_\<gamma> state - (1 - \<epsilon>)\<rceil> \<ge> 0" 
    by (smt (verit) \<epsilon>_axiom(1) ceiling_less_zero divide_nonneg_nonneg)
qed

lemma balance_less_new_gamma: "x \<in> \<V> \<Longrightarrow>orlins_entry state \<Longrightarrow> \<bar> balance state x \<bar>\<le> 2*new_\<gamma> state"
  unfolding new_\<gamma>_def Let_def
  apply(rule P_of_ifI, rule minE)
  unfolding orlins_entry_def
  using Max.coboundedI[of "{\<bar>balance state v\<bar> |v. v \<in> \<V>}" "\<bar>balance state x\<bar>"] \<V>_finite 
  by (simp, smt (verit) \<epsilon>_axiom(1) \<epsilon>_axiom(2) add_divide_distrib divide_eq_1_iff 
                 mult_le_cancel_right1 mult_nonneg_nonpos zero_le_mult_iff ,
      fastforce,
      simp, smt (verit) \<epsilon>_axiom(1) \<epsilon>_axiom(2) add_divide_distrib divide_eq_1_iff
                   mult_le_cancel_right1 mult_nonneg_nonpos zero_le_mult_iff )

lemma new_gamma_below_half_gamma: "new_\<gamma> state \<le> current_\<gamma> state / 2"
  unfolding new_\<gamma>_def Let_def
  by auto

lemma invar_forest_pres_orlins_one_step_check:
  assumes "invar_forest state"
          "aux_invar state"
          "invar_gamma state"
          "invar_non_zero_b state"
          "orlins_entry state"
  shows   "invar_forest (orlins_one_step_check state)"
  unfolding orlins_one_step_check_def orlins_one_step_def Let_def
  apply(cases "return state", simp add: assms, simp add: assms)
  apply(subst if_not_P, simp, subst if_not_P, simp)
proof(goal_cases)
  case 1
  have aux_invar_gamma_upd: "aux_invar (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
    by(auto intro: aux_invar_gamma simp add: assms)
  have invar_gamma_gamma_upd: "invar_gamma (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
    unfolding new_\<gamma>_def Let_def
    by(fastforce intro: gamma_upd_aux_invar_pres simp add: assms)
  hence new_gamma_0: "new_\<gamma> state > 0" unfolding invar_gamma_def by auto
  have loopA_dom: "loopA_dom (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
    using aux_invar_def aux_invar_gamma_upd 
    by(fastforce intro: termination_of_loopA[OF _ refl])
  have invar_gamma_after_loopA: "invar_gamma (loopA (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
    by(auto intro: loopA_invar_gamma_pres simp add: aux_invar_gamma_upd invar_gamma_gamma_upd)
  have aux_invar_after_loopA: "aux_invar (loopA (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
    by(auto intro: loopA_invar_aux_pres simp add: aux_invar_gamma_upd loopA_dom)
  have loopB_dom:"loopB_dom (loopA (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
    by(auto simp add: invar_gamma_after_loopA intro: loopB_termination)
  have same_gamma_loopB: "current_\<gamma> (loopB(loopA (state \<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))) =
                   current_\<gamma> (loopA (state \<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
    by(auto intro: loopB_changes_current_\<gamma> simp add: loopB_dom)
  have same_gamma_loopA: "current_\<gamma> (loopA (state \<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)) =
                            new_\<gamma> state"
    by(subst gamma_pres, auto simp add: aux_invar_gamma_upd)
  have init_Phi_below_N:"\<Phi> (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>) \<le> N"
    by(auto intro: Phi_init simp add: assms)
  have Phi_after_below2N: " \<Phi> ((loopA (state \<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))) \<le> 2*N"
    using Phi_increase_below_N[OF aux_invar_gamma_upd invar_gamma_gamma_upd] init_Phi_below_N by simp
  have card_below_N: "v \<in> \<V> \<Longrightarrow> card (connected_component (to_graph (\<FF>_imp state)) v) \<le> N" for v
    using N_def assms(2) aux_invar_def[of state] invar_aux10_def[of state] 
     card_mono[OF \<V>_finite, of "connected_component (to_graph (\<FF>_imp state)) v"] by simp
  have card_above_0: "v \<in> \<V> \<Longrightarrow> card (connected_component (to_graph (\<FF>_imp state)) v) > 0" for v
    using  assms(2) aux_invar_def[of state] invar_aux10_def[of state] 
      \<V>_finite V_non_empt finite_subset
    unfolding connected_component_def  by fastforce
  have invarA_1:"invarA_1 (2 * new_\<gamma> state) (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
    unfolding invarA_1_def apply rule
    subgoal for v 
    apply(simp, rule order.trans[OF balance_less_new_gamma[OF _ assms(5)]], simp)
      using card_above_0[of v]  new_gamma_0 by fastforce
    done  
  have invar_A2:"invarA_2 (8 * real N * new_\<gamma> state) (2 * new_\<gamma> state) (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
    unfolding invarA_2_def
    apply (rule, rule order.strict_trans1[of _ " 8 * real N * new_\<gamma> state"]) 
    using new_gamma_0 new_gamma_below_half_gamma[of state]  N_gtr_0 assms(1)[simplified invar_forest_def] 
    by(auto intro:  order.strict_trans1[of _ "8* real N * (current_\<gamma> state / 2)"]
         simp add: algebra_simps)
   have loopA_entry: "loopA_entry (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
    unfolding loopA_entry_def
    using new_gamma_0 new_gamma_below_half_gamma[of state]  N_gtr_0 assms(1)[simplified invar_forest_def] 
    by(auto intro:  order.strict_trans1[of _ "8* real N * (current_\<gamma> state / 2)"]
         simp add: algebra_simps)
  have loopB_entryF:"loopB_entryF (loopA (state \<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)) "
    using invarA_1 invar_A2 
    by(auto intro: loopB_entryF[OF aux_invar_gamma_upd loopA_entry invar_gamma_gamma_upd refl])
  have curr_flow:"current_flow (loopB (loopA (state \<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))) e
        \<ge> current_flow (loopA (state \<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)) e - 
          \<Phi> ((loopA (state \<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))) *
          current_\<gamma> (loopB(loopA (state \<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)))" for e
      apply(rule loopB_flow_Phi_final[OF _ refl])
      using invar_gamma_after_loopA loopB_dom loopB_entryF aux_invar_after_loopA
      unfolding loopB_entryF_def 
      by (simp, simp, smt (verit) Phi_after_below2N invar_gamma_after_loopA invar_gamma_def mult_nonneg_nonneg of_int_nonneg, simp)
  have current_flow_after_loopB:
         "current_flow (loopB (loopA (state \<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))) e
        \<ge> current_flow (loopA (state \<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)) e - 2*N*new_\<gamma> state" for e
    apply(rule order.trans)
    using curr_flow[of e, simplified  same_gamma_loopB[simplified same_gamma_loopA]]
          Phi_after_below2N new_gamma_0 
    by auto
  from loopB_entryF show ?case 
    using   loopB_changes_\<F>[OF loopB_dom]
    unfolding same_gamma_loopB same_gamma_loopA loopB_entryF_def 
              sym[OF new_\<gamma>_def[simplified Let_def]] invar_forest_def 
    by (auto intro!: order.strict_trans2[OF _ current_flow_after_loopB[of ]])
qed

lemma invar_forest_pres_orlins_one_step:
  assumes "invar_forest state"
          "aux_invar state"
          "invar_gamma state"
          "invar_non_zero_b state"
          "orlins_entry state"
          "return state = notyetterm"
        shows   "invar_forest (orlins_one_step state)"
  using invar_forest_pres_orlins_one_step_check[OF assms(1-5)] assms(6)
  unfolding orlins_one_step_check_def by simp

lemma invar_integral_pres_orlins_one_step_check:
  assumes "invar_integral state"
          "aux_invar state"
          "invar_gamma state"
          "invar_non_zero_b state"  
          "invar_forest state"
          "orlins_entry state"          
  shows   "invar_integral (orlins_one_step_check state)"
proof-
  have aux_invar_gamma_upd: "aux_invar (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
    by(auto intro: aux_invar_gamma simp add: assms)
  have invar_gamma_gamma_upd: "invar_gamma (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
    unfolding new_\<gamma>_def Let_def
    by(fastforce intro: gamma_upd_aux_invar_pres 
              simp add: assms)
  hence new_gamma_0: "new_\<gamma> state > 0" unfolding invar_gamma_def by auto
  have loopA_dom: "loopA_dom (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
    using aux_invar_def aux_invar_gamma_upd 
    by(fastforce intro: termination_of_loopA[OF _ refl])
  have invar_gamma_after_loopA: "invar_gamma (loopA (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
    by(auto intro: loopA_invar_gamma_pres simp add: aux_invar_gamma_upd invar_gamma_gamma_upd)
  have aux_invar_after_loopA: "aux_invar (loopA (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
    by(auto intro: loopA_invar_aux_pres simp add: aux_invar_gamma_upd loopA_dom)
  have loopB_dom:"loopB_dom (loopA (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
    by(auto simp add: invar_gamma_after_loopA intro: loopB_termination)
  have same_gamma_loopB: "current_\<gamma> (loopB(loopA (state \<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))) =
                   current_\<gamma> (loopA (state \<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
    by(auto intro: loopB_changes_current_\<gamma> simp add: loopB_dom)
  have same_gamma_loopA: "current_\<gamma> (loopA (state \<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)) =
                            new_\<gamma> state"
    by(subst gamma_pres, auto simp add: aux_invar_gamma_upd)
  have init_Phi_below_N:"\<Phi> (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>) \<le> N"
    by(auto intro: Phi_init simp add: assms)
  have Phi_after_below2N: " \<Phi> ((loopA (state \<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))) \<le> 2*N"
    using Phi_increase_below_N[OF aux_invar_gamma_upd invar_gamma_gamma_upd] init_Phi_below_N by simp
 have card_below_N: "v \<in> \<V> \<Longrightarrow> card (connected_component (to_graph (\<FF>_imp state)) v) \<le> N" for v
    using N_def assms(2) aux_invar_def[of state] invar_aux10_def[of state] 
     card_mono[OF \<V>_finite, of "connected_component (to_graph (\<FF>_imp state)) v"] by simp
  have card_above_0: "v \<in> \<V> \<Longrightarrow> card (connected_component (to_graph (\<FF>_imp state)) v) > 0" for v
    using  assms(2) aux_invar_def[of state] invar_aux10_def[of state] 
      \<V>_finite V_non_empt finite_subset
    unfolding connected_component_def  by fastforce
  have invarA_1:"invarA_1 (2 * new_\<gamma> state) (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
    unfolding invarA_1_def apply rule
    subgoal for v 
    apply(simp, rule order.trans[OF balance_less_new_gamma[OF _ assms(6)]], simp)
      using card_above_0[of v]  new_gamma_0 by fastforce
    done  
  have invar_A2:"invarA_2 (8 * real N * new_\<gamma> state) (2 * new_\<gamma> state) (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
    unfolding invarA_2_def
    apply (rule, rule order.strict_trans1[of _ " 8 * real N * new_\<gamma> state"]) 
    using new_gamma_0 new_gamma_below_half_gamma[of state]  N_gtr_0 assms(5)[simplified invar_forest_def] 
    by(auto intro:  order.strict_trans1[of _ "8* real N * (current_\<gamma> state / 2)"]
         simp add: algebra_simps)
   have loopA_entry: "loopA_entry (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
    unfolding loopA_entry_def
    using new_gamma_0 new_gamma_below_half_gamma[of state]  N_gtr_0 assms(5)[simplified invar_forest_def] 
    by(auto intro:  order.strict_trans1[of _ "8* real N * (current_\<gamma> state / 2)"]
         simp add: algebra_simps)
  have loopB_entryF:"loopB_entryF (loopA (state \<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)) "
    using invarA_1 invar_A2 
    by(auto intro: loopB_entryF[OF aux_invar_gamma_upd loopA_entry invar_gamma_gamma_upd refl])
  have curr_flow:"current_flow (loopB (loopA (state \<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))) e
        \<ge> current_flow (loopA (state \<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)) e - 
          \<Phi> ((loopA (state \<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))) *
          current_\<gamma> (loopB(loopA (state \<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)))" for e
    apply(rule loopB_flow_Phi_final[OF _ refl])
      using invar_gamma_after_loopA loopB_dom loopB_entryF aux_invar_after_loopA
      unfolding loopB_entryF_def 
      by (simp, simp, smt (verit) Phi_after_below2N invar_gamma_after_loopA invar_gamma_def mult_nonneg_nonneg of_int_nonneg, simp)
  have current_flow_after_loopB:
         "current_flow (loopB (loopA (state \<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))) e
        \<ge> current_flow (loopA (state \<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)) e - 2*N*new_\<gamma> state" for e
    apply(rule order.trans)
    using curr_flow[of e, simplified  same_gamma_loopB[simplified same_gamma_loopA]]
          Phi_after_below2N new_gamma_0 
    by auto
  show ?thesis
  unfolding orlins_one_step_check_def orlins_one_step_def Let_def
  apply(cases "return state", simp add: assms, simp add: assms)
  apply(subst if_not_P, simp, subst if_not_P, simp, rule loopB_invar_integral_pres)  
  subgoal
    apply(rule loopB_termination, rule loopA_invar_gamma_pres )
    using assms 
    by (force intro!: loopA_invar_gamma_pres  aux_invar_gamma gamma_upd_aux_invar_pres)+
  subgoal
    apply(rule loopA_invar_aux_pres, rule termination_of_loopA[OF _ refl])
    using assms(2) aux_invar_gamma[of state] 
    by (fastforce intro:  aux_invarE[OF aux_invar_gamma[of state]])+
  subgoal
    by(rule loopA_invar_integral_pres, fastforce intro: aux_invar_gamma simp add: assms,
       rule invar_integralI, cases "\<forall>e\<in>to_set (actives state). current_flow state e = 0", simp,
       (rule invar_integralE[OF assms(1)],
            auto intro: is_multiple_multiple[of _ "current_\<gamma> state"])+) 
  apply(fastforce intro!: loopA_invar_gamma_pres aux_invar_gamma gamma_upd_aux_invar_pres
            simp add: assms)
  unfolding sym[OF new_\<gamma>_def[of state], simplified Let_def]
    apply(rule order.trans) defer
    apply(rule order.strict_implies_order[OF allTurnSet[OF 
           loopB_entryF[simplified loopB_entryF_def], of ]])
    using Phi_after_below2N new_gamma_0 same_gamma_loopA 
    by force+
qed

lemma invar_integral_pres_orlins_one_step:
  assumes "invar_integral state"
          "aux_invar state"
          "invar_gamma state"
          "invar_non_zero_b state"
          "return state = notyetterm"
          "invar_forest state"
          "orlins_entry state"
  shows   "invar_integral (orlins_one_step state)"
  using invar_integral_pres_orlins_one_step_check[OF assms(1-4)]
  unfolding orlins_one_step_check_def 
  using assms by simp

lemma orlins_entry_ofter_one_step:
  assumes "aux_invar state" "invar_gamma state" "invar_non_zero_b state"
        "return (orlins_one_step state) = notyetterm"
  shows "orlins_entry (orlins_one_step state)"
   using assms unfolding orlins_one_step_def Let_def
  by(fastforce intro!: orlins_entry_after_loopB[OF _ refl] loopB_termination
                       loopA_invar_gamma_pres gamma_upd_aux_invar_pres aux_invar_gamma)

lemma optimality_pres_orlins_one_step_check:
  assumes "invar_forest state"
          "aux_invar state"
          "invar_gamma state"
          "invar_non_zero_b state"
          "orlins_entry state"
          "invar_integral state"
          "invar_isOptflow state"
  shows   "invar_isOptflow (orlins_one_step_check state)"
          "return (orlins_one_step state) = success \<Longrightarrow>
           is_Opt \<b> (current_flow (orlins_one_step state))"
          "return (orlins_one_step state) = failure \<Longrightarrow>
           \<nexists> f. f is \<b> flow"
  unfolding orlins_one_step_check_def orlins_one_step_def Let_def
  apply(cases "return state", simp add: assms, simp add: assms)
  apply(subst if_not_P, simp, subst if_not_P, simp)
  unfolding sym[OF orlins_one_step_def[simplified Let_def]]
proof-
  have aux_invar_gamma_upd: "aux_invar (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
    by(auto intro: aux_invar_gamma simp add: assms)
  have invar_gamma_gamma_upd: "invar_gamma (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
    unfolding new_\<gamma>_def Let_def
    by(fastforce intro: gamma_upd_aux_invar_pres 
              simp add: assms)
  hence new_gamma_0: "new_\<gamma> state > 0" unfolding invar_gamma_def by auto
  have loopA_dom: "loopA_dom (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
    using aux_invar_def aux_invar_gamma_upd 
    by(fastforce intro: termination_of_loopA[OF _ refl])
  have invar_gamma_after_loopA: "invar_gamma (loopA (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
    by(auto intro: loopA_invar_gamma_pres simp add: aux_invar_gamma_upd invar_gamma_gamma_upd)
  have aux_invar_after_loopA: "aux_invar (loopA (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
    by(auto intro: loopA_invar_aux_pres simp add: aux_invar_gamma_upd loopA_dom)
  have loopB_dom:"loopB_dom (loopA (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
    by(auto simp add: invar_gamma_after_loopA intro: loopB_termination)
  have same_gamma_loopB: "current_\<gamma> (loopB(loopA (state \<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))) =
                   current_\<gamma> (loopA (state \<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
    by(auto intro: loopB_changes_current_\<gamma> simp add: loopB_dom)
  have same_gamma_loopA: "current_\<gamma> (loopA (state \<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)) =
                            new_\<gamma> state"
    by(subst gamma_pres, auto simp add: aux_invar_gamma_upd)
  have init_Phi_below_N:"\<Phi> (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>) \<le> N"
    by(auto intro: Phi_init simp add: assms)
  have Phi_after_below2N: " \<Phi> ((loopA (state \<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))) \<le> 2*N"
    using Phi_increase_below_N[OF aux_invar_gamma_upd invar_gamma_gamma_upd] init_Phi_below_N by simp
  have card_below_N: "v \<in> \<V> \<Longrightarrow> card (connected_component (to_graph (\<FF>_imp state)) v) \<le> N" for v
    using N_def assms(2) aux_invar_def[of state] invar_aux10_def[of state] 
     card_mono[OF \<V>_finite, of "connected_component (to_graph (\<FF>_imp state)) v"] by simp
  have card_above_0: "v \<in> \<V> \<Longrightarrow> card (connected_component (to_graph (\<FF>_imp state)) v) > 0" for v
    using  assms(2) aux_invar_def[of state] invar_aux10_def[of state] 
      \<V>_finite V_non_empt finite_subset
    unfolding connected_component_def  by fastforce
  have invarA_1:"invarA_1 (2 * new_\<gamma> state) (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
    unfolding invarA_1_def apply rule
    subgoal for v 
    apply(simp, rule order.trans[OF balance_less_new_gamma[OF _ assms(5)]], simp)
      using card_above_0[of v]  new_gamma_0 by fastforce
    done  
  have invar_A2:"invarA_2 (8 * real N * new_\<gamma> state) (2 * new_\<gamma> state) (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
    unfolding invarA_2_def
    apply (rule, rule order.strict_trans1[of _ " 8 * real N * new_\<gamma> state"]) 
    using new_gamma_0 new_gamma_below_half_gamma[of state]  N_gtr_0 assms(1)[simplified invar_forest_def] 
    by(auto intro:  order.strict_trans1[of _ "8* real N * (current_\<gamma> state / 2)"]
         simp add: algebra_simps)
  have invarA_2_AfterloopA: "invarA_2 (8 * real N * new_\<gamma> state)
                                (2 * new_\<gamma> state) (loopA (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
    using new_gamma_0 invarA_1 invar_A2
    by(auto intro!: invarA2_pres[OF aux_invar_gamma_upd _ _ _ _ , of "2*new_\<gamma> state",simplified])
  have loopA_entry: "loopA_entry (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
    unfolding loopA_entry_def
    using new_gamma_0 new_gamma_below_half_gamma[of state]  N_gtr_0 assms(1)[simplified invar_forest_def] 
    by(auto intro:  order.strict_trans1[of _ "8* real N * (current_\<gamma> state / 2)"]
         simp add: algebra_simps)
  have loopB_entryF:"loopB_entryF (loopA (state \<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)) "
    using invarA_1 invar_A2 
    by(auto intro: loopB_entryF[OF aux_invar_gamma_upd loopA_entry invar_gamma_gamma_upd refl])
  have optA:"invar_isOptflow (loopA (state \<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
    using new_gamma_0 invar_isOpt_gamma_change[OF assms(7)] invar_A2 invar_gamma_gamma_upd 
    by(fastforce intro: flow_optimatlity_pres[OF aux_invar_gamma_upd _ invarA_1 _ _ refl ])
  have invar_integralbeforeA: "invar_integral (state \<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
    using assms(6)
    unfolding new_\<gamma>_def invar_integral_def Let_def
    by(auto intro: is_multiple_multiple[of "current_flow state _"  "current_\<gamma> state"]) 
  have invar_integralA: "invar_integral (loopA (state \<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"
    using aux_invar_gamma_upd assms
    by(fastforce intro: loopA_invar_integral_pres invar_integralbeforeA)
  have card_below_N_afterA: "v \<in> \<V> \<Longrightarrow>
     card (connected_component (to_graph (\<FF>_imp (loopA (state \<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)))) v) \<le> N" for v
    using N_def  aux_invar_after_loopA  card_mono[OF \<V>_finite ] 
    unfolding aux_invar_def invar_aux10_def by simp 
  have optB:"invar_isOptflow (loopB(loopA (state \<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)))"
    apply(rule loopB_invar_isOpt_pres[OF loopB_dom aux_invar_after_loopA invar_gamma_after_loopA 
                                         invar_integralA optA])
    unfolding same_gamma_loopA
    apply(rule order.trans) defer
     apply(rule order.strict_implies_order[OF all_to_meta_set[OF
                            invarA_2_AfterloopA[simplified invarA_2_def]]])
    using   card_below_N_afterA[OF fst_E_V] Phi_after_below2N new_gamma_0 N_gtr_0
             conjunct1[OF conjunct2[OF conjunct2[OF aux_invar_after_loopA[simplified
                     aux_invar_def invar_aux3_def] ]]]
    by(simp, intro pos_subs_ineq[of _ _ "(real_of_int _) * _"] ,  
       auto simp add: in_mono algebra_simps)
  thus "return state = notyetterm \<Longrightarrow> invar_isOptflow (orlins_one_step state)"
    unfolding orlins_one_step_def new_\<gamma>_def Let_def by simp
  show "return (orlins_one_step state) = success \<Longrightarrow> 
           is_Opt \<b> (current_flow (orlins_one_step state))"
    unfolding orlins_one_step_def Let_def sym[OF new_\<gamma>_def[simplified Let_def]]
    by(auto intro:loopB_correctness[OF loopB_dom aux_invar_after_loopA invar_gamma_after_loopA
                                    invar_integralA loopB_entryF optA Phi_after_below2N])
  show "return (orlins_one_step state) = failure \<Longrightarrow> \<nexists>f. f is \<b> flow"
    unfolding orlins_one_step_def Let_def sym[OF new_\<gamma>_def[simplified Let_def]]
    by(rule loopB_completeness[OF loopB_dom aux_invar_after_loopA invar_gamma_after_loopA
                                    invar_integralA loopB_entryF optA Phi_after_below2N])
qed

lemma optimality_pres_orlins_one_step:
  assumes "invar_forest state"
          "aux_invar state"
          "invar_gamma state"
          "invar_non_zero_b state"
          "orlins_entry state"
          "invar_integral state"
          "invar_isOptflow state"
          "return state= notyetterm"
  shows   "invar_isOptflow (orlins_one_step state)"
  using optimality_pres_orlins_one_step_check[OF assms(1-7)] assms(8)
  unfolding orlins_one_step_check_def by simp

lemma some_balance_after_one_step:
  assumes "return (orlins_one_step state) = notyetterm" "aux_invar state" "invar_gamma state"
          "invar_non_zero_b state"
 shows    "invar_non_zero_b (orlins_one_step state)"
  using assms(2-) assms(1)[simplified orlins_one_step_def Let_def]
  unfolding orlins_one_step_def Let_def
     by (intro remaining_balance_after_loopB[OF _ refl]) 
        (fastforce intro!: loopB_termination loopA_invar_gamma_pres 
                           aux_invar_gamma gamma_upd_aux_invar_pres)+

lemma no_important_no_merge_gamma:
  assumes "\<And> k' state'. k' \<le> k \<Longrightarrow> state' = (compow k' orlins_one_step_check state) \<Longrightarrow>
                \<nexists> v. important state' v" 
          "(\<And> k' state'. k' \<le> k \<Longrightarrow> state' = (compow k' orlins_one_step_check state) \<Longrightarrow>
                          card (comps \<V> (to_graph (\<FF>_imp state'))) = card (comps \<V> (to_graph (\<FF>_imp state))))"
          "state' = (compow k orlins_one_step_check state)"
          "return state' =notyetterm"
          "invar_gamma state"
          "aux_invar state"
          "invar_non_zero_b state"
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
    hence loopB_unfold:"(orlins_one_step_check^^Suc k') state = 
           (orlins_one_step_check^^ k') (orlins_one_step state)" for k'
      apply(subst funpow_Suc_right, simp)
      unfolding orlins_one_step_check_def using returnValue 
      by(auto split: if_split)
    hence loopB_unfold':"(orlins_one_step_check^^Suc k') state = 
           (orlins_one_step_check^^ k') (orlins_one_step_check state)" for k'
      by(subst funpow_Suc_right, simp)      
    have returnValue':"return (orlins_one_step_check state) = notyetterm"
      apply(rule ccontr)
       using succ_fail_not_changes[of "orlins_one_step_check state" "k"] loopB_unfold'[of k]
       Suc(4-)
       by (metis (full_types) orlins_one_step_check_def return.exhaust)
     hence returnValue'':"return (orlins_one_step state) = notyetterm"
       unfolding orlins_one_step_check_def 
       by (simp add: returnValue)
     have card_Same:"card (comps \<V> (to_graph (\<FF>_imp (orlins_one_step state)))) =
          card (comps \<V> (to_graph (\<FF>_imp state)))" 
      apply(rule Suc(3)[of 1], simp+)
      unfolding orlins_one_step_check_def orlins_one_step_def Let_def
      using returnValue by simp
    have balance_oneStep:"invar_non_zero_b (orlins_one_step state)"
       apply(rule some_balance_after_one_step)
       using  Suc(4-) returnValue'' by auto      
   have afterIH:"current_\<gamma> state' = (1 / 2) ^ k * current_\<gamma> ((orlins_one_step state)) \<and>
          state'\<lparr>current_\<gamma> := current_\<gamma> (orlins_one_step state)\<rparr> = (orlins_one_step state)"
      apply(rule  Suc(1))
      using Suc(2) loopB_unfold apply fastforce 
      using card_Same  loopB_unfold[of k] Suc balance_oneStep sym[OF loopB_unfold]
      by (auto intro: Suc(3)[of "Suc _"] invar_gamma_pres_orlins_one_step 
                      aux_invar_pres_orlins_one_step)

  have new_gamma:"new_\<gamma> state \<noteq> current_\<gamma> state / 2 \<Longrightarrow> False"
  proof(goal_cases)
   case 1
   hence 11:"\<forall> e \<in> to_set (actives state). current_flow state e = 0" 
         "(Max { \<bar> balance state v\<bar> | v. v \<in> \<V>}) = new_\<gamma> state"
     unfolding new_\<gamma>_def Let_def 
      apply presburger
     using 1  unfolding new_\<gamma>_def Let_def 
     by (smt (verit, best))
   obtain v where v_prop:"(\<bar> balance state v\<bar> =
                    Max { \<bar> balance state v\<bar> | v. v \<in> \<V>})" "v \<in> \<V>"
     using obtain_Max[of \<V> "\<lambda> v. \<bar> balance state v\<bar>"]  V_non_empt \<V>_finite by blast
   have "\<bar> balance state v\<bar> > 0"
     apply(rule bexE[OF Suc(8)[simplified invar_non_zero_b_def, simplified]])
       unfolding v_prop
       apply(subst Max_gr_iff[of "{\<bar>balance state v\<bar> |v. v \<in> \<V>}" 0])
       by( auto simp add: \<V>_finite V_non_empt)
     hence "v \<in> \<V> \<and> (1 - \<epsilon>) * new_\<gamma> state < \<bar>balance state v\<bar>" 
     unfolding sym[OF 11(2)] sym[OF v_prop(1)]
     using v_prop(2)  \<epsilon>_axiom(1) by force
   hence "\<exists> v. important state v"
     unfolding important_def  by auto
   then show ?case using Suc(2)[of 0, OF _ refl] by simp
  qed

  hence gamma_halved:"current_\<gamma> ((orlins_one_step state)) = (1/2) * current_\<gamma> state"
    unfolding orlins_one_step_def new_\<gamma>_def Let_def
    using Suc by (subst loopB_changes_current_\<gamma> | subst gamma_pres |
                  fastforce intro!: loopB_termination loopA_invar_gamma_pres 
                                    aux_invar_gamma gamma_upd_aux_invar_pres)+

  have not_call_cond_loopA: "loopA_call_cond (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>) \<Longrightarrow> False"
  proof(goal_cases)
    case 1
    have "card (comps \<V> (to_graph (\<FF>_imp (loopA (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))))) <
              card (comps \<V> (to_graph (\<FF>_imp (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))))"
      using Suc 1 by (intro card_strict_decrease[of "state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>"]) 
                     (fastforce intro: aux_invarE[of "state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>"] 
                                       termination_of_loopA[OF _ refl] aux_invar_gamma)+

    moreover have "card (comps \<V> (to_graph (\<FF>_imp (loopA (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))))) = 
                   card (comps \<V> (to_graph (\<FF>_imp (loopB (loopA (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))))))"
          using Suc[simplified invar_non_zero_b_def]
          by(subst loopB_changes_\<FF>_imp, intro loopB_termination) 
            (fastforce intro: loopA_invar_gamma_pres aux_invar_gamma 
                              gamma_upd_aux_invar_pres[simplified invar_non_zero_b_def] 
                    simp add: new_\<gamma>_def Let_def)+
        ultimately have "card (comps \<V> (to_graph (\<FF>_imp (orlins_one_step_check state)))) < 
                             card (comps \<V> (to_graph (\<FF>_imp state)))"
      unfolding orlins_one_step_check_def orlins_one_step_def new_\<gamma>_def Let_def
      using returnValue by simp
    thus False
      using Suc(3)[of 1, OF _ refl] by simp
  qed

  hence loopA_no_change:"loopA (state  \<lparr>current_\<gamma> := new_\<gamma> state \<rparr>) = state \<lparr>current_\<gamma> := new_\<gamma> state \<rparr>"
    using Suc 
    by(cases rule: loopA_cases[of "state  \<lparr>current_\<gamma> := new_\<gamma> state \<rparr>"])
      (subst loopA_simps(2) | 
       fastforce intro: termination_of_loopA[OF _ refl] 
       aux_invarE[of "state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>"]  aux_invar_gamma simp add: loopA_simps(2))+
      
  have same_state:"(orlins_one_step state) \<lparr> current_\<gamma> := current_\<gamma> state \<rparr> = state"
    unfolding orlins_one_step_def Let_def
    apply(subst loopA_no_change[simplified new_\<gamma>_def Let_def])
    apply(subst loopB_nothing_done)
    using Suc Suc(2)[of 0, OF _ refl] returnValue
    unfolding sym[OF  new_\<gamma>_def[simplified Let_def]] important_def invar_non_zero_b_def
    by auto
    
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
  unfolding aux_invar_def by simp

lemma forest_increase_orlins_one_step:
  assumes "aux_invar state" "invar_gamma state" "invar_non_zero_b state"
  shows" to_graph (\<FF>_imp (orlins_one_step state)) \<supseteq> to_graph (\<FF>_imp state)"
  unfolding orlins_one_step_def Let_def 
  apply(rule ord_eq_le_trans[of _ "to_graph (\<FF>_imp (state \<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))"])
  subgoal
    unfolding new_\<gamma>_def Let_def
    using assms 
    by (fastforce intro!: loopB_changes_\<FF>_imp loopB_termination loopA_invar_gamma_pres 
                          aux_invar_gamma gamma_upd_aux_invar_pres)
  subgoal
    apply(rule order.trans, rule forest_increase)
    unfolding new_\<gamma>_def Let_def
    using assms 
    by(subst loopB_changes_\<FF>_imp[simplified  new_\<gamma>_def Let_def] | 
       fastforce intro!: loopB_termination termination_of_loopA loopA_invar_gamma_pres 
                         gamma_upd_aux_invar_pres assms aux_invar_gamma 
                         invar_aux_to_invar_aux1[of "state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>", simplified  new_\<gamma>_def Let_def]
                         invar_aux17_from_aux_invar[of "state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>", simplified  new_\<gamma>_def Let_def])+
  done

lemma card_decrease_orlins_one_step:
  assumes "aux_invar state" "invar_gamma state" "invar_non_zero_b state"
  shows"card (comps \<V> (to_graph (\<FF>_imp (orlins_one_step state)))) \<le>
            card (comps \<V> (to_graph (\<FF>_imp state)))"
  apply(rule number_of_comps_anti_mono[OF forest_increase_orlins_one_step[OF assms]])
  using assms(1)unfolding aux_invar_def invar_aux5_def by simp

lemma orlins_some_steps_forest_increase:
  assumes "state' = (orlins_one_step_check ^^ k) state"
              "aux_invar state" "invar_gamma state" "invar_non_zero_b  state"
  shows " to_graph (\<FF>_imp state') \<supseteq> to_graph (\<FF>_imp state)"
  using assms
proof(induction k arbitrary: state state')
  case (Suc k)
  have unfold:"(orlins_one_step_check ^^ Suc k) state = 
        (orlins_one_step_check ^^ k) (orlins_one_step_check state)"
    by (metis funpow_simps_right(2) o_apply)
  show ?case 
  proof(cases "return state = notyetterm")
    case True
    hence one_step:"(orlins_one_step_check state)  = orlins_one_step state"
      unfolding orlins_one_step_check_def by simp
    show ?thesis
    proof(cases "return (orlins_one_step state) = notyetterm")
      case True
      have balance_after_one_step:"invar_non_zero_b (orlins_one_step state) "
        using True Suc by (intro some_balance_after_one_step)
      show ?thesis 
      apply(subst Suc(2))
      apply(subst unfold)
      apply(rule order.trans[of _ "to_graph (\<FF>_imp ((orlins_one_step_check  state)))"]) 
        subgoal
          unfolding orlins_one_step_check_def
          apply(subst if_split, rule, simp)+
          apply(rule forest_increase_orlins_one_step)
          using Suc by auto
        apply(rule Suc(1)[OF refl ])
        using aux_invar_pres_orlins_one_step invar_gamma_pres_orlins_one_step
              some_balance_after_one_step True Suc(3-) one_step 
        by auto    
    next
      case False
      thm notyetterm_no_change
      show ?thesis 
        apply(subst  Suc(2))
        using unfold notyetterm_no_change True forest_increase_orlins_one_step False one_step Suc
        unfolding orlins_one_step_check_def 
        by fastforce+
    qed
  next
    case False
    hence one_step_no_change:"(orlins_one_step_check state) = state" 
      unfolding orlins_one_step_check_def
      using return.exhaust by auto
    show ?thesis 
      apply(subst Suc(2))
      apply(subst unfold)
      apply(rule order.trans[of _ "to_graph (\<FF>_imp ((orlins_one_step_check  state)))", rotated])
      subgoal
        apply(rule Suc(1))
        using one_step_no_change Suc by auto
      subgoal
        unfolding orlins_one_step_check_def[of state]
        using False return.exhaust by auto
      done
  qed
qed simp

lemma orlins_some_steps_card_decrease:
  assumes "state' = (orlins_one_step_check ^^ k) state"
              "aux_invar state" "invar_gamma state" "invar_non_zero_b  state"
            shows "card (comps \<V> (to_graph (\<FF>_imp state'))) \<le> card (comps \<V> (to_graph (\<FF>_imp state)))"
  apply(rule number_of_comps_anti_mono[OF orlins_some_steps_forest_increase[OF assms]])
  using assms(2) unfolding aux_invar_def invar_aux5_def by simp

lemma orlins_compow_aux_invar_pres:
  assumes "aux_invar state"
          "invar_gamma state"
          "invar_non_zero_b state"
    shows "aux_invar ((orlins_one_step_check ^^ k) state)"
  using assms
proof(induction k arbitrary: state)
  case (Suc k)
  show ?case
  apply(subst funpow_Suc_right, simp, subst orlins_one_step_check_def)
  apply(cases "return state", simp add: Suc, simp add: Suc, simp)
  apply(cases "return (orlins_one_step state)")
  using notyetterm_no_change Suc  
      apply(fastforce intro: aux_invar_pres_orlins_one_step,
            fastforce intro: aux_invar_pres_orlins_one_step)
  using invar_gamma_pres_orlins_one_step  Suc(2-) 
  by(fastforce intro: aux_invar_pres_orlins_one_step | 
       intro Suc(1) aux_invar_pres_orlins_one_step some_balance_after_one_step | simp)+
qed simp

lemma orlins_compow_invar_gamma_pres:
  assumes "aux_invar state"
          "invar_gamma state"
          "invar_non_zero_b state"
    shows "invar_gamma ((orlins_one_step_check ^^ k) state)"
  using assms
proof(induction k arbitrary: state)
  case (Suc k)
  show ?case
  apply(subst funpow_Suc_right, simp, subst orlins_one_step_check_def)
  apply(cases "return state", simp add: Suc, simp add: Suc, simp)
  apply(cases "return (orlins_one_step state)")
  using notyetterm_no_change Suc  
      apply(fastforce intro: invar_gamma_pres_orlins_one_step,
            fastforce intro: invar_gamma_pres_orlins_one_step)
  using invar_gamma_pres_orlins_one_step  Suc(2-) 
  by(fastforce intro: aux_invar_pres_orlins_one_step | 
       intro Suc(1) aux_invar_pres_orlins_one_step some_balance_after_one_step | simp)+
qed simp

lemma orlins_compow_invar_integral_pres:
  assumes "aux_invar state"
          "invar_gamma state"
          "invar_non_zero_b state"
          "invar_integral state"
          "invar_forest state"
          "orlins_entry state"
    shows "invar_integral ((orlins_one_step_check ^^ k) state)"
  using assms
proof(induction k arbitrary: state)
  case (Suc k)
  show ?case
  apply(subst funpow_Suc_right, simp, subst orlins_one_step_check_def)
  apply(cases "return state", simp add: Suc, simp add: Suc, simp)
  apply(cases "return (orlins_one_step state)")
  using Suc notyetterm_no_change[of "orlins_one_step state" k] 
  apply(fastforce intro: invar_integral_pres_orlins_one_step,
        fastforce intro: invar_integral_pres_orlins_one_step)
  using invar_gamma_pres_orlins_one_step  Suc(2-) 
  apply(fastforce intro: aux_invar_pres_orlins_one_step 
                         invar_forest_pres_orlins_one_step orlins_entry_ofter_one_step| 
       intro Suc(1) invar_integral_pres_orlins_one_step 
       some_balance_after_one_step | simp)+
  done
qed simp

lemma orlins_compow_invar_isOptflow_pres:
  assumes "aux_invar state"
          "invar_gamma state"
          "invar_non_zero_b state"
          "invar_integral state"
          "invar_isOptflow state"
          "invar_forest state"
          "orlins_entry state"
    shows "invar_isOptflow ((orlins_one_step_check ^^ k) state)"
  using assms
proof(induction k arbitrary: state)
  case (Suc k)
  show ?case
  apply(subst funpow_Suc_right, simp, subst orlins_one_step_check_def)
  apply(cases "return state", simp add: Suc, simp add: Suc, simp)
  apply(cases "return (orlins_one_step state)")
  using Suc notyetterm_no_change[of "orlins_one_step state" k] 
  apply(fastforce intro: optimality_pres_orlins_one_step,
        fastforce intro: optimality_pres_orlins_one_step)
  using Suc(2-) by(intro Suc(1) | (intro some_balance_after_one_step, simp, simp, simp, simp) |
                   fastforce intro: invar_gamma_pres_orlins_one_step aux_invar_pres_orlins_one_step
                                    invar_integral_pres_orlins_one_step optimality_pres_orlins_one_step
                                    invar_forest_pres_orlins_one_step orlins_entry_ofter_one_step)+  
qed simp

lemma some_balance_after_k_steps:
  assumes "return ((compow k orlins_one_step_check) state) = notyetterm" 
          "aux_invar state" "invar_gamma state"
          "invar_non_zero_b state"
shows     "invar_non_zero_b ((compow k orlins_one_step_check) state) "
  using assms
  apply(induction k arbitrary: state, simp add: assms)
  subgoal for k' state
   using orlins_one_step_check_def funpow.simps(2)
   by(subst funpow.simps(2), simp, cases "return ((orlins_one_step_check ^^ k') state)")
     (fastforce intro: some_balance_after_one_step[of "((orlins_one_step_check ^^ k') state)", simplified]
                              orlins_compow_aux_invar_pres orlins_compow_invar_gamma_pres)+
  done

lemma orlins_entry_after_compow:
  assumes 
        "aux_invar state" "invar_gamma state" "invar_non_zero_b state"
        "return ((compow k orlins_one_step_check) state) = notyetterm"
        "orlins_entry state"
  shows "orlins_entry ((compow k orlins_one_step_check) state)"
  using assms 
proof(induction k arbitrary: state, simp)
  case (Suc k)
  have state_ret:"return state = notyetterm" 
    using notyetterm_no_change[of state "Suc k"] Suc(5) by force
  have one_step_check:"orlins_one_step_check state = 
       orlins_one_step state" using state_ret unfolding orlins_one_step_check_def by simp
  have state_ret_step:"return (orlins_one_step state) = notyetterm" 
    using notyetterm_no_change[of "(orlins_one_step state)" k, simplified sym[OF one_step_check]]
          Suc(5)[simplified funpow_Suc_right, simplified] one_step_check by force
  show ?case using Suc(5)
    apply(subst funpow_Suc_right)
    apply(subst (asm) funpow_Suc_right, simp, subst one_step_check, subst (asm) one_step_check)
    using Suc(2-) state_ret_step
    by(intro Suc(1) some_balance_after_one_step | 
      (fastforce intro: aux_invar_pres_orlins_one_step invar_gamma_pres_orlins_one_step 
                        orlins_entry_ofter_one_step)+)+
qed

lemma orlins_compow_invar_forest_pres:
  assumes "invar_forest state"
          "aux_invar state"
          "invar_gamma state"
          "invar_non_zero_b state"
          "orlins_entry state"
  shows   "invar_forest ((orlins_one_step_check ^^ k) state)"
  using assms apply(induction k arbitrary: state, simp)
  subgoal for k state
    apply(subst funpow_Suc_right, simp, subst orlins_one_step_check_def)
    apply(cases "return state", simp, simp, simp, cases "return (orlins_one_step state)")
    apply(subst notyetterm_no_change, simp, simp add: invar_forest_pres_orlins_one_step[of state])
    apply(subst notyetterm_no_change, simp, simp add: invar_forest_pres_orlins_one_step[of state])
    using invar_forest_pres_orlins_one_step[of state]  
          invar_gamma_pres_orlins_one_step[of state]
          aux_invar_pres_orlins_one_step[of state]
          some_balance_after_one_step[of state]
          orlins_entry_ofter_one_step[of state]
    by simp
  done

lemma important_or_merge_or_termination:
  assumes "invar_gamma state"
          "aux_invar state"
          "invar_non_zero_b state"
          "isuflow (current_flow state)"
          "invar_integral state"
          "\<k> =  nat (\<lceil>log 2 N \<rceil> + 3)"
  shows   "\<exists> k \<le> \<k>+1. return ((compow k orlins_one_step_check) state) \<noteq> notyetterm \<or>
                    (\<exists> v. important (compow k (orlins_one_step_check) state) v) \<or>
                    card (comps \<V> (to_graph (\<FF>_imp (compow k (orlins_one_step_check) state)))) 
                          < card (comps \<V> (to_graph (\<FF>_imp state)))"
proof-
  have gamma_0: "current_\<gamma> state > 0" 
    using assms(1) invar_gamma_def by auto
  have last_chance_merge:
       " (\<And> k. k \<le> \<k>  \<Longrightarrow> return (compow k (orlins_one_step_check) state) = notyetterm) \<Longrightarrow>
         (\<And> k. k \<le> \<k>  \<Longrightarrow> (\<nexists> v. important (compow k (orlins_one_step_check) state) v)) \<Longrightarrow>
         (\<And> k. k \<le> \<k>  \<Longrightarrow> \<not> card (comps \<V> (to_graph (\<FF>_imp (compow k (orlins_one_step_check) state)))) 
                                   < card (comps \<V> (to_graph (\<FF>_imp state)))) \<Longrightarrow>
         card (comps \<V> (to_graph (\<FF>_imp ((orlins_one_step_check ^^ (Suc \<k>)) state)))) < 
         card (comps \<V> (to_graph (\<FF>_imp state)))"
  proof(goal_cases)
    case 1 
    note note1= this
    have cards:"k \<le> \<k> \<Longrightarrow>
     card (comps \<V> (to_graph (\<FF>_imp ((orlins_one_step_check ^^ k) state)))) = 
               card (comps \<V> (to_graph (\<FF>_imp state)))" for k   
      using  orlins_some_steps_card_decrease[OF refl assms(2) assms(1) assms(3), of k]
             1(3)[of k, simplified not_less] by simp
    have gamma_after_k:
         "current_\<gamma> ((orlins_one_step_check ^^ (\<k>)) state) = (1 / 2) ^ (\<k>) * current_\<gamma> state"
         "((orlins_one_step_check ^^ (\<k>)) state)\<lparr>current_\<gamma> := current_\<gamma> state\<rparr> = state"
      using cards  1 assms(1-3) no_important_no_merge_gamma[of "\<k>" state, OF _ _refl] 
      by auto
    have gamma_after_k_minus1:
         "current_\<gamma> ((orlins_one_step_check ^^ (\<k>-1)) state) = (1 / 2) ^ (\<k>-1) * current_\<gamma> state"
         "(orlins_one_step_check ^^ (\<k>-1)) state\<lparr>current_\<gamma> := current_\<gamma> state\<rparr> = state"
      using cards  1 assms(1-3) no_important_no_merge_gamma[of "\<k>-1" state, OF _ _refl] 
      by auto
 have new_gamma:"\<forall> e \<in> to_set (actives state). current_flow state e = 0 \<Longrightarrow> False"
   proof(goal_cases)
   case 1
   hence 11: True
         "min (current_\<gamma> state / 2) (Max { \<bar> balance state v\<bar> | v. v \<in> \<V>}) = new_\<gamma> state"
     unfolding new_\<gamma>_def Let_def 
     by simp+
   obtain v where v_prop:"(\<bar> balance state v\<bar> =
                    Max { \<bar> balance state v\<bar> | v. v \<in> \<V>})" "v \<in> \<V>"
     using obtain_Max[of \<V> "\<lambda> v. \<bar> balance state v\<bar>"]  V_non_empt \<V>_finite by blast
   have "\<bar> balance state v\<bar> > 0"
     apply(rule bexE[OF assms(3)[simplified invar_non_zero_b_def, simplified]])
       unfolding v_prop
       apply(subst Max_gr_iff[of "{\<bar>balance state v\<bar> |v. v \<in> \<V>}" 0])
       by( auto simp add: \<V>_finite V_non_empt)
     hence "v \<in> \<V> \<and> (1 - \<epsilon>) * new_\<gamma> state < \<bar>balance state v\<bar>" 
     unfolding sym[OF 11(2)] sym[OF v_prop(1)]
     using v_prop(2)  \<epsilon>_axiom(1)
     by (smt (verit, best) assms(1) divide_pos_pos invar_gamma_def mult_le_cancel_right1)
   hence "\<exists> v. important state v"
     unfolding important_def  by auto
   then show ?case using note1(2)[of 0] by simp
 qed
  then obtain e where e_prop:"e \<in> to_set (actives state)" "current_flow state e > 0"
    using assms(4) aux_invar_def[of state] assms(2)  unfolding isuflow_def invar_aux1_def
    by force
  have e_flow_gamma:"current_flow state e \<ge>  current_\<gamma> state" 
    apply(rule exE[OF bspec[OF assms(5)[simplified invar_integral_def] e_prop(1)]])
    using e_prop(2)
    by (smt (verit, ccfv_SIG) less_one linorder_neq_iff mult_le_cancel_right1 of_nat_0_less_iff 
           of_nat_1 of_nat_less_imp_less split_mult_neg_le)
  have gamma_k:"current_\<gamma> state \<ge> 8 * N * (1 / 2) ^ \<k> * current_\<gamma> state"
    apply(subst mult.commute[of "8 * N * (1 / 2) ^ \<k> "], subst assms(6), rule mult_right_le_one_le)
    using assms(1) invar_gamma_def apply force
    by(simp, rule leq_mul_swap[of _ _ "2 ^ nat (\<lceil>log 2 (real N)\<rceil> + 3)"],
       subst mult.assoc, subst cancel_power_denominator, simp, simp,subst sym[OF log_le_cancel_iff[of 2]],
       (subst log_mult log283| simp add: N_gtr_0  | linarith)+)
  have e_gamma_k:"8*N * new_\<gamma> ((orlins_one_step_check ^^ \<k>) state) < current_flow state e"
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
  have call_cond:"loopA_call_cond
     ((orlins_one_step_check ^^ \<k>) state\<lparr>current_\<gamma> := new_\<gamma> ((orlins_one_step_check ^^ \<k>) state)\<rparr>)"
    apply(rule loopA_call_condI[OF refl refl refl refl refl refl refl], simp)
    apply(subst same_actives, subst same_flow)
    using e_gamma_k e_prop(1) 
          set_get(1)[OF invar_aux17_from_aux_invar[OF assms(2), simplified invar_aux17_def],
                     of "(\<lambda>e. 8 * real N * new_\<gamma> ((orlins_one_step_check ^^ \<k>) state) < current_flow state e)"]
    by fastforce
  have return_state:"return ((orlins_one_step_check ^^ \<k>) state) = notyetterm"
    using 1(1)[of \<k>] by simp 
  have "card (comps \<V> (to_graph (\<FF>_imp ((orlins_one_step_check ^^ (Suc \<k>)) state)))) < 
        card (comps \<V> (to_graph (\<FF>_imp ((orlins_one_step_check ^^ \<k>) state))))"
    apply(simp, subst orlins_one_step_check_def[of "(orlins_one_step_check ^^ \<k>) state"],simp add: return_state)
    unfolding orlins_one_step_def Let_def
    apply(subst loopB_changes_\<FF>_imp)
    subgoal using assms return_state
      by(intro loopB_termination loopA_invar_gamma_pres aux_invar_gamma orlins_compow_aux_invar_pres
               gamma_upd_aux_invar_pres orlins_compow_invar_gamma_pres some_balance_after_k_steps| simp)+    
    apply(rule order.strict_trans2, rule card_strict_decrease)
    using call_cond[simplified new_\<gamma>_def Let_def]
    by( auto intro: termination_of_loopA[OF _ refl] 
        aux_invarE[OF aux_invar_gamma[OF orlins_compow_aux_invar_pres[OF assms(2) assms(1) assms(3)]]]
        aux_invar_gamma[OF orlins_compow_aux_invar_pres[OF assms(2) assms(1) assms(3)]])
  hence "card (comps \<V> (to_graph (\<FF>_imp ((orlins_one_step_check ^^ (Suc \<k>)) state)))) < 
        card (comps \<V> (to_graph (\<FF>_imp state)))"
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
      by (metis (full_types) return.exhaust)     
    hence loopB_unfold:"(orlins_one_step_check^^Suc k') state = 
           (orlins_one_step_check^^ k') (orlins_one_step state)" for k'
      apply(subst funpow_Suc_right, simp)
      unfolding orlins_one_step_check_def using returnValue 
      by(auto split: if_split)
    hence loopB_unfold':"(orlins_one_step_check^^Suc k') state = 
           (orlins_one_step_check^^ k') (orlins_one_step_check state)" for k'
      by(subst funpow_Suc_right, simp)      
    have returnValue':"return (orlins_one_step_check state) = notyetterm"
      apply(rule ccontr)
       using succ_fail_not_changes[of "orlins_one_step_check state" "k"] loopB_unfold'[of k]
       Suc(2-)
       by (metis (full_types) orlins_one_step_check_def return.exhaust)
     hence returnValue'':"return (orlins_one_step state) = notyetterm"
       unfolding orlins_one_step_check_def 
       by (simp add: returnValue)
    have balance_oneStep:"invar_non_zero_b (orlins_one_step state) "
       apply(rule some_balance_after_one_step)
       using  Suc(4-) returnValue'' by auto     
   have afterIH:"current_\<gamma> state' \<le> (1 / 2) ^ k * current_\<gamma> ((orlins_one_step state))"
      apply(rule  Suc(1))
      using Suc(2) loopB_unfold  apply force
      using   loopB_unfold[of k] Suc balance_oneStep sym[OF loopB_unfold]
      by (auto intro: invar_gamma_pres_orlins_one_step 
                      aux_invar_pres_orlins_one_step)
    have new_gamma:"new_\<gamma> state \<le> current_\<gamma> state / 2"
      unfolding new_\<gamma>_def Let_def by(auto split: if_split)
  hence gamma_halved:"current_\<gamma> ((orlins_one_step state)) \<le> (1/2) * current_\<gamma> state"
    unfolding orlins_one_step_def new_\<gamma>_def Let_def
    using Suc by (subst loopB_changes_current_\<gamma> | subst gamma_pres |
                  fastforce intro!: loopB_termination loopA_invar_gamma_pres 
                                    aux_invar_gamma gamma_upd_aux_invar_pres)+
  have invar_gamma: "invar_gamma (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
    using  Max_lower_bound[of \<V> _ 0 "\<lambda> v. \<bar> balance state v\<bar>"]
          Suc(4, 6) E_not_empty \<V>_finite
    unfolding invar_gamma_def new_\<gamma>_def Let_def invar_non_zero_b_def
    by(auto split: if_split)  
    show ?case 
        using   afterIH
        using gamma_halved
        by (smt (verit, ccfv_SIG) One_nat_def ab_semigroup_mult_class.mult_ac(1) mult.commute 
                 ordered_comm_semiring_class.comm_mult_left_mono plus_1_eq_Suc
                 power_Suc0_right power_add zero_le_divide_1_iff zero_le_power)
  qed

lemma invar_gamma_non_zero_balance_set:
  assumes "aux_invar state" and
   bs_def: "bs = {v | v. v \<in> connected_component (to_graph (\<FF>_imp state)) z \<and> balance state v \<noteq> 0}" and "z \<in> \<V>"
 shows "bs = {} \<or> (\<exists> x. {x} = bs)"
proof-
  have "x \<in> bs \<Longrightarrow> y \<in> bs \<Longrightarrow> x \<noteq> y \<Longrightarrow> False" for x y
  proof(goal_cases)
    case 1
    hence prps:"x \<in> connected_component (to_graph (\<FF>_imp state)) z" "balance state x \<noteq> 0"
          "y \<in> connected_component (to_graph (\<FF>_imp state)) z" "balance state y \<noteq> 0" 
      unfolding bs_def by auto
    have in_V:"x \<in> \<V>" "y \<in> \<V>"
      using 1 assms unfolding aux_invar_def invar_aux10_def by auto
    hence "representative state x = x" "representative state y = y" 
      using assms(1) prps unfolding aux_invar_def invar_aux12_def by auto
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
          "invar_non_zero_b state"
  shows "current_\<gamma> (orlins_one_step_check state) = new_\<gamma> state"
  unfolding orlins_one_step_check_def
  using assms apply simp
  unfolding orlins_one_step_def Let_def new_\<gamma>_def
  using assms gamma_pres
   by(subst gamma_pres loopB_changes_current_\<gamma>| fastforce intro!: loopB_termination loopA_invar_gamma_pres aux_invar_gamma
                         gamma_upd_aux_invar_pres)+

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
  shows   "\<exists> k \<le> \<l> + 1. return ((compow k orlins_one_step_check) state) \<noteq> notyetterm \<or>
                      connected_component (to_graph (\<FF>_imp (compow k (orlins_one_step_check) state))) z \<supset>
                      connected_component (to_graph (\<FF>_imp state)) z"
proof-
  have gamma_0: "current_\<gamma> state > 0" 
    using assms(1) invar_gamma_def by auto
  have last_chance_merge:
       " (\<And> k. k \<le> \<l>  \<Longrightarrow> return (compow k (orlins_one_step_check) state) = notyetterm) \<Longrightarrow>
         (\<And> k. k \<le> \<l>  \<Longrightarrow> \<not> 
                    connected_component (to_graph (\<FF>_imp (compow k (orlins_one_step_check) state))) z \<supset>
                      connected_component (to_graph (\<FF>_imp state)) z) \<Longrightarrow>
                      connected_component (to_graph (\<FF>_imp (compow (Suc \<l>) (orlins_one_step_check) state))) z \<supset>
                      connected_component (to_graph (\<FF>_imp state)) z"
  proof(goal_cases)
    case 1 
    note note1= this
    have l_0:"\<l> > 0" using assms by simp
    have connected_compt_subs: "connected_component (to_graph (\<FF>_imp ((orlins_one_step_check ^^ \<l>) state))) z \<supseteq> 
                     connected_component (to_graph (\<FF>_imp state)) z"
      by (simp add: assms(1) assms(2) assms(3) con_comp_subset orlins_some_steps_forest_increase)
    hence same_forst: "connected_component (to_graph (\<FF>_imp ((orlins_one_step_check ^^ \<l>) state))) z = 
                     connected_component (to_graph (\<FF>_imp state)) z" 
      using 1(2)[of \<l>] by simp 
    have gamma_after_k:
         "current_\<gamma> ((orlins_one_step_check ^^ \<l>) state) \<le> (1 / 2) ^ \<l> * current_\<gamma> state"
      using  assms(1-3)  1(1)[of \<l>]  no_merge_gamma[OF refl, of \<l> state] by simp
    define state1 where "state1 = orlins_one_step_check state"
    have l_minus1_after1: "(orlins_one_step_check ^^ (\<l> - 1)) state1 = 
                           (orlins_one_step_check ^^ \<l>) state" 
      using l_0  funpow_Suc_right[of "\<l>-1" orlins_one_step_check] 
      unfolding state1_def by simp
    have props_after1: " invar_gamma state1" "aux_invar state1" "invar_non_zero_b state1"
      unfolding state1_def
      using some_balance_after_k_steps[of 1, simplified] assms(1-3) 1(1)[of 1] l_0 
      by(auto intro:  orlins_compow_invar_gamma_pres[of _ 1, simplified] 
                      orlins_compow_aux_invar_pres[of _ 1, simplified])
   have gamma_after_k_minus1:
         "current_\<gamma> ((orlins_one_step_check ^^ (\<l>-1)) state1) \<le> (1 / 2) ^ (\<l>-1) * current_\<gamma> state1 "
     apply(rule no_merge_gamma[ OF  refl, of "\<l>-1" state1])
       using l_minus1_after1  assms(1-3)  1(1)[of "\<l>"] props_after1 by auto
   hence gamma_after_k_minus1': " 2^(\<l> - 1) * current_\<gamma> ((orlins_one_step_check ^^ (\<l> - 1)) state1) 
                                   \<le>  current_\<gamma> state1"
     apply(subst sym[OF mult_le_cancel_left_pos, of "(1 / 2) ^ (\<l> - 1)"], simp) 
     by(subst real_mul_assoc, subst cancel_power_denominator, simp, simp)
   have current_gamma_new_gamma:"current_\<gamma> state1 = new_\<gamma> state" 
     unfolding state1_def
     using assms(1-3) 1(1)[of 0]  
     by(auto intro!:  one_step_current_gamma_new_gamma)
    define Z  where "Z = connected_component (to_graph (\<FF>_imp state)) z"
    have same_comp:"Z = connected_component (to_graph (\<FF>_imp ((orlins_one_step_check ^^ \<l>) state))) z"
      using  same_forst unfolding Z_def by simp
    have outgoing_active:"e \<in> \<E> \<Longrightarrow> fst e \<in> Z \<Longrightarrow> snd e \<notin> Z \<Longrightarrow> e \<in> to_set (actives state)" for e
      using assms(2) unfolding aux_invar_def Z_def invar_aux13_def 
      using connected_components_member_sym[of "fst e" "to_graph (\<FF>_imp state)" z] 
            connected_components_member_sym[of z "to_graph (\<FF>_imp state)" "snd e"] by auto
    have ingoing_active:"e \<in> \<E> \<Longrightarrow> snd e \<in> Z \<Longrightarrow> fst e \<notin> Z \<Longrightarrow> e \<in> to_set (actives state)" for e
      using assms(2) unfolding aux_invar_def Z_def invar_aux13_def 
      using connected_components_member_sym[of "snd e" "to_graph (\<FF>_imp state)" z] 
            connected_components_member_sym[of z "to_graph (\<FF>_imp state)" "fst e"] by auto
    have new_gamma_less: "new_\<gamma> state \<le> current_\<gamma> state / 2"
      by(rule new_gamma_below_half_gamma)
    have new_gamma_0: "new_\<gamma> state > 0"
      using assms(3)[simplified invar_non_zero_b_def] assms(8) balance_less_new_gamma by fastforce
    have balance_z_non_zero: "balance state z \<noteq> 0" and z_in_V: "z \<in> \<V>"
      using assms(1, 5) new_gamma_0 \<epsilon>_axiom unfolding important_def 
      by (smt (verit, ccfv_threshold) divide_less_eq_1 mul_zero_cancel, simp)
    hence "representative state z = z"
      unfolding Z_def
      using assms(2) z_in_V unfolding aux_invar_def invar_aux12_def by simp
    moreover hence "x \<in> Z \<Longrightarrow> representative state x = z" for x
      using assms(2) z_in_V unfolding aux_invar_def Z_def invar_aux7_def 
      by (metis in_connected_componentE)
    moreover have Z_inV:"Z \<subseteq> \<V>"
          using assms(2) z_in_V unfolding aux_invar_def Z_def invar_aux10_def by simp
    ultimately have Z_balance:"x \<in> Z \<Longrightarrow> balance state x \<noteq> 0 \<Longrightarrow> x = z" for x
      unfolding Z_def
      using assms(2) unfolding aux_invar_def invar_aux12_def by auto
    have flow_value1: "sum (\<b> - balance state) Z = 
                       sum (current_flow state) (\<Delta>\<^sup>+ Z) - sum (current_flow state) (\<Delta>\<^sup>- Z)"
      by(intro flow_value[of "current_flow state" "\<b> - balance state" Z], auto
      simp add: assms(9)[simplified invar_isOptflow_def is_Opt_def] Z_inV)
    have out_mult1:"\<exists> n::int. n*current_\<gamma> state = sum (current_flow state) (\<Delta>\<^sup>+ Z)"
      apply(rule sum_integer_multiple)
      using  Delta_plus_def rev_finite_subset[OF finite_E , of "\<Delta>\<^sup>+ Z"] apply force
      subgoal for e
      apply(rule ballE[OF assms(4)[simplified invar_integral_def], of e], metis of_int_of_nat_eq)
        using outgoing_active[of e]  unfolding Delta_plus_def by auto
      done
   have ing_mul1:"\<exists> n::int. n*current_\<gamma> state = sum (current_flow state) (\<Delta>\<^sup>- Z)"
      apply(rule sum_integer_multiple)
      using  Delta_minus_def rev_finite_subset[OF finite_E , of "\<Delta>\<^sup>- Z"] apply force
      subgoal for e
      apply(rule ballE[OF assms(4)[simplified invar_integral_def], of e], metis of_int_of_nat_eq)
        using ingoing_active[of e]  unfolding Delta_minus_def by auto
      done
    have cross_mult1:
        "\<exists> n::int. n * current_\<gamma> state = 
               sum (current_flow state) (\<Delta>\<^sup>+ Z) - sum (current_flow state) (\<Delta>\<^sup>- Z)"
      using  integer_multiple_sub ing_mul1 out_mult1 by metis
    have "sum (\<b> - balance state) Z = sum \<b> Z - sum (balance state) Z"
      apply(subst diff_conv_add_uminus, subst sym[OF sum_negf])
      using sum.distrib[of \<b> "- balance state" Z, simplified] by simp
    also have "... = sum \<b> Z - (sum (balance state) (Z - {z}) + sum (balance state) {z})"
      apply(subst (2)sum.subset_diff[of "{z}" Z ])
      using Z_def Z_inV \<V>_finite connected_component_def rev_finite_subset by fastforce+
    also have "... = sum \<b> Z - balance state z" 
      using Z_balance sum.neutral[of "Z-{z}" "balance state"] by fastforce
    finally have balance_sum:"sum (\<b> - balance state) Z = sum \<b> Z - balance state z " by simp
    have cal21:"\<epsilon> * new_\<gamma> state \<le> (1-\<epsilon>) * new_\<gamma> state"
      apply(rule mult_right_mono)
      using \<epsilon>_axiom new_gamma_0 by simp+
    also have cal22:"... < \<bar> balance state z \<bar>" using assms(5) unfolding important_def
      by simp
    also have cal23:"... \<le> (1-\<epsilon>) * current_\<gamma> state"
      using assms(8) z_in_V unfolding orlins_entry_def by simp
    also have cal24:"... < current_\<gamma> state - \<epsilon> * new_\<gamma> state"
      apply(subst left_diff_distrib)
      using mult_less_cancel_left_pos gamma_0 new_gamma_less new_gamma_0 \<epsilon>_axiom by auto
    have sum_b_Z_above_eps_gam:"\<bar> sum \<b> Z \<bar> > \<epsilon> * new_\<gamma> state"
    proof(rule ccontr, goal_cases)
      case 1
      hence asm:"\<bar>sum \<b> Z\<bar> \<le> \<epsilon> * new_\<gamma> state" by simp
      have " sum \<b> Z - balance state z \<le> \<bar>sum \<b> Z - balance state z\<bar>" by simp
      also have "... \<le> \<bar> sum \<b> Z\<bar> + \<bar> balance state z\<bar>" by simp
      also have "... <  current_\<gamma> state "
        using cal23 cal24 asm by simp
      finally have less_curr_gamma:"sum \<b> Z - balance state z < current_\<gamma> state" by simp
      have " sum \<b> Z - balance state z \<ge> - \<bar>sum \<b> Z - balance state z\<bar>" by simp
      have "- \<bar>sum \<b> Z - balance state z\<bar> \<ge> -\<bar> sum \<b> Z\<bar> -\<bar> balance state z\<bar>" by simp
      have gtr_minus_curr_gamma:"sum \<b> Z - balance state z > - current_\<gamma> state" 
        using  cal23 cal24 asm by simp
      have a1:" \<bar> sum \<b> Z - balance state z \<bar>  =  \<bar>  balance state z - sum \<b> Z  \<bar> " by simp
       have a2:"... \<ge> \<bar> \<bar>balance state z\<bar> - \<bar>sum \<b> Z \<bar>\<bar>" by simp
       have a3:"\<bar> \<bar>balance state z\<bar> - \<bar>sum \<b> Z \<bar>\<bar> > 0 "
        apply(subst zero_less_abs_iff, rule not_sym, rule order.strict_implies_not_eq)        
        using cal22 asm new_gamma_0 \<epsilon>_axiom(4) cal21 by linarith
       have "\<bar> sum \<b> Z - balance state z \<bar> > 0" using a2 a3 by simp
      moreover have "sum \<b> Z - balance state z = 0"
        apply(rule exE[OF cross_mult1[simplified sym[OF flow_value1] balance_sum]])
          using gtr_minus_curr_gamma less_curr_gamma gamma_0
          by (smt (verit, ccfv_threshold) int_less_real_le mult_le_cancel_right1 mult_minus_left  
                                          of_int_0_less_iff of_int_less_0_iff)
       ultimately show ?case by simp
     qed
     define state' where "state' = (orlins_one_step_check ^^ \<l>) state"
     have aux_invar_state': "aux_invar state'" unfolding state'_def
       using assms by(fastforce intro!: orlins_compow_aux_invar_pres)
     have invar_gamma_state': "invar_gamma state'" unfolding state'_def
       using assms by(fastforce intro: orlins_compow_invar_gamma_pres)
     have invar_integral_state': "invar_integral state'" unfolding state'_def
       using assms by(fastforce intro: orlins_compow_invar_integral_pres)
     have invar_isOptflow_state': "invar_isOptflow state'" unfolding state'_def
       using assms by(fastforce intro: orlins_compow_invar_isOptflow_pres)
     have orlins_entry_after: "orlins_entry state'" unfolding state'_def
       using assms 1(1)[of \<l>] by (fastforce intro: orlins_entry_after_compow)
     have remaining_balance_after: "invar_non_zero_b state'"
       unfolding state'_def
       by(rule some_balance_after_k_steps[OF 1(1)[of \<l>, OF order.refl]  assms(2) assms(1) assms(3)])
     have new_gamma_state'_0:"new_\<gamma> state' > 0"
       unfolding new_\<gamma>_def Let_def
       using remaining_balance_after
       by(fastforce intro: gamma_upd_aux_invar_pres[OF invar_gamma_state', simplified invar_gamma_def, simplified])
     have e_flow_gr_0:"\<And> e. e \<in> \<E> \<Longrightarrow> current_flow state' e \<ge> 0"
       using invar_isOptflow_state' 
       unfolding invar_isOptflow_def is_Opt_def isbflow_def isuflow_def
       by simp
     have flow_value2: "sum (\<b> - balance state') Z = 
                       sum (current_flow state') (\<Delta>\<^sup>+ Z) - sum (current_flow state') (\<Delta>\<^sup>- Z)"
      by(intro flow_value[of "current_flow state'" "\<b> - balance state'" Z], auto
      simp add: invar_isOptflow_state'[simplified invar_isOptflow_def is_Opt_def] Z_inV)
    have sumb_split:"sum (\<b> - balance state') Z = sum \<b> Z - sum (balance state') Z"
      apply(subst diff_conv_add_uminus, subst sym[OF sum_negf])
      using sum.distrib[of \<b> "- balance state'" Z, simplified] by simp
    have sumZ_below:"\<bar>sum (balance state') Z \<bar>\<le> (1- \<epsilon>) * current_\<gamma> state'"
    proof(cases rule: disjE[OF invar_gamma_non_zero_balance_set[OF aux_invar_state' refl z_in_V]])
      case 1
      hence "sum (balance state') Z = 0" using same_comp unfolding Z_def state'_def
        by simp
      moreover have "(1 - \<epsilon>) * current_\<gamma> state' > 0" using invar_gamma_state' \<epsilon>_axiom(4)
        unfolding invar_gamma_def by simp
      ultimately show ?thesis by simp
    next
      case 2
      then obtain x where x_prop: 
           "{x} = {v |v. v \<in> connected_component (to_graph (\<FF>_imp state')) z \<and> balance state' v \<noteq> 0} " by auto
      hence x_in_V:"x \<in> \<V>" using same_comp state'_def Z_def Z_inV by auto
      have "sum (balance state') Z = (balance state') x" 
        apply(subst  sum_filter_zero[OF rev_finite_subset[OF \<V>_finite Z_inV], 
                 of "balance state'"])
        apply(subst  (2) sym[OF sum_singleton[where f = "\<lambda> x. balance state' x"]])
        apply(subst  x_prop)
        apply(subst same_comp)
        unfolding state'_def by simp      
      moreover have "\<bar> (balance state') x \<bar> \<le> (1-\<epsilon>) * current_\<gamma> state'"
        using orlins_entry_after x_in_V unfolding orlins_entry_def by simp
      finally show ?thesis
        by simp
    qed
    have "sum (\<lambda> e. current_flow state' e) (\<Delta>\<^sup>+ Z \<union> \<Delta>\<^sup>- Z) = 
          sum (\<lambda> e. \<bar> current_flow state' e\<bar>) (\<Delta>\<^sup>+ Z \<union> \<Delta>\<^sup>- Z)"
      apply(rule sum_cong[of ])
      using e_flow_gr_0 unfolding Delta_plus_def Delta_minus_def by auto
    moreover have "sum (\<lambda> e. \<bar> current_flow state' e\<bar>) (\<Delta>\<^sup>+ Z \<union> \<Delta>\<^sup>- Z) = 
         sum (\<lambda> e. \<bar> current_flow state' e\<bar>) (\<Delta>\<^sup>+ Z) + 
             sum ((\<lambda> e. \<bar> current_flow state' e\<bar>)) (\<Delta>\<^sup>- Z)"
      apply(rule sum.union_disjoint)
      using rev_finite_subset[OF finite_E , of "\<Delta>\<^sup>+ Z"] rev_finite_subset[OF finite_E , of "\<Delta>\<^sup>- Z"] 
      unfolding Delta_plus_def Delta_minus_def by auto
    moreover have "sum (\<lambda> e. \<bar> current_flow state' e\<bar>) (\<Delta>\<^sup>+ Z) + 
             sum ((\<lambda> e. \<bar> current_flow state' e\<bar>)) (\<Delta>\<^sup>- Z) \<ge>
          \<bar> sum (current_flow state') (\<Delta>\<^sup>+ Z) - sum (current_flow state') (\<Delta>\<^sup>- Z) \<bar>"
      using sum_abs[of "current_flow state'" "\<Delta>\<^sup>+ Z"] sum_abs[of "current_flow state'" "\<Delta>\<^sup>- Z"] 
      by linarith
    moreover have "\<bar> sum (current_flow state') (\<Delta>\<^sup>+ Z) - sum (current_flow state') (\<Delta>\<^sup>- Z) \<bar>
                    = \<bar>sum \<b> Z - sum (balance state') Z \<bar>"
      using sumb_split flow_value2 by simp
    moreover have "... \<ge> \<bar>sum \<b> Z\<bar> - \<bar>sum (balance state') Z \<bar>"
      by simp
    moreover have "\<bar>sum \<b> Z\<bar> - \<bar>sum (balance state') Z \<bar> > 
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
      apply(subst  log_mult[of _  _2, simplified],  simp add: \<epsilon>_axiom, simp)
      unfolding assms(6) apply simp
      apply(subst add.commute[of "log 2 _"])
      apply(subst sym[OF diff_le_eq]) 
      apply(rule ord_eq_le_trans[OF _ real_nat_ceiling_ge]) 
      by argo
    moreover have " M * (8 * real N * current_\<gamma> state' / 2) \<ge>
                    M * (8 * real N * new_\<gamma> state')" 
      using N_gtr_0 M_gtr_zero  new_gamma_below_half_gamma[of state'] by simp
    ultimately have final_sum_chain:"sum (\<lambda> e. current_flow state' e) (\<Delta>\<^sup>+ Z \<union> \<Delta>\<^sup>- Z)  > 
              M * (8 * real N * new_\<gamma> state')" by argo
    have card_Delta_M:"card (\<Delta>\<^sup>+ Z \<union> \<Delta>\<^sup>- Z) \<le> M"
      unfolding M_def Delta_minus_def Delta_plus_def
      by(auto intro: card_mono[OF finite_E] )
    have "\<exists> e \<in> \<Delta>\<^sup>+ Z \<union> \<Delta>\<^sup>- Z. current_flow state' e > 8 * real N * new_\<gamma> state'"
    proof(rule ccontr, auto, goal_cases)
      case 1
      hence asm:"\<And> e. e \<in> \<Delta>\<^sup>+ Z \<union> \<Delta>\<^sup>- Z \<Longrightarrow> current_flow state' e \<le> 8 * real N * new_\<gamma> state'" by force
      have "sum (current_flow state') (\<Delta>\<^sup>+ Z \<union> \<Delta>\<^sup>- Z) 
           \<le> real M * (8 * real N * new_\<gamma> state')"
        apply(rule order.trans, rule sum_bounded_above[OF asm, of "\<Delta>\<^sup>+ Z \<union> \<Delta>\<^sup>- Z" id, simplified])
        using  card_Delta_M  M_gtr_zero N_gtr_0 new_gamma_state'_0 by simp
      thus?case using final_sum_chain by simp
    qed
    then obtain e where e_prop:"e \<in> \<Delta>\<^sup>+ Z \<union> \<Delta>\<^sup>- Z " " 8 * real N * new_\<gamma> state' < current_flow state' e"
      by auto
    hence e_E:"e \<in> \<E>"
      unfolding Delta_plus_def Delta_minus_def by auto
    have e_comps_neq:"connected_component (to_graph (\<FF>_imp state')) (fst e) \<noteq>
         connected_component (to_graph (\<FF>_imp state')) (snd e)" 
      using e_prop(1) same_comp connected_components_member_sym
      by (simp add: Z_def state'_def Delta_plus_def Delta_minus_def  same_comp) fast
    hence e_active: "e \<in> to_set (actives state')"
      using aux_invar_state' e_E unfolding aux_invar_def invar_aux13_def by auto
    have call_cond: "loopA_call_cond (state' \<lparr> current_\<gamma> := new_\<gamma> state'\<rparr>)"
      apply(rule loopA_call_condI[OF refl refl refl refl refl refl refl])
      using  e_active e_prop(2) 
             set_get(1)[OF invar_aux17_from_aux_invar[OF aux_invar_state', simplified invar_aux17_def],
                     of "(\<lambda>e. 8 * real N * new_\<gamma> state'  <
                        current_flow state' e)"]
      by (fastforce intro:  loopA_call_condI[OF refl refl refl refl refl refl])
  have e_comps:"connected_component (to_graph (\<FF>_imp (loopA (state'\<lparr>current_\<gamma> := new_\<gamma> state'\<rparr>)))) (fst e) =
                connected_component (to_graph (\<FF>_imp (loopA (state'\<lparr>current_\<gamma> := new_\<gamma> state'\<rparr>)))) (snd e)"
    using termination_of_loopA[OF _ refl] aux_invar_gamma[OF aux_invar_state'] aux_invar_def  e_active e_prop(2)
    apply(intro component_strict_increase[of "state'\<lparr>current_\<gamma> := new_\<gamma> state'\<rparr>" e])
    apply auto
    using set_get(1)[OF invar_aux17_from_aux_invar[OF aux_invar_state', simplified invar_aux17_def],
                     of "(\<lambda>e. 8 * real N * new_\<gamma> state'  <
                        current_flow state' e)"] 
    by (intro loopA_call_condI[OF refl refl refl refl refl refl refl ], simp, fast)
  have fst_snd_e_comp_Z:"Z = connected_component (to_graph (\<FF>_imp state')) (fst e) \<or>
                                Z = connected_component (to_graph (\<FF>_imp state')) (snd e)"
    using e_prop(1) same_comp[simplified sym[OF state'_def]]
    unfolding Delta_plus_def Delta_minus_def 
    using  connected_components_member_eq[of "fst e" "to_graph (\<FF>_imp state')" z] 
           connected_components_member_eq[of "snd e" "to_graph (\<FF>_imp state')" z] by auto
  have z_same_e:"connected_component (to_graph (\<FF>_imp (loopA (state'\<lparr>current_\<gamma> := new_\<gamma> state'\<rparr>)))) z =
        connected_component (to_graph (\<FF>_imp (loopA (state'\<lparr>current_\<gamma> := new_\<gamma> state'\<rparr>)))) (fst e)"
      using same_comp[simplified sym[OF state'_def]] e_comps fst_snd_e_comp_Z
            same_component_set_mono[OF  forest_increase[OF termination_of_loopA[OF _ refl]],
             of "state'\<lparr>current_\<gamma> := new_\<gamma> state'\<rparr>" z]    
          aux_invar_gamma[OF aux_invar_state', of "new_\<gamma> state'"] 
          invar_aux_to_invar_aux1  invar_aux17_from_aux_invar
      by fastforce
  have comps_monotone: " connected_component (to_graph (\<FF>_imp (state'\<lparr>current_\<gamma> := new_\<gamma> state'\<rparr>))) u
    \<subseteq> connected_component (to_graph (\<FF>_imp (loopA (state'\<lparr>current_\<gamma> := new_\<gamma> state'\<rparr>)))) u" for u
     using con_comp_subset[OF  forest_increase[OF termination_of_loopA[OF _ refl]],
             of "state'\<lparr>current_\<gamma> := new_\<gamma> state'\<rparr>" ]    
            aux_invar_gamma[OF aux_invar_state', of "new_\<gamma> state'"] 
            invar_aux_to_invar_aux1 invar_aux17_from_aux_invar by auto
   have disjoint_F_comps: 
       "connected_component (to_graph (\<FF>_imp state')) (fst e) \<inter> 
              connected_component (to_graph (\<FF>_imp state')) (snd e) = {}"
     using dVsI'(2)[of "make_pair e" "make_pair ` \<E>"] e_E 
           e_comps_neq unequal_components_disjoint [of _ "fst e" "snd e"]
           fst_E_V make_pair[OF refl refl] by auto
   have comp_strict_suubst_z:"connected_component (to_graph (\<FF>_imp state')) z
    \<subset> connected_component (to_graph (\<FF>_imp (loopA (state'\<lparr>current_\<gamma> := new_\<gamma> state'\<rparr>)))) z"
      apply(rule disjE[OF fst_snd_e_comp_Z])
      using z_same_e same_comp[simplified sym[OF state'_def]] fst_snd_e_comp_Z
      using  e_comps comps_monotone[of "fst e", simplified] comps_monotone[of "snd e", simplified]
             connected_component_non_empt[of "to_graph (\<FF>_imp state')" "(snd e)"] 
             connected_component_non_empt[of "to_graph (\<FF>_imp state')" "(fst e)"]disjoint_F_comps by auto
  have "connected_component (to_graph (\<FF>_imp ((orlins_one_step_check ^^ (Suc \<l>)) state))) z \<supset> 
        connected_component (to_graph (\<FF>_imp ((orlins_one_step_check ^^ \<l>) state))) z"
    apply(simp, subst orlins_one_step_check_def[of "(orlins_one_step_check ^^ \<l>) state"],simp add: 1(1)[of \<l>])
    unfolding orlins_one_step_def Let_def
    apply(subst loopB_changes_\<FF>_imp)
    subgoal
      using aux_invar_state' state'_def  invar_gamma_state'  remaining_balance_after 
      by(fastforce intro!: loopB_termination loopA_invar_gamma_pres aux_invar_gamma gamma_upd_aux_invar_pres)
    unfolding sym[OF new_\<gamma>_def[simplified  Let_def]] sym[OF state'_def]
    using comp_strict_suubst_z by simp
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
  shows   "\<exists> k \<le> \<l> + 1. (return ((compow k orlins_one_step_check) state) \<noteq> notyetterm) \<or>
                      card (comps \<V> (to_graph (\<FF>_imp state))) >
                      card (comps \<V> (to_graph (\<FF>_imp (compow k (orlins_one_step_check) state))))"
  apply(rule exE[OF if_important_then_comp_increase_or_termination[OF assms]])
  subgoal for k
    using orlins_some_steps_forest_increase[OF refl assms(2) assms(1) assms(3)] 
          assms(5)[simplified important_def] 
          orlins_compow_aux_invar_pres[OF assms(2) assms(1) assms(3),
             simplified aux_invar_def invar_aux15_def invar_aux5_def, of k] 
          number_of_comps_anti_mono_strict[of _ _ z] 
    by meson
  done

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
          "I = card (comps \<V> (to_graph (\<FF>_imp state)))"
    shows "return ((orlins_one_step_check ^^ (I * (\<l> + \<k> + 2))) state) \<noteq> notyetterm"
  using assms(3-)
proof(induction I arbitrary: state rule: less_induct)
  case (less F)
  hence uflow: "isuflow (current_flow state)"
    unfolding invar_isOptflow_def is_Opt_def isbflow_def by simp
  have F_1: "F \<ge> 1"
    using less(9) V_non_empt \<V>_finite card_image_le[of \<V> "connected_component (to_graph (\<FF>_imp state))"] 
          image_is_empty[of "connected_component (to_graph (\<FF>_imp state))" \<V>]
    unfolding comps_def 
    by (metis One_nat_def card_gt_0_iff finite_imageI less_Suc_eq_le linorder_not_le)
  obtain k where k_prop: "k \<le> \<k> + 1" "return ((orlins_one_step_check ^^ k) state) \<noteq> notyetterm \<or>
                  (\<exists>v. important ((orlins_one_step_check ^^ k) state) v) \<or>
                  card (comps \<V> (to_graph (\<FF>_imp ((orlins_one_step_check ^^ k) state)))) 
                              < card (comps \<V> (to_graph (\<FF>_imp state)))"
  using important_or_merge_or_termination[OF less(2) less(3) less(4) uflow less(5) assms(2)] by auto
  define state1 where "state1 = (orlins_one_step_check ^^ k) state"
  have invar_gamma_state1:"invar_gamma state1"
    using orlins_compow_invar_gamma_pres state1_def less(2-) by fast
  have aux_invar_state1: "aux_invar state1"
    using orlins_compow_aux_invar_pres state1_def less(2-) by fast
  have invar_integral_state1: "invar_integral state1"
    using orlins_compow_invar_integral_pres state1_def less(2-) by fast
  have invar_forest_state1: "invar_forest state1"
    using orlins_compow_invar_forest_pres state1_def less(2-) by fast
  have invar_isOptflow_state1: "invar_isOptflow state1"
    using orlins_compow_invar_isOptflow_pres state1_def less(2-) by fast
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
    then obtain v where v_prop:"important state1 v" using state1_def by auto
    have remaining_balance: "invar_non_zero_b state1"
      using some_balance_after_k_steps[OF 2(2) less(3) less(2) less(4)] state1_def by simp
    have orlins_entry_after_k: "orlins_entry state1"
     using orlins_entry_after_compow[OF less(3) less(2) less(4) 2(2) less(7)] state1_def by simp
   obtain l where l_prop:"l \<le> \<l> + 1" "return ((orlins_one_step_check ^^ l) state1) \<noteq> notyetterm \<or>
         card (comps \<V> (to_graph (\<FF>_imp ((orlins_one_step_check ^^ l) state1)))) 
               < card (comps \<V> (to_graph (\<FF>_imp state1)))"
     using if_important_then_merge_or_termination[OF invar_gamma_state1 aux_invar_state1 remaining_balance
           invar_integral_state1 v_prop assms(1) invar_forest_state1 orlins_entry_after_k invar_isOptflow_state1]
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
     hence 2: "card (comps \<V> (to_graph (\<FF>_imp ((orlins_one_step_check ^^ l) state1))))
                     < card (comps \<V> (to_graph (\<FF>_imp state1)))"
              "return ((orlins_one_step_check ^^ l) state1) = notyetterm" by simp+
     define state2 where "state2 = (orlins_one_step_check ^^ l) state1"
     define G where "G = card (comps \<V> (to_graph (\<FF>_imp state2)))"
     have G_less_F:"G < F" using G_def state2_def 2(1) 
           orlins_some_steps_card_decrease[OF state1_def less(3) less(2) less(4)] less(9) by simp
    have invar_gamma_state2:"invar_gamma state2"
      using orlins_compow_invar_gamma_pres state2_def  invar_gamma_state1  aux_invar_state1 
            remaining_balance 
      by fast
    have aux_invar_state2: "aux_invar state2"
       using orlins_compow_aux_invar_pres state2_def  invar_gamma_state1  aux_invar_state1 
            remaining_balance by fast
     have invar_integral_state2: "invar_integral state2"
       using orlins_compow_invar_integral_pres state2_def  invar_gamma_state1  aux_invar_state1 
            remaining_balance invar_integral_state1 orlins_entry_after_k invar_forest_state1 by fast
    have invar_forest_state2: "invar_forest state2"
       using orlins_compow_invar_forest_pres state2_def  invar_gamma_state1  aux_invar_state1 
            remaining_balance invar_forest_state1 orlins_entry_after_k by simp 
    have invar_isOptflow_state2: "invar_isOptflow state2"
      using orlins_compow_invar_isOptflow_pres state2_def invar_gamma_state1  aux_invar_state1 
            remaining_balance invar_forest_state1 invar_integral_state1 invar_isOptflow_state1 
            orlins_entry_after_k
      by fast
    have remaining_balance_state2: "invar_non_zero_b state2"
      using some_balance_after_k_steps[OF 2(2) aux_invar_state1 invar_gamma_state1 remaining_balance] 
            state2_def by simp
    have orlins_entry_after_l: "orlins_entry state2"
      using orlins_entry_after_compow[OF aux_invar_state1 invar_gamma_state1 remaining_balance
                                     , of l] state2_def 2(2) orlins_entry_after_k by simp
    have "return ((orlins_one_step_check ^^ (G * (\<l> + \<k> + 2))) state2) \<noteq> notyetterm"
      using less(1)[OF G_less_F invar_gamma_state2 aux_invar_state2 remaining_balance_state2
                   invar_integral_state2 invar_forest_state2 orlins_entry_after_l invar_isOptflow_state2 G_def] by simp
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
    hence 3: "card (comps \<V> (to_graph (\<FF>_imp ((orlins_one_step_check ^^ k) state)))) 
            < card (comps \<V> (to_graph (\<FF>_imp state)))"
             "return ((orlins_one_step_check ^^ k) state) = notyetterm" by simp+
    have remaining_balance: "invar_non_zero_b state1"
      using some_balance_after_k_steps[OF 3(2) less(3) less(2) less(4)] state1_def by simp
    have orlins_entry_after_k: "orlins_entry state1"
     using orlins_entry_after_compow[OF less(3) less(2) less(4) 3(2) less(7)] state1_def by simp
    define G where "G = card (comps \<V> (to_graph (\<FF>_imp state1)))"
    have G_less_F: "G < F" using 3 G_def less(9) state1_def by simp
    have "return ((orlins_one_step_check ^^ (G * (\<l> + \<k> + 2))) state1) \<noteq> notyetterm"
      using less(1)[OF G_less_F invar_gamma_state1 aux_invar_state1 remaining_balance invar_integral_state1
                   invar_forest_state1 orlins_entry_after_k invar_isOptflow_state1 G_def] by simp
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
          "return state = notyetterm"
          "state' = (orlins_one_step_check ^^ (Suc k)) state"
    shows "return state' = success \<Longrightarrow> is_Opt \<b> (current_flow state')"
  unfolding assms
  using assms(1-8)
  apply(induction k arbitrary: state)
  subgoal for state
    unfolding orlins_one_step_check_def
    by(auto intro: optimality_pres_orlins_one_step_check(2))
  subgoal for k state
    apply(subst funpow.simps(2), subst o_apply, subst orlins_one_step_check_def)
    apply(cases "return ((orlins_one_step_check ^^ Suc k) state)", simp)
    apply(subst (asm) (3) funpow.simps(2), subst (asm) o_apply)
    apply(subst (asm) orlins_one_step_check_def, simp)
    by((subst if_not_P, simp)+,
          (intro optimality_pres_orlins_one_step_check(2) orlins_compow_invar_forest_pres
                 orlins_compow_aux_invar_pres orlins_compow_invar_gamma_pres 
                 some_balance_after_k_steps orlins_entry_after_compow 
                 orlins_compow_invar_isOptflow_pres orlins_compow_invar_integral_pres |
           simp add: orlins_one_step_check_def)+)
  done

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
          "k > 0"
        shows "return state' = success \<Longrightarrow> is_Opt \<b> (current_flow state')"
  unfolding assms(9)
  using compow_correctness[OF assms(1-8) refl, of "k - 1"] assms(10) by simp

theorem compow_completeness:
  assumes "invar_gamma state"
          "aux_invar state"
          "invar_non_zero_b state"
          "invar_integral state"
          "invar_forest state"
          "orlins_entry state"
          "invar_isOptflow state"
          "return state = notyetterm"
          "state' = (orlins_one_step_check ^^ (Suc k)) state"
    shows "return state' = failure \<Longrightarrow> \<nexists> f. f is \<b> flow"
  unfolding assms
  using assms(1-8)
  apply(induction k arbitrary: state)
  subgoal for state
    unfolding orlins_one_step_check_def
    by(rule optimality_pres_orlins_one_step_check(3)[of state], auto)
  subgoal for k state
    apply(cases "return ((orlins_one_step_check ^^ Suc k) state)")
      apply(subst (asm) (2) funpow.simps(2), subst (asm) o_apply, subst (asm) orlins_one_step_check_def, simp)
    by(simp, (intro optimality_pres_orlins_one_step_check(3)[of "(orlins_one_step_check ^^ Suc k) state"]
                    some_balance_after_k_steps orlins_compow_invar_forest_pres orlins_compow_aux_invar_pres 
                    orlins_compow_invar_gamma_pres orlins_entry_after_compow  
                    orlins_compow_invar_integral_pres  orlins_compow_invar_isOptflow_pres| 
              simp add: orlins_one_step_check_def)+)
  done

corollary compow_completeness_gtr0:
  assumes "invar_gamma state"
          "aux_invar state"
          "invar_non_zero_b state"
          "invar_integral state"
          "invar_forest state"
          "orlins_entry state"
          "invar_isOptflow state"
          "return state = notyetterm"
          "state' = (orlins_one_step_check ^^ k) state"
          "k > 0"
    shows "return state' = failure \<Longrightarrow> \<nexists> f. f is \<b> flow"
  unfolding assms(9)
  using compow_completeness[OF assms(1-8) refl, of "k-1"] assms(10) by simp

lemma l_k_gtr_0: "(nat \<lceil>log 2 (real (4 * M * N) + (1 - \<epsilon>)) - log 2 \<epsilon>\<rceil> + 
                                      1 + nat (\<lceil>log 2 (real N)\<rceil> + 3) + 2) > 0"
  using M_def N_def finite_E \<V>_finite E_not_empty V_non_empt by simp

lemma number_of_comps_0: "card (comps \<V> X) > 0"
  unfolding comps_def
  using \<V>_finite V_non_empt by auto

theorem orlins_dom_and_results:
  assumes "return state = notyetterm"
          "invar_gamma state"
          "aux_invar state"
          "invar_non_zero_b state"
          "invar_integral state"
          "invar_forest state"
          "orlins_entry state"
          "invar_isOptflow state"
          "state' = orlins state"
    shows "orlins_dom state"
          "return state' = success \<Longrightarrow> is_Opt \<b> (current_flow state')"
          "return state' = failure \<Longrightarrow> \<nexists> f. f is \<b> flow"
          "return state' = notyetterm \<Longrightarrow> False"
  subgoal
   apply(rule conjunct1[OF succ_fail_term_same_check[OF refl assms(1)]])
   apply(rule sufficientE, rule finally_termination[OF refl refl assms(2-8) refl])
   using return.exhaust assms(1-8)[simplified invar_non_zero_b_def] by auto
  subgoal
   apply(rule sufficientE, rule finally_termination[OF refl refl assms(2-8) refl])
    unfolding assms(9)
    using return.exhaust  assms(4)[simplified invar_non_zero_b_def] l_k_gtr_0 number_of_comps_0
    apply(subst conjunct2[OF succ_fail_term_same_check[OF refl assms(1)]], fast,
          simp, subst (asm) conjunct2[OF succ_fail_term_same_check[OF refl assms(1)]]) 
       by( auto intro: compow_correctness_gtr0[OF assms(2-8) assms(1) refl])   
  subgoal
    apply(rule sufficientE, rule finally_termination[OF refl refl assms(2-8) refl])
    unfolding assms(9)
    using return.exhaust  assms(4)[simplified invar_non_zero_b_def] l_k_gtr_0 number_of_comps_0
    by(subst (asm) conjunct2[OF succ_fail_term_same_check[OF refl assms(1)]],
         fast, simp, intro compow_completeness_gtr0[OF assms(2-8) assms(1) refl], auto)
  apply(rule sufficientE, rule finally_termination[OF refl refl assms(2-8) refl])
  subgoal
    unfolding assms(9)
    apply(subst (asm) conjunct2[OF succ_fail_term_same_check[OF refl assms(1)]])
    using assms[simplified invar_non_zero_b_def] return.exhaust by auto
  done

definition "initial = \<lparr> current_flow = (\<lambda> e. 0), balance = \<b>,  \<FF> = {}, 
                        conv_to_rdg = default_conv_to_rdg, 
                        actives = filter (\<lambda> e. fst e \<noteq> snd e) \<E>_impl,
                        return = notyetterm, current_\<gamma> = Max { \<bar> \<b> v\<bar> | v. v \<in>\<V>},
                        representative = id, comp_card = (\<lambda> x. 1),
                        \<FF>_imp = empty_forest, 
                        not_blocked=(\<lambda> e. if e \<in> \<E> \<and> fst e \<noteq> snd e then True else False)\<rparr>"

lemma aux_invar_initial: "aux_invar initial"
proof(rule aux_invarI, goal_cases)
  case 1
  thus ?case
    apply(rule invar_aux1I)
    using initial_def \<E>_impl_meaning set_filter(1)
          set_filter(1)[OF  \<E>_impl_meaning(2), simplified \<E>_impl_meaning(1)]
    by(auto intro: invar_aux1I)
next
  case 2
  thus ?case
    apply(rule invar_aux2I)
    using empty_forest_axioms(1) neighb.set.set_isin neighb.set.invar_empty neighb.set.set_empty
    unfolding initial_def to_rdgs_def to_graph_def by simp 
next
  case 3
  thus?case
    apply(rule invar_aux3I)
    using empty_forest_axioms neighb.set.set_isin neighb.set.invar_empty neighb.set.set_empty
    unfolding initial_def to_rdgs_def to_graph_def  by simp
next
  case 4
  thus ?case
    apply(rule invar_aux4I)
    using empty_forest_axioms neighb.set.set_isin neighb.set.invar_empty neighb.set.set_empty
    unfolding initial_def to_rdgs_def to_graph_def by simp
next
  case 5
  thus ?case
    using initial_def default_conv_to_rdg 
    by(auto simp add: invar_aux6_def)
next
  case 6
  thus ?case
    by(auto intro: invar_aux8I simp add: initial_def)
next
  case 7
  thus ?case
    using empty_forest_axioms neighb.set.set_isin neighb.set.invar_empty neighb.set.set_empty  not_reachable_empt 
    by (fastforce intro: invar_aux7I simp add: initial_def to_graph_def)
next
  case 8
  thus ?case
    by(auto intro: invar_aux9I simp add: initial_def)
next
  case 9
  thus ?case
    using empty_forest_axioms neighb.set.set_isin neighb.set.invar_empty neighb.set.set_empty
   by(auto intro: invar_aux5I simp add: initial_def to_graph_def)
next
  case 10
  thus ?case
    using not_reachable_empt empty_forest_axioms neighb.set.set_isin neighb.set.invar_empty neighb.set.set_empty
    by (fastforce intro: invar_aux10I simp add: initial_def connected_component_def to_graph_def)
next
  case 11
  thus ?case
  proof(rule invar_aux11I, goal_cases)
    case (1 e)
    then show ?case
    unfolding initial_def  connected_component_def to_graph_def apply simp
    using  \<E>_impl_meaning  not_reachable_empt empty_forest_axioms neighb.set.set_isin 
           neighb.set.invar_empty neighb.set.set_empty
    by(subst (asm) set_filter[OF \<E>_impl_meaning(2)]) fastforce
  qed
next
  case 12
  thus ?case
    by(auto intro: invar_aux12I simp add: initial_def)
next
  case 13
  thus ?case
    using set_filter(1)[OF  \<E>_impl_meaning(2), simplified \<E>_impl_meaning(1)]
    using \<E>_impl_meaning(1) 
    by (intro invar_aux13I, auto simp add: initial_def )
next
  case 14
  thus ?case
    using empty_forest_axioms neighb.set.set_isin neighb.set.invar_empty neighb.set.set_empty
    by(auto intro!: invar_aux14I simp add: validF_def Vs_def initial_def to_graph_def dblton_graph_def)
next
  case 15
  thus ?case
    using empty_forest_axioms neighb.set.set_isin neighb.set.invar_empty neighb.set.set_empty
    by(auto intro: invar_aux15I simp add: Vs_def initial_def to_graph_def)
next
  case 16
  thus ?case    
    unfolding  invar_aux16_def initial_def connected_component_def  to_graph_def
    apply(simp, rule, rule sym)
    using  not_reachable_empt empty_forest_axioms neighb.set.set_isin neighb.set.invar_empty neighb.set.set_empty
    by (fastforce simp add: sym[OF is_singleton_altdef[simplified], simplified is_singleton_def])
next
  case 17
  thus ?case
    using invar_filter \<E>_impl_meaning
    by(simp add: invar_aux17_def initial_def) 
next
  case 18
  thus ?case
    using empty_forest_axioms 
    by (simp add: invar_aux18_def initial_def)
next
  case 19
  thus ?case
    using empty_forest_axioms neighb.set.set_isin neighb.set.invar_empty neighb.set.set_empty
    by (simp add: invar_aux19_def initial_def)
next
  case 20
  thus ?case
    using empty_forest_axioms neighb.set.set_isin neighb.set.invar_empty neighb.set.set_empty 
    by (simp add: invar_aux20_def initial_def)
next
  case 21
  show ?case
    using empty_forest_axioms neighb.set.set_isin neighb.set.invar_empty neighb.set.set_empty
    by(simp add: invar_aux21_def initial_def to_graph_def)
next
  case 22
  show ?case
    using empty_forest_axioms \<E>_impl_meaning set_filter(1) neighb.set.set_isin neighb.set.invar_empty neighb.set.set_empty
    by(simp add: invar_aux22_def initial_def to_graph_def to_rdgs_def)
qed
    
lemma invar_gamma_initial: "\<not> (\<forall> v \<in> \<V>. \<b> v = 0) \<Longrightarrow> invar_gamma initial"
  unfolding invar_gamma_def initial_def apply simp
  apply(rule bexE, simp)
  subgoal for x
    using Max_ge[of "{\<bar>\<b> v\<bar> |v. v \<in> \<V>}" "\<bar> \<b> x \<bar>"] \<V>_finite by fastforce
  done

lemma invar_forest_initial: "invar_forest initial"
  using empty_forest_axioms neighb.set.set_isin neighb.set.invar_empty neighb.set.set_empty
  unfolding invar_forest_def initial_def to_rdgs_def to_graph_def by simp

lemma invar_integral_initial: "invar_integral initial"
  unfolding invar_integral_def initial_def by simp

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

lemma invar_isOptflow_initial: "invar_isOptflow initial"
  unfolding invar_isOptflow_def initial_def 
  apply(intro no_augcycle_min_cost_flow)
  using u_non_neg   no_augcycle_at_beginning zero_ereal_def 
  unfolding isbflow_def isuflow_def ex_def
  by (auto , presburger)

lemma \<Phi>_initial: "invar_non_zero_b initial\<Longrightarrow> \<Phi> initial \<le> N"
  unfolding initial_def \<Phi>_def N_def apply simp
  apply(subst card_eq_sum, subst int_sum)
  apply(rule sum_mono)
  subgoal for v
    apply(rule exE[OF obtain_Max[OF \<V>_finite V_non_empt , of "\<lambda> x. \<bar> \<b> x \<bar>"]], simp)
    subgoal for x
      unfolding invar_non_zero_b_def
    apply(rule bexE[of \<V>  "\<lambda> v. \<b> v \<noteq> 0"], simp)
      subgoal for y
        apply(subst sym[OF one_add_one],rule add_mono, subst divide_le_eq_1_pos)
        using Max_ge[of " {\<bar>\<b> x\<bar> |x. x \<in> \<V>}" "\<bar> \<b> y \<bar>"]  Max_ge[of " {\<bar>\<b> x\<bar> |x. x \<in> \<V>}" ] 
              \<V>_finite \<epsilon>_axiom 
        by fastforce+
      done
    done
  done

lemma loopB_entry_initial: "loopB_entryF initial"
  using empty_forest_axioms neighb.set.set_isin neighb.set.invar_empty neighb.set.set_empty
  unfolding loopB_entryF_def initial_def to_rdgs_def to_graph_def by simp

theorem initial_state_orlins_dom_and_results:
  assumes "state' = orlins (loopB initial)"
    shows "orlins_dom (loopB initial)"
          "return state' = success \<Longrightarrow> is_Opt \<b> (current_flow state')"
          "return state' = failure \<Longrightarrow> \<nexists> f. f is \<b> flow"
          "return state' = notyetterm \<Longrightarrow> False"
proof-
  show "orlins_dom (loopB initial)"
  proof(cases "return (loopB initial)")
    case notyetterm
    then show ?thesis    
    proof(cases "\<forall> v \<in>\<V>. \<b> v = 0")
      case True
      thus ?thesis
        apply(subst loopB_simps'(1))
        unfolding loopB_succ_upd_def Let_def
        apply(rule loopB_succ_condI, simp, simp, simp, simp add: initial_def)
        by(auto intro:  loopB_succ_condI orlins.domintros)
    next
      case False
      thus  ?thesis
        apply(insert False notyetterm)
        apply(rule orlins_dom_and_results(1)[OF _ _ _ _ _ _ _ _ refl], simp)
        by(intro remaining_balance_after_loopB[OF loopB_termination refl, OF invar_gamma_initial]|
        (subst invar_forest_def, subst loopB_changes_\<F> ) |
        (fastforce intro: orlins_entry_after_loopB[OF _ refl] loopB_invar_isOpt_pres loopB_invar_aux_pres 
                            loopB_invar_gamma_pres  aux_invar_initial loopB_termination loopB_invar_integral_pres
                            invar_gamma_initial  invar_integral_initial  invar_isOptflow_initial
                  simp add: initial_def to_rdgs_def to_graph_def empty_forest_axioms
                            neighb.set.set_isin neighb.set.invar_empty neighb.set.set_empty))+
    qed
  qed (fastforce intro: orlins.domintros)+
  show "return state' = success \<Longrightarrow> is_Opt \<b> (current_flow state')"
  proof(goal_cases)
    case 1
    note succ_after = this
    show ?case
  proof(cases "return (loopB initial)")
    case notyetterm
    then show ?thesis    
    proof(cases "\<forall> v \<in>\<V>. \<b> v = 0")
      case True
      thus ?thesis
        apply(subst assms(1), subst loopB_simps'(1))
        unfolding loopB_succ_upd_def Let_def
        apply(rule loopB_succ_condI, simp, simp, simp, simp add: initial_def)
        apply(subst (asm) subst loopB_simps'(1), simp, simp add: notyetterm)
        apply(subst orlins.psimps, rule orlins.domintros)
        using invar_isOptflow_initial 
        unfolding invar_isOptflow_def initial_def is_Opt_def isbflow_def by auto
    next
      case False
      show ?thesis 
        apply(insert False notyetterm)
        apply(rule orlins_dom_and_results(2)[OF _ _ _ _ _ _ _ _ assms(1) succ_after])
        by(intro remaining_balance_after_loopB[OF loopB_termination refl, OF invar_gamma_initial]|
        (subst invar_forest_def, subst loopB_changes_\<F> ) |
        (fastforce intro: orlins_entry_after_loopB[OF _ refl] loopB_invar_isOpt_pres loopB_invar_aux_pres 
                            loopB_invar_gamma_pres  aux_invar_initial loopB_termination loopB_invar_integral_pres
                            invar_gamma_initial  invar_integral_initial  invar_isOptflow_initial
                  simp add: initial_def to_rdgs_def to_graph_def empty_forest_axioms
                          neighb.set.set_isin neighb.set.invar_empty neighb.set.set_empty))+
    qed
  next 
    case success
    show "is_Opt \<b> (current_flow state')"
      unfolding assms
    proof(subst orlins.psimps, fastforce intro: orlins.domintros simp add: success, simp add: success, 
            cases "\<forall> v \<in>\<V>. \<b> v = 0", goal_cases)
      case 1
      then show ?case
        apply(subst loopB_simps'(1))
        using invar_isOptflow_initial loopB_simps'(1)
        unfolding invar_isOptflow_def is_Opt_def isbflow_def initial_def loopB_succ_upd_def Let_def
        by (auto intro:  loopB_succ_condI)
    next
      case 2
      then show ?case
        using \<Phi>_initial[simplified invar_non_zero_b_def] loopB_entry_initial success
        by(fastforce intro: loopB_correctness loopB_invar_isOpt_pres aux_invar_initial 
                            loopB_termination 
                            invar_gamma_initial  invar_integral_initial  invar_isOptflow_initial
                   simp add: initial_def)
  qed 
   next 
     case failure
     hence "return state' = failure" unfolding assms
       by(subst orlins.psimps)
         (rule orlins.domintros, simp, simp, simp)
     thus "is_Opt \<b> (current_flow state')"
      using succ_after by simp
  qed
qed
  show "return state' = failure \<Longrightarrow> \<nexists>f. f is \<b> flow"
  proof(goal_cases)
    case 1
    note fail_after = this
    show ?case
  proof(cases "return (loopB initial)")
    case notyetterm
    then show ?thesis    
    proof(cases "\<forall> v \<in>\<V>. \<b> v = 0")
      case True
      thus ?thesis 
        apply(insert True fail_after notyetterm, subst (asm) loopB_simps'(1))
        unfolding loopB_succ_upd_def Let_def
         apply(rule loopB_succ_condI, simp, simp, simp, simp add: initial_def)
        by simp
    next
      case False
      thus ?thesis 
        apply(insert False fail_after notyetterm)
        apply(rule orlins_dom_and_results(3)[OF _ _ _ _ _ _ _ _ assms(1) fail_after])
        by(intro remaining_balance_after_loopB[OF loopB_termination refl, OF invar_gamma_initial]|
        (subst invar_forest_def, subst loopB_changes_\<F> ) |
        (fastforce intro: orlins_entry_after_loopB[OF _ refl] loopB_invar_isOpt_pres loopB_invar_aux_pres 
                            loopB_invar_gamma_pres  aux_invar_initial loopB_termination loopB_invar_integral_pres
                            invar_gamma_initial  invar_integral_initial  invar_isOptflow_initial
                  simp add: initial_def to_rdgs_def to_graph_def empty_forest_axioms
                            neighb.set.set_isin neighb.set.invar_empty neighb.set.set_empty))+
    qed
  next 
    case failure
    show "\<nexists>f. f is \<b> flow"
      using fail_after
    unfolding assms
    proof(subst (asm) orlins.psimps, fastforce intro: orlins.domintros simp add: failure, simp add: failure, 
            cases "\<forall> v \<in>\<V>. \<b> v = 0", goal_cases)
      case 1
      then show ?case
        apply(subst (asm) loopB_simps'(1))
        apply(fastforce intro: loopB_succ_condI simp add: initial_def)
        unfolding loopB_succ_upd_def Let_def
        by(subst (asm) orlins.psimps, rule orlins.domintros, auto)
    next
      case 2
      thus ?case
        using \<Phi>_initial[simplified invar_non_zero_b_def] loopB_entry_initial failure
        by(intro loopB_completeness[of initial, simplified],
           (fastforce intro: loopB_invar_isOpt_pres aux_invar_initial 
                            loopB_termination 
                            invar_gamma_initial  invar_integral_initial  invar_isOptflow_initial
            simp add:  initial_def to_graph_def empty_forest_axioms)+)
  qed 
   next 
     case success
     hence "return state' = success" unfolding assms
       by(subst orlins.psimps)
         (rule orlins.domintros, simp, simp, simp)
     thus "\<nexists>f. f is \<b> flow"
      using fail_after by simp
  qed
qed
  show "return state' = notyetterm \<Longrightarrow> False"
  proof(goal_cases)
    case 1
    note notyetterm_after = this
    show ?case
  proof(cases "return (loopB initial)")
    case notyetterm
    then show ?thesis    
    proof(cases "\<forall> v \<in>\<V>. \<b> v = 0")
      case True
      thus ?thesis 
        apply(insert True notyetterm,  subst (asm) loopB_simps'(1))
        unfolding loopB_succ_upd_def Let_def
        apply(rule loopB_succ_condI, simp, simp, simp, simp add: initial_def)
        by simp
    next
      case False
      thus ?thesis
        apply(insert False notyetterm)
        apply(rule orlins_dom_and_results(4)[OF _ _ _ _ _ _ _ _ assms(1) notyetterm_after])
        by(intro remaining_balance_after_loopB[OF loopB_termination refl, OF invar_gamma_initial]|
        (subst invar_forest_def, subst loopB_changes_\<F> ) |
        (fastforce intro: orlins_entry_after_loopB[OF _ refl] loopB_invar_isOpt_pres loopB_invar_aux_pres 
                            loopB_invar_gamma_pres  aux_invar_initial loopB_termination loopB_invar_integral_pres
                            invar_gamma_initial  invar_integral_initial  invar_isOptflow_initial
                  simp add: initial_def to_rdgs_def to_graph_def empty_forest_axioms
                            neighb.set.set_isin neighb.set.invar_empty neighb.set.set_empty))+
    qed
  next 
     case success
     hence "return state' = success" unfolding assms
       by(subst orlins.psimps)
         (rule orlins.domintros, simp, simp, simp)
     thus False
       using notyetterm_after by simp
  next 
     case failure
     hence "return state' = failure" unfolding assms
       by(subst orlins.psimps)
         (rule orlins.domintros, simp, simp, simp)
     thus False
      using notyetterm_after by simp
  qed
qed
qed

definition "orlins_ret1_cond state \<equiv>  (if return state = success then True
                 else if return state= failure then False
                 else (let f = current_flow state;
                      b = balance state;
                      \<gamma> = current_\<gamma> state;
                      E' = actives state;
                      \<gamma>' = (if \<forall> e \<in> to_set E'. f e = 0 then
                             min (\<gamma> / 2) (Max { \<bar> b v\<bar> | v. v \<in> \<V>})
                           else (\<gamma> / 2));
                      state' = loopA (state \<lparr>current_\<gamma> := \<gamma>' \<rparr>);
                      state'' = loopB state' 
                      in False)
)"

lemma orlins_ret1_condE: "orlins_ret1_cond state \<Longrightarrow>
                 \<lbrakk> return state = success \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  unfolding orlins_ret1_cond_def by presburger

lemma orlins_ret1_condI: " return state = success \<Longrightarrow> orlins_ret1_cond state"
  unfolding  orlins_ret1_cond_def by presburger

definition "orlins_call_cond state\<equiv> (if return state = success then False
                 else if return state= failure then False
                 else (let f = current_flow state;
                      b = balance state;
                      \<gamma> = current_\<gamma> state;
                      E' = actives state;
                      \<gamma>' = (if \<forall> e \<in> to_set E'. f e = 0 then
                             min (\<gamma> / 2) (Max { \<bar> b v\<bar> | v. v \<in> \<V>})
                           else (\<gamma> / 2));
                      state' = loopA (state \<lparr>current_\<gamma> := \<gamma>' \<rparr>);
                      state'' = loopB state' 
                      in True)
)"

lemma orlins_call_condE: "orlins_call_cond state \<Longrightarrow>
                 \<lbrakk> \<And> f b \<gamma> E' \<gamma>' state' state''. return state = notyetterm \<Longrightarrow>
                      f = current_flow state \<Longrightarrow>
                      b = balance state\<Longrightarrow>
                      \<gamma> = current_\<gamma> state \<Longrightarrow>
                      E' = actives state \<Longrightarrow>
                      \<gamma>' = (if \<forall> e \<in> to_set E' . f e = 0 then
                             min (\<gamma> / 2) (Max { \<bar> b v\<bar> | v. v \<in> \<V>})
                           else (\<gamma> / 2)) \<Longrightarrow>
                      state' = loopA (state \<lparr>current_\<gamma> := \<gamma>' \<rparr>) \<Longrightarrow>
                      state'' = loopB state'
                  \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  unfolding orlins_call_cond_def  Let_def 
  by(rule return.exhaust[of "return state"], simp, simp, simp)

lemma orlins_call_condI: " \<And> f b \<gamma> E' \<gamma>' state' state''. return state = notyetterm \<Longrightarrow>
                      f = current_flow state \<Longrightarrow>
                      b = balance state\<Longrightarrow>
                      \<gamma> = current_\<gamma> state \<Longrightarrow>
                      E' = actives state \<Longrightarrow>
                      \<gamma>' = (if \<forall> e \<in> to_set E' . f e = 0 then
                             min (\<gamma> / 2) (Max { \<bar> b v\<bar> | v. v \<in> \<V>})
                           else (\<gamma> / 2)) \<Longrightarrow>
                      state' = loopA (state \<lparr>current_\<gamma> := \<gamma>' \<rparr>) \<Longrightarrow>
                      state'' = loopB state'
                  \<Longrightarrow> orlins_call_cond state"
  unfolding  orlins_call_cond_def Let_def by force

definition "orlins_ret2_cond state \<equiv> (if return state = success then False
                 else if return state= failure then True
                 else (let f = current_flow state;
                      b = balance state;
                      \<gamma> = current_\<gamma> state;
                      E' = actives state;
                      \<gamma>' = (if \<forall> e \<in> to_set E'. f e = 0 then
                             min (\<gamma> / 2) (Max { \<bar> b v\<bar> | v. v \<in> \<V>})
                           else (\<gamma> / 2));
                      state' = loopA (state \<lparr>current_\<gamma> := \<gamma>' \<rparr>);
                      state'' = loopB state' 
                      in False))"

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

definition "orlins_upd state \<equiv> (let f = current_flow state;
                      b = balance state;
                      \<gamma> = current_\<gamma> state;
                      E' = actives state;
                      \<gamma>' = (if \<forall> e \<in> to_set E'. f e = 0 then
                             min (\<gamma> / 2) (Max { \<bar> b v\<bar> | v. v \<in> \<V>})
                           else (\<gamma> / 2));
                      state' = loopA (state \<lparr>current_\<gamma> := \<gamma>' \<rparr>);
                      state'' = loopB state' 
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
end
end