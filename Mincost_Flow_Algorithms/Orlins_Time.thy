section \<open>Formalisation of the Running Time of Orlin's Algorithm\<close>

theory Orlins_Time
  imports Maintain_Forest_Time Send_Flow_Time Orlins Laminar_Family
begin

locale orlins_time =
 maintain_forest_time where fst = fst + 
 send_flow_time where fst = fst + 
 orlins where fst = fst 
for fst::"'edge_type \<Rightarrow> 'a"+
fixes t\<^sub>O\<^sub>C::nat and  t\<^sub>O\<^sub>B::nat
begin  

function (domintros) orlins_time::"nat \<Rightarrow> ('e, 'f, 'c,'h, 'd, 'g, 'i) Algo_state  
                         \<Rightarrow> nat \<times> ('e, 'f, 'c,'h, 'd, 'g, 'i) Algo_state " where
"(orlins_time tt\<^sub>O\<^sub>C  state) = (if (return state = success) then (tt\<^sub>O\<^sub>C, state)
                 else if (return state = infeasible) then (tt\<^sub>O\<^sub>C, state)
                 else (let \<gamma>' = new_\<gamma> state;
                      state'time = maintain_forest_time (state \<lparr>current_\<gamma> := \<gamma>' \<rparr>);
                      state''time = send_flow_time (prod.snd state'time)
                      in ((t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B + prod.fst state'time + prod.fst state''time) 
                         +++ (orlins_time tt\<^sub>O\<^sub>C (prod.snd state''time))))
)"
  by auto

definition orlins_one_step_time::"('e, 'f, 'c,'h, 'd, 'g, 'i) Algo_state  
                                   \<Rightarrow> nat \<times>('e, 'f, 'c,'h, 'd, 'g, 'i) Algo_state " where
"orlins_one_step_time state =(  (let \<gamma>' = new_\<gamma> state;
                      state'time = maintain_forest_time (state \<lparr>current_\<gamma> := \<gamma>' \<rparr>);
                      state''time = send_flow_time (prod.snd state'time)
                      in ((t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B + prod.fst state'time + prod.fst state''time), (prod.snd state''time))))"

fun orlins_one_step_time_check::"nat \<times> ('e, 'f, 'c,'h, 'd, 'g, 'i) Algo_state 
                                  \<Rightarrow> nat \<times> ('e, 'f, 'c,'h, 'd, 'g, 'i) Algo_state " where
"orlins_one_step_time_check (t, state) = (  
                                 if return state = success then (t, state)
                                 else if return state = infeasible then (t, state)
                                 else (t +++ orlins_one_step_time state))"

lemma terminated_mono_one_step: "return (prod.snd ((orlins_one_step_time_check  ^^ i) init)) \<noteq> notyetterm \<Longrightarrow>
                                 (orlins_one_step_time_check  ^^ Suc i) init 
                                 = (orlins_one_step_time_check  ^^ i) init"
  apply(subst funpow.simps(2), simp, subst (2) surjective_pairing, subst orlins_one_step_time_check.simps) 
  using return.exhaust by auto
 
lemma terminated_mono: "return (prod.snd ((orlins_one_step_time_check  ^^ i) init)) \<noteq> notyetterm \<Longrightarrow>
                                 (orlins_one_step_time_check  ^^ (i + k )) init 
                                 = (orlins_one_step_time_check  ^^ i) init"
proof(induction k arbitrary: i init)
  case (Suc k)
  then show ?case
  apply(subst add.commute, subst add_Suc, subst add.commute)
  apply(subst funpow.simps(2), subst o_apply)
  apply(subst (2) surjective_pairing, subst orlins_one_step_time_check.simps)
  by (smt (z3) return.exhaust surjective_pairing)
qed simp

lemma succ_fail_not_changes_time:
  "return (prod.snd (t, state')) = success \<or> return (prod.snd (t, state')) = infeasible  
  \<Longrightarrow> compow k orlins_one_step_time_check (t, state') = (t, state')"
proof(induction k)
  case (Suc k)
  then show ?case
    by(subst funpow_Suc_right[of k orlins_one_step_time_check])
      (fastforce simp add: return.simps(2))
qed simp

lemma succ_fail_not_changes_time': 
 "return (prod.snd tstate) = success \<or> return (prod.snd tstate) = infeasible 
   \<Longrightarrow> compow k orlins_one_step_time_check tstate = tstate"
  using succ_fail_not_changes_time by(cases tstate) auto


lemma add_fst_assoc:"((a::nat) + b) +++ c = a +++ (b +++ c)"
  unfolding add_fst_def by simp

lemma orlins_time_dom_base_shift: "orlins_time_dom (t, state) \<Longrightarrow> orlins_time_dom (s, state)"
proof(induction  arbitrary: s rule: orlins_time.pinduct)
  case (1 t state)
  note IH = this
  show ?case
  proof(rule orlins_time.domintros, goal_cases)
    case (1 aa ba ab bb)
    show ?case 
      using 1 by (auto intro!: IH(2))
  qed
qed

lemma orlins_time_dom_base_extract: 
 "orlins_time_dom (t + s, state) \<Longrightarrow> 
 (orlins_time (t + s) state) = (t +++ (orlins_time s state))"
proof(induction  arbitrary: s t rule: orlins_time.pinduct)
  case (1 t state)
  note IH = this
  show ?case
  proof(subst orlins_time.psimps, goal_cases)
    case 1
    thus ?case
      using orlins_time_dom_base_shift IH(1) by simp
  next
    case 2
    thus ?case
    using orlins_time_dom_base_shift IH(1) 
    by(subst (2) orlins_time.psimps)
      (auto simp add: IH(2) add_fst_def Let_def)
 qed
qed

lemma succ_fail_term_same_with_time_dom:
"\<lbrakk>compow (Suc k) orlins_one_step_time_check (tt, state) = (tfin, state');
  return state' = success \<or> return state' = infeasible\<rbrakk>
  \<Longrightarrow>  orlins_time_dom (tt, state)"
proof(induction k arbitrary: state tt)
  case 0
  have A: "orlins_time_dom (tt, state)"
  proof(rule orlins_time.domintros, goal_cases)
    case (1 a b aa ba)
    have "(prod.fst (maintain_forest_time
         (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)) + tt + t\<^sub>O\<^sub>C +  t\<^sub>O\<^sub>B) +++
         send_flow_time (prod.snd (maintain_forest_time
         (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>))) =
          (tfin, state')"
      using 0[simplified] 1
      by(auto simp add: orlins_one_step_time_def orlins_one_step_time_check.simps Let_def add_fst_def)
    thus ?case 
      using 0(2)
      by(auto intro: orlins_time.domintros simp add: add_fst_def)
  qed
  thus ?case by simp
next
  case (Suc k)
    have aa:"(orlins_one_step_time_check ^^ (Suc (Suc k))) (tt, state) =
          (orlins_one_step_time_check ^^ Suc k) (orlins_one_step_time_check (tt, state))" 
      using funpow_Suc_right[of "Suc k" orlins_one_step_time_check] by simp
    show ?case 
    proof(cases "return (prod.snd (orlins_one_step_time_check (tt, state)))")
      case success
      note Success = this
      hence same_state:"(orlins_one_step_time_check ^^ Suc k) (orlins_one_step_time_check (tt, state)) = 
                       orlins_one_step_time_check (tt, state)"
        using succ_fail_not_changes_time[of"prod.fst (orlins_one_step_time_check (tt, state))" 
                                            "prod.snd (orlins_one_step_time_check (tt, state))" "Suc k"] 
        by (subst (2) sym[OF prod.collapse], subst (7) sym[OF prod.collapse])simp
      have A:"orlins_time_dom (tt, state)"
      proof(rule orlins_time.domintros, goal_cases)
        case (1 a b aa ba)
        then show ?case 
           using success(1) 
           by(auto intro: orlins_time.domintros simp add: orlins_one_step_time_def Let_def orlins_one_step_time_check.simps add_fst_def)
       qed
      then show ?thesis by simp
    next
      case infeasible
      note Failure = this
     hence same_state:"(orlins_one_step_time_check ^^ Suc k) (orlins_one_step_time_check (tt, state)) = 
                       orlins_one_step_time_check (tt, state)"
        using succ_fail_not_changes_time[of"prod.fst (orlins_one_step_time_check (tt, state))" 
                                            "prod.snd (orlins_one_step_time_check (tt, state))" "Suc k"] 
        by (subst (2) sym[OF prod.collapse], subst (7) sym[OF prod.collapse])simp
      have A:"orlins_time_dom (tt, state)"
      proof(rule orlins_time.domintros, goal_cases)
        case 1
        then show ?case 
           using infeasible(1) 1
           by(auto intro: orlins_time.domintros simp add: orlins_one_step_time_def Let_def orlins_one_step_time_check.simps add_fst_def)
       qed
      then show ?thesis by simp
    next
      case notyetterm
      hence "return state = notyetterm" 
        unfolding orlins_one_step_time_check.simps[of tt  state] add_fst_def 
        by (smt (verit, ccfv_SIG) return.exhaust snd_conv)
      hence last_step_swap:"(orlins_one_step_time_check ^^  k) 
                 (orlins_one_step_time_check (orlins_one_step_time_check (tt , state))) = 
             (orlins_one_step_time_check ^^  k) 
                 (orlins_one_step_time_check (tt + prod.fst (orlins_one_step_time  state),
                 prod.snd (orlins_one_step_time state)))"
        using orlins_one_step_time_check.simps[of tt  state]
        by(auto simp add: add_fst_def) 
      have dom_tt:"orlins_time_dom (tt + prod.fst (orlins_one_step_time  state) ,
                      prod.snd (orlins_one_step_time state))"                             
        apply(rule Suc(1)[OF _ Suc(3) ])
        using last_step_swap Suc(2)[simplified funpow_Suc_right o_apply] 
        by (subst funpow_Suc_right) auto
      have A:"orlins_time_dom (tt,state)"
      proof(rule orlins_time.domintros, goal_cases)
        case (1 aa ba ab bb)
        then show ?case 
          using orlins_time_dom_base_shift[OF  dom_tt(1)] 
          by(simp add: orlins_one_step_time_def Let_def)
       qed
      then show ?thesis by simp
    qed
 qed

lemma succ_fail_term_same_with_time:
  assumes "compow (Suc k) orlins_one_step_time_check (tt, state) = (tfin, state')"
          "return state' = success \<or> return state' = infeasible" 
    shows "orlins_time tt state  = (tfin, state')"
  using assms
proof(induction arbitrary:  tt k rule:
 orlins_time.pinduct[OF succ_fail_term_same_with_time_dom, of k tt state tfin state'])
  case 1
  show ?case
  using assms by simp
next
  case 2
  show ?case
    using assms by simp
next
  case (3 tt\<^sub>O\<^sub>C state  tt k)
  note IH=this
  show ?case
  proof(insert 3(1,3,4), 
        subst orlins_time.psimps, (rule succ_fail_term_same_with_time_dom;auto), 
        subst (asm)  funpow_Suc_right, subst (asm) o_apply, 
        subst (asm) orlins_one_step_time_check.simps, subst (asm) orlins_one_step_time_def, 
        cases "return state", goal_cases)
    case 3
    show ?case 
    proof(insert 3, subst if_not_P, goal_cases)
      case 2
      thus ?case
      proof( subst if_not_P, goal_cases)
      case 2
      thus ?case
        proof(subst (asm)  if_not_P, goal_cases)
        case 2
        thus ?case
        proof(subst (asm)  if_not_P,goal_cases)
        case 2
        show ?case
        proof(insert 2,(subst (asm) let_swap[of "add_fst tt"])+, cases k, goal_cases)
        case 1
        thus ?case
          by (smt (verit) add.commute add_fst_def fst_conv funpow_0 orlins_time.domintros orlins_time.psimps
              snd_conv)
        next
        case (2 nat)
        show ?case 
        apply(insert 2, (subst Let_def)+, subst sym[OF orlins_time_dom_base_extract])         
          by(fastforce intro!: succ_fail_term_same_with_time_dom[of "k - 1" _ _ tfin state'] IH(2)[where k10 = "k-1"] 
                     simp add: algebra_simps  Let_def add_fst_def sym[OF orlins_one_step_time_def[simplified Let_def]])+
      qed
    qed simp
  qed simp
qed simp
qed simp
    qed (auto simp add: terminated_mono[of 0, simplified])
  qed

lemmas maintain_forest_dom_underlying_invars = termination_of_maintain_forest'

lemma orlins_one_step_time_is_orlins_one_step:
      assumes "underlying_invars state" "invar_gamma state"
              "implementation_invar state"
              "invar_non_zero_b state"
              "orlins_entry state"
              "invar_forest state"
              "invar_integral state"
              "invar_isOptflow state"
shows "prod.snd (orlins_one_step_time state) = orlins_one_step state"
  by(auto intro!: invars_after_maintain_forest(10) invars_after_maintain_forest(11)  equal_results_B[symmetric] 
        simp add: assms  orlins_one_step_time_def orlins_one_step_def Let_def|
         subst equal_results_A[symmetric])+

lemma orlins_one_step_time_check_is_orlins_one_step_check:
      assumes "underlying_invars state" "invar_gamma state"
              "implementation_invar state"
              "invar_non_zero_b state"
              "orlins_entry state"
              "invar_forest state"
              "invar_integral state"
              "invar_isOptflow state"
       shows  "prod.snd (orlins_one_step_time_check (t, state)) = orlins_one_step_check state"
  by(auto simp add: orlins_one_step_time_is_orlins_one_step[OF assms] 
                   orlins_one_step_check_def add_fst_snd_same)
 
lemma invar_gamma_pres_orlins_one_step_time:
  assumes "underlying_invars state" "invar_gamma state" "invar_non_zero_b state"
              "implementation_invar state"
              "orlins_entry state"
              "invar_forest state"
              "invar_integral state"
              "invar_isOptflow state"
   shows "invar_gamma (prod.snd (orlins_one_step_time state))"
  using invar_gamma_pres_orlins_one_step[OF assms]
  by(auto simp add: orlins_one_step_time_is_orlins_one_step[OF assms(1,2,4,3,5-)])

lemma orlins_time_and_not_time_one_step_check_equal:
  assumes "underlying_invars state"
          "invar_gamma state"
          "invar_non_zero_b state"
           "implementation_invar state"
              "orlins_entry state"
              "invar_forest state"
              "invar_integral state"
              "invar_isOptflow state"
            shows " (prod.snd (orlins_one_step_time_check (t,state))) = orlins_one_step_check state"
  using orlins_one_step_time_check_is_orlins_one_step_check[OF assms(1,2,4,3,5-)] by blast

lemma orlins_time_and_not_time_one_step_equal:
  assumes "underlying_invars state"
          "invar_gamma state"
          "invar_non_zero_b state"
"implementation_invar state"
              "orlins_entry state"
              "invar_forest state"
              "invar_integral state"
              "invar_isOptflow state"
            shows "(prod.snd (orlins_one_step_time state)) = orlins_one_step state"
  using orlins_one_step_time_is_orlins_one_step[OF assms(1,2,4,3,5-)] by simp

lemma notyetterm_check_no_effect:"return state = notyetterm \<Longrightarrow> (orlins_one_step state) =  (orlins_one_step_check state)"
  by(simp add: orlins_one_step_check_def)

lemma notyetterm_check_no_effect_time:"return state = notyetterm \<Longrightarrow> (orlins_one_step_time state) =  (orlins_one_step_time_check (0, state))"
  by(simp add: add_fst_def)

lemma iterated_orlins_one_step_time_check_is_orlins_one_step_check:
      assumes "underlying_invars state" "invar_gamma state"
              "implementation_invar state"
              "invar_non_zero_b state"
              "orlins_entry state"
              "invar_forest state"
              "invar_integral state"
              "invar_isOptflow state"
              "state = prod.snd tstate"
       shows  "prod.snd ((orlins_one_step_time_check ^^k) tstate)
                    = (orlins_one_step_check^^k) state"
  using assms
proof(induction k arbitrary: tstate state)
  case (Suc k)
  have same_after_one_step:
            "prod.snd (orlins_one_step_time_check tstate) = 
             orlins_one_step_check state" 
    using  orlins_one_step_time_check_is_orlins_one_step_check[OF Suc(2-9), of "prod.fst tstate"]
    by(auto simp add:  Suc(10))
  show ?case 
    unfolding funpow_Suc_right o_apply
  proof(cases "return (orlins_one_step_check state)", goal_cases)
    case 1
    then show ?case
      by(auto simp add: succ_fail_not_changes_time' succ_fail_not_changes same_after_one_step)
  next
    case 2
    then show ?case
      by(auto simp add: succ_fail_not_changes_time' succ_fail_not_changes same_after_one_step)
  next
    case 3
    then show ?case 
    by(auto intro!: Suc(1) invars_pres_orlins_one_step_check 
          simp add: Suc(2-9) Suc(10)[symmetric] same_after_one_step)
  qed 
qed simp
 
lemma orlins_compow_time_invars_pres':
  assumes "underlying_invars state"
          "invar_gamma state"
          "invar_non_zero_b state"
          "final = (prod.snd ((orlins_one_step_time_check ^^ k) (t,state)))"
          "implementation_invar state"
          "orlins_entry state"
          "invar_forest state"
          "invar_integral state"
          "invar_isOptflow state"
    shows "underlying_invars final"
          "invar_gamma final"
          "implementation_invar final"
          "return final = notyetterm  \<Longrightarrow> orlins_entry final"
          "invar_forest final"
          "invar_integral final"  
          "invar_isOptflow final"
          "\<lbrakk> return final = success; k > 0; return state = notyetterm\<rbrakk> \<Longrightarrow>
           is_Opt \<b> (a_current_flow final)"
          "\<lbrakk>return final = infeasible; k > 0; return state = notyetterm \<rbrakk> \<Longrightarrow>
           \<nexists> f. f is \<b> flow"
          "return final = notyetterm \<Longrightarrow>  invar_non_zero_b final"
proof(unfold assms(4)  iterated_orlins_one_step_time_check_is_orlins_one_step_check[OF
      assms(1,2,5,3,6,7,8,9), of "(t, state)", simplified], goal_cases)
  case 1
  thus ?case
    using orlins_compow_underlying_invars_pres[OF assms(1,2,3,5,6,7,8,9)]
    by auto
next
  case 2
  thus ?case
    using orlins_compow_invar_gamma_pres[OF assms(1,2,3,5,6,7,8,9)]
    by auto
next
  case 3
  thus ?case
    using orlins_compow_implementation_invar_pres[OF assms(1,2,3,5,6,7,8,9)]
    by auto
next
  case 4
  thus ?case
    using orlins_entry_after_compow[OF assms(1,2,3) _ assms(6,5,7,8,9)]
    by auto
next
  case 5
  thus ?case 
    using orlins_compow_invar_forest_pres[OF assms(1,2,3,5,6,7,8,9)]
    by auto
next
  case 6
  thus ?case
    using  orlins_compow_invar_integral_pres[OF assms(1,2,3,5,6,7,8,9)] 
    by auto
next
  case 7
  thus ?case
    using orlins_compow_invar_isOptflow_pres[OF assms(1,2,3,5,6,7,8,9)]
    by auto
next
  case 8
  thus ?case
    using compow_correctness_gtr0[OF assms(2,1,3,8,7,6,9) _ refl _ assms(5)] 
    by auto
next
  case 10
  thus ?case
    using  some_balance_after_k_steps[OF _ assms(1,2,3,5,6,7,8,9)]
    by auto
next
  case 9
  thus ?case
    using compow_completeness_gtr0[OF assms(2,1,3,8,7,6,9,5)]
    by auto
qed

lemma orlins_compow_time_invars_pres:
  assumes "underlying_invars state"
          "invar_gamma state"
          "invar_non_zero_b state"
          "final = (prod.snd ((orlins_one_step_time_check ^^ k) (t,state)))"
          "implementation_invar state"
          "orlins_entry state"
          "invar_forest state"
          "invar_integral state"
          "invar_isOptflow state"
    shows "underlying_invars final \<and> invar_gamma final \<and>
           final = (orlins_one_step_check ^^ k) state \<and>
          (return final = notyetterm \<longrightarrow> invar_non_zero_b final) \<and>
          implementation_invar final \<and>
          (return final = notyetterm \<longrightarrow> orlins_entry final) \<and>
          invar_forest final \<and> invar_integral final \<and> invar_isOptflow final"
  using orlins_compow_underlying_invars_pres[OF assms(1,2,3,5,6,7,8,9)]
        orlins_compow_invar_gamma_pres[OF assms(1,2,3,5,6,7,8,9)]
        orlins_entry_after_compow[OF assms(1,2,3) _ assms(6,5,7,8,9)]
        orlins_compow_implementation_invar_pres[OF assms(1,2,3,5,6,7,8,9)]
        orlins_compow_invar_forest_pres[OF assms(1,2,3,5,6,7,8,9)]
        orlins_compow_invar_integral_pres[OF assms(1,2,3,5,6,7,8,9)]
        orlins_compow_invar_isOptflow_pres[OF assms(1,2,3,5,6,7,8,9)]
        some_balance_after_k_steps[OF _ assms(1,2,3,5,6,7,8,9)]
  by(auto simp add: assms(4) 
        iterated_orlins_one_step_time_check_is_orlins_one_step_check[OF
              assms(1,2,5,3,6,7,8,9), of "(t, state)", simplified]) 

lemma same_as_without_time:
  assumes "underlying_invars state"
          "invar_gamma state"
          "invar_non_zero_b state"
          "implementation_invar state"
          "orlins_entry state"
          "invar_forest state"
          "invar_integral state"
          "invar_isOptflow state"
 shows "prod.snd ((orlins_one_step_time_check ^^ i) (t, state)) = (orlins_one_step_check ^^ i) state"
  using iterated_orlins_one_step_time_check_is_orlins_one_step_check assms by auto

lemma Phi_contribution_important:
  assumes "invar_non_zero_b state" "invar_gamma state" "orlins_entry state"
          "v \<in> \<V>" "\<gamma>' = new_\<gamma> state" "implementation_invar state" "underlying_invars state"
  shows "(\<lceil>\<bar> a_balance state v\<bar> / \<gamma>' - (1 - \<epsilon>)\<rceil> = 1 \<longleftrightarrow> important state v)
        \<and> (\<lceil>\<bar> a_balance state v\<bar> / \<gamma>' - (1 - \<epsilon>)\<rceil> = 0 \<longleftrightarrow> \<not> important state v)"
proof
  show goal1:"(\<lceil>\<bar>a_balance state v\<bar> / \<gamma>' - (1 - \<epsilon>)\<rceil> = 1) = important state v"
  proof(rule iffI, goal_cases)
    case 1
    then show ?case 
    using balance_less_new_gamma[OF assms(7,2,6,1,3,4)] Phi_init(2,3)[OF assms(3,1,2,6,7,4)]
         assms(2,4,5) \<epsilon>_axiom(4) zero_less_divide_iff[of "\<bar>a_balance state v\<bar>" "new_\<gamma> state"] 
    by(force simp only: invar_gamma_def important_def ceil_is_int_iff_range
                      linordered_field_class.pos_less_divide_eq[symmetric])
next
  case 2
  moreover have "real_of_int 1 - 1 = 0" by simp
  moreover have "0 < \<bar>a_balance state v\<bar>"
    using balance_less_new_gamma[OF assms(7,2,6,1,3,4)] assms(2,4,5) \<epsilon>_axiom(4) 2
    by(auto simp : invar_gamma_def important_def mult_less_0_iff) 
  moreover hence "1 - \<epsilon> <  \<bar>a_balance state v\<bar> / new_\<gamma> state"
    using balance_less_new_gamma[OF assms(7,2,6,1,3,4)] Phi_init(2,3)[OF assms(3,1,2,6,7,4)]
         assms(2,4,5)  2  mult_less_0_iff[of 2 "new_\<gamma> state"] 
    by(auto simp : invar_gamma_def important_def intro!: mult_imp_less_div_pos) 
  ultimately show ?case 
    using  Phi_init(2,3)[OF assms(3,1,2,6,7,4)] assms(2,4,5) \<epsilon>_axiom(4)
    by(auto simp only: invar_gamma_def important_def ceil_is_int_iff_range ceiling_le_iff)
qed
  show "(\<lceil>\<bar>a_balance state v\<bar> / \<gamma>' - (1 - \<epsilon>)\<rceil> = 0) = (\<not> important state v)"
  proof(rule iffI, goal_cases)
    case 1
    then show ?case  
    using balance_less_new_gamma[OF assms(7,2,6,1,3,4)] Phi_init(2,3)[OF assms(3,1,2,6,7,4)]
         assms(2,4,5) \<epsilon>_axiom(4) goal1
    by(auto intro!: importantI)
  next
    case 2
    moreover hence "\<bar>a_balance state v\<bar> / new_\<gamma> state \<le> 1 - \<epsilon>"
     using balance_less_new_gamma[OF assms(7,2,6,1,3,4)] assms(2,4,5) \<epsilon>_axiom(4) 
           less_divide_eq[of "1 - \<epsilon>" " \<bar>a_balance state v\<bar>" "new_\<gamma> state"]
     by(unfold important_def ) argo
    ultimately show ?case 
      using Phi_init(2,3)[OF assms(3,1,2,6,7,4)] assms(2,4,5) 
      by(auto simp add: important_def invar_gamma_def ceil_is_int_iff_range)
  qed
qed

lemma runtime_add_constant:
  "(orlins_one_step_time_check  ^^ i) (t + s, state) = 
    t +++ (orlins_one_step_time_check  ^^ i) (s, state)"
proof(induction i arbitrary: s t state)
  case (Suc i)
  then show ?case 
  apply(subst funpow_Suc_right)+
  by (auto simp add: add_fst_def)
qed (simp add: add_fst_def)
 
theorem running_time_sum_general:
  assumes "final = (orlins_one_step_time_check  ^^ i) (0, state)"
          "return (prod.snd final) = notyetterm"
          "underlying_invars state"
          "invar_gamma state"
          "invar_non_zero_b state"
          "orlins_entry state"
          "implementation_invar state"
          "invar_forest state"
          "invar_integral state"
          "invar_isOptflow state"
    shows "prod.fst final \<le> (card (comps \<V> (to_graph (\<FF> state))) 
                                    - card (comps \<V> (to_graph (\<FF> (prod.snd final)))))
                                   * (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) 
                   +  i * (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f + t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B ) +
                     (\<Sum> j \<in> {1..i}. (let state' = ((orlins_one_step_check ^^ (j - 1)) state) in 
                                                     card { v. important state' v} )) 
                           *(t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f)"
  using assms
proof(induction i arbitrary: final state)
  case 0
  then show ?case by simp
next
  case (Suc i)
  have i_notyetterm:"return (prod.snd ((orlins_one_step_time_check ^^ i) (0, state))) = notyetterm"
    using Suc.prems(1) Suc.prems(2) terminated_mono_one_step by force
  define already_done where "already_done = (prod.snd ((orlins_one_step_time_check ^^ i) (0, state)))"
  have "(orlins_one_step_time_check ^^ Suc i) (0, state) = 
       prod.fst ((orlins_one_step_time_check ^^ i) (0, state)) +++ orlins_one_step_time already_done" 
    apply(subst funpow.simps(2), simp, subst (2) surjective_pairing, subst orlins_one_step_time_check.simps(1))
    using i_notyetterm 
    by(simp add: already_done_def add_fst_def)
  define f where "f = current_flow already_done"
  define b where "b = balance already_done" 
  define \<gamma> where "\<gamma> = current_\<gamma> already_done"
  define E' where "E' = actives already_done"
  define \<gamma>' where "\<gamma>' = new_\<gamma> already_done"
  define state'time where "state'time = maintain_forest_time (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)"
  define state''time where "state''time = send_flow_time (prod.snd state'time)"
  have orlins_one_step_time_unfolded:"orlins_one_step_time already_done = (t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B + prod.fst state'time + prod.fst state''time, prod.snd state''time)"
    by(simp add: orlins_one_step_time_def state''time_def state'time_def \<gamma>'_def E'_def \<gamma>_def b_def f_def Let_def)
  define bigsum where "bigsum = (card (comps \<V> (to_graph (\<FF> state))) - card (comps \<V> (to_graph (\<FF> already_done)))) *
         (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) + i * (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f + t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B) +
         (\<Sum>j = 1..i.
            let state' = (orlins_one_step_check ^^ (j - 1)) state
            in card {a. important state' a}) * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f)" 
  have bigsum_bound:"prod.fst ((orlins_one_step_time_check ^^ i) (0, state))
       \<le> bigsum"
    using Suc(1)[OF refl i_notyetterm Suc(4-11)] already_done_def  Suc.prems(5) Suc.prems(6) 
          bigsum_def by blast
  have underlying_invars_after_gamma: "underlying_invars (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)"
    using Suc.prems(3) Suc.prems(4) Suc.prems(5) already_done_def underlying_invars_gamma 
          orlins_compow_time_invars_pres[OF Suc(4,5,6) refl Suc(8,7,9,10,11)] by blast
  define timeA where "timeA = (card (comps \<V> (to_graph (\<FF> already_done))) - 
      card (comps \<V> (to_graph (\<FF> (prod.snd (maintain_forest_time 
                       (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>))))))) *
  (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B) +
  (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C)"
  have return_already_done: "return already_done = notyetterm" 
    using already_done_def i_notyetterm by blast
  have invars_already_done:  "underlying_invars already_done"
          "invar_gamma already_done"
          "implementation_invar already_done"
          "invar_non_zero_b already_done"
          "orlins_entry already_done"
          "invar_forest already_done"
          "invar_integral already_done"
          "invar_isOptflow already_done"
    using orlins_compow_time_invars_pres'[OF Suc(4-6) refl Suc(8,7,9,10,11), of i 0,
                      simplified already_done_def[symmetric]]
    by (auto simp add: return_already_done)
  have underlying_invars_after_gamma: "underlying_invars (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)"
    and other_invars_after_gamma:  "implementation_invar (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)"
         "invar_gamma (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)"
          "invar_non_zero_b (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)"
          "invar_integral (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)"
          "invar_isOptflow (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)"
    by (auto intro!: underlying_invars_gamma  implementation_invar_gamm_upd 
                     gamma_upd_underlying_invars_pres invar_integral_gamma_upd 
                     gamma_upd_invar_non_zero_b_pres invar_isOpt_gamma_change
                      invars_already_done
           simp add: \<gamma>'_def )
  have timeA:"prod.fst state'time  = timeA"
    by(auto intro!: time_boundA[of "already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>", simplified]
                        maintain_forest_dom_underlying_invars underlying_invars_after_gamma
          simp add: state'time_def timeA_def terminationA_iff[symmetric] other_invars_after_gamma)
  note invar_and_other_properties_after_forest = 
      invars_after_maintain_forest[OF  invars_already_done]
  have state'time_is:"prod.snd state'time = maintain_forest (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)"
    unfolding state'time_def 
    apply(subst equal_results_A[symmetric])
    by(auto intro!: maintain_forest_dom_underlying_invars
          simp add: underlying_invars_after_gamma other_invars_after_gamma)
  have underlying_invars_state'time:"underlying_invars (prod.snd state'time)"
   and invar_gamma_after_gamma:"invar_gamma (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)"
   and invar_gamma_state'time:"invar_gamma (prod.snd state'time)"
   and others_in_state': "implementation_invar (prod.snd state'time)"
     "invar_integral (prod.snd state'time)" "invar_isOptflow (prod.snd state'time)"
     "invar_above_6Ngamma (prod.snd state'time)"   
    using invar_and_other_properties_after_forest other_invars_after_gamma(2) 
    by(auto simp add: state'time_is \<gamma>'_def)
  have send_flow_time_phi:"prod.fst (send_flow_time (prod.snd state'time))
       \<le> nat (\<Phi> (prod.snd state'time)) * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) + (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f)"
    using  time_boundB[OF invar_gamma_state'time refl]  underlying_invars_state'time
           others_in_state'(1,2,3,4) by fastforce
  have Phi_mod_A:"\<Phi>  (prod.snd state'time)
       \<le> \<Phi> (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>) + int (card (comps \<V> (to_graph (\<FF> already_done)))) -
             int (card (comps \<V> (to_graph (\<FF> (maintain_forest (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>))))))"
    using  Phi_increase[OF underlying_invars_after_gamma invar_gamma_after_gamma other_invars_after_gamma(1)]
           other_invars_after_gamma(1)
    by(simp add: state'time_is)
  have send_flow_dom_after_forest: 
          "send_flow_dom (prod.snd state'time)"
    using \<gamma>'_def invar_and_other_properties_after_forest(11) state'time_is by fastforce
  have send_flow_is_same:
      "prod.snd (local.send_flow_time (prod.snd state'time)) = send_flow (prod.snd state'time)"
    using equal_results_B send_flow_dom_after_forest by auto
  have to_graph_final_is:"to_graph (\<FF> (prod.snd final)) = to_graph (\<FF> (prod.snd state''time))"
    unfolding Suc 
    apply(subst funpow.simps(2), subst o_apply, subst (2) surjective_pairing, subst orlins_one_step_time_check.simps)
    using i_notyetterm 
    by(simp add: add_fst_def  orlins_one_step_time_def state''time_def state'time_def already_done_def
               \<gamma>'_def E'_def f_def \<gamma>_def b_def Let_def)
  have card_maintain_forest_reduce:"card (comps \<V> (to_graph (\<FF> already_done))) \<ge>
             card (comps \<V> (to_graph (\<FF> (maintain_forest (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)))))"
    unfolding new_gamma_changes(1)[of already_done, symmetric] \<gamma>'_def
    using invar_and_other_properties_after_forest(10) 
          underlying_invars_gamma invars_already_done(1)  other_invars_after_gamma(1) 
    by(intro card_decrease)(auto simp add: \<gamma>'_def)
  have orlins_entry_late:"orlins_entry ((orlins_one_step_check ^^ i) state)"
    using Suc  same_as_without_time[OF Suc(4) Suc(5) Suc(6)]  i_notyetterm 
    by (auto intro:  orlins_entry_after_compow)
  note same_as_without_time2=same_as_without_time[OF Suc(4,5,6,8,7,9,10,11), of i 0]
  have invars_late: "invar_non_zero_b  ((orlins_one_step_check ^^ i) state)"
                    "invar_gamma ((orlins_one_step_check ^^ i)  state)"
    using  invars_already_done unfolding already_done_def same_as_without_time2
    by auto
  have Phi_number_important:"state' = (orlins_one_step_check ^^ i) state \<Longrightarrow>
         \<Phi> (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>) = card {a. important (state') a}" for state'
    unfolding  already_done_def \<gamma>'_def E'_def f_def b_def \<gamma>_def 
               sym[OF new_\<gamma>_def[simplified Let_def]] \<Phi>_def 
    apply((subst  same_as_without_time2)+ , rule trans)
     using Phi_contribution_important[OF invars_already_done(4,2,5) _ refl invars_already_done(3,1)] 
     by (fastforce intro!: binary_sum[OF \<V>_finite] arg_cong[of _ _ int] arg_cong[of _ _ card] 
                 simp add: important_def already_done_def same_as_without_time2)+
   have "prod.fst (orlins_one_step_time already_done)
         = prod.fst state'time + prod.fst state''time + t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B"
     by(simp add: orlins_one_step_time_def state'time_def state''time_def \<gamma>'_def \<gamma>_def E'_def f_def b_def Let_def)
   also have "... \<le> timeA + nat (\<Phi> (prod.snd state'time)) * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) + (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f) +
                      t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B"
     using timeA send_flow_time_phi unfolding state''time_def by simp
   also have "... \<le> timeA + ( nat(\<Phi> (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)) +
                                    (card (comps \<V> (to_graph (\<FF> already_done)))) -
                               card (comps \<V> (to_graph (\<FF> (local.maintain_forest (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)))))) * 
                            (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) + (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f) +
                      t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B"
     using Phi_mod_A card_maintain_forest_reduce by auto
   also have "... \<le> (card (comps \<V> (to_graph (\<FF> already_done))) 
                             - card (comps \<V> (to_graph (\<FF> (maintain_forest (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)))))) *
       (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
       (nat (\<Phi> (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>))) * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
       (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f + t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C) + t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B"
     using state'time_is[simplified state'time_def]  add_mult_distrib2 less_or_eq_imp_le 
     by(auto simp add: add_mult_distrib diff_add_assoc[OF card_maintain_forest_reduce]  timeA_def)
   also have "... \<le> (card (comps \<V> (to_graph (\<FF> already_done))) 
                           - card (comps \<V> (to_graph (\<FF> (local.maintain_forest (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)))))) *
       (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
       card {v . important already_done v } * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
       (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f + t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B)"
     using Phi_number_important[OF refl, simplified sym[OF already_done_def]]   
           same_as_without_time2[ simplified sym[OF already_done_def]] 
     by simp
   finally have ineq_for_one_it:"prod.fst (orlins_one_step_time already_done)
     \<le> (card (comps \<V> (to_graph (\<FF> already_done))) 
               - card (comps \<V> (to_graph (\<FF> (local.maintain_forest (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)))))) *
        (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
       card {v. important already_done v} * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
        (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f + t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B) " by simp
   have forest_final:"to_graph (\<FF> (local.maintain_forest (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>))) 
                         = to_graph (\<FF> (prod.snd final))" 
     unfolding Suc(2)
   proof(subst funpow.simps(2), subst o_apply, subst (2) surjective_pairing, 
       subst orlins_one_step_time_check.simps, goal_cases)
     case 1
     thus ?case
       using orlins_one_step_time_unfolded send_flow_dom_after_forest send_flow_is_same i_notyetterm
       by (fastforce intro!: cong[OF refl, of  _ _ to_graph] simp add: add_fst_def already_done_def send_flow_changes_\<FF> state''time_def state'time_is)
   qed
   have card_decrease_done:"(card (comps \<V> (to_graph (\<FF> state))) \<ge>
                card (comps \<V> (to_graph (\<FF> already_done))))"
     using orlins_some_steps_card_decrease[OF refl Suc(4,5,6,8,7,9,10,11)]
     by(auto simp add: already_done_def  same_as_without_time2)
   show ?case 
   proof(subst Suc(2), subst funpow.simps(2), subst o_apply, subst (2) surjective_pairing, 
       subst orlins_one_step_time_check.simps, goal_cases)
     case 1
     show ?case
     proof((subst if_not_P, subst i_notyetterm, rule return.simps(4,6))+, goal_cases)
       case 1
       show ?case
         unfolding add_fst_def
       proof(subst fst_conv, subst sym[OF already_done_def], goal_cases)
         case 1
         show ?case
         proof(rule order.trans[OF  add_mono[OF bigsum_bound ineq_for_one_it]], goal_cases)
           case 1
           show ?case
           proof(subst sym[OF forest_final], unfold bigsum_def, subst (4)already_done_def, 
               subst same_as_without_time2, goal_cases)
             case 1
             show ?case
               apply(subst add_assoc2, subst add_assoc2)
               apply(subst (16) semiring_normalization_rules(24), subst add_assoc3, 
                   subst semiring_normalization_rules(1))
               using card_maintain_forest_reduce card_decrease_done 
               by(auto simp add: algebra_simps)
           qed
         qed
       qed
     qed
   qed
 qed

 
theorem running_time_sum:
  assumes "final = (orlins_one_step_time_check  ^^ (Suc i)) (0, state)"
          "return (prod.snd final) \<noteq> notyetterm"
          "underlying_invars state"
          "invar_gamma state"
          "invar_non_zero_b state"
          "orlins_entry state"
          "\<And> j final. j \<le> i \<Longrightarrow> final = (orlins_one_step_time_check  ^^ j) (0, state)
              \<Longrightarrow> return (prod.snd final) = notyetterm"
          "implementation_invar state"
          "invar_forest state"
          "invar_integral state"
          "invar_isOptflow state"
    shows "prod.fst final \<le> (card (comps \<V> (to_graph (\<FF> state))) 
                                  - card (comps \<V> (to_graph (\<FF> (prod.snd final)))))
                                  * (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) 
                   +  i * (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f + t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B ) +
                     (\<Sum> j \<in> {1.. Suc i}. (let state' = ((orlins_one_step_check ^^ (j - 1)) state) in 
                                                     card { v. important state' v} )) 
                           *(t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f)+
                       (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f + t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B)"
proof-
  note Suc = assms
  have i_notyetterm:"return (prod.snd ((orlins_one_step_time_check ^^ i) (0, state)))
                         = notyetterm"
    using Suc(7)[of i] by simp
  define already_done where "already_done = (prod.snd ((orlins_one_step_time_check ^^ i) (0, state)))"
  have "(orlins_one_step_time_check ^^ Suc i) (0, state) = 
       prod.fst ((orlins_one_step_time_check ^^ i) (0, state))
                   +++ orlins_one_step_time already_done" 
    apply(subst funpow.simps(2), simp, subst (2) surjective_pairing, subst orlins_one_step_time_check.simps(1))
    using i_notyetterm 
    by(simp add: already_done_def add_fst_def)
  define f where "f = current_flow already_done"
  define b where "b = balance already_done" 
  define \<gamma> where "\<gamma> = current_\<gamma> already_done"
  define E' where "E' = actives already_done"
  define \<gamma>' where "\<gamma>' = new_\<gamma> already_done"
  define state'time where "state'time = maintain_forest_time (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)"
  define state''time where "state''time = send_flow_time (prod.snd state'time)"
  have orlins_one_step_time_unfolded:"orlins_one_step_time already_done = (t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B + prod.fst state'time + prod.fst state''time, prod.snd state''time)"
    by(simp add: orlins_one_step_time_def state''time_def state'time_def \<gamma>'_def E'_def \<gamma>_def b_def f_def Let_def)
  have "orlins_one_step_time already_done = 
    (t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B + prod.fst state'time + prod.fst state''time, prod.snd state''time)"
    by(simp add: orlins_one_step_time_def state''time_def state'time_def \<gamma>'_def E'_def \<gamma>_def b_def f_def Let_def)
  define bigsum where "bigsum = (card (comps \<V> (to_graph (\<FF> state))) -
                                 card (comps \<V> (to_graph (\<FF> already_done)))) *
         (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) + i * (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f + t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B) +
         (\<Sum>j = 1..i.
            let state' = (orlins_one_step_check ^^ (j - 1)) state
            in card {a. important state' a}) * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f)" 
  have bigsum_bound:"prod.fst ((orlins_one_step_time_check ^^ i) (0, state))
       \<le> bigsum"
    unfolding bigsum_def already_done_def
    using assms 
    by (fastforce intro!: running_time_sum_general[OF refl])
  have return_already_done: "return already_done = notyetterm" 
    using already_done_def i_notyetterm by blast
  have invars_already_done:  "underlying_invars already_done"
          "invar_gamma already_done"
          "implementation_invar already_done"
          "invar_non_zero_b already_done"
          "orlins_entry already_done"
          "invar_forest already_done"
          "invar_integral already_done"
          "invar_isOptflow already_done"
    using orlins_compow_time_invars_pres'[OF assms(3,4,5) refl assms(8,6,9,10,11), of i 0,
                      simplified already_done_def[symmetric]]
    by (auto simp add: return_already_done)
  have underlying_invars_after_gamma: "underlying_invars (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)"
 and other_invars_after_gamma:  "implementation_invar (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)"
         "invar_gamma (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)"
          "invar_non_zero_b (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)"
          "invar_integral (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)"
          "invar_isOptflow (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)"
    by (auto intro!: underlying_invars_gamma  implementation_invar_gamm_upd 
                     gamma_upd_underlying_invars_pres invar_integral_gamma_upd 
                     gamma_upd_invar_non_zero_b_pres invar_isOpt_gamma_change
                      invars_already_done
           simp add: \<gamma>'_def )
  note invar_and_other_properties_after_forest = 
      invars_after_maintain_forest[OF  invars_already_done]
  have state'time_is:"prod.snd state'time = maintain_forest (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)"
    unfolding state'time_def 
    apply(subst equal_results_A[symmetric])
    by(auto intro!: maintain_forest_dom_underlying_invars
          simp add: underlying_invars_after_gamma other_invars_after_gamma)
  have underlying_invars_state'time:"underlying_invars (prod.snd state'time)"
   and invar_gamma_after_gamma:"invar_gamma (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)"
   and invar_gamma_state'time:"invar_gamma (prod.snd state'time)"
   and others_in_state': "implementation_invar (prod.snd state'time)"
     "invar_integral (prod.snd state'time)" "invar_isOptflow (prod.snd state'time)"
     "invar_above_6Ngamma (prod.snd state'time)"
    
    using invar_and_other_properties_after_forest other_invars_after_gamma(2) 
    by(auto simp add: state'time_is \<gamma>'_def)
  define timeA where "timeA = (card (comps \<V> (to_graph (\<FF> already_done)))
                   - card (comps \<V> (to_graph (\<FF> (prod.snd (maintain_forest_time (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>))))))) *
  (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B) +
  (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C)"
 have timeA:"prod.fst state'time  = timeA"
    by(auto intro!: time_boundA[of "already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>", simplified]
                        maintain_forest_dom_underlying_invars underlying_invars_after_gamma
          simp add: state'time_def timeA_def terminationA_iff[symmetric] other_invars_after_gamma)
  have underlying_invars_state'time:"underlying_invars (prod.snd state'time)"
   and invar_gamma_after_gamma:"invar_gamma (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)"
   and invar_gamma_state'time:"invar_gamma (prod.snd state'time)"
   and others_in_state': "implementation_invar (prod.snd state'time)"
     "invar_integral (prod.snd state'time)" "invar_isOptflow (prod.snd state'time)"
     "invar_above_6Ngamma (prod.snd state'time)"    
    using invar_and_other_properties_after_forest other_invars_after_gamma(2) 
    by(auto simp add: state'time_is \<gamma>'_def) 
  have send_flow_time_phi:"prod.fst (send_flow_time (prod.snd state'time))
       \<le> nat (\<Phi> (prod.snd state'time)) * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) + (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f)"
    using  time_boundB[OF invar_gamma_state'time refl]  underlying_invars_state'time
           others_in_state'(1,2,3,4) by fastforce
  have Phi_mod_A:"\<Phi>  (prod.snd state'time)
       \<le> \<Phi> (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>) + int (card (comps \<V> (to_graph (\<FF> already_done)))) -
             int (card (comps \<V> (to_graph (\<FF> (maintain_forest (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>))))))"
    using  Phi_increase[OF underlying_invars_after_gamma invar_gamma_after_gamma other_invars_after_gamma(1)]
           other_invars_after_gamma(1)
    by(simp add: state'time_is)
  have send_flow_dom_after_forest: 
          "send_flow_dom (prod.snd state'time)"
    using \<gamma>'_def invar_and_other_properties_after_forest(11) state'time_is by fastforce
  have send_flow_is_same:
      "prod.snd (local.send_flow_time (prod.snd state'time)) = send_flow (prod.snd state'time)"
    using equal_results_B send_flow_dom_after_forest by auto
  have to_graph_final_is:"to_graph (\<FF> (prod.snd final)) = to_graph (\<FF> (prod.snd state''time))"
    unfolding Suc 
    apply(subst funpow.simps(2), subst o_apply, subst (2) surjective_pairing, 
          subst orlins_one_step_time_check.simps)
    using i_notyetterm 
    by(simp add: add_fst_def  orlins_one_step_time_def state''time_def state'time_def already_done_def
               \<gamma>'_def E'_def f_def \<gamma>_def b_def Let_def)
  have card_maintain_forest_reduce:"card (comps \<V> (to_graph (\<FF> already_done))) \<ge>
             card (comps \<V> (to_graph (\<FF> (maintain_forest (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)))))"
    unfolding new_gamma_changes(1)[of already_done, symmetric] \<gamma>'_def
    using invar_and_other_properties_after_forest(10) 
          underlying_invars_gamma invars_already_done(1)  other_invars_after_gamma(1) 
    by(intro card_decrease)(auto simp add: \<gamma>'_def)
  have orlins_entry_late:"orlins_entry ((orlins_one_step_check ^^ i) state)"
    using  assms  same_as_without_time[OF assms(3,4,5,8,6,9,10,11), of i 0 ]  i_notyetterm 
    by (auto intro!:  orlins_entry_after_compow)
  note same_as_without_time2=same_as_without_time[OF assms(3,4,5,8,6,9,10,11), of i 0]
  have invars_late: "invar_non_zero_b  ((orlins_one_step_check ^^ i) state)"
                    "invar_gamma ((orlins_one_step_check ^^ i)  state)"
    using  invars_already_done unfolding already_done_def same_as_without_time2
    by auto
  have Phi_number_important:"state' = (orlins_one_step_check ^^ i) state \<Longrightarrow>
         \<Phi> (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>) = card {a. important (state') a}" for state'
    unfolding  already_done_def \<gamma>'_def E'_def f_def b_def \<gamma>_def 
               sym[OF new_\<gamma>_def[simplified Let_def]] \<Phi>_def 
    apply((subst  same_as_without_time2)+ , rule trans)
     using Phi_contribution_important[OF invars_already_done(4,2,5) _ refl invars_already_done(3,1)] 
     by (fastforce intro!: binary_sum[OF \<V>_finite] arg_cong[of _ _ int] arg_cong[of _ _ card] 
                 simp add: important_def already_done_def same_as_without_time2)+
   have "prod.fst (orlins_one_step_time already_done)
         = prod.fst state'time + prod.fst state''time + t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B"
     by(simp add: orlins_one_step_time_def state'time_def state''time_def
               \<gamma>'_def \<gamma>_def E'_def f_def b_def Let_def)
   also have "... \<le> timeA + nat (\<Phi> (prod.snd state'time)) * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f)
                     + (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f) +  t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B"
     using timeA send_flow_time_phi by(simp add: state''time_def)
   also have "... \<le> timeA + ( nat(\<Phi> (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)) + 
                             (card (comps \<V> (to_graph (\<FF> already_done)))) -
                               card (comps \<V> (to_graph (\<FF> (local.maintain_forest (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)))))) * 
                            (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) + (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f) +
                      t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B"
     using Phi_mod_A card_maintain_forest_reduce by auto
   also have "... \<le> (card (comps \<V> (to_graph (\<FF> already_done))) 
                              - card (comps \<V> (to_graph (\<FF> (maintain_forest (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)))))) *
       (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
       (nat (\<Phi> (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>))) * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
       (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f + t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C) + t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B"
    using state'time_is[simplified state'time_def]  add_mult_distrib2 less_or_eq_imp_le 
     by(auto simp add: add_mult_distrib diff_add_assoc[OF card_maintain_forest_reduce]  timeA_def)
   also have "... \<le> (card (comps \<V> (to_graph (\<FF> already_done))) -
                          card (comps \<V> (to_graph (\<FF> (local.maintain_forest (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)))))) *
       (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
       card {v . important already_done v } * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
       (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f + t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B)"    
     using Phi_number_important[OF refl, simplified sym[OF already_done_def]]   
           same_as_without_time2[simplified sym[OF already_done_def]] 
     by simp
   finally have ineq_for_one_it:"prod.fst (orlins_one_step_time already_done)
     \<le> (card (comps \<V> (to_graph (\<FF> already_done))) 
               - card (comps \<V> (to_graph (\<FF> (local.maintain_forest (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)))))) *
        (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
       card {v. important already_done v} * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
        (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f + t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B) " by simp
   have forest_final:"to_graph (\<FF> (local.maintain_forest (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>))) 
                            = to_graph (\<FF> (prod.snd final))" 
     unfolding assms(1)
     apply(subst funpow.simps(2), subst o_apply, subst (2) surjective_pairing, 
           subst orlins_one_step_time_check.simps)
     using orlins_one_step_time_unfolded send_flow_dom_after_forest send_flow_is_same i_notyetterm
     by (fastforce intro!: cong[OF refl, of  _ _ to_graph] simp add: add_fst_def already_done_def send_flow_changes_\<FF> state''time_def state'time_is)
   have card_decrease_done:"(card (comps \<V> (to_graph (\<FF> state))) 
                                \<ge> card (comps \<V> (to_graph (\<FF> already_done))))"

     using orlins_some_steps_card_decrease[OF refl assms(3,4,5,8,6,9,10,11)]
     by(auto simp add: already_done_def  same_as_without_time2)
   show ?thesis
   proof(subst Suc(1), subst funpow.simps(2), subst o_apply, subst (2) surjective_pairing, 
       subst orlins_one_step_time_check.simps, goal_cases)
     case 1
     show ?case
     proof((subst if_not_P, subst i_notyetterm, rule return.simps(4,6))+, goal_cases)
       case 1
       show ?case
         unfolding add_fst_def
       proof(subst fst_conv, subst sym[OF already_done_def], goal_cases)
         case 1
         show ?case
         proof(rule order.trans[OF  add_mono[OF bigsum_bound ineq_for_one_it]], goal_cases)
           case 1
           show ?case
           proof(subst sym[OF forest_final], unfold bigsum_def, subst (4)already_done_def, 
               subst same_as_without_time2, goal_cases)
             case 1
             show ?case
               apply(subst add_assoc2, subst add_assoc2)
               apply(subst (16) semiring_normalization_rules(24), subst add_assoc3, 
                   subst semiring_normalization_rules(1))
               using card_maintain_forest_reduce card_decrease_done 
               by(auto simp add: algebra_simps)
           qed
         qed
       qed
     qed
   qed
 qed

definition "important_initial state v = ( v\<in> \<V> \<and> ( \<bar>a_balance state v \<bar> > (1 - \<epsilon>)*current_\<gamma> state ))"

lemmas invars_initial = invar_gamma_initial implementation_invar_initial
 invar_integral_initial invar_isOptflow_initial  invar_above_6Ngamma_initial
 invar_non_zero_b_initial underlying_invars_initial

theorem running_time_sum_from_init:
  assumes "final = (orlins_one_step_time_check  ^^ i) (send_flow_time initial)"
          "return (prod.snd final) \<noteq> notyetterm"
          "\<And> j final. j < i \<Longrightarrow> final = (orlins_one_step_time_check  ^^ j)  (send_flow_time initial)
              \<Longrightarrow> return (prod.snd final) = notyetterm"
          "\<not> (\<forall> v \<in> \<V>. \<b> v = 0)"
    shows "prod.fst final \<le> (card (comps \<V> (to_graph (\<FF> initial))) 
                             - card (comps \<V> (to_graph (\<FF> (prod.snd final))))) * 
                            (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f)
                   +  i * (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f + t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B ) +
                     ((\<Sum> j \<in> {1..i}. (let state' = ((orlins_one_step_check ^^ (j - 1))  (send_flow initial)) in 
                                                     card { v. important state' v} )) +
                                                     card { v. important_initial initial v})
                           *(t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f)+
                       (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f )"
proof-
  have "prod.fst (send_flow_time initial) \<le>
       nat (\<Phi> initial) * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) + (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f)"
    and  invar_non_zero_b_initial: " invar_non_zero_b initial"
    by(auto intro!:  time_boundB simp add:  assms(4) invars_initial)
  have Max_gtr_0:"Max {\<bar>\<b> v\<bar> |v. v \<in> \<V>} > 0"
    using assms(4)  Max_lower_bound[OF \<V>_finite V_non_empt, of _ 0 "\<lambda> x. \<bar> \<b> x \<bar>"] by auto
  have b_lower:"x \<in> \<V> \<Longrightarrow> 0 \<le> \<lceil>\<bar>\<b> x\<bar> / Max {\<bar>\<b> v\<bar> |v. v \<in> \<V>} - (1 - \<epsilon>)\<rceil>" for x
  proof(goal_cases)
    case 1
    hence "0 < \<bar>\<b> x\<bar> / Max {\<bar>\<b> v\<bar> |v. v \<in> \<V>} + \<epsilon>"
      using Max_gtr_0 \<epsilon>_axiom(1) divide_less_0_iff[of "\<bar>\<b> x\<bar>" "Max {\<bar>\<b> v\<bar> |v. v \<in> \<V>}"] 
      by simp
    then show ?case 
      by simp
  qed
  have b_upper:"x \<in> \<V> \<Longrightarrow>  \<lceil>\<bar>\<b> x\<bar> / Max {\<bar>\<b> v\<bar> |v. v \<in> \<V>} - (1 - \<epsilon>)\<rceil> \<le> 1" for x
  proof(goal_cases)
    case 1
    note one = this
    have "\<bar>\<b> x\<bar> / Max {\<bar>\<b> v\<bar> |v. v \<in> \<V>} + \<epsilon> \<le> 2"
    proof(rule order.trans[of _ "1+1"], rule add_mono_thms_linordered_semiring(1), 
        rule conjI, goal_cases)
      case 1
      have "\<bar>\<b> x\<bar> \<le> Max {\<bar>\<b> v\<bar> |v. v \<in> \<V>}"
        using \<epsilon>_axiom(2)  Max.coboundedI[of "{\<bar>\<b> v\<bar> |v. v \<in> \<V>}"  "\<bar>\<b> x\<bar>"]  Max_gtr_0 \<V>_finite one
        by fastforce
      thus ?case
        using Max_gtr_0
        by(auto simp add: algebra_simps intro!: linordered_field_class.mult_imp_div_pos_le)
    qed (insert \<epsilon>_axiom(2), simp+) 
    thus ?case by simp
  qed
  have Phi_number_important:"(\<Phi> initial) = card {a. important_initial initial a}"
  proof-
    have "(\<Sum>v\<in>\<V>. \<lceil>\<bar>if v \<in> \<V> then \<b> v else 0\<bar> / Max {\<bar>\<b> v\<bar> |v. v \<in> \<V>} - (1 - \<epsilon>)\<rceil>) =
    int (card {a \<in> \<V>. (1 - \<epsilon>) * Max {\<bar>\<b> v\<bar> |v. v \<in> \<V>} < \<bar>if a \<in> \<V> then \<b> a else 0\<bar>})"
    proof(rule trans[OF  binary_sum[OF \<V>_finite]], goal_cases)
      case (1 x)
      thus ?case
        using b_lower[OF 1] b_upper[OF 1] by presburger
    next
      case 2
      show ?case
      proof((rule arg_cong[of _ _ int] arg_cong[of _ _ card])+, rule Collect_cong_set, goal_cases)
        case (1 x)
        have "\<lceil>\<bar>\<b> x\<bar> / Max {\<bar>\<b> v\<bar> |v. v \<in> \<V>} - (1 - \<epsilon>)\<rceil> = 1"
          if "\<bar>\<b> x\<bar> / Max {\<bar>\<b> v\<bar> |v. v \<in> \<V>} + \<epsilon> \<le> 2" "1 - \<epsilon> < \<bar>\<b> x\<bar> / Max {\<bar>\<b> v\<bar> |v. v \<in> \<V>}"
          using 1 that by linarith
        moreover have "1 - \<epsilon> < \<bar>\<b> x\<bar> / Max {\<bar>\<b> v\<bar> |v. v \<in> \<V>}"
          if "\<lceil>\<bar>\<b> x\<bar> / Max {\<bar>\<b> v\<bar> |v. v \<in> \<V>} - (1 - \<epsilon>)\<rceil> = 1 "
          using 1 that by linarith
        ultimately show ?case 
          using  Max_gtr_0 b_upper[OF 1] 1 one_le_ceiling[of "\<bar>\<b> x\<bar> / Max {\<bar>\<b> v\<bar> |v. v \<in> \<V>} - (1 - \<epsilon>)"]
          by (auto  simp add: pos_less_divide_eq[symmetric])
      qed
    qed        
    thus ?thesis 
      by(auto simp add: initial_def \<Phi>_def important_initial_def new_\<gamma>_def Let_def 
          init_gamma abstract_bal_map_init_is) 
  qed
  have same_state_after_init_send_flow:
    "prod.snd (local.send_flow_time initial) = send_flow initial" 
    by(auto intro!: equal_results_B[symmetric,of initial] 
        simp add: initial_state_orlins_dom_and_results(5))
  have same_F_After_send_flow': "to_graph (\<FF> (send_flow initial)) = to_graph (\<FF> initial)"
    and same_F_After_send_flow: "to_graph (\<FF> (prod.snd (send_flow_time initial)))
                                 = to_graph (\<FF> initial)"
    by(auto intro!: cong[OF refl, OF send_flow_changes_\<FF>] 
        simp add: initial_state_orlins_dom_and_results(5) same_state_after_init_send_flow)
  have take_first_time_out:"((prod.fst (send_flow_time initial)) +++ ((orlins_one_step_time_check ^^ i) (0, send_flow initial))) =
        (orlins_one_step_time_check ^^ i) (send_flow_time initial)" for i
    using runtime_add_constant[of i "prod.fst (send_flow_time initial)" 0 "send_flow initial"] 
    by(auto simp add: add_fst_def same_state_after_init_send_flow[symmetric] )
  have send_flow_time_bound:"prod.fst (send_flow_time initial) \<le>
                 nat (\<Phi> initial) * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) + (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f)"
    using  time_boundB[OF invars_initial(1) refl invars_initial(7,2,3,4,5)] assms(4) by simp
  show ?thesis
  proof(cases i)
    case 0
    then show ?thesis
      using assms 0 same_F_After_send_flow Phi_number_important send_flow_time_bound
      by simp
  next
    case (Suc nat)
    have return_after_init_send_flow: "return (send_flow initial) = notyetterm"
      using assms(3)[of 0, OF _ refl, simplified] Suc
      by (simp add: same_state_after_init_send_flow)
    have underlying_invars_send_flow:"underlying_invars (send_flow initial)"
      and invar_gamma_send_flow:"invar_gamma (send_flow initial)"
      and invar_non_zero_b_send_flow:"invar_non_zero_b (send_flow initial)"
      and orlins_entry_send_flow:"orlins_entry (local.send_flow initial)"
      and other_invars: "implementation_invar (send_flow initial)"
      "invar_forest (send_flow initial)"
      "invar_integral (send_flow initial)"
      "invar_isOptflow (send_flow initial)"
      using send_flow_invars_pres[OF  initial_state_orlins_dom_and_results(5)[OF refl]
          invars_initial(7,1,2,3,4,5), OF assms(4)]
        phi_initial_leq_2N
      by (auto intro!: remaining_balance_after_send_flow orlins_entry_after_send_flow
          send_flow_invar_forest 
          simp add: invars_initial assms(4) return_after_init_send_flow)
    have sum_bound:"prod.fst ((orlins_one_step_time_check ^^ Suc nat) (0, local.send_flow initial))
  \<le> (card (comps \<V> (to_graph (\<FF> (local.send_flow initial)))) -
      card (comps \<V> (to_graph (\<FF> (prod.snd ((orlins_one_step_time_check ^^ Suc nat) (0, local.send_flow initial))))))) *
     (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
     nat * (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f + t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B) +
     (\<Sum>j = 1..Suc nat.
         let state' = (orlins_one_step_check ^^ (j - 1)) (local.send_flow initial) in card {v. important state' v}) *
     (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
     (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f + t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B)"
      using  arg_cong[OF take_first_time_out[of "Suc nat", simplified add_fst_def], of prod.snd]
        assms(2)[simplified assms(1) Suc]  arg_cong[OF take_first_time_out[ simplified add_fst_def],
          of prod.snd] Suc assms(3)  
      by (intro running_time_sum[OF refl, of nat "send_flow initial", 
            OF _  underlying_invars_send_flow invar_gamma_send_flow invar_non_zero_b_send_flow 
            orlins_entry_send_flow _ other_invars])
        fastforce+
    have take_out:"prod.fst ((orlins_one_step_time_check ^^ i) (send_flow_time initial)) = 
       prod.fst (send_flow_time initial) + prod.fst ((orlins_one_step_time_check ^^ i) (0, local.send_flow initial))"
      using fst_conv take_first_time_out[of i, symmetric] by(auto simp add: add_fst_def) 
    show ?thesis 
    proof((subst assms(1))+, subst take_out, subst (5) surjective_pairing, goal_cases)
      case 1
      show ?case
      proof(subst equal_results_B[OF initial_send_flow(2), symmetric], goal_cases)
        case 1
        show ?case
        proof(subst runtime_add_constant[of i "prod.fst (send_flow_time initial)" 0, 
              simplified add_fst_def, simplified], goal_cases)
          case 1
          show ?case
            using  same_F_After_send_flow' Phi_number_important Suc
            by (intro order.trans[OF  add_mono[OF 
                    send_flow_time_bound sum_bound[simplified sym[OF Suc]]]])
              (auto simp add: algebra_simps)
        qed
      qed
    qed
  qed
qed

definition  "\<l> =  nat (\<lceil> log 2 (4*M*N + (1 - \<epsilon>)) - log 2 \<epsilon>\<rceil>) + 1"

lemma invar_non_zero_b_gamma_upd_pres:
  "invar_non_zero_b state \<Longrightarrow> invar_non_zero_b (state \<lparr> current_\<gamma> := gamma \<rparr>)"
  by(auto intro!: invar_non_zero_bI elim!: invar_non_zero_bE)

lemma 
  assumes  "\<not> (\<forall> v \<in> \<V>. \<b> v = 0)"
  shows underlying_invars_send_flow_initial[initial_invars]:"underlying_invars (send_flow initial)"
    and invar_gamma_send_flow_initial[initial_invars]:"invar_gamma (send_flow initial)"
    and invar_non_zero_b_send_flow_initial[initial_invars]:"return (send_flow initial) = notyetterm \<Longrightarrow> invar_non_zero_b (send_flow initial)"
    and orlins_entry_send_flow_initial[initial_invars]:"return (send_flow initial) = notyetterm \<Longrightarrow> orlins_entry (local.send_flow initial)"
    and other_invars_send_flow_initial[initial_invars]: "implementation_invar (send_flow initial)"
                      "invar_forest (send_flow initial)"
                      "invar_integral (send_flow initial)"
                      "invar_isOptflow (send_flow initial)"
    using send_flow_invars_pres[OF  initial_state_orlins_dom_and_results(5)[OF refl]
                                      invars_initial(7,1,2,3,4,5), OF assms(1)]
         phi_initial_leq_2N
    by (auto intro!: remaining_balance_after_send_flow orlins_entry_after_send_flow
                     send_flow_invar_forest 
          simp add: invars_initial assms(1) )

lemma number_of_important:
  assumes "final = (orlins_one_step_check  ^^ i) (send_flow initial)"
          "return final \<noteq> notyetterm"
          "\<And> j final. j < i \<Longrightarrow> final = (orlins_one_step_check  ^^ j)  (send_flow initial)
              \<Longrightarrow> return final = notyetterm"
          "\<not> (\<forall> v \<in> \<V>. \<b> v = 0)"
    shows "((\<Sum> j \<in> {1..i}. (let state' = ((orlins_one_step_check ^^ (j - 1))  (send_flow initial)) in 
                                                     card { v. important state' v} )) +
                                                     card { v. important_initial initial v})
          \<le> (\<l> + 1) * (2*N - 1)"                                         
proof- 
  have Max_b_gtr_0:"Max {\<bar>\<b> v\<bar> |v. v \<in> \<V>} > 0"
    using assms(4)  Max_gr_iff[of "{\<bar>\<b> v\<bar> |v. v \<in> \<V>}" 0] \<V>_finite V_non_empt by auto
  define pseudo_initial where "pseudo_initial = initial \<lparr> current_\<gamma> := 2 * current_\<gamma> initial\<rparr>"
  have pseudo_initial_return: "return pseudo_initial = notyetterm"
    by(auto simp add: pseudo_initial_def initial_def)
  have all_zero_initial: " a_current_flow initial e = 0" for e
    by(auto simp add: initial_def init_flow'(1)[OF refl])
  have new_gamma_pseudo_initial:"new_\<gamma> (initial\<lparr>current_\<gamma> := 2 * current_\<gamma> initial\<rparr>) =  current_\<gamma> initial"
    using all_zero_initial
    by (auto simp add: new_gamma_is(1) implementation_invar_gamm_upd 
                       implementation_invar_initial  current_gamma_initial underlying_invars_gamma
                       underlying_invars_initial)
  have send_flow_sim:"orlins_one_step_check pseudo_initial = send_flow initial"
    using pseudo_initial_return all_zero_initial 
         new_gamma_is(1)[OF implementation_invar_initial underlying_invars_initial]
     by(auto intro!: cong[OF refl, of _ _ send_flow] all_actives_zero_flow_same_state 
                     invar_gamma_initial
           simp add: orlins_one_step_check_def  orlins_one_step_def pseudo_initial_def 
                     new_gamma_pseudo_initial underlying_invars_initial assms(4) )
  have pseudo_initial_important:
       "important pseudo_initial v \<longleftrightarrow> important_initial initial v" for v
    by(simp add: pseudo_initial_def important_def important_initial_def new_gamma_pseudo_initial)
  define Imps where "Imps = 
                 (\<lambda> j. if j \<le> i then let state = (orlins_one_step_check ^^ j) pseudo_initial in
                 {v. important ((orlins_one_step_check ^^ j) pseudo_initial) v} else {})"
  define comps_with_imp where "comps_with_imp = 
                 (\<lambda> j. (if j \<le> i then let state = (orlins_one_step_check ^^ j) pseudo_initial in
                 { C | C. C \<in> comps \<V>  (to_graph (\<FF> state)) \<and> 
                        (\<exists> v. important state v \<and> C = connected_component (to_graph (\<FF> state)) v)} else {}))"
  have underlying_invars_pseudo_initial: "underlying_invars pseudo_initial"
    and invar_gamma_pseudo_initial: "invar_gamma pseudo_initial"
    and invar_non_zero_b_pseudo_initial: "invar_non_zero_b pseudo_initial"
    and invar_integral_pseudo_initial: "invar_integral pseudo_initial"
    and invar_forest_pseudo_initial: "invar_forest pseudo_initial"
    and other_invars: "orlins_entry pseudo_initial"
                      "implementation_invar pseudo_initial"
                      "invar_isOptflow pseudo_initial"
    using invar_gamma_initial assms(4) \<V>_finite  \<epsilon>_axiom
    by(force simp add: invar_gamma_def pseudo_initial_def all_zero_initial 
                         update_gamma_same_F F_initial_empty implementation_invar_initial
                         invar_isOptflow_initial underlying_invars_initial current_gamma_initial
      intro!: invar_non_zero_b_gamma_upd_pres invar_non_zero_b_initial invar_integralI
              invar_forestI  implementation_invar_gamm_upd invar_isOpt_gamma_change
              underlying_invars_gamma orlins_entryI
             order.trans[of "\<bar> _ \<bar>" "(1/2) * (2 *  Max {\<bar>a_balance initial v\<bar> |v. v \<in> \<V>} )"
                               "(1 - \<epsilon>) * (2 *  Max _ )"]
             linorder_class.Max_ge)+
  note invars_pseudo_initial =  underlying_invars_pseudo_initial  
                               invar_gamma_pseudo_initial invar_non_zero_b_pseudo_initial
                              invar_integral_pseudo_initial invar_forest_pseudo_initial
                              other_invars
  have underlying_invars_pres: "underlying_invars ((orlins_one_step_check ^^ j) pseudo_initial)" for j
    using invars_pseudo_initial
    by(auto intro!: orlins_compow_underlying_invars_pres[of pseudo_initial j])
  have invar_gamma_pres: "invar_gamma ((orlins_one_step_check ^^ j) pseudo_initial)" for j
    using invars_pseudo_initial
    by(auto intro: orlins_compow_invar_gamma_pres[of pseudo_initial j])
  have invar_non_zero_b_pres: "j \<le> i  \<Longrightarrow>invar_non_zero_b ((orlins_one_step_check ^^ j) pseudo_initial)" for j
  proof(cases "j = 0", goal_cases)
    case 1
    then show ?thesis 
     using invar_non_zero_b_pseudo_initial by simp
  next
    case 2
    show ?thesis 
    proof(rule some_balance_after_k_steps[OF _ invars_pseudo_initial(1,2,3,7,6,5,4,8)], goal_cases)
      case 1
      show ?case
      proof(rule trans[OF _ assms(3)[of "j-1", OF _ refl]], goal_cases)
        case 1
        show ?case
          using 2
          by(unfold sym[OF send_flow_sim] sym[OF funpow.simps(2)] sym[OF funpow_swap1]
             sym[OF o_apply[of orlins_one_step_check "orlins_one_step_check ^^ (_ - 1)"]])
             auto
      qed (insert 2, auto)
    qed
  qed
  have invar_forest_after_one:"invar_forest (orlins_one_step_check pseudo_initial)"
    by (simp add: send_flow_sim F_initial_empty(1) initial_send_flow(2) invar_forest_def
        send_flow_changes_\<F>)
  have invar_integral_after_one:"invar_integral (orlins_one_step_check pseudo_initial)"
    by (simp add: assms(4) underlying_invars_initial implementation_invar_initial initial_send_flow(2)
        invar_above_6Ngamma_initial invar_gamma_initial invar_integral_initial invar_isOptflow_initial
        send_flow_invars_pres(4) send_flow_sim)
  note orlins_entry_pseudo_initial = other_invars(1)
  have orlins_entry_one_step: "i > 0 \<Longrightarrow> orlins_entry (orlins_one_step_check pseudo_initial)"
    by (simp add: assms(3,4) underlying_invars_initial implementation_invar_initial
        invar_above_6Ngamma_initial invar_gamma_initial invar_integral_initial 
        invar_isOptflow_initial orlins_entry_after_send_flow send_flow_sim)
  have invar_forest_pres: "j \<le> i \<Longrightarrow> invar_forest ((orlins_one_step_check ^^ j) pseudo_initial)" for j
  proof(cases j, goal_cases)
    case 1
    then show ?thesis 
      using invar_forest_pseudo_initial by simp
  next
    case (2 nat)
    hence "invar_forest ((orlins_one_step_check ^^ (j - 1) \<circ>
                      orlins_one_step_check) pseudo_initial)"
      using assms(4) invar_forest_pseudo_initial send_flow_sim  
        invar_non_zero_b_pres[of 1, simplified] orlins_entry_one_step 
      by(auto intro!: orlins_compow_invar_forest_pres underlying_invars_send_flow_initial
          invar_gamma_send_flow_initial other_invars_send_flow_initial)
    then show ?thesis 
      using invar_forest_pseudo_initial 2
      by(subst Suc_pred', simp, subst funpow_Suc_right) 
  qed
  have implementation_invar_pres: "j \<le> i \<Longrightarrow> implementation_invar ((orlins_one_step_check ^^ j) pseudo_initial)" for j
  proof(cases j, goal_cases)
    case 1
    then show ?thesis 
      using other_invars by simp
  next
    case (2 nat)
    hence "implementation_invar ((orlins_one_step_check ^^ (j - 1) \<circ>
                      orlins_one_step_check) pseudo_initial)"
      using assms(4) other_invars send_flow_sim  
        invar_non_zero_b_pres[of 1, simplified] orlins_entry_one_step 
      by(auto intro!: orlins_compow_implementation_invar_pres underlying_invars_send_flow_initial
          invar_gamma_send_flow_initial other_invars_send_flow_initial)
    then show ?thesis 
      using other_invars 2
      by(subst Suc_pred', simp, subst funpow_Suc_right) 
  qed
  have invar_integral_pres: "j \<le> i \<Longrightarrow> invar_integral ((orlins_one_step_check ^^ j) pseudo_initial)" for j
  proof (cases j, goal_cases)
    case 1
    thus ?case
      using invar_integral_pseudo_initial by simp
  next
    case 2
    have "invar_integral ((orlins_one_step_check ^^ (j - 1) \<circ>
                orlins_one_step_check) pseudo_initial)"
      using assms(4)  send_flow_sim  invar_non_zero_b_pres[of 1, simplified] orlins_entry_one_step 
        invar_integral_pseudo_initial 2
      by(auto intro!: orlins_compow_invar_integral_pres underlying_invars_send_flow_initial
          invar_gamma_send_flow_initial other_invars_send_flow_initial)
    thus ?case 
      using 2
      by(subst Suc_pred', simp, subst funpow_Suc_right)
  qed
  have orlins_entry_pres: "j \<le> i \<Longrightarrow> orlins_entry ((orlins_one_step_check ^^ j) pseudo_initial)" for j
  proof(cases j, goal_cases)
    case 1
    thus ?case
      using orlins_entry_pseudo_initial by simp
  next
    case (2 nat)
    note two = 2
    have "return ((orlins_one_step_check ^^ j) pseudo_initial) = notyetterm"
    proof(subst 2, subst Suc_pred', goal_cases)
      case 2
      thus ?case
        using two send_flow_sim 
        by(subst funpow_Suc_right)(auto intro!: assms(3)[of nat])
    qed (insert 2, simp)
    thus ?case
      using  assms(3)  other_invars invar_forest_pseudo_initial  invar_integral_pseudo_initial
      by (auto intro!: orlins_entry_after_compow[OF underlying_invars_pseudo_initial 
            invar_gamma_pseudo_initial 
            invar_non_zero_b_pseudo_initial])
  qed
  have invar_isOptflow_pseudo_initial: "invar_isOptflow pseudo_initial"
    using invar_isOptflow_initial 
    by(simp add: pseudo_initial_def invar_isOptflow_def)
  have invar_isOptflow_pres: "invar_isOptflow ((orlins_one_step_check ^^ j) pseudo_initial)" for j
    using underlying_invars_pseudo_initial  invar_gamma_pseudo_initial  invar_non_zero_b_pseudo_initial 
          invar_integral_pseudo_initial invar_forest_pseudo_initial 
          other_invars
    by (auto intro!: orlins_compow_invar_isOptflow_pres)

  have card_Imps_card_compst_with_ip_same:"card (Imps j) = card (comps_with_imp j)" for j
  proof(cases "j > i")
    case True
    then show ?thesis 
      unfolding Imps_def comps_with_imp_def by simp
  next
    case False
    hence j_leq_i:"j \<le> i" by simp
    define state where "state = (orlins_one_step_check ^^ j) pseudo_initial"
    show ?thesis 
    proof(rule bij_betw_same_card[of "\<lambda> v. connected_component (to_graph (\<FF> state)) v"], goal_cases)
      case 1
      show ?case
        unfolding bij_betw_def
      proof(rule conjI, goal_cases)
        case 1
        show ?case unfolding inj_on_def
        proof(rule,rule, rule,  goal_cases)
          case (1 x y)
          have new_gamma_gtr_0:"new_\<gamma> ((orlins_one_step_check ^^ j) pseudo_initial) > 0"
          proof(cases j, goal_cases)
            case 1
            thus ?case
              by (simp add: assms(4) invar_gammaD invar_gamma_initial new_gamma_pseudo_initial
                  pseudo_initial_def)  
          next
            case 2
            thus ?case
              using invar_non_zero_b_pres[OF j_leq_i] underlying_invars_pres[of j]
                implementation_invar_pres[OF j_leq_i]  invar_gamma_pres[of j]
              by(auto intro!: invar_gammaD[OF new_gamma_is(7), simplified])
          qed
          have non_zero_balance_x:"\<bar>a_balance state x\<bar> > 0"
            using 1(1) j_leq_i invar_gamma_pres[of j] new_gamma_gtr_0 \<epsilon>_axiom(4)
            by (auto simp add: algebra_simps state_def Imps_def Let_def invar_gamma_def important_def)
          have non_zero_balance_y:"\<bar>a_balance state y\<bar> > 0"
            using 1(2) j_leq_i invar_gamma_pres[of j] new_gamma_gtr_0 \<epsilon>_axiom(4)
            by(auto simp add: algebra_simps state_def Imps_def Let_def invar_gamma_def important_def)
          have "representative state x = representative state y"
            using underlying_invars_pres[of j, simplified underlying_invars_def inv_reachable_same_rep_def] 1(3)
            by(fastforce simp add: state_def connected_component_def)
          moreover have "representative state x = x"
            using underlying_invars_pres[of j, simplified underlying_invars_def inv_pos_bal_rep_def] 1(3) 1(1)
              non_zero_balance_x j_leq_i
            by(fastforce simp add: Imps_def important_def Let_def state_def)
          moreover have "representative state y = y"
            using underlying_invars_pres[of j, simplified underlying_invars_def inv_pos_bal_rep_def] 1(3) 1(2)
              non_zero_balance_y j_leq_i
            by(simp add: Imps_def important_def Let_def state_def)
          ultimately show ?case by simp
        qed
      next
        case 2
        then show ?case 
          unfolding comps_with_imp_def Imps_def Let_def state_def comps_def important_def
          apply(subst if_P[OF j_leq_i ])+
          by auto 
      qed
    qed
  qed
  define \<S> where "\<S> = (\<Union> j. (comps_with_imp j))"
  have finite_S: "finite \<S>" 
    using underlying_invars_pres \<V>_finite
    by(simp add: \<S>_def comps_with_imp_def Let_def comps_def underlying_invars_def 
                 inv_components_in_V_def)
  have comps_with_imp_subs_S: "\<Union> (range comps_with_imp) \<subseteq> \<S>"
    by(simp add :\<S>_def)
  have component_lifetime:  "ii + \<l>  < j \<Longrightarrow> C \<in> comps_with_imp ii \<Longrightarrow> C \<notin> comps_with_imp j" for ii j C
  proof( goal_cases)
    case 1
    note one = this
    have ii_leq_i:"ii \<le> i" 
      apply(rule ccontr)
      using  1(2)by(simp add: comps_with_imp_def Let_def)
    define state where "state = (orlins_one_step_check ^^ ii) pseudo_initial"
    have C_prop:" C \<in> comps \<V>  (to_graph (\<FF> state))" 
                        "(\<exists> v. important state v \<and>
                              C = connected_component (to_graph (\<FF> state)) v)"
      using 1(2) ii_leq_i unfolding comps_with_imp_def Let_def state_def by auto
    then obtain v where v_prop:"important state v" "C = connected_component (to_graph (\<FF> state)) v"
      by auto
    show ?case
    proof(cases "j > i")
      case True
      then show ?thesis unfolding comps_with_imp_def by simp
    next
      case False
      hence j_leq_i:"j \<le> i" by simp
      have invar_gamma_state: "invar_gamma state"
       and underlying_invars_state: "underlying_invars state" 
       and invar_non_zero_b_state: "invar_non_zero_b state"
       and invar_integral_state: "invar_integral state"
       and invar_forest_state: "invar_forest state"
       and orlins_entry_state: "orlins_entry state"
       and invar_isOptflow_state: "invar_isOptflow state"
       and implementation_invar_state: "implementation_invar state"
        using invar_gamma_pres  underlying_invars_pres  invar_non_zero_b_pres[OF ii_leq_i]
              invar_integral_pres[OF ii_leq_i] invar_forest_pres[OF ii_leq_i]
              orlins_entry_pres [OF ii_leq_i] invar_isOptflow_pres 
              implementation_invar_pres[OF ii_leq_i]
        by(auto simp add: state_def)
      have "\<exists>k\<le>\<l> + 1. return ((orlins_one_step_check ^^ k) state) \<noteq> notyetterm \<or>
            connected_component (to_graph (\<FF> state)) v 
                    \<subset> connected_component (to_graph (\<FF> ((orlins_one_step_check ^^ k) state))) v"
        using invar_gamma_state  underlying_invars_state  invar_non_zero_b_state  invar_integral_state 
              v_prop  \<l>_def  invar_forest_state  orlins_entry_state  invar_isOptflow_state implementation_invar_state
        by(intro if_important_then_comp_increase_or_termination[of state v \<l>]) auto
      then obtain k where k_prop:"k\<le>\<l> + 1" "return ((orlins_one_step_check ^^ k) state) \<noteq> notyetterm \<or>
            connected_component (to_graph (\<FF> state)) v 
            \<subset> connected_component (to_graph (\<FF> ((orlins_one_step_check ^^ k) state))) v"
        by auto
      have "return state \<noteq> notyetterm \<Longrightarrow> False"
        using pseudo_initial_def initial_def  ii_leq_i 1 j_leq_i
              assms(3)[of "ii-1", OF _ refl, simplified sym[OF send_flow_sim] 
              sym[OF o_apply[of "orlins_one_step_check ^^ (ii - 1)" "orlins_one_step_check" pseudo_initial]] 
              sym[OF funpow_Suc_right[of "ii - 1" orlins_one_step_check]]] 
        by (cases ii) (auto  simp add: state_def)
      hence k_not_0:"k = 0 \<Longrightarrow> False"
        using k_prop(2) by simp
      have "connected_component (to_graph (\<FF> state)) v 
           \<subset> connected_component (to_graph (\<FF> ((orlins_one_step_check ^^ k) state))) v"
        unfolding state_def
      proof(rule make_pos_rule'[OF k_prop(2)[simplified state_def], simplified], goal_cases)
        case 1
        have "return ((orlins_one_step_check ^^ (k + ii)) pseudo_initial) = notyetterm"
        proof(rule trans[OF _ assms(3)[of "ii + k - 1", OF _  refl]], goal_cases)
          case 2
          show ?case
            using  j_leq_i one(1) k_prop(1) by simp
        next
          case 1
          have "orlins_one_step_check ^^ (k + ii) = orlins_one_step_check ^^ Suc (ii + k - 1)"
            using k_not_0 
            by (subst sym[OF Suc_pred'[of "ii + k"]])
              (auto  simp add: add.commute[of k ii])
          thus ?case
            by(auto simp add: sym[OF o_apply[of "orlins_one_step_check ^^ _" "orlins_one_step_check"]] 
                sym[OF funpow_Suc_right]  sym[OF send_flow_sim] ) 
        qed
        thus ?case
          by(simp add: sym[OF o_apply[of "orlins_one_step_check ^^ k" "orlins_one_step_check ^^ ii"]]
              sym[OF funpow_add])
      qed
      moreover have "connected_component (to_graph (\<FF> ((orlins_one_step_check ^^ k) state))) v
                \<subseteq> connected_component (to_graph (\<FF> ((orlins_one_step_check ^^ ((j - ii) - k))
                                                ((orlins_one_step_check ^^ k) state)))) v"
      proof(rule con_comp_subset, goal_cases)
        case 1
        have steps_are:"(orlins_one_step_check ^^ k) ((orlins_one_step_check ^^ ii) pseudo_initial) 
              = (orlins_one_step_check ^^ (k + ii)) pseudo_initial"
          by(simp add: sym[OF o_apply[of "orlins_one_step_check ^^ _" "orlins_one_step_check ^^ _"]]
              subst sym[OF funpow_add] )
        show ?case
          using  j_leq_i k_prop(1) 1 one
          by(intro orlins_some_steps_forest_increase[OF refl,
                of "(orlins_one_step_check ^^ k) state" "(j-ii) - k"])
            (auto intro!:  invar_non_zero_b_pres[of "k + ii"] implementation_invar_pres[of "k + ii"] 
              orlins_entry_pres[of "k + ii"] invar_isOptflow_pres[of "k + ii"] 
              invar_forest_pres[of "k + ii"]  invar_integral_pres[of "k + ii"]
              underlying_invars_pres[of "k + ii"] invar_gamma_pres[of "k + ii"]
              simp add: state_def steps_are )
      qed
      moreover have "to_graph (\<FF> ((orlins_one_step_check ^^ ((j-ii) - k)) 
                         ((orlins_one_step_check ^^ k) state))) =
                     to_graph (\<FF> ((orlins_one_step_check ^^ j) (pseudo_initial)))"
        using  j_leq_i k_prop(1) 1 
         by (simp add: sym[OF o_apply[of "orlins_one_step_check ^^ _" "orlins_one_step_check ^^ _"]] 
                       sym[OF funpow_add] state_def)
      ultimately have component_increase: 
        "connected_component (to_graph (\<FF> state)) v 
             \<subset> connected_component (to_graph (\<FF> (((orlins_one_step_check ^^ j)) pseudo_initial))) v"
        by simp
      have not_in_j:"connected_component (to_graph (\<FF> state)) v 
                      \<in> comps \<V> (to_graph (\<FF> ((orlins_one_step_check ^^ j) pseudo_initial))) \<Longrightarrow> False"
      proof(goal_cases)
        case 1
        then obtain w where "w \<in> \<V>" "connected_component (to_graph (\<FF> state)) v = 
               connected_component (to_graph (\<FF> ((orlins_one_step_check ^^ j) pseudo_initial))) w" 
          by(auto simp add: comps_def)
        moreover hence "connected_component (to_graph (\<FF> ((orlins_one_step_check ^^ j) pseudo_initial))) w =
                       connected_component (to_graph (\<FF> ((orlins_one_step_check ^^ j) pseudo_initial))) v"
          using connected_components_member_eq[of v _ w]
                in_connected_componentI2[of v _ "to_graph (\<FF> state)"] 
          by simp
        ultimately show ?case 
          using component_increase by simp
      qed
      thus ?thesis  
        using j_leq_i  v_prop(2) not_in_j
        by(auto simp add:comps_with_imp_def Let_def comps_def)
    qed
  qed

  have beyonf_i_empty:"i < j \<Longrightarrow> comps_with_imp j = {}" for j
    unfolding comps_with_imp_def by auto

  have card_S_laminar_bound:"card \<S> \<le> (2*N  - 1)"
  proof-
    have "laminar \<V> \<S>"
    proof(rule laminarI, goal_cases)
      case (1 X Y)
      note XY_props = this
      then obtain k l where get_k_and_l:"X \<in> comps_with_imp k" "Y \<in> comps_with_imp l"
        by(auto simp add: \<S>_def)
      have k_and_l_i: "k \<le> i" "l \<le> i"
        using get_k_and_l
        by(auto intro: ccontr simp add:  comps_with_imp_def )
    define stateX where "stateX = (orlins_one_step_check ^^ k) pseudo_initial"
    obtain x where x_prop:"important stateX x" "X = connected_component (to_graph (\<FF> stateX)) x"
      using get_k_and_l(1) k_and_l_i(1)
      by(auto simp add: stateX_def comps_with_imp_def Let_def)
    define stateY where "stateY = (orlins_one_step_check ^^ l) pseudo_initial"
    obtain y where y_prop:"important stateY y" "Y = connected_component (to_graph (\<FF> stateY)) y"
      using get_k_and_l(2) k_and_l_i(2)
      by(auto simp add: stateY_def comps_with_imp_def Let_def)
    have underlying_invars_stateX: "underlying_invars stateX"
     and invar_gamma_stateX: "invar_gamma stateX"
     and invar_non_zero_b_stateX:"invar_non_zero_b stateX"
     and underlying_invars_stateY: "underlying_invars stateY"
     and invar_gamma_stateY: "invar_gamma stateY"
     and invar_non_zero_b_stateY:"invar_non_zero_b stateY"
     and implementation_invar_stateX: "implementation_invar stateX"
     and orlins_entry_stateX: "orlins_entry stateX"
     and invar_forest_stateX: "invar_forest stateX"
     and invar_integral_stateX: "invar_integral stateX"
     and invar_isOptflow_stateX: "invar_isOptflow stateX"
     and implementation_invar_stateY: "implementation_invar stateY"
     and orlins_entry_stateY: "orlins_entry stateY"
     and invar_forest_stateY: "invar_forest stateY"
     and invar_integral_stateY: "invar_integral stateY"
     and invar_isOptflow_stateY: "invar_isOptflow stateY"
      using underlying_invars_pres[of k] invar_gamma_pres[of k]
            implementation_invar_pres[of k] orlins_entry_pres[of k]
            invar_forest_pres[of k] invar_integral_pres[of k]
            invar_isOptflow_pres[of k] invar_non_zero_b_pres[of k] 
            k_and_l_i(1) underlying_invars_pres[of l] invar_gamma_pres[of l]
            invar_non_zero_b_pres[of l] k_and_l_i(2)
            implementation_invar_pres[of l] orlins_entry_pres[of l]
            invar_forest_pres[of l] invar_integral_pres[of l]
           invar_isOptflow_pres[of l]
      by(auto simp add: stateX_def stateY_def)
    have "\<not> X \<subseteq> Y \<Longrightarrow> \<not> Y \<subseteq> X \<Longrightarrow> \<not> X \<inter> Y = {} \<Longrightarrow> False"
      proof(goal_cases)
        case 1
        note X_Y_props = this
        have comparison_cases:"((a::nat) < b \<Longrightarrow> P) \<Longrightarrow> ((a = b) \<Longrightarrow> P) \<Longrightarrow> (a > b \<Longrightarrow> P) \<Longrightarrow> P" for a b P  by force
        show ?case 
        proof(cases rule: comparison_cases[of k l])
          case 1
          have stateY_from_stateX:"stateY = (orlins_one_step_check ^^ (l - k)) stateX"
            using 1
            by(simp add: sym[OF o_apply[of "orlins_one_step_check ^^ _" "orlins_one_step_check ^^ _"]] 
                         sym[OF funpow_add] stateX_def stateY_def)
          have forest_subs:"to_graph (\<FF> stateX) \<subseteq> to_graph (\<FF> stateY)"
            using stateY_from_stateX  underlying_invars_stateX invar_gamma_stateX
                  invar_non_zero_b_stateX implementation_invar_stateX orlins_entry_stateX
                  invar_forest_stateX invar_integral_stateX invar_isOptflow_stateX
            by (intro orlins_some_steps_forest_increase[of _ "l - k"])
          define X' where "X' = connected_component (to_graph (\<FF> stateY)) x"
          have X_subs_X':"X \<subseteq> X'"
            by(auto intro!: con_comp_subset[OF forest_subs] simp add: x_prop(2) X'_def)
          have "X' \<inter> Y \<noteq> {}"
            using X_Y_props(3) X_subs_X' by blast
          hence "X' = Y"
            using X'_def y_prop(2) connected_components_member_eq[of _ "to_graph (\<FF> stateY)"]
            by(unfold disjoint_iff) blast
          moreover have "X' \<noteq> Y"
            using X_Y_props X_subs_X' by simp
          ultimately show ?thesis by simp
        next
          case 2
          have forest_same:"to_graph (\<FF> stateX) = to_graph (\<FF> stateY)"
            using stateX_def stateY_def 2 by simp
          hence "X = Y"
            using X_Y_props y_prop(2) x_prop(2)
            by (metis connected_components_member_eq disjoint_iff)
          moreover have "X \<noteq> Y"
            using X_Y_props forest_same by simp
          ultimately show ?thesis by simp
        next
          case 3
          have stateX_from_stateY:"stateX = (orlins_one_step_check ^^ (k - l)) stateY"
            using 3
            by(simp add: sym[OF o_apply[of "orlins_one_step_check ^^ _" "orlins_one_step_check ^^ _"]] 
                         sym[OF funpow_add] stateX_def stateY_def)
          have forest_subs:"to_graph (\<FF> stateY) \<subseteq> to_graph (\<FF> stateX)"
            using stateX_from_stateY  underlying_invars_stateY invar_gamma_stateY invar_non_zero_b_stateY
                  implementation_invar_stateY orlins_entry_stateY invar_forest_stateY 
                  invar_integral_stateY invar_isOptflow_stateY
            by (intro orlins_some_steps_forest_increase[of _ "k - l"])
          define Y' where "Y' = connected_component (to_graph (\<FF> stateX)) y"
          have Y_subs_Y':"Y \<subseteq> Y'"
            unfolding y_prop(2) Y'_def
            by(rule con_comp_subset[OF forest_subs])
          have "Y' \<inter> X \<noteq> {}"
            using X_Y_props(3) Y_subs_Y' by blast
          hence "Y' = X"
            using Y'_def x_prop(2) 
            by (metis connected_components_member_eq disjoint_iff)
          moreover have "Y' \<noteq> X"
            using X_Y_props Y_subs_Y' by simp
          ultimately show ?thesis by simp
        qed
      qed
      thus ?case by auto
    next
      case (2 X)
      then obtain k where get_k:"X \<in> comps_with_imp k" 
        by(auto simp add: \<S>_def)     
      have k_i: "k \<le> i"
        using get_k 
        by(auto intro: ccontr simp add: comps_with_imp_def  )
     define stateX where "stateX = (orlins_one_step_check ^^ k) pseudo_initial"
     obtain x where x_prop:"important stateX x" "X = connected_component (to_graph (\<FF> stateX)) x"
       using get_k(1) k_i(1)
       by(auto simp add: stateX_def comps_with_imp_def Let_def)
     hence "x \<in> \<V>"
      by(simp add: important_def)
     moreover have underlying_invars_stateX: "underlying_invars stateX"
       using underlying_invars_pres[of k] stateX_def by simp
     ultimately show ?case 
       by(auto simp add:  underlying_invars_def inv_components_in_V_def x_prop(2) connected_component_def)
    next
      case 3 
      then show ?case 
        using V_non_empt by simp
    qed
    thus ?thesis
      by(rule laminar_family_number_of_sets[OF N_def \<V>_finite])
  qed
  have "((\<Sum> j \<in> {1..i}. (let state' = ((orlins_one_step_check ^^ (j - 1))  (send_flow initial)) in 
                                                     card { v. important state' v} )) +
                                                     card { v. important_initial initial v}) =
       (\<Sum> j \<in> {1..i}. (card (Imps j))) + card { v. important_initial initial v}"
  proof-
    have "(\<Sum>j = Suc 0..i.
        card (Collect (important ((orlins_one_step_check ^^ (j - Suc 0)) (local.send_flow initial))))) =
         (\<Sum>j = Suc 0..i. card (Imps j))"
      unfolding Imps_def Let_def
    proof(subst sym[OF send_flow_sim],
        rule sum_up_same_cong[OF _ _ refl, of "Suc 0" "Suc i", simplified sum_indes_less_suc_conv],
        goal_cases)
      case 1
      thus ?case
        by(auto simp add: sym[OF funpow_swap1] sym[OF o_apply[of orlins_one_step_check 
                "orlins_one_step_check ^^ (_ - Suc 0)"]] sym[OF funpow.simps(2)])
    qed simp
    thus ?thesis by simp
  qed
  also have " ... = 
         (\<Sum> j \<in> {1..i}. (card (Imps j))) +  (card (Imps 0))"
    unfolding Imps_def
    using pseudo_initial_important by (simp, presburger)
  also have "... = (\<Sum> j \<in> {0..i}. (card (Imps j)))"
    by(auto intro!: sum.atLeast_Suc_atMost[symmetric] simp add:  add.commute[of "sum _ _" "card _"])
  also have "... = (\<Sum> j \<in> {0..i}. (card (comps_with_imp j)))"
    using card_Imps_card_compst_with_ip_same by simp
  also have "... = (\<Sum> j \<in> {0..<Suc i}. (card (comps_with_imp j)))"
    by(unfold sum_indes_less_suc_conv) simp 
  also have "... \<le> (\<l> + 1) * card \<S>"
    using finite_S  comps_with_imp_subs_S  component_lifetime  beyonf_i_empty 
    by (rule sum_cards_with_life_time[of \<S> comps_with_imp "\<l>" i])
  also have "... \<le> (\<l> + 1) * (2*N - 1)"
    using card_S_laminar_bound  mult_le_mono2 by blast
  finally show ?thesis by simp
qed

definition "\<k> =  nat (\<lceil>log 2 N \<rceil> + 3)"

theorem running_time_initial:
  assumes "final = orlins_time t\<^sub>O\<^sub>C (send_flow initial)"
  shows "prod.fst final + prod.fst (send_flow_time initial) \<le> 
              (N - 1) * (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) 
          +   (N * (\<l> + \<k> + 2) - 1)* (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f +
                                    t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B )
          +   ((\<l> + 1) * (2 * N - 1)) *(t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f)
          +   (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f ) + t\<^sub>O\<^sub>C 

                         \<and> prod.snd final = orlins (send_flow initial)"
proof(cases "\<forall> v \<in> \<V>. \<b> v = 0")
  case True 
  hence send_flow_succ_cond:"send_flow_succ_cond initial" 
    by(auto intro!: all_bal_zero_send_flow_dom(2)
             simp add: implementation_invar_initial balance_initial)
  have a:"prod.fst (send_flow_time initial) = (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f )"
      and bb:"return (send_flow initial) = success"
    using  initial_send_flow(2) 
    by(all \<open>subst send_flow_time_simps(1)[OF _ send_flow_succ_cond] |
            subst send_flow_simps(1)[OF _ send_flow_succ_cond]\<close>)
      (auto simp add: terminationB_iff send_flow_time_succ_upd_def send_flow_succ_upd_def)
  hence "prod.fst final = t\<^sub>O\<^sub>C"
    by (subst assms(1), subst orlins_time.psimps)(auto intro: orlins_time.domintros)
  moreover have "orlins (send_flow initial) = prod.snd final"
    using bb 
    by (subst orlins_time.psimps orlins.psimps |
        auto intro: orlins.domintros orlins_time.domintros simp add: assms(1))+
  ultimately show ?thesis
    using a by auto
next
  case False
  have Max_b_gtr_0:"Max {\<bar>\<b> v\<bar> |v. v \<in> \<V>} > 0"
    using False  Max_gr_iff[of "{\<bar>\<b> v\<bar> |v. v \<in> \<V>}" 0] \<V>_finite V_non_empt by auto
  define pseudo_initial where "pseudo_initial = initial \<lparr> current_\<gamma> := 2 * current_\<gamma> initial\<rparr>"
have pseudo_initial_return: "return pseudo_initial = notyetterm"
    by(auto simp add: pseudo_initial_def initial_def)
  have all_zero_initial: " a_current_flow initial e = 0" for e
    by(auto simp add: initial_def init_flow'(1)[OF refl])
  have new_gamma_pseudo_initial:"new_\<gamma> (initial\<lparr>current_\<gamma> := 2 * current_\<gamma> initial\<rparr>) =  current_\<gamma> initial"
    using all_zero_initial
    by (auto simp add: new_gamma_is(1) implementation_invar_gamm_upd 
                       implementation_invar_initial  current_gamma_initial underlying_invars_gamma
                       underlying_invars_initial)
  have send_flow_sim:"orlins_one_step_check pseudo_initial = send_flow initial"
    using pseudo_initial_return all_zero_initial 
         new_gamma_is(1)[OF implementation_invar_initial underlying_invars_initial]
     by(auto intro!: cong[OF refl, of _ _ send_flow] all_actives_zero_flow_same_state 
                     invar_gamma_initial
           simp add: orlins_one_step_check_def  orlins_one_step_def pseudo_initial_def 
                     new_gamma_pseudo_initial underlying_invars_initial False)
  have pseudo_initial_important:
       "important pseudo_initial v \<longleftrightarrow> important_initial initial v" for v
    by(simp add: pseudo_initial_def important_def important_initial_def new_gamma_pseudo_initial)
have underlying_invars_pseudo_initial: "underlying_invars pseudo_initial"
    and invar_gamma_pseudo_initial: "invar_gamma pseudo_initial"
    and invar_non_zero_b_pseudo_initial: "invar_non_zero_b pseudo_initial"
    and invar_integral_pseudo_initial: "invar_integral pseudo_initial"
    and invar_forest_pseudo_initial: "invar_forest pseudo_initial"
    and other_invars: "orlins_entry pseudo_initial"
                      "implementation_invar pseudo_initial"
                      "invar_isOptflow pseudo_initial"
    using invar_gamma_initial False \<V>_finite  \<epsilon>_axiom
    by(force simp add: invar_gamma_def pseudo_initial_def all_zero_initial 
                         update_gamma_same_F F_initial_empty implementation_invar_initial
                         invar_isOptflow_initial underlying_invars_initial current_gamma_initial
      intro!: invar_non_zero_b_gamma_upd_pres invar_non_zero_b_initial invar_integralI
              invar_forestI  implementation_invar_gamm_upd invar_isOpt_gamma_change
              underlying_invars_gamma orlins_entryI
             order.trans[of "\<bar> _ \<bar>" "(1/2) * (2 *  Max {\<bar>a_balance initial v\<bar> |v. v \<in> \<V>} )"
                               "(1 - \<epsilon>) * (2 *  Max _ )"]
             linorder_class.Max_ge)+
  note invars_pseudo_initial =  underlying_invars_pseudo_initial  
                               invar_gamma_pseudo_initial invar_non_zero_b_pseudo_initial
                              invar_integral_pseudo_initial invar_forest_pseudo_initial
                              other_invars
  have card_F_pseudo_initial: "N = card (comps \<V> (to_graph (\<FF> pseudo_initial)))"
    using not_reachable_empt empty_forest_axioms
    by(fastforce intro!: bij_betw_same_card[of "\<lambda> x. {x}"] 
               simp add: bij_betw_def inj_on_def adj_map_specs.vset.set.set_isin adj_map_specs.vset.set.invar_empty 
                         adj_map_specs.vset.set.set_empty pseudo_initial_def comps_def initial_def 
                         connected_component_def N_def empty_forest_empty(2))

  have "return ((orlins_one_step_check ^^ (N * (\<l> + \<k> + 2))) pseudo_initial) \<noteq> notyetterm"
    using \<l>_def \<k>_def invar_gamma_pseudo_initial underlying_invars_pseudo_initial
          invar_non_zero_b_pseudo_initial invar_integral_pseudo_initial invar_forest_pseudo_initial
          other_invars card_F_pseudo_initial 
    by (intro finally_termination)
  hence termy:"return ((orlins_one_step_check ^^ (N * (\<l> + \<k> + 2) - 1)) (send_flow initial)) \<noteq> notyetterm"
    using N_gtr_0 
    by (simp add: sym[OF send_flow_sim] sym[OF o_apply[of "_ ^^ _" "orlins_one_step_check"]] 
                  sym[OF funpow_Suc_right])
  obtain I where I_prop:"return ((orlins_one_step_check ^^ I) (send_flow initial)) \<noteq> notyetterm "
          "\<not> (\<exists> J < I. return ((orlins_one_step_check ^^ J) (send_flow initial)) \<noteq> notyetterm)"
    by(rule get_least, rule termy, simp) 
  have switch_timed_and_untimed:"(prod.snd ((orlins_one_step_time_check ^^ Ii) (t\<^sub>O\<^sub>C, send_flow initial))) =
         (orlins_one_step_check ^^ Ii)  (send_flow initial)" for Ii
  proof(cases I)
    case 0
    then show ?thesis 
    proof(subst notyetterm_no_change, goal_cases)
      case 1
      thus ?case
        using I_prop(1) by simp
    next
      case 2
      show ?case using I_prop(1)  return.exhaust 2
        by (subst (2) sym[OF snd_conv[of t\<^sub>O\<^sub>C "send_flow _"]], subst succ_fail_not_changes_time) auto
    qed
  next
    case (Suc n)
    thus ?thesis
    using False I_prop(2)
    by(auto intro!: same_as_without_time initial_invars
          simp add: underlying_invars_initial)
  qed
  have I_bound: " I \<le> (N * (\<l> + \<k> + 2) - 1)"
      using I_prop termy  not_less by blast
  have I_prop': "return (prod.snd ((orlins_one_step_time_check ^^ I) (t\<^sub>O\<^sub>C, send_flow initial))) \<noteq> notyetterm "
          "\<not> (\<exists> J < I. return (prod.snd ((orlins_one_step_time_check ^^ J) (t\<^sub>O\<^sub>C, send_flow initial))) \<noteq> notyetterm)"
    using switch_timed_and_untimed I_prop by auto
  have I_prop'': "return (prod.snd ((orlins_one_step_time_check ^^ I) (send_flow_time initial))) \<noteq> notyetterm "
          "\<not> (\<exists> J < I. return (prod.snd ((orlins_one_step_time_check ^^ J) (send_flow_time initial))) \<noteq> notyetterm)"
    using I_prop' equal_results_B[OF initial_send_flow(2)] 
          runtime_add_constant[of _ t\<^sub>O\<^sub>C 0 "send_flow initial"] 
          runtime_add_constant[of _ "prod.fst (send_flow_time initial)" 0 "send_flow initial"]
    by(auto simp add: add_fst_def)
  have to_time:"(orlins_one_step_time_check ^^ I) (t\<^sub>O\<^sub>C, send_flow initial) = 
        orlins_time t\<^sub>O\<^sub>C (send_flow initial)"
  proof(cases I)
    case 0
    then show ?thesis 
      using I_prop' return.exhaust 
      by (subst orlins_time.psimps | auto intro: orlins_time.domintros)+  
   next
    case (Suc n)
    thus ?thesis
      using  I_prop'(1) return.exhaust 
      by (subst  succ_fail_term_same_with_time[of _ t\<^sub>O\<^sub>C "send_flow initial"] | 
                   auto intro: sym[OF prod.collapse])+
  qed
  have to_usual: "(orlins_one_step_check ^^ I)  (send_flow initial) =
                  orlins (send_flow initial)"
  proof(cases I)
    case 0
    then show ?thesis 
      using I_prop return.exhaust 
      by (subst orlins.psimps | auto intro: orlins.domintros)+   
  next
    case (Suc n)
    thus ?thesis
      using  I_prop(1) return.exhaust 
      by (subst  succ_fail_term_same[of _ "send_flow initial"] | 
                   auto intro: sym[OF prod.collapse])+
  qed
  have time_swap:"prod.fst (send_flow_time initial) +++ (orlins_one_step_time_check ^^ I) (t\<^sub>O\<^sub>C, send_flow initial) =
       t\<^sub>O\<^sub>C +++  (orlins_one_step_time_check ^^ I) (send_flow_time initial)"
  proof(subst sym[OF runtime_add_constant], subst (6)sym[OF prod.collapse], 
      subst sym[OF runtime_add_constant], goal_cases)
    case 1
    show ?case
      by(rule arg_cong[of "(_, _)"])
        (auto simp add: equal_results_B[OF initial_send_flow(2)])
  qed
  have number_of_comps_diff: "card (comps \<V> (to_graph (\<FF> initial))) -
    card (comps \<V> (to_graph (\<FF> (prod.snd ((orlins_one_step_time_check ^^ I) (send_flow_time initial)))))) \<le> N - 1" 
    using \<V>_finite V_non_empt 
    by (auto simp add: Suc_leI card_gt_0_iff diff_le_mono2 comps_def pseudo_initial_def card_F_pseudo_initial )
  show ?thesis
  proof(rule, goal_cases)
    case 1
    have "prod.fst final + prod.fst (send_flow_time initial) = 
          t\<^sub>O\<^sub>C  + prod.fst ((orlins_one_step_time_check ^^ I) (send_flow_time initial))"
      using time_swap 
      by (simp add:  add_fst_def assms sym[OF to_time])
    also have "... \<le>  t\<^sub>O\<^sub>C + ((card (comps \<V> (to_graph (\<FF> initial))) -
    card (comps \<V> (to_graph (\<FF> (prod.snd ((orlins_one_step_time_check ^^ I) (send_flow_time initial))))))) *
   (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
   I * (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f + t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B) +
   ((\<Sum>j = 1..I.
        let state' = (orlins_one_step_check ^^ (j - 1)) (local.send_flow initial) in card {v. important state' v}) +
    card {v. important_initial initial v}) *
   (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
   (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f))"
      using I_prop'' False 
      by (fastforce intro!: add_mono running_time_sum_from_init[OF refl, of I])
    also have "... \<le> t\<^sub>O\<^sub>C + ((card (comps \<V> (to_graph (\<FF> initial))) -
    card (comps \<V> (to_graph (\<FF> (prod.snd ((orlins_one_step_time_check ^^ I) (send_flow_time initial))))))) *
   (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
   I * (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f + t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B) +
   ((\<l> + 1) * (2 * N - 1) *
   (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
   (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f)))"
      using  number_of_important[OF refl] I_prop False by simp
    also have "... \<le> t\<^sub>O\<^sub>C + ((N - 1) *
   (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
   I * (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f + t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B) +
   ((\<l> + 1) * (2 * N - 1) *
   (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
   (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f)))"
      using number_of_comps_diff by simp
    also have "... \<le> t\<^sub>O\<^sub>C + (N - 1) *
   (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
   ( N * (\<l> + \<k> + 2) - 1) * (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f + t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B) +
   ((\<l> + 1) * (2 * N - 1) *
   (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
   (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f))"
      using I_bound by simp
    finally show ?case by simp
  next
    case 2
    then show ?case 
      using  assms sym[OF to_time]  switch_timed_and_untimed to_usual 
      by simp
  qed
qed
    
end 
end