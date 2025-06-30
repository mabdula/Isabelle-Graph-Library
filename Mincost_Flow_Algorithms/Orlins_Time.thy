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

function (domintros) orlins_time::"nat \<Rightarrow> ('a, 'd, 'c, 'edge_type) Algo_state  
                         \<Rightarrow> nat \<times> ('a, 'd, 'c, 'edge_type) Algo_state" where
"(orlins_time tt\<^sub>O\<^sub>C  state) = (if (return state = success) then (tt\<^sub>O\<^sub>C, state)
                 else if (return state = failure) then (tt\<^sub>O\<^sub>C, state)
                 else (let f = current_flow state;
                      b = balance state;
                      \<gamma> = current_\<gamma> state;
                      E' = actives state;
                      \<gamma>' = (if \<forall> e \<in> to_set E'. f e = 0 then
                             min (\<gamma> / 2) (Max { \<bar> b v\<bar> | v. v \<in> \<V>})
                           else (\<gamma> / 2));
                      state'time = maintain_forest_time (state \<lparr>current_\<gamma> := \<gamma>' \<rparr>);
                      state''time = send_flow_time (prod.snd state'time)
                      in ((t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B + prod.fst state'time + prod.fst state''time) 
                         +++ (orlins_time tt\<^sub>O\<^sub>C (prod.snd state''time))))
)"
  by auto

definition orlins_one_step_time::"('a, 'd, 'c, 'edge_type) Algo_state 
                                   \<Rightarrow> nat \<times>('a, 'd, 'c, 'edge_type) Algo_state" where
"orlins_one_step_time state =(  (let f = current_flow state;
                      b = balance state;
                      \<gamma> = current_\<gamma> state;
                      E' = actives state;
                      \<gamma>' = (if \<forall> e \<in> to_set E'. f e = 0 then
                             min (\<gamma> / 2) (Max { \<bar> b v\<bar> | v. v \<in> \<V>})
                           else (\<gamma> / 2));
                      state'time = maintain_forest_time (state \<lparr>current_\<gamma> := \<gamma>' \<rparr>);
                      state''time = send_flow_time (prod.snd state'time)
                      in ((t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B + prod.fst state'time + prod.fst state''time), (prod.snd state''time))))"

fun orlins_one_step_time_check::"nat \<times> ('a, 'd, 'c, 'edge_type) Algo_state
                                  \<Rightarrow> nat \<times> ('a, 'd, 'c, 'edge_type) Algo_state" where
"orlins_one_step_time_check (t, state) = (  
                                 if return state = success then (t, state)
                                 else if return state = failure then (t, state)
                                 else (t +++ orlins_one_step_time state))"

lemma terminated_mono_one_step: "return (prod.snd ((orlins_one_step_time_check  ^^ i) init)) \<noteq> notyetterm \<Longrightarrow>
                                 (orlins_one_step_time_check  ^^ Suc i) init 
                                 = (orlins_one_step_time_check  ^^ i) init"
  apply(subst funpow.simps(2), simp, subst (2) surjective_pairing, subst orlins_one_step_time_check.simps) 
  using return.exhaust by auto

lemma terminated_mono: "return (prod.snd ((orlins_one_step_time_check  ^^ i) init)) \<noteq> notyetterm \<Longrightarrow>
                                 (orlins_one_step_time_check  ^^ (i + k )) init 
                                 = (orlins_one_step_time_check  ^^ i) init"
  apply(induction k arbitrary: i init)
  apply simp
  apply(subst add.commute, subst add_Suc, subst add.commute)
  apply(subst funpow.simps(2), subst o_apply)
  apply(subst (2) surjective_pairing, subst orlins_one_step_time_check.simps) 
  by (smt (z3) return.exhaust surjective_pairing)

lemma succ_fail_not_changes_time: " return (prod.snd (t, state')) = success
                                  \<or> return (prod.snd (t, state')) = failure  \<Longrightarrow>
compow k orlins_one_step_time_check (t, state') = (t, state')"
  apply(induction k, simp)
  subgoal for k
    by(subst funpow_Suc_right[of k orlins_one_step_time_check], fastforce simp add: return.simps(2))
  done

lemma maintain_forest_dom_aux_invar: "aux_invar state \<Longrightarrow> maintain_forest_dom state"
  using aux_invar_def termination_of_maintain_forest by blast

lemma invar_gamma_pres_orlins_one_step_time:
  assumes "aux_invar state" "invar_gamma state" "invar_non_zero_b state"
  shows "invar_gamma (prod.snd (orlins_one_step_time state))"
  unfolding orlins_one_step_time_def Let_def
  using assms
  apply(subst snd_conv)
  apply(subst sym[OF  equal_results_B])
  subgoal send_flow_dom
    apply(subst sym[OF equal_results_A])
    by(fastforce intro!: maintain_forest_dom_aux_invar send_flow_termination maintain_forest_invar_gamma_pres aux_invar_gamma 
       gamma_upd_aux_invar_pres[of state] invar_aux17_from_aux_invar | simp)+
  subgoal
    by(intro send_flow_invar_gamma_pres[OF  send_flow_dom] | 
       subst sym[OF equal_results_A] | 
       fastforce intro!: maintain_forest_dom_aux_invar  maintain_forest_invar_gamma_pres aux_invar_gamma 
       gamma_upd_aux_invar_pres[of state] invar_aux17_from_aux_invar| simp)+
  done

lemma orlins_time_and_not_time_one_step_check_equal:
  assumes "aux_invar state"
          "invar_gamma state"
          "invar_non_zero_b state"
    shows " (prod.snd (orlins_one_step_time_check (t,state))) = orlins_one_step_check state"
  apply(subst orlins_one_step_time_check.simps, subst orlins_one_step_check_def)
  unfolding orlins_one_step_time_def orlins_one_step_def add_fst_def Let_def
  using gamma_upd_aux_invar_pres[OF assms(2) assms(3), simplified Let_def]  assms  
  by (subst sym[OF equal_results_A]  sym[OF equal_results_B] | 
     fastforce intro!: send_flow_termination maintain_forest_invar_gamma_pres arg_cong[of _ _ send_flow] 
                      sym[OF equal_results_A] maintain_forest_dom_aux_invar aux_invar_gamma invar_aux17_from_aux_invar)+

lemma orlins_time_and_not_time_one_step_equal:
  assumes "aux_invar state"
          "invar_gamma state"
          "invar_non_zero_b state"
        shows "(prod.snd (orlins_one_step_time state)) = orlins_one_step state"
  unfolding orlins_one_step_time_def orlins_one_step_def add_fst_def Let_def
  using gamma_upd_aux_invar_pres[OF assms(2) assms(3), simplified Let_def]  assms  
  by (subst sym[OF equal_results_A]  sym[OF equal_results_B] | 
     fastforce intro!: send_flow_termination maintain_forest_invar_gamma_pres arg_cong[of _ _ send_flow] 
                      sym[OF equal_results_A] maintain_forest_dom_aux_invar aux_invar_gamma invar_aux17_from_aux_invar)+

lemma notyetterm_check_no_effect:"return state = notyetterm \<Longrightarrow> (orlins_one_step state) =  (orlins_one_step_check state)"
  by(simp add: orlins_one_step_check_def)

lemma notyetterm_check_no_effect_time:"return state = notyetterm \<Longrightarrow> (orlins_one_step_time state) =  (orlins_one_step_time_check (0, state))"
  by(simp add: add_fst_def)

lemma orlins_compow_time_invars_pres:
  assumes "aux_invar state"
          "invar_gamma state"
          "invar_non_zero_b state"
          "final = (prod.snd ((orlins_one_step_time_check ^^ k) (t,state)))"
    shows "aux_invar final \<and> invar_gamma final \<and>
              final = (orlins_one_step_check ^^ k) state \<and>
              (return final = notyetterm \<longrightarrow> invar_non_zero_b final)"
  using assms
proof(induction k arbitrary: state t final)
  case (Suc k)
  show ?case
  proof((subst Suc(5))+, rule, goal_cases)
    case 1
    show "aux_invar (prod.snd ((orlins_one_step_time_check ^^ Suc k) (t, state)))"
    apply(subst funpow_Suc_right, cases "return state")
    apply(simp add: conjunct1[OF Suc(1)[OF Suc(2) Suc(3) Suc(4) refl]], 
          simp add: conjunct1[OF Suc(1)[OF Suc(2) Suc(3) Suc(4) refl]])
      using Suc(1) aux_invar_pres_orlins_one_step[OF Suc(2) Suc(3) Suc(4)] 
            invar_gamma_pres_orlins_one_step[OF Suc(2) Suc(3) Suc(4)]
            orlins_time_and_not_time_one_step_equal[OF Suc(2) Suc(3) Suc(4)]  
            some_balance_after_one_step[OF _ Suc(2) Suc(3) Suc(4)] terminated_mono[of 0, simplified]  
      by (cases "return (orlins_one_step state) = notyetterm") 
         (auto simp add: add_fst_def)
  next
    case 2
    show ?case
    proof(rule, goal_cases)
      case 1
      show ?case
        apply(subst funpow_Suc_right, cases "return state" )
        using conjunct1[OF conjunct2[OF Suc(1)[OF Suc(2) Suc(3) Suc(4) refl]], of t]  apply (simp, simp)
        using Suc(1)  aux_invar_pres_orlins_one_step[OF Suc(2) Suc(3) Suc(4)] 
              invar_gamma_pres_orlins_one_step[OF Suc(2) Suc(3) Suc(4)]
              orlins_time_and_not_time_one_step_equal[OF Suc(2) Suc(3) Suc(4)]  
              some_balance_after_one_step[OF _ Suc(2) Suc(3) Suc(4)] terminated_mono[of 0, simplified] 
        by (cases "return (orlins_one_step state) = notyetterm") 
           (auto simp add: funpow_Suc_right add_fst_def)
  next
    case 2
    show ?case
    proof(rule, goal_cases)
      case 1
      show ?case
       apply(cases "return state" )
        using conjunct1[OF conjunct2[OF conjunct2[OF Suc(1)[OF Suc(2) Suc(3) Suc(4) refl]], of t]] 
              terminated_mono[of 0 _ k, simplified] 
        apply (simp add: orlins_one_step_check_def succ_fail_not_changes, 
               simp add: orlins_one_step_check_def succ_fail_not_changes)
        using Suc(1) aux_invar_pres_orlins_one_step[OF Suc(2) Suc(3) Suc(4)] 
            invar_gamma_pres_orlins_one_step[OF Suc(2) Suc(3) Suc(4)]
            orlins_time_and_not_time_one_step_equal[OF Suc(2) Suc(3) Suc(4)]  
            some_balance_after_one_step[OF _ Suc(2) Suc(3) Suc(4)]  terminated_mono[of 0, simplified]
            funpow_swap1[of orlins_one_step_check]  notyetterm_no_change 
            notyetterm_check_no_effect[of state] 
        by (cases "return (orlins_one_step state) = notyetterm")
           (auto simp add: funpow_swap1 add_fst_def)
    next
      case 2
      have weird_subgoal: 
           "return (prod.snd (orlins_one_step_time_check ((orlins_one_step_time_check ^^ k) (t, state))))
             = notyetterm \<Longrightarrow> return state = notyetterm \<Longrightarrow>
             prod.snd (orlins_one_step_time state) = orlins_one_step state \<Longrightarrow>
              return (orlins_one_step state) \<noteq> notyetterm \<Longrightarrow> False"
     using notyetterm_check_no_effect_time[of state]
           terminated_mono[of 0 "orlins_one_step_time_check (t, state)" k, simplified funpow_0 plus_nat.add_0]
           funpow_swap1 [of orlins_one_step_time_check k "(t, state)"]
           orlins_time_and_not_time_one_step_check_equal[OF Suc(2) Suc(3) Suc(4), of 0] 
           orlins_time_and_not_time_one_step_check_equal[OF Suc(2) Suc(3) Suc(4), of t] 
     by metis
      show ?case
        apply(cases "return state" )
        using conjunct1[OF conjunct2[OF conjunct2[OF Suc(1)[OF Suc(2) Suc(3) Suc(4) refl]], of t]] 
              terminated_mono[of 0 _ k, simplified] 
        apply (simp add: orlins_one_step_check_def succ_fail_not_changes, 
               simp add: orlins_one_step_check_def succ_fail_not_changes)
        using mp[OF conjunct2[OF conjunct2[OF conjunct2[OF Suc(1)[OF _ _ _ refl]]]]]
              aux_invar_pres_orlins_one_step[OF Suc(2) Suc(3) Suc(4)] 
              invar_gamma_pres_orlins_one_step[OF Suc(2) Suc(3) Suc(4)]
              orlins_time_and_not_time_one_step_equal[OF Suc(2) Suc(3) Suc(4)]  
              some_balance_after_one_step[OF _ Suc(2) Suc(3) Suc(4)]  weird_subgoal        
       by (auto simp add: add_fst_def funpow_swap1 orlins_one_step_check_def)
      qed
    qed
  qed
qed simp

lemma same_as_without_time:
  assumes "aux_invar state"
          "invar_gamma state"
          "invar_non_zero_b state"
    shows "prod.snd ((orlins_one_step_time_check ^^ i) (t, state)) = (orlins_one_step_check ^^ i) state"
  using assms(1) assms(2) assms(3) orlins_compow_time_invars_pres by blast

lemma Phi_contribution_important:
 "invar_non_zero_b state \<Longrightarrow> invar_gamma state \<Longrightarrow>  orlins_entry state \<Longrightarrow> 
  v \<in> \<V> \<Longrightarrow> \<gamma>' = new_\<gamma> state \<Longrightarrow> 
          (\<lceil>\<bar> balance state v\<bar> / \<gamma>' - (1 - \<epsilon>)\<rceil> = 1 \<longleftrightarrow> important state v)
        \<and> (\<lceil>\<bar> balance state v\<bar> / \<gamma>' - (1 - \<epsilon>)\<rceil> = 0 \<longleftrightarrow> \<not> important state v)"
  using balance_less_new_gamma[of v state] Phi_init(2,3)[of state v]
  unfolding invar_gamma_def important_def
  by (smt (verit, del_insts) \<epsilon>_axiom(4) ceiling_less_one less_divide_eq mult_le_cancel_right1)

lemma runtime_add_constant:"(orlins_one_step_time_check  ^^ i) (t + s, state) = 
       t +++ (orlins_one_step_time_check  ^^ i) (s, state)"
  apply(induction i arbitrary: s t state)
  unfolding add_fst_def apply simp
  apply(subst funpow_Suc_right)+
  by (auto simp add: add_fst_def)
 

theorem running_time_sum_general:
  assumes "final = (orlins_one_step_time_check  ^^ i) (0, state)"
          "return (prod.snd final) = notyetterm"
          "aux_invar state"
          "invar_gamma state"
          "invar_non_zero_b state"
          "orlins_entry state"
        shows "prod.fst final \<le> (card (comps \<V> (to_graph (\<FF>_imp state))) 
                                    - card (comps \<V> (to_graph (\<FF>_imp (prod.snd final)))))
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
  define \<gamma>' where "\<gamma>' = (if \<forall>e \<in> to_set E'. f e = 0 then min (\<gamma> / 2) (Max {\<bar>b v\<bar> |v. v \<in> \<V>}) else \<gamma> / 2)"
  define state'time where "state'time = maintain_forest_time (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)"
  define state''time where "state''time = send_flow_time (prod.snd state'time)"
  have "orlins_one_step_time already_done = (t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B + prod.fst state'time + prod.fst state''time, prod.snd state''time)"
    by(simp add: orlins_one_step_time_def state''time_def state'time_def \<gamma>'_def E'_def \<gamma>_def b_def f_def Let_def)
  define bigsum where "bigsum = (card (comps \<V> (to_graph (\<FF>_imp state))) - card (comps \<V> (to_graph (\<FF>_imp already_done)))) *
         (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) + i * (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f + t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B) +
         (\<Sum>j = 1..i.
            let state' = (orlins_one_step_check ^^ (j - 1)) state
            in card {a. important state' a}) * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f)" 
  have bigsum_bound:"prod.fst ((orlins_one_step_time_check ^^ i) (0, state))
       \<le> bigsum"
    using Suc(1)[OF refl i_notyetterm Suc(4) Suc(5) Suc(6)] already_done_def  Suc.prems(5) Suc.prems(6) 
          bigsum_def by blast
  have aux_invar_after_gamma: "aux_invar (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)"
    using Suc.prems(3) Suc.prems(4) Suc.prems(5) already_done_def aux_invar_gamma 
          orlins_compow_time_invars_pres by blast
  define timeA where "timeA = (card (comps \<V> (to_graph (\<FF>_imp already_done))) - 
      card (comps \<V> (to_graph (\<FF>_imp (prod.snd (maintain_forest_time 
                       (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>))))))) *
  (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B) +
  (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C)"
  have aux_invar_after_gamma: "aux_invar (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)"
    using orlins_compow_time_invars_pres[OF Suc(4) Suc(5) Suc(6) refl] 
    by (fastforce intro: aux_invar_gamma simp add: already_done_def)
  have timeA:"prod.fst state'time  = timeA"
    using aux_invar_after_gamma 
          maintain_forest_dom_aux_invar[simplified ] 
          terminationA_iff[OF invar_aux17_from_aux_invar[OF aux_invar_after_gamma ]]
    by (auto intro: time_boundA[of "already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>", simplified] simp add: state'time_def timeA_def)
  have aux_invar_state'time:"aux_invar (prod.snd state'time)"
    using aux_invar_after_gamma 
    unfolding state'time_def
    by(subst  sym[OF equal_results_A], 
       auto intro: maintain_forest_dom_aux_invar maintain_forest_invar_aux_pres invar_aux17_from_aux_invar)
  have invar_gamma_after_gamma:"invar_gamma (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)"
    using  gamma_upd_aux_invar_pres[of already_done,
           simplified sym[OF new_\<gamma>_def[simplified Let_def]] 
           sym[OF \<gamma>'_def[ simplified E'_def f_def  \<gamma>_def b_def sym[OF new_\<gamma>_def[simplified Let_def]]]]]
           i_notyetterm orlins_compow_time_invars_pres[OF Suc(4) Suc(5) Suc(6) refl] 
    by(fastforce simp add: already_done_def)   
  have invar_gamma_state'time:"invar_gamma (prod.snd state'time)"
    using  sym[OF equal_results_A[OF _ invar_aux17_from_aux_invar]]  aux_invar_after_gamma  gamma_upd_aux_invar_pres[of already_done,
           simplified sym[OF new_\<gamma>_def[simplified Let_def]] 
           sym[OF \<gamma>'_def[ simplified E'_def f_def  \<gamma>_def b_def sym[OF new_\<gamma>_def[simplified Let_def]]]]]
           i_notyetterm orlins_compow_time_invars_pres[OF Suc(4) Suc(5) Suc(6) refl] 
    by (fastforce intro:  maintain_forest_dom_aux_invar maintain_forest_invar_gamma_pres simp add: already_done_def state'time_def)
  have send_flow_time_phi:"prod.fst (send_flow_time (prod.snd state'time))
       \<le> nat (\<Phi> (prod.snd state'time)) * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) + (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f)"
    using  time_boundB[OF invar_gamma_state'time refl] by simp
  have Phi_mod_A:"\<Phi>  (prod.snd state'time)
       \<le> \<Phi> (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>) + int (card (comps \<V> (to_graph (\<FF>_imp already_done)))) -
             int (card (comps \<V> (to_graph (\<FF>_imp (maintain_forest (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>))))))"
    using equal_results_A[OF maintain_forest_dom_aux_invar invar_aux17_from_aux_invar] 
          aux_invar_after_gamma Phi_increase[OF aux_invar_after_gamma invar_gamma_after_gamma]   
    by (simp add: state'time_def)
  have "to_graph (\<FF>_imp (prod.snd state'time)) = to_graph (\<FF>_imp (prod.snd state''time))"
    unfolding state''time_def
    apply(subst sym[OF equal_results_B])
    using  sym[OF send_flow_changes_\<FF>_imp] send_flow_termination invar_gamma_state'time by auto
  have "to_graph (\<FF>_imp (prod.snd final)) = to_graph (\<FF>_imp (prod.snd state''time))"
    unfolding Suc 
    apply(subst funpow.simps(2), subst o_apply, subst (2) surjective_pairing, subst orlins_one_step_time_check.simps)
    using i_notyetterm 
    by(simp add: add_fst_def  orlins_one_step_time_def state''time_def state'time_def already_done_def
               \<gamma>'_def E'_def f_def \<gamma>_def b_def Let_def)
  have card_maintain_forest_reduce:"card (comps \<V> (to_graph (\<FF>_imp already_done))) \<ge>
             card (comps \<V> (to_graph (\<FF>_imp (maintain_forest (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)))))"
    using card_decrease aux_invar_after_gamma maintain_forest_dom_aux_invar by force
  hence "\<Phi> (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>) + int (card (comps \<V> (to_graph (\<FF>_imp already_done)))) -
             int (card (comps \<V> (to_graph (\<FF>_imp (maintain_forest (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)))))) =
         \<Phi> (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>) +  (card (comps \<V> (to_graph (\<FF>_imp already_done)))) -
             card (comps \<V> (to_graph (\<FF>_imp (maintain_forest (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)))))" by auto
  have orlins_entry_late:"orlins_entry ((orlins_one_step_check ^^ i) state)"
    using Suc  same_as_without_time[OF Suc(4) Suc(5) Suc(6)]  i_notyetterm 
    by (auto intro:  orlins_entry_after_compow)
  have invars_late: "invar_non_zero_b  ((orlins_one_step_check ^^ i) state)"
                    "invar_gamma ((orlins_one_step_check ^^ i)  state)"
    using orlins_compow_time_invars_pres[OF Suc(4) Suc(5) Suc(6) refl] 
          i_notyetterm by fastforce+
  have Phi_number_important:"state' = (orlins_one_step_check ^^ i) state \<Longrightarrow>
         \<Phi> (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>) = card {a. important (state') a}" for state'
    unfolding  already_done_def \<gamma>'_def E'_def f_def b_def \<gamma>_def sym[OF new_\<gamma>_def[simplified Let_def]] \<Phi>_def 
    apply((subst same_as_without_time[OF Suc(4) Suc(5) Suc(6)])+ , rule trans)
     using Phi_contribution_important[of already_done ,
                simplified already_done_def  orlins_compow_time_invars_pres[OF Suc(4) Suc(5) Suc(6) refl],
             OF invars_late(1) invars_late(2) orlins_entry_late _ refl] 
     by (fastforce intro!: binary_sum[OF \<V>_finite] arg_cong[of _ _ int] arg_cong[of _ _ card] simp add: important_def)+
   have "prod.fst (orlins_one_step_time already_done)
         = prod.fst state'time + prod.fst state''time + t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B"
     by(simp add: orlins_one_step_time_def state'time_def state''time_def \<gamma>'_def \<gamma>_def E'_def f_def b_def Let_def)
   also have "... \<le> timeA + nat (\<Phi> (prod.snd state'time)) * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) + (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f) +
                      t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B"
     using timeA send_flow_time_phi unfolding state''time_def by simp
   also have "... \<le> timeA + ( nat(\<Phi> (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)) +
                                    (card (comps \<V> (to_graph (\<FF>_imp already_done)))) -
                               card (comps \<V> (to_graph (\<FF>_imp (local.maintain_forest (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)))))) * 
                            (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) + (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f) +
                      t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B"
     using Phi_mod_A card_maintain_forest_reduce by auto
   also have "... \<le> (card (comps \<V> (to_graph (\<FF>_imp already_done))) 
                             - card (comps \<V> (to_graph (\<FF>_imp (maintain_forest (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)))))) *
       (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
       (nat (\<Phi> (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>))) * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
       (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f + t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C) + t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B"
     using sym[OF equal_results_A[OF maintain_forest_dom_aux_invar[OF aux_invar_after_gamma]]]  
           add_mult_distrib2 less_or_eq_imp_le 
     by (auto simp add: add_mult_distrib diff_add_assoc[OF card_maintain_forest_reduce] 
                        invar_aux17_from_aux_invar[OF aux_invar_after_gamma]  timeA_def)
   also have "... \<le> (card (comps \<V> (to_graph (\<FF>_imp already_done))) 
                           - card (comps \<V> (to_graph (\<FF>_imp (local.maintain_forest (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)))))) *
       (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
       card {v . important already_done v } * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
       (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f + t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B)"
     using Phi_number_important[OF refl, simplified sym[OF already_done_def]]   
           same_as_without_time[OF Suc(4) Suc(5) Suc(6), of i 0, simplified sym[OF already_done_def]] 
     by simp
   finally have ineq_for_one_it:"prod.fst (orlins_one_step_time already_done)
     \<le> (card (comps \<V> (to_graph (\<FF>_imp already_done))) 
               - card (comps \<V> (to_graph (\<FF>_imp (local.maintain_forest (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)))))) *
        (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
       card {v. important already_done v} * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
        (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f + t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B) " by simp
   have forest_final:"to_graph (\<FF>_imp (local.maintain_forest (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>))) 
                         = to_graph (\<FF>_imp (prod.snd final))" 
     unfolding Suc(2)
     apply(subst funpow.simps(2), subst o_apply, subst (2) surjective_pairing, subst orlins_one_step_time_check.simps)
     apply(subst if_not_P, simp add: i_notyetterm)+
     using  maintain_forest_invar_gamma_pres aux_invar_after_gamma invar_gamma_after_gamma 
             sym[OF equal_results_A] sym[OF equal_results_B] 
              send_flow_termination maintain_forest_dom_aux_invar sym[OF send_flow_changes_\<FF>_imp] 
                       maintain_forest_invar_gamma_pres invar_aux17_from_aux_invar 
     by (force simp add: Let_def sym[OF \<gamma>'_def[simplified f_def b_def E'_def \<gamma>_def]]
                        sym[OF already_done_def] add_fst_def  orlins_one_step_time_def)
   have card_decrease_done:"(card (comps \<V> (to_graph (\<FF>_imp state))) \<ge> 
                card (comps \<V> (to_graph (\<FF>_imp already_done))))"
     using same_as_without_time[OF Suc(4) Suc(5) Suc(6), of i 0, simplified sym[OF already_done_def]]
     by(auto intro: orlins_some_steps_card_decrease[OF refl Suc(4) Suc(5) Suc(6)])
  show ?case 
    apply(subst Suc(2), subst funpow.simps(2), subst o_apply, subst (2) surjective_pairing, 
          subst orlins_one_step_time_check.simps)
    apply(subst if_not_P, simp add: i_notyetterm)+
    unfolding add_fst_def
    apply(subst fst_conv, subst sym[OF already_done_def])
    apply(rule order.trans)
    apply(rule add_mono[OF bigsum_bound ineq_for_one_it])
    apply(subst sym[OF forest_final])
    unfolding bigsum_def 
    apply(subst (4)already_done_def, subst same_as_without_time[OF Suc(4) Suc(5) Suc(6), of i 0])
    apply(subst add_assoc2, subst add_assoc2)
    apply(subst (16) semiring_normalization_rules(24), subst add_assoc3, subst semiring_normalization_rules(1))
    using card_maintain_forest_reduce card_decrease_done 
    by(auto simp add: algebra_simps)
qed

theorem running_time_sum:
  assumes "final = (orlins_one_step_time_check  ^^ (Suc i)) (0, state)"
          "return (prod.snd final) \<noteq> notyetterm"
          "aux_invar state"
          "invar_gamma state"
          "invar_non_zero_b state"
          "orlins_entry state"
          "\<And> j final. j \<le> i \<Longrightarrow> final = (orlins_one_step_time_check  ^^ j) (0, state)
              \<Longrightarrow> return (prod.snd final) = notyetterm"
        shows "prod.fst final \<le> (card (comps \<V> (to_graph (\<FF>_imp state))) 
                                  - card (comps \<V> (to_graph (\<FF>_imp (prod.snd final)))))
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
  define \<gamma>' where "\<gamma>' = (if \<forall> e \<in> to_set E'. f e = 0 then min (\<gamma> / 2) (Max {\<bar>b v\<bar> |v. v \<in> \<V>}) else \<gamma> / 2)"
  define state'time where "state'time = maintain_forest_time (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)"
  define state''time where "state''time = send_flow_time (prod.snd state'time)"
  have "orlins_one_step_time already_done = 
    (t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B + prod.fst state'time + prod.fst state''time, prod.snd state''time)"
    by(simp add: orlins_one_step_time_def state''time_def state'time_def \<gamma>'_def E'_def \<gamma>_def b_def f_def Let_def)
  define bigsum where "bigsum = (card (comps \<V> (to_graph (\<FF>_imp state))) -
                                 card (comps \<V> (to_graph (\<FF>_imp already_done)))) *
         (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) + i * (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f + t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B) +
         (\<Sum>j = 1..i.
            let state' = (orlins_one_step_check ^^ (j - 1)) state
            in card {a. important state' a}) * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f)" 
  have bigsum_bound:"prod.fst ((orlins_one_step_time_check ^^ i) (0, state))
       \<le> bigsum"
    unfolding bigsum_def already_done_def
    using assms 
    by (fastforce intro!: running_time_sum_general[OF refl])
  have aux_invar_after_gamma: "aux_invar (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)"
    using assms(1-6) already_done_def aux_invar_gamma 
          orlins_compow_time_invars_pres by blast
  define timeA where "timeA = (card (comps \<V> (to_graph (\<FF>_imp already_done)))
                   - card (comps \<V> (to_graph (\<FF>_imp (prod.snd (maintain_forest_time (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>))))))) *
  (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B) +
  (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C)"
  have aux_invar_after_gamma: "aux_invar (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)"
    using orlins_compow_time_invars_pres[OF assms(3,4,5) refl] 
    by (fastforce intro: aux_invar_gamma simp add: already_done_def)
  have timeA:"prod.fst state'time  = timeA"
    using aux_invar_after_gamma 
          maintain_forest_dom_aux_invar[simplified ] 
          terminationA_iff[OF invar_aux17_from_aux_invar[OF aux_invar_after_gamma ]]
    by (auto intro: time_boundA[of "already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>", simplified] simp add: state'time_def timeA_def)
  have aux_invar_state'time:"aux_invar (prod.snd state'time)"
    using aux_invar_after_gamma 
    unfolding state'time_def
    by(subst  sym[OF equal_results_A], 
       auto intro: maintain_forest_dom_aux_invar maintain_forest_invar_aux_pres invar_aux17_from_aux_invar)
  have invar_gamma_after_gamma:"invar_gamma (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)"
    using  gamma_upd_aux_invar_pres[of already_done,
           simplified sym[OF new_\<gamma>_def[simplified Let_def]] 
           sym[OF \<gamma>'_def[ simplified E'_def f_def  \<gamma>_def b_def sym[OF new_\<gamma>_def[simplified Let_def]]]]]
           i_notyetterm orlins_compow_time_invars_pres[OF assms(3,4,5) refl] 
    by(fastforce simp add: already_done_def)    
  have invar_gamma_state'time:"invar_gamma (prod.snd state'time)"
    using  sym[OF equal_results_A]  aux_invar_after_gamma  gamma_upd_aux_invar_pres[of already_done,
           simplified sym[OF new_\<gamma>_def[simplified Let_def]] 
           sym[OF \<gamma>'_def[ simplified E'_def f_def  \<gamma>_def b_def sym[OF new_\<gamma>_def[simplified Let_def]]]]]
           i_notyetterm orlins_compow_time_invars_pres[OF assms(3,4,5) refl] 
    by (fastforce intro!:  maintain_forest_dom_aux_invar maintain_forest_invar_gamma_pres invar_aux17_from_aux_invar simp add: already_done_def state'time_def)
  have send_flow_time_phi:"prod.fst (send_flow_time (prod.snd state'time))
       \<le> nat (\<Phi> (prod.snd state'time)) * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) + (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f)"
    using  time_boundB[OF invar_gamma_state'time refl] by simp
  have Phi_mod_A:"\<Phi>  (prod.snd state'time)
       \<le> \<Phi> (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>) + int (card (comps \<V> (to_graph (\<FF>_imp already_done)))) -
             int (card (comps \<V> (to_graph (\<FF>_imp (maintain_forest (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>))))))"
    using equal_results_A[OF maintain_forest_dom_aux_invar] aux_invar_after_gamma          
      Phi_increase invar_gamma_after_gamma
      invar_aux17_from_aux_invar 
    by (force simp add: state'time_def)
  have "to_graph (\<FF>_imp (prod.snd state'time)) = to_graph (\<FF>_imp (prod.snd state''time))"
    using  sym[OF equal_results_B]  sym[OF send_flow_changes_\<FF>_imp] send_flow_termination invar_gamma_state'time
    by (simp add:  state''time_def)
  have "to_graph (\<FF>_imp (prod.snd final)) = to_graph (\<FF>_imp (prod.snd state''time))"
    unfolding Suc 
    apply(subst funpow.simps(2), subst o_apply, subst (2) surjective_pairing, subst orlins_one_step_time_check.simps)
    using i_notyetterm 
    by(simp add: add_fst_def  orlins_one_step_time_def state''time_def state'time_def already_done_def
               \<gamma>'_def E'_def f_def \<gamma>_def b_def Let_def)
  have card_maintain_forest_reduce:"card (comps \<V> (to_graph (\<FF>_imp already_done))) \<ge>
             card (comps \<V> (to_graph (\<FF>_imp (maintain_forest (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)))))"
    using card_decrease aux_invar_after_gamma maintain_forest_dom_aux_invar by force
  hence "\<Phi> (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>) + int (card (comps \<V> (to_graph (\<FF>_imp already_done)))) -
             int (card (comps \<V> (to_graph (\<FF>_imp (maintain_forest (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)))))) =
         \<Phi> (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>) +  (card (comps \<V> (to_graph (\<FF>_imp already_done)))) -
             card (comps \<V> (to_graph (\<FF>_imp (maintain_forest (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)))))" by auto
  have orlins_entry_late:"orlins_entry ((orlins_one_step_check ^^ i) state)"
    using Suc(2-6) Suc(7)[of i] same_as_without_time[OF assms(3,4,5)]  i_notyetterm 
    by(auto intro: orlins_entry_after_compow)
  have invars_late: "invar_non_zero_b  ((orlins_one_step_check ^^ i) state)"
                    "invar_gamma ((orlins_one_step_check ^^ i)  state)"
    using orlins_compow_time_invars_pres[OF assms(3,4,5) refl] 
          i_notyetterm by fastforce+
  have Phi_number_important:"state' = (orlins_one_step_check ^^ i) state \<Longrightarrow>
         \<Phi> (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>) = card {a. important (state') a}" for state'
    unfolding  already_done_def \<gamma>'_def E'_def f_def b_def \<gamma>_def sym[OF new_\<gamma>_def[simplified Let_def]] \<Phi>_def 
    apply((subst same_as_without_time[OF assms(3,4,5)])+ , rule trans)
     using Phi_contribution_important[of already_done ,
                simplified already_done_def  orlins_compow_time_invars_pres[OF assms(3,4,5) refl],
             OF invars_late(1) invars_late(2) orlins_entry_late _ refl]  
     by (fastforce intro!: binary_sum[OF \<V>_finite] arg_cong[of _ _ int] arg_cong[of _ _ card] simp add: important_def)+
   have "prod.fst (orlins_one_step_time already_done)
         = prod.fst state'time + prod.fst state''time + t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B"
     by(simp add: orlins_one_step_time_def state'time_def state''time_def
               \<gamma>'_def \<gamma>_def E'_def f_def b_def Let_def)
   also have "... \<le> timeA + nat (\<Phi> (prod.snd state'time)) * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f)
                     + (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f) +  t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B"
     using timeA send_flow_time_phi by(simp add: state''time_def)
   also have "... \<le> timeA + ( nat(\<Phi> (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)) + 
                             (card (comps \<V> (to_graph (\<FF>_imp already_done)))) -
                               card (comps \<V> (to_graph (\<FF>_imp (local.maintain_forest (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)))))) * 
                            (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) + (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f) +
                      t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B"
     using Phi_mod_A card_maintain_forest_reduce by auto
   also have "... \<le> (card (comps \<V> (to_graph (\<FF>_imp already_done))) 
                              - card (comps \<V> (to_graph (\<FF>_imp (maintain_forest (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)))))) *
       (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
       (nat (\<Phi> (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>))) * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
       (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f + t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C) + t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B"
     using sym[OF equal_results_A[OF maintain_forest_dom_aux_invar[OF aux_invar_after_gamma]]]  
           add_mult_distrib2 less_or_eq_imp_le 
     by (auto simp add: add_mult_distrib diff_add_assoc[OF card_maintain_forest_reduce] 
               invar_aux17_from_aux_invar[OF aux_invar_after_gamma] timeA_def)
   also have "... \<le> (card (comps \<V> (to_graph (\<FF>_imp already_done))) -
                          card (comps \<V> (to_graph (\<FF>_imp (local.maintain_forest (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)))))) *
       (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
       card {v . important already_done v } * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
       (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f + t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B)"
     using Phi_number_important[OF refl, simplified sym[OF already_done_def]]   
           same_as_without_time[OF assms(3,4,5), of i 0, simplified sym[OF already_done_def]] 
     by simp
   finally have ineq_for_one_it:"prod.fst (orlins_one_step_time already_done)
     \<le> (card (comps \<V> (to_graph (\<FF>_imp already_done))) 
               - card (comps \<V> (to_graph (\<FF>_imp (local.maintain_forest (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>)))))) *
        (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
       card {v. important already_done v} * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
        (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f + t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B) " by simp
   have forest_final:"to_graph (\<FF>_imp (local.maintain_forest (already_done\<lparr>current_\<gamma> := \<gamma>'\<rparr>))) 
                            = to_graph (\<FF>_imp (prod.snd final))" 
     unfolding Suc(1)
     apply(subst funpow.simps(2), subst o_apply, subst (2) surjective_pairing, subst orlins_one_step_time_check.simps)
     apply(subst if_not_P, simp add: i_notyetterm)+
     unfolding sym[OF already_done_def] add_fst_def  orlins_one_step_time_def
     apply((subst let_swap[of prod.snd])+, simp)
     using maintain_forest_invar_gamma_pres aux_invar_after_gamma invar_gamma_after_gamma 
            sym[OF equal_results_A] sym[OF equal_results_B]
              send_flow_termination maintain_forest_dom_aux_invar sym[OF send_flow_changes_\<FF>_imp] 
                       maintain_forest_invar_gamma_pres invar_aux17_from_aux_invar 
     by (force simp add:  Let_def sym[OF \<gamma>'_def[simplified f_def b_def E'_def \<gamma>_def]])
   have card_decrease_done:"(card (comps \<V> (to_graph (\<FF>_imp state))) 
                                \<ge> card (comps \<V> (to_graph (\<FF>_imp already_done))))"
     using same_as_without_time[OF assms(3,4,5), of i 0, simplified sym[OF already_done_def]]
     by(auto intro: orlins_some_steps_card_decrease[OF refl assms(3,4,5)])
  show ?thesis
    apply(subst Suc(1), subst funpow.simps(2), subst o_apply, subst (2) surjective_pairing, 
          subst orlins_one_step_time_check.simps)
    apply(subst if_not_P, simp add: i_notyetterm)+
    unfolding add_fst_def
    apply(subst fst_conv, subst sym[OF already_done_def])
    apply(rule order.trans, rule add_mono[OF bigsum_bound ineq_for_one_it], subst sym[OF forest_final])
    unfolding bigsum_def 
    apply(subst (4)already_done_def, subst same_as_without_time[OF assms(3,4,5), of i 0])
    apply(subst add_assoc2, subst add_assoc2)
    apply(subst (16) semiring_normalization_rules(24), subst add_assoc3, subst semiring_normalization_rules(1))
    using card_maintain_forest_reduce card_decrease_done 
    by(auto simp add: algebra_simps)
qed

definition "important_initial state v = ( v\<in> \<V> \<and> ( \<bar>balance state v \<bar> > (1 - \<epsilon>)*current_\<gamma> state ))"

theorem running_time_sum_from_init:
  assumes 
          "final = (orlins_one_step_time_check  ^^ i) (send_flow_time initial)"
          "return (prod.snd final) \<noteq> notyetterm"
          "\<And> j final. j < i \<Longrightarrow> final = (orlins_one_step_time_check  ^^ j)  (send_flow_time initial)
              \<Longrightarrow> return (prod.snd final) = notyetterm"
          "\<not> (\<forall> v \<in> \<V>. \<b> v = 0)"
        shows "prod.fst final \<le> (card (comps \<V> (to_graph (\<FF>_imp initial))) 
                             - card (comps \<V> (to_graph (\<FF>_imp (prod.snd final))))) * 
                            (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) 
                   +  i * (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f + t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B ) +
                     ((\<Sum> j \<in> {1..i}. (let state' = ((orlins_one_step_check ^^ (j - 1))  (send_flow initial)) in 
                                                     card { v. important state' v} )) +
                                                     card { v. important_initial initial v})
                           *(t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f)+
                       (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f )"
proof-
  have "prod.fst (send_flow_time initial) \<le> nat (\<Phi> initial) * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) + (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f)"
    using  time_boundB[OF invar_gamma_initial[OF assms(4)] refl] by simp
  have  invar_non_zero_b_initial: " invar_non_zero_b initial"
    using assms(4) unfolding invar_non_zero_b_def initial_def by simp
  have Max_gtr_0:"Max {\<bar>\<b> v\<bar> |v. v \<in> \<V>} > 0"
    using assms(4)  Max_lower_bound[OF \<V>_finite V_non_empt, of _ 0 "\<lambda> x. \<bar> \<b> x \<bar>"] by auto
  have b_lower:"x \<in> \<V> \<Longrightarrow> 0 \<le> \<lceil>\<bar>\<b> x\<bar> / Max {\<bar>\<b> v\<bar> |v. v \<in> \<V>} - (1 - \<epsilon>)\<rceil>" for x
    by (simp, smt (verit) Max_gtr_0 \<epsilon>_axiom(1) divide_less_0_iff)
  have b_upper:"x \<in> \<V> \<Longrightarrow>  \<lceil>\<bar>\<b> x\<bar> / Max {\<bar>\<b> v\<bar> |v. v \<in> \<V>} - (1 - \<epsilon>)\<rceil> \<le> 1" for x
    apply simp
    apply(rule order.trans[of _ "1+1"])
     apply(rule add_mono_thms_linordered_semiring(1))
    apply rule
    using \<epsilon>_axiom(2) 
    using Max.coboundedI[of "{\<bar>\<b> v\<bar> |v. v \<in> \<V>}"  "\<bar>\<b> x\<bar>"]  Max_gtr_0 \<V>_finite
    apply (metis (mono_tags) Max_lower_bound all_not_in_conv divide_le_eq_1_pos linorder_le_less_linear order_less_irrefl)
    using  \<epsilon>_axiom(2) by simp+
  have Phi_number_important:"(\<Phi> initial) = card {a. important_initial initial a}"
    unfolding initial_def \<Phi>_def important_initial_def new_\<gamma>_def Let_def apply simp
    apply(rule trans)
    apply(rule binary_sum[OF \<V>_finite])
    using b_lower b_upper 
    apply (smt (verit, best))
    apply(rule arg_cong[of _ _ int] arg_cong[of _ _ card])+
    apply(rule Collect_cong_set)
    by (smt (verit, ccfv_SIG) Max_gtr_0 b_upper one_le_ceiling pos_less_divide_eq)
  have "prod.fst (send_flow_time initial) \<le> nat (\<Phi> initial) * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) + (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f)"
    using time_boundB[OF invar_gamma_initial[OF assms(4)] refl] by simp
  have same_F_After_send_flow: "to_graph (\<FF>_imp (prod.snd (send_flow_time initial))) = to_graph (\<FF>_imp initial)"
    using equal_results_B send_flow_termination[OF invar_gamma_initial[OF assms(4)]]
          send_flow_changes_\<FF>_imp by simp
  have same_F_After_send_flow': "to_graph (\<FF>_imp (send_flow initial)) = to_graph (\<FF>_imp initial)"
    using equal_results_B send_flow_termination[OF invar_gamma_initial[OF assms(4)]]
          send_flow_changes_\<FF>_imp by simp
  have take_first_time_out:"((prod.fst (send_flow_time initial)) +++ ((orlins_one_step_time_check ^^ i) (0, send_flow initial))) =
        (orlins_one_step_time_check ^^ i) (send_flow_time initial)" for i
    using runtime_add_constant[of i "prod.fst (send_flow_time initial)" 0 "send_flow initial"] 
          equal_results_B send_flow_termination[OF invar_gamma_initial[OF assms(4)]] 
    by(simp add: add_fst_def)
  have send_flow_time_bound:"prod.fst (send_flow_time initial) \<le>
                 nat (\<Phi> initial) * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) + (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f)"
    using  time_boundB[OF invar_gamma_initial[OF assms(4)] refl] by simp
  show ?thesis
proof(cases i)
  case 0
  then show ?thesis
    using assms 0 same_F_After_send_flow Phi_number_important send_flow_time_bound
    by simp
next
  case (Suc nat)
  have aux_invar_send_flow:"aux_invar (send_flow initial)"
    using assms(4) aux_invar_initial invar_gamma_initial send_flow_termination send_flow_axioms
          send_flow_invar_aux_pres by blast
  have invar_gamma_send_flow:"invar_gamma (send_flow initial)"
    using assms(4) invar_gamma_initial send_flow_invar_gamma_pres send_flow_termination by blast
  have invar_non_zero_b_send_flow:"invar_non_zero_b (send_flow initial)"
    using assms(3)[of 0, OF _ refl, simplified] Suc  equal_results_B 
          send_flow_termination[OF invar_gamma_initial[OF assms(4)]] 
    by (fastforce intro!: remaining_balance_after_send_flow[OF _ refl])  
  have orlins_entry_send_flow:"orlins_entry (local.send_flow initial)"
    using assms(3)[of 0, OF _ refl, simplified] Suc  equal_results_B 
          send_flow_termination invar_gamma_initial[OF assms(4)] 
    by (fastforce intro: orlins_entry_after_send_flow[OF _ refl])
  have sum_bound:"prod.fst ((orlins_one_step_time_check ^^ Suc nat) (0, local.send_flow initial))
  \<le> (card (comps \<V> (to_graph (\<FF>_imp (local.send_flow initial)))) -
      card (comps \<V> (to_graph (\<FF>_imp (prod.snd ((orlins_one_step_time_check ^^ Suc nat) (0, local.send_flow initial))))))) *
     (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
     nat * (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f + t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B) +
     (\<Sum>j = 1..Suc nat.
         let state' = (orlins_one_step_check ^^ (j - 1)) (local.send_flow initial) in card {v. important state' v}) *
     (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
     (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f + t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B)"
  apply(rule running_time_sum[OF refl, of nat "send_flow initial", 
      OF _  aux_invar_send_flow invar_gamma_send_flow invar_non_zero_b_send_flow orlins_entry_send_flow])
    using  arg_cong[OF take_first_time_out[of "Suc nat", simplified add_fst_def], of prod.snd]
           assms(2)[simplified assms(1) Suc]  arg_cong[OF take_first_time_out[ simplified add_fst_def],
            of prod.snd] Suc assms(3) 
    by fastforce+
  have take_out:"prod.fst ((orlins_one_step_time_check ^^ i) (send_flow_time initial)) = 
       prod.fst (send_flow_time initial) + prod.fst ((orlins_one_step_time_check ^^ i) (0, local.send_flow initial))"
    apply(subst (2) surjective_pairing,
          subst sym[OF equal_results_B[OF send_flow_termination[OF invar_gamma_initial[OF assms(4)]]]])
    using runtime_add_constant[of i "prod.fst (send_flow_time initial)" 0, simplified add_fst_def]
    by simp
  show ?thesis 
    apply(subst assms(1))+ (*REWRITE*)
    apply(subst take_out)  
    apply(subst (5) surjective_pairing)
    apply(subst sym[OF equal_results_B[OF send_flow_termination[OF invar_gamma_initial[OF assms(4)]]]])
    apply(subst runtime_add_constant[of i "prod.fst (send_flow_time initial)" 0, simplified add_fst_def, simplified])
    apply(subst snd_conv) (*ALGEBRA*)
    apply(rule order.trans)
    apply(rule add_mono[OF  send_flow_time_bound sum_bound[simplified sym[OF Suc]]])
    using  same_F_After_send_flow' Phi_number_important Suc
    by (auto simp add: algebra_simps)
 qed
qed

definition  "\<l> =  nat (\<lceil> log 2 (4*M*N + (1 - \<epsilon>)) - log 2 \<epsilon>\<rceil>) + 1"

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
  have send_flow_sim:"orlins_one_step_check pseudo_initial = send_flow initial"
    unfolding orlins_one_step_check_def pseudo_initial_def initial_def orlins_one_step_def Let_def 
    using Max_b_gtr_0 N_def cardV_0 set_get(1-3)[OF invar_filter[OF \<E>_impl_meaning(2)]]
    by(subst maintain_forest_simps(2), intro maintain_forest_ret_condI )
      (fastforce intro!: maintain_forest_ret_condI 
               simp add: maintain_forest_simps(2) mult_less_0_iff)+
  have pseudo_initial_important:
       "important pseudo_initial v \<longleftrightarrow> important_initial initial v" for v
    by(simp add: pseudo_initial_def important_def important_initial_def initial_def new_\<gamma>_def)
  define Imps where "Imps = 
                 (\<lambda> j. if j \<le> i then let state = (orlins_one_step_check ^^ j) pseudo_initial in
                 {v. important ((orlins_one_step_check ^^ j) pseudo_initial) v} else {})"
  define comps_with_imp where "comps_with_imp = 
                 (\<lambda> j. (if j \<le> i then let state = (orlins_one_step_check ^^ j) pseudo_initial in
                 { C | C. C \<in> comps \<V>  (to_graph (\<FF>_imp state)) \<and> 
                        (\<exists> v. important state v \<and> C = connected_component (to_graph (\<FF>_imp state)) v)} else {}))"
  have aux_invar_pseudo_initial: "aux_invar pseudo_initial"
   using aux_invar_gamma[OF aux_invar_initial] by (simp add:  pseudo_initial_def)
  have invar_gamma_pseudo_initial: "invar_gamma pseudo_initial"
    using invar_gamma_initial assms(4) by(simp add: invar_gamma_def pseudo_initial_def)
  have invar_non_zero_b_pseudo_initial: "invar_non_zero_b pseudo_initial"
    using assms(4) by(simp add: pseudo_initial_def initial_def invar_non_zero_b_def)
  have invar_integral_pseudo_initial: "invar_integral pseudo_initial"
    by(simp add: invar_integral_def pseudo_initial_def initial_def)
  have invar_forest_pseudo_initial: "invar_forest pseudo_initial"
    using empty_forest_axioms vset.set.set_isin vset.set.invar_empty vset.set.set_empty
    by(simp add: invar_forest_def pseudo_initial_def initial_def to_rdgs_def to_graph_def)
  have aux_invar_pres: "aux_invar ((orlins_one_step_check ^^ j) pseudo_initial)" for j
    using aux_invar_pseudo_initial invar_gamma_pseudo_initial invar_non_zero_b_pseudo_initial
    by(auto intro: orlins_compow_aux_invar_pres[of pseudo_initial j])
  have invar_gamma_pres: "invar_gamma ((orlins_one_step_check ^^ j) pseudo_initial)" for j
    using aux_invar_pseudo_initial invar_gamma_pseudo_initial invar_non_zero_b_pseudo_initial
    by(fastforce intro: orlins_compow_invar_gamma_pres[of pseudo_initial j])
  have invar_non_zero_b_pres: "j \<le> i  \<Longrightarrow>invar_non_zero_b ((orlins_one_step_check ^^ j) pseudo_initial)" for j
    apply(cases "j = 0")
    using invar_non_zero_b_pseudo_initial apply simp
    apply(rule some_balance_after_k_steps[OF _ aux_invar_pseudo_initial invar_gamma_pseudo_initial
                                          invar_non_zero_b_pseudo_initial])
    apply(rule trans) defer
    apply(rule assms(3)[of "j-1", OF _ refl], simp)
    apply(subst sym[OF send_flow_sim]) 
    apply(subst sym[OF funpow_swap1])
    apply(subst sym[OF o_apply[of orlins_one_step_check "orlins_one_step_check ^^ (_ - 1)"]])
    apply(subst sym[OF funpow.simps(2)])
    by auto
  have invar_forest_after_one:"invar_forest (orlins_one_step_check pseudo_initial)"
    apply(subst send_flow_sim)
    unfolding invar_forest_def
    using  send_flow_termination[of initial] invar_gamma_initial assms(4)
    apply ((subst send_flow_changes_\<F>| subst send_flow_changes_current_\<gamma>), simp)+
    using empty_forest_axioms vset.set.set_isin vset.set.invar_empty vset.set.set_empty
    by(simp add: initial_def to_rdgs_def to_graph_def)
  have invar_integral_after_one:"invar_integral (orlins_one_step_check pseudo_initial)"
    using assms(4) invar_gamma_initial send_flow_termination aux_invar_initial invar_integral_initial
    by (fastforce intro: send_flow_invar_integral_pres 
          simp add: send_flow_sim initial_def to_rdgs_def empty_forest_axioms to_graph_def   
                    \<E>_impl_meaning set_filter(1) vset.set.set_isin vset.set.invar_empty vset.set.set_empty)
  have orlins_entry_pseudo_initial: "orlins_entry  pseudo_initial"
  proof-
    have "v \<in> \<V> \<Longrightarrow> \<bar>\<b> v\<bar> \<le> (1 - \<epsilon>) * (2 * Max {\<bar>\<b> v\<bar> |v. v \<in> \<V>}) " for v
    apply(rule order.trans, rule Max.coboundedI[of "{\<bar>\<b> v\<bar> |v. v \<in> \<V>}"])
    using  \<epsilon>_axiom Max.coboundedI[of "{\<bar>\<b> v\<bar> |v. v \<in> \<V>}"] \<V>_finite Max_b_gtr_0 
    by auto
  thus ?thesis
    by(auto simp add: orlins_entry_def pseudo_initial_def initial_def)
  qed
  have orlins_entry_one_step: "i > 0 \<Longrightarrow> orlins_entry (orlins_one_step_check pseudo_initial)"
    using  send_flow_sim  assms(4) invar_gamma_initial send_flow_term
    by (auto intro: orlins_entry_after_send_flow[OF _ refl] simp add: assms(3))
  have invar_forest_pres: "j \<le> i \<Longrightarrow> invar_forest ((orlins_one_step_check ^^ j) pseudo_initial)" for j
    apply(cases j)
    using invar_forest_pseudo_initial 
    apply(simp, subst Suc_pred', simp, subst funpow_Suc_right, simp)
    using invar_forest_after_one assms(4) aux_invar_initial invar_gamma_initial send_flow_invar_aux_pres
          send_flow_sim send_flow_termination send_flow_invar_gamma_pres invar_non_zero_b_pres[of 1, simplified]
          orlins_entry_one_step 
    by (auto intro: orlins_compow_invar_forest_pres)
  have invar_integral_pres: "j \<le> i \<Longrightarrow> invar_integral ((orlins_one_step_check ^^ j) pseudo_initial)" for j
    apply (cases j)
    using invar_integral_pseudo_initial
    apply(simp, subst Suc_pred', simp, subst funpow_Suc_right, simp)
    using aux_invar_initial  send_flow_invar_aux_pres  assms(4) invar_gamma_initial send_flow_invar_gamma_pres
          send_flow_termination assms(3) send_flow_sim send_flow_term remaining_balance_after_send_flow 
          invar_integral_after_one  invar_forest_after_one  orlins_entry_one_step 
    by (fastforce intro: orlins_compow_invar_integral_pres)
  have orlins_entry_pres: "j \<le> i \<Longrightarrow> orlins_entry ((orlins_one_step_check ^^ j) pseudo_initial)" for j
    apply(cases j)
    using orlins_entry_pseudo_initial apply simp
    apply(rule orlins_entry_after_compow[OF aux_invar_pseudo_initial invar_gamma_pseudo_initial 
                 invar_non_zero_b_pseudo_initial])
    apply(subst Suc_pred', simp, subst funpow_Suc_right)
    using send_flow_sim assms(3)[of "j-1", OF _ refl]  orlins_entry_pseudo_initial 
    by  auto
  have invar_isOptflow_pseudo_initial: "invar_isOptflow pseudo_initial"
    using invar_isOptflow_initial 
    by(simp add: pseudo_initial_def invar_isOptflow_def)
  have invar_isOptflow_pres: "invar_isOptflow ((orlins_one_step_check ^^ j) pseudo_initial)" for j
    using aux_invar_pseudo_initial  invar_gamma_pseudo_initial  invar_non_zero_b_pseudo_initial 
          invar_integral_pseudo_initial  invar_isOptflow_pseudo_initial  invar_forest_pseudo_initial 
          orlins_entry_pseudo_initial 
    by (auto intro: orlins_compow_invar_isOptflow_pres)

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
      apply(rule bij_betw_same_card[of "\<lambda> v. connected_component (to_graph (\<FF>_imp state)) v"])
      unfolding bij_betw_def
    proof(rule, goal_cases)
      case 1
      show ?case unfolding inj_on_def
      proof(rule,rule, rule,  goal_cases)
        case (1 x y)
        have new_gamma_gtr_0:"new_\<gamma> ((orlins_one_step_check ^^ j) pseudo_initial) > 0"
          apply(cases j)
          subgoal
            unfolding pseudo_initial_def new_\<gamma>_def Let_def initial_def 
            using Max_b_gtr_0 by auto          
          using gamma_upd_aux_invar_pres[of state] invar_gamma_pres[of j] invar_non_zero_b_pres[of j] j_leq_i
          by(auto simp add: invar_gamma_def Let_def state_def new_\<gamma>_def)
        have non_zero_balance_x:"\<bar>balance state x\<bar> > 0"
          using 1(1) j_leq_i invar_gamma_pres[of j] new_gamma_gtr_0
          unfolding state_def Imps_def Let_def invar_gamma_def important_def
          by (auto , smt (verit) \<epsilon>_axiom(4) divide_le_eq_1_pos mul_zero_cancel)
        have non_zero_balance_y:"\<bar>balance state y\<bar> > 0"
          using 1(2) j_leq_i invar_gamma_pres[of j] new_gamma_gtr_0
          unfolding state_def Imps_def Let_def invar_gamma_def important_def
          by (auto , smt (verit) \<epsilon>_axiom(4) divide_le_eq_1_pos mul_zero_cancel)
        have "representative state x = representative state y"
          using aux_invar_pres[of j, simplified aux_invar_def invar_aux7_def] 1(3)
          by(fastforce simp add: state_def connected_component_def)
        moreover have "representative state x = x"
          using aux_invar_pres[of j, simplified aux_invar_def invar_aux12_def] 1(3) 1(1)
                non_zero_balance_x j_leq_i
          by(fastforce simp add: Imps_def important_def Let_def state_def)
        moreover have "representative state y = y"
          using aux_invar_pres[of j, simplified aux_invar_def invar_aux12_def] 1(3) 1(2)
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
  define \<S> where "\<S> = (\<Union> j. (comps_with_imp j))"
  have finite_S: "finite \<S>" 
    using aux_invar_pres \<V>_finite
    by(simp add: \<S>_def comps_with_imp_def Let_def comps_def aux_invar_def 
                 invar_aux10_def)
  have comps_with_imp_subs_S: "\<Union> (range comps_with_imp) \<subseteq> \<S>"
    by(simp add :\<S>_def)
  have component_lifetime:  "ii + \<l>  < j \<Longrightarrow> C \<in> comps_with_imp ii \<Longrightarrow> C \<notin> comps_with_imp j" for ii j C
  proof( goal_cases)
    case 1
    have ii_leq_i:"ii \<le> i" 
      apply(rule ccontr)
      using  1(2)by(simp add: comps_with_imp_def Let_def)
    define state where "state = (orlins_one_step_check ^^ ii) pseudo_initial"
    have C_prop:" C \<in> comps \<V>  (to_graph (\<FF>_imp state))" 
                        "(\<exists> v. important state v \<and>
                              C = connected_component (to_graph (\<FF>_imp state)) v)"
      using 1(2) ii_leq_i unfolding comps_with_imp_def Let_def state_def by auto
    then obtain v where v_prop:"important state v" "C = connected_component (to_graph (\<FF>_imp state)) v"
      by auto
    show ?case
    proof(cases "j > i")
      case True
      then show ?thesis unfolding comps_with_imp_def by simp
    next
      case False
      hence j_leq_i:"j \<le> i" by simp
      have invar_gamma_state: "invar_gamma state"
        using invar_gamma_pres state_def by simp
      have aux_invar_state: "aux_invar state" 
        using aux_invar_pres state_def by simp
      have invar_non_zero_b_state: "invar_non_zero_b state"
        using invar_non_zero_b_pres state_def ii_leq_i by simp
      have invar_integral_state: "invar_integral state"
        using invar_integral_pres[of ii] state_def ii_leq_i by simp
      have invar_forest_state: "invar_forest state"
        using invar_forest_pres[of ii] state_def ii_leq_i by simp
      have orlins_entry_state: "orlins_entry state"
        using orlins_entry_pres state_def ii_leq_i by simp
      have invar_isOptflow_state: "invar_isOptflow state"
        using  invar_isOptflow_pres state_def by simp

      have "\<exists>k\<le>\<l> + 1. return ((orlins_one_step_check ^^ k) state) \<noteq> notyetterm \<or>
            connected_component (to_graph (\<FF>_imp state)) v 
                    \<subset> connected_component (to_graph (\<FF>_imp ((orlins_one_step_check ^^ k) state))) v"
        using invar_gamma_state  aux_invar_state  invar_non_zero_b_state  invar_integral_state 
              v_prop  \<l>_def  invar_forest_state  orlins_entry_state  invar_isOptflow_state 
        by (intro if_important_then_comp_increase_or_termination[of state v \<l>])
      then obtain k where k_prop:"k\<le>\<l> + 1" "return ((orlins_one_step_check ^^ k) state) \<noteq> notyetterm \<or>
            connected_component (to_graph (\<FF>_imp state)) v 
            \<subset> connected_component (to_graph (\<FF>_imp ((orlins_one_step_check ^^ k) state))) v"
        by auto
      have "return state \<noteq> notyetterm \<Longrightarrow> False"
        using pseudo_initial_def initial_def  ii_leq_i 1 j_leq_i
              assms(3)[of "ii-1", OF _ refl, simplified sym[OF send_flow_sim] 
              sym[OF o_apply[of "orlins_one_step_check ^^ (ii - 1)" "orlins_one_step_check" pseudo_initial]] 
              sym[OF funpow_Suc_right[of "ii - 1" orlins_one_step_check]]] 
        by (cases ii) (auto  simp add: state_def)
      hence k_not_0:"k = 0 \<Longrightarrow> False"
        using k_prop(2) by simp
      have "connected_component (to_graph (\<FF>_imp state)) v 
           \<subset> connected_component (to_graph (\<FF>_imp ((orlins_one_step_check ^^ k) state))) v"
        unfolding state_def
        apply(rule make_pos_rule'[OF k_prop(2)[simplified state_def], simplified])
        apply(subst sym[OF o_apply[of "orlins_one_step_check ^^ k" "orlins_one_step_check ^^ ii"]])
        apply(subst sym[OF funpow_add])
        apply(rule trans)
        defer
         apply(rule assms(3)[of "ii + k - 1", OF _  refl])
        using  j_leq_i 1(1) k_prop(1) apply simp
        using   1(1) k_prop(1) unfolding sym[OF send_flow_sim] 
        apply(subst sym[OF o_apply[of "orlins_one_step_check ^^ _" "orlins_one_step_check"]])
        apply(subst sym[OF funpow_Suc_right]) 
        apply(rule arg_cong[of _ _ return])
        apply(rule cong[of "_ ^^ _" "_ ^^ _"])
        apply(subst sym[OF Suc_pred'[of "ii + k"]])
        using k_not_0  add.commute[of k ii] by (auto, argo)
      moreover have "connected_component (to_graph (\<FF>_imp ((orlins_one_step_check ^^ k) state))) v
                \<subseteq> connected_component (to_graph (\<FF>_imp ((orlins_one_step_check ^^ ((j - ii) - k))
                                                ((orlins_one_step_check ^^ k) state)))) v"
        apply(rule con_comp_subset)
        apply(rule orlins_some_steps_forest_increase[OF refl, of "(orlins_one_step_check ^^ k) state" "(j-ii) - k"])
        unfolding state_def
        apply(subst sym[OF o_apply[of "orlins_one_step_check ^^ _" "orlins_one_step_check ^^ _"]], 
              subst sym[OF funpow_add], 
              simp add: aux_invar_pres[of "k + ii"] invar_gamma_pres[of "k + ii"]
                        invar_non_zero_b_pres[of "k + ii"] )+
        apply(subst sym[OF o_apply[of "orlins_one_step_check ^^ _" "orlins_one_step_check ^^ _"]], 
              subst sym[OF funpow_add])
        apply(rule  invar_non_zero_b_pres[of "k + ii"])
        using  j_leq_i k_prop(1) 1 by simp
      moreover have "to_graph (\<FF>_imp ((orlins_one_step_check ^^ ((j-ii) - k)) 
                         ((orlins_one_step_check ^^ k) state))) =
                     to_graph (\<FF>_imp ((orlins_one_step_check ^^ j) (pseudo_initial)))"
        unfolding state_def
        apply(subst sym[OF o_apply[of "orlins_one_step_check ^^ _" "orlins_one_step_check ^^ _"]] 
               sym[OF funpow_add])+
        using  j_leq_i k_prop(1) 1 by simp
      ultimately have component_increase: 
      "connected_component (to_graph (\<FF>_imp state)) v 
             \<subset> connected_component (to_graph (\<FF>_imp (((orlins_one_step_check ^^ j)) pseudo_initial))) v"
        by simp
      have not_in_j:"connected_component (to_graph (\<FF>_imp state)) v 
                      \<in> comps \<V> (to_graph (\<FF>_imp ((orlins_one_step_check ^^ j) pseudo_initial))) \<Longrightarrow> False"
      proof(goal_cases)
        case 1
        then obtain w where "w \<in> \<V>" "connected_component (to_graph (\<FF>_imp state)) v = 
               connected_component (to_graph (\<FF>_imp ((orlins_one_step_check ^^ j) pseudo_initial))) w" 
          by(auto simp add: comps_def)
        moreover hence "connected_component (to_graph (\<FF>_imp ((orlins_one_step_check ^^ j) pseudo_initial))) w =
                       connected_component (to_graph (\<FF>_imp ((orlins_one_step_check ^^ j) pseudo_initial))) v"
          by (metis connected_components_member_eq in_connected_componentI2)
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
    obtain x where x_prop:"important stateX x" "X = connected_component (to_graph (\<FF>_imp stateX)) x"
      using get_k_and_l(1) k_and_l_i(1)
      by(auto simp add: stateX_def comps_with_imp_def Let_def)
    define stateY where "stateY = (orlins_one_step_check ^^ l) pseudo_initial"
    obtain y where y_prop:"important stateY y" "Y = connected_component (to_graph (\<FF>_imp stateY)) y"
      using get_k_and_l(2) k_and_l_i(2)
      by(auto simp add: stateY_def comps_with_imp_def Let_def)
    have aux_invar_stateX: "aux_invar stateX"
      using aux_invar_pres[of k] stateX_def by simp
    have invar_gamma_stateX: "invar_gamma stateX"
      using invar_gamma_pres[of k] stateX_def by simp
    have invar_non_zero_b_stateX:"invar_non_zero_b stateX"
      using invar_non_zero_b_pres[of k] stateX_def k_and_l_i(1) by simp
    have aux_invar_stateY: "aux_invar stateY"
      using aux_invar_pres[of l] stateY_def by simp
    have invar_gamma_stateY: "invar_gamma stateY"
      using invar_gamma_pres[of l] stateY_def by simp
    have invar_non_zero_b_stateY:"invar_non_zero_b stateY"
      using invar_non_zero_b_pres[of l] stateY_def k_and_l_i(2) by simp
    have "\<not> X \<subseteq> Y \<Longrightarrow> \<not> Y \<subseteq> X \<Longrightarrow> \<not> X \<inter> Y = {} \<Longrightarrow> False"
      proof(goal_cases)
        case 1
        note X_Y_props = this
        have comparison_cases:"((a::nat) < b \<Longrightarrow> P) \<Longrightarrow> ((a = b) \<Longrightarrow> P) \<Longrightarrow> (a > b \<Longrightarrow> P) \<Longrightarrow> P" for a b P  by force
        show ?case 
        proof(cases rule: comparison_cases[of k l])
          case 1
          have stateY_from_stateX:"stateY = (orlins_one_step_check ^^ (l - k)) stateX"
            unfolding stateX_def stateY_def
            apply(subst sym[OF o_apply[of "orlins_one_step_check ^^ _" "orlins_one_step_check ^^ _"]], 
                  subst sym[OF funpow_add])
            using 1 by simp
          have forest_subs:"to_graph (\<FF>_imp stateX) \<subseteq> to_graph (\<FF>_imp stateY)"
            using stateY_from_stateX  aux_invar_stateX invar_gamma_stateX invar_non_zero_b_stateX 
            by (intro orlins_some_steps_forest_increase[of _ "l - k"])
          define X' where "X' = connected_component (to_graph (\<FF>_imp stateY)) x"
          have X_subs_X':"X \<subseteq> X'"
            by(auto intro!: con_comp_subset[OF forest_subs] simp add: x_prop(2) X'_def)
          have "X' \<inter> Y \<noteq> {}"
            using X_Y_props(3) X_subs_X' by blast
          hence "X' = Y"
            using X'_def y_prop(2) 
            by (metis connected_components_member_eq disjoint_iff)
          moreover have "X' \<noteq> Y"
            using X_Y_props X_subs_X' by simp
          ultimately show ?thesis by simp
        next
          case 2
          have forest_same:"to_graph (\<FF>_imp stateX) = to_graph (\<FF>_imp stateY)"
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
            unfolding stateX_def stateY_def
            apply(subst sym[OF o_apply[of "orlins_one_step_check ^^ _" "orlins_one_step_check ^^ _"]], 
                  subst sym[OF funpow_add])
            using 3 by simp
          have forest_subs:"to_graph (\<FF>_imp stateY) \<subseteq> to_graph (\<FF>_imp stateX)"
            using stateX_from_stateY  aux_invar_stateY invar_gamma_stateY invar_non_zero_b_stateY 
            by (intro orlins_some_steps_forest_increase[of _ "k - l"])
          define Y' where "Y' = connected_component (to_graph (\<FF>_imp stateX)) y"
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
     obtain x where x_prop:"important stateX x" "X = connected_component (to_graph (\<FF>_imp stateX)) x"
       using get_k(1) k_i(1)
       by(auto simp add: stateX_def comps_with_imp_def Let_def)
     hence "x \<in> \<V>"
      by(simp add: important_def)
     moreover have aux_invar_stateX: "aux_invar stateX"
       using aux_invar_pres[of k] stateX_def by simp
     ultimately show ?case 
       by(auto simp add:  aux_invar_def invar_aux10_def x_prop(2) connected_component_def)
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
    apply simp
    unfolding Imps_def Let_def
    apply(subst sym[OF send_flow_sim])
    apply(rule sum_up_same_cong[OF _ _ refl, of "Suc 0" "Suc i", simplified sum_indes_less_suc_conv])
    apply(subst sym[OF funpow_swap1])
    apply(subst sym[OF o_apply[of orlins_one_step_check "orlins_one_step_check ^^ (_ - Suc 0)"]])
    apply(subst sym[OF funpow.simps(2)])
    by auto
  also have " ... = 
         (\<Sum> j \<in> {1..i}. (card (Imps j))) +  (card (Imps 0))"
    unfolding Imps_def
    using pseudo_initial_important by (simp, presburger)
  also have "... = (\<Sum> j \<in> {0..i}. (card (Imps j)))"
    by (metis Suc_eq_plus1 add.commute less_eq_nat.simps(1) plus_nat.add_0 sum.atLeast_Suc_atMost)
  also have "... = (\<Sum> j \<in> {0..i}. (card (comps_with_imp j)))"
    using card_Imps_card_compst_with_ip_same by simp
  also have "... = (\<Sum> j \<in> {0..<Suc i}. (card (comps_with_imp j)))"
    by (metis sum_indes_less_suc_conv)
  also have "... \<le> (\<l> + 1) * card \<S>"
    using finite_S  comps_with_imp_subs_S  component_lifetime  beyonf_i_empty 
    by (rule sum_cards_with_life_time[of \<S> comps_with_imp "\<l>" i])
  also have "... \<le> (\<l> + 1) * (2*N - 1)"
    using card_S_laminar_bound  mult_le_mono2 by blast
  finally show ?thesis by simp
qed

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
      apply(rule IH(2))
      using 1 by auto
  next
    case (2 aa ba ab bb e)
    show ?case 
      apply(rule IH(2))
      using 2 by auto
  qed
qed

lemma orlins_time_dom_base_extract: 
"orlins_time_dom (t + s, state) \<Longrightarrow> 
(orlins_time (t + s) state) = (t +++ (orlins_time s state))"
proof(induction  arbitrary: s t rule: orlins_time.pinduct)
  case (1 t state)
  note IH = this
  show ?case
    apply(subst orlins_time.psimps)
    using orlins_time_dom_base_shift IH(1) apply simp
    apply(subst (2) orlins_time.psimps)
    using orlins_time_dom_base_shift IH(1) 
    by(auto simp add: IH(2)[OF _ _ refl refl refl refl refl refl] add_fst_def Let_def)
qed

lemma succ_fail_term_same_with_time_dom:
"compow (Suc k) orlins_one_step_time_check (tt, state) = (tfin, state') \<Longrightarrow>
       return state' = success \<or> return state' = failure \<Longrightarrow> 
         orlins_time_dom (tt, state)"
proof(induction k arbitrary: state tt)
  case 0
  have A: "orlins_time_dom (tt, state)"
  proof(rule orlins_time.domintros, goal_cases)
    case (1 a b aa ba)
    have "(prod.fst (maintain_forest_time
         (state\<lparr>current_\<gamma> := min (current_\<gamma> state / 2) (Max {\<bar>balance state v\<bar> |v. v \<in> \<V>})\<rparr>)) + tt + t\<^sub>O\<^sub>C +  t\<^sub>O\<^sub>B) +++
         send_flow_time (prod.snd (maintain_forest_time
         (state\<lparr>current_\<gamma> := min (current_\<gamma> state / 2) (Max {\<bar>balance state v\<bar> |v. v \<in> \<V>})\<rparr>))) =
          (tfin, state')"
      using 0[simplified] 1
      by(auto simp add: orlins_one_step_time_def orlins_one_step_time_check.simps Let_def add_fst_def)
    thus ?case 
      using 0(2)
      by(auto intro: orlins_time.domintros simp add: add_fst_def)
  next
    case (2 a b aa ba e)
    have "(prod.fst (maintain_forest_time
         (state\<lparr>current_\<gamma> := current_\<gamma> state / 2 \<rparr>)) + tt + t\<^sub>O\<^sub>C +  t\<^sub>O\<^sub>B) +++
         send_flow_time (prod.snd (maintain_forest_time
         (state\<lparr>current_\<gamma> := current_\<gamma> state / 2 \<rparr>))) =
          (tfin, state')"
      using 0[simplified] 2
      by(auto simp add: orlins_one_step_time_def  Let_def add_fst_def)
    thus ?case 
      using 0(2)
       by(auto intro: orlins_time.domintros simp add: add_fst_def)
   qed
   thus ?case  by simp
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
        apply(subst (2) sym[OF prod.collapse], subst (7) sym[OF prod.collapse])
        using succ_fail_not_changes_time[of"prod.fst (orlins_one_step_time_check (tt, state))" 
                                            "prod.snd (orlins_one_step_time_check (tt, state))" "Suc k"] 
        by simp
      have A:"orlins_time_dom (tt, state)"
      proof(rule orlins_time.domintros, goal_cases)
        case (1 a b aa ba)
        then show ?case 
           using success(1) 
           by(auto intro: orlins_time.domintros simp add: orlins_one_step_time_def Let_def orlins_one_step_time_check.simps add_fst_def)
      next
        case (2 a b aa ba e)
        then show ?case
          using 2 success
          unfolding orlins_one_step_time_def Let_def orlins_one_step_time_check.simps add_fst_def
          by(subst (asm) if_not_P, auto intro: orlins_time.domintros)       
      qed
      then show ?thesis by simp
    next
      case failure
      note Failure = this
     hence same_state:"(orlins_one_step_time_check ^^ Suc k) (orlins_one_step_time_check (tt, state)) = 
                       orlins_one_step_time_check (tt, state)"
        apply(subst (2) sym[OF prod.collapse], subst (7) sym[OF prod.collapse])
        using succ_fail_not_changes_time[of"prod.fst (orlins_one_step_time_check (tt, state))" 
                                            "prod.snd (orlins_one_step_time_check (tt, state))" "Suc k"] 
        by simp
      have A:"orlins_time_dom (tt, state)"
      proof(rule orlins_time.domintros, goal_cases)
        case 1
        then show ?case 
           using failure(1) 1
           by(auto intro: orlins_time.domintros simp add: orlins_one_step_time_def Let_def orlins_one_step_time_check.simps add_fst_def)
      next
        case (2 a b)
        then show ?case
          using 2 failure
          unfolding orlins_one_step_time_def Let_def orlins_one_step_time_check.simps add_fst_def
          by(subst (asm) if_not_P, auto intro: orlins_time.domintros)     
      qed
      then show ?thesis by simp
    next
      case notyetterm
      hence "return state = notyetterm" 
        unfolding orlins_one_step_time_check.simps[of tt  state] add_fst_def 
        by (smt (verit, ccfv_SIG) return.exhaust snd_conv)
      hence 11:"(orlins_one_step_time_check ^^  k) 
                 (orlins_one_step_time_check (orlins_one_step_time_check (tt , state))) = 
             (orlins_one_step_time_check ^^  k) 
                 (orlins_one_step_time_check (tt + prod.fst (orlins_one_step_time  state),
                 prod.snd (orlins_one_step_time state)))"
        using orlins_one_step_time_check.simps[of tt  state]
        by(auto simp add: add_fst_def) 
      have 12:"orlins_time_dom (tt + prod.fst (orlins_one_step_time  state) , prod.snd (orlins_one_step_time state))"                             
        apply(rule  Suc(1))
        apply(subst funpow_Suc_right)
        using 11 Suc(2)[simplified funpow_Suc_right o_apply]  Suc(3) 
        by auto
      have A:"orlins_time_dom (tt,state)"
      proof(rule orlins_time.domintros, goal_cases)
        case (1 aa ba ab bb)
        then show ?case 
          using orlins_time_dom_base_shift[OF 12(1)] 
          by(simp add: orlins_one_step_time_def Let_def)
      next
        case (2 aa ba ab bb e)
        hence snd_same:"prod.snd (orlins_one_step_time state) =
              prod.snd (send_flow_time (prod.snd (maintain_forest_time (state\<lparr>current_\<gamma> := current_\<gamma> state / 2\<rparr>))))"
          by(auto simp add: orlins_one_step_time_def Let_def)
        show ?case 
          using sym[OF snd_same]  orlins_time_dom_base_shift[OF 12(1)] 
          by auto
      qed
      then show ?thesis by simp
    qed
  qed

lemma succ_fail_term_same_with_time:
  assumes "compow (Suc k) orlins_one_step_time_check (tt, state) = (tfin, state')"
          "return state' = success \<or> return state' = failure" 
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
        show ?case
          apply(insert 1)
         by((subst add_fst_def Let_def)+,(subst orlins_time.psimps), 
              (subst add_fst_def Let_def | subst (asm) add_fst_def Let_def )+,
              rule orlins_time.domintros[of _ tt], simp, simp,
               (subst (2) orlins_time.psimps),
               ((subst add_fst_def Let_def | subst (asm) add_fst_def Let_def )+,
                 rule orlins_time.domintros[of _ tt], simp, simp), 
                ((subst add_fst_def Let_def | subst (asm) add_fst_def Let_def )+, (auto)[]))
      next
        case (2 nat)
        show ?case 
        apply(insert 2, (subst Let_def)+, subst sym[OF orlins_time_dom_base_extract])         
          by(fastforce intro!: succ_fail_term_same_with_time_dom[of "k - 1" _ _ tfin state'] IH(2)[where k42 = "k-1"] 
                     simp add: algebra_simps  Let_def add_fst_def sym[OF orlins_one_step_time_def[simplified Let_def]])+
      qed
    qed simp
  qed simp
qed simp
qed simp
    qed (auto simp add: terminated_mono[of 0, simplified])
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
  have a:"prod.fst (send_flow_time initial) = (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f )"
    using True by (subst send_flow_time.psimps)(auto intro: send_flow_time.domintros simp add: add_fst_def initial_def)
  have bb:"return (send_flow initial) = success"
    using True by (subst send_flow.psimps)(auto intro: send_flow.domintros simp add: add_fst_def initial_def)
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
  have send_flow_sim:"orlins_one_step_check pseudo_initial = send_flow initial"
    unfolding orlins_one_step_check_def pseudo_initial_def initial_def orlins_one_step_def Let_def 
    using Max_b_gtr_0 N_def cardV_0 set_get(1-3)[OF invar_filter[OF \<E>_impl_meaning(2)]]
    by(subst maintain_forest_simps(2), intro maintain_forest_ret_condI)
      (fastforce simp add: maintain_forest_simps(2) mult_less_0_iff)+
  have pseudo_initial_important:
       "important pseudo_initial v \<longleftrightarrow> important_initial initial v" for v
    by(simp add: pseudo_initial_def important_def important_initial_def initial_def new_\<gamma>_def)
  have aux_invar_pseudo_initial: "aux_invar pseudo_initial"
   using aux_invar_gamma[OF aux_invar_initial] by (simp add: pseudo_initial_def)
  have invar_gamma_pseudo_initial: "invar_gamma pseudo_initial"
    using invar_gamma_initial False by(simp add: invar_gamma_def pseudo_initial_def)
  have invar_non_zero_b_pseudo_initial: "invar_non_zero_b pseudo_initial"
    using False by(simp add: pseudo_initial_def initial_def invar_non_zero_b_def)
  have invar_integral_pseudo_initial: "invar_integral pseudo_initial"
    by(simp add: invar_integral_def pseudo_initial_def initial_def)
  have invar_forest_pseudo_initial: "invar_forest pseudo_initial"
    using empty_forest_axioms vset.set.set_isin vset.set.invar_empty vset.set.set_empty
    by(simp add: invar_forest_def pseudo_initial_def initial_def to_rdgs_def to_graph_def)
  have orlins_entry_pseudo_initial: "orlins_entry  pseudo_initial"
    using  \<epsilon>_axiom Max.coboundedI[of "{\<bar>\<b> v\<bar> |v. v \<in> \<V>}"] \<V>_finite Max_b_gtr_0 
    by (auto intro: order.trans[OF Max.coboundedI[of "{\<bar>\<b> v\<bar> |v. v \<in> \<V>}"]] simp add:  orlins_entry_def pseudo_initial_def initial_def )
  have invar_isOptflow_pseudo_initial: "invar_isOptflow pseudo_initial"
    using invar_isOptflow_initial 
    by(simp add: pseudo_initial_def invar_isOptflow_def)
  have card_F_pseudo_initial: "N = card (comps \<V> (to_graph (\<FF>_imp pseudo_initial)))"
    using not_reachable_empt empty_forest_axioms
    by (fastforce intro: bij_betw_same_card[of "\<lambda> x. {x}"] 
               simp add: bij_betw_def inj_on_def vset.set.set_isin vset.set.invar_empty 
                         vset.set.set_empty pseudo_initial_def comps_def initial_def connected_component_def N_def to_graph_def)
  have "return ((orlins_one_step_check ^^ (N * (\<l> + \<k> + 2))) pseudo_initial) \<noteq> notyetterm"
    using \<l>_def \<k>_def invar_gamma_pseudo_initial aux_invar_pseudo_initial
          invar_non_zero_b_pseudo_initial invar_integral_pseudo_initial invar_forest_pseudo_initial
          orlins_entry_pseudo_initial invar_isOptflow_pseudo_initial
          card_F_pseudo_initial empty_forest_axioms to_graph_def
    by (intro finally_termination)
  hence termy:"return ((orlins_one_step_check ^^ (N * (\<l> + \<k> + 2) - 1)) (send_flow initial)) \<noteq> notyetterm"
    apply(subst sym[OF send_flow_sim])
    apply(subst  sym[OF o_apply[of "_ ^^ _" "orlins_one_step_check"]])
    apply(subst sym[OF funpow_Suc_right])
    using N_gtr_0 by simp
  obtain I where I_prop:"return ((orlins_one_step_check ^^ I) (send_flow initial)) \<noteq> notyetterm "
          "\<not> (\<exists> J < I. return ((orlins_one_step_check ^^ J) (send_flow initial)) \<noteq> notyetterm)"
    by(rule get_least, rule termy, simp) 
  have switch_timed_and_untimed:"(prod.snd ((orlins_one_step_time_check ^^ Ii) (t\<^sub>O\<^sub>C, send_flow initial))) =
         (orlins_one_step_check ^^ Ii)  (send_flow initial)" for Ii
    apply(cases I)
    subgoal
      apply(subst notyetterm_no_change)
      using I_prop(1) apply simp
      apply(subst (2) sym[OF snd_conv[of t\<^sub>O\<^sub>C "send_flow _"]], subst succ_fail_not_changes_time)
      using I_prop(1)  return.exhaust by auto
      using send_flow_invar_aux_pres[OF send_flow_termination] aux_invar_initial
            send_flow_invar_gamma_pres[OF send_flow_termination]  invar_gamma_initial[OF False]  I_prop(2) 
      by (auto intro!: same_as_without_time remaining_balance_after_send_flow[OF send_flow_termination refl])
    have I_bound: " I \<le> (N * (\<l> + \<k> + 2) - 1)"
      using I_prop termy  not_less by blast
  have I_prop': "return (prod.snd ((orlins_one_step_time_check ^^ I) (t\<^sub>O\<^sub>C, send_flow initial))) \<noteq> notyetterm "
          "\<not> (\<exists> J < I. return (prod.snd ((orlins_one_step_time_check ^^ J) (t\<^sub>O\<^sub>C, send_flow initial))) \<noteq> notyetterm)"
    using switch_timed_and_untimed I_prop by auto
  have I_prop'': "return (prod.snd ((orlins_one_step_time_check ^^ I) (send_flow_time initial))) \<noteq> notyetterm "
          "\<not> (\<exists> J < I. return (prod.snd ((orlins_one_step_time_check ^^ J) (send_flow_time initial))) \<noteq> notyetterm)"
    using I_prop' equal_results_B[OF send_flow_termination[OF invar_gamma_initial[OF False]]] 
          runtime_add_constant[of _ t\<^sub>O\<^sub>C 0 "send_flow initial"] 
          runtime_add_constant[of _ "prod.fst (send_flow_time initial)" 0 "send_flow initial"]
    by(auto simp add: add_fst_def)
  have to_time:"(orlins_one_step_time_check ^^ I) (t\<^sub>O\<^sub>C, send_flow initial) = 
        orlins_time t\<^sub>O\<^sub>C (send_flow initial)"
    apply(cases I)
    subgoal
      using I_prop' return.exhaust 
      by (subst orlins_time.psimps | auto intro: orlins_time.domintros)+   
    using  I_prop'(1) return.exhaust 
    by (subst  succ_fail_term_same_with_time[of _ t\<^sub>O\<^sub>C "send_flow initial"] | 
                   auto intro: sym[OF prod.collapse])+
  have to_usual: "(orlins_one_step_check ^^ I)  (send_flow initial) =
                  orlins (send_flow initial)"
    apply(cases I)
    subgoal
      using I_prop return.exhaust 
      by (subst orlins.psimps | auto intro: orlins.domintros)+   
    using  I_prop(1) return.exhaust 
    by (subst  succ_fail_term_same[of _ "send_flow initial"] | 
                   auto intro: sym[OF prod.collapse])+
  have time_swap:"prod.fst (send_flow_time initial) +++ (orlins_one_step_time_check ^^ I) (t\<^sub>O\<^sub>C, send_flow initial) =
       t\<^sub>O\<^sub>C +++  (orlins_one_step_time_check ^^ I) (send_flow_time initial)"
    apply(subst sym[OF runtime_add_constant], subst (6)sym[OF prod.collapse], subst sym[OF runtime_add_constant])
    apply(rule arg_cong[of "(_, _)"])
    using equal_results_B[OF send_flow_termination[OF invar_gamma_initial[OF False]]]
    by auto
  have number_of_comps_diff: "card (comps \<V> (to_graph (\<FF>_imp initial))) -
    card (comps \<V> (to_graph (\<FF>_imp (prod.snd ((orlins_one_step_time_check ^^ I) (send_flow_time initial)))))) \<le> N - 1" 
    using \<V>_finite V_non_empt 
    by (auto simp add: Suc_leI card_gt_0_iff diff_le_mono2 comps_def pseudo_initial_def card_F_pseudo_initial )
  show ?thesis
  proof(rule, goal_cases)
    case 1
    have "prod.fst final + prod.fst (send_flow_time initial) = 
          t\<^sub>O\<^sub>C  + prod.fst ((orlins_one_step_time_check ^^ I) (send_flow_time initial))"
      using time_swap 
      by (simp add:  add_fst_def assms sym[OF to_time])
    also have "... \<le>  t\<^sub>O\<^sub>C + ((card (comps \<V> (to_graph (\<FF>_imp initial))) -
    card (comps \<V> (to_graph (\<FF>_imp (prod.snd ((orlins_one_step_time_check ^^ I) (send_flow_time initial))))))) *
   (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
   I * (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f + t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>O\<^sub>C + t\<^sub>O\<^sub>B) +
   ((\<Sum>j = 1..I.
        let state' = (orlins_one_step_check ^^ (j - 1)) (local.send_flow initial) in card {v. important state' v}) +
    card {v. important_initial initial v}) *
   (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +
   (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f))"
      using I_prop'' False 
      by (fastforce intro!: add_mono running_time_sum_from_init[OF refl, of I])
    also have "... \<le> t\<^sub>O\<^sub>C + ((card (comps \<V> (to_graph (\<FF>_imp initial))) -
    card (comps \<V> (to_graph (\<FF>_imp (prod.snd ((orlins_one_step_time_check ^^ I) (send_flow_time initial))))))) *
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
