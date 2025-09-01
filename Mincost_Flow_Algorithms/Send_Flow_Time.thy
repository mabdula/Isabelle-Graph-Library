section \<open>Formalisation of Running Time of Ordinary Augmentations (Send-Flow)\<close>

theory Send_Flow_Time
  imports Send_Flow 
begin

locale send_flow_time =
send_flow_reasoning where fst = fst for fst::"'edge_type \<Rightarrow> 'a"+
fixes t\<^sub>B\<^sub>C::nat and t\<^sub>B\<^sub>B::nat and t\<^sub>B\<^sub>u\<^sub>f::nat and t\<^sub>B\<^sub>F::nat
begin

function (domintros) send_flow_time::
"('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state 
\<Rightarrow> nat \<times> ('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state" where
  "send_flow_time state = t\<^sub>B\<^sub>u\<^sub>f +++ 
   (let f = current_flow state;  b = balance state; \<gamma> = current_\<gamma> state
 in (if test_all_vertices_zero_balance state 
     then (t\<^sub>B\<^sub>C +  t\<^sub>B\<^sub>F, state \<lparr> return:=success\<rparr>) 
     else (case get_source state of Some s \<Rightarrow> 
            (case get_source_target_path_a state s of Some (t, P) \<Rightarrow>
                   (let f' = augment_edges_impl f \<gamma> P;
                       b' = move b \<gamma> s t;
                       state' = state \<lparr> current_flow := f', balance := b'\<rparr> in   
                           ((t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B) +++ (send_flow_time state')))          
                  | None \<Rightarrow>  ((t\<^sub>B\<^sub>C +  t\<^sub>B\<^sub>F), state \<lparr> return := infeasible\<rparr>)) 
     | None \<Rightarrow> 
          (case get_target state of Some t \<Rightarrow> 
            (case get_source_target_path_b state t of Some (s, P) \<Rightarrow>
                   (let f' = augment_edges_impl f \<gamma> P;
                       b' = move b \<gamma> s t;
                       state' = state \<lparr> current_flow := f', balance := b'\<rparr> in
                         ((t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B) +++ (send_flow_time state')))                    
                | None \<Rightarrow> ((t\<^sub>B\<^sub>C +  t\<^sub>B\<^sub>F) , state \<lparr> return := infeasible\<rparr>))
          | None \<Rightarrow> ((t\<^sub>B\<^sub>C +  t\<^sub>B\<^sub>F), state \<lparr> return := notyetterm\<rparr>)))))"
  by auto

lemma terminationB_iff:"send_flow_dom state \<longleftrightarrow> send_flow_time_dom state"
proof(rule, goal_cases)
  case 1
  show ?case
  proof(induction  rule: send_flow.pinduct[OF 1])
    case (1 state)
    note IH=this
    show ?case
      by(rule send_flow_time.domintros, fastforce intro: IH(2), rule IH(3), auto)
  qed
next
  case 2
  show ?case 
  proof(induction  rule: send_flow_time.pinduct[OF 2])
    case (1 state)
    note IH=this
    show ?case
      by(rule send_flow.domintros, fastforce intro: IH(2), rule IH(3), auto)
  qed
qed

lemma equal_results_B: 
  assumes "send_flow_dom state" 
  shows "send_flow state = prod.snd (send_flow_time state)"
proof(induction rule: send_flow.pinduct[OF assms])
  case (1 state)
  note IH=this
  hence time_dom: "send_flow_time_dom state"
    using terminationB_iff[of state] by simp
  show ?case 
  proof(subst send_flow.psimps[OF IH(1)], subst send_flow_time.psimps[OF time_dom], subst Let_def, 
        subst Let_def, subst Let_def, goal_cases)
    case 1
    show ?case 
    proof(subst (7) Let_def, subst (7) Let_def, subst (7) Let_def, subst add_fst_def,
          subst snd_conv, subst if_distrib[of prod.snd],
          rule if_cong[OF refl], goal_cases)
      case 2
      show ?case
      proof(insert 2, subst option.case_distrib[of prod.snd], rule option.case_cong[OF refl],
            goal_cases)
      case 1
      thus ?case 
        by(auto simp add: option.case_distrib[of prod.snd]  add_fst_snd_same
                     intro!: option.case_cong IH(2))
   next
     case (2 s)
     thus ?case
       by(auto simp add: option.case_distrib[of prod.snd] add_fst_snd_same 
                    intro!: option.case_cong IH(3))
  qed
 qed simp
qed
qed

definition "send_flow_time_succ_upd state = (let
                    f = current_flow state;
                    b = balance state;
                    \<gamma> = current_\<gamma> state
 in  (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f +  t\<^sub>B\<^sub>F, state \<lparr> return:=success\<rparr>))"

lemma send_flow_time_succ_upd_changes: 
"\<FF> (prod.snd (send_flow_time_succ_upd state)) = \<FF> state"
"conv_to_rdg (prod.snd(send_flow_time_succ_upd state)) = conv_to_rdg state"
"actives (prod.snd (send_flow_time_succ_upd state)) = actives state"
"current_\<gamma> (prod.snd (send_flow_time_succ_upd state)) = current_\<gamma>  state"
"representative (prod.snd (send_flow_time_succ_upd state)) = representative state"
"\<F> (prod.snd (send_flow_time_succ_upd state)) = \<F> state"
  by (auto simp add: \<F>_def send_flow_time_succ_upd_def Let_def)

definition "send_flow_time_call1_upd state = 
(let f = current_flow state;
     b = balance state;
     \<gamma> = current_\<gamma> state;
     s = the (get_source state);
     (t, P ) = the (get_source_target_path_a state s);
     f' = augment_edges_impl f \<gamma> P;
     b' = move b \<gamma> s t 
 in  (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f , state \<lparr> current_flow := f', balance := b'\<rparr>))"

value "t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f +  t\<^sub>B\<^sub>F"

lemma send_flow_call1_upd_changes: 
"\<FF> (send_flow_call1_upd state) = \<FF> state"
"conv_to_rdg (send_flow_call1_upd state) = conv_to_rdg state"
"actives (send_flow_call1_upd state) = actives state"
"current_\<gamma> (send_flow_call1_upd state) = current_\<gamma>  state"
"representative (send_flow_call1_upd state) = representative state"
"\<F> (send_flow_call1_upd state) = \<F> state"
  by (auto simp add: send_flow_call1_upd_def Let_def \<F>_def split: prod.split)

definition "send_flow_time_fail_upd state = (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f +  t\<^sub>B\<^sub>F, state \<lparr> return :=infeasible \<rparr>)"

lemma send_flow_time_fail_upd_changes: 
"\<FF> (prod.snd (send_flow_time_fail_upd state)) = \<FF> state"
"conv_to_rdg (prod.snd (send_flow_time_fail_upd state)) = conv_to_rdg state"
"actives (prod.snd (send_flow_time_fail_upd state)) = actives state"
"current_\<gamma> (prod.snd (send_flow_time_fail_upd state)) = current_\<gamma>  state"
"representative (prod.snd (send_flow_time_fail_upd state)) = representative state"
"\<F> (prod.snd (send_flow_time_fail_upd state)) = \<F> state"
  by(auto simp add: send_flow_time_fail_upd_def Let_def \<F>_def split: prod.split)

definition "send_flow_time_call2_upd state= (let
                    f = current_flow state;
                    b = balance state;
                    \<gamma> = current_\<gamma> state;
                    t = the (get_target state);
                    (s, P) =  the (get_source_target_path_b state t);
                    f' = augment_edges_impl f \<gamma> P;
                    b' = move b \<gamma> s t 
in (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f, state \<lparr> current_flow := f', balance := b'\<rparr>))"

lemma send_flow_time_call2_upd_changes: 
"\<FF> (prod.snd (send_flow_time_call2_upd state)) = \<FF> state"
"conv_to_rdg (prod.snd (send_flow_time_call2_upd state)) = conv_to_rdg state"
"actives (prod.snd (send_flow_time_call2_upd state)) = actives state"
"current_\<gamma> (prod.snd (send_flow_time_call2_upd state)) = current_\<gamma>  state"
"representative (prod.snd (send_flow_time_call2_upd state)) = representative state"
"\<F> (prod.snd (send_flow_time_call2_upd state)) = \<F> state"
  by (auto simp add: send_flow_time_call2_upd_def Let_def \<F>_def split: prod.splits)

definition "send_flow_time_cont_upd state = (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f +  t\<^sub>B\<^sub>F, state \<lparr> return := notyetterm\<rparr>)"

lemma send_flow_time_cont_upd_changes: 
"\<FF> (prod.snd (send_flow_time_cont_upd state)) = \<FF> state"
"conv_to_rdg (prod.snd (send_flow_time_cont_upd state)) = conv_to_rdg state"
"actives (prod.snd (send_flow_time_cont_upd state)) = actives state"
"current_\<gamma> (prod.snd (send_flow_time_cont_upd state)) = current_\<gamma>  state"
"representative (prod.snd (send_flow_time_cont_upd state)) = representative state"
"\<F> (prod.snd (send_flow_time_cont_upd state)) = \<F> state"
 by(auto simp add: send_flow_time_cont_upd_def Let_def \<F>_def)

lemma send_flow_time_simps: 
  assumes "send_flow_time_dom state"
  shows   "send_flow_succ_cond state \<Longrightarrow> send_flow_time state = (send_flow_time_succ_upd state)"
          "send_flow_cont_cond state \<Longrightarrow> send_flow_time state = (send_flow_time_cont_upd state)"
          "send_flow_fail1_cond state \<Longrightarrow> send_flow_time state = (send_flow_time_fail_upd state)"
          "send_flow_fail2_cond state \<Longrightarrow> send_flow_time state = (send_flow_time_fail_upd state)"
          "send_flow_call1_cond state \<Longrightarrow> send_flow_time state = (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +++ send_flow_time (send_flow_call1_upd state)"
          "send_flow_call2_cond state \<Longrightarrow> send_flow_time state = (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +++ send_flow_time (send_flow_call2_upd state)"
proof-
  show "send_flow_succ_cond state \<Longrightarrow> send_flow_time state = send_flow_time_succ_upd state"
    using  send_flow_time.psimps[OF assms]
    unfolding send_flow_time_succ_upd_def Let_def add_fst_def
    by (auto elim: send_flow_succ_condE)
  show "send_flow_cont_cond state \<Longrightarrow> send_flow_time state = send_flow_time_cont_upd state"
    apply(subst send_flow_time.psimps, simp add: assms)
    apply(rule send_flow_cont_condE, simp)
    unfolding send_flow_time_cont_upd_def  Let_def add_fst_def by simp
  show "send_flow_fail1_cond state \<Longrightarrow> send_flow_time state = send_flow_time_fail_upd state"
    apply(subst send_flow_time.psimps, simp add: assms)
    apply(rule send_flow_fail1_condE, simp)
    unfolding send_flow_time_fail_upd_def  Let_def add_fst_def by auto
  show "send_flow_fail2_cond state \<Longrightarrow> send_flow_time state = send_flow_time_fail_upd state"
    apply(subst send_flow_time.psimps, simp add: assms)
    apply(rule send_flow_fail2_condE, simp)
    unfolding send_flow_time_fail_upd_def  Let_def add_fst_def by auto
  show " send_flow_call1_cond state \<Longrightarrow> send_flow_time state = (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +++ send_flow_time (send_flow_call1_upd state)"
  proof- (*Problem with automation*)
    assume asm:"send_flow_call1_cond state"
    show "send_flow_time state = (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +++ send_flow_time (send_flow_call1_upd state)"
    proof(rule send_flow_call1_condE[OF asm], goal_cases)
      case (1 f b \<gamma> s t P f' b' state')
      thus ?case  
        apply(subst send_flow_time.psimps[OF assms])
        unfolding send_flow_call1_upd_def Let_def add_fst_def
        by auto
     qed
   qed
   show " send_flow_call2_cond state \<Longrightarrow> send_flow_time state = (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +++ send_flow_time (send_flow_call2_upd state)"
   proof- (*Problem with automation*)
    assume asm:"send_flow_call2_cond state"
    show "send_flow_time state = (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +++ send_flow_time (send_flow_call2_upd state)"
    proof(rule send_flow_call2_condE[OF asm], goal_cases)
      case (1 f b \<gamma> s t P f' b' state')
      thus ?case  
       using send_flow_time.psimps assms
        unfolding send_flow_call2_upd_def Let_def add_fst_def
         by (auto elim: send_flow_call2_condE)
     qed
   qed
 qed   

lemma send_flow_call1_cond_Phi: 
  assumes "send_flow_call1_cond state" "invar_gamma state" 
          "implementation_invar state"
  shows   "\<Phi> state > 0"
proof(rule send_flow_call1_condE[OF assms(1)],  goal_cases)
  case (1 f b \<gamma> s t P f' b' state')
  have s_exists: "(1 - \<epsilon>) * \<gamma> < abstract_bal_map b s"  "s \<in> \<V>"
    using if_send_flow_call1_cond_basic[OF assms(1,3) 1(5)[symmetric]]
    by(auto simp add: 1)
  show ?case 
    unfolding \<Phi>_def
    apply(rule ordered_comm_monoid_add_class.sum_pos2[OF \<V>_finite s_exists(2)])
    using assms(2) s_exists(1)
     by(auto simp add: pos_less_divide_eq 1 elim!: invar_gammaE)
      (smt (verit, best) \<epsilon>_axiom(1) divide_nonneg_pos zero_le_ceiling)
 qed

lemma send_flow_call2_cond_Phi: 
  assumes "send_flow_call2_cond state" "invar_gamma state" 
          "implementation_invar state"
  shows   "\<Phi> state > 0"
proof(rule send_flow_call2_condE[OF assms(1)],  goal_cases)
  case (1 f b \<gamma> t s P f' b' state')
  have t_exists: " - (1 - \<epsilon>) * \<gamma> > abstract_bal_map b t"  "t \<in> \<V>"
    using if_send_flow_call2_cond_basic[OF assms(1,3) 1(6)[symmetric]]
    by(auto simp add: 1)
  show ?case 
    unfolding \<Phi>_def
    apply(rule ordered_comm_monoid_add_class.sum_pos2[OF \<V>_finite t_exists(2)])
    using assms(2) t_exists(1)
    by(auto simp add: pos_less_divide_eq 1  elim!: invar_gammaE, argo) 
      (metis \<epsilon>_axiom(1) abs_div_pos abs_ge_zero add_nonneg_pos)
qed

lemma time_boundB: 
  assumes "invar_gamma state"
          "\<phi> = nat (\<Phi> state)"
          "underlying_invars state"
          "implementation_invar state"
          "invar_integral state"
          "invar_isOptflow state"
          "invar_above_6Ngamma state"
  shows   "prod.fst (send_flow_time state) \<le> 
             \<phi> * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) + (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f)"
  using assms
proof(induction \<phi> arbitrary: state rule: less_induct)
  case (less \<phi>)
  hence send_flow_time_dom: "send_flow_time_dom state" 
    using send_flow_term[of state] terminationB_iff[of state] by simp 
  show ?case
  proof(cases rule: send_flow_cases[of state])
    case 1
    thus ?thesis
      by(auto simp add: send_flow_time_simps(2)[OF send_flow_time_dom] send_flow_time_cont_upd_def)
  next
    case 2
    thus ?thesis
      by(auto simp add: send_flow_time_simps(1)[OF send_flow_time_dom] send_flow_time_succ_upd_def)
  next
    case 3
    thus?thesis
      apply(subst send_flow_time_simps(5)[OF send_flow_time_dom], simp)
      unfolding add_fst_def 
      proof(rule order.trans[of _ "t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f + nat (\<Phi> ( (send_flow_call1_upd state))) * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) + (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f)"],
          goal_cases)
       case 1
       thus ?case       
          using send_flow_call1_cond_Phi_decr[OF _ less(2)] less(2-) 
                send_flow_call1_cond_Phi[OF _ less(2)]  invar_gamma_pres_call1[OF less(2)] 
          by(simp, subst (2) sym[OF add.assoc])
            (auto intro!: less(1) invar_aux_pres_call1 send_flow_invar_isOptflow_call1(1,2)
                              send_flow_call1_invar_integral_pres invar_above_6Ngamma_call1_pres
                 dest:  invar_above_6Ngamma_forest_flow_above_gamma invar_above_6Ngamma_pos_flow_F)
    next
      case 2
      thus ?case
      apply simp
      apply(rule order.trans[of _ "t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f + nat (\<Phi> state - 1) * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f)"])
        using  send_flow_call1_cond_Phi_decr[OF 3 less(2,4,5)
                invar_above_6Ngamma_pos_flow_F[OF less(2,8)] less(7)] less(2) 
                send_flow_call1_cond_Phi[OF 3 less(2,5)] 
        by(auto simp add: less(3)) (simp add: mult_eq_if nat_diff_distrib')
  qed
next
  case 4
  thus?thesis
      apply(subst send_flow_time_simps(6)[OF send_flow_time_dom], simp)
      unfolding add_fst_def 
      proof(rule order.trans[of _ "t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f + nat (\<Phi> ( (send_flow_call2_upd state))) * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) + (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f)"],
          goal_cases)
       case 1
       thus ?case        
          using send_flow_call2_cond_Phi_decr[OF _ less(2)] less(2-) 
                send_flow_call2_cond_Phi[OF _ less(2)]  invar_gamma_pres_call2[OF less(2)] 
          by(simp, subst (2) sym[OF add.assoc])
            (auto intro!: less(1) invar_aux_pres_call2 send_flow_invar_isOptflow_call2(1,2)
                              send_flow_call2_invar_integral_pres invar_above_6Ngamma_call2_pres
                 dest:  invar_above_6Ngamma_forest_flow_above_gamma invar_above_6Ngamma_pos_flow_F)
    next
      case 2
      thus ?case
      apply simp
      apply(rule order.trans[of _ "t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f + nat (\<Phi> state - 1) * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f)"])
        using  send_flow_call2_cond_Phi_decr[OF 2 less(2,4,5)
                invar_above_6Ngamma_pos_flow_F[OF less(2,8)] less(7)] less(2) 
                send_flow_call2_cond_Phi[OF 2 less(2,5)] 
        by(auto simp add: less(3)) (simp add: mult_eq_if nat_diff_distrib')
    qed
next
  case 5
  thus ?thesis
    by(auto simp add: send_flow_time_simps(3)[OF send_flow_time_dom] send_flow_time_fail_upd_def)
next
  case 6
  thus ?thesis
      by(auto simp add: send_flow_time_simps(4)[OF send_flow_time_dom] send_flow_time_fail_upd_def)
 qed
qed

end
end