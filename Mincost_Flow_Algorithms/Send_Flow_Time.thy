section \<open>Formalisation of Running Time of Ordinary Augmentations\<close>

theory Send_Flow_Time
  imports Send_Flow
begin

locale send_flow_time =
send_flow_reasoning where fst = fst for fst::"'edge_type \<Rightarrow> 'a"+
fixes t\<^sub>B\<^sub>C::nat and t\<^sub>B\<^sub>B::nat and t\<^sub>B\<^sub>u\<^sub>f::nat and t\<^sub>B\<^sub>F::nat
begin

function (domintros) send_flow_time::"('a, 'c, 'd, 'edge_type) Algo_state \<Rightarrow> nat \<times> ('a, 'c, 'd, 'edge_type) Algo_state" where
  "send_flow_time state = t\<^sub>B\<^sub>u\<^sub>f +++ 
                (let
                    f = current_flow state;
                    b = balance state;
                    \<gamma> = current_\<gamma> state
 in (if \<forall> v \<in> \<V>. b v = 0 then  (t\<^sub>B\<^sub>C +  t\<^sub>B\<^sub>F, state \<lparr> return:=success\<rparr>)
     else if \<exists> s \<in> \<V>. b s > (1 - \<epsilon>) * \<gamma> then 
          ( let s = get_source state
            in (if \<exists> t \<in> \<V>. b t < - \<epsilon> * \<gamma> \<and> resreach f s t then
                   let t = get_target_for_source state s;
                       P = get_source_target_path_a state s t;
                       f' = augment_edges f \<gamma> P;
                       b' = (\<lambda> v. if v = s then b s - \<gamma> 
                                  else if v = t then b t + \<gamma>
                                  else b v);
                       state' = state \<lparr> current_flow := f', balance := b'\<rparr> in   
                           ((t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B) +++ (send_flow_time state'))          
                else
                        ((t\<^sub>B\<^sub>C +  t\<^sub>B\<^sub>F), state \<lparr> return := failure\<rparr>))) 
     else if \<exists> t \<in> \<V>. b t < - (1 -\<epsilon>) * \<gamma> then 
          ( let t = get_target state
            in (if \<exists> s \<in> \<V>.  b s >  \<epsilon> * \<gamma> \<and> resreach f s t then
                   let s = get_source_for_target state t;
                       P = get_source_target_path_b state s t;
                       f' = augment_edges f \<gamma> P;
                       b' = (\<lambda> v. if v = s then b s - \<gamma> 
                                  else if v = t then b t + \<gamma>
                                  else b v);
                       state' = state \<lparr> current_flow := f', balance := b'\<rparr> in
                         ((t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B) +++ (send_flow_time state'))                    
                else
                       ((t\<^sub>B\<^sub>C +  t\<^sub>B\<^sub>F) , state \<lparr> return := failure\<rparr>))
          ) 
      else ((t\<^sub>B\<^sub>C +  t\<^sub>B\<^sub>F), state \<lparr> return := notyetterm\<rparr>)
    ))"
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
    proof(subst (13) Let_def, subst (13) Let_def, subst (13) Let_def, subst add_fst_def,
          subst snd_conv, subst if_distrib[of prod.snd],
          rule if_cong[OF refl], goal_cases)
      case 2
      show ?case
      proof(insert 2, subst if_distrib[of prod.snd], rule if_cong[OF refl], goal_cases)
      case 1
      show ?case 
       apply(insert 1, subst Let_def, subst (6) Let_def, subst if_distrib[of prod.snd], rule if_cong, simp)
       unfolding Let_def
       by(subst add_fst_snd_same, rule  IH(2)[OF]) auto
   next
     case 2
     show ?case
    apply(insert 2, subst if_distrib[of prod.snd], rule if_cong, simp, subst Let_def, subst (6) Let_def)
    apply(subst if_distrib[of prod.snd], rule if_cong, simp)
    unfolding Let_def
    by(subst add_fst_snd_same,rule IH(3)[OF]) auto
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
  unfolding send_flow_time_succ_upd_def Let_def by auto

definition "send_flow_time_call1_upd state = (let
                    f = current_flow state;
                    b = balance state;
                    \<gamma> = current_\<gamma> state;
                    s = get_source state;
                    t = get_target_for_source state s;
                    P = get_source_target_path_a state s t;
                    f' = augment_edges f \<gamma> P;
                    b' = (\<lambda> v. if v = s then b s - \<gamma> 
                                  else if v = t then b t + \<gamma>
                                  else b v) in
                    (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f , state \<lparr> current_flow := f', balance := b'\<rparr>))"

value "t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f +  t\<^sub>B\<^sub>F"

lemma send_flow_call1_upd_changes: 
"\<FF> (send_flow_call1_upd state) = \<FF> state"
"conv_to_rdg (send_flow_call1_upd state) = conv_to_rdg state"
"actives (send_flow_call1_upd state) = actives state"
"current_\<gamma> (send_flow_call1_upd state) = current_\<gamma>  state"
"representative (send_flow_call1_upd state) = representative state"
"\<F> (send_flow_call1_upd state) = \<F> state"
  unfolding send_flow_call1_upd_def Let_def by auto

definition "send_flow_time_fail_upd state = (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f +  t\<^sub>B\<^sub>F, state \<lparr> return :=failure \<rparr>)"

lemma send_flow_time_fail_upd_changes: 
"\<FF> (prod.snd (send_flow_time_fail_upd state)) = \<FF> state"
"conv_to_rdg (prod.snd (send_flow_time_fail_upd state)) = conv_to_rdg state"
"actives (prod.snd (send_flow_time_fail_upd state)) = actives state"
"current_\<gamma> (prod.snd (send_flow_time_fail_upd state)) = current_\<gamma>  state"
"representative (prod.snd (send_flow_time_fail_upd state)) = representative state"
"\<F> (prod.snd (send_flow_time_fail_upd state)) = \<F> state"
  unfolding send_flow_time_fail_upd_def Let_def by auto

definition "send_flow_time_call2_upd state= (let
                    f = current_flow state;
                    b = balance state;
                    \<gamma> = current_\<gamma> state;
                    t = get_target state;
                    s = get_source_for_target state t;
                    P = get_source_target_path_b state s t;
                    f' = augment_edges f \<gamma> P;
                    b' = (\<lambda> v. if v = s then b s - \<gamma> 
                                  else if v = t then b t + \<gamma>
                                  else b v) in
                       (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f, state \<lparr> current_flow := f', balance := b'\<rparr>))"

lemma send_flow_time_call2_upd_changes: 
"\<FF> (prod.snd (send_flow_time_call2_upd state)) = \<FF> state"
"conv_to_rdg (prod.snd (send_flow_time_call2_upd state)) = conv_to_rdg state"
"actives (prod.snd (send_flow_time_call2_upd state)) = actives state"
"current_\<gamma> (prod.snd (send_flow_time_call2_upd state)) = current_\<gamma>  state"
"representative (prod.snd (send_flow_time_call2_upd state)) = representative state"
"\<F> (prod.snd (send_flow_time_call2_upd state)) = \<F> state"
  unfolding send_flow_time_call2_upd_def Let_def by auto

definition "send_flow_time_cont_upd state = (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f +  t\<^sub>B\<^sub>F, state \<lparr> return := notyetterm\<rparr>)"

lemma send_flow_time_cont_upd_changes: 
"\<FF> (prod.snd (send_flow_time_cont_upd state)) = \<FF> state"
"conv_to_rdg (prod.snd (send_flow_time_cont_upd state)) = conv_to_rdg state"
"actives (prod.snd (send_flow_time_cont_upd state)) = actives state"
"current_\<gamma> (prod.snd (send_flow_time_cont_upd state)) = current_\<gamma>  state"
"representative (prod.snd (send_flow_time_cont_upd state)) = representative state"
"\<F> (prod.snd (send_flow_time_cont_upd state)) = \<F> state"
  unfolding send_flow_time_cont_upd_def Let_def by auto

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

lemma send_flow_call1_cond_Phi: "send_flow_call1_cond state \<Longrightarrow> invar_gamma state \<Longrightarrow> \<Phi> state > 0"
proof(rule send_flow_call1_condE[of state],  goal_cases)
  case (2 f b \<gamma> s t P f' b' state')
  note 1 = 2
  show ?case 
  unfolding \<Phi>_def
  proof(insert 1, rule bexE[where P = "\<lambda> s. (1 - \<epsilon>) * \<gamma> < b s" and A = \<V>],  goal_cases)
    case (2 ss)
    show ?case 
    apply(insert 2, rule ordered_comm_monoid_add_class.sum_pos2[OF \<V>_finite, of ss], simp)
    unfolding invar_gamma_def 
     apply (simp add: pos_less_divide_eq)
    by (smt (verit, best) \<epsilon>_axiom(1) divide_nonneg_pos zero_le_ceiling)
qed
qed

lemma send_flow_call2_cond_Phi: "send_flow_call2_cond state \<Longrightarrow> invar_gamma state \<Longrightarrow> \<Phi> state > 0"
proof(rule send_flow_call2_condE[of state], goal_cases)
  case (2 f b \<gamma> t s P f' b' state')
  show ?case
  unfolding \<Phi>_def
  proof(insert 2, rule bexE[where P = "\<lambda> t. - (1 - \<epsilon>) * \<gamma> > b t" and A = \<V>],  goal_cases)
    case (2 tt)
    show ?case 
    apply(insert 2, rule ordered_comm_monoid_add_class.sum_pos2[OF \<V>_finite, of tt], simp)
    unfolding invar_gamma_def
    apply (smt (verit, ccfv_SIG) pos_minus_divide_less_eq zero_less_ceiling)
    by (smt (verit, best) \<epsilon>_axiom(1) divide_nonneg_pos zero_le_ceiling)
qed
qed

lemma time_boundB: 
  assumes "invar_gamma state"
          "\<phi> = nat (\<Phi> state)"
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
          using send_flow_call1_cond_Phi_decr[OF _ less(2)] less(3) 
                send_flow_call1_cond_Phi[OF _ less(2)]  invar_gamma_pres_call1[OF less(2)] 
          by (simp, subst (2) sym[OF add.assoc], auto intro: less(1))
    next
      case 2
      thus ?case
      apply simp
      apply(rule order.trans[of _ "t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f + nat (\<Phi> state - 1) * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f)"])
      using  send_flow_call1_cond_Phi_decr[OF _ less(2)] less(3) 
                send_flow_call1_cond_Phi[OF _ less(2)] 
      by (force, auto simp add: mult_eq_if nat_diff_distrib)
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
          using send_flow_call2_cond_Phi_decr[OF _ less(2)] less(3) 
                send_flow_call2_cond_Phi[OF _ less(2)]  invar_gamma_pres_call2[OF less(2)] 
          by (simp, subst (2) sym[OF add.assoc], auto intro: less(1))
    next
      case 2
      thus ?case
      apply simp
      apply(rule order.trans[of _ "t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f + nat (\<Phi> state - 1) * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f)"])
      using  send_flow_call2_cond_Phi_decr[OF _ less(2)] less(3) 
                send_flow_call2_cond_Phi[OF _ less(2)] 
      by (force, auto simp add: mult_eq_if nat_diff_distrib)
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