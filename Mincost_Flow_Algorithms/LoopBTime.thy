section \<open>Formalisation of Running Time of Ordinary Augmentations\<close>

theory LoopBTime
  imports LoopB
begin

locale loopBTime =
loopB_Reasoning where fst = fst for fst::"'edge_type \<Rightarrow> 'a"+
fixes t\<^sub>B\<^sub>C::nat and t\<^sub>B\<^sub>B::nat and t\<^sub>B\<^sub>u\<^sub>f::nat and t\<^sub>B\<^sub>F::nat
begin

function (domintros) loopBtime::"('a, 'c, 'd, 'edge_type) Algo_state \<Rightarrow> nat \<times> ('a, 'c, 'd, 'edge_type) Algo_state" where
  "loopBtime state = t\<^sub>B\<^sub>u\<^sub>f +++ 
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
                           ((t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B) +++ (loopBtime state'))          
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
                         ((t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B) +++ (loopBtime state'))                    
                else
                       ((t\<^sub>B\<^sub>C +  t\<^sub>B\<^sub>F) , state \<lparr> return := failure\<rparr>))
          ) 
      else ((t\<^sub>B\<^sub>C +  t\<^sub>B\<^sub>F), state \<lparr> return := notyetterm\<rparr>)
    ))"
  by auto

lemma terminationB_iff:"loopB_dom state \<longleftrightarrow> loopBtime_dom state"
proof(rule, goal_cases)
  case 1
  show ?case
  proof(induction  rule: loopB.pinduct[OF 1])
    case (1 state)
    note IH=this
    show ?case
      by(rule loopBtime.domintros, fastforce intro: IH(2), rule IH(3), auto)
  qed
next
  case 2
  show ?case 
  proof(induction  rule: loopBtime.pinduct[OF 2])
    case (1 state)
    note IH=this
    show ?case
      by(rule loopB.domintros, fastforce intro: IH(2), rule IH(3), auto)
  qed
qed

lemma equal_results_B: 
  assumes "loopB_dom state" 
  shows "loopB state = prod.snd (loopBtime state)"
proof(induction rule: loopB.pinduct[OF assms])
  case (1 state)
  note IH=this
  hence time_dom: "loopBtime_dom state"
    using terminationB_iff[of state] by simp
  show ?case 
  proof(subst loopB.psimps[OF IH(1)], subst loopBtime.psimps[OF time_dom], subst Let_def, 
        subst Let_def, subst Let_def, goal_cases)
    case 1
    show ?case 
    proof(subst (13) Let_def, subst (13) Let_def, subst (13) Let_def, subst add_fst_def,
          subst snd_conv, subst if_distrib[of prod.snd],
          rule if_cong, simp, simp, subst if_distrib[of prod.snd], rule if_cong, simp, goal_cases)
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
 qed
qed

definition "loopBtime_succ_upd state = (let
                    f = current_flow state;
                    b = balance state;
                    \<gamma> = current_\<gamma> state
 in  (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f +  t\<^sub>B\<^sub>F, state \<lparr> return:=success\<rparr>))"

lemma loopBtime_succ_upd_changes: 
"\<FF> (prod.snd (loopBtime_succ_upd state)) = \<FF> state"
"conv_to_rdg (prod.snd(loopBtime_succ_upd state)) = conv_to_rdg state"
"actives (prod.snd (loopBtime_succ_upd state)) = actives state"
"current_\<gamma> (prod.snd (loopBtime_succ_upd state)) = current_\<gamma>  state"
"representative (prod.snd (loopBtime_succ_upd state)) = representative state"
"\<F> (prod.snd (loopBtime_succ_upd state)) = \<F> state"
  unfolding loopBtime_succ_upd_def Let_def by auto

definition "loopBtime_call1_upd state = (let
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

lemma loopB_call1_upd_changes: 
"\<FF> (loopB_call1_upd state) = \<FF> state"
"conv_to_rdg (loopB_call1_upd state) = conv_to_rdg state"
"actives (loopB_call1_upd state) = actives state"
"current_\<gamma> (loopB_call1_upd state) = current_\<gamma>  state"
"representative (loopB_call1_upd state) = representative state"
"\<F> (loopB_call1_upd state) = \<F> state"
  unfolding loopB_call1_upd_def Let_def by auto

definition "loopBtime_fail_upd state = (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f +  t\<^sub>B\<^sub>F, state \<lparr> return :=failure \<rparr>)"

lemma loopBtime_fail_upd_changes: 
"\<FF> (prod.snd (loopBtime_fail_upd state)) = \<FF> state"
"conv_to_rdg (prod.snd (loopBtime_fail_upd state)) = conv_to_rdg state"
"actives (prod.snd (loopBtime_fail_upd state)) = actives state"
"current_\<gamma> (prod.snd (loopBtime_fail_upd state)) = current_\<gamma>  state"
"representative (prod.snd (loopBtime_fail_upd state)) = representative state"
"\<F> (prod.snd (loopBtime_fail_upd state)) = \<F> state"
  unfolding loopBtime_fail_upd_def Let_def by auto

definition "loopBtime_call2_upd state= (let
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

lemma loopBtime_call2_upd_changes: 
"\<FF> (prod.snd (loopBtime_call2_upd state)) = \<FF> state"
"conv_to_rdg (prod.snd (loopBtime_call2_upd state)) = conv_to_rdg state"
"actives (prod.snd (loopBtime_call2_upd state)) = actives state"
"current_\<gamma> (prod.snd (loopBtime_call2_upd state)) = current_\<gamma>  state"
"representative (prod.snd (loopBtime_call2_upd state)) = representative state"
"\<F> (prod.snd (loopBtime_call2_upd state)) = \<F> state"
  unfolding loopBtime_call2_upd_def Let_def by auto

definition "loopBtime_cont_upd state = (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f +  t\<^sub>B\<^sub>F, state \<lparr> return := notyetterm\<rparr>)"

lemma loopBtime_cont_upd_changes: 
"\<FF> (prod.snd (loopBtime_cont_upd state)) = \<FF> state"
"conv_to_rdg (prod.snd (loopBtime_cont_upd state)) = conv_to_rdg state"
"actives (prod.snd (loopBtime_cont_upd state)) = actives state"
"current_\<gamma> (prod.snd (loopBtime_cont_upd state)) = current_\<gamma>  state"
"representative (prod.snd (loopBtime_cont_upd state)) = representative state"
"\<F> (prod.snd (loopBtime_cont_upd state)) = \<F> state"
  unfolding loopBtime_cont_upd_def Let_def by auto

lemma loopBtime_simps: 
  assumes "loopBtime_dom state"
  shows   "loopB_succ_cond state \<Longrightarrow> loopBtime state = (loopBtime_succ_upd state)"
          "loopB_cont_cond state \<Longrightarrow> loopBtime state = (loopBtime_cont_upd state)"
          "loopB_fail1_cond state \<Longrightarrow> loopBtime state = (loopBtime_fail_upd state)"
          "loopB_fail2_cond state \<Longrightarrow> loopBtime state = (loopBtime_fail_upd state)"
          "loopB_call1_cond state \<Longrightarrow> loopBtime state = (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +++ loopBtime (loopB_call1_upd state)"
          "loopB_call2_cond state \<Longrightarrow> loopBtime state = (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +++ loopBtime (loopB_call2_upd state)"
proof-
  show "loopB_succ_cond state \<Longrightarrow> loopBtime state = loopBtime_succ_upd state"
    using  loopBtime.psimps[OF assms]
    unfolding loopBtime_succ_upd_def Let_def add_fst_def
    by (auto elim: loopB_succ_condE)
  show "loopB_cont_cond state \<Longrightarrow> loopBtime state = loopBtime_cont_upd state"
    apply(subst loopBtime.psimps, simp add: assms)
    apply(rule loopB_cont_condE, simp)
    unfolding loopBtime_cont_upd_def  Let_def add_fst_def by simp
  show "loopB_fail1_cond state \<Longrightarrow> loopBtime state = loopBtime_fail_upd state"
    apply(subst loopBtime.psimps, simp add: assms)
    apply(rule loopB_fail1_condE, simp)
    unfolding loopBtime_fail_upd_def  Let_def add_fst_def by auto
  show "loopB_fail2_cond state \<Longrightarrow> loopBtime state = loopBtime_fail_upd state"
    apply(subst loopBtime.psimps, simp add: assms)
    apply(rule loopB_fail2_condE, simp)
    unfolding loopBtime_fail_upd_def  Let_def add_fst_def by auto
  show " loopB_call1_cond state \<Longrightarrow> loopBtime state = (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +++ loopBtime (loopB_call1_upd state)"
  proof- (*Problem with automation*)
    assume asm:"loopB_call1_cond state"
    show "loopBtime state = (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +++ loopBtime (loopB_call1_upd state)"
    proof(rule loopB_call1_condE[OF asm], goal_cases)
      case (1 f b \<gamma> s t P f' b' state')
      thus ?case  
        apply(subst loopBtime.psimps[OF assms])
        unfolding loopB_call1_upd_def Let_def add_fst_def
        by auto
     qed
   qed
   show " loopB_call2_cond state \<Longrightarrow> loopBtime state = (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +++ loopBtime (loopB_call2_upd state)"
   proof- (*Problem with automation*)
    assume asm:"loopB_call2_cond state"
    show "loopBtime state = (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) +++ loopBtime (loopB_call2_upd state)"
    proof(rule loopB_call2_condE[OF asm], goal_cases)
      case (1 f b \<gamma> s t P f' b' state')
      thus ?case  
       using loopBtime.psimps assms
        unfolding loopB_call2_upd_def Let_def add_fst_def
         by (auto elim: loopB_call2_condE)
     qed
   qed
 qed   

lemma loopB_call1_cond_Phi: "loopB_call1_cond state \<Longrightarrow> invar_gamma state \<Longrightarrow> \<Phi> state > 0"
proof(rule loopB_call1_condE, simp, goal_cases)
  case (1 f b \<gamma> s t P f' b' state')
  show ?case 
  unfolding \<Phi>_def
  proof(insert 1, rule bexE[where P = "\<lambda> s. (1 - \<epsilon>) * \<gamma> < b s" and A = \<V>], simp, goal_cases)
    case (1 ss)
    show ?case 
    apply(insert 1, rule ordered_comm_monoid_add_class.sum_pos2[OF \<V>_finite, of ss], simp)
    unfolding invar_gamma_def 
     apply (simp add: pos_less_divide_eq)
    by (smt (verit, best) \<epsilon>_axiom(1) divide_nonneg_pos zero_le_ceiling)
qed
qed

lemma loopB_call2_cond_Phi: "loopB_call2_cond state \<Longrightarrow> invar_gamma state \<Longrightarrow> \<Phi> state > 0"
proof(rule loopB_call2_condE, simp, goal_cases)
  case (1 f b \<gamma> t s P f' b' state')
  show ?case
  unfolding \<Phi>_def
  proof(insert 1, rule bexE[where P = "\<lambda> t. - (1 - \<epsilon>) * \<gamma> > b t" and A = \<V>], simp, goal_cases)
    case (1 tt)
    show ?case 
    apply(insert 1, rule ordered_comm_monoid_add_class.sum_pos2[OF \<V>_finite, of tt], simp)
    unfolding invar_gamma_def
    apply (smt (verit, ccfv_SIG) pos_minus_divide_less_eq zero_less_ceiling)
    by (smt (verit, best) \<epsilon>_axiom(1) divide_nonneg_pos zero_le_ceiling)
qed
qed

lemma time_boundB: 
  assumes "invar_gamma state"
          "\<phi> = nat (\<Phi> state)"
  shows   "prod.fst (loopBtime state) \<le> 
             \<phi> * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) + (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f)"
  using assms
proof(induction \<phi> arbitrary: state rule: less_induct)
  case (less \<phi>)
  hence loopBtime_dom: "loopBtime_dom state"
    using loopB_term[of state] terminationB_iff[of state] by simp 
  show ?case
  proof(cases rule: loopB_cases[of state])
    case 1
    thus ?thesis
      by(auto simp add: loopBtime_simps(2)[OF loopBtime_dom] loopBtime_cont_upd_def)
  next
    case 2
    thus ?thesis
      by(auto simp add: loopBtime_simps(1)[OF loopBtime_dom] loopBtime_succ_upd_def)
  next
    case 3
    thus?thesis
      apply(subst loopBtime_simps(5)[OF loopBtime_dom], simp)
      unfolding add_fst_def 
      proof(rule order.trans[of _ "t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f + nat (\<Phi> ( (loopB_call1_upd state))) * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) + (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f)"],
          goal_cases)
       case 1
       thus ?case       
          using loopB_call1_cond_Phi_decr[OF _ less(2)] less(3) 
                loopB_call1_cond_Phi[OF _ less(2)]  invar_gamma_pres_call1[OF less(2)] 
          by (simp, subst (2) sym[OF add.assoc], auto intro: less(1))
    next
      case 2
      thus ?case
      apply simp
      apply(rule order.trans[of _ "t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f + nat (\<Phi> state - 1) * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f)"])
      using  loopB_call1_cond_Phi_decr[OF _ less(2)] less(3) 
                loopB_call1_cond_Phi[OF _ less(2)] 
      by (force, auto simp add: mult_eq_if nat_diff_distrib)
  qed
next
  case 4
  thus?thesis
      apply(subst loopBtime_simps(6)[OF loopBtime_dom], simp)
      unfolding add_fst_def 
      proof(rule order.trans[of _ "t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f + nat (\<Phi> ( (loopB_call2_upd state))) * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f) + (t\<^sub>B\<^sub>F + t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>u\<^sub>f)"],
          goal_cases)
       case 1
       thus ?case       
          using loopB_call2_cond_Phi_decr[OF _ less(2)] less(3) 
                loopB_call2_cond_Phi[OF _ less(2)]  invar_gamma_pres_call2[OF less(2)] 
          by (simp, subst (2) sym[OF add.assoc], auto intro: less(1))
    next
      case 2
      thus ?case
      apply simp
      apply(rule order.trans[of _ "t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f + nat (\<Phi> state - 1) * (t\<^sub>B\<^sub>C + t\<^sub>B\<^sub>B + t\<^sub>B\<^sub>u\<^sub>f)"])
      using  loopB_call2_cond_Phi_decr[OF _ less(2)] less(3) 
                loopB_call2_cond_Phi[OF _ less(2)] 
      by (force, auto simp add: mult_eq_if nat_diff_distrib)
  qed
next
  case 5
  thus ?thesis
    by(auto simp add: loopBtime_simps(3)[OF loopBtime_dom] loopBtime_fail_upd_def)
next
  case 6
  thus ?thesis
      by(auto simp add: loopBtime_simps(4)[OF loopBtime_dom] loopBtime_fail_upd_def)
 qed
qed

end
end