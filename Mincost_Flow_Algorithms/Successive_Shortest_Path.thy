(*
  Author: Thomas Ammer
*)

theory Successive_Shortest_Path
  imports SSP_Preps
begin

provenance human

section \<open>The Successive Shortest Path Algorithm\<close>

text \<open>Due to termination issues, we now have to restrict to integer capacities and balances.\<close>

locale SSP = cost_flow_network where fst = fst + 
             algo where fst = fst
           for fst::"'edge \<Rightarrow>'a"+
  fixes get_source::"('a \<Rightarrow> real) \<Rightarrow> 'a option" and
        get_reachable_target::"('edge \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real)\<Rightarrow> 'a \<Rightarrow> 'a option" and
        get_min_augpath::"('edge \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('edge Redge) list)"
  assumes integral_u:  "\<And> e. e \<in> \<E> \<Longrightarrow> \<exists> n::nat. \<u> e = real n"
   and    integral_b:  "\<And> v. v\<in> \<V> \<Longrightarrow> \<exists> n::int. \<b> v =  n"
   and   is_balance_b: "is_balance \<b>"
   and get_source_axioms: "\<And> b v. get_source b = Some v \<Longrightarrow> b v > 0"
                          "\<And> b v. get_source b = Some v \<Longrightarrow> v \<in> \<V>"
                          "\<And> b. (\<exists> v \<in> \<V>. b v > 0) \<longrightarrow> get_source b \<noteq> None"
   and get_reachable_target_axioms: 
          "\<And> f s t b. get_reachable_target f b s = Some t \<Longrightarrow> resreach f s t"
          "\<And> f s t b. get_reachable_target f b s = Some t \<Longrightarrow> b t < 0"
          "\<And> f s t b. get_reachable_target f b s = Some t \<Longrightarrow> t \<in> \<V>"     
          "\<And> f s b. (\<exists> t \<in> \<V>. resreach f s t \<and> b t < 0) 
                        \<longrightarrow> get_reachable_target f b s \<noteq> None"
  and get_min_augpath_axioms: True
          "\<And> f s t P. resreach f s t \<Longrightarrow> 
                get_min_augpath f s t = P \<Longrightarrow> is_s_t_path  f s t P"
          "\<And> f s t P. resreach f s t \<Longrightarrow> (\<nexists> C. augcycle f C) \<Longrightarrow>
                get_min_augpath f s t = P \<Longrightarrow> is_min_path  f s t P"
  and conservative_weights: "\<nexists> C. closed_w (make_pair ` \<E>) (map make_pair C) \<and> set C \<subseteq> \<E> \<and>
                                     foldr (\<lambda> e acc. acc + \<c> e) C 0 < 0"
begin

function  (domintros) SSP::"('a, 'edge) Algo_state \<Rightarrow> ('a, 'edge) Algo_state" where
"SSP state = 
  (let b = balance state; f = current_flow state in
  (if zero_balance b then state \<lparr>return := success\<rparr> 
   else (case get_source b of 
             None \<Rightarrow> state \<lparr> return := failure\<rparr> |
             Some s  \<Rightarrow>(case get_reachable_target f b s of 
                        None \<Rightarrow> state\<lparr> return := failure\<rparr> |
                        (Some t) \<Rightarrow> (
                        let 
                           P = get_min_augpath f s t;
                           \<gamma> = real_of_ereal (min (min (b s) (- b t)) (Rcap f (set P)));
                           f' = augment_edges f \<gamma> P;
                           b' = (\<lambda> v. if v = s then b s - \<gamma> else
                                        if v = t then b t + \<gamma> else b v) 
                        in SSP (state\<lparr> current_flow := f',
                                   balance :=  b' \<rparr>)
)
))))"
  by pat_completeness simp

definition "SSP_ret_1_cond state = 
  (let b = balance state; f = current_flow state in
  (if zero_balance b then True
   else (case get_source b of 
             None \<Rightarrow>False |
             Some s  \<Rightarrow>(case get_reachable_target f b s of 
                        None \<Rightarrow> False |
                        (Some t) \<Rightarrow> (
                        let 
                           P = get_min_augpath f s t;
                           \<gamma> = real_of_ereal (min (min (b s) (- b t)) (Rcap f (set P)));
                           f' = augment_edges f \<gamma> P;
                           b' = (\<lambda> v. if v = s then b s - \<gamma> else
                                        if v = t then b t + \<gamma> else b v) 
                        in False)
))))" 

lemma SSP_ret_1_condE: 
  "SSP_ret_1_cond state \<Longrightarrow> 
   \<lbrakk> \<And> b. b = balance state \<Longrightarrow> zero_balance b \<Longrightarrow> P\<rbrakk> \<Longrightarrow> 
   P"
  by (auto simp: SSP_ret_1_cond_def Let_def split!: option.splits if_splits)

lemma SSP_ret_1_condI:
  "b = balance state \<Longrightarrow> zero_balance b \<Longrightarrow> SSP_ret_1_cond state"
  by (auto simp: SSP_ret_1_cond_def Let_def split!: option.splits if_splits)
 

definition "SSP_ret_2_cond state = 
  (let b = balance state; f = current_flow state in
  (if zero_balance b then False
   else (case get_source b of 
             None \<Rightarrow>True |
             Some s  \<Rightarrow>(case get_reachable_target f b s of 
                        None \<Rightarrow> False |
                        (Some t) \<Rightarrow> (
                        let 
                           P = get_min_augpath f s t;
                           \<gamma> = real_of_ereal(min (min (b s) (- b t)) (Rcap f (set P)));
                           f' = augment_edges f \<gamma> P;
                           b' = (\<lambda> v. if v = s then b s - \<gamma> else
                                        if v = t then b t + \<gamma> else b v) 
                        in False)
))))"

lemma SSP_ret_2_condE: 
  "SSP_ret_2_cond state \<Longrightarrow> 
   \<lbrakk> \<And> b f.  b = balance state \<Longrightarrow> \<not> zero_balance b \<Longrightarrow>
              f = current_flow state \<Longrightarrow> get_source b = None \<Longrightarrow> P\<rbrakk> \<Longrightarrow> 
   P"  
  by (auto simp: SSP_ret_2_cond_def Let_def split!: option.splits if_splits)

lemma SSP_ret_2_condI: 
  "\<lbrakk> b = balance state ; \<not> zero_balance b ;
     f = current_flow state ; get_source b = None \<rbrakk> \<Longrightarrow> SSP_ret_2_cond state"  
  by (auto simp: SSP_ret_2_cond_def Let_def split!: option.splits if_splits)

definition "SSP_ret_3_cond state = 
  (let b = balance state; f = current_flow state in
  (if zero_balance b then False
   else (case get_source b of 
             None \<Rightarrow> False |
             Some s  \<Rightarrow>(case get_reachable_target f b s of 
                        None \<Rightarrow> True |
                        (Some t) \<Rightarrow> (
                        let 
                           P = get_min_augpath f s t;
                           \<gamma> = real_of_ereal (min (min (b s) (- b t)) (Rcap f (set P)));
                           f' = augment_edges f \<gamma> P;
                           b' = (\<lambda> v. if v = s then b s - \<gamma> else
                                        if v = t then b t + \<gamma> else b v) 
                        in False)
))))"

lemma SSP_ret_3_condE: 
  "SSP_ret_3_cond state \<Longrightarrow> 
   \<lbrakk> \<And> b f s.  b = balance state \<Longrightarrow> \<not> zero_balance b \<Longrightarrow>
              f = current_flow state \<Longrightarrow> get_source b = Some s \<Longrightarrow> 
         get_reachable_target f b s = None\<Longrightarrow> P\<rbrakk> \<Longrightarrow> 
   P"  
  by (auto simp: SSP_ret_3_cond_def Let_def split!: option.splits if_splits)

lemma SSP_ret_3_condI: 
  "\<lbrakk> b = balance state ;  \<not> zero_balance b ;
    f = current_flow state ; get_source b = Some s ; 
         get_reachable_target f b s = None \<rbrakk> \<Longrightarrow>SSP_ret_3_cond state"  
  by (auto simp: SSP_ret_3_cond_def Let_def split!: option.splits if_splits)


definition "SSP_call_4_cond state = 
  (let b = balance state; f = current_flow state in
  (if zero_balance b then False
   else (case get_source b of 
             None \<Rightarrow> False |
             Some s  \<Rightarrow>(case get_reachable_target f b s of 
                        None \<Rightarrow> False |
                        (Some t) \<Rightarrow> (
                        let 
                           P = get_min_augpath f s t;
                           \<gamma> = real_of_ereal (min (min (b s) (- b t)) (Rcap f (set P)));
                           f' = augment_edges f \<gamma> P;
                           b' = (\<lambda> v. if v = s then b s - \<gamma> else
                                        if v = t then b t + \<gamma> else b v) 
                        in True)
))))"

lemma SSP_call_4_condE: 
  "SSP_call_4_cond state \<Longrightarrow> 
   \<lbrakk> \<And> b f s t.  b = balance state \<Longrightarrow> \<not> zero_balance b \<Longrightarrow>
              f = current_flow state \<Longrightarrow> get_source b = Some s \<Longrightarrow> 
         get_reachable_target f b s = Some t \<Longrightarrow> P\<rbrakk> \<Longrightarrow> 
   P"  
  by (auto simp: SSP_call_4_cond_def Let_def split!: option.splits if_splits)

lemma SSP_call_4_condI: 
  " \<lbrakk>b = balance state ; \<not> zero_balance b;
     f = current_flow state ; get_source b = Some s;
     get_reachable_target f b s = Some t\<rbrakk> \<Longrightarrow> SSP_call_4_cond state"  
  by (auto simp: SSP_call_4_cond_def Let_def split!: option.splits if_splits)

lemma SSP_cases:
  assumes
   "SSP_ret_1_cond state \<Longrightarrow> P"
   "SSP_ret_2_cond state \<Longrightarrow> P"
   "SSP_ret_3_cond state \<Longrightarrow> P"
   "SSP_call_4_cond state \<Longrightarrow> P"
 shows P
proof-
  have "SSP_ret_1_cond state  \<or> SSP_ret_2_cond state \<or>
        SSP_ret_3_cond state \<or> SSP_call_4_cond state"
    by (auto simp add: SSP_ret_1_cond_def SSP_ret_2_cond_def
                       SSP_ret_3_cond_def SSP_call_4_cond_def
                       Let_def
           split: list.split_asm option.split_asm if_splits)
  then show ?thesis
    using assms
    by auto
qed

definition "SSP_ret1 state = state\<lparr>return := success\<rparr>"

definition "SSP_ret2 state = state \<lparr> return := failure\<rparr>"

definition "SSP_ret3 state =  state\<lparr> return := failure\<rparr>"

definition "SSP_upd4 state = (let b = balance state; f = current_flow state;
                                  s = the ( get_source b); 
                                  t = the (get_reachable_target f b s );
                                  P = get_min_augpath f s t;
                                  \<gamma> = real_of_ereal (min (min (b s) (- b t)) (Rcap f (set P)));
                                  f' = augment_edges f \<gamma> P;
                                  b' = (\<lambda> v. if v = s then b s - \<gamma> else
                                        if v = t then b t + \<gamma> else b v) 
                                  in (state\<lparr> current_flow := f',balance :=  b' \<rparr>))"

definition "SSP_upd4' state = (let b = balance state; f = current_flow state;
                                  s = the ( get_source b); 
                                  t = the (get_reachable_target f b s );
                                  P = get_min_augpath f s t;
                                  \<gamma> = real_of_ereal (min (min (b s) (- b t)) (Rcap f (set P)))
                                  in (state\<lparr> current_flow := augment_edges f \<gamma> P,
                                      balance := (\<lambda> v. if v = s then b s - \<gamma> else
                                        if v = t then b t + \<gamma> else b v)  \<rparr>))"

lemma SSP_upd4_same: "SSP_upd4' state = SSP_upd4 state"
  unfolding SSP_upd4_def SSP_upd4'_def Let_def by \<^marker>\<open>provenance ai\<close> simp

declare[[simp_trace_depth_limit=1000]]

lemma SSP_simps:
  assumes "SSP_dom state" 
  shows"SSP_call_4_cond state \<Longrightarrow> SSP state = SSP (SSP_upd4 state)"
       "SSP_ret_1_cond state \<Longrightarrow> SSP state = (SSP_ret1 state)"
       "SSP_ret_2_cond state \<Longrightarrow> SSP state = (SSP_ret2 state)"
       "SSP_ret_3_cond state \<Longrightarrow> SSP state = (SSP_ret3 state)"
  subgoal  
    apply(rule SSP_call_4_condE, simp)
    apply(thin_tac " SSP_call_4_cond state")
    apply(subst SSP.psimps[OF assms])
    unfolding SSP_upd4_def
    apply \<^marker>\<open>provenance ai\<close>(simp split: option.splits if_splits, simp add: Let_def)
    done    
  by (auto simp add: SSP.psimps[OF assms]
                       SSP_ret_1_cond_def SSP_ret1_def
                       SSP_ret_2_cond_def SSP_ret2_def
                       SSP_ret_3_cond_def SSP_ret3_def
                       SSP_call_4_cond_def SSP_upd4_def
                      Let_def
            split: list.splits option.splits if_splits)

lemma cond_4_single: "SSP_call_4_cond state  \<Longrightarrow> \<not> SSP_ret_1_cond state "
      "SSP_call_4_cond state  \<Longrightarrow> \<not> SSP_ret_2_cond state "
      "SSP_call_4_cond state  \<Longrightarrow> \<not> SSP_ret_3_cond state "
   by(auto elim!:  SSP_ret_1_condE  SSP_ret_2_condE SSP_ret_3_condE SSP_call_4_condE)
 
lemma SSP_induct: 
  assumes "SSP_dom state"
  assumes "\<And>state. \<lbrakk>SSP_dom state;
                     SSP_call_4_cond state \<Longrightarrow> P (SSP_upd4 state)\<rbrakk> \<Longrightarrow> P state"
  shows "P state"
  apply(rule SSP.pinduct)
  subgoal using assms(1) .
  apply(rule assms(2))
   apply simp
  apply(rule SSP_call_4_condE, simp)
  unfolding SSP_upd4_def 
  subgoal for state b f s t
    apply(thin_tac " SSP_call_4_cond state")
    apply(subst let_swap[of P])+
    by simp
  done

named_theorems invar_holds_intros

lemma invar_balance_holds_4[invar_holds_intros]: 
"\<lbrakk>SSP_call_4_cond state; invar_balance state\<rbrakk> 
            \<Longrightarrow> invar_balance (SSP_upd4 state)"
  apply(rule SSP_call_4_condE, simp, thin_tac "SSP_call_4_cond state")
  unfolding invar_balance_def SSP_upd4_def is_balance_def
  subgoal for b f s t
    apply(rule trans[of _ "sum (balance state) \<V>"], subst Groups_Big.comm_monoid_add_class.sum.remove[of _ s])
    using \<V>_finite  get_source_axioms(2)[of "(balance state)" s]
    apply(simp, simp, subst Groups_Big.comm_monoid_add_class.sum.remove[of _ t])
    using get_source_axioms(2)[of "(balance state)" s] 
    using \<V>_finite get_reachable_target_axioms(3)[of f "balance state" s t]
          get_reachable_target_axioms(2)[of f "balance state" s t] 
          get_source_axioms(1)[of "(balance state)" s]
    unfolding Let_def
    by(auto simp add: Groups_Big.comm_monoid_add_class.sum.remove)
  done

lemma invar_balance_holds_1[invar_holds_intros]: "\<lbrakk>SSP_ret_1_cond state; invar_balance state\<rbrakk> \<Longrightarrow> invar_balance (SSP_ret1 state)"
  by (auto simp:SSP_ret1_def intro: invar_balance_intro)

lemma invar_balance_holds_2[invar_holds_intros]: "\<lbrakk>SSP_ret_2_cond state; invar_balance state\<rbrakk> \<Longrightarrow> invar_balance (SSP_ret2 state)"
  by (auto simp:SSP_ret2_def intro: invar_balance_intro)

lemma invar_balance_holds_3[invar_holds_intros]: "\<lbrakk>SSP_ret_3_cond state; invar_balance state\<rbrakk> \<Longrightarrow> invar_balance (SSP_ret3 state)"
  by (auto simp:SSP_ret3_def intro: invar_balance_intro)

lemma invar_balance_holds: 
   assumes "SSP_dom state" "invar_balance state"
   shows "invar_balance (SSP state)"
  using assms(2)
proof(induction rule: SSP_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    apply(rule SSP_cases[where state = state])
    by (auto intro!: IH invar_holds_intros  simp: SSP_simps[OF IH(1)])
qed

lemma failure_SSP_ret3_cond:
  assumes "SSP_dom state" "invar_balance state" "return (SSP state) = failure"
  shows "SSP_ret_3_cond (SSP state)" using assms(2-3)
proof(induction rule: SSP_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
  proof(rule SSP_cases[where state = state], goal_cases)
    case 1
    then show ?case
      using IH(4) IH(1)
      by(auto simp add: SSP_ret1_def SSP_simps(2))
  next
    case 2
    then show ?case 
        using IH(3)  get_source_axioms(3)[of _] sum_zero_not_all_zero[of \<V> "balance state", OF \<V>_finite]
        by (fastforce intro: SSP_ret_2_condE 
                   simp add: zero_balance_def invar_balance_def is_balance_def)
  next
    case 3
    then show ?case
       using IH 
       by(fastforce elim: SSP_ret_3_condE intro: SSP_ret_3_condI 
                  simp add: SSP_ret3_def SSP_simps)+
  next
    case 4
    then show ?case 
      using IH(4)
      by(auto intro: IH(2) 
              simp add: invar_balance_holds_4  IH(3) IH(1) SSP_simps(1)  IH(4))
  qed
qed

lemma is_integral_flowE: "is_integral_flow f \<Longrightarrow>
                          ((\<And> e. e \<in> \<E> \<Longrightarrow> \<exists> n::int. f e = n) \<Longrightarrow> P) \<Longrightarrow>
                         P"
  unfolding is_integral_flow_def by simp

lemma is_integral_balanceI: "(\<And> v. v \<in> \<V> \<Longrightarrow> \<exists> n::int. (b::'a\<Rightarrow> real) v = n) \<Longrightarrow>
                              is_integral_balance b"
  unfolding is_integral_balance_def by simp

lemma is_integral_balanceE: "is_integral_balance b \<Longrightarrow>
                          ((\<And> v. v \<in> \<V> \<Longrightarrow> \<exists> n::int. (b::'a\<Rightarrow> real) v = n) \<Longrightarrow> P) \<Longrightarrow>
                             P"
  unfolding is_integral_balance_def by simp

lemma "invar_integral \<lparr>current_flow = (\<lambda> e. 0), balance = \<b>,  return = notyetterm\<rparr>"
  by(force intro: invar_integralI is_integral_flowI is_integral_balanceI
            simp: integral_b)

lemma invar_integral_holds_4[invar_holds_intros]: 
  assumes "SSP_call_4_cond state"  "invar_integral state"
  shows "invar_integral (SSP_upd4 state)"
proof(rule invar_integralI)
  define b where "b = balance state"
  define f where " f = current_flow state"
  define s where " s = the ( get_source b)"
  define t where " t = the (get_reachable_target f b s )"
  define P where " P = get_min_augpath f s t"
  define \<gamma> where " \<gamma> = real_of_ereal (min (min (b s) (- b t)) (Rcap f (set P)))"
  define f' where "f' = augment_edges f \<gamma> P"
  define b' where "b' = (\<lambda> v. if v = s then b s - \<gamma> else
                                        if v = t then b t + \<gamma> else b v)"
  have s_in_V: "s \<in> \<V>"
    by (force intro: get_source_axioms(2)[of b] SSP_call_4_condE[OF assms(1)] 
           simp add: b_def s_def)

  have t_in_V: "t \<in> \<V>"
    by (force intro: get_reachable_target_axioms(3)[of f b s] SSP_call_4_condE[OF assms(1)]
           simp add: b_def f_def s_def t_def)

  have resreach_f_s_t:"resreach f  s t"
    by (intro get_reachable_target_axioms(1)[of f b s], 
           force intro: SSP_call_4_condE[OF assms(1)]
              simp add: b_def f_def s_def t_def )
  
  have "is_integral (b s)"
      using assms(2)  s_in_V is_integral_neg 
      by (auto intro: is_integral_balanceE[of "balance state"] 
            simp add:  invar_integral_def  is_integral_def b_def)

  moreover have "is_integral (- b t)"
      using assms(2)  t_in_V is_integral_neg  
      by (auto intro: is_integral_balanceE[of "balance state"] 
            simp add: invar_integral_def  is_integral_def b_def )

  ultimately have "is_integral (min (b s) (- b t))"
    by(rule integral_min) 

  moreover have s_neq_t: "s \<noteq> t"
    apply(rule SSP_call_4_condE[OF assms(1)])
    using get_source_axioms(1) get_reachable_target_axioms(2)
    unfolding s_def t_def b_def f_def by fastforce

  moreover have "is_integral (real_of_ereal (Rcap f (set P)))"
    using get_min_augpath_axioms(2)[OF resreach_f_s_t refl] s_neq_t
    using assms(2)  augpath_cases[of f P] 
    unfolding is_min_path_def is_s_t_path_def  augpath_def prepath_def 
              invar_integral_def f_def  P_def 
    by (auto intro: Rcap_integral)
      
  ultimately have integral_gamma: "is_integral \<gamma>"
    unfolding \<gamma>_def using integral_min
    by \<^marker>\<open>provenance ai\<close> (auto simp: min_def)

  show "is_integral_flow (current_flow (SSP_upd4 state))"
  proof-
    have f'_integral: "is_integral_flow f'"
      using assms(2) integral_gamma 
      unfolding invar_integral_def is_integral_def f_def  f'_def
      by (auto intro: integral_flow_pres)
    show ?thesis
      using f'_integral
      unfolding f'_def P_def \<gamma>_def s_def t_def f_def b_def SSP_upd4_def Let_def 
      by auto
  qed
  show "is_integral_balance (balance (SSP_upd4 state))"
  proof-
      have b'_integral: "is_integral_balance b'"
        unfolding b'_def
        proof \<^marker>\<open>provenance ai\<close> (intro is_integral_balanceI)
          fix v assume v_in_V: "v \<in> \<V>"
          have b_integral: "is_integral (b v)"
            using assms(2) v_in_V
            by (auto intro: is_integral_balanceE[of "balance state"]
                     simp add: invar_integral_def is_integral_def b_def)
          obtain k where gamma_int: "\<gamma> = real_of_int k"
            using integral_gamma unfolding is_integral_def by auto
          show "\<exists>n::int. (if v = s then b s - \<gamma> else if v = t then b t + \<gamma> else b v) = real_of_int n"
          proof (cases "v = s")
            case True
            have "is_integral (b s)" using b_integral True by simp
            then obtain m where "b s = real_of_int m" unfolding is_integral_def by auto
            with gamma_int have "b s - \<gamma> = real_of_int (m - k)" by (simp add: of_int_diff)
            with True show ?thesis by (intro exI[of _ "m - k"]) auto
          next
            case False
            note v_neq_s = False
            show ?thesis
            proof (cases "v = t")
              case True
              have "is_integral (b t)" using b_integral True by simp
              then obtain m where "b t = real_of_int m" unfolding is_integral_def by auto
              with gamma_int have "b t + \<gamma> = real_of_int (m + k)" by simp
              with v_neq_s True show ?thesis by (intro exI[of _ "m + k"]) auto
            next
              case False
              obtain m where "b v = real_of_int m" using b_integral unfolding is_integral_def by auto
              with v_neq_s False show ?thesis by (intro exI[of _ "m"]) auto
            qed
          qed
        qed
      show ?thesis 
      using b'_integral
      unfolding b'_def P_def \<gamma>_def s_def t_def f_def b_def SSP_upd4_def Let_def 
      by simp
  qed
qed

lemma invar_integral_holds_1[invar_holds_intros]:
 "\<lbrakk>SSP_ret_1_cond state; invar_integral state\<rbrakk> \<Longrightarrow> invar_integral (SSP_ret1 state)"
  by (auto simp:SSP_ret1_def invar_integral_def intro: invar_integralI)

lemma invar_integral_holds_2[invar_holds_intros]: 
"\<lbrakk>SSP_ret_2_cond state; invar_integral state\<rbrakk> \<Longrightarrow> invar_integral (SSP_ret2 state)"
  by (auto simp:SSP_ret2_def invar_integral_def intro: invar_integralI)

lemma invar_integral_holds_3[invar_holds_intros]: 
"\<lbrakk>SSP_ret_3_cond state; invar_integral state\<rbrakk> \<Longrightarrow> invar_integral (SSP_ret3 state)"
  by (auto simp:SSP_ret3_def invar_integral_def intro: invar_integralI)

lemma invar_integral_holds: 
   assumes "SSP_dom state" "invar_integral state"
   shows "invar_integral (SSP state)"
  using assms(2)
proof(induction rule: SSP_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    apply(rule SSP_cases[where state = state])
    by (auto intro!: IH invar_holds_intros  simp: SSP_simps[OF IH(1)])
qed

lemma SSP_call_4_cond_SSP_dom:
        "SSP_call_4_cond state \<Longrightarrow> SSP_dom (SSP_upd4 state) \<Longrightarrow>
                    SSP_dom state"
  apply(rule SSP.domintros)
  apply(rule forw_subst[of _ "SSP_upd4 state" SSP_dom])
  subgoal
    unfolding SSP_upd4_def SSP_call_4_cond_def Let_def
    by \<^marker>\<open>provenance ai\<close> (auto simp add: ereal_min option.sel cong: if_cong)
  by simp 

lemma SSP_ret_1_cond_SSP_dom:
        "SSP_ret_1_cond state  \<Longrightarrow>
                    SSP_dom state"
  by(auto intro: SSP.domintros elim: SSP_ret_1_condE)

lemma SSP_ret_2_cond_SSP_dom:
        "SSP_ret_2_cond state  \<Longrightarrow>
                    SSP_dom state"
  by(force intro: SSP.domintros elim: SSP_ret_2_condE)

lemma SSP_ret_3_cond_SSP_dom:
        "SSP_ret_3_cond state  \<Longrightarrow>
                    SSP_dom state"
  by(force intro: SSP.domintros elim: SSP_ret_3_condE)

theorem integral_balance_termination:
  assumes "invar_integral state"
  shows "SSP_dom state"
  using assms
proof(induction "bABSnat (balance state)" arbitrary: state rule: less_induct)
  case less
  show ?case 
  proof(cases rule: SSP_cases[of state])
    case 1
    then show ?thesis using SSP_ret_1_cond_SSP_dom by simp
  next
    case 2
    then show ?thesis using SSP_ret_2_cond_SSP_dom by simp
  next
    case 3
    then show ?thesis using SSP_ret_3_cond_SSP_dom by simp
  next
    case 4
      define b where "b = balance state"
  define f where " f = current_flow state"
  define s where " s = the ( get_source b)"
  define t where " t = the (get_reachable_target f b s )"
  define P where " P = get_min_augpath f s t"
  define \<gamma> where " \<gamma> = real_of_ereal  (min (min (b s) (- b t)) (Rcap f (set P)))"
  define f' where "f' = augment_edges f \<gamma> P"
  define b' where "b' = (\<lambda> v. if v = s then b s - \<gamma> else
                                        if v = t then b t + \<gamma> else b v)"
  have s_in_V: "s \<in> \<V>"
    by (auto intro!: get_source_axioms(2)[of b] intro: SSP_call_4_condE[OF 4] 
           simp add: b_def s_def)

  have b_s_pos: "b s > 0 "
    by(fastforce intro!: get_source_axioms(1)[of b] intro: SSP_call_4_condE[OF 4] 
               simp add: b_def s_def)

  have int_b_s: "is_integral (b s)"
    apply(rule is_integral_balanceE[of b])
    using b_def invar_integral_def less.prems s_in_V 
    by(auto simp add:is_integral_def )

  have "abs (b s) \<ge> 1" 
    using b_s_pos int_b_s is_integral_def by auto

  have t_in_V: "t \<in> \<V>"
    by (force intro:  get_reachable_target_axioms(3)[of f b s] SSP_call_4_condE[OF 4] 
           simp add: b_def f_def s_def t_def)

  have t_is_neg: "b t < 0"
    by (force intro!:  get_reachable_target_axioms(2)[of f b s] intro: SSP_call_4_condE[OF 4] 
           simp add: b_def f_def s_def t_def)

  have int_b_s: "is_integral (b t)"
    apply(rule is_integral_balanceE[of b])
    using b_def invar_integral_def less.prems t_in_V
    unfolding is_integral_def by auto

  have "abs (b t) \<ge> 1" 
    using int_b_s is_integral_def t_is_neg by fastforce


  have resreach_f_s_t:"resreach f  s t"
    by (intro get_reachable_target_axioms(1)[of f b s], 
           force intro: SSP_call_4_condE[OF 4]
              simp add: b_def f_def s_def t_def )

  have "is_integral (b s)"
      using less.prems  s_in_V is_integral_neg 
      by (auto intro: is_integral_balanceE[of "balance state"] 
            simp add:  invar_integral_def  is_integral_def b_def)

  moreover have "is_integral (- b t)"
      using less.prems  t_in_V is_integral_neg  
      by (auto intro: is_integral_balanceE[of "balance state"] 
            simp add: invar_integral_def  is_integral_def b_def )

  ultimately have "is_integral (min (b s) (- b t))"
    by(rule integral_min) 

  moreover have s_neq_t: "s \<noteq> t"
    apply(rule SSP_call_4_condE[OF 4])
    using get_source_axioms(1) get_reachable_target_axioms(2)
    unfolding s_def t_def b_def f_def by fastforce

  moreover have "is_integral (real_of_ereal (Rcap f (set P)))"
    using get_min_augpath_axioms(2)[OF resreach_f_s_t refl] s_neq_t
    using less.prems augpath_cases[of f P] 
    unfolding is_min_path_def is_s_t_path_def  augpath_def prepath_def 
              invar_integral_def f_def  P_def 
    by (auto intro: Rcap_integral)
      
  ultimately have integral_gamma: "is_integral \<gamma>"
    unfolding \<gamma>_def using integral_min
  proof \<^marker>\<open>provenance ai\<close> (cases "ereal (min (b s) (- b t)) \<le> Rcap f (set P)")
    case True
    hence gamma_val_eq1:
      "real_of_ereal (min (min (b s) (- b t)) (Rcap f (set P))) = min (b s) (- b t)"
      by (simp add: min_def)
    show "is_integral (real_of_ereal (min (min (b s) (- b t)) (Rcap f (set P))))"
      unfolding gamma_val_eq1
      using \<open>is_integral (min (b s) (- b t))\<close> .
  next
    case False
    hence gamma_val_eq2:
      "real_of_ereal (min (min (b s) (- b t)) (Rcap f (set P))) = real_of_ereal (Rcap f (set P))"
      by (simp add: min_def)
    show "is_integral (real_of_ereal (min (min (b s) (- b t)) (Rcap f (set P))))"
      unfolding gamma_val_eq2
      using \<open>is_integral (real_of_ereal (Rcap f (set P)))\<close> .
  qed

  have P_augpath:"augpath f P"
    using  get_min_augpath_axioms(2)[of f s t P, OF resreach_f_s_t]
    unfolding P_def is_min_path_def is_s_t_path_def
    by auto

  have Rcap_pos: "(Rcap f (set P)) > 0"
    by(rule augpath_rcap[OF P_augpath])

  have gamma_pos: "\<gamma> > 0"
    unfolding \<gamma>_def
    using Rcap_pos t_is_neg b_s_pos
  proof \<^marker>\<open>provenance ai\<close> -
    have min1_pos: "0 < min (ereal (b s)) (ereal (- b t))"
      using b_s_pos t_is_neg by (simp add: min_less_iff_conj)
    have overall_pos: "0 < min (min (ereal (b s)) (ereal (- b t))) (Rcap f (set P))"
      using min1_pos Rcap_pos by (simp add: min_less_iff_conj)
    have b_s_lt_inf: "ereal (b s) < \<infinity>"
      by simp
    have min1_lt_inf: "min (ereal (b s)) (ereal (- b t)) < \<infinity>"
      using min.cobounded1[of "ereal (b s)" "ereal (- b t)"] b_s_lt_inf
      by (rule le_less_trans)
    have overall_lt_inf: "min (min (ereal (b s)) (ereal (- b t))) (Rcap f (set P)) < \<infinity>"
      using min.cobounded1[of "min (ereal (b s)) (ereal (- b t))"] min1_lt_inf
      by (rule le_less_trans)
    have overall_neq_inf: "min (min (ereal (b s)) (ereal (- b t))) (Rcap f (set P)) \<noteq> \<infinity>"
      using overall_lt_inf by simp
    show "0 < Rcap f (set P) \<Longrightarrow> b t < 0 \<Longrightarrow> 0 < b s \<Longrightarrow>
           0 < real_of_ereal (min (ereal (min (b s) (- b t))) (Rcap f (set P)))"
      using overall_pos overall_neq_inf by (simp add: zero_less_real_of_ereal)
  qed
    
  have s_red: "abs (b' s) < abs (b s)"
  proof \<^marker>\<open>provenance ai\<close> -
    have step1: "min (min (b s) (- b t)) (Rcap f (set P)) \<le> ereal (min (b s) (- b t))"
      by (rule min.cobounded1)
    have step2: "min (b s) (- b t) \<le> b s"
      by (rule min.cobounded1)
    have step2': "ereal (min (b s) (- b t)) \<le> ereal (b s)"
      using step2 by simp
    have le_ereal: "min (min (b s) (- b t)) (Rcap f (set P)) \<le> ereal (b s)"
      by (rule order_trans[OF step1 step2'])
    have gamma_le_bs: "real_of_ereal (min (min (b s) (- b t)) (Rcap f (set P))) \<le> b s"
    proof (cases "min (min (b s) (- b t)) (Rcap f (set P))")
      case (real r)
      then show ?thesis using le_ereal by simp
    next
      case PInf
      then show ?thesis using le_ereal by simp
    next
      case MInf
      then show ?thesis using b_s_pos by simp
    qed
    have gamma_le: "\<gamma> \<le> b s"
      unfolding \<gamma>_def using gamma_le_bs by simp
    have b'_s_eq: "b' s = b s - \<gamma>"
      unfolding b'_def by simp
    have h1: "abs (b s) = b s"
      using b_s_pos by (simp add: abs_of_pos)
    have h2: "abs (b s - \<gamma>) = b s - \<gamma>"
      using gamma_le by (simp add: abs_of_nonneg)
    show "abs (b' s) < abs (b s)"
      unfolding b'_s_eq h1 h2
      using gamma_pos by linarith
  qed

  have t_red: "abs (b' t) < abs (b t)"
    unfolding b'_def 
    using gamma_pos t_is_neg
    unfolding \<gamma>_def 
  proof \<^marker>\<open>provenance ai\<close> -
    have step1: "min (min (b s) (- b t)) (Rcap f (set P)) \<le> ereal (min (b s) (- b t))"
      by (rule min.cobounded1)
    have step2: "min (b s) (- b t) \<le> - b t"
      by (rule min.cobounded2)
    have step2': "ereal (min (b s) (- b t)) \<le> ereal (- b t)"
      using step2 by simp
    have le_ereal: "min (min (b s) (- b t)) (Rcap f (set P)) \<le> ereal (- b t)"
      by (rule order_trans[OF step1 step2'])
    have gamma_le_bt: "real_of_ereal (min (min (b s) (- b t)) (Rcap f (set P))) \<le> - b t"
    proof (cases "min (min (b s) (- b t)) (Rcap f (set P))")
      case (real r)
      then show ?thesis using le_ereal by simp
    next
      case PInf
      then show ?thesis using le_ereal by simp
    next
      case MInf
      then show ?thesis using t_is_neg by simp
    qed
    have gamma_le: "\<gamma> \<le> - b t"
      unfolding \<gamma>_def using gamma_le_bt by simp
    have b't_eq: "b' t = b t + \<gamma>"
      unfolding b'_def using s_neq_t by simp
    have le0: "b t + \<gamma> \<le> 0"
      using gamma_le by linarith
    have main: "\<bar>b t + \<gamma>\<bar> < \<bar>b t\<bar>"
    proof -
      have "\<bar>b t + \<gamma>\<bar> = - (b t + \<gamma>)"
        using le0 by (simp add: abs_of_nonpos)
      also have "- (b t + \<gamma>) < - b t"
        using gamma_pos by linarith
      also have "- b t = \<bar>b t\<bar>"
        using t_is_neg by simp
      finally show ?thesis .
    qed
    have \<gamma>e_def: "real_of_ereal (min (min (ereal (b s)) (ereal (- b t))) (Rcap f (set P))) = \<gamma>"
      using \<gamma>_def by simp
    show "0 < real_of_ereal (min (ereal (min (b s) (- b t))) (Rcap f (set P))) \<Longrightarrow>
           b t < 0 \<Longrightarrow>
           \<bar>if t = s
             then b s -
                  real_of_ereal (min (ereal (min (b s) (- b t))) (Rcap f (set P)))
             else if t = t
                  then b t +
                       real_of_ereal (min (ereal (min (b s) (- b t))) (Rcap f (set P)))
                  else b t\<bar> < \<bar>b t\<bar>"
      using s_neq_t main by (simp add: \<gamma>e_def)
  qed
   
    show ?thesis 
    proof(cases rule: SSP_call_4_cond_SSP_dom[OF 4])
      case 1
      have invar_integral:"invar_integral (SSP_upd4 state)"
        using less 4 by ( auto intro: invar_integral_holds_4)
      hence int_b: "is_integral_balance (balance (SSP_upd4 state))"
        unfolding invar_integral_def by simp
        
      have abs_less:"bABSnat (balance (SSP_upd4 state)) < bABSnat (balance state)"
        apply(rule bABSnat_mono[of _ _ s, OF int_b conjunct2[OF less(2)[simplified invar_integral_def]]
                                             _ s_in_V])
          using t_red s_red
          by(unfold  b'_def  SSP_upd4_def Let_def  \<gamma>_def s_def t_def b_def f_def P_def) auto        
      show ?case 
        by(rule less(1)[OF abs_less invar_integral])
    qed
  qed 
qed

lemma termination_initial_state:
" SSP_dom \<lparr>current_flow = (\<lambda> e. 0), balance = \<b>,  return = notyetterm\<rparr>"
 by(force intro: integral_balance_termination
                 invar_integralI  is_integral_flowI is_integral_balanceI 
       simp add: integral_b)

lemma invar_opt_holds_1[invar_holds_intros]:
 "\<lbrakk>SSP_ret_1_cond state; invar_opt state\<rbrakk> \<Longrightarrow> invar_opt (SSP_ret1 state)"
  by (auto simp:SSP_ret1_def invar_opt_def )

lemma invar_opt_holds_2[invar_holds_intros]: 
"\<lbrakk>SSP_ret_2_cond state; invar_opt state\<rbrakk> \<Longrightarrow> invar_opt (SSP_ret2 state)"
  by (auto simp:SSP_ret2_def invar_opt_def)

lemma invar_opt_holds_3[invar_holds_intros]: 
"\<lbrakk>SSP_ret_3_cond state; invar_opt state\<rbrakk> \<Longrightarrow> invar_opt (SSP_ret3 state)"
  by (auto simp:SSP_ret3_def invar_opt_def)

lemma invar_opt_holds_4[invar_holds_intros]: 
  assumes "SSP_call_4_cond state"  "invar_opt state"
  shows "invar_opt (SSP_upd4 state)"
proof-
  define b where "b = balance state"
  define f where " f = current_flow state"
  define s where " s = the ( get_source b)"
  define t where " t = the (get_reachable_target f b s )"
  define P where " P = get_min_augpath f s t"
  define \<gamma> where " \<gamma> = real_of_ereal (min (min (b s) (- b t)) (Rcap f (set P)))"
  define f' where "f' = augment_edges f \<gamma> P"
  define b' where "b' = (\<lambda> v. if v = s then b s - \<gamma> else
                                        if v = t then b t + \<gamma> else b v)"
  have s_in_V: "s \<in> \<V>"
    by (force intro: get_source_axioms(2)[of b] SSP_call_4_condE[OF assms(1)] 
           simp add: b_def s_def)

  have t_in_V: "t \<in> \<V>"
    by (force intro: get_reachable_target_axioms(3)[of f b s] SSP_call_4_condE[OF assms(1)]
           simp add: b_def f_def s_def t_def)

  have resreach_f_s_t:"resreach f  s t"
    by (intro get_reachable_target_axioms(1)[of f b s], 
           force intro: SSP_call_4_condE[OF assms(1)]
              simp add: b_def f_def s_def t_def )

  have P_augpath:"augpath f P"
    using  get_min_augpath_axioms(2)[of f s t P, OF resreach_f_s_t]
    unfolding P_def is_min_path_def is_s_t_path_def
    by auto

  have Rcap_pos: "(Rcap f (set P)) > 0"
    by(rule augpath_rcap[OF P_augpath])

  have b_s_pos: "b s > 0 "
    by(fastforce intro!: get_source_axioms(1)[of b] intro: SSP_call_4_condE[OF assms(1)] 
               simp add: b_def s_def)

  have t_is_neg: "b t < 0"
    by (force intro!:  get_reachable_target_axioms(2)[of f b s] 
               intro: SSP_call_4_condE[OF assms(1)] 
           simp add: b_def f_def s_def t_def)

  have gamma_pos: "\<gamma> > 0"
    unfolding \<gamma>_def
    using Rcap_pos t_is_neg b_s_pos
  proof \<^marker>\<open>provenance ai\<close> -
    have ne_le: "\<And>x y::ereal. x \<le> y \<Longrightarrow> y \<noteq> \<infinity> \<Longrightarrow> x \<noteq> \<infinity>"
    proof -
      fix x y :: ereal
      assume "x \<le> y" "y \<noteq> \<infinity>"
      show "x \<noteq> \<infinity>"
      proof (rule notI)
        assume "x = \<infinity>"
        with \<open>x \<le> y\<close> have "\<infinity> \<le> y" by simp
        then have "y = \<infinity>" by (simp add: ereal_infty_less_eq(1))
        with \<open>y \<noteq> \<infinity>\<close> show False by simp
      qed
    qed
    have fin1: "min (ereal (b s)) (ereal (- b t)) \<le> ereal (b s)"
      by (rule min.cobounded1)
    then have ne1: "min (ereal (b s)) (ereal (- b t)) \<noteq> \<infinity>"
      using PInfty_neq_ereal(1)[of "b s"] by (rule ne_le)
    have fin2: "min (min (ereal (b s)) (ereal (- b t))) (Rcap f (set P)) \<le> min (ereal (b s)) (ereal (- b t))"
      by (rule min.cobounded1)
    then have ne2: "min (min (ereal (b s)) (ereal (- b t))) (Rcap f (set P)) \<noteq> \<infinity>"
      using ne1 by (rule ne_le)
    have conj_fact: "0 < min (min (b s) (- b t)) (Rcap f (set P)) \<and>
                    min (min (b s) (- b t)) (Rcap f (set P)) \<noteq> \<infinity>"
    proof
      show "0 < min (min (b s) (- b t)) (Rcap f (set P))"
        using b_s_pos t_is_neg Rcap_pos by simp
    next
      show "min (min (b s) (- b t)) (Rcap f (set P)) \<noteq> \<infinity>"
        using ne2 by simp
    qed
    show "0 < Rcap f (set P) \<Longrightarrow> b t < 0 \<Longrightarrow> 0 < b s \<Longrightarrow>
          0 < real_of_ereal (min (ereal (min (b s) (- b t))) (Rcap f (set P)))"
      using conj_fact by (simp add: zero_less_real_of_ereal)
  qed

  have s_hd_P: "s = fstv (hd P)"
  using get_min_augpath_axioms(2)[of f s t P, OF resreach_f_s_t] 
  unfolding is_min_path_def is_s_t_path_def P_def by auto

  have t_last_P: "t = sndv (last P)"
  using get_min_augpath_axioms(2)[of f s t P, OF resreach_f_s_t] 
  unfolding is_min_path_def is_s_t_path_def P_def by auto

  have no_augcycle:"\<nexists>C. augcycle f C"
    using assms  invar_opt_def  f_def min_cost_flow_no_augcycle 
    by blast

  have good_cap: "ereal \<gamma> \<le> Rcap (current_flow state) (set P)"
    unfolding \<gamma>_def f_def
  proof \<^marker>\<open>provenance ai\<close> -
    have Rcap_eq: "Rcap (current_flow state) (set P) = Rcap f (set P)"
      by (simp add: f_def)
    have le1: "min (min (b s) (- b t)) (Rcap f (set P)) \<le> Rcap f (set P)"
      by (rule min.cobounded2)
    have le2: "min (min (b s) (- b t)) (Rcap f (set P)) \<le> ereal (min (b s) (- b t))"
      by (rule min.cobounded1)
    have not_PInf: "min (min (b s) (- b t)) (Rcap f (set P)) \<noteq> \<infinity>"
    proof -
      have lt0: "ereal (b s) < \<infinity>" by simp
      have mb1: "min (ereal (b s)) (ereal (- b t)) \<le> ereal (b s)"
        by (rule min.cobounded1)
      from mb1 lt0 have lt1: "min (ereal (b s)) (ereal (- b t)) < \<infinity>"
        by (rule le_less_trans)
      have mb2: "min (min (ereal (b s)) (ereal (- b t))) (Rcap f (set P))
                 \<le> min (ereal (b s)) (ereal (- b t))"
        by (rule min.cobounded1)
      from mb2 lt1 have "min (min (ereal (b s)) (ereal (- b t))) (Rcap f (set P)) < \<infinity>"
        by (rule le_less_trans)
      then show ?thesis by simp
    qed
    have not_MInf: "min (min (b s) (- b t)) (Rcap f (set P)) \<noteq> - \<infinity>"
    proof (cases "ereal (min (b s) (- b t)) \<le> Rcap f (set P)")
      case True
      have min1_ne_MInf: "min (ereal (b s)) (ereal (- b t)) \<noteq> - \<infinity>"
        by (auto simp: min_def MInfty_neq_ereal)
      with True have "min (min (b s) (- b t)) (Rcap f (set P)) = ereal (min (b s) (- b t))"
        by (simp add: min_def)
      then show ?thesis using min1_ne_MInf by simp
    next
      case False
      then have "min (min (b s) (- b t)) (Rcap f (set P)) = Rcap f (set P)"
        by (simp add: min_def)
      then show ?thesis using Rcap_pos by force
    qed
    have eq: "ereal (real_of_ereal (min (min (b s) (- b t)) (Rcap f (set P))))
                = min (min (b s) (- b t)) (Rcap f (set P))"
    proof (cases "min (min (b s) (- b t)) (Rcap f (set P))")
      case (real r)
      then show ?thesis by simp
    next
      case PInf
      then show ?thesis using not_PInf by simp
    next
      case MInf
      then show ?thesis using not_MInf by simp
    qed
    show "ereal (real_of_ereal (min (ereal (min (b s) (- b t)))
                              (Rcap (current_flow state) (set P))))
          \<le> Rcap (current_flow state) (set P)"
      using eq le1 Rcap_eq
      by simp
  qed

  have s_neq_t: "s \<noteq> t"
    using s_def t_def  get_source_axioms(1)[of b s]
            get_reachable_target_axioms(2)[of f b s t]
            get_source_axioms(3)[of b] assms(1)
            get_reachable_target_axioms(4)[of f s b] 
            b_def f_def s_def t_def 
      by (force intro:  SSP_call_4_condE[OF assms(1)])

  show ?thesis
    unfolding invar_opt_def
    apply(rule path_aug_opt_pres[of s t "\<lambda> v. \<b> v  - b v" f \<gamma> P])  
    using assms(2) gamma_pos  get_min_augpath_axioms(3)[OF resreach_f_s_t no_augcycle] 
          s_hd_P t_last_P good_cap s_neq_t
    by(auto  split: if_split
          simp add: SSP_upd4_def P_def invar_opt_def  \<gamma>_def t_def s_def f_def b_def  Let_def)  
qed

lemma invar_opt_holds: 
   assumes "SSP_dom state" "invar_opt state"
   shows "invar_opt (SSP state)"
  using assms(2)
proof(induction rule: SSP_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    apply(rule SSP_cases[where state = state])
    by (auto intro!: IH invar_holds_intros  simp: SSP_simps[OF IH(1)])
qed

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
  hence cost_neg': "foldr (\<lambda> e acc. acc + \<c> e) (map oedge C) 0 < 0" using aa by \<^marker>\<open>provenance ai\<close> simp
  moreover have map_eq: "map to_vertex_pair C = map make_pair (map oedge C)"
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
  moreover have subset_E: "set (map oedge C) \<subseteq> \<E> " 
    using C_prop  
    by (auto simp add: image_def augcycle_def \<EE>_def)
  ultimately show False
  proof \<^marker>\<open>provenance ai\<close> -
    have closed_w_oedge: "closed_w (make_pair ` \<E>) (map make_pair (map oedge C))"
      using aa(1) map_eq by simp
    have conj: "closed_w (make_pair ` \<E>) (map make_pair (map oedge C)) \<and>
          set (map oedge C) \<subseteq> \<E> \<and>
          foldr (\<lambda> e acc. acc + \<c> e) (map oedge C) 0 < 0"
      using closed_w_oedge subset_E cost_neg' by blast
    with conservative_weights show False by blast
  qed
qed

text \<open>By this, we can already prove correctness.\<close>

lemma invar_opt_initial_state:
"invar_opt \<lparr>current_flow = (\<lambda> e. 0), balance = \<b>,  return = notyetterm\<rparr>"
  unfolding invar_opt_def
  apply(rule no_augcycle_min_cost_flow)
  subgoal
    unfolding isbflow_def isuflow_def ex_def
    using u_non_neg  integral_u by fastforce
  using no_augcycle_at_beginning by simp

lemma  if_term_not_notyetterm:
  assumes "(SSP_dom state)"
  shows"return (SSP state) \<noteq> notyetterm"
  apply(rule SSP_induct[OF assms(1)])
  subgoal for state
  proof(rule SSP_cases[of state], goal_cases)
    case 1
    show ?case 
      apply(insert 1, rule SSP_ret_1_condE, simp)
      apply(subst SSP.psimps, simp)  
      by auto
  next
    case 2
    show ?case
      apply(insert 2, rule SSP_ret_2_condE, simp)
      apply(subst SSP.psimps, simp)  
      by auto
  next
    case 3
    show ?case
      apply(insert 3, rule SSP_ret_3_condE, simp)
      apply(subst SSP.psimps, simp)  
      by auto
  qed (auto simp add: SSP_simps)
  done


lemma success:
  assumes "(SSP_dom state)"
          "return (SSP state) = success"
        shows "SSP_ret_1_cond (SSP state)"
  using assms(2)
  apply(induction rule: SSP_induct[OF assms(1)])
  subgoal for state
    apply(rule SSP_cases[of state])   
    apply(rule SSP_ret_1_condE, simp)
    apply(subst SSP.psimps)
    by(auto split: option.split if_split 
         simp add: Let_def SSP_ret_1_cond_def SSP_simps(1) SSP_ret3_def SSP_simps(4)  SSP_ret2_def SSP_simps(3))
  done

theorem total_correctness:
  assumes "final = SSP \<lparr>current_flow = (\<lambda> e. 0), balance = \<b>,  return = notyetterm\<rparr>"
  shows   "return final = success \<Longrightarrow> is_Opt \<b> (current_flow final)"
          "return final = failure \<Longrightarrow> \<nexists> f. is_Opt \<b> f"
          "return final = notyetterm \<Longrightarrow> False"
proof-
  show "return final = success \<Longrightarrow> is_Opt \<b> (current_flow final)"
  proof-
    assume asm:"return final = success"
    have ret_1:"SSP_ret_1_cond final" 
      using asm  assms
      by(auto intro: success termination_initial_state)
    have invar_opt:"invar_opt final" 
      using assms
      by(auto intro: invar_opt_holds termination_initial_state invar_opt_initial_state)
    show "is_Opt \<b> (current_flow final)"
      apply(rule SSP_ret_1_condE[of final, OF ret_1])
      using invar_opt
      unfolding invar_opt_def zero_balance_def  is_Opt_def isbflow_def ex_def
      by simp
  qed
  show "return final = failure \<Longrightarrow> \<nexists> f. is_Opt \<b> f"
  proof-
     assume asm:"return final = failure"
    have ret_1:"SSP_ret_3_cond final" unfolding assms(1)
      apply(rule failure_SSP_ret3_cond, rule termination_initial_state)
      using asm is_balance_b unfolding assms(1) invar_balance_def is_balance_def by simp+

    have invar_opt:"invar_opt final" unfolding assms(1)
      by(rule invar_opt_holds, rule termination_initial_state,
           rule  invar_opt_initial_state)

    obtain  b  s \<f> where bsf_prop:" b = balance final" "\<not> zero_balance b"
              "\<f> = current_flow final" "get_source b = Some s"
              "get_reachable_target \<f> b s = None"
      using SSP_ret_3_condE ret_1 by blast

    hence bs_pos:"b s > 0" "s \<in> \<V>"
      using get_source_axioms by auto

    have is_Opt_term:"is_Opt (\<lambda> v. \<b> v -  b v) \<f>" 
      using invar_opt unfolding invar_opt_def
      using bsf_prop by simp

    have rescutsat:"sum (\<lambda> v. \<b> v -  b v) (Rescut \<f> s) = Cap (Rescut \<f> s)"
      using is_Opt_term  bsf_prop get_source_axioms 
      by (auto intro!:flow_saturates_res_cut[simplified Extended_Real.sum_ereal] 
                      Rescut_around_in_V 
             simp add: is_Opt_def)

    have sumbb:"sum (\<lambda> v. \<b> v -  b v) (Rescut \<f> s) = 
         sum \<b> (Rescut \<f> s) - sum b (Rescut \<f> s)"
      using sum_subtractf by auto

    have sumb0:"sum b (Rescut \<f> s) > 0"
    proof(rule ccontr)
      assume asm:" \<not> 0 < sum b (Rescut \<f> s)"
      show False
      proof(cases "0 = sum b (Rescut \<f> s)")
        case True
        have "s \<in> (Rescut \<f> s)" "b s > 0" 
           by (fastforce simp add: bs_pos(1) Rescut_def )+
         then obtain t where t_prop:"t \<in> (Rescut \<f> s)" "b t < 0"
           using True sum_pos2[of "Rescut \<f> s" s b] finite_Rescut[of s \<f>, OF bs_pos(2)]
           by force
        hence rsf:"resreach \<f>  s t" unfolding Rescut_def  using bs_pos  by auto
        have "t \<in> \<V>" using t_prop(1) Rescut_around_in_V bs_pos by auto
        thus False using get_reachable_target_axioms(4)[of \<f> s b] t_prop bsf_prop rsf by simp
      next
        case False
        hence "0 > sum b (Rescut \<f> s)" using asm by simp
        hence "sum b (Rescut \<f> s) < 0" by simp
        then obtain t where t_prop:"t \<in> (Rescut \<f> s)" "b t < 0"
        by (meson less_le_not_le linorder_linear sum_nonneg)
        hence rsf:"resreach \<f>  s t" unfolding Rescut_def  using bs_pos  by auto
        have "t \<in> \<V>" using t_prop(1) Rescut_around_in_V bs_pos by auto
        thus False using get_reachable_target_axioms(4)[of \<f> s b] t_prop bsf_prop rsf by simp
      qed
    qed

    hence sumbb':"sum (\<lambda> v. \<b> v -  b v) (Rescut \<f> s) < sum \<b> (Rescut \<f> s)" using sumbb by simp

    show " \<nexists>f. is_Opt \<b> f"
    proof
      assume "\<exists>f. is_Opt \<b> f "
      then obtain f where f_prop:"is_Opt \<b> f" by auto
      have le_cut: "sum \<b> (Rescut \<f> s) \<le> Cap (Rescut \<f> s)"
        using f_prop bsf_prop get_source_axioms 
        by (auto intro!: flow_less_cut[of f,simplified Extended_Real.sum_ereal]
                         Rescut_around_in_V 
               simp add:  is_Opt_def )
      have "ereal (sum \<b> (Rescut \<f> s)) \<le> ereal (sum (\<lambda> v. \<b> v -  b v) (Rescut \<f> s))"
        using le_cut rescutsat by \<^marker>\<open>provenance ai\<close> simp
      hence "sum \<b> (Rescut \<f> s) \<le> sum (\<lambda> v. \<b> v -  b v) (Rescut \<f> s)"
        by \<^marker>\<open>provenance ai\<close> (simp add: ereal_less_eq)
      thus False
        using sumbb' by \<^marker>\<open>provenance ai\<close> linarith
    qed
  qed
  show "return final = notyetterm \<Longrightarrow> False"
  proof-
    assume "return final = notyetterm"
    moreover have "return final \<noteq> notyetterm" unfolding assms(1)
      by(auto intro!: if_term_not_notyetterm termination_initial_state)
    ultimately show False by simp
  qed
qed

end
end