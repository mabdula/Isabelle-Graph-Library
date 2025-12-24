section \<open>A Capacity Scaling Algorithm\<close>

text \<open>In the last section we have proven that augmenting along a path preserves optimality. 
Just the balances need to be changed. The subsequent theory uses this as an invariant for an algorithm.
In its most basic form the procedure can be described as follows:
\begin{itemize}
\item Find a source $s$ with $b\; s > 0$, a target $t$ with $b \; t < 0$ 
and an augmenting path $p$ of minimum costs connecting them.
\item augment as much flow as possible: $\gamma = \min \lbrace Rcap \; p , b\; s, - b \; t \rbrace$.
\item The amount of flow left to be distributed decreases: $b \; s \leftarrow b \; s - \gamma$
and  $b \; t \leftarrow b \; t + \gamma$.
\item repeat this until $b = 0$ (minimum cost flow found)
 or there are no $s$, $t$ and $p$ (no $b$-flow exists).
\end{itemize}

For computing maximum flows via the Ford-Fulkerson method it appears to be beneficial
 to choose augmenting paths with high capacities. Concretely, this is done by capacity scaling:
Use all paths with capacity above a lower bound $L$, set $L = \frac{1}{2} \cdot L$ and repeat.
A similar approach may be applied for selecting source, target and path
 in the case of a minimum cost flow problem.
Thus, the algorithm can be refined:
\begin{enumerate}
\item Choose some initial $L = 2^l$ and set $b' = b$.
\item If $b' = 0$ then stop since all supplies and demands have been evened already.
\item Choose some $s$, $t$ and $p$ in between such that $b' \; s > L$, $b' \; t < - L$, $Rcap \; p > L$ 
and $p$ is minimum-cost path.
In case of non-existence go to 5.
\item  Augment $f$ along $p$. $b \; s \leftarrow b \; s - \gamma$ and  $b \; t \leftarrow b \; t + \gamma$.
\item Whenever $L = 1$, there can't be a $b$-flow. Otherwise, halve $L$ and continue at 3.
\end{enumerate}
\<close>

theory Scaling
  imports SSP_Preps
begin

text \<open>In contrast to the naive algorithm, we are now facing two mutually nested loops. 
We will compile this to Isabelle by making use of two recursive functions, one for each loop.
The function corresponding to the outer loop will handle the changes in $L$, 
whereas the second function is used for the (possibly repeated) augmentation above the threshold $L$.
The algorithm modifies three variables, namely the scaling parameter $L$, the current flow $f$ 
and the remaining balance $b'$.
We can modularize the interplay of both loops by making use of Isabelle locales.
By doing so, one can fix some auxiliary procedures to be called by other functions
 while instantiating them later on. Due to the locale approach, 
the threshold  $L$ does not have to be carried by the program state.
Instead of this, we parametrize the inner loop's locale and the corresponding axioms with $L$.
\<close>

subsection \<open>The inner Loop\<close>

text \<open>Let us now take a look at the locale for realizing the inner loop.
We fix some parameter $L$ indicating the current threshold set from outside.
The function $get \_ source \_ target \_ path$ is supposed
 to return an appropriate triple of source, target and an augmenting path.
This means in particular:
\begin{itemize}
\item If some $(s, t, P)$ are returned, then $b \;s > L$, $b \; t < -L$ and $Rcap \; P > L$.
Additionally, $P$ has to be a path of minimum costs connection $s$ and $t$.
\item Concerning completeness, if there are such $s$, $t$ and $P$,
 then the function has to return some of those.
 In order to instantiate this function, we also require the absence of cycles.
The important case is $k = 0$ which will be used for a completeness proof.
In fact, the axiom for $k > 0$ is never referred to.
\end{itemize}
\<close>

locale SSP = algo where fst = fst for fst::"'edge_type \<Rightarrow> 'a" +
  fixes L::nat and
        get_source_target_path
            ::"('edge_type \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real)  \<Rightarrow> ('a \<times> 'a \<times> 'edge_type Redge list) option"
   assumes get_source_target_path_axioms:
     " \<And> b f s t P . get_source_target_path f b = Some (s,t,P) \<Longrightarrow>
                     s \<in> \<V>"
     " \<And> b f s t P . get_source_target_path f b = Some (s,t,P) \<Longrightarrow>
                     b s > real L"
     " \<And> b f s t P . get_source_target_path f b = Some (s,t,P) \<Longrightarrow>
                     t \<in> \<V>"
     " \<And> b f s t P . get_source_target_path f b = Some (s,t,P) \<Longrightarrow>
                     b t < - real L"
     " \<And> b f s t P . get_source_target_path f b = Some (s,t,P) \<Longrightarrow>
                     resreach_cap f L s t"
     " \<And> b f s t P . get_source_target_path f b = Some (s,t,P) \<Longrightarrow>
                      is_min_path f s t P"
     " \<And> b f s t P . get_source_target_path f b = Some (s,t,P) \<Longrightarrow>
                      Rcap f (set P) > L"
     " \<And> b f s t P. (\<nexists> C. augcycle f C) \<Longrightarrow>is_min_path f s t P \<Longrightarrow> s \<in> \<V> \<Longrightarrow> t \<in> \<V> \<Longrightarrow> L > 0 \<Longrightarrow>
                    b s > real L \<Longrightarrow> b t < - real L \<Longrightarrow>
                    resreach_cap f L s t \<Longrightarrow> Rcap f (set P) > L \<Longrightarrow>
                    (\<exists> s t P. get_source_target_path f b = Some (s,t,P))"
      " \<And> b f s t P. (\<nexists> C. augcycle f C) \<Longrightarrow> is_s_t_path f s t P \<Longrightarrow> s \<in> \<V> \<Longrightarrow> t \<in> \<V> \<Longrightarrow> L = 0 \<Longrightarrow>
                    b s > real L \<Longrightarrow> b t < - real L \<Longrightarrow>
                    resreach_cap f L s t \<Longrightarrow> Rcap f (set P) > L \<Longrightarrow>
                   (\<exists> s t P. get_source_target_path f b = Some (s,t,P))"
begin

text \<open>We then formalize the inner loop:
\begin{itemize}
\item If zero balance $b' = 0$ is reached, then we are already done and the procedure 
terminates answering $success$.
\item Otherwise, choose $s$, $t$ and $P$
\item If there are none, then at least for the current threshold $L$ there is nothing to do.
(Deciding the non-existence of a $b$-flow is left to the next locale!)
\item Otherwise, augment along the path, modify $b'$ and $f$, continue.
\end{itemize}
Please note the $\mathbf{function}$ operator. 
By this, functions with non-trivial termination arguments may be defined.
\<close>

subsubsection \<open>Function Definition and Setup\<close>

function  (domintros) SSP::"('a, 'edge_type) Algo_state \<Rightarrow> ('a, 'edge_type) Algo_state" where
"SSP state = 
  (let b = balance state; f = current_flow state in
  (if zero_balance b then state \<lparr>return := success\<rparr> 
   else (case get_source_target_path f b of 
             None \<Rightarrow> state \<lparr> return := notyetterm\<rparr> |
             Some (s, t, P)  \<Rightarrow> (
                            let 
                           \<gamma> = real_of_ereal ( min (min (b s) (- b t)) (Rcap f (set P)));
                           f' = augment_edges f \<gamma> P;
                           b' = (\<lambda> v. if v = s then b s - \<gamma> else
                                        if v = t then b t + \<gamma> else b v) 
                        in SSP (state\<lparr> current_flow := f',
                                   balance :=  b' \<rparr>)
)
)))"
  by pat_completeness simp

text \<open>Now, we define some conditions indicating the exact
 execution branch taken in $SSP$ before recursion.\<close>

text \<open>First condition: Successful return.\<close>

definition "SSP_ret_1_cond state = 
  (let b = balance state; f = current_flow state in
  (if zero_balance b then True
   else (case get_source_target_path f b of 
             None \<Rightarrow> False |
             Some (s, t, P)  \<Rightarrow> (
                            let 
                           \<gamma> = real_of_ereal ( min (min (b s) (- b t)) (Rcap f (set P)));
                           f' = augment_edges f \<gamma> P;
                           b' = (\<lambda> v. if v = s then b s - \<gamma> else
                                        if v = t then b t + \<gamma> else b v) 
                        in False)
)
))" 

text \<open>Introduction and elimination rules for technical reasons.\<close>

lemma SSP_ret_1_condE: 
  "SSP_ret_1_cond state \<Longrightarrow> 
   \<lbrakk> \<And> b. b = balance state \<Longrightarrow> zero_balance b \<Longrightarrow> P\<rbrakk> \<Longrightarrow> 
   P"
  by (auto simp: SSP_ret_1_cond_def Let_def split!: option.splits if_splits)

lemma SSP_ret_1_condI:
  "b = balance state \<Longrightarrow> zero_balance b \<Longrightarrow> SSP_ret_1_cond state"
  by (auto simp: SSP_ret_1_cond_def Let_def split!: option.splits if_splits)
 
text \<open>Same for non-zero balance and path non-existence.\<close>

definition "SSP_ret_2_cond state = 
   (let b = balance state; f = current_flow state in
  (if zero_balance b then False 
   else (case get_source_target_path f b of 
             None \<Rightarrow> True |
             Some (s, t, P)  \<Rightarrow> (
                            let 
                           \<gamma> = real_of_ereal ( min (min (b s) (- b t)) (Rcap f (set P)));
                           f' = augment_edges f \<gamma> P;
                           b' = (\<lambda> v. if v = s then b s - \<gamma> else
                                        if v = t then b t + \<gamma> else b v) 
                        in False
)
)))"

lemma SSP_ret_2_condE: 
  "SSP_ret_2_cond state \<Longrightarrow> 
   \<lbrakk> \<And> b f.  b = balance state \<Longrightarrow> \<not> zero_balance b \<Longrightarrow>
              f = current_flow state \<Longrightarrow> get_source_target_path f b = None \<Longrightarrow> P\<rbrakk> \<Longrightarrow> 
   P"  
  by (auto simp: SSP_ret_2_cond_def Let_def split!: option.splits if_splits)

lemma SSP_ret_2_condI: 
  "\<lbrakk> b = balance state ; \<not> zero_balance b ;
     f = current_flow state ; get_source_target_path f b = None \<rbrakk> \<Longrightarrow> SSP_ret_2_cond state"  
  by (auto simp: SSP_ret_2_cond_def Let_def split!: option.splits if_splits)

text \<open>The case for recursion: non-zero balance and appropriate source, target and path found.\<close>

definition "SSP_call_3_cond state = 
   (let b = balance state; f = current_flow state in
  (if zero_balance b then False 
   else (case get_source_target_path f b of 
             None \<Rightarrow> False |
             Some (s, t, P)  \<Rightarrow> (
                            let 
                           \<gamma> = real_of_ereal ( min (min (b s) (- b t)) (Rcap f (set P)));
                           f' = augment_edges f \<gamma> P;
                           b' = (\<lambda> v. if v = s then b s - \<gamma> else
                                        if v = t then b t + \<gamma> else b v) 
                        in True
)
)))"

lemma SSP_call_3_condE: 
  "SSP_call_3_cond state \<Longrightarrow> 
   \<lbrakk> \<And> b f s t p.  b = balance state \<Longrightarrow> \<not> zero_balance b \<Longrightarrow>
              f = current_flow state \<Longrightarrow> 
         get_source_target_path f b = Some (s,t,p) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> 
   P"  
  by (auto simp: SSP_call_3_cond_def Let_def split!: option.splits if_splits)

lemma SSP_call_3_condI: 
  "\<lbrakk> b = balance state ;  \<not> zero_balance b ;
    f = current_flow state ; get_source_target_path f b = Some (s,t,p) 
 \<rbrakk> \<Longrightarrow>SSP_call_3_cond state"  
  by (auto simp: SSP_call_3_cond_def Let_def split!: option.splits if_splits)

text \<open>Altogether, the three conditions given above are total.\<close>

lemma SSP_cases:
  assumes
   "SSP_ret_1_cond state \<Longrightarrow> P"
   "SSP_ret_2_cond state \<Longrightarrow> P"
   "SSP_call_3_cond state \<Longrightarrow> P"
 shows P
proof-
  have "SSP_ret_1_cond state  \<or> SSP_ret_2_cond state \<or>
        SSP_call_3_cond state "
    by (auto simp add: SSP_ret_1_cond_def SSP_ret_2_cond_def
                       SSP_call_3_cond_def
                       Let_def
           split: list.split_asm option.split_asm if_splits)
  then show ?thesis
    using assms
    by auto
qed

text \<open>Now we extract the program state modifications before termination or recursion.\<close>

definition "SSP_ret1 state = state\<lparr>return := success\<rparr>"

definition "SSP_ret2 state = state \<lparr> return := notyetterm\<rparr>"


definition "SSP_upd3 state = (let b = balance state; f = current_flow state;
                                  (s,t,P) = the (get_source_target_path f b);
                                  \<gamma> = real_of_ereal ( min (min (b s) (- b t)) (Rcap f (set P)));
                                  f' = augment_edges f \<gamma> P;
                                  b' = (\<lambda> v. if v = s then b s - \<gamma> else
                                        if v = t then b t + \<gamma> else b v) 
                                  in (state\<lparr> current_flow := f',balance :=  b' \<rparr>))"

text \<open>Let's redefine for pleasing the simplifier.\<close>

definition "SSP_upd3' state = (let b = balance state; f = current_flow state;
                                  (s,t,P) = the (get_source_target_path f b);
                                  \<gamma> = real_of_ereal ( min (min (b s) (- b t)) (Rcap f (set P)))
                                  in (state\<lparr> current_flow := augment_edges f \<gamma> P,
                                      balance := (\<lambda> v. if v = s then b s - \<gamma> else
                                        if v = t then b t + \<gamma> else b v)  \<rparr>))"

lemma SSP_upd4_same: "SSP_upd3' state = SSP_upd3 state"
  by(auto simp add: SSP_upd3_def SSP_upd3'_def)

declare[[simp_trace_depth_limit=1000]]

text \<open>We consider loop unfolding. Due to this, $SSP$ can be replaced by a final
 state in case of termination and
 by $SSP \; next$ where $next$ is the modified program state in case of recursion.\<close>

lemma SSP_simps:
  assumes "SSP_dom state" 
  shows"SSP_call_3_cond state \<Longrightarrow> SSP state = SSP (SSP_upd3 state)"
       "SSP_ret_1_cond state \<Longrightarrow> SSP state = (SSP_ret1 state)"
       "SSP_ret_2_cond state \<Longrightarrow> SSP state = (SSP_ret2 state)"
  subgoal  
    apply(rule SSP_call_3_condE, simp)
    apply(subst SSP.psimps[OF assms])
    unfolding SSP_upd3_def
    apply(simp split: option.splits if_splits, metis)
    done    
  by (auto simp add: SSP.psimps[OF assms]
                       SSP_ret_1_cond_def SSP_ret1_def
                       SSP_ret_2_cond_def SSP_ret2_def
                       SSP_call_3_cond_def SSP_upd3_def
                      Let_def
            split: list.splits option.splits if_splits)

text \<open>When the execution trace  reached the part for recursion,
none of the conditions for termination can be true.\<close>

lemma cond_4_single: "SSP_call_3_cond state  \<Longrightarrow> \<not> SSP_ret_1_cond state "
      "SSP_call_3_cond state  \<Longrightarrow> \<not> SSP_ret_2_cond state "
  by(auto elim: SSP_ret_1_condE  SSP_call_3_condE 
         elim!: SSP_ret_2_condE 
         intro: SSP_call_3_condE)
  
text \<open>We show an induction principle for this function.
Intuitively, the induction is conducted with the number of loop iterations.
Since $SSP$ does not necessarily terminate, we assume $SSP \_ dom$ to denote termination.
\<close>

lemma SSP_induct: 
  assumes "SSP_dom state"
  assumes "\<And>state. \<lbrakk>SSP_dom state;
                     SSP_call_3_cond state \<Longrightarrow> P (SSP_upd3 state)\<rbrakk> \<Longrightarrow> P state"
  shows "P state"
  apply(rule SSP.pinduct)
  subgoal using assms(1) .
  apply(rule assms(2))
  unfolding SSP_upd3_def Let_def 
  apply meson 
  apply(rule SSP_call_3_condE)
  by simp+

named_theorems invar_holds_intros

subsubsection \<open>First Invariant: Sound Balances\<close>

text \<open>We show that if the initial balance $b$ was well-formed, i.e. total sum of $0$, then
this will be preserved throughout the algorithm.
\<close>

text \<open>The interesting case is of course recursion after \textit{modifying} the program state.
For all nodes but $s$ and $t$ the $b'$-values do not change, whereas for $s$ and $t$
 the changes are cancelled.
\<close>

lemma invar_balance_holds_4[invar_holds_intros]:
 "\<lbrakk>SSP_call_3_cond state; invar_balance state\<rbrakk> \<Longrightarrow> invar_balance (SSP_upd3 state)"
  apply(rule SSP_call_3_condE, simp)
  unfolding invar_balance_def SSP_upd3_def is_balance_def
  subgoal for b f s t P
    apply(rule trans[of _ "sum (balance state) \<V>"])
      using \<V>_finite get_source_target_path_axioms(1-4)[of f b s t P]
      apply(subst Groups_Big.comm_monoid_add_class.sum.remove[of _ s], simp, simp)
      apply(subst Groups_Big.comm_monoid_add_class.sum.remove[of _ t], simp, force)
      subgoal
       apply(rule trans[of _ "_ + (_ + sum (balance state) (\<V> - {s} - {t}))"])
       apply(rule sum_eq_split, simp)+
       unfolding Let_def
       by(intro sum.cong, simp, simp,
          subst Groups_Big.comm_monoid_add_class.sum.remove[of _ s], simp, simp, 
          subst Groups_Big.comm_monoid_add_class.sum.remove[of _ t], auto) 
   by simp
 done

text \<open>The other two cases are trivial since balances are not modified.\<close>

lemma invar_balance_holds_1[invar_holds_intros]:
 "\<lbrakk>SSP_ret_1_cond state; invar_balance state\<rbrakk> \<Longrightarrow> invar_balance (SSP_ret1 state)"
  by (auto simp:SSP_ret1_def intro: invar_balance_intro)

lemma invar_balance_holds_2[invar_holds_intros]: 
"\<lbrakk>SSP_ret_2_cond state; invar_balance state\<rbrakk> \<Longrightarrow> invar_balance (SSP_ret2 state)"
  by (auto simp:SSP_ret2_def intro: invar_balance_intro)

text \<open>By making use of our induction principle we can show preservation of the first invariant.\<close>

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

subsubsection \<open>Second Invariant: Integrality\<close>

text \<open>First of all, let us show the integrality of the initial state.\<close>

lemma "invar_integral \<lparr>current_flow = (\<lambda> e. 0), balance = \<b>,  return = notyetterm\<rparr>"
  by(force intro: invar_integralI is_integral_flowI is_integral_balanceI
            simp: integral_b)

text \<open>We show preservation of integrality.
When changing an integer flow and balance by integers, the result is still integer.
\<close>

lemma invar_integral_holds_4[invar_holds_intros]: 
  assumes "SSP_call_3_cond state"  "invar_integral state"
  shows "invar_integral (SSP_upd3 state)"
proof(rule invar_integralI)
  define b where "b = balance state"
  define f where " f = current_flow state"
  obtain s t P where stp_def: "(s,t,P) = the (get_source_target_path f b)" 
    by (metis prod_cases3)
  have stp_prop: "Some (s,t,P) = get_source_target_path f b"
    apply(rule SSP_call_3_condE[OF assms(1)])
    using b_def f_def stp_def by simp
  define \<gamma> where " \<gamma> = real_of_ereal( min (min (b s) (- b t)) (Rcap f (set P)))"
  define f' where "f' = augment_edges f \<gamma> P"
  define b' where "b' = (\<lambda> v. if v = s then b s - \<gamma> else
                                        if v = t then b t + \<gamma> else b v)"
  have s_in_V: "s \<in> \<V>"
    apply(rule get_source_target_path_axioms(1)[of f b s t P], rule SSP_call_3_condE[OF assms(1)])
    by (simp add: b_def stp_def stp_prop f_def)

  have t_in_V: "t \<in> \<V>"
    apply(rule get_source_target_path_axioms(3)[of f b s t P], rule SSP_call_3_condE[OF assms(1)])
    by (simp add: b_def stp_def stp_prop f_def)

  have resreach_f_s_t:"resreach_cap f L s t"
    using stp_prop 
    by (auto intro: get_source_target_path_axioms(5)[of f b s t P])

  have "is_integral (b s)"
      unfolding b_def
      apply(rule is_integral_balanceE[of "balance state"])
      using assms(2)  s_in_V is_integral_neg 
      unfolding invar_integral_def  is_integral_def by auto

  moreover have "is_integral (- b t)"
      unfolding b_def
      apply(rule is_integral_balanceE[of "balance state"])
      using assms(2)  t_in_V is_integral_neg 
      unfolding invar_integral_def  is_integral_def by auto

  ultimately have "is_integral (min (b s) (- b t))"
    by(rule integral_min) 

  moreover have "is_integral (real_of_ereal (Rcap f (set P)))"
    using assms(2) unfolding invar_integral_def f_def 
    using get_source_target_path_axioms(6)[of f b s t P] stp_prop stp_def
    unfolding is_min_path_def is_s_t_path_def
    using augpath_cases[of f P] 
    by (auto intro: Rcap_integral)
      
  ultimately have integral_gamma: "is_integral \<gamma>"
    unfolding \<gamma>_def using integral_min 
    by (simp add: min_def)

  show "is_integral_flow (current_flow (SSP_upd3 state))"
  proof-
    have f'_integral: "is_integral_flow f'"
      unfolding f'_def using assms(2) integral_gamma 
      unfolding invar_integral_def is_integral_def f_def
      by (auto intro: integral_flow_pres)
    show ?thesis
      apply(subst arg_cong[of _ f' is_integral_flow])     
      unfolding SSP_upd3_def Let_def
      using  f'_integral stp_prop
      unfolding f'_def  \<gamma>_def f_def b_def 
      by (subst sym[OF stp_def[simplified b_def f_def]], auto)
  qed

  have intgs:"is_integral (b s + \<gamma>)"
     by (auto intro: integral_add simp add: \<open>is_integral (b s)\<close> integral_gamma)

   have "is_integral (b t)" 
     using \<open>is_integral (- b t)\<close> is_integral_neg by fastforce

  have intgt:"is_integral (b t - \<gamma>)"
     by (auto intro: integral_sub simp add: \<open>is_integral (b t)\<close> integral_gamma)

  show "is_integral_balance (balance (SSP_upd3 state))"
  proof-
      have b'_integral: "is_integral_balance b'"
      unfolding b'_def
      proof(rule is_integral_balanceI, goal_cases)
        case (1 v)
        then show ?case 
          using \<open>is_integral (b s)\<close> integral_sub integral_add  \<open>is_integral (b t)\<close>
                 integral_gamma is_integral_def is_integral_balanceE[of b] assms(2) 
          unfolding invar_integral_def b_def (*takes some time*)
          by (cases "v = s", simp, cases "v = t") force+
      qed
      show ?thesis 
      using  sym[OF stp_def[simplified b_def f_def]] b'_integral  stp_prop
      unfolding f'_def \<gamma>_def f_def b_def b'_def SSP_upd3_def Let_def by auto
  qed
qed

text \<open>Trivial for immediate termination.\<close>

lemma invar_integral_holds_1[invar_holds_intros]:
 "\<lbrakk>SSP_ret_1_cond state; invar_integral state\<rbrakk> \<Longrightarrow> invar_integral (SSP_ret1 state)"
  by (auto simp:SSP_ret1_def invar_integral_def intro: invar_integralI)

lemma invar_integral_holds_2[invar_holds_intros]: 
"\<lbrakk>SSP_ret_2_cond state; invar_integral state\<rbrakk> \<Longrightarrow> invar_integral (SSP_ret2 state)"
  by (auto simp:SSP_ret2_def invar_integral_def intro: invar_integralI)

text \<open>Again by the induction principle.\<close>

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

subsubsection \<open>Termination for Integral Settings\<close>

text \<open>Termination is an inductive property.\<close>

lemma SSP_call_3_cond_SSP_dom:"SSP_call_3_cond state \<Longrightarrow> SSP_dom (SSP_upd3 state) \<Longrightarrow> SSP_dom state"
  unfolding SSP_upd3_def SSP_call_3_cond_def Let_def 
  apply(rule SSP.domintros) 
  apply(subst sym[OF Extended_Real.ereal_min])+
  by simp

lemma SSP_ret_1_cond_SSP_dom: "SSP_ret_1_cond state  \<Longrightarrow>SSP_dom state"
  by(auto intro: SSP.domintros elim: SSP_ret_1_condE)

lemma SSP_ret_2_cond_SSP_dom:"SSP_ret_2_cond state  \<Longrightarrow> SSP_dom state"
  by(force intro: SSP.domintros elim: SSP_ret_2_condE)
 
text \<open>For integral balances, flows and capacities we can show termination.
In any iteration, the absolute value $\vert b' \vert$ has to decrease by at least $1$.
Then we continue with strong induction.
\<close>

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
      define b where "b = balance state"
  define f where " f = current_flow state"
  obtain s t P where stp_def: "(s,t,P) = the (get_source_target_path f b)" 
    by (metis prod_cases3)
  have stp_prop: "Some (s,t,P) = get_source_target_path f b"
    apply(rule SSP_call_3_condE[OF 3])
    using b_def f_def stp_def by simp
  define \<gamma> where " \<gamma> = real_of_ereal (min (min (b s) (- b t)) (Rcap f (set P)))"
  define f' where "f' = augment_edges f \<gamma> P"
  define b' where "b' = (\<lambda> v. if v = s then b s - \<gamma> else
                                        if v = t then b t + \<gamma> else b v)"

  have s_in_V: "s \<in> \<V>"
      by(rule get_source_target_path_axioms(1)[of f b s t P], rule SSP_call_3_condE[OF 3])
        (simp add: b_def stp_def stp_prop f_def)

  have t_in_V: "t \<in> \<V>"
    by(rule get_source_target_path_axioms(3)[of f b s t P], rule SSP_call_3_condE[OF 3])
      (simp add: b_def stp_def stp_prop f_def)

  have resreach_f_s_t:"resreach_cap f L s t"
    using stp_prop 
    by (auto intro: get_source_target_path_axioms(5)[of f b s t P])

  have b_s_pos: "b s > L "
    by(rule get_source_target_path_axioms(2)[of f b s t P], rule SSP_call_3_condE[OF 3])
      (simp add: stp_prop)

  have int_b_s: "is_integral (b s)"
    using is_integral_balanceE[of b] b_def invar_integral_def less.prems  is_integral_def  s_in_V 
    by auto

  have "abs (b s) \<ge> 1" 
    using b_s_pos int_b_s is_integral_def by auto

  have t_is_neg: "b t < - real L"
    using  get_source_target_path_axioms(4)[of f b s t P] SSP_call_3_condE[OF 3]
    by (simp add: stp_prop)

  have int_b_s: "is_integral (b t)"
    using is_integral_balanceE[of b]  b_def invar_integral_def less.prems  is_integral_def  t_in_V 
    by auto

  have "abs (b t) \<ge> L" 
    using int_b_s is_integral_def t_is_neg 
    by simp

  have resreach_f_s_t:"resreach_cap f L s t"
    using stp_prop by (auto intro: get_source_target_path_axioms(5)[of f b s t P])

  have "is_integral (b s)"
    unfolding b_def
    using invar_integral_def is_integral_balanceE  is_integral_def less.prems s_in_V 
    by fast
   
  moreover have "is_integral (- b t)"
    by (simp add: int_b_s is_integral_neg)

  ultimately have "is_integral (min (b s) (- b t))"
    by(rule integral_min) 

  moreover have "is_integral (real_of_ereal (Rcap f (set P)))"
    using less.prems get_source_target_path_axioms(6)[of f b s t P]  stp_prop 
    by(auto intro!: Rcap_integral intro:  augpath_cases[of f P] 
             elim!: invar_integralE is_min_pathE is_s_t_pathE  simp add: f_def)
    
  ultimately have integral_gamma: "is_integral \<gamma>"
    using integral_min
    by (simp add: min_def \<gamma>_def)

  have P_augpath:"augpath f P"
    using get_source_target_path_axioms(6)[of f b s t P] stp_prop 
    by (auto elim: is_min_pathE is_s_t_pathE)

  have Rcap_pos: "(Rcap f (set P)) > L"
    using stp_prop get_source_target_path_axioms(7)[of f b s t P ] resreach_f_s_t 
    by auto

  have gamma_pos: "\<gamma> > L"
    using Rcap_pos t_is_neg b_s_pos  P_augpath augpath_rcap 
    by(auto simp add: min_def ereal_less_real_iff \<gamma>_def)

  have s_red: "abs (b' s) < abs (b s)"
    using gamma_pos b_s_pos 
    by(auto simp add: b'_def  min_def ereal_less_real_iff \<gamma>_def)

  have t_red: "abs (b' t) < abs (b t)"
    using gamma_pos t_is_neg 
    by(auto simp add: b'_def  min_def ereal_less_real_iff \<gamma>_def)
   
  show ?thesis 
    proof(cases rule: SSP_call_3_cond_SSP_dom[OF 3])
      case 1
      have invar_integral:"invar_integral (SSP_upd3 state)"
        using less 3 by(auto intro: invar_integral_holds_4)
      hence int_b: "is_integral_balance (balance (SSP_upd3 state))"
        unfolding invar_integral_def by simp 
      have bs:"\<bar>balance (SSP_upd3 state) s\<bar> \<le> \<bar>balance state s\<bar>"
          unfolding  \<gamma>_def  b_def f_def 
          using sym[OF  stp_prop[simplified f_def b_def ]] s_red  
          unfolding b'_def  SSP_upd3_def Let_def  \<gamma>_def  b_def f_def 
          by simp
      have bt: "\<bar>balance (SSP_upd3 state) t\<bar> \<le> \<bar>balance state t\<bar>"
          using     sym[OF  stp_prop[simplified f_def b_def ]] t_red  
          unfolding b'_def  SSP_upd3_def Let_def \<gamma>_def  b_def f_def  by auto    
      have bv:"v \<in> \<V> \<Longrightarrow> \<bar>balance (SSP_upd3 state) v\<bar> \<le> \<bar>balance state v\<bar>"for v
          using bs bt 
          unfolding b'_def  SSP_upd3_def Let_def \<gamma>_def  b_def f_def 
          by(auto simp add: bt sym[OF  stp_prop[simplified f_def b_def ]]) 
       
      have abs_less:"bABSnat (balance (SSP_upd3 state)) < bABSnat (balance state)"
        using int_b less(2) invar_integral_def[of state] bv s_in_V sym[OF stp_prop[simplified f_def b_def]]
        s_red unfolding b'_def  SSP_upd3_def Let_def \<gamma>_def  b_def f_def (*takes some time*)
        by (auto intro: bABSnat_mono[of _ _ s])   
       
      show ?case 
        by(rule less(1)[OF abs_less invar_integral])
    qed
  qed
qed

text \<open>The impossibility of arbitrary small decreases is essential to the argument above.
For general real values, such changes are not forbidden and thus those settings frequently
 suffer from non-termination. Not even convergence to the correct solution is guaranteed.
\<close>

text \<open>The $notyetterm$ flag set tells us that the second condition regarding branching applies.\<close>

lemma abort_SSP_ret_cond:
  assumes "SSP_dom state" "invar_balance state" "return (SSP state) = notyetterm"
  shows "SSP_ret_2_cond (SSP state)" using assms(2-3)
proof(induction rule: SSP_induct[OF assms(1)])
  case IH: (1 state)
  have "SSP_ret_1_cond state \<Longrightarrow> SSP_ret_2_cond (local.SSP state)"
      using IH(4) IH(1) SSP_simps(2)
      by(auto simp add: SSP_ret1_def)
  moreover have "SSP_ret_2_cond state \<Longrightarrow> SSP_ret_2_cond (local.SSP state)"
      unfolding Let_def using IH.hyps 
      by(auto intro!: SSP_ret_2_condI 
               split: if_splits 
               elim!: SSP_ret_2_condE 
            simp add: SSP.psimps IH.hyps)
  moreover have "SSP_call_3_cond state \<Longrightarrow> SSP_ret_2_cond (local.SSP state)"
       using IH.IH IH.hyps IH.prems(1) IH.prems(2) SSP_simps(1)[of state] invar_balance_holds_4[of state]
       by auto     
  ultimately show ?case
    by(auto intro: SSP_cases)
qed

subsubsection \<open>Third Invariant: Optimality\<close>

text \<open>The previous invariants were of rather technical importance.
After those preparations we finally come to the conceptually interesting part based on Theorem 9.11.
\<close>

text \<open>As usual, the easy cases first.\<close>

lemma invar_opt_holds_1[invar_holds_intros]:
 "\<lbrakk>SSP_ret_1_cond state; invar_opt state\<rbrakk> \<Longrightarrow> invar_opt (SSP_ret1 state)"
  by (auto simp:SSP_ret1_def invar_opt_def )

lemma invar_opt_holds_2[invar_holds_intros]: 
"\<lbrakk>SSP_ret_2_cond state; invar_opt state\<rbrakk> \<Longrightarrow> invar_opt (SSP_ret2 state)"
  by (auto simp:SSP_ret2_def invar_opt_def)

text \<open>Now we show that the current flow $f$ is always optimum for the difference 
$b - b'$ where $b$ is the initial and $b'$ the current balance. \<close>

lemma invar_opt_holds_4[invar_holds_intros]: 
  assumes "SSP_call_3_cond state"  "invar_opt state"
  shows "invar_opt (SSP_upd3 state)"
proof-
  define b where "b = balance state"
  define f where " f = current_flow state"
  obtain s t P where stp_def: "(s,t,P) = the (get_source_target_path f b)" 
    by (metis prod_cases3)
  have stp_prop: "Some (s,t,P) = get_source_target_path f b"
    apply(rule SSP_call_3_condE[OF assms(1)])
    using b_def f_def stp_def by simp
  define \<gamma> where " \<gamma> = real_of_ereal (min (min (b s) (- b t)) (Rcap f (set P)))"
  define f' where "f' = augment_edges f \<gamma> P"
  define b' where "b' = (\<lambda> v. if v = s then b s - \<gamma> else
                                        if v = t then b t + \<gamma> else b v)"

  have s_in_V: "s \<in> \<V>"
    by(rule get_source_target_path_axioms(1)[of f b s t P], rule SSP_call_3_condE[OF assms(1)])
      (simp add: b_def stp_def stp_prop f_def)

  have t_in_V: "t \<in> \<V>"
    by(rule get_source_target_path_axioms(3)[of f b s t P], rule SSP_call_3_condE[OF assms(1)])
      (simp add: b_def stp_def stp_prop f_def)

  have resreach_f_s_t:"resreach_cap f L s t"
   using stp_prop by (auto intro: get_source_target_path_axioms(5)[of f b s t P])

  have P_augpath:"augpath f P"
    using get_source_target_path_axioms(6)[of f b s t P] stp_prop
    by(auto elim: is_min_pathE is_s_t_pathE)

  have Rcap_pos: "(Rcap f (set P)) > L"
    using stp_prop get_source_target_path_axioms(7)[of f b s t P]  resreach_f_s_t 
    by simp

  have b_s_pos: "b s > L "
    by(rule get_source_target_path_axioms(2)[of f b s t P], rule SSP_call_3_condE[OF assms(1)])
      (simp add: stp_prop)

  have t_is_neg: "b t < - real L"
    by(rule get_source_target_path_axioms(4)[of f b s t P], rule SSP_call_3_condE[OF assms(1)])
      (simp add: stp_prop)

  have gamma_pos: "\<gamma> > L"
    using Rcap_pos t_is_neg b_s_pos  P_augpath augpath_rcap
    by(auto simp add: \<gamma>_def  min_def ereal_less_real_iff )
 
  have t_last_P: "t = sndv (last P)" and s_hd_P: "s = fstv (hd P)"
    using get_source_target_path_axioms(6)[OF sym[OF stp_prop]] 
    by(auto elim: is_min_pathE is_s_t_pathE)

  have s_neq_t: "s \<noteq> t"
    using stp_prop get_source_target_path_axioms(1-6)[OF sym[OF stp_prop]]
    by (auto elim!: SSP_call_3_condE[OF assms(1)])

  have opt_flow: "is_Opt (\<lambda>v. \<b> v - b v) f"
    using assms(2) by(simp add: invar_opt_def b_def f_def)

  have min_path: "is_min_path (current_flow state) s t P"
    using stp_prop get_source_target_path_axioms(1-6)[OF sym[OF stp_prop]] f_def by auto

  have flow_is: "current_flow (SSP_upd3 state) = augment_edges (current_flow state) \<gamma> P"
    using  sym[OF stp_def[simplified f_def b_def]]
    by (auto simp add: SSP_upd3_def  \<gamma>_def  f_def b_def Let_def)

  show ?thesis
    unfolding invar_opt_def
    apply(rule path_aug_opt_pres[of s t "\<lambda> v. \<b> v  - b v" f \<gamma> P])
    using P_augpath  s_neq_t opt_flow  gamma_pos
          min_path flow_is sym[OF stp_prop[simplified b_def f_def]]   
    by(auto intro: path_aug_opt_pres[of s t "\<lambda> v. \<b> v  - b v" f \<gamma> P] split: if_split 
          simp add: ereal_real  SSP_upd3_def \<gamma>_def Let_def b_def s_hd_P t_last_P f_def)
   qed

text \<open>Let's summarize those three lemmas.\<close>

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

text \<open>There is just one possibility for telling $success$.\<close>

lemma success:
  assumes "(SSP_dom state)"  "return (SSP state) = success"
    shows "SSP_ret_1_cond (SSP state)"
  using assms(2)
proof(induction rule: SSP_induct[OF assms(1)])
  case (1 state)
  note 11 = this
  then show ?case
  proof(cases rule: SSP_cases[of state])
    case 1
    then show ?thesis 
    apply(rule SSP_ret_1_condE, simp)
      by(auto split: option.split if_split 
           simp add: Let_def SSP_ret_1_cond_def SSP.psimps 11)
  next
    case 2
    then show ?thesis using 11 
      apply(subst(asm) SSP_simps(3), simp, simp)
      unfolding SSP_ret2_def by simp
  qed (auto simp add: SSP_simps(1))
qed

text \<open>Similarly, $notyetterm$ may just appear in connection to the second condition.\<close>

lemma notyetterm:
  assumes "(SSP_dom state)""return (SSP state) = notyetterm"
    shows "SSP_ret_2_cond (SSP state)"
  using assms(2)
proof(induction rule: SSP_induct[OF assms(1)])
  case (1 state)
  note 11 = this
  then show ?case
  proof(cases rule: SSP_cases[of state])
    case 1
    then show ?thesis 
      apply(rule SSP_ret_1_condE, simp) 
      using 11 SSP_ret1_def 
      apply(subst (asm) SSP_simps(2), simp, simp)
      unfolding SSP_ret1_def by simp
  next
    case 2
    then show ?thesis
      apply(subst  SSP_simps(3), simp, simp)
      unfolding SSP_ret2_def SSP_ret_2_cond_def using 11 by auto
  qed (auto simp add: SSP_simps(1))
qed

text \<open>The $failure$ flag is never set. (Actually, that is left to the outer loop then.)\<close>

lemma  never_failure:  
  assumes "SSP_dom state"
  shows   "return (SSP state) \<noteq> failure"
proof(induction rule: SSP_induct[OF assms])
  case (1 state)
  note 11 = this
  then show ?case
  proof(cases rule: SSP_cases[of state])
    case 1
    then show ?thesis using 11 
      apply(subst SSP_simps(2))
      unfolding SSP_ret1_def by auto
  next
    case 2
    then show ?thesis using 11
      apply(subst SSP_simps(3))
      unfolding SSP_ret2_def by auto
  qed (subst SSP_simps(1), simp)
qed

text \<open>We show total correctness for an initial state satisfying all three invariants.
By integrality ($invar_integral$), we get termination.
 Moreover, the flag was set to $success$, and thus $b' = 0$. 
We obtain optimality for the flow $f$ for $b - b' = b$.
\<close>

theorem total_correctness1:
  assumes "final = SSP state"
          "invar_opt state"
          "invar_integral state"
          "invar_balance state"
  shows   "return final = success \<Longrightarrow> is_Opt \<b> (current_flow final)"
proof-
  have SSP_dom: "SSP_dom state"
    by(rule integral_balance_termination[OF assms(3)])
  show "return final = success \<Longrightarrow> is_Opt \<b> (current_flow final)"
  proof-
    assume asm:"return final = success"
    have ret_1:"SSP_ret_1_cond final" 
      unfolding assms(1)
      by( auto intro: success simp add: SSP_dom assms(2) asm[simplified assms(1)])
    have invar_opt:"invar_opt final" 
      unfolding assms(1)
      using assms SSP_dom  by (auto intro: invar_opt_holds)
    show "is_Opt \<b> (current_flow final)"
      apply(rule SSP_ret_1_condE[of final, OF ret_1])
      using invar_opt
      unfolding invar_opt_def zero_balance_def is_Opt_def isbflow_def ex_def 
      by simp
  qed
qed

text \<open>We strengthen the previous result for the $k=0$ case.
The part for $success$ follows immediately.
Similarly for $failure$, since that is left to the outer loop.
Things get more sophisticated for $notyetterm$ which in fact is a completeness statement.
We assume that after termination of $SSP$, the $notyetterm$ flag was set.
This indicates that another iteration of the outer loop should be done.
However, we can't do that since $k$ is already zero.
From the axioms we conclude that there are no $s$, $t$ and $p$ suitable for augmentation.
Because of $b \neq 0$ there is some source $s$ still active where no target is reachable from.
Now, recall some results from the very first theory on residual graphs.
Consider the residual cut $X$ around $s$. 
If there was a $b$-flow $f'$, then the sum of all balances within $X$ is less or equal than the cut
 capacity.
On the other hand we know that the residual cut is saturated, i.e. its capacity equals
 the sum of $b - b'$ over $X$.
But this is a contradiction since for $s$ we have $b' \; s >0$ and all $b - b'$ values are non-negative.
\<close>

theorem total_correctness:
  assumes "final = SSP state"
          "invar_opt state"
          "invar_integral state"
          "invar_balance state"
          "L = 0"
  shows   "return final = success \<Longrightarrow> is_Opt \<b> (current_flow final)"
          "return final = notyetterm \<Longrightarrow> \<nexists> f. f is \<b> flow"
          "return final = failure \<Longrightarrow> False"
proof-
  have SSP_dom: "SSP_dom state"
    by(rule integral_balance_termination[OF assms(3)])
  show "return final = success \<Longrightarrow> is_Opt \<b> (current_flow final)"
  proof-
    assume asm:"return final = success"
    have ret_1:"SSP_ret_1_cond final" unfolding assms(1)
      by( auto intro: success simp add: SSP_dom assms(2) asm[simplified assms(1)])
    have invar_opt:"invar_opt final" 
      unfolding assms(1)
      by (auto intro: invar_opt_holds simp add: assms SSP_dom )
    show "is_Opt \<b> (current_flow final)"
      apply(rule SSP_ret_1_condE[of final, OF ret_1])
      using invar_opt
      unfolding invar_opt_def zero_balance_def
      unfolding is_Opt_def isbflow_def ex_def by simp
  qed
  show "return final = notyetterm \<Longrightarrow> \<nexists> f. f is \<b> flow"
  proof-
    assume asm:"return final = notyetterm"
    have ret_1:"SSP_ret_2_cond final" unfolding assms(1)
      apply(rule notyetterm, rule SSP_dom)
      using asm is_balance_b unfolding assms(1) invar_balance_def is_balance_def by simp+
    have invar_opt:"invar_opt final" unfolding assms(1)
      by(rule invar_opt_holds, auto simp add: assms SSP_dom)
    have invar_integral:"invar_integral final" unfolding assms(1)
      by(rule invar_integral_holds, auto simp add: assms SSP_dom)
    obtain  b \<f> where bsf_prop:" b = balance final" "\<not> zero_balance b"
              "\<f> = current_flow final" 
      using SSP_ret_2_condE ret_1 by blast
    hence None:"get_source_target_path \<f> b = None" 
      using SSP_ret_2_condE ret_1 get_source_target_path_axioms by auto
    have is_Opt_term:"is_Opt (\<lambda> v. \<b> v -  b v) \<f>" 
      using invar_opt bsf_prop unfolding invar_opt_def
       by simp
    have b_is_balance: "is_balance b"
      unfolding bsf_prop assms
      using assms invar_balance_def SSP_dom 
      by (auto intro: invar_balance_holds[simplified invar_balance_def])
    then obtain s where s_prop: "s \<in> \<V>" "b s > 0"
      using  bsf_prop(2)
      unfolding zero_balance_def is_balance_def
      using \<V>_finite sum_zero_not_all_zero by blast

    have rescutsat:"sum (\<lambda> v. \<b> v -  b v) (Rescut \<f> s) = Cap (Rescut \<f> s)"
      using is_Opt_term s_prop  flow_saturates_res_cut Rescut_around_in_V 
      unfolding is_Opt_def
      by simp

    have sumbb:"sum (\<lambda> v. \<b> v -  b v) (Rescut \<f> s) = 
         sum \<b> (Rescut \<f> s) - sum b (Rescut \<f> s)"
      using sum_subtractf by auto

    have no_augcycle: "\<nexists>C. augcycle \<f> C" 
      using is_Opt_term min_cost_flow_no_augcycle by blast

    have no_s_t_path: "\<nexists> t P. is_s_t_path \<f> s t P \<and> s \<in> \<V> \<and> t \<in> \<V> \<and> b t < 0 "
    proof(rule ccontr)
      assume "\<not> (\<nexists> t P. is_s_t_path \<f> s t P \<and> s \<in> \<V> \<and> t \<in> \<V> \<and> b t < 0)"
      then obtain t P where tp: "is_s_t_path \<f> s t P" "s \<in> \<V>" "t \<in> \<V>" "b t < 0" by auto
      thus False
        using None assms(5) no_augcycle  get_source_target_path_axioms(9)[of \<f> s t P b] tp
              augpath_cap_to_resreach is_s_t_path_def s_prop(2) zero_ereal_def 
        unfolding is_min_path_def is_s_t_path_def  augpath_def 
         by force
     qed

    have no_augcycle: "\<nexists> C. augcycle \<f> C"
      using is_Opt_term min_cost_flow_no_augcycle by presburger

    have sumb0:"sum b (Rescut \<f> s) > 0"
    proof(rule ccontr)
      assume asm:" \<not> 0 < sum b (Rescut \<f> s)"
      show False
      proof(cases "0 = sum b (Rescut \<f> s)")
        case True
        have "s \<in> (Rescut \<f> s)" "b s > 0"
           by (fastforce simp add: s_prop(2) Rescut_def)+
         then obtain t where t_prop:"t \<in> (Rescut \<f> s)" "b t < 0"
           using sum_pos2[of "Rescut \<f> s" s b] finite_Rescut[OF  s_prop(1)]
           by(force simp add:  True)
         hence rsf:"resreach \<f>  s t"  
           using s_prop(2) by (fastforce simp add: Rescut_def)
         have tV: "t \<in> \<V>" 
           using Rescut_around_in_V s_prop(1) t_prop(1) by blast
         then obtain p where p_prop: "augpath \<f> p" "set p \<subseteq> \<EE>"
                                   "fstv (hd p) = s" "sndv (last p) = t" 
          using subset_mono_awalk' resreach_imp_augpath[of \<f> s t] rsf
           by (auto intro: augpathI )
         then obtain p' where p'_prop: "prepath  p'" "set p' \<subseteq> set p"
                                   "fstv (hd p') = s" "sndv (last p') = t" "distinct p'" "p' \<noteq> []"
           by (metis dual_order.refl prepath_drop_cycles augpath_def prepath_def)
         hence "augpath \<f> p'"
           using p_prop(1) unfolding augpath_def augpath_def Rcap_def 
           by auto
          hence "is_s_t_path \<f> s t p'"
            unfolding is_s_t_path_def using p'_prop p_prop by simp
         thus False using no_s_t_path tV t_prop(2) s_prop(1)  s_prop(2) by auto
      next
        case False
        hence "0 > sum b (Rescut \<f> s)" using asm by simp
        hence "sum b (Rescut \<f> s) < 0" by simp
        then obtain t where t_prop:"t \<in> (Rescut \<f> s)" "b t < 0"
        by (meson less_le_not_le linorder_linear sum_nonneg)
        hence rsf:"resreach \<f>  s t" unfolding Rescut_def 
          using s_prop(2) by fastforce
        have tV: "t \<in> \<V>" using t_prop(1) Rescut_around_in_V s_prop by auto
         then obtain p where p_prop: "augpath \<f> p" "set p \<subseteq> \<EE>"
                                   "fstv (hd p) = s" "sndv (last p) = t" 
            unfolding augpath_def prepath_def
             using subset_mono_awalk' augpath_def prepath_def resreach_imp_augpath[of \<f> s t] rsf
           by auto
        then obtain p' where p'_prop: "prepath  p'" "set p' \<subseteq> set p"
                                   "fstv (hd p') = s" "sndv (last p') = t" "distinct p'" "p' \<noteq> []"
           by (metis dual_order.refl prepath_drop_cycles augpath_def prepath_def)
         hence "augpath \<f> p'"
           using p_prop(1) unfolding augpath_def  augpath_def Rcap_def  
           by auto
          hence "is_s_t_path \<f> s t p'"
            unfolding is_s_t_path_def using p'_prop p_prop by simp
         thus False using no_s_t_path tV t_prop(2) s_prop(1)  s_prop(2) by auto
      qed
    qed

    text \<open>This follows since $b'$ is not 0 yet.\<close>

    hence sumbb':"sum (\<lambda> v. \<b> v -  b v) (Rescut \<f> s) < sum \<b> (Rescut \<f> s)" using sumbb by simp

    show " \<nexists>f. f is \<b> flow"
    proof
      assume "\<exists>f. f is \<b> flow"
      then obtain f where f_prop:"f is \<b> flow" by auto

      text \<open>But if there was such a flow, then then sum of balances has to be below cut capacity.\<close>

      have "sum \<b> (Rescut \<f> s) \<le> Cap (Rescut \<f> s)"
        using f_prop s_prop  flow_less_cut[of f] Rescut_around_in_V
        unfolding is_Opt_def 
        by force
      thus False using sumbb sumb0 rescutsat 
        using  ereal_less_eq(3)[of "sum \<b> (Rescut \<f> s)" "(\<Sum>v\<in>Rescut \<f> s. \<b> v - b v)"] 
        by simp
    qed
  qed
  show "return final = failure \<Longrightarrow> False"
  proof-
    assume "return final = failure"
    moreover have "return final \<noteq> failure" unfolding  assms(1)
      by(auto simp add: never_failure integral_balance_termination assms(3))
    ultimately show False by simp
  qed
qed

end

subsection \<open>Locale for the Outer Loop\<close>

text \<open>Now we do the locale related to the outer loop.
 It is concerned with monitoring the inner loop's results, decreasing the threshold value $L$ and
deciding non-existence of a $b$-flow.
Again, the locale axioms assume a function for obtaining sources, targets and paths.
In there, $L$ is a parameter.
Furthermore, we assume \textit{conservative weights}. 
This means that there are no negative cycles in the beginning.
We use this for showing the third invariant for the initial state.
\<close>

locale Scaling = 
algo where fst = fst for fst::"'edge_type \<Rightarrow> 'a"+
fixes get_source_target_path
            ::"nat \<Rightarrow> ('edge_type \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real)  \<Rightarrow> ('a \<times> 'a \<times> 'edge_type Redge list) option"
   assumes get_source_target_path_axioms:
     " \<And> b f s t P (k::nat). get_source_target_path k f b = Some (s,t,P) \<Longrightarrow>
                     s \<in> \<V>"
     " \<And> b f s t P (k::nat). get_source_target_path k f b = Some (s,t,P) \<Longrightarrow>
                     b s > real k"
     " \<And> b f s t P (k::nat). get_source_target_path k f b = Some (s,t,P) \<Longrightarrow>
                     t \<in> \<V>"
     " \<And> b f s t P (k::nat). get_source_target_path k f b = Some (s,t,P) \<Longrightarrow>
                     b t < - real k"
     " \<And> b f s t P (k::nat). get_source_target_path k f b = Some (s,t,P) \<Longrightarrow>
                     resreach_cap f k s t"
     " \<And> b f s t P (k::nat). get_source_target_path k f b = Some (s,t,P) \<Longrightarrow>
                      is_min_path f s t P"
     " \<And> b f s t P (k::nat). get_source_target_path k f b = Some (s,t,P) \<Longrightarrow>
                      Rcap f (set P) > k"
     " \<And> b f s t P (L::nat). (\<nexists> C. augcycle f C) \<Longrightarrow> is_min_path f s t P \<Longrightarrow> s \<in> \<V> \<Longrightarrow> t \<in> \<V> \<Longrightarrow> L > 0 \<Longrightarrow>
                    b s > real L \<Longrightarrow> b t < - real L \<Longrightarrow>
                    resreach_cap f L s t \<Longrightarrow> Rcap f (set P) > L \<Longrightarrow>
                    (\<exists> s t P. get_source_target_path L f b = Some (s,t,P))"

     " \<And> b f s t P (L::nat). (\<nexists> C. augcycle f C) \<Longrightarrow>is_s_t_path f s t P \<Longrightarrow> s \<in> \<V> \<Longrightarrow> t \<in> \<V> \<Longrightarrow> L = 0 \<Longrightarrow>
                    b s > real L \<Longrightarrow> b t < - real L \<Longrightarrow>
                    resreach_cap f L s t \<Longrightarrow> Rcap f (set P) > L \<Longrightarrow>
                    (\<exists> s t P. get_source_target_path L f b = Some (s,t,P))"

and conservative_weights: "\<nexists> C. closed_w (make_pair ` \<E>) (map make_pair C) \<and> set C \<subseteq> \<E>
                                 \<and> foldr (\<lambda> e acc. acc + \<c> e) C 0 < 0"

begin

lemma Scaling_from_this[simp]: "Scaling snd  create_edge \<u> \<c> \<E> \<b> fst get_source_target_path" 
  by (simp add: Scaling_axioms)

text \<open>For all $L$.\<close>

lemma SSP_from_this[simp]: "\<And> L . SSP snd create_edge  \<u> \<c> \<E>  \<b> fst L (get_source_target_path L)"
  using Scaling_axioms unfolding Scaling_def Scaling_axioms_def SSP_axioms_def SSP_def
  by(auto simp add: get_source_target_path_axioms)

subsubsection \<open>Function Setup\<close>

text \<open>The inner loop is parametrized by some threshold $L$.\<close>

definition "ssp (L::nat) = SSP.SSP snd \<u> \<E> fst (get_source_target_path L)"

definition "ssp_dom L  state = SSP.SSP_dom snd \<u> \<E> fst (get_source_target_path L) state"

text \<open>The outer loop is realized by recursion on $l$. The threshold value $L$ is then $2^l$.
If the inner loop  already successful, then a minimum cost flow was found.
If not, then we either have to decrease $L$ or there is no $b$-flow.
Please note that due to the locale approach, the threshold variable $L$ 
is not needed to be incorporated into the program state.
\<close>

function  (domintros) Scaling::"nat \<Rightarrow> ('a, 'edge_type) Algo_state \<Rightarrow> ('a, 'edge_type) Algo_state" where
"Scaling l state = (let state' = ssp (2^l-1) state in 
                   (case return state' of
                     success \<Rightarrow> state' 
                     | failure \<Rightarrow> state'
                     | notyetterm \<Rightarrow> (
                      if l = 0 then state' \<lparr> return:= failure\<rparr>
                               else Scaling (l-1) state')))"
  by pat_completeness simp

text \<open>As in the previous locale, we decompose the function into conditioned execution paths.\<close>

definition "Scaling_ret_1_cond k state =
             (let state' = ssp (2^k-1) state in 
                   (case return state' of
                     success \<Rightarrow> True
                     | failure \<Rightarrow> False
                     | notyetterm \<Rightarrow> (
                      if k = 0 then False
                               else False)))"

text \<open>Technicalities.\<close>

lemma Scaling_ret_1_condI:
    "state' = ssp (2^k-1) state \<Longrightarrow> return state' = success \<Longrightarrow> Scaling_ret_1_cond k state"
  unfolding Scaling_ret_1_cond_def by simp

lemma Scaling_ret_1_condE: "Scaling_ret_1_cond k state \<Longrightarrow>
                          (\<And> state'. state' = ssp (2^k-1) state \<Longrightarrow> return state' = success \<Longrightarrow> P)
                            \<Longrightarrow> P"
  by(cases "return (ssp (2 ^ k - 1) state)")
    (auto simp add: Scaling_ret_1_cond_def Let_def) 
  
text \<open>Failure.\<close>

definition "Scaling_ret_2_cond k state = 
             (let state' = ssp (2^k-1) state in 
                   (case return state' of
                     success \<Rightarrow> False
                     | failure \<Rightarrow> True
                     | notyetterm \<Rightarrow> (
                      if k = 0 then False
                               else False)))"

lemma Scaling_ret_2_condI:
    "state' = ssp (2^k-1) state \<Longrightarrow> return state' = failure \<Longrightarrow> Scaling_ret_2_cond k state"
  unfolding Scaling_ret_2_cond_def by simp

lemma Scaling_ret_2_condE:
 "\<lbrakk>Scaling_ret_2_cond k state;
      (\<And> state'. \<lbrakk>state' = ssp (2^k-1) state; return state' = failure\<rbrakk> \<Longrightarrow> P)\<rbrakk>
   \<Longrightarrow> P"
  by(cases "return (ssp (2 ^ k - 1) state)")
    (auto simp add: Scaling_ret_2_cond_def Let_def) 

definition "Scaling_ret_3_cond k state =
             (let state' = ssp (2^k-1) state in 
                   (case return state' of
                     success \<Rightarrow> False
                     | failure \<Rightarrow> False
                     | notyetterm \<Rightarrow> (
                      if k = 0 then True
                               else False)))"

lemma Scaling_ret_3_condI: 
 "\<lbrakk>state' = ssp (2^k-1) state; return state' = notyetterm; k = 0\<rbrakk>
    \<Longrightarrow> Scaling_ret_3_cond k state"
  by(simp add: Scaling_ret_3_cond_def)

lemma Scaling_ret_3_condE:
   "Scaling_ret_3_cond k state \<Longrightarrow>
   (\<And> state'. \<lbrakk>state' = ssp (2^k-1) state; return state' = notyetterm;  k = 0\<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
   P"
  by(cases "return (ssp (2 ^ k - Suc 0) state)", all \<open>cases "k = 0"\<close>)
    (auto simp add: Scaling_ret_3_cond_def Let_def) 

definition "Scaling_call_4_cond k state =
             (let state' = ssp (2^k-1) state in 
                   (case return state' of
                     success \<Rightarrow> False
                     | failure \<Rightarrow> False
                     | notyetterm \<Rightarrow> (
                      if k = 0 then False
                               else True)))"

lemma Scaling_call_4_condI: "state' = ssp (2^k-1) state \<Longrightarrow> return state' = notyetterm \<Longrightarrow> k > 0 
                             \<Longrightarrow> Scaling_call_4_cond k state"
  unfolding Scaling_call_4_cond_def by simp

lemma Scaling_call_4_condE:
   "Scaling_call_4_cond k state \<Longrightarrow>
    (\<And> state'. \<lbrakk>state' = ssp (2^k-1) state; return state' = notyetterm;  k > 0\<rbrakk> \<Longrightarrow> P) 
   \<Longrightarrow> P"
  by(cases "return (ssp (2 ^ k - Suc 0) state)", all \<open>cases "k = 0"\<close>)
    (auto simp add: Scaling_call_4_cond_def Let_def) 

text \<open>Again, we can introduce a predicate by analyzing the taken execution path.\<close>

lemma Scaling_cases:
  assumes  "Scaling_ret_1_cond k state \<Longrightarrow> P"
           "Scaling_ret_2_cond k state \<Longrightarrow> P"
           "Scaling_ret_3_cond k state \<Longrightarrow> P"
           "Scaling_call_4_cond k state \<Longrightarrow> P"
    shows  P
proof-
  have "Scaling_ret_1_cond k state  \<or> Scaling_ret_2_cond k state \<or>
        Scaling_ret_3_cond k state  \<or> Scaling_call_4_cond k state"
    by (auto simp add: Scaling_ret_1_cond_def Scaling_ret_2_cond_def
                       Scaling_ret_3_cond_def Scaling_call_4_cond_def
                       Let_def
           split: list.split_asm option.split_asm if_splits return.splits)
  then show ?thesis
    using assms
    by auto
qed

text \<open>Modifications by the function.\<close>

definition "Scaling_ret1 k state =
                  (let state' = ssp (2^k-1) state in state')"

definition "Scaling_ret2 k state =
                  (let state' = ssp (2^k-1) state in state')"

definition "Scaling_ret3 k state = 
                  (let state' = ssp (2^k-1) state in state'\<lparr> return:= failure\<rparr>)"


definition "Scaling_upd4 k state = 
                  (let state' = ssp (2^k-1) state in  state')"


declare[[simp_trace_depth_limit=1000]]

text \<open>Conditional simplification.\<close>

lemma Scaling_simps:
  assumes "Scaling_dom (k,state)" 
  shows "Scaling_call_4_cond k state  \<Longrightarrow> Scaling k state = Scaling (k-1) (Scaling_upd4 k state)"
        "Scaling_ret_1_cond k state  \<Longrightarrow> Scaling k state = Scaling_ret1 k state"
        "Scaling_ret_2_cond k state  \<Longrightarrow> Scaling k state = Scaling_ret2 k state"
        "Scaling_ret_3_cond k state  \<Longrightarrow> Scaling k state = Scaling_ret3 k state"  
  unfolding Scaling_upd4_def     
  by (auto    elim!: Scaling_call_4_condE
           simp add: Scaling.psimps[OF assms]
                     Scaling_ret_1_cond_def Scaling_ret1_def
                     Scaling_ret_2_cond_def Scaling_ret2_def
                     Scaling_ret_3_cond_def Scaling_ret3_def
                     Scaling_call_4_cond_def Scaling_upd4_def
              split: list.splits return.splits if_splits)

text \<open>An induction principle.\<close>

lemma Scaling_induct: 
  assumes "Scaling_dom (k,state)"
  assumes "\<And>k state. \<lbrakk>Scaling_dom (k, state);
                      Scaling_call_4_cond k state \<Longrightarrow> P (k-1) (Scaling_upd4 k state)\<rbrakk>
          \<Longrightarrow> P k state"
  shows "P k state"
  apply(rule Scaling.pinduct[OF assms(1)])
  apply(rule assms(2))
  unfolding Scaling_upd4_def 
  by (auto intro: assms(2) elim!: Scaling_call_4_condE)

subsubsection \<open>Preservation of Invariants\<close>

text \<open>We unite all three invariants.\<close>

definition "invar_comb  state = (invar_balance state \<and> invar_integral state \<and> invar_opt state)"

text \<open>Introduction and elimination lemmas.\<close>

lemma invar_combE: "invar_comb state \<Longrightarrow> 
                    (invar_balance state \<Longrightarrow> invar_integral state \<Longrightarrow> invar_opt state \<Longrightarrow> P) \<Longrightarrow> 
                    P"
  unfolding invar_comb_def by simp

lemma invar_combI: "invar_balance state \<Longrightarrow> invar_integral state \<Longrightarrow> invar_opt state \<Longrightarrow> invar_comb state"
  unfolding invar_comb_def by simp

named_theorems invar_holds_intros

text \<open>Preservation during recursion.\<close>
thm  SSP.invar_balance_holds[of   _ _ _ _ _ _ _  "2^k -1", OF SSP_from_this]

lemma invar_comb_holds_4[invar_holds_intros]: 
      "\<lbrakk>Scaling_call_4_cond k state; invar_comb  state \<rbrakk>  \<Longrightarrow> invar_comb(Scaling_upd4 k state)"
  unfolding Scaling_upd4_def Let_def
  apply(rule Scaling_call_4_condE, simp, rule invar_combI)
  apply(all \<open>rule invar_combE[of state]\<close>)
  using  SSP.invar_balance_holds[of   _ _ _ _ _ _ _  "2^k -1", OF SSP_from_this, of state]
           SSP.invar_integral_holds[of   _ _ _ _ _ _ _  "2^k -1", OF SSP_from_this, of state]
           SSP.invar_opt_holds[of   _ _ _ _ _ _ _  "2^k -1", OF SSP_from_this, of state]
           SSP.integral_balance_termination[of   _ _ _ _ _ \<b> _ "2^k -1", OF SSP_from_this, of state]
  by(auto  simp add:  ssp_def)

     
lemma invar_comb_holds_1[invar_holds_intros]: 
       "\<lbrakk>Scaling_ret_1_cond k state; invar_comb  state \<rbrakk>  \<Longrightarrow> invar_comb(Scaling_ret1 k state)"
  apply(rule invar_combI)
  apply(all \<open>rule invar_combE[of state]\<close>)
  using  SSP.invar_balance_holds[of   _ _ _ _ _ \<b> _ "2^k -1", OF SSP_from_this, of state]
           SSP.invar_integral_holds[of   _ _ _ _ _ \<b> _ "2^k -1", OF SSP_from_this, of state]
           SSP.invar_opt_holds[of   _ _ _ _ _ \<b> _ "2^k -1", OF SSP_from_this, of state]
           SSP.integral_balance_termination[of   _ _ _ _ _ \<b> _ "2^k -1", OF SSP_from_this, of state]
  by(auto simp add:  ssp_def  Scaling_ret1_def)

lemma invar_comb_holds_2[invar_holds_intros]: 
       "\<lbrakk>Scaling_ret_2_cond k state; invar_comb  state \<rbrakk> 
            \<Longrightarrow> invar_comb(Scaling_ret2 k state)"
  apply(rule invar_combI)
  apply(all \<open>rule invar_combE[of state]\<close>)
  using  SSP.invar_balance_holds[of   _ _ _ _ _ \<b> _ "2^k -1", OF SSP_from_this, of state]
           SSP.invar_integral_holds[of   _ _ _ _ _ \<b> _ "2^k -1", OF SSP_from_this, of state]
           SSP.invar_opt_holds[of   _ _ _ _ _ \<b> _ "2^k -1", OF SSP_from_this, of state]
           SSP.integral_balance_termination[of   _ _ _ _ _ \<b> _ "2^k -1", OF SSP_from_this, of state]
  by(auto simp add:  ssp_def  Scaling_ret2_def)

lemma reset_return_invar_balance_pres: "invar_balance state \<Longrightarrow> invar_balance (state \<lparr> return:= val \<rparr>)"
  unfolding invar_balance_def by simp

lemma reset_return_invar_integral_pres: "invar_integral state \<Longrightarrow> invar_integral (state \<lparr> return:= val \<rparr>)"
  unfolding invar_integral_def by simp

lemma reset_return_invar_opt_pres:"invar_opt state \<Longrightarrow> invar_opt (state \<lparr> return:= val \<rparr>)"
  unfolding invar_opt_def by simp

lemma invar_comb_holds_3[invar_holds_intros]: 
       "\<lbrakk>Scaling_ret_3_cond k state; invar_comb  state \<rbrakk>  \<Longrightarrow> invar_comb(Scaling_ret3 k state)"
   apply(rule invar_combI)
  apply(all \<open>rule invar_combE[of state]\<close>)
  using  SSP.invar_balance_holds[of   _ _ _ _ _ \<b> _ "2^k -1", OF SSP_from_this, of state]
           SSP.invar_integral_holds[of   _ _ _ _ _ \<b> _ "2^k -1", OF SSP_from_this, of state]
           SSP.invar_opt_holds[of   _ _ _ _ _ \<b> _ "2^k -1", OF SSP_from_this, of state]
           SSP.integral_balance_termination[of   _ _ _ _ _ \<b> _ "2^k -1", OF SSP_from_this, of state]
           reset_return_invar_balance_pres[of state failure] reset_return_invar_integral_pres[of state failure]
           reset_return_invar_opt_pres[of state failure]
  by(auto simp add:  ssp_def  Scaling_ret3_def invar_balance_def invar_integral_def invar_opt_def) 

text \<open>We combine the results by induction.\<close>

lemma invar_comb_holds: 
   assumes "Scaling_dom (k, state)" "invar_comb state"
   shows " invar_comb (Scaling k state)"
  using assms(2)
proof(induction rule: Scaling_induct[OF assms(1)])
  case (1 k state)
  note IH = this
  show ?case
    apply(rule Scaling_cases[where state = state and k = k])
    by(auto intro!: IH[simplified] invar_holds_intros  simp: Scaling_simps[OF IH(1)])
qed

subsubsection \<open>Final Correctness and Completeness Results\<close>

lemma Scaling_total: "Scaling_dom (k, state)"
  by(induction k arbitrary: state)(rule Scaling.domintros, simp)+

text \<open>Whenever $success$ is returned, there is a previous state with some desirable properties.\<close>

lemma get_prev_state_success:
  assumes "final = Scaling k start" "return final = success" "invar_comb start"
   shows  "\<exists> kk prev. final = ssp (2^kk-1) prev \<and> invar_comb prev" 
  using assms
proof(induction rule: Scaling_induct[of k start, OF  Scaling_total])
  case (1 k state)
  then show ?case
      using     Scaling_total Scaling_simps Scaling_upd4_def invar_comb_holds_4
      unfolding Scaling_ret1_def Scaling_ret2_def Scaling_ret3_def
      by (cases rule:  Scaling_cases[of k state]) auto
  qed

text \<open>Analogously for $failure$.\<close>

lemma  get_prev_state_failure:
 assumes "final = Scaling k start""return final = failure""invar_comb start"
  shows  "\<exists> prev. ((\<exists> kk. final = ssp (2^kk-1) prev ) \<or> 
                                (final = (ssp 0 prev)\<lparr> return := failure\<rparr> \<and> return (ssp 0 prev) = notyetterm ))\<and> invar_comb prev" 
    using assms
  proof(induction rule: Scaling_induct[of k start, OF  Scaling_total])
    case (1 k state)
    then show ?case 
      using     Scaling_total Scaling_simps[of k state] 
                Scaling_upd4_def invar_comb_holds_4  Scaling_total
      unfolding Scaling_ret1_def Scaling_ret2_def Scaling_ret3_def
      by(cases rule: Scaling_cases[of k state])(auto elim!:  Scaling_ret_3_condE)
  qed

  text \<open>Total correctness and completeness carry on from $SSP$ in the 
        first locale to the $Scaling$ function.\<close>

lemma total_correctness_general:
  assumes "invar_comb start"
          "final = Scaling k start"
  shows   "return final = success \<Longrightarrow> is_Opt \<b> (current_flow final)"
          "return final = failure \<Longrightarrow> \<nexists> f. f is \<b> flow"
          "return final = notyetterm \<Longrightarrow> False"
proof-
  show "return final = success \<Longrightarrow> is_Opt \<b> (current_flow final)"
  proof-
    assume asm:"return final = success"
    then obtain state_prev k' where prev: " final = ssp (2^k' -1 ) state_prev" "invar_comb state_prev"
          using get_prev_state_success assms by fast
    have "is_Opt \<b> (current_flow final)"
      apply(rule SSP.total_correctness1[OF SSP_from_this, of  _ "2^k'-1"])
      using prev unfolding ssp_def invar_comb_def asm 
      by auto
    thus ?thesis by simp
  qed
  show "return final = failure \<Longrightarrow> \<nexists> f. f is \<b> flow"
  proof-
    assume asm:"return final = failure"
     then obtain prev where prev: "((\<exists> kk. final = ssp (2^kk-1) prev ) \<or> 
                    (final = (ssp 0 prev)\<lparr> return := failure\<rparr> \<and> return (ssp 0 prev) = notyetterm ))"
                      "invar_comb prev"
          using get_prev_state_failure assms by fast
     hence prev_props: "final = (ssp 0 prev)\<lparr> return := failure\<rparr>"
                       "return (ssp 0 prev) = notyetterm"       
                       "invar_comb prev"
       using SSP.never_failure[OF SSP_from_this] asm SSP.integral_balance_termination[OF SSP_from_this]
             SSP_from_this invar_combE
       unfolding ssp_def by blast+
     have "\<nexists> f. f is \<b> flow"
       apply(rule  SSP.total_correctness(2)[OF SSP_from_this, of _  0 prev])
       using prev_props 
       by(auto simp add: ssp_def invar_comb_def) 
     thus ?thesis by simp
   qed
   show "return final = notyetterm  \<Longrightarrow> False"
        unfolding assms(2)
        proof(induction rule: Scaling_induct[of k start, OF Scaling_total])
          case (1 k state)
          then show ?case 
            using     Scaling_simps
            unfolding Scaling_ret1_def Scaling_ret2_def Scaling_ret3_def
            by (cases rule: Scaling_cases[of k state])
               (auto elim!: Scaling_ret_1_condE Scaling_ret_2_condE Scaling_ret_3_condE)
        qed
      qed

text \<open>In the beginning, there cannot be an augmenting path. So the invariant will hold initially.\<close>

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

lemma invar_opt_initial_state:
"invar_opt \<lparr>current_flow = (\<lambda> e. 0), balance = \<b>,  return = notyetterm\<rparr>"
  unfolding invar_opt_def
  apply(intro no_augcycle_min_cost_flow)
  using u_non_neg   no_augcycle_at_beginning zero_ereal_def 
  unfolding isbflow_def isuflow_def ex_def
  by (auto , presburger)

text \<open>Finally, we obtain total correctness and completeness for the initial state and threshold value $L$.\<close>

theorem total_correctness:
  assumes "L = \<lceil> log 2 (max 1 ((\<Sum> v \<in> \<V>. abs (\<b> v))/2))\<rceil>"
          "final = Scaling L \<lparr>current_flow = (\<lambda> e. 0), balance = \<b>,  return = notyetterm\<rparr>"
  shows   "return final = success \<Longrightarrow> is_Opt \<b> (current_flow final)" (is "?succ \<Longrightarrow> ?opt")
          "return final = failure \<Longrightarrow> \<nexists> f. f is \<b> flow" (is "?fail \<Longrightarrow> ?noopt")
          "return final = notyetterm \<Longrightarrow> False" (is "?no_term \<Longrightarrow> _")
proof-
  have aa:"invar_comb \<lparr>current_flow = \<lambda>e. 0, balance = \<b>, return = notyetterm\<rparr>"
    apply(intro invar_combI)
    using integral_b is_balance_b
    unfolding is_integral_balance_def is_integral_flow_def invar_balance_def invar_integral_def
    by (auto intro: invar_opt_initial_state)
  thus "?succ \<Longrightarrow> ?opt" "?fail \<Longrightarrow> ?noopt" "?no_term \<Longrightarrow> False"
    using assms  total_correctness_general[of "\<lparr>current_flow = \<lambda>e. 0, balance = \<b>, return = notyetterm\<rparr>" _ L]
    by simp+
qed

end
end