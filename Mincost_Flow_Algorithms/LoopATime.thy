section \<open>Formalisation of the Running Time of Forest Maintenance\<close>

theory LoopATime
  imports LoopA
begin

locale loopATime =
loopA where fst = fst for fst::"'edge_type \<Rightarrow> 'a"+ 
fixes t\<^sub>A\<^sub>C::nat and t\<^sub>A\<^sub>B::nat and t\<^sub>A\<^sub>u\<^sub>f::nat 
begin
function (domintros) loopAtime::"('a, 'd, 'c, 'edge_type) Algo_state 
             \<Rightarrow> nat \<times> ('a, 'd, 'c, 'edge_type) Algo_state" where
"loopAtime state = (let \<FF> = \<FF> state;
                    f = current_flow state;
                    b = balance state;
                    r = representative state;
                    E' = actives state;
                    to_rdg = conv_to_rdg state;
                    \<gamma> = current_\<gamma> state;
                    cards = comp_card state;
                    \<FF>_imp = \<FF>_imp state
                in (t\<^sub>A\<^sub>u\<^sub>f +++ (if \<exists> aa. get_from_set (\<lambda> e. f e > 8 * real N *\<gamma>) E' = Some aa
                    then let e = the ( get_from_set (\<lambda> e. f e > 8 * real N *\<gamma>) E');
                             x = fst e; y = snd e;
                             to_rdg' = (\<lambda> d. if d = make_pair e then F e
                                             else if prod.swap d = make_pair e then B e 
                                             else to_rdg d);
                             (x, y) = (if cards x \<le> cards y 
                                       then (x,y) else (y,x));
                              \<FF>' = insert {fst  e, snd e} \<FF>;
                             \<FF>_imp' = insert_undirected_edge (fst e) (snd e) \<FF>_imp;
                             x' = r x; y' = r y;
                             Q = get_path x' y' \<FF>_imp';
                             f' = (if b x' > 0 
                                   then augment_edges f (b x') (to_redge_path to_rdg' Q) 
                                   else augment_edges f (- b x') (to_redge_path to_rdg' (rev Q)));
                             b' = (\<lambda> v. if v= x' then 0 
                                        else if v = y' then b y' + b x'
                                        else b v);
                            E'' = filter (\<lambda> d. {r (fst d) , r (snd d)} \<noteq> {x', y'}) E';
                            r' = (\<lambda> v. if r v = x' \<or> r v = y'  then y' else r v);
                            cards' = (\<lambda> v. if r' v = y' then cards x + cards y else cards v);
                            nb = not_blocked state;
                            nb' = (\<lambda> d. if e = d then True
                                        else if {r (fst d) , r (snd d)} = {x', y'} then False
                                        else nb d);
                            state' = state \<lparr>  \<FF> := \<FF>', current_flow := f',
                                    balance := b',  representative := r',
                                    actives := E'', conv_to_rdg := to_rdg', comp_card := cards',
                                    \<FF>_imp:= \<FF>_imp', not_blocked := nb'\<rparr>
                            in  ((t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B) +++ (loopAtime state'))
                    else ( t\<^sub>A\<^sub>C, state))))"
  by auto

lemma terminationA_iff:
  assumes "invar_aux17 state"
  shows "loopA_dom state \<longleftrightarrow> loopAtime_dom state"
proof(rule, goal_cases)
  case 1
  show ?case
    using assms unfolding invar_aux17_def
  proof(induction  rule: loopA.pinduct[OF 1])
    case (1 state)
    note IH=this
    show ?case
      by(rule loopAtime.domintros) 
        (rule IH(2), auto intro: invar_filter simp add: IH(3))+
  qed
next
  case 2
  show ?case 
    using assms unfolding invar_aux17_def
  proof(induction  rule: loopAtime.pinduct[OF 2])
    case (1 state)
    note IH=this
    show ?case
       by(rule loopA.domintros) 
        (rule IH(2), auto intro: invar_filter simp add: IH(3))+
  qed
qed

lemma equal_results_A: 
  assumes "loopA_dom state" "invar_aux17 state"
  shows "loopA state = prod.snd (loopAtime state)"
  using assms(2) unfolding invar_aux17_def
proof(induction rule: loopA.pinduct[OF assms(1)])
  case (1 state)
  note IH=this
  hence time_dom: "loopAtime_dom state"
    using terminationA_iff[of state, simplified invar_aux17_def] invar_filter  by simp
  note IH' =  make_cong[where f = loopA and g = "prod.snd \<circ> loopAtime", simplified, OF IH(2)]
  show ?case 
    apply(subst loopA.psimps[OF IH(1)], subst loopAtime.psimps[OF time_dom])
    apply(cases rule: loopA_cases[of state])
    subgoal
      unfolding Let_def add_fst_def 
      by(auto elim: loopA_ret_condE[of state ])
    subgoal
      apply(rule loopA_call_condE[of state], simp)
      apply((subst let_swap[of prod.snd])+, (rule let_cong, simp)+, subst add_fst_def, subst snd_conv)
      apply(subst if_P[where P= "\<exists>aa. get_from_set _ _ = Some aa"], simp)+
      apply(subst let_swap[of prod.snd] | subst prod.case_distrib[of prod.snd])+
      apply(subst add_fst_def, subst snd_conv)
      apply((rule let_cong, simp)|(rule split_cong[rotated], simp))+
      by(rule IH(2))(auto intro: invar_filter simp add: IH(3))
    done
qed

lemma loopAtime_simps:
  assumes "loopAtime_dom state" 
  shows"loopA_call_cond state \<Longrightarrow> loopAtime state = (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B) +++ loopAtime (loopA_upd state)"
       "loopA_ret_cond state \<Longrightarrow> loopAtime state =  (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C, state)"
  subgoal  
    apply(subst loopAtime.psimps[OF assms])
    unfolding loopA_upd_def Let_def add_fst_def
    apply(rule loopA_call_condE, simp) 
    apply(auto split: if_splits prod.splits)
    done 
  by (auto simp add: loopAtime.psimps[OF assms] loopA_ret_cond_def Let_def add_fst_def
              split: if_splits)

lemma time_boundA:
  assumes "loopAtime_dom state" 
          "aux_invar state"
  shows "prod.fst (loopAtime state) = 
     (card (comps \<V> (to_graph (\<FF>_imp state))) 
   -  card (comps \<V> (to_graph (\<FF>_imp (prod.snd (loopAtime state))))))*
                                  (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B) + (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C)"
  using assms(2-)
proof(induction rule: loopA_induct[OF assms(1)[simplified sym[OF terminationA_iff[OF invar_aux17_from_aux_invar[OF assms(2)]]]]])
  case (1 state)
  note IH=this
  hence loopAtime_dom: "loopAtime_dom state" 
    using terminationA_iff invar_aux17_from_aux_invar by auto
  have axi: " aux_invar state" 
    using IH by simp
  have upd_dom:"loopA_call_cond state \<Longrightarrow> loopA_dom (loopA_upd state)"
    using aux_invar_def axi  invar_aux_pres_one_step   termination_of_loopA[OF _ refl] 
    by auto
  have auxii: "loopA_call_cond state \<Longrightarrow> aux_invar (loopA_upd state)"
    by (simp add: axi invar_aux_pres_one_step)
  show ?case
    apply(cases rule: loopA_cases[of state])
    subgoal
      using  loopAtime_simps(2)[OF loopAtime_dom] by simp
    subgoal
      apply(subst loopAtime_simps(1)[OF loopAtime_dom], simp)+
      unfolding add_fst_def 
      apply(simp, subst IH(2)[OF _ auxii], simp)
      apply(rule trans[of _ "((card (comps \<V> (to_graph (\<FF>_imp (loopA_upd state)))) 
                                     - card (comps \<V> (to_graph (\<FF>_imp (prod.snd (loopAtime (loopA_upd state))))))) *
                                 (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B) + ( t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B)) "], simp)
      apply(subst semiring_normalization_rules(2), rule arg_cong[of _ _ "\<lambda> x. (*) x (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B)"])
      using  mono_one_step(3)[of state, OF _ axi]
             card_decrease[OF upd_dom auxii] equal_results_A[OF upd_dom, OF _ invar_aux17_from_aux_invar] 
             invar_aux_pres_one_step[OF axi]
      by simp
    done
qed

end
end