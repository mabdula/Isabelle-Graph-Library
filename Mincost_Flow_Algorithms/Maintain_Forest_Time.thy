section \<open>Formalisation of the Running Time of Forest Maintenance\<close>

theory Maintain_Forest_Time
  imports Maintain_Forest
begin

locale maintain_forest_time =
maintain_forest where fst = fst for fst::"'edge_type \<Rightarrow> 'a"+ 
fixes t\<^sub>A\<^sub>C::nat and t\<^sub>A\<^sub>B::nat and t\<^sub>A\<^sub>u\<^sub>f::nat 
begin
function (domintros) maintain_forest_time::"('e, 'f, 'c,'h, 'd, 'g, 'i) Algo_state 
             \<Rightarrow> nat \<times> ('e, 'f, 'c,'h, 'd, 'g, 'i) Algo_state " where
"maintain_forest_time state = (let \<FF> = \<FF> state;
                    f = current_flow state;
                    b = balance state;
                    r_card = rep_comp_card state;
                    E' = actives state;
                    to_rdg = conv_to_rdg state;
                    \<gamma> = current_\<gamma> state
                in 
     (t\<^sub>A\<^sub>u\<^sub>f +++ 
        (case get_from_set  (\<lambda> e. abstract_flow_map f e > 8 * real N *\<gamma>) E'  of (Some e) \<Rightarrow>
                            ( let x = fst e; y = snd e;
                             to_rdg' = add_direction to_rdg x y e;
                             cardx = abstract_comp_map r_card x;
                             cardy = abstract_comp_map r_card y;
                             (x, y) = (if cardx \<le> cardy 
                                       then (x,y) else (y,x));
                              \<FF>' =insert_undirected_edge (fst e) (snd e) \<FF>;
                             x' = abstract_rep_map r_card x; 
                             y' = abstract_rep_map r_card y;
                             Q = get_path x' y' \<FF>';
                             f' = (if abstract_bal_map b x' > 0 
                                   then augment_edges_impl f (abstract_bal_map b x') (to_redge_path to_rdg' Q) 
                                   else augment_edges_impl f (- abstract_bal_map b x') (to_redge_path to_rdg' (itrev Q)));
                             b' = move_balance b x' y';
                            E'' = filter (\<lambda> d. {abstract_rep_map r_card (fst d) ,
                                                abstract_rep_map r_card (snd d)}
                                                 \<noteq> {x', y'} ) E';
                            r_card' = rep_comp_upd_all 
                                (\<lambda> u urc. if prod.fst (urc) = x' \<or> prod.fst (urc) = y'
                                    then (y', cardx + cardy) else urc) r_card;
                            nb = not_blocked state;
                            nb' = not_blocked_upd_all (\<lambda> d b. 
                                   if d = e then True
                                   else if {abstract_rep_map r_card (fst d) ,
                                            abstract_rep_map r_card (snd d)} = {x', y'} 
                                   then False
                                   else b) nb;
                            state' = state \<lparr>  \<FF> := \<FF>', current_flow := f',
                                    balance := b', 
                                    actives := E'', conv_to_rdg := to_rdg',
                                    rep_comp_card:= r_card',
                                    not_blocked := nb'\<rparr>
                            in  ((t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B) +++ (maintain_forest_time state')))
                    | None \<Rightarrow> ( t\<^sub>A\<^sub>C, state))))"
  by auto

lemma terminationA_iff:
  shows "maintain_forest_dom state \<longleftrightarrow> maintain_forest_time_dom state"
proof(rule, goal_cases)
  case 1
  show ?case
  proof(induction  rule: maintain_forest.pinduct[OF 1])
    case (1 state)
    note IH=this
    show ?case
      by(rule maintain_forest_time.domintros) 
        (rule IH(2), auto)+
  qed
next
  case 2
  show ?case 
  proof(induction  rule: maintain_forest_time.pinduct[OF 2])
    case (1 state)
    note IH=this
    show ?case
       by(rule maintain_forest.domintros) 
        (rule IH(2), auto)+
  qed
qed

lemma equal_results_A: 
  assumes "maintain_forest_dom state" 
  shows "maintain_forest state = prod.snd (maintain_forest_time state)"
proof(induction rule: maintain_forest.pinduct[OF assms(1)]) 
  case (1 state)
  note IH=this
  hence time_dom: "maintain_forest_time_dom state"
    using terminationA_iff invar_filter  by simp
  note IH' =  make_cong[where f = maintain_forest and g = "prod.snd \<circ> maintain_forest_time", simplified, OF IH(2)]
  show ?case 
    apply(subst maintain_forest.psimps[OF IH(1)], subst maintain_forest_time.psimps[OF time_dom])
    apply(cases rule: maintain_forest_cases[of state])
    subgoal
      (*takes some time*)
      by(auto elim: maintain_forest_ret_condE[of state ] simp add: Let_def add_fst_def )
    subgoal
      apply(rule maintain_forest_call_condE[of state], simp)
      apply((subst let_swap[of prod.snd])+, (rule let_cong, simp)+,
             subst add_fst_def, subst snd_conv)
      apply(subst option.case_eq_if)+
      apply(subst if_not_P[where P= "get_from_set _ _ = None"], simp)+
      apply(subst let_swap[of prod.snd] | subst prod.case_distrib[of prod.snd])+
      apply(subst add_fst_def, subst snd_conv)
      apply((rule let_cong, simp)|(rule split_cong[rotated], simp))+
      (*takes some time*)
      by(rule IH(2))auto
    done
qed

lemma maintain_forest_time_simps:
  assumes "maintain_forest_time_dom state" 
  shows"maintain_forest_call_cond state \<Longrightarrow> maintain_forest_time state = (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B) +++ maintain_forest_time (maintain_forest_upd state)"
       "maintain_forest_ret_cond state \<Longrightarrow> maintain_forest_time state =  (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C, state)"
  subgoal  
    apply(subst maintain_forest_time.psimps[OF assms])
    unfolding maintain_forest_upd_def Let_def add_fst_def
    apply(rule maintain_forest_call_condE, simp) 
    by(unfold option.case_eq_if)(auto split: if_splits prod.splits)
  by (auto simp add: maintain_forest_time.psimps[OF assms] maintain_forest_ret_cond_def Let_def add_fst_def
              split: if_splits option.split)

lemma time_boundA:
  assumes "maintain_forest_time_dom state" 
          "aux_invar state" "implementation_invar state"
  shows "prod.fst (maintain_forest_time state) = 
     (card (comps \<V> (to_graph (\<FF> state))) 
   -  card (comps \<V> (to_graph (\<FF> (prod.snd (maintain_forest_time state))))))*
                                  (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B) + (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C)"
  using assms(2-)
proof(induction rule: maintain_forest_induct[OF assms(1)[simplified sym[OF terminationA_iff]]])
  case (1 state)
  note IH=this
  hence maintain_forest_time_dom: "maintain_forest_time_dom state" 
    using terminationA_iff by auto
  have axi: " aux_invar state" 
    using IH by simp
  have upd_dom:"maintain_forest_call_cond state \<Longrightarrow> maintain_forest_dom (maintain_forest_upd state)"
    and auxii: "maintain_forest_call_cond state \<Longrightarrow> aux_invar (maintain_forest_upd state)"
    and auxiii: "maintain_forest_call_cond state \<Longrightarrow> implementation_invar (maintain_forest_upd state)"
    by(auto intro!:  termination_of_maintain_forest' invar_aux_pres_one_step invars_pres_one_step(1)
          simp add: IH(3,4))
  show ?case
    apply(cases rule: maintain_forest_cases[of state])
    subgoal
      using  maintain_forest_time_simps(2)[OF maintain_forest_time_dom] by simp
    subgoal
      apply(subst maintain_forest_time_simps(1)[OF maintain_forest_time_dom], simp)+
      unfolding add_fst_def 
      apply(simp, subst IH(2)[OF _ auxii auxiii], simp)
      apply(rule trans[of _ "((card (comps \<V> (to_graph (\<FF> (maintain_forest_upd state)))) 
                                     - card (comps \<V> (to_graph (\<FF> (prod.snd (maintain_forest_time (maintain_forest_upd state))))))) *
                                 (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B) + ( t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B)) "], simp)
      apply(subst semiring_normalization_rules(2), rule arg_cong[of _ _ "\<lambda> x. (*) x (t\<^sub>A\<^sub>u\<^sub>f + t\<^sub>A\<^sub>C + t\<^sub>A\<^sub>B)"])
      using  mono_one_step(3)[of state, OF _ axi]
             card_decrease[OF upd_dom auxii auxiii] equal_results_A[OF upd_dom] 
             invar_aux_pres_one_step[OF auxii] IH(4) 
      by simp
    done
qed

end
end