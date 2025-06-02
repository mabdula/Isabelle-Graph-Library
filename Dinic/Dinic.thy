theory Dinic
imports Flow_Theory.Blocking_Flow
begin

record 'f dinic_state = current_flow::'f

locale dinic_spec = flow_network_spec
  where fst = "fst::'e \<Rightarrow> 'v" for fst + 
fixes find_blocking_flow::"'flow_impl \<Rightarrow> 'resflow_impl option"
and   flow_lookup::"'flow_impl \<Rightarrow> 'e \<Rightarrow> real option"
and   flow_update::"'flow_impl \<Rightarrow> 'e \<Rightarrow> real \<Rightarrow> 'flow_impl"
and   flow_empty::"'flow_impl"
and   flow_invar::"'flow_impl \<Rightarrow> bool"
and   resflow_iterate::"'resflow_impl \<Rightarrow> ('flow_impl \<Rightarrow> 'e Redge \<Rightarrow> real \<Rightarrow> 'flow_impl) 
                            \<Rightarrow> 'flow_impl \<Rightarrow> 'flow_impl"
and   resflow_lookup::"'resflow_impl \<Rightarrow> 'e Redge \<Rightarrow> real option"
and   resflow_invar::"'resflow_impl \<Rightarrow> bool"
and   s t::'v
begin

definition "add_flow f e \<gamma> = (if \<gamma> = 0 then f
                              else (case flow_lookup f e 
                                    of None \<Rightarrow>  flow_update f e \<gamma> 
                                    | Some fl \<Rightarrow> flow_update f e (fl + \<gamma>)))"

definition "augment_impl f rf = resflow_iterate rf
            (\<lambda> acc e \<gamma>. (case e 
                         of F e \<Rightarrow> add_flow acc e \<gamma>
                         | B e  \<Rightarrow> add_flow acc e (-\<gamma>))) f"

function (domintros) dinic::"'flow_impl dinic_state \<Rightarrow> 'flow_impl dinic_state"
  where "dinic state = (let f = current_flow state in
                        (case (find_blocking_flow f) 
                         of None \<Rightarrow> state |
                         Some rf \<Rightarrow> dinic (state \<lparr> current_flow := augment_impl f rf \<rparr>)))"
  by pat_completeness auto


definition "dinic_initial = \<lparr> current_flow = flow_empty \<rparr>"

partial_function (tailrec) dinic_impl::"'flow_impl dinic_state \<Rightarrow> 'flow_impl dinic_state"
  where "dinic_impl state = (let f = current_flow state in
                        (case (find_blocking_flow f) 
                         of None \<Rightarrow> state |
                         Some rf \<Rightarrow> dinic_impl (state \<lparr> current_flow := augment_impl f rf \<rparr>)))"

lemmas [code] = dinic_initial_def dinic_impl.simps augment_impl_def add_flow_def

definition dinic_upd::"'flow_impl dinic_state \<Rightarrow> 'flow_impl dinic_state"
  where "dinic_upd state = (let f = current_flow state;
                           rf = the (find_blocking_flow f) in
                           state \<lparr> current_flow := augment_impl f rf \<rparr>)"

definition "dinic_ret_cond state = (find_blocking_flow (current_flow state) = None)"

lemma dinic_ret_condE: "dinic_ret_cond state \<Longrightarrow> (find_blocking_flow (current_flow state) = None \<Longrightarrow> P ) \<Longrightarrow> P"
  by(auto simp add: dinic_ret_cond_def)

definition "dinic_upd_cond state = (find_blocking_flow (current_flow state) \<noteq> None)"

lemma dinic_upd_condE: "dinic_upd_cond state \<Longrightarrow>
   (\<And> f. find_blocking_flow (current_flow state) = Some f \<Longrightarrow> P ) \<Longrightarrow> P"
  by(auto simp add: dinic_upd_cond_def)

lemma dinic_cases: "(dinic_ret_cond state \<Longrightarrow> P) \<Longrightarrow>
                    (dinic_upd_cond state \<Longrightarrow> P) \<Longrightarrow> P"
  by(auto simp add: dinic_ret_cond_def dinic_upd_cond_def)

lemma dinic_simps:
  shows   "dinic_ret_cond state \<Longrightarrow> dinic state = state" 
          "dinic_dom state \<Longrightarrow> dinic_upd_cond state \<Longrightarrow> dinic state = dinic (dinic_upd state)"
using dinic.psimps[OF dinic.domintros[of state]] dinic.psimps[of state]
  by(auto elim: dinic_upd_condE dinic_ret_condE 
      simp add: dinic_upd_def)

lemma dinic_domintros:
  shows   "dinic_ret_cond state \<Longrightarrow> dinic_dom state" 
          "dinic_upd_cond state \<Longrightarrow> dinic_dom (dinic_upd state) \<Longrightarrow> dinic_dom state"
  by(auto intro: dinic.domintros 
          elim!: dinic_ret_condE dinic_upd_condE 
       simp add: dinic_upd_def)

lemma dinic_induct:
  assumes "dinic_dom state"
  assumes "\<And> state. 
         \<lbrakk> dinic_dom state; dinic_upd_cond state  \<Longrightarrow> P (dinic_upd state)\<rbrakk> \<Longrightarrow> P state"
   shows "P  state"
  using assms(2)
  by(induction rule: dinic.pinduct[OF assms(1)])
    (auto simp add: dinic_upd_cond_def dinic_upd_def dinic.psimps Let_def 
              split: option.split)

definition "invar_flow state = 
         is_s_t_flow (abstract_real_map (flow_lookup (current_flow state))) s t"

lemma invar_flowI: "is_s_t_flow (abstract_real_map (flow_lookup (current_flow state))) s t \<Longrightarrow> invar_flow state"
  by(auto simp add: invar_flow_def)

lemma invar_flowE: "invar_flow state \<Longrightarrow>
 (is_s_t_flow (abstract_real_map (flow_lookup (current_flow state))) s t \<Longrightarrow> P ) \<Longrightarrow> P"
  by(auto simp add: invar_flow_def)

definition "invar_basic state = 
(flow_invar (current_flow state) \<and> 
dom (flow_lookup (current_flow state)) \<subseteq> \<E>)"

lemma invar_basicI: 
"dom (flow_lookup (current_flow state)) \<subseteq> \<E> \<Longrightarrow>  flow_invar (current_flow state) \<Longrightarrow> invar_basic state"
  by(auto simp add: invar_basic_def)

lemma invar_basicE: 
" invar_basic state \<Longrightarrow>(dom (flow_lookup (current_flow state)) \<subseteq> \<E> 
\<Longrightarrow>  flow_invar (current_flow state) \<Longrightarrow> P) \<Longrightarrow> P"
  by(auto simp add: invar_basic_def)

end

locale dinic =
dinic_spec where fst = "fst::'edge_type \<Rightarrow> 'v" +
flow_network where fst = fst for fst +
assumes find_blocking_flow:
       "\<And> f. flow_invar f \<Longrightarrow> find_blocking_flow f = None
            \<longleftrightarrow> \<not> resreach (abstract_real_map (flow_lookup f)) s t"
       "\<And> f rf. flow_invar f \<Longrightarrow> find_blocking_flow f = Some rf \<Longrightarrow> resflow_invar rf"
       "\<And> f rf. flow_invar f \<Longrightarrow> find_blocking_flow f = Some rf \<Longrightarrow>
         residual_level_blocking_flow  (abstract_real_map (flow_lookup f)) s t
                                       (abstract_real_map (resflow_lookup rf))"
       "\<And> f rf. flow_invar f \<Longrightarrow> find_blocking_flow f = Some rf \<Longrightarrow>
          dom (resflow_lookup rf) \<subseteq> residual_level_graph (abstract_real_map (flow_lookup f)) s"
assumes  resflow_iterate: 
  "\<And> rf f init. resflow_invar rf \<Longrightarrow> \<exists> es. set es =  dom (resflow_lookup rf) \<and>
                                    distinct es \<and>
                                    resflow_iterate rf f init = 
                                    foldr (\<lambda> e acc. f acc e (the (resflow_lookup rf e))) es init"
assumes flow_datastructure:
        "flow_invar flow_empty"
        "\<And> f. flow_invar f \<Longrightarrow> flow_invar (flow_update f e x)"
        "\<And> f. flow_invar f \<Longrightarrow> flow_lookup (flow_update f e x) = (flow_lookup f)(e:= Some x)"
        "\<And> e. flow_lookup flow_empty e = None"
begin

lemma flow_lookup_empty_zero_flow: "abstract_real_map (flow_lookup flow_empty) = (\<lambda> e. 0)"
  by (auto simp add: abstract_real_map_none flow_datastructure(4))

lemma add_flow_correct: 
  assumes "flow_invar f"
  shows   "flow_invar (add_flow f e g)"
          "abstract_real_map (flow_lookup (add_flow f e g)) = 
           (\<lambda> d. if d = e then abstract_real_map (flow_lookup f) e + g else
                               abstract_real_map (flow_lookup f) d)"
          "dom (flow_lookup  (add_flow f e g)) = (if g \<noteq> 0 
                                                 then Set.insert e (dom (flow_lookup f))
                                                 else dom (flow_lookup f))"
 by(auto  simp add: add_flow_def abstract_real_map_def assms flow_datastructure 
             split: option.split)

lemma augment_impl_correct:
  assumes "flow_invar f" "resflow_invar rf"
  shows "flow_invar (augment_impl f rf)"
        "abstract_real_map (flow_lookup (augment_impl f rf)) = 
        augment_residual_flow (abstract_real_map (flow_lookup f))
         (abstract_real_map (resflow_lookup rf))"
        "dom (flow_lookup (augment_impl f rf)) =
        dom (flow_lookup f) \<union> oedge ` { e . e \<in> dom (resflow_lookup rf)
                             \<and> the (resflow_lookup rf e) \<noteq> 0 }"
proof-
  let ?iteration="(\<lambda> rf e acc.
           case e of F ea \<Rightarrow> add_flow acc ea (the (resflow_lookup rf e))
           | B ea \<Rightarrow> add_flow acc ea (- the (resflow_lookup rf e)))"
  obtain es where es_prop:
    "set es = dom (resflow_lookup rf)" "distinct es"    
    "resflow_iterate rf
     (\<lambda>acc e \<gamma>. case e of F e \<Rightarrow> add_flow acc e \<gamma> | B e \<Rightarrow> add_flow acc e (- \<gamma>)) f =
     foldr  (?iteration rf) es f"
    using resflow_iterate[OF assms(2), of _ f] by fast
  have flow_invar_steps:"flow_invar
     (foldr (?iteration rf) es f)"
    by(auto intro:  foldr_invar split: Redge.split simp add:  assms(1) add_flow_correct(1))
  show "flow_invar (augment_impl f rf)"
    by(auto simp add: augment_impl_def es_prop(3) flow_invar_steps)
  have "abstract_real_map
     (flow_lookup
       (foldr (?iteration rf) es f)) =
    (\<lambda>e. abstract_real_map (flow_lookup f) e + 
         (if F e \<in> set es then abstract_real_map (resflow_lookup rf) (F e) else 0) +
         (if B e \<in> set es then - abstract_real_map (resflow_lookup rf) (B e) else 0))"
    using assms(1) es_prop(2)  equalityD1[OF es_prop(1)] 
  proof(induction es  arbitrary: f rf)
    case Nil
    then show ?case 
      by (auto simp add: abstract_real_map_empty)
  next
    case (Cons e es)
    hence dinstinct_es_and_dom: "distinct es" "set  es \<subseteq> dom (resflow_lookup rf)" by auto
    have flow_invar_now: "flow_invar (foldr (?iteration rf) es f)"
      by (simp add: Cons.prems(1) add_flow_correct(1) Redge.split_sel foldr_invar)
    show ?case 
        using Cons(3,4)  
        by(cases e)
          (auto simp add: add_flow_correct(2)[OF flow_invar_now] 
           Cons(1)[OF Cons(2) dinstinct_es_and_dom] abstract_real_map_some )
    qed
    thus "abstract_real_map (flow_lookup (augment_impl f rf)) =
        augment_residual_flow (abstract_real_map (flow_lookup f)) 
                           (abstract_real_map (resflow_lookup rf))"
     by(auto simp add: augment_impl_def augment_residual_flow_def es_prop(3)
                       abstract_real_map_none domIff es_prop(1))
   show "dom (flow_lookup (augment_impl f rf)) =
        dom (flow_lookup f) \<union> oedge ` { e . e \<in> dom (resflow_lookup rf)
                             \<and> the (resflow_lookup rf e) \<noteq> 0 }"
     unfolding augment_impl_def es_prop(1)[symmetric] es_prop(3) 
    using assms(1)
   proof(induction es arbitrary: f)
     case (Cons e es)
      have flow_invar_now: "flow_invar (foldr (?iteration rf) es f)"
      by (simp add: Cons.prems(1) add_flow_correct(1) Redge.split_sel foldr_invar)  
     then show ?case 
       by(cases e)
         (force simp add: add_flow_correct(3)[OF flow_invar_now] Cons(1)[OF Cons(2)])+
   qed simp
 qed

lemma invar_basic_holds_call:
  assumes "invar_basic state" "dinic_upd_cond state"
  shows   "invar_basic (dinic_upd state)"
proof(rule invar_basicE[OF assms(1)], rule dinic_upd_condE[OF assms(2)], goal_cases)
  case (1 f)
  have dom_lookup_in_E:
       "dom (resflow_lookup (the (find_blocking_flow (current_flow state)))) \<subseteq> \<EE>"
    by(intro subset_trans[OF find_blocking_flow(4)[OF 1(2)]])
       (auto simp add: 1(3) residual_level_graph_in_E)
  have invar_res:"resflow_invar (the (find_blocking_flow (current_flow state)))"
    by(auto intro!:  find_blocking_flow(2)[OF 1(2)] simp add: 1(3))
  show ?case 
  using dom_lookup_in_E  oedge_on_\<EE> 1(1)  augment_impl_correct(3)[OF 1(2) invar_res]
  by(intro invar_basicI)
    (auto intro!:augment_impl_correct(1)[OF 1(2)] invar_res find_blocking_flow(2)[OF 1(2)] 
        simp add: 1(3) dinic_upd_def Let_def)
qed

lemma invar_basic_holds:
  assumes "dinic_dom state" "invar_basic state"
  shows   "invar_basic (dinic state)"
  using assms(2)
proof(induction rule: dinic_induct[OF assms(1)])
  case (1 state)
  then show ?case 
    by(cases state rule: dinic_cases)
      (auto intro: invar_basic_holds_call simp add: dinic_simps)
qed

lemma invar_flow_holds_call:
  assumes  "dinic_upd_cond state" "invar_basic state" "invar_flow state"
  shows   "invar_flow (dinic_upd state)"
  apply(rule dinic_upd_condE[OF assms(1)], rule invar_flowI)
  apply(simp add: dinic_upd_def Let_def, subst augment_impl_correct(2))
  using find_blocking_flow(4)
  by(auto intro!: augment_s_t_flow_by_residual_s_t_flow
                  residual_level_blocking_flow_to_residual_flow 
           intro: find_blocking_flow(2,3) abstract_real_map_none 
                  invar_basicE[OF assms(2)] invar_flowE[OF assms(3)] 
            elim: is_s_t_flowE)

lemma invar_flow_holds:
  assumes "dinic_dom state" "invar_basic state" "invar_flow state"
  shows   "invar_flow (dinic state)"
  using assms(2-)
proof(induction rule: dinic_induct[OF assms(1)])
  case (1 state)
  then show ?case 
    by(cases state rule: dinic_cases)
      (auto intro: invar_basic_holds_call invar_flow_holds_call simp add: dinic_simps)
qed

lemma dinic_ret_cond_max_flow:
  assumes "dinic_ret_cond state" "invar_flow state" "invar_basic state"
  shows   "is_max_flow s t (abstract_real_map (flow_lookup (current_flow state)))"
  apply(rule dinic_ret_condE[OF assms(1)])
  apply(rule invar_flowE[OF assms(2)])
  apply(rule invar_basicE[OF assms(3)])
  using find_blocking_flow(1)
  by (auto intro:  no_maxflow_resreach
            elim: is_s_t_flowE invar_basicE[OF assms(3)])

lemma dinic_final_max_flow_general:
  assumes "dinic_dom state" "invar_basic state" "invar_flow state"
  shows   "is_max_flow s t (abstract_real_map (flow_lookup (current_flow (dinic state))))"
  using assms(2-)
proof(induction rule: dinic_induct[OF assms(1)])
  case (1 state)
  note IH = this
  show ?case 
    by(cases state rule: dinic_cases)
      (auto simp add: dinic_simps(2)[OF IH(1)] dinic_simps(1)
               intro: dinic_ret_cond_max_flow IH(2)  invar_basic_holds_call
                      invar_flow_holds_call IH(3,4))
qed

lemma dist_increase_upd:
  assumes "dinic_upd_cond state" "invar_basic state" "invar_flow state"
  shows "\<exists> d. enat d = residual_distance (abstract_real_map
                         (flow_lookup (current_flow state))) s t \<and>
             residual_distance (abstract_real_map
                         (flow_lookup (current_flow (dinic_upd state)))) s t \<ge> enat d + 1"
proof(rule dinic_upd_condE[OF assms(1)], goal_cases)
  case (1 rf)
  have resreach:"resreach (abstract_real_map (flow_lookup (current_flow state))) s t "
    using find_blocking_flow(1)[of "current_flow state"] 1
    by(auto intro: invar_basicE[OF assms(2)])
  obtain d where d_def: 
      "enat d = residual_distance (abstract_real_map (flow_lookup (current_flow state))) s t "
    using resreach_residual_dist_less_infty[OF resreach] by auto
  have flow_after_is: "abstract_real_map (flow_lookup (augment_impl (current_flow state) rf)) =
    augment_residual_flow (abstract_real_map (flow_lookup (current_flow state)))
        (abstract_real_map (resflow_lookup rf))"
    by(auto intro: augment_impl_correct(2) invar_basicE[OF assms(2)] find_blocking_flow(2)[OF _ 1])
  have blocking_flow: "residual_level_blocking_flow (abstract_real_map (flow_lookup (current_flow state))) s t
     (abstract_real_map (resflow_lookup rf))"
    using "1"
    by(auto intro: find_blocking_flow(3) invar_basicE[OF assms(2)])
  have s_t_flow: "abstract_real_map (flow_lookup (current_flow state)) is s -- t flow"
    by(auto intro: invar_flowE[OF assms(3)])
  have outside_dom_0:"e \<notin> residual_level_graph (abstract_real_map (flow_lookup (current_flow state))) s \<Longrightarrow>
        e \<in> \<EE> \<Longrightarrow> abstract_real_map (resflow_lookup rf) e = 0" for e
   using "1" assms(2) find_blocking_flow(4)[of "current_flow state" rf]
    by(auto  intro: abstract_real_map_none invar_basicE[OF assms(2)] simp add: domIff)
  have "residual_distance (abstract_real_map (flow_lookup
                             (current_flow (dinic_upd state)))) s t > enat d"
    using blocking_flow_augment_dist_increase[OF 
                    blocking_flow s_t_flow outside_dom_0 resreach refl, simplified]
    by( simp add: flow_after_is  1 dinic_upd_def d_def)
  thus ?thesis
    using d_def add_mono1 enat_less_plus_1_leq
    by(auto intro!: exI[of _ d])
qed

lemma dinic_term_general:
  assumes "invar_basic state" "invar_flow state"
   shows  "dinic_dom state"
proof-
  obtain d where           "enat d = card \<V> - residual_distance 
              (abstract_real_map (flow_lookup (current_flow state))) s t"
   by(auto intro: exE[OF enat_ile[OF diff_le_self_enat[of "card \<V>"],
           of "residual_distance (abstract_real_map (flow_lookup (current_flow state))) s t"]])
  from assms this
  show ?thesis
proof(induction d arbitrary: state rule: less_induct)
  case (less dd)
  show ?case 
  proof(cases state rule: dinic_cases)
    case 1
    then show ?thesis
     by(auto intro!: dinic_domintros(1))
  next
    case 2   
    have resreach:"resreach (abstract_real_map (flow_lookup (current_flow state))) s t "
    using find_blocking_flow(1)[of "current_flow state"] less(2,3)
    by(force intro: invar_basicE[OF less(2)] dinic_upd_condE[OF 2])
    obtain d where d_prop:"enat d = residual_distance (abstract_real_map 
        (flow_lookup (current_flow state))) s t"
        "enat d + 1 \<le> residual_distance (abstract_real_map (flow_lookup 
           (current_flow (dinic_upd state)))) s t"
      using dist_increase_upd[OF 2 less(2,3)] by auto 
    have measure_decrease:"card \<V> - residual_distance (abstract_real_map (flow_lookup 
           (current_flow (dinic_upd state)))) s t <
             card \<V> - residual_distance (abstract_real_map 
        (flow_lookup (current_flow state))) s t"
    proof(cases "residual_distance (abstract_real_map
                      (flow_lookup (current_flow (dinic_upd state)))) s t")
      case (enat nat)
      then show ?thesis 
        using d_prop(1)[symmetric] d_prop(2) 
        using resreach_dist_number_of_verts_bound[OF resreach]
        by simp(fastforce intro!: diff_less_mono2[of d nat "card \<V>"] 
                      intro: Suc_le_lessD [of d nat]
                   simp add: enat_ord_simps(1)[symmetric] plus_1_eSuc(2))
    next
      case infinity
      thus ?thesis 
        using d_prop(1)[symmetric]  resreach_dist_number_of_verts_bound[OF resreach]
        by(simp add:  enat_0_iff(1))
    qed
    then obtain i where i_prop:"enat i =
         enat (card \<V>) -
           residual_distance (abstract_real_map (flow_lookup (current_flow (dinic_upd state)))) s t"
      using enat_iless[of _ dd] less.prems(3) by fastforce
    show ?thesis 
      using less(4)
      by(auto intro!: dinic_domintros(2)[OF 2] 
                      less(1)[simplified enat_ord_code(2)[symmetric], of i]
               intro: invar_basic_holds_call invar_flow_holds_call
            simp add: i_prop measure_decrease less(2,3) 2)
  qed
 qed
qed

context
  assumes s_and_t: "s \<in> \<V>" "t\<in> \<V>" "s\<noteq> t"
begin

lemma initial_state_invars: "invar_basic dinic_initial" "invar_flow dinic_initial"
   by(auto intro!: invar_basicI invar_flowI zero_flow_is_s_t_flow
         simp add: dinic_initial_def flow_datastructure(1,4) flow_lookup_empty_zero_flow s_and_t)

lemma dinic_total_correctness:
"is_max_flow s t (abstract_real_map (flow_lookup (current_flow (dinic dinic_initial))))"
"dinic_dom dinic_initial"
  using dinic_term_general[OF initial_state_invars]
        dinic_final_max_flow_general[OF _ initial_state_invars]
  by auto  
end
end
end