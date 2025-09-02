section \<open>Formalisation of Loop for Ordinary Augmentations (Send-Flow)\<close>

theory Send_Flow
  imports Orlins_Preparation
begin

subsection \<open>Setup\<close>

locale send_flow_spec = 
  algo_spec where fst = fst and 
  get_from_set= "get_from_set ::('edge_type \<Rightarrow> bool) \<Rightarrow> 'd \<Rightarrow> 'edge_type option"
  and flow_empty = "flow_empty::'e" and bal_empty = "bal_empty::'f" and rep_comp_empty = "rep_comp_empty::'g"
  and conv_empty = "conv_empty::'h" and not_blocked_empty = "not_blocked_empty::'i"
for fst::"'edge_type \<Rightarrow> 'a" and get_from_set and 
    flow_empty and bal_empty and rep_comp_empty and conv_empty and not_blocked_empty +

fixes get_source_target_path_a
  ::"('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state  \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'edge_type Redge list) option" 
  and get_source_target_path_b
  ::"('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state  \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'edge_type Redge list) option" 
  and get_source::"('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state \<Rightarrow> 'a option"
  and get_target::"('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state \<Rightarrow> 'a option"
  and test_all_vertices_zero_balance::"('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state \<Rightarrow> bool"
begin

function (domintros) send_flow::"('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state  \<Rightarrow> ('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state" where
  "send_flow state = 
(let f = current_flow state;  b = balance state; \<gamma> = current_\<gamma> state
 in (if test_all_vertices_zero_balance state then state \<lparr> return:=success\<rparr> 
     else (case get_source state of Some s \<Rightarrow> 
            (case get_source_target_path_a state s of Some (t, P) \<Rightarrow>
                   (let f' = augment_edges_impl f \<gamma> P;
                       b' = move b \<gamma> s t;
                       state' = state \<lparr> current_flow := f', balance := b'\<rparr> in   
                           send_flow state')
                 | None \<Rightarrow> state \<lparr> return := infeasible\<rparr>) 
     | None \<Rightarrow> 
          (case get_target state of Some t \<Rightarrow> 
            (case get_source_target_path_b state t of Some (s, P) \<Rightarrow>
                   (let f' = augment_edges_impl f \<gamma> P;
                       b' = move b \<gamma> s t;
                       state' = state \<lparr> current_flow := f', balance := b'\<rparr> in   
                           send_flow state')
                 | None \<Rightarrow> state \<lparr> return := infeasible\<rparr>)
         | None \<Rightarrow> state \<lparr> return := notyetterm\<rparr>
    ))))"
  by pat_completeness auto

partial_function (tailrec) send_flow_impl::"('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state  \<Rightarrow> ('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state" where
  "send_flow_impl state = 
(let f = current_flow state;  b = balance state; \<gamma> = current_\<gamma> state
 in (if test_all_vertices_zero_balance state then state \<lparr> return:=success\<rparr> 
     else (case get_source state of Some s \<Rightarrow> 
            (case get_source_target_path_a state s of Some (t, P) \<Rightarrow>
                   (let f' = augment_edges_impl f \<gamma> P;
                       b' = move b \<gamma> s t;
                       state' = state \<lparr> current_flow := f', balance := b'\<rparr> in   
                           send_flow_impl state')
                 | None \<Rightarrow> state \<lparr> return := infeasible\<rparr>) 
     | None \<Rightarrow> 
          (case get_target state of Some t \<Rightarrow> 
            (case get_source_target_path_b state t of Some (s, P) \<Rightarrow>
                   (let f' = augment_edges_impl f \<gamma> P;
                       b' = move b \<gamma> s t;
                       state' = state \<lparr> current_flow := f', balance := b'\<rparr> in   
                           send_flow_impl state')
                 | None \<Rightarrow> state \<lparr> return := infeasible\<rparr>)
         | None \<Rightarrow> state \<lparr> return := notyetterm\<rparr>
    ))))"

lemmas [code] = send_flow_impl.simps

definition send_flow_succ_upd::"('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state
\<Rightarrow> ('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state" where
  "send_flow_succ_upd state =  state \<lparr> return:=success\<rparr>"

definition send_flow_fail_upd::"('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state  
\<Rightarrow> ('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state " where
  "send_flow_fail_upd state =  state \<lparr> return:=infeasible\<rparr>"

definition send_flow_call1_upd::"('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state 
\<Rightarrow> ('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state " where
  "send_flow_call1_upd state = (let
                    f = current_flow state;
                    b = balance state;
                    \<gamma> = current_\<gamma> state;
                    s = the (get_source state); 
                    (t, P) =  the (get_source_target_path_a state s);
                    f' = augment_edges_impl f \<gamma> P;
                       b' = move b \<gamma> s t;
                       state' = state \<lparr> current_flow := f', balance := b'\<rparr> in   
                           state')"

definition send_flow_call2_upd::"('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state  
\<Rightarrow> ('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state" where
  "send_flow_call2_upd state = (let
                    f = current_flow state;
                    b = balance state;
                    \<gamma> = current_\<gamma> state;
                    t = the (get_target state); 
                    (s, P) =  the (get_source_target_path_b state t);
                    f' = augment_edges_impl f \<gamma> P;
                       b' = move b \<gamma> s t;
                       state' = state \<lparr> current_flow := f', balance := b'\<rparr> in   
                           state')"

definition send_flow_cont_upd::"('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state 
\<Rightarrow> ('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state " where
  "send_flow_cont_upd state = state \<lparr> return := notyetterm\<rparr>"

definition "send_flow_succ_cond state = 
(let f = current_flow state;  b = balance state; \<gamma> = current_\<gamma> state
 in (if test_all_vertices_zero_balance state then True 
     else False))"

lemma send_flow_succ_condE:
"send_flow_succ_cond state \<Longrightarrow>
 ( \<And> f b \<gamma> . \<lbrakk>f = current_flow state; b = balance state; \<gamma> = current_\<gamma> state;
              test_all_vertices_zero_balance state\<rbrakk> \<Longrightarrow> P) 
\<Longrightarrow> P"
  unfolding  send_flow_succ_cond_def by presburger

lemma send_flow_succ_condI:
 "\<lbrakk>f = current_flow state;  b = balance state; \<gamma> = current_\<gamma> state;
   test_all_vertices_zero_balance state\<rbrakk>
 \<Longrightarrow> send_flow_succ_cond state"
  unfolding  send_flow_succ_cond_def by presburger

definition "send_flow_call1_cond state = 
(let f = current_flow state;  b = balance state; \<gamma> = current_\<gamma> state
 in (if test_all_vertices_zero_balance state then False
     else (case get_source state of Some s \<Rightarrow> 
            (case get_source_target_path_a state s of Some (t, P) \<Rightarrow> True
                                                     | None \<Rightarrow> False) 
                                 | None \<Rightarrow> False)))"

lemma send_flow_call1_condE: 
  assumes "send_flow_call1_cond state"
    "( \<And> f b \<gamma> s t P f' b' state'. 
       \<lbrakk>f = current_flow state; b = balance state; \<gamma> = current_\<gamma> state;
        \<not> test_all_vertices_zero_balance state; get_source state = Some s;
        get_source_target_path_a state s = Some (t, P); f' = augment_edges_impl f \<gamma> P;
        b' = move b \<gamma> s t\<rbrakk>
      \<Longrightarrow> state' = state \<lparr> current_flow := f', balance := b'\<rparr> \<Longrightarrow> Q)"
  shows Q 
  using assms(1)
  by(all \<open>cases "test_all_vertices_zero_balance state"\<close>,
     all \<open>cases "get_source state"\<close>,
     all \<open>cases "get_source_target_path_a state (the (get_source state))"\<close>)
    (auto simp add: send_flow_call1_cond_def if_split intro!: assms(2))

lemma send_flow_call1_condI: 
  "( \<And> f b \<gamma> s t P f' b' state'. 
    \<lbrakk>f = current_flow state; b = balance state; \<gamma> = current_\<gamma> state;
     \<not> test_all_vertices_zero_balance state; get_source state = Some s;
     get_source_target_path_a state s = Some (t, P); f' = augment_edges_impl f \<gamma> P ;
     b' = move b \<gamma> s t; state' = state \<lparr> current_flow := f', balance := b'\<rparr>\<rbrakk> 
   \<Longrightarrow> send_flow_call1_cond state)"
  by(auto simp add: send_flow_call1_cond_def  split: option.split) 

definition "send_flow_call2_cond state =
(let f = current_flow state;  b = balance state; \<gamma> = current_\<gamma> state
 in (if test_all_vertices_zero_balance state then False
     else (case get_source state of Some s \<Rightarrow> False
     | None \<Rightarrow> 
          (case get_target state of Some t \<Rightarrow> 
            (case get_source_target_path_b state t of Some (s, P) \<Rightarrow> True
                 | None \<Rightarrow> False)
         | None \<Rightarrow> False
    ))))"

lemma send_flow_call2_condE: 
  assumes "send_flow_call2_cond state" 
    "( \<And> f b \<gamma> t s P f' b' state'.
      \<lbrakk>f = current_flow state; b = balance state; \<gamma> = current_\<gamma> state;
       \<not> test_all_vertices_zero_balance state; get_source state = None; get_target state = Some t;
       get_source_target_path_b state t = Some (s, P); f' = augment_edges_impl f \<gamma> P;
       b' = move b \<gamma> s t; state' = state \<lparr> current_flow := f', balance := b'\<rparr>\<rbrakk>
     \<Longrightarrow> Q)"
  shows Q
  apply(rule assms(2)[OF refl refl refl _ _ _ _ refl refl refl,
        of "the (get_target state)"
        "prod.fst ( the (get_source_target_path_b state (the (get_target state))))"
        "prod.snd ( the (get_source_target_path_b state (the (get_target state))))"])
  apply(all \<open>cases "test_all_vertices_zero_balance state"\<close>)
  apply(all \<open>cases "get_source state"\<close>)
  apply(all \<open>cases "get_target state"\<close>)
  apply(all \<open>cases "get_source_target_path_b state (the (get_target state))"\<close>)
  using assms(1)
  by(auto simp add: send_flow_call2_cond_def if_split intro!: assms(2))

lemma send_flow_call2_condI: 
  "\<And> f b \<gamma> t s P f' b' state'.
   \<lbrakk>f = current_flow state ; b = balance state ; \<gamma> = current_\<gamma> state;
    \<not> test_all_vertices_zero_balance state; get_source state = None; get_target state = Some t;
     get_source_target_path_b state t = Some (s, P); f' = augment_edges_impl f \<gamma> P;
     b' = move b \<gamma> s t ; state' = state \<lparr> current_flow := f', balance := b'\<rparr>\<rbrakk>
  \<Longrightarrow> send_flow_call2_cond state"
  by(auto simp add: send_flow_call2_cond_def if_split)

definition "send_flow_fail1_cond state = 
(let f = current_flow state;  b = balance state; \<gamma> = current_\<gamma> state
 in (if test_all_vertices_zero_balance state then False
     else (case get_source state of Some s \<Rightarrow> 
            (case get_source_target_path_a state s of Some (t, P) \<Rightarrow> False
                                                     | None \<Rightarrow> True) 
                                 | None \<Rightarrow> False)))"

lemma send_flow_fail1_condE: 
  assumes "send_flow_fail1_cond state"
    "\<And> f b \<gamma> s. f = current_flow state \<Longrightarrow>
                    b = balance state \<Longrightarrow>
                    \<gamma> = current_\<gamma> state \<Longrightarrow>
                   \<not> test_all_vertices_zero_balance state \<Longrightarrow>
                  get_source state = Some s\<Longrightarrow>
                  get_source_target_path_a state s = None  \<Longrightarrow> Q"
  shows Q
  apply(all \<open>cases "test_all_vertices_zero_balance state"\<close>)
  apply(all \<open>cases "get_source state"\<close>)
  apply(all \<open>cases "get_source_target_path_a state (the (get_source state))"\<close>)
  using assms(1)
  by(auto simp add: send_flow_fail1_cond_def if_split intro!: assms(2))

definition "send_flow_fail2_cond state =
(let f = current_flow state;  b = balance state; \<gamma> = current_\<gamma> state
 in (if test_all_vertices_zero_balance state then False
     else (case get_source state of Some s \<Rightarrow> False
     | None \<Rightarrow> 
          (case get_target state of Some t \<Rightarrow> 
            (case get_source_target_path_b state t of Some (s, P) \<Rightarrow> False
                 | None \<Rightarrow> True)
         | None \<Rightarrow> False
    ))))"

lemma send_flow_fail2_condE: 
  assumes "send_flow_fail2_cond state" 
    "\<And> f b \<gamma> t.
      \<lbrakk>f = current_flow state ; b = balance state; \<gamma> = current_\<gamma> state;
       \<not> test_all_vertices_zero_balance state; get_source state = None;
       get_target state = Some t; get_source_target_path_b state t = None\<rbrakk> 
       \<Longrightarrow> Q"
  shows Q
  apply(rule assms(2)[OF refl refl refl _ _ _ _ ,
        of "the (get_target state)"])
  apply(all \<open>cases "test_all_vertices_zero_balance state"\<close>)
  apply(all \<open>cases "get_source state"\<close>)
  apply(all \<open>cases "get_target state"\<close>)
  apply(all \<open>cases "get_source_target_path_b state (the (get_target state))"\<close>)
  using assms(1)
  by(auto simp add: send_flow_fail2_cond_def if_split intro!: assms(2))

lemma send_flow_fail2_condI: 
  "\<And> f b \<gamma> t. 
   \<lbrakk>f = current_flow state; b = balance state; \<gamma> = current_\<gamma> state;
    \<not> test_all_vertices_zero_balance state; get_source state = None;
    get_target state = Some t; get_source_target_path_b state t = None\<rbrakk> 
   \<Longrightarrow> send_flow_fail2_cond state"
  by(auto simp add: send_flow_fail2_cond_def if_split)

definition "send_flow_cont_cond state =
 (let f = current_flow state;  b = balance state; \<gamma> = current_\<gamma> state
 in (if test_all_vertices_zero_balance state then False 
     else (case get_source state of Some s \<Rightarrow> False
     | None \<Rightarrow> 
          (case get_target state of Some t \<Rightarrow> False 
         | None \<Rightarrow> True ))))"

lemma send_flow_cont_condE: 
  assumes "send_flow_cont_cond state" 
    "\<lbrakk>\<not> test_all_vertices_zero_balance state; get_source state = None; get_target state = None\<rbrakk> 
     \<Longrightarrow> Q"
  shows Q
  apply(rule assms(2))
  apply(all \<open>cases "test_all_vertices_zero_balance state"\<close>)
  apply(all \<open>cases "get_source state"\<close>)
  apply(all \<open>cases "get_target state"\<close>)
  using assms(1)
  by(auto simp add: send_flow_cont_cond_def if_split intro!: assms(2))

lemma send_flow_cont_condI: 
  "\<lbrakk>\<not> test_all_vertices_zero_balance state; get_source state = None; get_target state = None\<rbrakk> 
   \<Longrightarrow> send_flow_cont_cond state"
  by(auto simp add: send_flow_cont_cond_def if_split)

lemma send_flow_cases: 
  assumes "send_flow_cont_cond  state \<Longrightarrow> P"
          "send_flow_succ_cond  state \<Longrightarrow> P"
          "send_flow_call1_cond  state \<Longrightarrow> P"
          "send_flow_call2_cond  state \<Longrightarrow> P"
          "send_flow_fail1_cond  state \<Longrightarrow> P"
          "send_flow_fail2_cond  state \<Longrightarrow> P"
  shows P
proof-
  have "send_flow_cont_cond  state \<or> send_flow_succ_cond state \<or>
        send_flow_call1_cond  state \<or> send_flow_call2_cond state \<or>
        send_flow_fail1_cond  state \<or> send_flow_fail2_cond state"
    by(auto simp add: send_flow_cont_cond_def send_flow_succ_cond_def
        send_flow_call1_cond_def send_flow_call2_cond_def
        send_flow_fail1_cond_def send_flow_fail2_cond_def Let_def
        split: if_split option.split)    
  thus P
    using assms by auto
qed

lemma send_flow_succ_upd_changes: 
  "\<FF> (send_flow_succ_upd state) = \<FF> state"
  "conv_to_rdg (send_flow_succ_upd state) = conv_to_rdg state"
  "actives (send_flow_succ_upd state) = actives state"
  "current_\<gamma> (send_flow_succ_upd state) = current_\<gamma>  state"
  "rep_comp_card (send_flow_succ_upd state) = rep_comp_card state"
  "\<F> (send_flow_succ_upd state) = \<F> state"
  "\<F>_redges (send_flow_succ_upd state) = \<F>_redges state"
  "not_blocked (send_flow_succ_upd state) = not_blocked state"
  "balance (send_flow_succ_upd state) = balance state"
  "current_flow (send_flow_succ_upd state) = current_flow state"
  "\<Phi> (send_flow_succ_upd state) = \<Phi> state"
  by(auto simp add: send_flow_succ_upd_def Let_def \<Phi>_def F_def F_redges_def)

lemma send_flow_call1_upd_changes: 
  "\<FF> (send_flow_call1_upd state) = \<FF> state"
  "conv_to_rdg (send_flow_call1_upd state) = conv_to_rdg state"
  "actives (send_flow_call1_upd state) = actives state"
  "current_\<gamma> (send_flow_call1_upd state) = current_\<gamma>  state"
  "rep_comp_card (send_flow_call1_upd state) = rep_comp_card state"
  "\<F> (send_flow_call1_upd state) = \<F> state"
  "\<F>_redges (send_flow_call1_upd state) = \<F>_redges state"
  "not_blocked (send_flow_call1_upd state) = not_blocked state"
  by (auto simp add: send_flow_call1_upd_def Let_def F_def F_redges_def
      split: option.split if_split prod.split)

lemma send_flow_fail_upd_changes: 
  "\<FF> (send_flow_fail_upd state) = \<FF> state"
  "conv_to_rdg (send_flow_fail_upd state) = conv_to_rdg state"
  "actives (send_flow_fail_upd state) = actives state"
  "current_\<gamma> (send_flow_fail_upd state) = current_\<gamma>  state"
  "rep_comp_card (send_flow_fail_upd state) = rep_comp_card state"
  "\<F> (send_flow_fail_upd state) = \<F> state"
  "\<F>_redges (send_flow_fail_upd state) = \<F>_redges state"
  "not_blocked (send_flow_fail_upd state) = not_blocked state"
  "balance (send_flow_fail_upd state) = balance state"
  "current_flow (send_flow_fail_upd state) = current_flow state"
  "\<Phi> (send_flow_fail_upd state) = \<Phi> state"
  by(auto simp add: send_flow_fail_upd_def Let_def \<Phi>_def F_def F_redges_def)

lemma send_flow_call2_upd_changes: 
  "\<FF> (send_flow_call2_upd state) = \<FF> state"
  "conv_to_rdg (send_flow_call2_upd state) = conv_to_rdg state"
  "actives (send_flow_call2_upd state) = actives state"
  "current_\<gamma> (send_flow_call2_upd state) = current_\<gamma>  state"
  "rep_comp_card (send_flow_call2_upd state) = rep_comp_card state"
  "\<F> (send_flow_call2_upd state) = \<F> state"
  "\<F>_redges (send_flow_call2_upd state) = \<F>_redges state"
  "not_blocked (send_flow_call2_upd state) = not_blocked state"
  by (auto split: prod.split simp add: send_flow_call2_upd_def Let_def F_def F_redges_def)

lemma send_flow_cont_upd_changes: 
  "\<FF> (send_flow_cont_upd state) = \<FF> state"
  "conv_to_rdg (send_flow_cont_upd state) = conv_to_rdg state"
  "actives (send_flow_cont_upd state) = actives state"
  "current_\<gamma> (send_flow_cont_upd state) = current_\<gamma>  state"
  "rep_comp_card (send_flow_cont_upd state) = rep_comp_card state"
  "\<F> (send_flow_cont_upd state) = \<F> state"
  "\<F>_redges (send_flow_cont_upd state) = \<F>_redges state"
  "not_blocked (send_flow_cont_upd state) = not_blocked state"
  "balance (send_flow_cont_upd state) = balance state"
  "current_flow (send_flow_cont_upd state) = current_flow state"
  "\<Phi> (send_flow_cont_upd state) = \<Phi> state"
  by(auto simp add: send_flow_cont_upd_def Let_def \<Phi>_def F_def F_redges_def)

lemma send_flow_simps: 
  assumes "send_flow_dom state"
  shows   "send_flow_succ_cond state \<Longrightarrow> send_flow state = (send_flow_succ_upd state)"
          "send_flow_cont_cond state \<Longrightarrow> send_flow state = (send_flow_cont_upd state)"
          "send_flow_fail1_cond state \<Longrightarrow> send_flow state = (send_flow_fail_upd state)"
          "send_flow_fail2_cond state \<Longrightarrow> send_flow state = (send_flow_fail_upd state)"
          "send_flow_call1_cond state \<Longrightarrow> send_flow state = send_flow (send_flow_call1_upd state)"
          "send_flow_call2_cond state \<Longrightarrow> send_flow state = send_flow (send_flow_call2_upd state)"
proof(goal_cases)
  case 1
  thus ?case
    using  send_flow.psimps  assms
    by (auto elim: send_flow_succ_condE simp add: send_flow_succ_upd_def Let_def )
next
  case 2
  thus ?case
    by(auto elim!: send_flow_cont_condE simp add: send_flow.psimps[OF assms] send_flow_cont_upd_def)
next
  case 3
  thus ?case
    by(auto elim!: send_flow_fail1_condE simp add: send_flow.psimps[OF assms] send_flow_fail_upd_def)
next
  case 4
  thus ?case
    by(auto elim!: send_flow_fail2_condE simp add: send_flow.psimps[OF assms] send_flow_fail_upd_def)
next 
  case 5
  show ?case
  proof(rule send_flow_call1_condE[OF 5], goal_cases)
    case (1 f b \<gamma> s t P f' b' state')
    thus ?case  
      using send_flow.psimps assms
      by (auto simp add: send_flow_call1_upd_def Let_def  elim: send_flow_call1_condE)
  qed
next
  case 6
  show ?case
  proof(rule send_flow_call2_condE[OF 6], goal_cases)
    case (1 f b \<gamma> s t P f' b' state')
    thus ?case  
      using send_flow.psimps assms
      by (auto simp add: send_flow_call2_upd_def Let_def  elim: send_flow_call2_condE)
  qed
qed  

lemma send_flow_induct:
  assumes "send_flow_dom state"
    "\<And> state. \<lbrakk> send_flow_dom state ; 
             send_flow_call1_cond state \<Longrightarrow> P (send_flow_call1_upd state);
             send_flow_call2_cond state \<Longrightarrow> P (send_flow_call2_upd state) \<rbrakk> \<Longrightarrow> P state"
  shows "P state"
proof(rule send_flow.pinduct[OF assms(1)], goal_cases)
  case (1 state)
  note IH = this
  show ?case 
  proof(rule assms(2)[OF IH(1)], goal_cases)
    case 1
    then show ?case
      using IH(3)
      by(auto elim!:  send_flow_call1_condE[of state] 
           simp add: send_flow_call1_upd_def Let_def)
  next
    case 2
    then show ?case
      using IH(2)
      by(auto elim!:  send_flow_call2_condE[of state] 
           simp add: send_flow_call2_upd_def Let_def)
  qed
qed


lemma send_flow_dom_impl_same:
  assumes "send_flow_dom state"
  shows   "send_flow_impl state = send_flow state"
proof(induction rule: send_flow_induct[OF assms])
  case (1 state)
  note IH = this
  show ?case 
  proof(cases state rule: send_flow_cases)
    case 3
    show ?thesis 
      unfolding send_flow_simps(5)[OF IH(1) 3]
      by(rule trans[OF _ IH(2)], subst send_flow_impl.simps)
        (auto intro: send_flow_call1_condE[OF 3] 
          simp add: send_flow_call1_upd_def Let_def 3
          split: prod.split option.split)
  next
    case 4
    show ?thesis
      unfolding send_flow_simps(6)[OF IH(1) 4]
      by(rule trans[OF _ IH(3)], subst send_flow_impl.simps)
        (auto intro: send_flow_call2_condE[OF 4] 
          simp add: send_flow_call2_upd_def Let_def 4
          split: prod.split option.split)
  qed (auto elim!: send_flow_cont_condE send_flow_succ_condE send_flow_fail1_condE
                   send_flow_fail2_condE
      simp add: send_flow_impl.simps send_flow.psimps[OF IH(1)])
qed

lemma send_flow_dom_impl_cong:
  assumes "send_flow_dom state'" "state = state'"
  shows   "send_flow_impl state = send_flow state'"
  using send_flow_dom_impl_same assms by auto

lemma send_flow_dom_succ: "send_flow_succ_cond state \<Longrightarrow> send_flow_dom state"
  by(auto elim: send_flow_succ_condE intro: send_flow.domintros)

lemma send_flow_dom_cont: "send_flow_cont_cond state \<Longrightarrow> send_flow_dom state"
  by(auto elim!: send_flow_cont_condE intro: send_flow.domintros)

lemma send_flow_dom_fail1: "send_flow_fail1_cond state \<Longrightarrow> send_flow_dom state"
  by(auto elim!: send_flow_fail1_condE intro: send_flow.domintros)

lemma send_flow_dom_fail2: "send_flow_fail2_cond state \<Longrightarrow> send_flow_dom state"
  by(auto elim!: send_flow_fail2_condE intro: send_flow.domintros)

lemma send_flow_dom_call1: 
  "\<lbrakk>send_flow_call1_cond state; (send_flow_dom (send_flow_call1_upd state))\<rbrakk>
     \<Longrightarrow> send_flow_dom state" 
  by(auto intro: send_flow.domintros 
       simp add: send_flow_call1_upd_def Let_def
          elim!: send_flow_call1_condE)

lemma send_flow_dom_call2: 
  "\<lbrakk>send_flow_call2_cond state; (send_flow_dom (send_flow_call2_upd state))\<rbrakk>
    \<Longrightarrow> send_flow_dom state"
  by(auto intro: send_flow.domintros 
       simp add: send_flow_call2_upd_def Let_def
          elim!: send_flow_call2_condE)

lemma send_flow_simps_without_dom: 
  shows   "send_flow_succ_cond state \<Longrightarrow> send_flow state = (send_flow_succ_upd state)"
          "send_flow_cont_cond state \<Longrightarrow> send_flow state = (send_flow_cont_upd state)"
          "send_flow_fail1_cond state \<Longrightarrow> send_flow state = (send_flow_fail_upd state)"
          "send_flow_fail2_cond state \<Longrightarrow> send_flow state = (send_flow_fail_upd state)"
  using send_flow_dom_succ send_flow_dom_cont send_flow_dom_fail1 send_flow_dom_fail2
        send_flow_simps 
  by auto

definition "get_source_target_path_a_cond state s t P b \<gamma> f = (
             get_source_target_path_a state s = Some (t, P) \<and> s \<in> \<V>  \<and>
             underlying_invars state \<and> (\<forall> e \<in> \<F> state . abstract_flow_map f e > 0)\<and>
             b = balance state\<and> \<gamma> = current_\<gamma> state \<and> Some s = get_source state \<and>
             f = current_flow state  \<and> invar_gamma state \<and>
             implementation_invar state \<and> invar_isOptflow state)"

definition "impl_a_None_cond state  s b \<gamma> f = (
            b = balance state \<and> \<gamma> = current_\<gamma> state \<and> f = current_flow state\<and>
            s \<in> \<V> \<and> underlying_invars state \<and> (\<forall> e \<in> \<F> state . abstract_flow_map f e > 0)\<and>
            get_source_target_path_a state s = None \<and> Some s = get_source state \<and>
            implementation_invar state \<and> invar_gamma state)"

definition "get_source_target_path_b_cond state s t P b \<gamma> f =
           (get_source_target_path_b state t = Some (s, P) \<and> t \<in> \<V> \<and>
           underlying_invars state \<and>
           (\<forall> e \<in> \<F> state . abstract_flow_map f e > 0)
           \<and> b = balance state\<and> \<gamma> = current_\<gamma> state \<and>
            Some t = get_target state \<and> f = current_flow state \<and>
           invar_gamma state \<and>
           implementation_invar state \<and> invar_isOptflow state)"

definition "impl_b_None_cond state t b \<gamma> f = 
(b = balance state\<and> \<gamma> = current_\<gamma> state\<and> f = current_flow state \<and>
 t \<in> \<V> \<and> underlying_invars state \<and> (\<forall> e \<in> \<F> state . abstract_flow_map f e > 0)\<and>
 get_source_target_path_b state t = None\<and> Some t = get_target state \<and>
 implementation_invar state \<and> invar_gamma state )"

definition "vertex_selection_cond state b \<gamma> =
(b = balance state \<and> \<gamma> = current_\<gamma> state\<and> implementation_invar state)"

lemma get_source_target_path_a_condI:
  "\<lbrakk>get_source_target_path_a state s = Some (t, P) ; s \<in> \<V> ; 
    underlying_invars state; (\<forall> e \<in> \<F> state . abstract_flow_map f e > 0); 
    b = balance state; \<gamma> = current_\<gamma> state ; Some s = get_source state;
    f = current_flow state;  invar_gamma state;
    implementation_invar state;  invar_isOptflow state\<rbrakk> 
   \<Longrightarrow> get_source_target_path_a_cond state s t P b \<gamma> f"
  by(auto simp add: get_source_target_path_a_cond_def)

lemma  get_source_target_path_b_condI:
  "\<lbrakk>get_source_target_path_b state t = Some (s, P); t \<in> \<V>; underlying_invars state;
    (\<forall> e \<in> \<F> state . abstract_flow_map f e > 0); b = balance state; \<gamma> = current_\<gamma> state ;
    Some t = get_target state; f = current_flow state; invar_gamma state;
    implementation_invar state;  invar_isOptflow state\<rbrakk>
   \<Longrightarrow> get_source_target_path_b_cond state s t P b \<gamma> f"
  by(auto simp add: get_source_target_path_b_cond_def)

lemma get_source_target_path_a_condE:
  "get_source_target_path_a_cond state s t P b \<gamma> f \<Longrightarrow>
   (\<lbrakk>get_source_target_path_a state s = Some (t, P) ; s \<in> \<V> ; 
    underlying_invars state; (\<forall> e \<in> \<F> state . abstract_flow_map f e > 0); 
    b = balance state; \<gamma> = current_\<gamma> state ;  Some s = get_source state ;
    f = current_flow state; invar_gamma state;
    implementation_invar state;  invar_isOptflow state\<rbrakk> 
   \<Longrightarrow> Q) 
  \<Longrightarrow> Q"
  by(auto simp add: get_source_target_path_a_cond_def)

lemma  get_source_target_path_b_condE:
  "get_source_target_path_b_cond state s t P b \<gamma> f \<Longrightarrow>
   (\<lbrakk>get_source_target_path_b state t = Some (s, P); t \<in> \<V>; underlying_invars state;
    (\<forall> e \<in> \<F> state . abstract_flow_map f e > 0); b = balance state; \<gamma> = current_\<gamma> state ;
     Some t = get_target state;  f = current_flow state; invar_gamma state;
     implementation_invar state;  invar_isOptflow state\<rbrakk>
    \<Longrightarrow> Q) 
   \<Longrightarrow> Q"
  by(auto simp add: get_source_target_path_b_cond_def)

definition "get_source_cond s state b \<gamma>=
          (b = balance state \<and> \<gamma> = current_\<gamma> state \<and>  Some s = get_source state 
          \<and> implementation_invar state)"

lemma get_source_condI: 
  "\<lbrakk>b = balance state; \<gamma> = current_\<gamma> state;  Some s = get_source state;
   implementation_invar state\<rbrakk> 
   \<Longrightarrow>get_source_cond s state b \<gamma>"
  by(auto simp add: get_source_cond_def)

lemma get_source_condE: 
  "get_source_cond s state b \<gamma> \<Longrightarrow> 
   (\<lbrakk>b = balance state; \<gamma> = current_\<gamma> state;  Some s = get_source state; implementation_invar state\<rbrakk> 
     \<Longrightarrow>P) 
   \<Longrightarrow> P"
  by(auto simp add: get_source_cond_def)

definition "get_target_cond t state b \<gamma>= 
(b = balance state \<and> \<gamma> = current_\<gamma> state \<and> Some t = get_target state \<and>
implementation_invar state)"

lemma get_target_condI: 
  "\<lbrakk>b = balance state ; \<gamma> = current_\<gamma> state; Some t = get_target state;
    implementation_invar state\<rbrakk> \<Longrightarrow> get_target_cond t state b \<gamma>"
  by(auto simp add: get_target_cond_def)

lemma get_target_condE: 
  "get_target_cond t state b \<gamma> \<Longrightarrow>
   (\<lbrakk>b = balance state ; \<gamma> = current_\<gamma> state; Some t = get_target state; implementation_invar state\<rbrakk> 
     \<Longrightarrow> P) 
   \<Longrightarrow> P"
  by(auto simp add: get_target_cond_def)

lemma impl_a_None_condI:
  "\<lbrakk>b = balance state; \<gamma> = current_\<gamma> state; f = current_flow state;
   s \<in> \<V>; underlying_invars state; (\<forall> e \<in> \<F> state . abstract_flow_map f e > 0);
   get_source_target_path_a state s = None; Some s = get_source state;
    implementation_invar state; invar_gamma state\<rbrakk>
   \<Longrightarrow>impl_a_None_cond state s b \<gamma> f"
  by(auto simp add: impl_a_None_cond_def)

lemma impl_a_None_condE:
  "impl_a_None_cond state s b \<gamma> f \<Longrightarrow>
   (\<lbrakk>b = balance state; \<gamma> = current_\<gamma> state; f = current_flow state;
     s \<in> \<V>; underlying_invars state; (\<forall> e \<in> \<F> state . abstract_flow_map f e > 0);
     get_source_target_path_a state s = None; Some s = get_source state;
     implementation_invar state; invar_gamma state\<rbrakk>
   \<Longrightarrow>P) 
  \<Longrightarrow> P"
  by(auto simp add: impl_a_None_cond_def)

lemma impl_b_None_condI:
  "\<lbrakk>b = balance state; \<gamma> = current_\<gamma> state; f = current_flow state;
    t \<in> \<V>; underlying_invars state; (\<forall> e \<in> \<F> state . abstract_flow_map f e > 0);
    get_source_target_path_b state t = None; Some t = get_target state;
    implementation_invar state; invar_gamma state \<rbrakk>
   \<Longrightarrow> impl_b_None_cond state t b \<gamma> f"
  by(auto simp add: impl_b_None_cond_def)

lemma impl_b_None_condE:
  "impl_b_None_cond state t b \<gamma> f \<Longrightarrow> 
   (\<lbrakk>b = balance state; \<gamma> = current_\<gamma> state; f = current_flow state;  t \<in> \<V>; 
     underlying_invars state; (\<forall> e \<in> \<F> state . abstract_flow_map f e > 0);
     get_source_target_path_b state t = None; Some t = get_target state;
    implementation_invar state; invar_gamma state \<rbrakk> 
   \<Longrightarrow> P) 
  \<Longrightarrow> P"
  by(auto simp add: impl_b_None_cond_def)

lemma vertex_selection_condI: 
  "\<lbrakk>b = balance state; \<gamma> = current_\<gamma> state; implementation_invar state\<rbrakk>
   \<Longrightarrow> vertex_selection_cond state b \<gamma>"
  by(auto simp add: vertex_selection_cond_def)

lemma vertex_selection_condE: 
  "vertex_selection_cond state b \<gamma> \<Longrightarrow> 
  (\<lbrakk>b = balance state; \<gamma> = current_\<gamma> state; implementation_invar state\<rbrakk>
    \<Longrightarrow> P) 
  \<Longrightarrow> P"
  by(auto simp add: vertex_selection_cond_def)

end

locale send_flow = 
  send_flow_spec +
  algo +
  assumes get_source_target_path_a_axioms:                         
    "\<And> state s t P b \<gamma> f. get_source_target_path_a_cond state s t P b \<gamma> f \<Longrightarrow> is_min_path (abstract_flow_map f) s t P"
    "\<And> state s t P b \<gamma> f. get_source_target_path_a_cond state s t P b \<gamma> f  \<Longrightarrow> oedge ` set P \<subseteq> to_set (actives state) \<union> \<F> state"
    "\<And> state s t P b \<gamma> f. get_source_target_path_a_cond state s t P b \<gamma> f  \<Longrightarrow>
            t \<in> \<V> \<and> abstract_bal_map b t < - \<epsilon> * \<gamma>"
    and get_source_target_path_b_axioms:"\<And> state s t P b \<gamma> f. get_source_target_path_b_cond state s t P b \<gamma> f  \<Longrightarrow> is_min_path (abstract_flow_map f) s t P"
    "\<And> state s t P b \<gamma> f. get_source_target_path_b_cond state s t P b \<gamma> f \<Longrightarrow> oedge ` set P \<subseteq> to_set (actives state) \<union> \<F> state"
    "\<And> state s t P b \<gamma> f. get_source_target_path_b_cond state s t P b \<gamma> f
            \<Longrightarrow> s \<in> \<V> \<and> abstract_bal_map b s > \<epsilon> * \<gamma>"
    and get_source_axioms:
    "\<And> s state b \<gamma>. get_source_cond s state b \<gamma> \<Longrightarrow> s \<in> \<V> \<and> abstract_bal_map b s > (1 - \<epsilon>) * \<gamma>"
    "\<And> state b \<gamma>. vertex_selection_cond state b  \<gamma>
         \<Longrightarrow> \<not> (\<exists> s \<in> \<V>. abstract_bal_map b s > (1 - \<epsilon>) * \<gamma>) \<longleftrightarrow> ((get_source state) = None )"
    and get_target_axioms:
    "\<And> t state b \<gamma>. get_target_cond t state b \<gamma>\<Longrightarrow> t \<in> \<V> \<and> abstract_bal_map b t < - (1 -\<epsilon>) * \<gamma>"
    "\<And> state b \<gamma>. vertex_selection_cond state b  \<gamma>
             \<Longrightarrow> \<not> (\<exists> t \<in> \<V>. abstract_bal_map b t < -(1 - \<epsilon>) * \<gamma>) \<longleftrightarrow> ((get_target state) = None)"
    and impl_a_None:
    "\<And> state s b \<gamma> f.  impl_a_None_cond state s b \<gamma> f
    \<Longrightarrow> \<not> (\<exists> t \<in> \<V>. abstract_bal_map b t < - \<epsilon> * \<gamma> \<and> resreach (abstract_flow_map f) s t) 
           \<longleftrightarrow> get_source_target_path_a state s = None"
    and impl_b_None:
    "\<And> state t b \<gamma> f. impl_b_None_cond state t b \<gamma> f
     \<Longrightarrow> \<not> (\<exists> s \<in> \<V>. abstract_bal_map b s > \<epsilon> * \<gamma> \<and> resreach (abstract_flow_map f) s t) 
           \<longleftrightarrow> get_source_target_path_b state t = None"
    and test_all_vertices_zero_balance:
    "\<And> state b. \<lbrakk>b = balance state; implementation_invar state\<rbrakk>
        \<Longrightarrow> test_all_vertices_zero_balance state \<longleftrightarrow> (\<forall> v \<in> \<V>. abstract_bal_map b v = 0)"
begin

subsection \<open>Single Step Lemmas\<close>

lemma if_send_flow_succ_cond:
  assumes "send_flow_succ_cond state"
          "implementation_invar state"
  shows "\<forall> v \<in> \<V>. a_balance state v = 0"
  using assms(1,2) send_flow_succ_condE 
  by(auto simp add: test_all_vertices_zero_balance elim!: send_flow_succ_condE)

lemma if_send_flow_call1_cond_basic:
  assumes "send_flow_call1_cond state"
          "implementation_invar state"
          "Some s = get_source state"
  shows "\<exists> v \<in> \<V>. a_balance state v \<noteq> 0"
        "s \<in> \<V>" "a_balance state s > (1 - \<epsilon>) * current_\<gamma> state"
  using assms(1,2) 
    get_source_axioms(1)[OF get_source_condI, OF refl refl assms(3)] assms(1,2)
  by(auto simp add: test_all_vertices_zero_balance elim!: send_flow_call1_condE)

lemma if_send_flow_call1_cond_advanced:
  assumes "send_flow_call1_cond state"
          "implementation_invar state"
          "Some s = get_source state"
          "Some (t, P) = get_source_target_path_a state s"
          "underlying_invars state"
          "invar_gamma state"
          "pos_flow_F state"
          "invar_isOptflow state"
  shows   "t \<in> \<V>" "a_balance state t < - \<epsilon> * current_\<gamma> state"
          "resreach (a_current_flow state) s t"
          "is_min_path (a_current_flow state) s t P"
          "oedge ` set P \<subseteq> to_set (actives state) \<union> \<F> state"
          "distinct P" "Rcap (a_current_flow state) (set P) > 0"
  using get_source_target_path_a_axioms[OF get_source_target_path_a_condI,
         OF assms(4)[symmetric] _ assms(5) _ refl refl assms(3) refl assms(6,2,8)]
         assms(1,2,3,7) if_send_flow_call1_cond_basic(2)[OF assms(1,2,3)] 
  by(auto elim!: pos_flow_FE intro!: is_min_path_resreach is_min_path_Rcap
      is_min_path_distinct) 

lemma if_send_flow_fail1_cond_basic:
  assumes "send_flow_fail1_cond state"
          "implementation_invar state"
          "Some s = get_source state"
  shows   "\<exists> v \<in> \<V>. a_balance state v \<noteq> 0"
          "s \<in> \<V>" "a_balance state s > (1 - \<epsilon>) * current_\<gamma> state"
  using assms(1,2) 
    get_source_axioms(1)[OF get_source_condI, OF refl refl assms(3)] assms(1,2)
  by(auto simp add: test_all_vertices_zero_balance elim!: send_flow_fail1_condE)

lemma if_send_flow_fail1_cond_advanced:
  assumes "send_flow_fail1_cond state"
          "implementation_invar state"
          "Some s = get_source state"
          "None = get_source_target_path_a state s"
          "underlying_invars state"
          "invar_gamma state"
          "pos_flow_F state"
          "invar_isOptflow state"
  shows "\<nexists> t. t \<in> \<V> \<and> a_balance state t < - \<epsilon> * current_\<gamma> state \<and>
                resreach (a_current_flow state) s t"
  using impl_a_None[OF impl_a_None_condI, OF refl refl refl _ assms(5) _  _ assms(3,2,6)]
    assms(1,2,3,4,7) if_send_flow_fail1_cond_basic(2)
  by(auto elim: pos_flow_FE)

lemma if_send_flow_call2_cond_basic:
  assumes "send_flow_call2_cond state"
          "implementation_invar state"
          "Some t = get_target state"
  shows "\<exists> v \<in> \<V>. a_balance state v \<noteq> 0"
        "\<nexists> s. s \<in> \<V> \<and> a_balance state t > (1 - \<epsilon>) * current_\<gamma> state"
        "t \<in> \<V>" "a_balance state t < - (1 - \<epsilon>) * current_\<gamma> state"
  using assms(1,2)  get_source_axioms(2)[OF  vertex_selection_condI] 
    get_target_axioms(1)[OF get_target_condI, OF refl refl assms(3)] assms(1,2)
  by(auto simp add: test_all_vertices_zero_balance elim!: send_flow_call2_condE)

lemma if_send_flow_call2_cond_advanced:
  assumes "send_flow_call2_cond state"
          "implementation_invar state"
          "None = get_source state"
          "Some t = get_target state"
          "Some (s, P) = get_source_target_path_b state t"
          "underlying_invars state"
          "invar_gamma state"
          "pos_flow_F state"
          "invar_isOptflow state"
  shows "s \<in> \<V>" "a_balance state s > \<epsilon> * current_\<gamma> state"
        "resreach (a_current_flow state) s t"
        "is_min_path (a_current_flow state) s t P"
        "oedge ` set P \<subseteq> to_set (actives state) \<union> \<F> state"
        "distinct P" "Rcap (a_current_flow state) (set P) > 0"
  using get_source_target_path_b_axioms[OF get_source_target_path_b_condI,
      OF assms(5)[symmetric] _ assms(6) _  refl refl assms(4) refl assms(7,2,9)]
  using if_send_flow_call2_cond_basic(3)[OF assms(1,2,4)] assms(8)
  by(auto elim!: pos_flow_FE intro!: is_min_path_resreach is_min_path_Rcap
      is_min_path_distinct)

lemma if_send_flow_fail2_cond_basic:
  assumes "send_flow_fail2_cond state"
          "implementation_invar state"
          "Some t = get_target state"
  shows "\<exists> v \<in> \<V>. a_balance state v \<noteq> 0"
        "\<nexists> s. s \<in> \<V> \<and> a_balance state t > (1 - \<epsilon>) * current_\<gamma> state"
        "t \<in> \<V>" "a_balance state t < - (1 - \<epsilon>) * current_\<gamma> state"
  using assms(1,2)  get_source_axioms(2)[OF  vertex_selection_condI] 
    get_target_axioms(1)[OF get_target_condI, OF refl refl assms(3)] assms(1,2)
  by(auto simp add: test_all_vertices_zero_balance elim!: send_flow_fail2_condE)

lemma if_send_flow_fail2_cond_advanced:
  assumes "send_flow_fail2_cond state"
          "implementation_invar state"
          "None = get_source state"
          "Some t = get_target state"
          "None = get_source_target_path_b state t"
          "underlying_invars state"
          "invar_gamma state"
          "pos_flow_F state"
          "invar_isOptflow state"
  shows   "\<nexists> s. s \<in> \<V> \<and> a_balance state s > \<epsilon> * current_\<gamma> state \<and> 
                   resreach (a_current_flow state) s t"
  using impl_b_None[OF impl_b_None_condI, OF refl refl refl _ assms(6) _  _ assms(4,2,7)]
    if_send_flow_fail2_cond_basic(3) assms(1,2,4,5,8) 
  by(auto elim!: pos_flow_FE )

lemma if_send_flow_cont_cond_basic:
  assumes "send_flow_cont_cond state"
          "implementation_invar state"
          "None = get_source state"
          "None = get_target state"
  shows "\<exists> v \<in> \<V>. a_balance state v \<noteq> 0"
        "\<nexists> s. s \<in> \<V> \<and> a_balance state s > (1 - \<epsilon>) * current_\<gamma> state"
        "\<nexists> t. t \<in> \<V> \<and> a_balance state t < - (1 - \<epsilon>) * current_\<gamma> state"
  using get_source_axioms(2)[OF  vertex_selection_condI, OF refl refl assms(2)]
        get_target_axioms(2)[OF  vertex_selection_condI, OF refl refl assms(2)]
  using assms test_all_vertices_zero_balance
  by(auto elim: send_flow_cont_condE)

lemma send_flow_call1_inv_pos_bal_rep_pres:
  assumes "send_flow_call1_cond state"
          "invar_gamma state" "implementation_invar state"
          "underlying_invars state" "pos_flow_F state"
          "invar_isOptflow state"
  shows   "inv_pos_bal_rep (send_flow_call1_upd state)"
proof(rule send_flow_call1_condE[OF assms(1)], goal_cases)
  case (1 f b \<gamma> s t P f' b' state')
  note unf = this
  hence s_prop:"(1 - \<epsilon>) * \<gamma> < abstract_bal_map b s " "s \<in> \<V>" 
    using assms(1,3) if_send_flow_call1_cond_basic by auto
  have t_prop:" abstract_bal_map b t < - \<epsilon> * \<gamma> " "resreach (abstract_flow_map f) s t " " t \<in> \<V>"
    using if_send_flow_call1_cond_advanced(1-3)[OF assms(1,3) _ _ assms(4,2,5,6)] 1 by auto
  have b_s: "abstract_bal_map b s > 0"
    using s_prop assms(2)
    unfolding invar_gamma_def unf 
    by (smt (verit, ccfv_SIG) \<epsilon>_axiom(2) add_divide_distrib divide_eq_1_iff mul_zero_cancel)
  have b_t: "abstract_bal_map b t < 0"
    using t_prop assms(2)
    unfolding invar_gamma_def unf
    by (smt (verit, del_insts) \<epsilon>_axiom(1) mult_neg_pos)
  have s_rep: "representative state s = s" 
    using s_prop  b_s unf
    by (simp add: assms(4) from_underlying_invars'(12))
  have t_rep: "representative state t = t" 
    using t_prop  b_t unf
    by (simp add: assms(4) from_underlying_invars'(12))
  show ?case 
  proof(rule inv_pos_bal_repI, goal_cases)
    case (1 v)
    have same_rep:"representative (send_flow_call1_upd state) v = representative state v"
      using send_flow_call1_upd_changes(5) by fastforce
    have b_b': "b' = balance (send_flow_call1_upd state)" 
      by(auto split: option.split prod.split 
          simp add: unf send_flow_call1_upd_def Let_def )
    then show ?case 
    proof(cases "v = s")
      case True
      show ?thesis 
        using True s_rep same_rep by argo
    next
      case False
      note false = this
      then show ?thesis 
      proof(cases "v = t")
        case True
        then show ?thesis 
          using same_rep t_rep by auto
      next
        case False
        hence "abstract_bal_map b' v = abstract_bal_map b v" 
          using assms(3) false unf(2,8) by fastforce
        hence "abstract_bal_map b v \<noteq> 0" using 1 b_b' by simp
        hence "representative state v = v"
          using 1 assms(4) from_underlying_invars'(12) unf(2) by blast
        then show ?thesis
          by (simp add: send_flow_call1_upd_changes(5))
      qed
    qed
  qed
qed

lemma send_flow_call2_inv_pos_bal_rep_pres:
  assumes "send_flow_call2_cond state" 
          "invar_gamma state" "implementation_invar state"
          "underlying_invars state" "pos_flow_F state"
          "invar_isOptflow state"
  shows   "inv_pos_bal_rep (send_flow_call2_upd state)"
proof(rule send_flow_call2_condE[OF assms(1)], goal_cases)
  case (1 f b \<gamma> t s P f' b' state')
  note unf = this
  have t_prop:"abstract_bal_map b t < - (1-\<epsilon>) * \<gamma> "  " t \<in> \<V>" 
    using assms(1,3) if_send_flow_call2_cond_basic unf(2,3,6) by auto
  hence s_prop:"\<epsilon> * \<gamma> < abstract_bal_map b s " "s \<in> \<V>" "resreach (abstract_flow_map f) s t " 
    using if_send_flow_call2_cond_advanced(1-3)[OF assms(1,3) _ _ _ assms(4,2,5,6)] 1 by auto    
  have b_s: "abstract_bal_map b s > 0"
    using s_prop assms(2)
    unfolding invar_gamma_def unf 
    by (smt (verit) \<epsilon>_axiom(1) mult_pos_pos)
  have b_t: "abstract_bal_map b t < 0"
    using t_prop assms(2)  \<epsilon>_axiom(2)
    unfolding invar_gamma_def unf
    by auto (smt (z3) mult_neg_pos)
  have s_rep: "representative state s = s" 
    using s_prop assms(3) b_s unf
    by (simp add: assms(4) from_underlying_invars'(12))
  have t_rep: "representative state t = t" 
    using t_prop assms(3) b_t unf 
    by (simp add: assms(4) from_underlying_invars'(12))
  show ?case 
  proof(rule inv_pos_bal_repI, goal_cases)
    case (1 v)
    have same_rep:"representative (send_flow_call2_upd state) v = representative state v"
      by (simp add: send_flow_call2_upd_changes(5))
    have b_b': "b' = balance (send_flow_call2_upd state)"
      by(auto split: option.split prod.split 
          simp add: unf send_flow_call2_upd_def Let_def)
    then show ?case 
    proof(cases "v = s")
      case True
      show ?thesis
        using True s_rep same_rep by argo
    next
      case False
      note false = this
      then show ?thesis 
      proof(cases "v = t")
        case True
        then show ?thesis
          using same_rep t_rep by auto
      next
        case False
        hence "abstract_bal_map b' v = abstract_bal_map b v" 
          using assms(3) false unf(2,9) by fastforce
        hence "abstract_bal_map b v \<noteq> 0" using 1 b_b' by simp
        hence "representative state v = v"
          by (simp add: "1"(1) assms(4) from_underlying_invars'(12) unf(2))
        then show ?thesis 
          using same_rep by auto
      qed
    qed
  qed
qed

lemma invar_aux_pres_call1:
  assumes "send_flow_call1_cond state"
          "invar_gamma state" "implementation_invar state"
          "underlying_invars state" "pos_flow_F state"
          "invar_isOptflow state"
  shows   "underlying_invars (send_flow_call1_upd state)"
  apply(rule underlying_invars_pres[of state, OF assms(4)])      
  using send_flow_call1_upd_changes[of state] 
    send_flow_call1_inv_pos_bal_rep_pres[OF assms(1,2,3,4,5,6)]
  by(auto elim!:  inv_pos_bal_repE intro: forest_symmetic
      simp add: validF_def) 

lemma invar_aux_pres_call2:
  assumes "send_flow_call2_cond state"
          "invar_gamma state" "implementation_invar state"
          "underlying_invars state" "pos_flow_F state"
          "invar_isOptflow state"
  shows   "underlying_invars (send_flow_call2_upd state)"
  apply(rule underlying_invars_pres[of state, OF assms(4)])      
  using send_flow_call2_upd_changes[of state] 
    send_flow_call2_inv_pos_bal_rep_pres[OF assms(1,2,3,4,5,6)]
  by(auto elim!:  inv_pos_bal_repE intro: forest_symmetic
      simp add: validF_def) 

lemma underlying_invars_pres_succ:
  "underlying_invars state \<Longrightarrow> underlying_invars (send_flow_succ_upd state)"
  and underlying_invars_pres_cont:
  "underlying_invars state \<Longrightarrow> underlying_invars (send_flow_cont_upd state)"
  and underlying_invars_pres_fail:
  "underlying_invars  state \<Longrightarrow> underlying_invars  (send_flow_fail_upd state)"
  using  send_flow_succ_upd_changes[of state] send_flow_cont_upd_changes[of state]
    send_flow_fail_upd_changes[of state]
  by(auto simp add: underlying_invars_def inv_actives_in_E_def inv_digraph_abs_F_in_E_def inv_forest_in_E_def
      inv_forest_actives_disjoint_def inv_finite_forest_def inv_conversion_consistent_def inv_reachable_same_rep_def 
      inv_rep_reachable_def inv_reps_in_V_def inv_components_in_V_def inv_active_different_comps_def 
      inv_pos_bal_rep_def inv_inactive_same_component_def inv_dbltn_graph_forest_def inv_forest_in_V_def
      inv_comp_card_correct_def  inv_set_invar_actives_def inv_forest_good_graph_def inv_digraph_abs_\<FF>_sym_def 
      inv_unbl_iff_forest_active_def
      elim: validFE intro!: validFI)

lemma implementation_invar_pres_succ:
  "implementation_invar state \<Longrightarrow> implementation_invar (send_flow_succ_upd state)"
  and implementation_invar_pres_cont:
  "implementation_invar state \<Longrightarrow> implementation_invar (send_flow_cont_upd state)"
  and implementation_invar_pres_fail:
  "implementation_invar state \<Longrightarrow> implementation_invar  (send_flow_fail_upd state)"
  by(unfold implementation_invar_def
      send_flow_succ_upd_changes[of state] send_flow_cont_upd_changes[of state]
      send_flow_fail_upd_changes[of state]) auto

lemma invar_gamma_pres_succ:
  "invar_gamma state \<Longrightarrow> invar_gamma (send_flow_succ_upd state)"
  by(auto simp add: send_flow_succ_upd_def invar_gamma_def)

lemma invar_gamma_pres_cont:
  "invar_gamma state \<Longrightarrow> invar_gamma (send_flow_cont_upd state)"
  by(simp add: send_flow_cont_upd_def invar_gamma_def)

lemma invar_gamma_pres_fail:
  "invar_gamma state \<Longrightarrow> invar_gamma (send_flow_fail_upd state)"
  by(simp add: send_flow_fail_upd_def invar_gamma_def)

lemma invar_gamma_pres_call1:
  "invar_gamma state \<Longrightarrow> invar_gamma (send_flow_call1_upd state)"
  by(auto simp add: send_flow_call1_upd_def invar_gamma_def Let_def split: prod.split)

lemma invar_gamma_pres_call2:
  "invar_gamma state \<Longrightarrow> invar_gamma (send_flow_call2_upd state)"
  by(auto simp add: send_flow_call2_upd_def invar_gamma_def Let_def split: prod.split)

theorem send_flow_invar_gamma_pres: 
  assumes "send_flow_dom state" "invar_gamma state"
  shows   "invar_gamma (send_flow state)"
  using assms(2) 
proof(induction rule: send_flow_induct[OF assms(1)])
  case (1 state)
  note IH = this
  then show ?case 
  proof(cases rule: send_flow_cases[of state])
    case 1
    show ?thesis
      by(subst  send_flow_simps(2)[OF IH(1) 1])
        (force intro!: invar_gamma_pres_cont[of state] 
             simp add: send_flow_cont_upd_def[of state] 1 IH)
  next
    case 2
    show ?thesis
      by(subst  send_flow_simps(1)[OF IH(1) 2])
        (force intro!: invar_gamma_pres_succ[of state] 
             simp add: send_flow_succ_upd_def[of state] 2 IH)
  next 
    case 3
    show ?thesis
      using send_flow_call1_upd_changes[of state] 1 
      by (auto intro!: IH(2)[OF 3] invar_gamma_pres_call1 
             simp add: send_flow_simps(5)[OF 1(1) 3])
  next 
    case 4
    show ?thesis
      using send_flow_call2_upd_changes[of state] IH
      by (auto intro!: IH(3)[OF 4] invar_gamma_pres_call2 
             simp add: send_flow_simps(6)[OF 1(1) 4])
  next
    case 5
    show ?thesis
      by(subst send_flow_simps(3)[OF IH(1) 5])
        (force intro!: invar_gamma_pres_fail[of state ] 
            simp add: send_flow_fail_upd_def[of state] IH 1)
  next
    case 6
    show ?thesis
      by(subst send_flow_simps(4)[OF IH(1) 6])
        (force intro!: invar_gamma_pres_fail[of state ]
             simp add: send_flow_fail_upd_def[of state] 6 IH)
  qed
qed

lemma send_flow_changes_\<FF>: 
  assumes "send_flow_dom state"
  shows   "\<FF> (send_flow state) = \<FF> state"
proof(induction rule: send_flow_induct[OF assms(1)])
  case (1 state)
  note IH = this
  show ?case
  proof(cases rule: send_flow_cases[of state])
    case 1
    then show ?thesis 
      using send_flow_cont_upd_changes[of state] 
      by (simp add:  send_flow_simps(2)[OF IH(1) 1])
  next
    case 2
    then show ?thesis
      using send_flow_succ_upd_changes[of state] 
      by (simp add: send_flow_simps(1)[OF IH(1) 2])
  next
    case 3
    then show ?thesis 
      using send_flow_simps(5)[OF IH(1) 3] IH send_flow_call1_upd_changes 
      by auto
  next
    case 4
    then show ?thesis 
      using send_flow_simps(6)[OF IH(1) 4] IH send_flow_call2_upd_changes 
      by auto
  next
    case 5
    then show ?thesis 
      using send_flow_fail_upd_changes[of state] 
      by (simp add: send_flow_simps(3)[OF IH(1) 5])
  next
    case 6
    then show ?thesis
      using send_flow_fail_upd_changes[of state] 
      by (simp add: send_flow_simps(4)[OF IH(1) 6])
  qed
qed

lemma send_flow_changes_conv_to_rdg: 
  assumes "send_flow_dom state"
  shows   "conv_to_rdg (send_flow state) = conv_to_rdg state"
proof(induction rule: send_flow_induct[OF assms(1)])
  case (1 state)
  note IH = this
  show ?case
  proof(cases rule: send_flow_cases[of state])
    case 1
    then show ?thesis 
      using send_flow_cont_upd_changes[of state] 
      by (simp add: send_flow_simps(2)[OF IH(1) 1])
  next
    case 2
    then show ?thesis
      using send_flow_succ_upd_changes[of state] 
      by (simp add:  send_flow_simps(1)[OF IH(1) 2])
  next
    case 3
    then show ?thesis 
      using send_flow_simps(5)[OF IH(1) 3] IH send_flow_call1_upd_changes 
      by auto
  next
    case 4
    then show ?thesis 
      using send_flow_simps(6)[OF IH(1) 4] IH send_flow_call2_upd_changes 
      by auto
  next
    case 5
    then show ?thesis 
      using send_flow_fail_upd_changes[of state]
      by(simp add: send_flow_simps(3)[OF IH(1) 5])
  next
    case 6
    then show ?thesis
      using send_flow_fail_upd_changes[of state] 
      by (simp add: send_flow_simps(4)[OF IH(1) 6])
  qed
qed

lemma send_flow_changes_actives: 
  assumes "send_flow_dom state"
  shows   "actives (send_flow state) = actives state"
proof(induction rule: send_flow_induct[OF assms(1)])
  case (1 state)
  note IH = this
  show ?case
  proof(cases rule: send_flow_cases[of state])
    case 1
    then show ?thesis 
      using send_flow_cont_upd_changes[of state] 
      by (simp add: send_flow_simps(2)[OF IH(1) 1])
  next
    case 2
    then show ?thesis
      using send_flow_succ_upd_changes[of state] 
      by (simp add: send_flow_simps(1)[OF IH(1) 2])
  next
    case 3
    then show ?thesis 
      using send_flow_simps(5)[OF IH(1) 3] IH send_flow_call1_upd_changes 
      by auto
  next
    case 4
    then show ?thesis 
      using send_flow_simps(6)[OF IH(1) 4] IH send_flow_call2_upd_changes 
      by auto
  next
    case 5
    then show ?thesis 
      using send_flow_fail_upd_changes[of state] 
      by (simp add: send_flow_simps(3)[OF IH(1) 5])
  next
    case 6
    then show ?thesis
      using send_flow_fail_upd_changes[of state] 
      by (simp add: send_flow_simps(4)[OF IH(1) 6])
  qed
qed

lemma send_flow_changes_current_\<gamma>: 
  assumes "send_flow_dom state"
  shows   "current_\<gamma> (send_flow state) = current_\<gamma> state"
proof(induction rule: send_flow_induct[OF assms(1)])
  case (1 state)
  note IH = this
  show ?case
  proof(cases rule: send_flow_cases[of state])
    case 1
    then show ?thesis 
      using send_flow_cont_upd_changes[of state] 
      by (simp add: send_flow_simps(2)[OF IH(1) 1])
  next
    case 2
    then show ?thesis
      using send_flow_succ_upd_changes[of state]
      by (simp add: send_flow_simps(1)[OF IH(1) 2])
  next
    case 3
    then show ?thesis 
      using send_flow_simps(5)[OF IH(1) 3] IH send_flow_call1_upd_changes 
      by auto
  next
    case 4
    then show ?thesis 
      using send_flow_simps(6)[OF IH(1) 4] IH send_flow_call2_upd_changes 
      by auto
  next
    case 5
    then show ?thesis 
      using send_flow_fail_upd_changes[of state] 
      by (simp add:  send_flow_simps(3)[OF IH(1) 5])
  next
    case 6
    then show ?thesis
      using send_flow_fail_upd_changes[of state] 
      by (simp add: send_flow_simps(4)[OF IH(1) 6])
  qed
qed

lemma send_flow_changes_rep_comp_card: 
  assumes "send_flow_dom state"
  shows   "rep_comp_card (send_flow state) = rep_comp_card state"
proof(induction rule: send_flow_induct[OF assms(1)])
  case (1 state)
  note IH = this
  show ?case
  proof(cases rule: send_flow_cases[of state])
    case 1
    then show ?thesis 
      using send_flow_cont_upd_changes[of state] 
      by (simp add: send_flow_simps(2)[OF IH(1) 1])
  next
    case 2
    then show ?thesis
      using send_flow_succ_upd_changes[of state] 
      by (simp add:  send_flow_simps(1)[OF IH(1) 2])
  next
    case 3
    then show ?thesis 
      using send_flow_simps(5)[OF IH(1) 3] IH send_flow_call1_upd_changes 
      by auto
  next
    case 4
    then show ?thesis 
      using send_flow_simps(6)[OF IH(1) 4] IH send_flow_call2_upd_changes 
      by auto
  next
    case 5
    then show ?thesis 
      using send_flow_fail_upd_changes[of state] 
      by (simp add: send_flow_simps(3)[OF IH(1) 5])
  next
    case 6
    then show ?thesis
      using send_flow_fail_upd_changes[of state] 
      by (simp add: send_flow_simps(4)[OF IH(1) 6])
  qed
qed

lemma send_flow_changes_representative: 
  assumes "send_flow_dom state"
  shows   "representative (send_flow state) = representative state"
  by (simp add: assms send_flow_changes_rep_comp_card)

lemma send_flow_changes_comp_card: 
  assumes "send_flow_dom state"
  shows   "comp_card (send_flow state) = comp_card state"
  by (simp add: assms send_flow_changes_rep_comp_card)

lemma send_flow_changes_\<F>_redges: 
  assumes "send_flow_dom state"
  shows   "\<F>_redges (send_flow state) = \<F>_redges state"
  by (simp add: assms send_flow_changes_\<FF> send_flow_changes_conv_to_rdg F_def F_redges_def)

lemma send_flow_changes_\<F>: 
  assumes "send_flow_dom state"
  shows   "\<F> (send_flow state) = \<F> state" 
  using assms send_flow_changes_\<F>_redges by (force simp add: F_def F_redges_def)

lemma send_flow_changes_not_blocked: 
  assumes "send_flow_dom state"
  shows   "not_blocked (send_flow state) = not_blocked state"
proof(induction rule: send_flow_induct[OF assms(1)])
  case (1 state)
  note IH = this
  show ?case
  proof(cases rule: send_flow_cases[of state])
    case 1
    then show ?thesis 
      using send_flow_cont_upd_changes[of state] 
      by (simp add: send_flow_simps(2)[OF IH(1) 1])
  next
    case 2
    then show ?thesis
      using send_flow_succ_upd_changes[of state] 
      by (simp add:  send_flow_simps(1)[OF IH(1) 2])
  next
    case 3
    then show ?thesis 
      using send_flow_simps(5)[OF IH(1) 3] IH send_flow_call1_upd_changes 
      by auto
  next
    case 4
    then show ?thesis 
      using send_flow_simps(6)[OF IH(1) 4] IH send_flow_call2_upd_changes 
      by auto
  next
    case 5
    then show ?thesis 
      using send_flow_fail_upd_changes[of state] 
      by (simp add: send_flow_simps(3)[OF IH(1) 5])
  next
    case 6
    then show ?thesis
      using send_flow_fail_upd_changes[of state] 
      by (simp add: send_flow_simps(4)[OF IH(1) 6])
  qed
qed

lemma send_flow_call1_cond_Phi_decr:
  assumes "send_flow_call1_cond state" "invar_gamma state"
          "underlying_invars state" "implementation_invar state"
          "pos_flow_F state"  "invar_isOptflow state"
  shows   "\<Phi> (send_flow_call1_upd state) \<le> \<Phi> state - 1"
proof(rule send_flow_call1_condE[OF assms(1)], goal_cases)
  case (1 f b \<gamma> s t P f' b' state')
  hence "state' = send_flow_call1_upd state" 
    by(auto simp add: send_flow_call1_upd_def  Let_def)
  have gamma_0: "\<gamma> > 0" using assms by(auto elim!: invar_gammaE simp add: 1)
  have sP: "(1 - \<epsilon>) * \<gamma> < abstract_bal_map b s"  "s \<in> \<V>" 
    using  "1"(2,3,5) assms(1,4) if_send_flow_call1_cond_basic[OF assms(1,4)] 
    by auto
  have tP: "abstract_bal_map b t < - \<epsilon> * \<gamma>" "resreach (abstract_flow_map f) s t" "t \<in> \<V>" 
    using if_send_flow_call1_cond_advanced[OF assms(1,4) _ _ assms(3,2,5,6)] 1 by auto
  have s_neq_t:"s \<noteq> t" using sP tP gamma_0
    by (smt (verit, best) mult_less_cancel_right_disj)
  have b'_is: "abstract_bal_map b'= 
        (\<lambda>v. if v = s then abstract_bal_map b s - \<gamma>
        else if v = t then abstract_bal_map b t + \<gamma> else abstract_bal_map b v)"
    using abstract_bal_map_homo_move_gamma[OF _ refl, of b \<gamma> s t] assms(4) 
    by (auto simp add: 1)
  have bs_decr:"\<lceil> \<bar> abstract_bal_map b s - \<gamma>\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> 
                   \<le> \<lceil> \<bar> abstract_bal_map b s\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> - 1"
  proof(cases "abstract_bal_map b s \<ge> \<gamma>")
    case True
    hence "\<lceil> \<bar>abstract_bal_map b s - \<gamma>\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> =
                 \<lceil> (abstract_bal_map b s - \<gamma>) / \<gamma> - (1 - \<epsilon>)\<rceil>" by simp
    also have "... = \<lceil> (abstract_bal_map b s ) / \<gamma> - (1 - \<epsilon>) - 1\<rceil>"
      using gamma_0
      by (smt (verit) diff_divide_distrib divide_self_if)
    also have "... = \<lceil> abstract_bal_map b s / \<gamma> - (1 - \<epsilon>)\<rceil> - 1" 
      using ceiling_diff_one[of "abstract_bal_map b s / \<gamma> - (1 - \<epsilon>)"] by simp
    also have "... = \<lceil> \<bar>abstract_bal_map b s \<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> - 1"
      using sP gamma_0 \<epsilon>_axiom  True 
      by auto
    finally show ?thesis by simp 
  next
    case False
    have "\<lceil>\<bar>abstract_bal_map b s - \<gamma>\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> = \<lceil> (\<gamma> - abstract_bal_map b s) / \<gamma> - (1 - \<epsilon>)\<rceil>"
      using False by simp
    also have "... \<le> \<lceil> \<epsilon> - (1 - \<epsilon>)\<rceil>" 
      apply(rule ceiling_mono, simp, subst pos_divide_le_eq[OF gamma_0])
      using False sP(1) by argo
    also have "... = 0" using \<epsilon>_axiom by linarith
    also have "... \<le> 1 -  1" by simp
    also have "... \<le> \<lceil>abstract_bal_map b s / \<gamma> - (1 - \<epsilon>)\<rceil> -1"
      using sP(1) gamma_0 
      by (simp add: pos_less_divide_eq)
    also have "... = \<lceil>\<bar>abstract_bal_map  b s \<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> - 1" 
      using sP gamma_0 \<epsilon>_axiom  \<open>\<lceil>\<epsilon> - (1 - \<epsilon>)\<rceil> = 0\<close> mult_less_0_iff[of "1 - \<epsilon>" \<gamma>] zero_less_ceiling 
      by(auto intro!: cong[of ceiling])
    finally show ?thesis by simp
  qed
  have bt_decr:"\<lceil> \<bar>abstract_bal_map b t + \<gamma>\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> \<le> \<lceil> \<bar>abstract_bal_map b t\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil>"
  proof(cases "abstract_bal_map b t \<le> - \<gamma>")
    case True
    hence "\<lceil> \<bar>abstract_bal_map b t + \<gamma>\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> = \<lceil> -(abstract_bal_map b t + \<gamma>) / \<gamma> - (1 - \<epsilon>)\<rceil>" by simp
    also have "... = \<lceil> - (abstract_bal_map b t ) / \<gamma> - (1 - \<epsilon>) - 1\<rceil>"
      using gamma_0
      by (simp add: diff_divide_distrib)
    also have "... = \<lceil> ( - abstract_bal_map b t) / \<gamma> - (1 - \<epsilon>)\<rceil> - 1" 
      using ceiling_diff_one[of "(-abstract_bal_map b t) / \<gamma> - (1 - \<epsilon>)"] by simp
    also have "... = \<lceil> \<bar>abstract_bal_map b t \<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> - 1"
      using sP gamma_0 \<epsilon>_axiom  True 
      by auto
    finally show ?thesis by simp 
  next
    case False
    have "\<lceil>\<bar>abstract_bal_map b t + \<gamma>\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> = \<lceil> (\<gamma> + abstract_bal_map b t) / \<gamma> - (1 - \<epsilon>)\<rceil>"
      using False 
      by (auto intro: cong[of ceiling])
    also have "... \<le> \<lceil> (1 - \<epsilon>) - (1 - \<epsilon>)\<rceil>" 
      apply(rule ceiling_mono, simp, subst pos_divide_le_eq[OF gamma_0])
      using False tP(1) by argo
    also have "... = 0" by simp
    also have "... \<le> \<lceil> - abstract_bal_map b t / \<gamma> - (1 - \<epsilon>)\<rceil>"
      using tP(1) gamma_0 \<epsilon>_axiom mult_less_0_iff[of "- \<epsilon>" \<gamma>] 
            pos_less_divide_eq[of \<gamma> 0 "- abstract_bal_map b t"] zero_le_ceiling 
      by linarith
    also have "... = \<lceil>\<bar> abstract_bal_map b t \<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> "
      using tP gamma_0 \<epsilon>_axiom mult_neg_pos[of "-\<epsilon>" \<gamma>] 
      by (intro cong[of ceiling], simp)linarith
    finally show ?thesis by simp
  qed
  have "\<Phi> (send_flow_call1_upd state) = \<Phi> state'"
    by (simp add: \<open>state' = send_flow_call1_upd state\<close>)
  also have "... = (\<Sum> v \<in>  \<V>. \<lceil> \<bar> abstract_bal_map b' v\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil>)"
    using 1  unfolding \<Phi>_def by simp
  also have "... = (\<Sum> v \<in>  \<V> - {s, t}. \<lceil> \<bar> abstract_bal_map b' v\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil>) + 
                   \<lceil> \<bar> abstract_bal_map b' s\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> + \<lceil> \<bar> abstract_bal_map b' t\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil>"
    apply(rule trans[OF comm_monoid_add_class.sum.subset_diff[of "\<V> - {s, t}" \<V>]])
    using \<V>_finite  Diff_Diff_Int[of \<V>] sP(2) tP(3) s_neq_t by auto
  also have "... = (\<Sum> v \<in>  \<V> - {s, t}. \<lceil> \<bar> abstract_bal_map b v\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil>) + 
                   \<lceil> \<bar> abstract_bal_map b s - \<gamma>\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> + \<lceil> \<bar> abstract_bal_map b t + \<gamma>\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil>"
    using s_neq_t by (simp add:  b'_is)
  also have "...  \<le> (\<Sum> v \<in>  \<V> - {s, t}. \<lceil> \<bar> abstract_bal_map b v\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil>) + 
                   \<lceil> \<bar> abstract_bal_map b s \<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> + \<lceil> \<bar> abstract_bal_map b t \<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> -1 "
    using bt_decr bs_decr by simp
  also have "... =  (\<Sum> v \<in>  \<V>. \<lceil> \<bar> abstract_bal_map b v\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil>) - 1" 
    apply(simp, rule trans[OF _ sym[OF comm_monoid_add_class.sum.subset_diff[of "\<V> - {s, t}" \<V>]]])
    using \<V>_finite  Diff_Diff_Int[of \<V>] sP(2) tP(3) s_neq_t 
    by auto
  also have "... = \<Phi> state - 1"
    by(simp add: 1 \<Phi>_def)
  finally show ?case by simp
qed

lemma send_flow_call2_cond_Phi_decr:
  assumes "send_flow_call2_cond state" "invar_gamma state"
          "underlying_invars state" "implementation_invar state"
          "pos_flow_F state"  "invar_isOptflow state"
  shows   "\<Phi> (send_flow_call2_upd state) \<le> \<Phi> state - 1"
proof(rule send_flow_call2_condE[OF assms(1)], goal_cases)
  case (1 f b \<gamma> t s P f' b' state')
  hence "state' = send_flow_call2_upd state"
    by(auto simp add: send_flow_call2_upd_def  Let_def)
  have gamma_0: "\<gamma> > 0" using assms 
    by(auto simp add: 1 elim!: invar_gammaE)
  have sP: "\<epsilon> * \<gamma> < abstract_bal_map b s" "resreach (abstract_flow_map f) s t"  "s \<in> \<V>" 
    using if_send_flow_call2_cond_advanced[OF assms(1,4) _ _ _ assms(3,2,5,6)] 1 by auto
  have tP: "abstract_bal_map b t < - (1-\<epsilon>) * \<gamma>"  "t \<in> \<V>" 
    using  "1"(2,3,5,6) assms(1,4) if_send_flow_call2_cond_basic[OF assms(1,4)] 
    by auto
  have s_neq_t:"s \<noteq> t" using sP tP gamma_0
    by (smt (verit, best) mult_less_cancel_right_disj)
  have b'_is: "abstract_bal_map b'= 
        (\<lambda>v. if v = s then abstract_bal_map b s - \<gamma>
        else if v = t then abstract_bal_map b t + \<gamma> else abstract_bal_map b v)"
    using abstract_bal_map_homo_move_gamma[OF _ refl, of b \<gamma> s t] assms(4) 
    by (auto simp add: 1)
  have bt_decr:"\<lceil> \<bar>abstract_bal_map b t + \<gamma>\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> 
                  \<le> \<lceil> \<bar>abstract_bal_map b t\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> - 1"
  proof(cases "abstract_bal_map  b t \<le> - \<gamma>")
    case True
    hence "\<lceil> \<bar>abstract_bal_map b t + \<gamma>\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> = \<lceil> -(abstract_bal_map b t + \<gamma>) / \<gamma> - (1 - \<epsilon>)\<rceil>" by simp
    also have "... = \<lceil> (-abstract_bal_map b t ) / \<gamma> - (1 - \<epsilon>) - 1\<rceil>" using gamma_0
      by (simp add: diff_divide_distrib)
    also have "... = \<lceil> (- abstract_bal_map b t) / \<gamma> - (1 - \<epsilon>)\<rceil> - 1" 
      using ceiling_diff_one[of "(- abstract_bal_map b t) / \<gamma> - (1 - \<epsilon>)"] by simp
    also have "... = \<lceil> \<bar>abstract_bal_map b t \<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> - 1"
      using sP gamma_0 \<epsilon>_axiom  True by auto
    finally show ?thesis by simp 
  next
    case False
    have "\<lceil>\<bar>abstract_bal_map b t + \<gamma>\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> = \<lceil> (\<gamma> + abstract_bal_map b t) / \<gamma> - (1 - \<epsilon>)\<rceil>"
      using False 
      by (smt (verit, best))
    also have "... \<le> \<lceil> \<epsilon> - (1 - \<epsilon>)\<rceil>" 
      apply(rule ceiling_mono, simp, subst pos_divide_le_eq[OF gamma_0])
      using False tP(1) by argo
    also have "... = 0" using \<epsilon>_axiom by linarith
    also have "... \<le> 1 -  1" by simp
    also have "... \<le> \<lceil> (- abstract_bal_map b t) / \<gamma> - (1 - \<epsilon>)\<rceil> -1"
      using tP(1) gamma_0 
      by (smt (verit) mult_minus_left one_le_ceiling pos_less_divide_eq)
    also have "... = \<lceil>\<bar> abstract_bal_map b t \<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> - 1" 
      apply(simp, rule cong[of ceiling], simp)
      using tP gamma_0 \<epsilon>_axiom 
      by auto (smt (verit, ccfv_SIG) diff_divide_distrib mult_neg_pos)
    finally show ?thesis by simp
  qed
  have bs_decr:"\<lceil> \<bar> abstract_bal_map b s - \<gamma>\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> \<le> \<lceil> \<bar>abstract_bal_map b s\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil>"
  proof(cases "abstract_bal_map b s \<ge> \<gamma>")
    case True
    hence "\<lceil> \<bar>abstract_bal_map b s - \<gamma>\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> = \<lceil> (abstract_bal_map b s - \<gamma>) / \<gamma> - (1 - \<epsilon>)\<rceil>" by simp
    also have "... = \<lceil> (abstract_bal_map b s ) / \<gamma> - (1 - \<epsilon>) - 1\<rceil>" using gamma_0
      by (simp add: diff_divide_distrib)
    also have "... = \<lceil> (abstract_bal_map b s) / \<gamma> - (1 - \<epsilon>)\<rceil> - 1" 
      using ceiling_diff_one[of "(abstract_bal_map b s) / \<gamma> - (1 - \<epsilon>)"] by simp
    also have "... = \<lceil> \<bar>abstract_bal_map b s \<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> - 1"
      using sP gamma_0 \<epsilon>_axiom  True by auto
    finally show ?thesis by simp 
  next
    case False
    have "\<lceil>\<bar>abstract_bal_map b s - \<gamma>\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> 
                = \<lceil> ( \<gamma> - abstract_bal_map b s ) / \<gamma> - (1 - \<epsilon>)\<rceil>"
      using False 
      by (auto intro: cong[of ceiling])
    also have "... \<le> \<lceil> (1 - \<epsilon>) - (1 - \<epsilon>)\<rceil>" 
      apply(rule ceiling_mono, simp, subst pos_divide_le_eq[OF gamma_0])
      using False sP(1) by argo
    also have "... = 0" by simp
    also have "... \<le> \<lceil> abstract_bal_map b s / \<gamma> - (1 - \<epsilon>)\<rceil>"
      using sP(1) gamma_0 \<epsilon>_axiom  mult_less_0_iff[of \<epsilon> \<gamma>]
            pos_less_divide_eq[of \<gamma> \<epsilon> "abstract_bal_map b s"]
      by simp
    also have "... = \<lceil>\<bar> abstract_bal_map b s \<bar> / \<gamma> - (1 - \<epsilon>)\<rceil>"
      using sP gamma_0 \<epsilon>_axiom  mult_less_0_iff[of \<epsilon> \<gamma>] 
      by (auto intro: cong[of ceiling])
    finally show ?thesis by simp
  qed
  have "\<Phi> (send_flow_call2_upd state) = \<Phi> state'"
    by (simp add: \<open>state' = send_flow_call2_upd state\<close>)
  also have "... = (\<Sum> v \<in>  \<V>. \<lceil> \<bar> abstract_bal_map b' v\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil>)"
    using 1  unfolding \<Phi>_def by simp
  also have "... = (\<Sum> v \<in>  \<V> - {s, t}. \<lceil> \<bar> abstract_bal_map b' v\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil>) + 
                   \<lceil> \<bar> abstract_bal_map b' s\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> + \<lceil> \<bar> abstract_bal_map b' t\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil>"
    apply(rule trans[OF comm_monoid_add_class.sum.subset_diff[of "\<V> - {s, t}" \<V>]])
    using \<V>_finite  Diff_Diff_Int[of \<V>] tP(2) sP(3) s_neq_t by auto
  also have "... = (\<Sum> v \<in>  \<V> - {s, t}. \<lceil> \<bar> abstract_bal_map b v\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil>) + 
                   \<lceil> \<bar> abstract_bal_map b s - \<gamma>\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> + \<lceil> \<bar> abstract_bal_map b t + \<gamma>\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil>" 
    using s_neq_t by (simp add: b'_is)
  also have "...  \<le> (\<Sum> v \<in>  \<V> - {s, t}. \<lceil> \<bar> abstract_bal_map b v\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil>) + 
                   \<lceil> \<bar> abstract_bal_map b s \<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> + \<lceil> \<bar> abstract_bal_map b t \<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> -1 "
    using bt_decr bs_decr by simp
  also have "... =  (\<Sum> v \<in>  \<V>. \<lceil> \<bar>abstract_bal_map b v\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil>) - 1"
    apply(simp, rule trans[OF _ sym[OF comm_monoid_add_class.sum.subset_diff[of "\<V> - {s, t}" \<V>]]])
    using \<V>_finite  Diff_Diff_Int[of \<V>] sP(3) tP(2) s_neq_t by auto
  also have "... = \<Phi> state - 1"
    unfolding 1 \<Phi>_def by simp
  finally show ?case by simp
qed

lemma send_flow_succ_upd_Phi_pres:
  "\<Phi> (send_flow_succ_upd state) = \<Phi> state"
  by(simp add: \<Phi>_def send_flow_succ_upd_def Let_def)

lemma send_flow_cont_upd_Phi_pres:
  "\<Phi> (send_flow_cont_upd state) = \<Phi> state"
  by(simp add: \<Phi>_def send_flow_cont_upd_def Let_def)

lemma send_flow_fail_upd_Phi_pres:
  "\<Phi> (send_flow_fail_upd state) = \<Phi> state"
  by(simp add: \<Phi>_def send_flow_fail_upd_def Let_def)

lemma send_flow_cont_upd_flow_pres:
   "current_flow (send_flow_cont_upd state) = current_flow state"
  by(simp add: send_flow_cont_upd_def)

lemma send_flow_succ_upd_flow_pres: 
  "current_flow (send_flow_succ_upd state) = current_flow state"
  by(simp add: send_flow_succ_upd_def)

lemma send_flow_fail_upd_flow_pres: 
  "current_flow (send_flow_fail_upd state) = current_flow state"
  by(simp add: send_flow_fail_upd_def)

lemma send_flow_call1_cond_flow_Phi:
  assumes  "send_flow_call1_cond state" "invar_gamma state"
          "underlying_invars state" "implementation_invar state"
          "pos_flow_F state"  "invar_isOptflow state"
          "state' = send_flow_call1_upd state"
  shows   "a_current_flow  state' e \<ge> a_current_flow state e - (\<Phi> state - \<Phi> state')*current_\<gamma> state'"
  unfolding assms(2)
proof(rule send_flow_call1_condE[OF assms(1)], goal_cases)
  case (1 f b \<gamma> s t P f' b' state')
  hence "state' = send_flow_call1_upd state" 
    by(auto simp add: send_flow_call1_upd_def  Let_def)
  have gamma_0: "\<gamma> > 0" using assms by(auto elim!: invar_gammaE simp add: 1)
  have sP: "(1 - \<epsilon>) * \<gamma> < abstract_bal_map b s"  "s \<in> \<V>" 
    using  "1"(2,3,5) assms(1,4) if_send_flow_call1_cond_basic[OF assms(1,4)] 
    by auto
  have tP: "abstract_bal_map b t < - \<epsilon> * \<gamma>" "resreach (abstract_flow_map f) s t" "t \<in> \<V>" 
    "is_min_path (a_current_flow state) s t P" 
    "oedge ` set P \<subseteq> to_set (actives state) \<union> \<F> state"
    "distinct P"
    using if_send_flow_call1_cond_advanced[OF assms(1,4) _ _ assms(3,2,5,6)] 1 by auto
  have flow_dom_is: "flow_domain (current_flow state) = \<E>" "flow_invar (current_flow state)"
    using assms(4) 1 by auto
  have f'_is:"abstract_flow_map f' = augment_edges (abstract_flow_map f) \<gamma> P"
    unfolding 1
    using tP(5) from_underlying_invars'(1,3)[OF assms(3)]
    by(intro augment_edges_homo[OF _ flow_dom_is(2)])
      (auto simp add: image_set  flow_dom_is(1) simp del: set_map)
  have "abstract_flow_map f e- \<gamma> \<le> abstract_flow_map f' e" 
    using invar_gamma_def  distinct_path_augment[of P \<gamma> "abstract_flow_map f" e]
      tP(6) gamma_0 
    by (auto simp add:  f'_is)
  moreover have "\<Phi> state - \<Phi> (send_flow_call1_upd state) \<ge> 1"
    using send_flow_call1_cond_Phi_decr[of state, OF assms(1-6)] by simp
  ultimately have "abstract_flow_map f' e \<ge> abstract_flow_map f e - \<gamma> * (\<Phi> state - \<Phi> (send_flow_call1_upd state))"
    using gamma_0 
    by (smt (verit) mult_less_cancel_left2 of_int_less_1_iff)
  moreover have "current_\<gamma> (send_flow_call1_upd state) = \<gamma>"
    by (simp add: "1"(3) send_flow_call1_upd_changes(4))
  moreover have "current_flow (send_flow_call1_upd state) = f'"
    by(auto simp add: 1 send_flow_call1_upd_def Let_def)
  ultimately show ?case using 1
    by (simp add: assms(7) mult.commute)
qed

lemma send_flow_call2_cond_flow_Phi:
  assumes "send_flow_call2_cond state" "invar_gamma state"
          "underlying_invars state" "implementation_invar state"
          "pos_flow_F state"  "invar_isOptflow state"
          "state' = send_flow_call2_upd state"
  shows   "a_current_flow  state' e \<ge> a_current_flow state e - (\<Phi> state - \<Phi> state')*current_\<gamma> state'"
  unfolding assms(2)
proof(rule send_flow_call2_condE[OF assms(1)], goal_cases)
  case (1 f b \<gamma> t s P f' b' state')
  have gamma_0: "\<gamma> > 0" using assms 
    by(auto simp add: 1 elim!: invar_gammaE)
  have sP: "\<epsilon> * \<gamma> < abstract_bal_map b s" "resreach (abstract_flow_map f) s t"  "s \<in> \<V>" 
    "is_min_path (a_current_flow state) s t P" 
    "oedge ` set P \<subseteq> to_set (actives state) \<union> \<F> state"
    "distinct P"
    using if_send_flow_call2_cond_advanced[OF assms(1,4) _ _ _ assms(3,2,5,6)] 1 by auto
  have tP: "abstract_bal_map b t < - (1-\<epsilon>) * \<gamma>"  "t \<in> \<V>" 
    using  "1"(2,3,5,6) assms(1,4) if_send_flow_call2_cond_basic[OF assms(1,4)] 
    by auto
  have flow_dom_is: "flow_domain (current_flow state) = \<E>" "flow_invar (current_flow state)"
    using assms(4) 1 by auto
  have f'_is:"abstract_flow_map f' = augment_edges (abstract_flow_map f) \<gamma> P"
    unfolding 1
    using sP(5) from_underlying_invars'(1,3)[OF assms(3)]
    by(intro augment_edges_homo[OF _ flow_dom_is(2)])
      (auto simp add: image_set  flow_dom_is(1) simp del: set_map)
  have "abstract_flow_map f e- \<gamma> \<le> abstract_flow_map f' e" 
    using invar_gamma_def  distinct_path_augment[of P \<gamma> "abstract_flow_map f" e]
      sP(6) gamma_0 
    by (auto simp add:  f'_is)
  moreover have "\<Phi> state - \<Phi> (send_flow_call2_upd state) \<ge> 1"
    using send_flow_call2_cond_Phi_decr[of state, OF assms(1-6)] by simp
  ultimately have "abstract_flow_map f' e \<ge> abstract_flow_map f e - \<gamma> * (\<Phi> state - \<Phi> (send_flow_call2_upd state))"
    using gamma_0 
    by (smt (verit) mult_less_cancel_left2 of_int_less_1_iff)
  moreover have "current_\<gamma> (send_flow_call2_upd state) = \<gamma>"
    by (simp add: "1"(3) send_flow_call2_upd_changes(4))
  moreover have "current_flow (send_flow_call2_upd state) = f'"
    by(auto simp add: 1 send_flow_call2_upd_def Let_def)
  ultimately show ?case 
    using 1
    by (simp add: assms(7) mult.commute)
qed 

lemma send_flow_call1_invar_integral_pres:
  assumes "send_flow_call1_cond state"
          "invar_integral state" "invar_gamma state"
          "underlying_invars state" "implementation_invar state"
          "pos_flow_F state"  "invar_isOptflow state"
  shows   "invar_integral (send_flow_call1_upd state)"
proof(rule send_flow_call1_condE[OF assms(1)], goal_cases)
  case (1 f b \<gamma> s t P f' b' state')
  have gamma_0: "\<gamma> > 0" using assms by(auto elim!: invar_gammaE simp add: 1)
  have sP: "(1 - \<epsilon>) * \<gamma> < abstract_bal_map b s"  "s \<in> \<V>" 
    using  "1"(2,3,5) assms(1,4) if_send_flow_call1_cond_basic[OF assms(1,5)] 
    by auto
  have tP: "abstract_bal_map b t < - \<epsilon> * \<gamma>" "resreach (abstract_flow_map f) s t" "t \<in> \<V>" 
    "is_min_path (a_current_flow state) s t P" 
    "oedge ` set P \<subseteq> to_set (actives state) \<union> \<F> state"
    "distinct P" "Rcap (abstract_flow_map f) (set P) > 0"
    using if_send_flow_call1_cond_advanced[OF assms(1,5) _ _ assms(4,3,6,7)] 1 by auto
  have flow_dom_is: "flow_domain (current_flow state) = \<E>" "flow_invar (current_flow state)"
    using assms(5) 1 by auto
  have f'_is:"abstract_flow_map f' = augment_edges (abstract_flow_map f) \<gamma> P"
    unfolding 1
    using tP(5) from_underlying_invars'(1,3)[OF assms(4)]
    by(intro augment_edges_homo[OF _ flow_dom_is(2)])
      (auto simp add: image_set  flow_dom_is(1) simp del: set_map)
  show ?case  
  proof(rule invar_integralI)
    fix e
    assume "e \<in> to_set (actives (send_flow_call1_upd state))"
    moreover have "actives (send_flow_call1_upd state) = 
                   actives state" 
      by (simp add: send_flow_call1_upd_changes(3))
    ultimately have "e \<in> to_set (actives state)" by simp
    then obtain x where x_prop:"a_current_flow state e = real (x::nat) * \<gamma>"
      using assms(2) by(auto elim: invar_integralE simp add: 1)
    have f': "f' = current_flow (send_flow_call1_upd state)"
      by(auto simp add: 1 send_flow_call1_upd_def Let_def)
    show "\<exists>x. a_current_flow (send_flow_call1_upd state) e 
            = real x * current_\<gamma> (send_flow_call1_upd state)"
    proof(cases "e \<in> oedge ` set P")
      case True 
      then obtain ee where ee_prop:"ee \<in> set P" "e = oedge ee" by auto
      hence "ee = F e \<or> ee = B e" by(cases ee) (auto intro: oedge.elims[of ee])
      hence e_erev:"(F e \<in> set P \<and> \<not> (B e) \<in> set P) \<or>
                    (\<not> F e \<in> set P \<and>  (B e) \<in> set P) \<or> 
                    ( F e \<in> set P \<and>  (B e) \<in> set P)" 
        using ee_prop by auto
      have x_0:"B e \<in> set P \<Longrightarrow> x > 0"
      proof(rule ccontr)
        assume asm:"B e \<in> set P" "\<not> 0 < x"
        hence "x = 0" by simp
        hence rcap:"rcap (abstract_flow_map f) (B e) = 0"
          using x_prop 1 by simp        
        have "Rcap (abstract_flow_map f) (set P) \<le> 0"
          using asm(1) rcap 
          by (force intro!: Min.coboundedI simp add: Rcap_def)
        thus False 
          using tP(7) by simp
      qed
      note one = 1
      show ?thesis
      proof(cases rule: disjE[OF e_erev])
        case 1
        thus ?thesis 
          using e_rev_in_es_flow_change[of e P  "abstract_flow_map f" \<gamma>, OF _ _ tP(6)] x_prop f'_is
          by (auto intro!: exI[of _ "x+1"] 
              simp add: send_flow_call1_upd_changes(4) f'_is sym[OF f'] one distrib_left mult.commute)  
      next
        case 2
        thus ?thesis
        using rev_e_in_es_flow_change[of e P   "abstract_flow_map f" \<gamma>, OF _ _ tP(6), simplified]
          x_prop x_0  there_and_back_flow_not_change[of e P  "abstract_flow_map f" \<gamma>, OF _ _ tP(6), simplified] 
          f'_is 
        by (auto  intro: exI[of _ "x-1"] disjE[where P="F e \<notin> set P \<and> B e \<in> set P"]
            simp add: left_diff_distrib' one sym[OF f'] send_flow_call1_upd_changes(4))  
      qed
    next
      case False
      thus ?thesis
        using e_not_in_es_flow_not_change[of P e  "abstract_flow_map f" \<gamma>] x_prop f'_is
        by(auto simp add: sym[OF f'] 1 send_flow_call1_upd_changes(4))
    qed
  qed
qed

lemma send_flow_call2_invar_integral_pres:
  assumes "send_flow_call2_cond state"
          "invar_integral state" "invar_gamma state"
          "underlying_invars state" "implementation_invar state"
          "pos_flow_F state"  "invar_isOptflow state"
  shows   "invar_integral (send_flow_call2_upd state)"
proof(rule send_flow_call2_condE[OF assms(1)], goal_cases)
  case (1 f b \<gamma> t s P f' b' state')
  have gamma_0: "\<gamma> > 0" using assms 
    by(auto simp add: 1 elim!: invar_gammaE)
  have sP: "\<epsilon> * \<gamma> < abstract_bal_map b s" "resreach (abstract_flow_map f) s t"  "s \<in> \<V>" 
    "is_min_path (a_current_flow state) s t P" 
    "oedge ` set P \<subseteq> to_set (actives state) \<union> \<F> state"
    "distinct P" "Rcap (abstract_flow_map f) (set P) > 0"
    using if_send_flow_call2_cond_advanced[OF assms(1,5) _ _ _ assms(4,3,6,7)] 1 by auto
  have tP: "abstract_bal_map b t < - (1-\<epsilon>) * \<gamma>"  "t \<in> \<V>" 
    using  "1"(2,3,5,6) if_send_flow_call2_cond_basic[OF assms(1,5)] 
    by auto
  have flow_dom_is: "flow_domain (current_flow state) = \<E>" "flow_invar (current_flow state)"
    using assms(5) 1 by auto
  have f'_is:"abstract_flow_map f' = augment_edges (abstract_flow_map f) \<gamma> P"
    unfolding 1
    using sP(5) from_underlying_invars'(1,3)[OF assms(4)]
    by(intro augment_edges_homo[OF _ flow_dom_is(2)])
      (auto simp add: image_set  flow_dom_is(1) simp del: set_map)
  show ?case unfolding invar_integral_def
  proof
    fix e
    assume "e \<in> to_set (actives (send_flow_call2_upd state))"
    moreover have "actives (send_flow_call2_upd state) = 
                   actives state" 
      by (simp add: send_flow_call2_upd_changes(3))
    ultimately have "e \<in> to_set (actives state)" by simp
    then obtain x where x_prop:"a_current_flow state e = real (x::nat) * \<gamma>"
      using assms(2) by(auto elim: invar_integralE simp add: 1)
    have f': "f' = current_flow (send_flow_call2_upd state)"
      by(auto simp add: 1 send_flow_call2_upd_def Let_def)
    show "\<exists>x. a_current_flow (send_flow_call2_upd state) e = real x * current_\<gamma> (send_flow_call2_upd state)"
    proof(cases "e \<in> oedge ` set P")
      case True 
      then obtain ee where ee_prop:"ee \<in> set P" "e = oedge ee" by auto
      hence "ee = F e \<or> ee = B e" by (cases ee )(auto intro: oedge.elims[of ee])
      hence e_erev:"(F e \<in> set P \<and> \<not> (B e) \<in> set P) \<or>
                    (\<not> F e \<in> set P \<and>  (B e) \<in> set P) \<or> 
                    ( F e \<in> set P \<and>  (B e) \<in> set P)" 
        using ee_prop by auto
      have x_0:"B e \<in> set P \<Longrightarrow> x > 0"
      proof(rule ccontr)
        assume asm:"B e \<in> set P" "\<not> 0 < x"
        hence "x = 0" by simp
        hence rcap:"rcap (abstract_flow_map f) (B e) = 0"
          using x_prop 1 by auto         
        have "Rcap (abstract_flow_map f) (set P) \<le> 0"
          using asm(1) rcap 
          by (force intro!: Min.coboundedI simp add:  Rcap_def)
        thus False
          using sP(7) by simp
      qed
      note one = 1
      show ?thesis
      proof(cases rule: disjE[OF e_erev])
        case 1
        thus ?thesis
          using e_rev_in_es_flow_change[of e P "abstract_flow_map f" \<gamma>, OF _ _ sP(6)] x_prop f'_is
          by (auto intro!: exI[of _ "x+1"] 
                 simp add: distrib_left mult.commute one sym[OF f'] send_flow_call2_upd_changes(4))
      next
        case 2
        thus ?thesis
        using rev_e_in_es_flow_change[of e P  "abstract_flow_map f" \<gamma>, OF _ _ sP(6), simplified]
              x_prop x_0 there_and_back_flow_not_change[of e P "abstract_flow_map f" \<gamma>, OF _ _ sP(6), simplified] f'_is
        by(auto intro:  disjE[where P="F e \<notin> set P \<and> B e \<in> set P"] exI[of _ "x-1"] 
             simp add: left_diff_distrib' 1 sym[OF f'] send_flow_call2_upd_changes(4))
     qed
    next
      case False
      thus ?thesis
        using e_not_in_es_flow_not_change[of P e  "abstract_flow_map f" \<gamma>] x_prop f'_is
        by(auto simp add: 1 sym[OF f']  send_flow_call2_upd_changes(4))
    qed
  qed
qed

lemma send_flow_cont_invar_integral_pres:
  "invar_integral state \<Longrightarrow> invar_integral (send_flow_cont_upd state)"
  by(simp add: send_flow_cont_upd_def invar_integral_def)

lemma send_flow_fail_invar_integral_pres:
  "invar_integral state \<Longrightarrow> invar_integral (send_flow_fail_upd state)"
  by(simp add: send_flow_fail_upd_def invar_integral_def)

lemma send_flow_succ_invar_integral_pres:
  "invar_integral state \<Longrightarrow> invar_integral (send_flow_succ_upd state)"
  by(auto simp add: send_flow_succ_upd_def invar_integral_def)

lemma outside_actives_and_F_no_change_succ:
  assumes "e \<notin> to_set (actives state)" "e \<notin> \<F> state"
  shows   "a_current_flow state e = a_current_flow (send_flow_succ_upd state) e"
  by(simp add: send_flow_succ_upd_def Let_def)

lemma outside_actives_and_F_no_change_cont:
  assumes "e \<notin> to_set (actives state)" "e \<notin> \<F> state"
  shows   "a_current_flow state e = a_current_flow (send_flow_cont_upd state) e"
  by(simp add: send_flow_cont_upd_def Let_def)

lemma outside_actives_and_F_no_change_fail:
  assumes "e \<notin> to_set (actives state)" "e \<notin> \<F> state"
  shows   "a_current_flow state e = a_current_flow (send_flow_fail_upd state) e"
  by(simp add: send_flow_fail_upd_def Let_def)

lemma outside_actives_and_F_no_change_call1:
  assumes "send_flow_call1_cond state" "e \<notin> to_set (actives state)" "e \<notin> \<F> state"
          "invar_gamma state" "underlying_invars state" "implementation_invar state"
          "pos_flow_F state"  "invar_isOptflow state"
  shows   "a_current_flow state e = a_current_flow (send_flow_call1_upd state) e"
proof(rule send_flow_call1_condE[OF assms(1)], goal_cases)
  case (1 f b \<gamma> s t P f' b' state')
  have gamma_0: "\<gamma> > 0" using assms by(auto elim!: invar_gammaE simp add: 1)
  have sP: "(1 - \<epsilon>) * \<gamma> < abstract_bal_map b s"  "s \<in> \<V>" 
    using  "1"(2,3,5)  if_send_flow_call1_cond_basic[OF assms(1,6)] 
    by auto
  have tP: "abstract_bal_map b t < - \<epsilon> * \<gamma>" "resreach (abstract_flow_map f) s t" "t \<in> \<V>" 
    "is_min_path (a_current_flow state) s t P" 
    "oedge ` set P \<subseteq> to_set (actives state) \<union> \<F> state"
    "distinct P" "Rcap (abstract_flow_map f) (set P) > 0"
    using if_send_flow_call1_cond_advanced[OF assms(1,6) _ _ assms(5,4,7,8)] 1 by auto
  have flow_dom_is: "flow_domain (current_flow state) = \<E>" "flow_invar (current_flow state)"
    using assms(6) 1 by auto
  have f'_is:"abstract_flow_map f' = augment_edges (abstract_flow_map f) \<gamma> P"
    unfolding 1
    using tP(5) from_underlying_invars'(1,3)[OF assms(5)]
    by(intro augment_edges_homo[OF _ flow_dom_is(2)])
      (auto simp add: image_set  flow_dom_is(1) simp del: set_map)
  have f': "f' = current_flow (send_flow_call1_upd state)"
    by(auto simp add: 1 send_flow_call1_upd_def Let_def)
  have "e \<notin> oedge ` set P"
    using tP(5) assms(2,3) by auto
  thus ?case 
    using f' f'_is e_not_in_es_flow_not_change[of P e "abstract_flow_map f" \<gamma>]
    by(force simp add: 1)
qed

lemma outside_actives_and_F_no_change_call2:
  assumes "send_flow_call2_cond state" "e \<notin> to_set (actives state)" "e \<notin> \<F> state"
          "invar_gamma state" "underlying_invars state" "implementation_invar state"
          "pos_flow_F state"  "invar_isOptflow state"
  shows   "a_current_flow state e = a_current_flow (send_flow_call2_upd state) e"
proof(rule send_flow_call2_condE[OF assms(1)], goal_cases)
  case (1 f b \<gamma> t s P f' b' state')
  have gamma_0: "\<gamma> > 0" using assms 
    by(auto simp add: 1 elim!: invar_gammaE)
  have sP: "\<epsilon> * \<gamma> < abstract_bal_map b s" "resreach (abstract_flow_map f) s t"  "s \<in> \<V>" 
    "is_min_path (a_current_flow state) s t P" 
    "oedge ` set P \<subseteq> to_set (actives state) \<union> \<F> state"
    "distinct P" "Rcap (abstract_flow_map f) (set P) > 0"
    using if_send_flow_call2_cond_advanced[OF assms(1,6) _ _ _ assms(5,4,7,8)] 1 by auto
  have tP: "abstract_bal_map b t < - (1-\<epsilon>) * \<gamma>"  "t \<in> \<V>" 
    using  "1"(2,3,5,6) if_send_flow_call2_cond_basic[OF assms(1,6)] 
    by auto
  have flow_dom_is: "flow_domain (current_flow state) = \<E>" "flow_invar (current_flow state)"
    using assms(6) 1 by auto
  have f'_is:"abstract_flow_map f' = augment_edges (abstract_flow_map f) \<gamma> P"
    unfolding 1
    using sP(5) from_underlying_invars'(1,3)[OF assms(5)]
    by(intro augment_edges_homo[OF _ flow_dom_is(2)])
      (auto simp add: image_set  flow_dom_is(1) simp del: set_map)
  have f': "f' = current_flow (send_flow_call2_upd state)"
    by(auto simp add: 1 send_flow_call2_upd_def Let_def)
  have "e \<notin> oedge ` set P"
    using sP(5) assms(2,3) by auto
  thus ?case 
    using f' f'_is e_not_in_es_flow_not_change[of P e "abstract_flow_map f" \<gamma>]
    by(force simp add: 1)
qed 

lemma send_flow_invar_isOptflow_call1:
  assumes "send_flow_call1_cond state"
          "invar_gamma state" "underlying_invars state" "implementation_invar state"
          "pos_flow_F state"  "invar_isOptflow state" "invar_integral state"
          "\<And> e. e \<in> \<F> state \<Longrightarrow> a_current_flow state e \<ge> current_\<gamma> state"
  shows   "invar_isOptflow (send_flow_call1_upd state)"
          "implementation_invar (send_flow_call1_upd state)"
proof(all \<open>rule send_flow_call1_condE[OF assms(1)]\<close>, goal_cases)
  case (1 f b \<gamma> s t P f' b' state')
  note basics = this
  have gamma_0: "\<gamma> > 0" using assms by(auto elim!: invar_gammaE simp add: 1)
  have sP: "(1 - \<epsilon>) * \<gamma> < abstract_bal_map b s"  "s \<in> \<V>" 
    using  "1"(2,3,5)  if_send_flow_call1_cond_basic[OF assms(1,4)] 
    by auto
  have tP: "abstract_bal_map b t < - \<epsilon> * \<gamma>" "resreach (abstract_flow_map f) s t" "t \<in> \<V>" 
    "is_min_path (a_current_flow state) s t P" 
    "oedge ` set P \<subseteq> to_set (actives state) \<union> \<F> state"
    "distinct P" "Rcap (abstract_flow_map f) (set P) > 0"
    using if_send_flow_call1_cond_advanced[OF assms(1,4) _ _ assms(3,2,5,6) ] 1 by auto
  have s_neq_t:"s \<noteq> t" using sP tP gamma_0
    by (smt (verit, best) mult_less_cancel_right_disj)
  have flow_dom_is: "flow_domain (current_flow state) = \<E>" "flow_invar (current_flow state)"
    using assms(4) 1 by auto
  have f'_is:"abstract_flow_map f' = augment_edges (abstract_flow_map f) \<gamma> P"
    unfolding 1
    using tP(5) from_underlying_invars'(1,3)[OF assms(3)]
    by(intro augment_edges_homo[OF _ flow_dom_is(2)])
      (auto simp add: image_set  flow_dom_is(1) simp del: set_map)
  have b'_is: "abstract_bal_map b'= 
        (\<lambda>v. if v = s then abstract_bal_map b s - \<gamma>
        else if v = t then abstract_bal_map b t + \<gamma> else abstract_bal_map b v)"
    using abstract_bal_map_homo_move_gamma[OF _ refl, of b \<gamma> s t] assms(4) 
    by (auto simp add: 1)
  have hdP: "fstv (hd P) = s" and lastP: "sndv (last P) = t" 
    using tP(4) by(auto elim!: is_min_pathE is_s_t_pathE)
  have bal_after_is: "balance (send_flow_call1_upd state) = b'"
    and flow_after_is: "current_flow (send_flow_call1_upd state) = f'"
    by(auto simp add: basics send_flow_call1_upd_def Let_def)
  have egtr0:"e \<in> set P \<Longrightarrow> rcap (abstract_flow_map f) e > 0" for e
    by (simp add: rcap_extr_non_zero tP(7))
  have e_gamma:"e \<in> set P \<Longrightarrow> rcap (abstract_flow_map f) e \<ge> \<gamma>" for e
  proof-
    assume asm:"e \<in> set P"
    hence oedge:"oedge e \<in> to_set (actives state) \<union> \<F> state"
      using tP(5) by auto
    show "ereal \<gamma> \<le> \<uu>\<^bsub>abstract_flow_map f\<^esub>e"
    proof(rule UnE[OF oedge], goal_cases)
      case 1
      have rcap0:"rcap (abstract_flow_map f) e > 0" 
        using asm egtr0 by auto
      moreover obtain rc where  "(abstract_flow_map f) (oedge e) = (rc::nat) * \<gamma>"
        using assms(7) 1 by(auto elim!: invar_integralE simp add: basics)
      ultimately show ?case 
        using infinite_u[of "oedge e"] gamma_0 
        by(cases rule: erev.cases[of e])(auto intro: nat.exhaust[of rc])
    next
      case 2
      have rcap0:"rcap (abstract_flow_map f) e > 0" 
        using asm egtr0 by auto
      moreover have "(abstract_flow_map f) (oedge e) \<ge> \<gamma>"
        using  2 by(auto simp add: basics intro: assms(8)) 
      then show ?case 
        using  infinite_u[of "oedge e"] gamma_0
        by(auto intro: erev.cases[of e] simp add: basics) 
    qed
  qed
  have gamma_Rcap:"ereal \<gamma> \<le> Rcap (abstract_flow_map f) (set P)"
    using  e_gamma 
    by (auto intro: Min.boundedI simp add: Rcap_def)
  show "invar_isOptflow (send_flow_call1_upd state)"
    using path_aug_opt_pres[OF s_neq_t _ gamma_Rcap _ _ f'_is refl, of "\<b> - a_balance state"]
      gamma_0 tP(4) b'_is assms(6) hdP lastP
    by(auto elim!: invar_isOptflowE 
        intro!: invar_isOptflowI 
        intro: is_Opt_cong[OF refl, rotated]
        simp add: basics bal_after_is flow_after_is b'_is f'_is)
  have P_in_E:"set (map oedge P) \<subseteq> \<E>" 
    using  from_underlying_invars'(1,3)[OF assms(3)] tP(5) by auto
  have flow_dom_is_after: "flow_domain (current_flow  (send_flow_call1_upd state)) = \<E>"
    "flow_invar (current_flow  (send_flow_call1_upd state))"
    using augment_edges_impl_invar[of P f] augment_edges_impl_domain[of P f] flow_dom_is P_in_E 
    by(auto simp add: send_flow_call1_upd_def Let_def basics split: prod.split)
  have same_dom: "bal_domain (move b \<gamma> s t ) = bal_domain b "
    apply(rule abstract_bal_map_domain_move)
    using sP(2) tP(3) assms(4) by (auto simp add: basics)
  also have "... = \<V>"
    using assms(4) basics(2) sP(2) tP(3) by auto
  finally have bal_dom_is_after: "bal_domain (balance  (send_flow_call1_upd state)) = \<V>"
    "bal_invar (balance  (send_flow_call1_upd state))"
    using assms(4) by(auto simp add: send_flow_call1_upd_def Let_def basics split: prod.split)
  show "implementation_invar (send_flow_call1_upd state)"
    apply(rule implementation_invarE[OF assms(4)])
    apply(rule implementation_invarI)
    using bal_dom_is_after flow_dom_is_after
    by(auto simp add: send_flow_call1_upd_changes)
qed

lemma send_flow_invar_isOptflow_call2:
  assumes "send_flow_call2_cond state"
          "invar_gamma state" "underlying_invars state" "implementation_invar state"
          "pos_flow_F state"  "invar_isOptflow state" "invar_integral state"
          "\<And> e. e \<in> \<F> state \<Longrightarrow> a_current_flow state e \<ge> current_\<gamma> state"
  shows   "invar_isOptflow (send_flow_call2_upd state)"
          "implementation_invar (send_flow_call2_upd state)"
proof(all \<open>rule send_flow_call2_condE[OF assms(1)]\<close>, goal_cases)
  case (1 f b \<gamma> t s P f' b' state')
  note basics = this
  have gamma_0: "\<gamma> > 0" using assms 
    by(auto simp add: 1 elim!: invar_gammaE)
  have sP: "\<epsilon> * \<gamma> < abstract_bal_map b s" "resreach (abstract_flow_map f) s t"  "s \<in> \<V>" 
    "is_min_path (a_current_flow state) s t P" 
    "oedge ` set P \<subseteq> to_set (actives state) \<union> \<F> state"
    "distinct P" "Rcap (abstract_flow_map f) (set P) > 0"
    using if_send_flow_call2_cond_advanced[OF assms(1,4) _ _ _ assms(3,2,5,6)] 1 by auto
  have tP: "abstract_bal_map b t < - (1-\<epsilon>) * \<gamma>"  "t \<in> \<V>" 
    using  "1"(2,3,5,6) if_send_flow_call2_cond_basic[OF assms(1,4)] 
    by auto
  have s_neq_t:"s \<noteq> t" using sP tP gamma_0
    by (smt (verit, best) mult_less_cancel_right_disj)
  have flow_dom_is: "flow_domain (current_flow state) = \<E>" "flow_invar (current_flow state)"
    using assms(4) 1 by auto
  have f'_is:"abstract_flow_map f' = augment_edges (abstract_flow_map f) \<gamma> P"
    unfolding 1
    using sP(5) from_underlying_invars'(1,3)[OF assms(3)]
    by(intro augment_edges_homo[OF _ flow_dom_is(2)])
      (auto simp add: image_set  flow_dom_is(1) simp del: set_map)
  have b'_is: "abstract_bal_map b'= 
        (\<lambda>v. if v = s then abstract_bal_map b s - \<gamma>
        else if v = t then abstract_bal_map b t + \<gamma> else abstract_bal_map b v)"
    using abstract_bal_map_homo_move_gamma[OF _ refl, of b \<gamma> s t] assms(4) 
    by (auto simp add: 1)
  have hdP: "fstv (hd P) = s" and lastP: "sndv (last P) = t" 
    using sP(4) by(auto elim!: is_min_pathE is_s_t_pathE)
  have bal_after_is: "balance (send_flow_call2_upd state) = b'"
    and flow_after_is: "current_flow (send_flow_call2_upd state) = f'"
    by(auto simp add: basics send_flow_call2_upd_def Let_def)
  have egtr0:"e \<in> set P \<Longrightarrow> rcap (abstract_flow_map f) e > 0" for e
    by (simp add: rcap_extr_non_zero sP(7))
  have e_gamma:"e \<in> set P \<Longrightarrow> rcap (abstract_flow_map f) e \<ge> \<gamma>" for e
  proof-
    assume asm:"e \<in> set P"
    hence oedge:"oedge e \<in> to_set (actives state) \<union> \<F> state"
      using sP(5) by auto
    show "ereal \<gamma> \<le> \<uu>\<^bsub>abstract_flow_map f\<^esub>e"
    proof(rule UnE[OF oedge], goal_cases)
      case 1
      have rcap0:"rcap (abstract_flow_map f) e > 0" 
        using asm egtr0 by auto
      moreover obtain rc where  "(abstract_flow_map f) (oedge e) = (rc::nat) * \<gamma>"
        using assms(7) 1 by(auto elim!: invar_integralE simp add: basics)
      ultimately show ?case 
        using infinite_u[of "oedge e"] gamma_0 
        by(cases rule: erev.cases[of e])(auto intro: nat.exhaust[of rc])
    next
      case 2
      have rcap0:"rcap (abstract_flow_map f) e > 0" 
        using asm egtr0 by auto
      moreover have "(abstract_flow_map f) (oedge e) \<ge> \<gamma>"
        using  2 by(auto simp add: basics intro: assms(8)) 
      then show ?case 
        using  infinite_u[of "oedge e"] gamma_0
        by(auto intro: erev.cases[of e] simp add: basics) 
    qed
  qed
  have gamma_Rcap:"ereal \<gamma> \<le> Rcap (abstract_flow_map f) (set P)"
    using  e_gamma 
    by (auto intro: Min.boundedI simp add: Rcap_def)
  show "invar_isOptflow (send_flow_call2_upd state)"
    using path_aug_opt_pres[OF s_neq_t _ gamma_Rcap _ _ f'_is refl, of "\<b> - a_balance state"]
      gamma_0 sP(4) b'_is assms(6) hdP lastP
    by(auto elim!: invar_isOptflowE 
        intro!: invar_isOptflowI 
        intro: is_Opt_cong[OF refl, rotated]
        simp add: basics bal_after_is flow_after_is b'_is f'_is)
  have P_in_E:"set (map oedge P) \<subseteq> \<E>" 
    using  from_underlying_invars'(1,3)[OF assms(3)] sP(5) by auto
  have flow_dom_is_after: "flow_domain (current_flow  (send_flow_call2_upd state)) = \<E>"
    "flow_invar (current_flow  (send_flow_call2_upd state))"
    using augment_edges_impl_invar[of P f] augment_edges_impl_domain[of P f] flow_dom_is P_in_E 
    by(auto simp add: send_flow_call2_upd_def Let_def basics split: prod.split)
  have same_dom: "bal_domain (move b \<gamma> s t ) = bal_domain b "
    apply(rule abstract_bal_map_domain_move)
    using tP(2) sP(3) assms(4) by (auto simp add: basics)
  also have "... = \<V>"
    using assms(4) basics(2) sP(2) sP(3) by auto
  finally have bal_dom_is_after: "bal_domain (balance  (send_flow_call2_upd state)) = \<V>"
    "bal_invar (balance  (send_flow_call2_upd state))"
    using assms(4) by(auto simp add: send_flow_call2_upd_def Let_def basics split: prod.split)
  show "implementation_invar (send_flow_call2_upd state)"
    apply(rule implementation_invarE[OF assms(4)])
    apply(rule implementation_invarI)
    using bal_dom_is_after flow_dom_is_after
    by(auto simp add: send_flow_call2_upd_changes)
qed

lemma send_flow_invar_isOptflow_cont:
  assumes "invar_isOptflow state"  
  shows   "invar_isOptflow (send_flow_cont_upd state)"
  using assms unfolding send_flow_cont_upd_def invar_isOptflow_def by simp

lemma send_flow_invar_isOptflow_succ:
  assumes "invar_isOptflow state"  
  shows   "invar_isOptflow (send_flow_succ_upd state)"
  using assms unfolding send_flow_succ_upd_def invar_isOptflow_def by simp

lemma send_flow_invar_isOptflow_fail:
  assumes "invar_isOptflow state"  
  shows   "invar_isOptflow (send_flow_fail_upd state)"
  using assms unfolding send_flow_fail_upd_def invar_isOptflow_def by simp


lemma
  assumes "invar_gamma state" "invar_above_6Ngamma state"
  shows   invar_above_6Ngamma_pos_flow_F: "pos_flow_F state"
    and   invar_above_6Ngamma_forest_flow_above_gamma:
            "\<And> e. e \<in> \<F> state \<Longrightarrow> current_\<gamma> state \<le> a_current_flow state e"
proof-
  have gamma_0: "current_\<gamma> state > 0" 
    using assms(1) by(auto elim!: invar_gammaE)
  show gamma_flow:"e \<in> \<F> state \<Longrightarrow> current_\<gamma> state \<le> a_current_flow state e" for e
  proof(rule order.trans[of _ "4*N*current_\<gamma> state"], goal_cases)
    case 1
    thus ?case
      using  gamma_0  N_gtr_0 by simp
  next
    case 2
    thus ?case
      using  gamma_0 Phi_nonneg[of state, OF assms(1)] N_gtr_0 
      by(intro order.trans[OF _ order.strict_implies_order[OF 
               invar_above_6NgammaD[OF assms(2),of e]]])
        (auto simp add: mult.commute right_diff_distrib')
  qed
  show flowF:  " pos_flow_F  state"
    using gamma_0 gamma_flow by (fastforce intro!: pos_flow_FI)
qed

theorem 
  assumes "send_flow_call1_cond state"
          "underlying_invars state" "invar_gamma state"
          "implementation_invar state"
          "invar_isOptflow state"
          "invar_above_6Ngamma state"
  shows invar_above_6Ngamma_call1_pres:
          "invar_above_6Ngamma (send_flow_call1_upd state)"
    and send_flow_call1_upd_Phi:
           "a_current_flow (send_flow_call1_upd state) e \<ge>
              a_current_flow state e - (\<Phi> state -
                            \<Phi> (send_flow_call1_upd state))*
                       current_\<gamma> (send_flow_call1_upd state)"
proof-
  have gamma_0: "current_\<gamma> state > 0" 
    using assms(3) by(auto elim!: invar_gammaE)
  have gamma_Phi_flow: "e \<in> \<F> (send_flow_call1_upd state) \<Longrightarrow>
         real (6 * N) * current_\<gamma> (send_flow_call1_upd state) -
         real_of_int (int (2 * N) - \<Phi> (send_flow_call1_upd state)) * 
               current_\<gamma> (send_flow_call1_upd state)
         < a_current_flow (send_flow_call1_upd state) e" for e
    using  invar_above_6NgammaD[OF assms(6), of e]  send_flow_call1_upd_changes(6)[of state] 
      send_flow_call1_upd_changes(4)[of state] assms(3,6)
      send_flow_call1_cond_Phi_decr[OF assms(1,3,2,4) _ assms(5)] 
    by (auto intro: order.strict_trans2[OF _ send_flow_call1_cond_flow_Phi[OF assms(1,3,2,4)
                              _ assms(5) refl]]  invar_above_6Ngamma_pos_flow_F
          simp add: left_diff_distrib') 
  thus "invar_above_6Ngamma (send_flow_call1_upd state)"
    by(auto intro: invar_above_6NgammaI)
  show "a_current_flow state e -
    real_of_int (\<Phi> state - \<Phi> (send_flow_call1_upd state)) * current_\<gamma> (send_flow_call1_upd state)
    \<le> a_current_flow (send_flow_call1_upd state) e"
    using  send_flow_call1_cond_flow_Phi[OF assms(1,3,2,4) _ assms(5) refl] 
      invar_above_6Ngamma_pos_flow_F assms(3,6)
    by auto
qed

theorem 
  assumes "send_flow_call2_cond state"
          "underlying_invars state" "invar_gamma state"
          "implementation_invar state"
          "invar_isOptflow state"
          "invar_above_6Ngamma state"
  shows invar_above_6Ngamma_call2_pres:
          "invar_above_6Ngamma (send_flow_call2_upd  state)"
    and send_flow_call2_upd_Phi:
          "a_current_flow (send_flow_call2_upd state) e \<ge>
              a_current_flow state e - (\<Phi> state -
                            \<Phi> (send_flow_call2_upd state))*
                       current_\<gamma> (send_flow_call2_upd state)"
proof-
  have gamma_0: "current_\<gamma> state > 0" 
    using assms(3) by(auto elim!: invar_gammaE)
  have gamma_Phi_flow: "e \<in> \<F> (send_flow_call2_upd state) \<Longrightarrow>
         real (6 * N) * current_\<gamma> (send_flow_call2_upd state) -
         real_of_int (int (2 * N) - \<Phi> (send_flow_call2_upd state)) * 
               current_\<gamma> (send_flow_call2_upd state)
         < a_current_flow (send_flow_call2_upd state) e" for e
    using  invar_above_6NgammaD[OF assms(6), of e]  send_flow_call2_upd_changes(6)[of state] 
      send_flow_call2_upd_changes(4)[of state] 
      send_flow_call2_cond_Phi_decr[OF assms(1,3,2,4) _ assms(5)] assms(3,6)
    by(auto intro: order.strict_trans2[OF _send_flow_call2_cond_flow_Phi[OF assms(1,3,2,4)
            _ assms(5) refl]] invar_above_6Ngamma_pos_flow_F
         simp add: left_diff_distrib') 
  thus "invar_above_6Ngamma (send_flow_call2_upd state)"
    by(auto intro: invar_above_6NgammaI)
  show "a_current_flow state e -
    real_of_int (\<Phi> state - \<Phi> (send_flow_call2_upd state)) * current_\<gamma> (send_flow_call2_upd state)
    \<le> a_current_flow (send_flow_call2_upd state) e"
    using  send_flow_call2_cond_flow_Phi[OF assms(1,3,2,4) _ assms(5) refl] 
      invar_above_6Ngamma_pos_flow_F assms(3,6)
    by auto
qed

theorem invar_above_6Ngamma_fail1_pres:
  assumes "send_flow_fail1_cond state"
          "invar_above_6Ngamma state"
  shows   "invar_above_6Ngamma (send_flow_fail_upd  state)"
  using assms 
  by(auto elim!: send_flow_fail1_condE invar_above_6NgammaE
      intro!: invar_above_6NgammaI
      simp add: send_flow_fail_upd_Phi_pres send_flow_fail_upd_changes(1,2,4)
      send_flow_fail_upd_flow_pres F_def F_redges_def)

theorem invar_above_6Ngamma_fail2_pres:
  assumes "send_flow_fail2_cond state"
          "invar_above_6Ngamma state"
  shows   "invar_above_6Ngamma (send_flow_fail_upd  state)"
  using assms 
  by(auto elim!: send_flow_fail2_condE invar_above_6NgammaE
      intro!: invar_above_6NgammaI
      simp add: send_flow_fail_upd_Phi_pres send_flow_fail_upd_changes
      send_flow_fail_upd_flow_pres)

theorem invar_above_6Ngamma_succ_pres:
  assumes "send_flow_succ_cond state"
          "invar_above_6Ngamma state"
  shows   "invar_above_6Ngamma (send_flow_succ_upd  state)"
  using assms 
  by(auto elim!: send_flow_succ_condE invar_above_6NgammaE
      intro!: invar_above_6NgammaI
      simp add: send_flow_succ_upd_Phi_pres send_flow_succ_upd_changes(1,2,4)
      send_flow_succ_upd_flow_pres F_def F_redges_def)

theorem invar_above_6Ngamma_cont_pres:
  assumes "send_flow_cont_cond state"
          "invar_above_6Ngamma state"
  shows   "invar_above_6Ngamma (send_flow_cont_upd  state)"
  using assms 
  by(auto elim!: send_flow_cont_condE invar_above_6NgammaE
      intro!: invar_above_6NgammaI
      simp add: send_flow_cont_upd_Phi_pres send_flow_cont_upd_changes(1,2,4)
      send_flow_cont_upd_flow_pres F_def F_redges_def)

subsection \<open>Inductions\<close>

theorem send_flow_invars_pres:
  assumes "send_flow_dom state"
          "underlying_invars state" "invar_gamma state"
          "implementation_invar state"
          "invar_integral state"
          "invar_isOptflow state"
          "invar_above_6Ngamma state"
  shows   "underlying_invars (send_flow state)" 
          "invar_gamma (send_flow state)"
          "implementation_invar (send_flow state)"
          "invar_integral (send_flow state)"
          "invar_isOptflow (send_flow state)"
          "invar_above_6Ngamma (send_flow state)"
          "\<And> e. a_current_flow  (send_flow state) e \<ge>
               a_current_flow state e - (\<Phi> state - \<Phi> (send_flow state))*current_\<gamma> state"
          "\<And> e. e \<notin> to_set (actives state) \<Longrightarrow>e \<notin> \<F> state \<Longrightarrow>
               a_current_flow state e = a_current_flow (send_flow state) e"
proof-
  have  "underlying_invars (send_flow state) \<and> 
         invar_gamma (send_flow state) \<and> 
         implementation_invar (send_flow state) \<and>
         invar_integral (send_flow state) \<and>
         invar_isOptflow (send_flow state) \<and>
         invar_above_6Ngamma (send_flow state) \<and>
         (\<forall> e. a_current_flow  (send_flow state) e \<ge>
               a_current_flow state e -
                   (\<Phi> state - \<Phi> (send_flow state))* current_\<gamma> state) \<and>
         (\<forall> e. e \<notin> to_set (actives state) \<and> e \<notin> \<F> state \<longrightarrow>
               a_current_flow state e = a_current_flow (send_flow state) e)" 
    using assms(2-)
  proof(induction rule: send_flow_induct[OF assms(1)])
    case (1 state)
    note IH = this    
    show ?case 
    proof(cases rule: send_flow_cases[of state])
      case 3
      have pos_flow_F: "pos_flow_F state"
        by(auto intro!: invar_above_6Ngamma_pos_flow_F 
            simp add:  IH(4-) 3)
      have IH_applied:
        "underlying_invars (send_flow (send_flow_call1_upd state))"
        "invar_gamma (send_flow (send_flow_call1_upd state))"
        "implementation_invar (send_flow (send_flow_call1_upd state))"
        "invar_integral (send_flow (send_flow_call1_upd state))"
        "invar_isOptflow (send_flow (send_flow_call1_upd state))"
        "invar_above_6Ngamma (send_flow (send_flow_call1_upd state))"
        "\<And> e. a_current_flow (send_flow_call1_upd state) e -
              real_of_int (\<Phi> (send_flow_call1_upd state) 
            - \<Phi> (send_flow (send_flow_call1_upd state))) *
               current_\<gamma> (send_flow_call1_upd state)
            \<le> a_current_flow (send_flow (send_flow_call1_upd state)) e"
        "\<And> e. e \<notin> to_set (actives (send_flow_call1_upd state)) \<Longrightarrow>
                   e \<notin> \<F> (send_flow_call1_upd state) \<Longrightarrow>
                 a_current_flow (send_flow_call1_upd state) e =
                 a_current_flow (send_flow (send_flow_call1_upd state)) e"
        using 3  IH(2)  invar_aux_pres_call1 send_flow_invar_isOptflow_call1
          invar_above_6Ngamma_call1_pres send_flow_call1_invar_integral_pres
          invar_gamma_pres_call1 invar_above_6Ngamma_forest_flow_above_gamma
        by(auto simp add:  IH(4-) pos_flow_F)
      moreover have "a_current_flow state e -
         (real_of_int (\<Phi> state) - real_of_int (\<Phi> (send_flow (send_flow_call1_upd state)))) *
         current_\<gamma> state
         \<le> a_current_flow (send_flow (send_flow_call1_upd state)) e" for e
        using IH_applied(7)[of e]
          send_flow_call1_cond_flow_Phi[OF 3 IH(5,4,6) pos_flow_F IH(8) refl, of e]
        by (auto  simp add: left_diff_distrib'  send_flow_call1_upd_changes(4) )
      moreover have "a_current_flow state e =
             a_current_flow (send_flow (send_flow_call1_upd state)) e"
        if "e \<notin> to_set (actives state)" "e \<notin> \<F> state" for e
        using IH_applied(8)[of e] that
          outside_actives_and_F_no_change_call1[OF 3 that IH(5,4,6) pos_flow_F IH(8)]           
        by (auto  simp add: left_diff_distrib'  send_flow_call1_upd_changes)
      ultimately show ?thesis
        by(auto simp add: send_flow_simps(5)[OF IH(1) 3])
    next
      case 4
      have pos_flow_F: "pos_flow_F state"
        by(auto intro!: invar_above_6Ngamma_pos_flow_F
            simp add:  IH(4-) 4)
      have IH_applied:
        "underlying_invars (send_flow (send_flow_call2_upd state))"
        "invar_gamma (send_flow (send_flow_call2_upd state))"
        "implementation_invar (send_flow (send_flow_call2_upd state))"
        "invar_integral (send_flow (send_flow_call2_upd state))"
        "invar_isOptflow (send_flow (send_flow_call2_upd state))"
        "invar_above_6Ngamma (send_flow (send_flow_call2_upd state))"
        "\<And> e. a_current_flow (send_flow_call2_upd state) e -
              real_of_int (\<Phi> (send_flow_call2_upd state) 
            - \<Phi> (send_flow (send_flow_call2_upd state))) *
               current_\<gamma> (send_flow_call2_upd state)
            \<le> a_current_flow (send_flow (send_flow_call2_upd state)) e"
        "\<And> e. e \<notin> to_set (actives (send_flow_call2_upd state)) \<Longrightarrow>
                   e \<notin> \<F> (send_flow_call2_upd state) \<Longrightarrow>
                 a_current_flow (send_flow_call2_upd state) e =
                 a_current_flow (send_flow (send_flow_call2_upd state)) e"
        using 4 IH(3)  invar_aux_pres_call2 send_flow_invar_isOptflow_call2
          invar_above_6Ngamma_call2_pres send_flow_call2_invar_integral_pres
          invar_gamma_pres_call2 invar_above_6Ngamma_forest_flow_above_gamma
        by(auto simp add:  IH(4-) pos_flow_F)
      moreover have "a_current_flow state e -
         (real_of_int (\<Phi> state) - real_of_int (\<Phi> (send_flow (send_flow_call2_upd state)))) *
         current_\<gamma> state
         \<le> a_current_flow (send_flow (send_flow_call2_upd state)) e" for e
        using IH_applied(7)[of e]
          send_flow_call2_cond_flow_Phi[OF 4 IH(5,4,6) pos_flow_F IH(8) refl, of e]
        by (auto  simp add: left_diff_distrib' send_flow_call2_upd_changes)
      moreover have "a_current_flow state e =
             a_current_flow (send_flow (send_flow_call2_upd state)) e"
        if "e \<notin> to_set (actives state)" "e \<notin> \<F> state" for e
        using IH_applied(8)[of e] that
          outside_actives_and_F_no_change_call2[OF 4 that IH(5,4,6) pos_flow_F IH(8)]           
        by (auto  simp add: left_diff_distrib'  send_flow_call2_upd_changes)
      ultimately show ?thesis
        by(auto simp add: send_flow_simps(6)[OF IH(1) 4])
    next
      case 1
      thus ?thesis
        using IH(4-) 
        by(auto simp add: send_flow_simps(2)[OF IH(1) 1] 
            send_flow_cont_upd_Phi_pres send_flow_cont_upd_flow_pres
            intro: underlying_invars_pres_cont  invar_gamma_pres_cont
            implementation_invar_pres_cont send_flow_cont_invar_integral_pres
            send_flow_invar_isOptflow_cont invar_above_6Ngamma_cont_pres)
    next
      case 2
      thus ?thesis
        using IH(4-) 
        by(auto simp add: send_flow_simps(1)[OF IH(1) 2] 
            send_flow_succ_upd_Phi_pres send_flow_succ_upd_flow_pres
            intro: underlying_invars_pres_succ  invar_gamma_pres_succ
            implementation_invar_pres_succ send_flow_succ_invar_integral_pres
            send_flow_invar_isOptflow_succ invar_above_6Ngamma_succ_pres) 
    next
      case 5
      thus ?thesis
        using IH(4-) 
        by(auto simp add: send_flow_simps(3)[OF IH(1) 5] 
            send_flow_fail_upd_Phi_pres send_flow_fail_upd_flow_pres
            intro: underlying_invars_pres_fail  invar_gamma_pres_fail
            implementation_invar_pres_fail send_flow_fail_invar_integral_pres
            send_flow_invar_isOptflow_fail invar_above_6Ngamma_fail1_pres)
    next
      case 6
      thus ?thesis
        using IH(4-) 
        by(auto simp add: send_flow_simps(4)[OF IH(1) 6] 
            send_flow_fail_upd_Phi_pres send_flow_fail_upd_flow_pres
            intro: underlying_invars_pres_fail  invar_gamma_pres_fail
            implementation_invar_pres_fail send_flow_fail_invar_integral_pres
            send_flow_invar_isOptflow_fail invar_above_6Ngamma_fail2_pres)
    qed
  qed
  thus  "underlying_invars (send_flow state)" 
    "invar_gamma (send_flow state)"
    "implementation_invar (send_flow state)"
    "invar_integral (send_flow state)"
    "invar_isOptflow (send_flow state)"
    "invar_above_6Ngamma (send_flow state)"
    "\<And> e. a_current_flow  (send_flow state) e \<ge>
               a_current_flow state e - (\<Phi> state - \<Phi> (send_flow state))*current_\<gamma> state"
    "\<And> e. e \<notin> to_set (actives state) \<Longrightarrow>e \<notin> \<F> state \<Longrightarrow>
               a_current_flow state e = a_current_flow (send_flow state) e"
    by auto
qed

theorem send_flow_invar_aux_pres: 
  assumes "send_flow_dom state"
          "underlying_invars state" "invar_gamma state"
          "implementation_invar state"
          "invar_integral state"
          "invar_isOptflow state"
          "invar_above_6Ngamma state"
  shows   "underlying_invars (send_flow state)"
  using assms by(auto intro: send_flow_invars_pres(1))

lemma send_flow_term:
  assumes "underlying_invars state" "invar_gamma state"
          "implementation_invar state"
          "invar_integral state"
          "invar_isOptflow state"
          "invar_above_6Ngamma state"
          "\<phi> = nat (\<Phi> state)"
  shows   "send_flow_dom state"
  using assms 
proof(induction \<phi> arbitrary: state rule: less_induct)
  case (less \<phi>)
  note IH = this
  then show ?case
  proof(cases rule: send_flow_cases[of state])
    case 3
    have pos_flow_F: "pos_flow_F state" 
      using "3" IH(2-) 
      by(auto intro!: invar_above_6Ngamma_pos_flow_F) 
    show ?thesis 
      using IH(2-) send_flow_call1_cond_Phi_decr[OF 3 IH(3,2,4) pos_flow_F IH(6)]
        Phi_nonneg[OF invar_gamma_pres_call1[OF IH(3)]]
      by(auto intro!: IH(1) invar_aux_pres_call1 send_flow_invar_isOptflow_call1
          invar_above_6Ngamma_call1_pres send_flow_call1_invar_integral_pres
          invar_gamma_pres_call1 invar_above_6Ngamma_forest_flow_above_gamma 3 pos_flow_F
          send_flow_dom_call1[OF 3])
  next
    case 4
    have pos_flow_F: "pos_flow_F state" 
      using  4 IH(2-) 
      by(auto intro!: invar_above_6Ngamma_pos_flow_F) 
    show ?thesis 
      using IH(2-) send_flow_call2_cond_Phi_decr[OF 4 IH(3,2,4) pos_flow_F IH(6)]
        Phi_nonneg[OF invar_gamma_pres_call2[OF IH(3)]]
      by(auto intro!: IH(1) invar_aux_pres_call2 send_flow_invar_isOptflow_call2
          invar_above_6Ngamma_call2_pres send_flow_call2_invar_integral_pres
          invar_gamma_pres_call2 invar_above_6Ngamma_forest_flow_above_gamma 4 pos_flow_F
          send_flow_dom_call2[OF 4])
  qed (simp add: send_flow_dom_succ 
      send_flow_dom_cont 
      send_flow_dom_fail1
      send_flow_dom_fail2)+
qed

lemmas send_flow_termination = send_flow_term[OF _ _ _ _ _ _ refl]

lemma all_bal_zero_send_flow_dom:
  "\<lbrakk>implementation_invar state; \<forall>v\<in>\<V>. a_balance state v = 0\<rbrakk> \<Longrightarrow> send_flow_dom state"
  "\<lbrakk>implementation_invar state; \<forall>v\<in>\<V>. a_balance state v = 0\<rbrakk> \<Longrightarrow> send_flow_succ_cond state"
  using test_all_vertices_zero_balance 
  by(auto intro!: send_flow_dom_succ send_flow_succ_condI)

lemma 
  assumes "underlying_invars state" "invar_gamma state"
          "implementation_invar state"
          "invar_integral state"
          "invar_isOptflow state"
          "invar_above_6Ngamma state"
          "return (send_flow state) = notyetterm"
  shows orlins_entry_after_send_flow: "orlins_entry (send_flow state)"
    and remaining_balance_after_send_flow:  "invar_non_zero_b (send_flow state)"
proof-
  have dom:"send_flow_dom state"
    using assms(1,2,3,4,5,6) send_flow_termination by blast
  have"orlins_entry (send_flow state) \<and> invar_non_zero_b (send_flow state)"
    using assms 
  proof(induction rule: send_flow_induct[OF dom])
    case (1 state)
    note IH = this
    then show ?case
    proof(cases state rule: send_flow_cases)
      case 1
      show ?thesis
        using if_send_flow_cont_cond_basic(1,2,3)[OF 1 IH(6)]
        by (cases rule: send_flow_cont_condE[OF 1])
           (force intro!: orlins_entryI ordered_ab_group_add_abs_class.abs_leI invar_non_zero_bI
                simp add: send_flow_changes_current_\<gamma>[OF IH(1)]  send_flow_simps_without_dom(2)[OF 1]
                          send_flow_cont_upd_changes(4,9) algebra_simps)+
    next
      case 2
      thus ?thesis
        using IH(10)
        by(auto simp add:  send_flow_simps_without_dom(1)[OF 2] send_flow_succ_upd_def)
    next
      case 3
      have pos_flow_F: "pos_flow_F state" 
        using "3" IH(2-) 
        by(auto intro!: invar_above_6Ngamma_pos_flow_F) 
      show ?thesis 
        using IH(4-) IH(2)
        by(auto intro!:  invar_aux_pres_call1 send_flow_invar_isOptflow_call1
            invar_above_6Ngamma_call1_pres send_flow_call1_invar_integral_pres
            invar_gamma_pres_call1 invar_above_6Ngamma_forest_flow_above_gamma 3 pos_flow_F
            simp add: send_flow_simps(5)[OF IH(1) 3])
    next
      case 4
      have pos_flow_F: "pos_flow_F state" 
        using 4 IH(2-) 
        by(auto intro!: invar_above_6Ngamma_pos_flow_F) 
      show ?thesis 
        using IH(4-) IH(3)
        by(auto intro!: invar_aux_pres_call2 send_flow_invar_isOptflow_call2
            invar_above_6Ngamma_call2_pres send_flow_call2_invar_integral_pres
            invar_gamma_pres_call2 invar_above_6Ngamma_forest_flow_above_gamma 4 pos_flow_F
            simp add: send_flow_simps(6)[OF IH(1) 4])
    next
      case 5
      thus ?thesis
        using IH(10)
        by(auto simp add:  send_flow_simps_without_dom(3)[OF 5] send_flow_fail_upd_def)
    next
      case 6
      thus ?thesis
        using IH(10)
        by(auto simp add:  send_flow_simps_without_dom(4)[OF 6] send_flow_fail_upd_def)
    qed
  qed
  thus "orlins_entry (send_flow state)"  "invar_non_zero_b (send_flow state)"
    by auto
qed

theorem send_flow_flow_Phi:
  assumes "underlying_invars state" "invar_gamma state"
          "implementation_invar state"
          "invar_integral state"
          "invar_isOptflow state"
          "invar_above_6Ngamma state"
          "state' = send_flow state"
  shows   "a_current_flow  state' e \<ge> a_current_flow state e - (\<Phi> state - \<Phi> state')*current_\<gamma> state'"
  using send_flow_invars_pres(7)[of state] send_flow_changes_current_\<gamma> assms
    send_flow_termination
  by auto

lemma send_flow_flow_Phi_final:
  assumes "underlying_invars state" "invar_gamma state"
          "implementation_invar state"
          "invar_integral state"
          "invar_isOptflow state"
          "invar_above_6Ngamma state"
          "state' = send_flow state"
  shows   "a_current_flow  state' e \<ge> a_current_flow state e - \<Phi> state*current_\<gamma> state'"
  using send_flow_flow_Phi[of state state' e] Phi_nonneg[of state] assms
    invar_gammaE send_flow_invar_gamma_pres Phi_nonneg  
    send_flow_flow_Phi[of state state' e] 
    send_flow_termination
  by(smt mult_less_cancel_right_disj of_int_le_iff)

theorem send_flow_invar_integral_pres:
  assumes "underlying_invars state" "invar_gamma state"
          "implementation_invar state"
          "invar_integral state"
          "invar_isOptflow state"
          "invar_above_6Ngamma state"
  shows   "invar_integral (send_flow state)"
  using assms send_flow_termination send_flow_invars_pres(4) by blast

theorem send_flow_implementation_invar_pres:
  assumes "underlying_invars state" "invar_gamma state"
          "implementation_invar state"
          "invar_integral state"
          "invar_isOptflow state"
          "invar_above_6Ngamma state"
  shows   "implementation_invar (send_flow state)"
  using assms send_flow_termination send_flow_invars_pres(3) by blast

theorem outside_actives_and_F_no_change:
  assumes "underlying_invars state" "invar_gamma state"
          "implementation_invar state"
          "invar_integral state"
          "invar_isOptflow state"
          "invar_above_6Ngamma state"
          "e \<notin> to_set (actives state)" "e \<notin> \<F> state"
  shows   "a_current_flow state e = a_current_flow (send_flow state) e"
  using assms send_flow_termination send_flow_invars_pres(8) by blast

theorem send_flow_invar_isOpt_pres:
  assumes "underlying_invars state" "invar_gamma state"
          "implementation_invar state"
          "invar_integral state"
          "invar_isOptflow state"
          "invar_above_6Ngamma state"
  shows   "invar_isOptflow (send_flow state)"
  using assms send_flow_termination send_flow_invars_pres(5) by blast

lemma  send_flow_succ_balance: 
  assumes "underlying_invars state" "invar_gamma state"
          "implementation_invar state"
          "invar_integral state"
          "invar_isOptflow state"
          "invar_above_6Ngamma state"
          "return (send_flow state) = success"
  shows   "\<forall> v \<in> \<V>. a_balance (send_flow state) v = 0"
proof-
  have dom:"send_flow_dom state"
    using assms(1,2,3,4,5,6) send_flow_termination by blast
  show ?thesis
    using assms 
  proof(induction rule: send_flow_induct[OF dom])
    case (1 state)
    note IH = this
    then show ?case
    proof(cases state rule: send_flow_cases)
      case 1
      show ?thesis
        using IH(10)
        by(auto simp add:  send_flow_simps_without_dom(2)[OF 1] send_flow_cont_upd_def)
    next
      case 2
      thus ?thesis
        using IH(10) if_send_flow_succ_cond[OF 2 IH(6)]
        by(auto simp add:  send_flow_simps_without_dom(1)[OF 2] send_flow_succ_upd_changes)
    next
      case 3
      have pos_flow_F: "pos_flow_F state" 
        using "3" IH(2-) 
        by(auto intro!: invar_above_6Ngamma_pos_flow_F) 
      show ?thesis 
        using IH(4-) IH(2)
        by(auto intro!:  invar_aux_pres_call1 send_flow_invar_isOptflow_call1
            invar_above_6Ngamma_call1_pres send_flow_call1_invar_integral_pres
            invar_gamma_pres_call1 invar_above_6Ngamma_forest_flow_above_gamma 3 pos_flow_F
            simp add: send_flow_simps(5)[OF IH(1) 3])
    next
      case 4
      have pos_flow_F: "pos_flow_F state" 
        using 4 IH(2-) 
        by(auto intro!: invar_above_6Ngamma_pos_flow_F) 
      show ?thesis 
        using IH(4-) IH(3)
        by(auto intro!: invar_aux_pres_call2 send_flow_invar_isOptflow_call2
            invar_above_6Ngamma_call2_pres send_flow_call2_invar_integral_pres
            invar_gamma_pres_call2 invar_above_6Ngamma_forest_flow_above_gamma 4 pos_flow_F
            simp add: send_flow_simps(6)[OF IH(1) 4])
    next
      case 5
      thus ?thesis
        using IH(10)
        by(auto simp add:  send_flow_simps_without_dom(3)[OF 5] send_flow_fail_upd_def)
    next
      case 6
      thus ?thesis
        using IH(10)
        by(auto simp add:  send_flow_simps_without_dom(4)[OF 6] send_flow_fail_upd_def)
    qed
  qed
qed

lemma send_flow_entry_invar_above_6Ngamma:
  assumes "invar_gamma state"  "send_flow_entryF state"  "\<Phi> state \<le> 2*N"
  shows   "invar_above_6Ngamma state"
proof(rule invar_above_6NgammaI, rule send_flow_entryFE[OF assms(2)],
      rule invar_gammaE[OF assms(1)], 
      rule order.strict_trans1[of _ "current_\<gamma> state * (real N * 6)"], goal_cases)
  case 1
  thus ?case
    using  assms(3) 
    by(auto simp add: algebra_simps intro!: preorder_class.order.strict_implies_order)
next
  case 2
  thus ?case
    using  assms(3) 
    by(auto simp add: algebra_simps intro!: preorder_class.order.strict_implies_order)
qed

subsection \<open>Final Results\<close>

theorem send_flow_correctness:
  assumes "underlying_invars state"
          "implementation_invar state"
          "invar_gamma state"
          "invar_integral state"
          "send_flow_entryF state"
          "invar_isOptflow state"
          "\<Phi> state \<le> 2*N"
          "return (send_flow state) = success"
  shows   "is_Opt \<b> (a_current_flow (send_flow state))"
proof-
  have invar_above_6Ngamma: "invar_above_6Ngamma state" 
    using send_flow_entry_invar_above_6Ngamma assms(3,5,7) by auto
  have "\<forall> v \<in> \<V>. a_balance (send_flow state) v = 0"
    using send_flow_succ_balance[of state] invar_above_6Ngamma assms by simp
  moreover have "is_Opt (\<b> - a_balance (send_flow state)) (a_current_flow (send_flow state))"
    using assms invar_above_6Ngamma 
    by(auto intro: invar_isOptflowD send_flow_invar_isOpt_pres)
  ultimately show ?thesis
    by(simp add: is_Opt_def isbflow_def)
qed

lemma send_flow_fail_balance: 
  assumes "underlying_invars state" "invar_gamma state"
          "implementation_invar state"
          "invar_integral state"
          "invar_isOptflow state"
          "invar_above_6Ngamma state"
          "state' = (send_flow state)" 
          "return state' = infeasible"
  shows   "(\<exists> s \<in> \<V>. (a_balance state' s > (1 - \<epsilon>) * current_\<gamma> state' \<and>
                     (\<forall> t \<in> \<V>. resreach (a_current_flow state') s t \<longrightarrow>
                               a_balance state' t \<ge> - \<epsilon> * current_\<gamma> state'))) \<or>

              (\<exists> t \<in> \<V>. (a_balance state' t < - (1 - \<epsilon>) * current_\<gamma> state' \<and>
                     (\<forall> s \<in> \<V>. resreach (a_current_flow state') s t \<longrightarrow>
                               a_balance state' s \<le>  \<epsilon> * current_\<gamma> state')))"
proof-
  have dom:"send_flow_dom state"
    using assms(1,2,3,4,5,6) send_flow_termination by blast
  show ?thesis
    using assms 
  proof(induction rule: send_flow_induct[OF dom])
    case (1 state)
    note IH = this
    then show ?case
    proof(cases state rule: send_flow_cases)
      case 1
      show ?thesis
        using IH(10,11)
        by(auto simp add:  send_flow_simps_without_dom(2)[OF 1] send_flow_cont_upd_def)
    next
      case 2
      thus ?thesis
        using IH(10,11)
        by(auto simp add:  send_flow_simps_without_dom(1)[OF 2] send_flow_succ_upd_def)
    next
      case 3
      have pos_flow_F: "pos_flow_F state" 
        using "3" IH(2-) 
        by(auto intro!: invar_above_6Ngamma_pos_flow_F) 
      show ?thesis 
        using IH(4-) IH(2)
        by(auto intro!:  invar_aux_pres_call1 send_flow_invar_isOptflow_call1
            invar_above_6Ngamma_call1_pres send_flow_call1_invar_integral_pres
            invar_gamma_pres_call1 invar_above_6Ngamma_forest_flow_above_gamma 3 pos_flow_F
            simp add: send_flow_simps(5)[OF IH(1) 3])
    next
      case 4
      have pos_flow_F: "pos_flow_F state" 
        using 4 IH(2-) 
        by(auto intro!: invar_above_6Ngamma_pos_flow_F) 
      show ?thesis 
        using IH(4-) IH(3)
        by(auto intro!: invar_aux_pres_call2 send_flow_invar_isOptflow_call2
            invar_above_6Ngamma_call2_pres send_flow_call2_invar_integral_pres
            invar_gamma_pres_call2 invar_above_6Ngamma_forest_flow_above_gamma 4 pos_flow_F
            simp add: send_flow_simps(6)[OF IH(1) 4])
    next
      case 5
      have pos_flow_F: "pos_flow_F state" 
        using IH(2-) 
        by(auto intro!: invar_above_6Ngamma_pos_flow_F) 
      show ?thesis
      proof(rule disjI1, rule send_flow_fail1_condE[OF 5], goal_cases)
        case 1
        thus ?case
        using if_send_flow_fail1_cond_advanced[OF 5 IH(6) _ _ IH(4,5) pos_flow_F IH(8), 
            of "the (get_source state)"]
          if_send_flow_fail1_cond_basic(2,3)[OF 5 IH(6), of "the (get_source state)"] 
        by (force intro:  bexI[of _ "the (get_source state)"] 
               simp add: IH(10) send_flow_simps_without_dom(3)[OF 5]  send_flow_fail_upd_changes)+
      qed
    next
      case 6
      have pos_flow_F: "pos_flow_F state" 
        using IH(2-) 
        by(auto intro!: invar_above_6Ngamma_pos_flow_F) 
      show ?thesis
      proof(rule disjI2, rule send_flow_fail2_condE[OF 6], goal_cases)
        case 1
        thus ?case
        using if_send_flow_fail2_cond_advanced[OF 6 IH(6) _ _ _IH(4,5) pos_flow_F IH(8), 
             of "the (get_target state)"]
             if_send_flow_fail2_cond_basic(3,4)[OF 6 IH(6), of "the (get_target state)"] 
        by (force intro:  bexI[of _ "the (get_target state)"] 
               simp add: IH(10) send_flow_simps_without_dom(4)[OF 6]  send_flow_fail_upd_changes )+
      qed
    qed
  qed
qed

theorem send_flow_completeness:
  assumes "underlying_invars state"
          "implementation_invar state"
          "invar_gamma state"
          "invar_integral state"
          "send_flow_entryF state"
          "invar_isOptflow state"
          "\<Phi> state \<le> 2*N"
          "return (send_flow state) = infeasible"
  shows   "\<nexists> f. (f is  \<b> flow)"
proof-
  define state' where "state' = send_flow state"
  have invar_above_6Ngamma: "invar_above_6Ngamma state" 
    using send_flow_entry_invar_above_6Ngamma assms(3,5,7) by auto
  have s_and_t:"(\<exists> s \<in> \<V>. (a_balance state' s > (1 - \<epsilon>) * current_\<gamma> state' \<and>
                     (\<forall> t \<in> \<V>. resreach (a_current_flow state') s t \<longrightarrow>
                               a_balance state' t \<ge> - \<epsilon> * current_\<gamma> state'))) \<or>

        (\<exists> t \<in> \<V>. (a_balance state' t < - (1 - \<epsilon>) * current_\<gamma> state' \<and>
                     (\<forall> s \<in> \<V>. resreach (a_current_flow state') s t \<longrightarrow>
                               a_balance state' s \<le>  \<epsilon> * current_\<gamma> state')))"
    using send_flow_fail_balance[OF assms(1,3,2,4,6) invar_above_6Ngamma state'_def] assms(8) 
    by(simp add: state'_def)
  moreover have is_Opt:"is_Opt (\<b> - a_balance (send_flow state)) (a_current_flow (send_flow state))"
    using assms(1,2,3,4,6) invar_above_6Ngamma 
    by(auto elim!: invar_isOptflowE[OF send_flow_invar_isOpt_pres])
  have gamma_0: "current_\<gamma> state' > 0" and gamma_same: "current_\<gamma> state' = current_\<gamma> state"
    using assms invar_above_6Ngamma  send_flow_invars_pres(2) send_flow_term 
      send_flow_changes_current_\<gamma> 
    by (auto simp add: state'_def elim!: invar_gammaE) 
  have eps_card_V:"0 \<le> - real (card \<V>) * \<epsilon> + 1"
    using  \<epsilon>_axiom cardV_0
    by (simp add: mult.commute pos_le_divide_eq N_def)
  have eps_card_V':"real (card \<V> ) * \<epsilon> - 1 \<le> 0"
    using eps_card_V by linarith
  have eps_card_rewrite:"- real (card \<V>) * \<epsilon> + 1 \<le> - real (card \<V> - 1) * \<epsilon> + 1 - \<epsilon>"
    by(auto simp add: algebra_simps) 
      (metis Suc_pred cardV_0 distrib_left dual_order.refl mult.right_neutral of_nat_Suc)
  show ?thesis
  proof(rule disjE[OF s_and_t], goal_cases)
    case 1
    then obtain s where s_prop:"s \<in> \<V> " "(1 - \<epsilon>) * current_\<gamma> state' < a_balance state' s"
      "\<forall>t\<in>\<V>. resreach (a_current_flow state') s t \<longrightarrow> - \<epsilon> * current_\<gamma> state' \<le> a_balance state' t"
      by auto
    have "(\<Sum> x \<in> Rescut (a_current_flow state') s. a_balance state' x) =
         (\<Sum> x \<in> Rescut (a_current_flow state') s - {s}. a_balance state' x) + a_balance state' s"
      using finite_Rescut s_prop(1)
      by (intro trans[OF sum.subset_diff[where B="{s}"]])(auto simp add: Rescut_def)
    also have "... > (N - 1) * ( - \<epsilon> * current_\<gamma> state') + (1 - \<epsilon>) * current_\<gamma> state' "
    proof(rule add_le_less_mono, rule order.trans[rotated], 
          rule sum_bounded_below[of _ "-\<epsilon> *  current_\<gamma> state'"], goal_cases)
      case 1
      thus ?case
        using s_prop(3) Rescut_around_in_V[OF s_prop(1)]
        by(auto simp add: Rescut_def)
    next
      case 2
      thus ?case
        using Rescut_around_in_V[of s "a_current_flow state'"] gamma_0 \<epsilon>_axiom \<V>_finite
        unfolding N_def 
        by  (simp, subst card_Diff_singleton,
            auto intro: mult_right_mono_neg simp add: Rescut_def card_mono diff_le_mono s_prop(1))
    next
      case 3
      thus ?case
        using s_prop by(auto simp add: N_def)
    qed
    finally have 11: "real (N - 1) * (- \<epsilon> * current_\<gamma> state') + (1 - \<epsilon>) * current_\<gamma> state'
           < sum (a_balance state') (Rescut (a_current_flow state') s ) " by simp
    have residual_balance:"(\<Sum> x \<in> Rescut (a_current_flow state') s. a_balance state' x) > 0"
    proof(rule xt1(7), rule 11,
          rule order.trans[of _ " (- real (card \<V> - 1) *  \<epsilon>  + 1 - \<epsilon>) * current_\<gamma> state'"], goal_cases)
      case 1
      thus ?case
        apply(subst sym[OF mult_zero_left[of "current_\<gamma> state'"]])
        using eps_card_V eps_card_rewrite   gamma_0 gamma_same 
        by(intro mult_right_mono[where c="current_\<gamma> state'"]) auto
      case 2
      thus ?case
        by(auto simp add: algebra_simps  N_def )
    qed
    have Rescut_fV: "Rescut (a_current_flow state') s \<subseteq> \<V>" 
      by (simp add: Rescut_around_in_V s_prop(1))
    show ?case 
    proof(rule ccontr, goal_cases)
      case (1)
      then obtain f where "f is \<b> flow" by auto
      note 1 = this
      have " (\<Sum> v \<in> Rescut (a_current_flow state') s. ereal (\<b> v)) \<le>
                     Cap (Rescut (a_current_flow state') s)"
        using flow_less_cut[OF 1 Rescut_fV] by simp
      also have "... =  (\<Sum> v \<in> Rescut (a_current_flow state') s. ereal (\<b> v - a_balance state' v))"
        using flow_saturates_res_cut[of "a_current_flow state'" " \<b> - a_balance state'" s] is_Opt
          Rescut_fV by(auto elim: is_OptE simp add: state'_def)
      also have "... = (\<Sum> v \<in> Rescut (a_current_flow state') s. \<b> v ) -
                         (\<Sum> v \<in> Rescut (a_current_flow state') s. a_balance state' v)"
        by (simp add: sum_subtractf)
      also have "...  < (\<Sum> v \<in> Rescut (a_current_flow state') s. \<b> v ) "
        using residual_balance by simp
      finally show False by simp
    qed
  next
    case 2
    then obtain t where t_prop: "a_balance state' t < - (1 - \<epsilon>) * current_\<gamma> state'" "t \<in> \<V>"
      "(\<forall>s\<in>\<V>. resreach (a_current_flow state') s t \<longrightarrow> a_balance state' s \<le> \<epsilon> * current_\<gamma> state')"
      by auto
    have "(\<Sum> x \<in> ARescut (a_current_flow state') t. a_balance state' x) =
         (\<Sum> x \<in> ARescut (a_current_flow state') t - {t}. a_balance state' x) + a_balance state' t"
    proof(rule trans, rule sum.subset_diff[where B="{t}"], goal_cases)
      case 3
      then show ?case 
        using finite_ARescut t_prop(2)
        by (auto simp add: ARescut_def)
    next
      case 2
      thus ?case
        using finite_ARescut t_prop(2) by auto
    qed (auto simp add: ARescut_def finite_ARescut[OF t_prop(2)])
    also have "... < (N - 1) * ( \<epsilon> * current_\<gamma> state') + (- (1 - \<epsilon>) * current_\<gamma> state') "
    proof(rule add_le_less_mono, rule order.trans[rotated],
          rule order.trans, rule sum_bounded_above[of 
            "ARescut (a_current_flow state') t - {t}" "a_balance state'" "\<epsilon> *  current_\<gamma> state'"],
          goal_cases) 
      case 1
      thus ?case
        using  t_prop ARescut_around_in_V
        by (unfold ARescut_def) blast
    next
      case 2
      thus ?case
        using t_prop  ARescut_around_in_V[of t "a_current_flow state'"] gamma_0 \<epsilon>_axiom \<V>_finite       
        by (subst card_Diff_singleton)
           (auto  simp add: N_def  ARescut_def card_mono diff_le_mono)
    next
      case 3
      thus ?case by blast
    next
      case 4
      thus ?case
        using  t_prop by auto   
    qed
    finally have 11: "real (N - 1) * ( \<epsilon> * current_\<gamma> state') - (1 - \<epsilon>) * current_\<gamma> state'
                       > sum (a_balance state') (ARescut (a_current_flow state') t ) " 
      by linarith
    have residual_balance:"(\<Sum> x \<in> ARescut (a_current_flow state') t. a_balance state' x) < 0"
      proof(rule xt1(8)[rotated], rule 11, 
            rule order.trans[of _ " ( real (card \<V> - 1) *  \<epsilon>  - ( 1 - \<epsilon>)) * current_\<gamma> state'"], goal_cases)
      case 2
      thus ?case
        using eps_card_rewrite gamma_0 gamma_same eps_card_V 
        by (subst sym[OF mult_zero_left[of "current_\<gamma> state'"]], 
            intro  mult_right_mono[where c="current_\<gamma> state'"]) auto
    qed(simp add: algebra_simps N_def)
    have ARescut_fV: "ARescut (a_current_flow state') t \<subseteq> \<V>" 
      by (simp add: ARescut_around_in_V t_prop)
    show ?case 
    proof(rule ccontr,  goal_cases)
      case (1)
      then obtain f where "f is \<b> flow" by auto
      note 1 = this
      have " - (\<Sum> v \<in> ARescut (a_current_flow state') t. ereal (\<b> v)) \<le>
             ACap (ARescut (a_current_flow state') t)"
        using minus_leq_flip[OF flow_less_acut[OF 1 ARescut_fV]] by simp 
      also have "... =  - (\<Sum> v \<in> ARescut (a_current_flow state') t. ereal (\<b> v - a_balance state' v))"
        using flow_saturates_ares_cut[of "a_current_flow state'" " \<b> - a_balance state'" t,
            simplified, OF _ ARescut_fV ] is_Opt
        by(auto elim!:  is_OptE simp add: state'_def)
      also have "... = - ((\<Sum> v \<in> ARescut (a_current_flow state') t. \<b> v ) -
                         (\<Sum> v \<in> ARescut (a_current_flow state') t. a_balance state' v))"
        by (simp add: sum_subtractf)
      also have "...  < - (\<Sum> v \<in> ARescut (a_current_flow state') t. \<b> v ) "
        using residual_balance
        by simp
      finally show False by simp
    qed
  qed
qed

lemma send_flow_nothing_done: 
  assumes "\<not> (\<forall> v \<in> \<V>. a_balance  state v = 0)"
          "\<not> (\<exists> v \<in> \<V>. \<bar> a_balance state v\<bar> > (1- \<epsilon>) * current_\<gamma> state)"
          "implementation_invar state"
          "invar_gamma state"
  shows   "send_flow state = state\<lparr> return:= notyetterm\<rparr>"
proof(subst send_flow_cases[of state], goal_cases)
  case 1
  thus ?case
    by (auto intro: send_flow_cont_condE 
        simp add: send_flow_cont_upd_def send_flow_simps_without_dom(2) )
next
  case 2
  moreover hence "(\<forall> v \<in> \<V>. a_balance  state v = 0)"
    using assms(3) if_send_flow_succ_cond 
    by(auto elim!: send_flow_succ_condE)
  ultimately show ?case
    using assms(1)by simp
next
  case 3
  show ?case
  proof(rule send_flow_call1_condE [OF 3], rule invar_gammaE[OF assms(4)], goal_cases)
    case (1 f b \<gamma> s t P f' b' state')
    hence "(1 - \<epsilon>) * current_\<gamma> state < \<bar>a_balance state s\<bar>" "s \<in> \<V>"
      using  if_send_flow_call1_cond_basic[OF 3 assms(3) 1(5)[symmetric]]  
      by(auto simp add: algebra_simps)
    thus ?case
      using assms(2) by blast
  qed
next
  case 4
  show ?case
  proof(rule send_flow_call2_condE [OF 4], rule invar_gammaE[OF assms(4)], goal_cases)
    case (1 f b \<gamma> t s P f' b' state')
    hence "(1 - \<epsilon>) * current_\<gamma> state < \<bar>a_balance state t\<bar>" "t \<in> \<V>"
      using  if_send_flow_call2_cond_basic[OF 4 assms(3) 1(6)[symmetric]]  
      by(auto simp add: algebra_simps)
    thus ?case
      using assms(2) by blast
  qed
next
  case 5
  show ?case
  proof(rule send_flow_fail1_condE [OF 5], rule invar_gammaE[OF assms(4)], goal_cases)
    case (1 f b \<gamma> s)
    hence "(1 - \<epsilon>) * current_\<gamma> state < \<bar>a_balance state s\<bar>" "s \<in> \<V>"
      using  if_send_flow_fail1_cond_basic[OF 5 assms(3) 1(5)[symmetric]]  
      by(auto simp add: algebra_simps)
    thus ?case
      using assms(2) by blast
  qed
next
  case 6
  show ?case
  proof(rule send_flow_fail2_condE [OF 6], rule invar_gammaE[OF assms(4)], goal_cases)
    case (1 f b \<gamma> t)
    hence "(1 - \<epsilon>) * current_\<gamma> state < \<bar>a_balance state t\<bar>" "t \<in> \<V>"
      using  if_send_flow_fail2_cond_basic[OF 6 assms(3) 1(6)[symmetric]]  
      by(auto simp add: algebra_simps)
    thus ?case
      using assms(2) by blast
  qed
qed simp

lemma send_flow_forest_no_change:
  assumes "send_flow_dom state"
  shows   "(send_flow state) \<lparr>current_flow := current_flow state,
                              balance := balance state,
                              return:= return state\<rparr> = state"
  using assms 
  by(auto intro!: Algo_state.equality send_flow_changes_\<FF> send_flow_changes_conv_to_rdg
      send_flow_changes_actives send_flow_changes_current_\<gamma>
      send_flow_changes_rep_comp_card
      send_flow_changes_not_blocked)

lemma send_flow_invar_forest:
  assumes "underlying_invars state" "invar_gamma state"
          "implementation_invar state"
          "invar_integral state"
          "invar_isOptflow state"
          "invar_above_6Ngamma state"
          "real_of_int (\<Phi> state) \<le> 2 * real N"
  shows   "invar_forest (send_flow state)"
proof(rule invar_forestI, goal_cases)
  case (1 e)
  have send_flow_dom: "send_flow_dom state"
    by(auto intro!: send_flow_termination simp add: assms )
  hence alt_1: "e \<in> \<F> state"
    using 1 by (simp add: send_flow_changes_\<F> send_flow_dom)
  have phi_bound: "real_of_int (\<Phi> state) *
    current_\<gamma> state \<le> 2 * real N * current_\<gamma> state" 
    using assms by (auto elim: invar_gammaE)
  have above_6Ngamma_after: "invar_above_6Ngamma (send_flow state)"
    using assms(1,2,3,4,5,6) send_flow_dom send_flow_invars_pres(6) by blast
  have same_gamma: "current_\<gamma> (send_flow state) = current_\<gamma> state" 
    by (simp add: send_flow_changes_current_\<gamma> send_flow_dom)
  hence "real (4 * N) * current_\<gamma> (send_flow state) \<le>
        real (6 * N) * current_\<gamma> state - real (2 * N)  * current_\<gamma> state" 
    using phi_bound assms(2)  Phi_nonneg[OF assms(2)]
    by (auto simp add: algebra_simps elim!: invar_gammaE)
  also have "... \<le> real (6 * N) * current_\<gamma> (send_flow state) -
         real_of_int (int (2 * N) - \<Phi> (send_flow state)) * current_\<gamma> (send_flow state)"
    using same_gamma assms(2) Phi_nonneg
    by (auto simp add: algebra_simps invar_gammaI elim!: invar_gammaE)
  also have "... < a_current_flow (send_flow state) e"     
    using invar_above_6NgammaD[OF above_6Ngamma_after 1] by simp
  finally show ?case by simp
qed
end
end