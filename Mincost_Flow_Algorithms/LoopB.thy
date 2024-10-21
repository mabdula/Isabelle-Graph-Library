section \<open>Formalisation of Loop for Ordinary Augmentations\<close>

theory LoopB
  imports IntermediateSummary
begin

locale loopB_spec = algo_spec where fst="fst::'edge_type \<Rightarrow>'a" 
  and edge_map_update = "edge_map_update :: 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'c"
and get_from_set = "get_from_set :: ('edge_type \<Rightarrow> bool) \<Rightarrow> 'd \<Rightarrow> 'edge_type option"
for fst edge_map_update get_from_set+
fixes get_source_target_path_a ::"('a, 'd, 'c, 'edge_type) Algo_state \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'edge_type Redge list" 
  and get_source_target_path_b ::"('a, 'd, 'c, 'edge_type) Algo_state \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'edge_type Redge list"
  and get_source::"('a, 'd, 'c, 'edge_type) Algo_state \<Rightarrow> 'a"
  and get_target::"('a, 'd, 'c, 'edge_type) Algo_state \<Rightarrow> 'a"
  and get_source_for_target::"('a, 'd, 'c, 'edge_type) Algo_state \<Rightarrow> 'a \<Rightarrow> 'a"
  and get_target_for_source::"('a, 'd, 'c, 'edge_type) Algo_state \<Rightarrow> 'a \<Rightarrow> 'a"

locale loopB = algo where fst="fst::'edge_type \<Rightarrow>'a" and edge_map_update = "edge_map_update :: 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'c"+
loopB_spec where  fst= fst and get_source_target_path_a
 = "get_source_target_path_a::('a, 'd, 'c, 'edge_type) Algo_state \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'edge_type Redge list" 
  and edge_map_update = "edge_map_update :: 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'c"
and get_from_set = "get_from_set :: ('edge_type \<Rightarrow> bool) \<Rightarrow> 'd \<Rightarrow> 'edge_type option"
for fst  get_source_target_path_a edge_map_update
begin

term \<F>

function (domintros) loopB::"('a, 'd, 'c, 'edge_type) Algo_state \<Rightarrow> ('a, 'd, 'c, 'edge_type) Algo_state" where
  "loopB state = (let
                    f = current_flow state;
                    b = balance state;
                    \<gamma> = current_\<gamma> state
 in (if \<forall> v \<in> \<V>. b v = 0 then state \<lparr> return:=success\<rparr> 
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
                           loopB state'             
                else
                        state \<lparr> return := failure\<rparr>)) 
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
                         loopB state'                    
                else
                       state \<lparr> return := failure\<rparr>)
          ) 
      else state \<lparr> return := notyetterm\<rparr>
    ))"
  by auto


definition "loopB_succ_cond state = (let
                    f = current_flow state;
                    b = balance state;
                    \<gamma> = current_\<gamma> state
 in (if \<forall> v \<in> \<V>. b v = 0 then True
     else if \<exists> s \<in> \<V>. b s > (1 - \<epsilon>) * \<gamma> then 
          ( let s = get_source state
            in (if \<exists> t \<in> \<V>. b t < - \<epsilon> * \<gamma> \<and> resreach f s t then
                   let t = get_target_for_source state s;
                       P = get_source_target_path_a state s t;
                       f' = augment_edges f \<gamma> P;
                       b' = (\<lambda> v. if v = s then b s - \<gamma> 
                                  else if v = t then b t + \<gamma>
                                  else b v) in
                       False                   
                else
                        False)) 
     else if \<exists> t \<in> \<V>. b t < - (1 -\<epsilon>) * \<gamma> then 
          ( let t = get_target state
            in (if \<exists> s \<in> \<V>.  b s > \<epsilon> * \<gamma> \<and> resreach f s t then
                   let s = get_source_for_target state t;
                       P = get_source_target_path_b state s t;
                       f' = augment_edges f \<gamma> P;
                       b' = (\<lambda> v. if v = s then b s - \<gamma> 
                                  else if v = t then b t + \<gamma>
                                  else b v) in
                       False                    
                else
                       False)
          ) 
      else False
    ))"

lemma loopB_succ_condE:" loopB_succ_cond state \<Longrightarrow> (
                       \<And> f b \<gamma> . f = current_flow state \<Longrightarrow>
                    b = balance state \<Longrightarrow>
                    \<gamma> = current_\<gamma> state \<Longrightarrow>
                    \<forall> v \<in> \<V>. b v = 0 \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding  loopB_succ_cond_def by presburger

lemma loopB_succ_condI:"  f = current_flow state \<Longrightarrow>
                    b = balance state \<Longrightarrow>
                    \<gamma> = current_\<gamma> state \<Longrightarrow>
                    \<forall> v \<in> \<V>. b v = 0 \<Longrightarrow> loopB_succ_cond state"
  unfolding  loopB_succ_cond_def by presburger

definition "loopB_call1_cond state = (let
                    f = current_flow state;
                    b = balance state;
                    \<gamma> = current_\<gamma> state
 in (if \<forall> v \<in> \<V>. b v = 0 then False
     else if \<exists> s \<in> \<V>. b s > (1 - \<epsilon>) * \<gamma> then 
          ( let s = get_source state
            in (if \<exists> t \<in> \<V>. b t < - \<epsilon> * \<gamma> \<and> resreach f s t then
                   let t = get_target_for_source state s;
                       P = get_source_target_path_a state s t;
                       f' = augment_edges f \<gamma> P;
                       b' = (\<lambda> v. if v = s then b s - \<gamma> 
                                  else if v = t then b t + \<gamma>
                                  else b v) in
                       True                 
                else
                        False)) 
     else if \<exists> t \<in> \<V>. b t < - (1 -\<epsilon>) * \<gamma> then 
          ( let t = get_target state
            in (if \<exists> s \<in> \<V>.  b s > \<epsilon> * \<gamma> \<and> resreach f s t then
                   let s = get_source_for_target state t;
                       P = get_source_target_path_b state s t;
                       f' = augment_edges f \<gamma> P;
                       b' = (\<lambda> v. if v = s then b s - \<gamma> 
                                  else if v = t then b t + \<gamma>
                                  else b v) in
                       False                    
                else
                       False)
          ) 
      else False
    ))"

lemma loopB_call1_condE: "loopB_call1_cond state \<Longrightarrow>
                     ( \<And> f b \<gamma> s t P f' b' state'. f = current_flow state \<Longrightarrow>
                    b = balance state \<Longrightarrow>
                    \<gamma> = current_\<gamma> state \<Longrightarrow>
                   \<not>(\<forall>v\<in>\<V>. b v = 0) \<Longrightarrow>
                   \<exists> s \<in> \<V>. b s > (1 - \<epsilon>) * \<gamma> \<Longrightarrow>
                  s = get_source state \<Longrightarrow>
                  t = get_target_for_source state s \<Longrightarrow>
                  \<exists> t \<in> \<V>. b t < - \<epsilon> * \<gamma> \<and> resreach f s t  \<Longrightarrow>
                       P = get_source_target_path_a state s t \<Longrightarrow>
                       f' = augment_edges f \<gamma> P \<Longrightarrow>
                       b' = (\<lambda> v. if v = s then b s - \<gamma> 
                                  else if v = t then b t + \<gamma>
                                  else b v) \<Longrightarrow>
              state' = state \<lparr> current_flow := f', balance := b'\<rparr> \<Longrightarrow>
 PP) \<Longrightarrow> PP" for PP
  unfolding loopB_call1_cond_def Let_def by presburger


definition "loopB_call2_cond state = (let
                    f = current_flow state;
                    b = balance state;
                    \<gamma> = current_\<gamma> state
 in (if \<forall> v \<in> \<V>. b v = 0 then False
     else if \<exists> s \<in> \<V>. b s > (1 - \<epsilon>) * \<gamma> then 
          ( let s = get_source state
            in (if \<exists> t \<in> \<V>. b t < - \<epsilon> * \<gamma> \<and> resreach f s t then
                   let t = get_target_for_source state s;
                       P = get_source_target_path_a state s t;
                       f' = augment_edges f \<gamma> P;
                       b' = (\<lambda> v. if v = s then b s - \<gamma> 
                                  else if v = t then b t + \<gamma>
                                  else b v) in
                       False                
                else
                        False)) 
     else if \<exists> t \<in> \<V>. b t < - (1 -\<epsilon>) * \<gamma> then 
          ( let t = get_target state
            in (if \<exists> s \<in> \<V>.  b s > \<epsilon> * \<gamma> \<and> resreach f s t then
                   let s = get_source_for_target state t;
                       P = get_source_target_path_b state s t;
                       f' = augment_edges f \<gamma> P;
                       b' = (\<lambda> v. if v = s then b s - \<gamma> 
                                  else if v = t then b t + \<gamma>
                                  else b v) in
                       True                   
                else
                       False)
          ) 
      else False
    ))"

lemma loopB_call2_condE: "loopB_call2_cond state \<Longrightarrow>( \<And> f b \<gamma> t s P f' b' state'.
                    f = current_flow state \<Longrightarrow>
                    b = balance state \<Longrightarrow>
                    \<gamma> = current_\<gamma> state \<Longrightarrow>
 \<not> (\<forall> v \<in> \<V>. b v = 0) \<Longrightarrow>
  \<not> (\<exists> s \<in> \<V>. b s > (1 - \<epsilon>) * \<gamma>) \<Longrightarrow>
    \<exists> t \<in> \<V>. b t < - (1 -\<epsilon>) * \<gamma> \<Longrightarrow>
     t = get_target state \<Longrightarrow>
     \<exists> s \<in> \<V>.  b s > \<epsilon> * \<gamma> \<and> resreach f s t \<Longrightarrow>
     s = get_source_for_target state t \<Longrightarrow>
                       P = get_source_target_path_b state s t \<Longrightarrow>
                       f' = augment_edges f \<gamma> P \<Longrightarrow>
                       b' = (\<lambda> v. if v = s then b s - \<gamma> 
                                  else if v = t then b t + \<gamma>
                                  else b v) \<Longrightarrow>
                       state' = state \<lparr> current_flow := f', balance := b'\<rparr>
                     \<Longrightarrow> PP) \<Longrightarrow> PP" for PP
unfolding loopB_call2_cond_def Let_def by presburger

definition "loopB_fail1_cond state = (let
                    f = current_flow state;
                    b = balance state;
                    \<gamma> = current_\<gamma> state
 in (if \<forall> v \<in> \<V>. b v = 0 then False
     else if \<exists> s \<in> \<V>. b s > (1 - \<epsilon>) * \<gamma> then 
          ( let s = get_source state
            in (if \<exists> t \<in> \<V>. b t < - \<epsilon> * \<gamma> \<and> resreach f s t then
                   let t = get_target_for_source state s;
                       P = get_source_target_path_a state s t;
                       f' = augment_edges f \<gamma> P;
                       b' = (\<lambda> v. if v = s then b s - \<gamma> 
                                  else if v = t then b t + \<gamma>
                                  else b v) in
                       False                
                else
                       True)) 
     else if \<exists> t \<in> \<V>. b t < - (1 -\<epsilon>) * \<gamma> then 
          ( let t = get_target state
            in (if \<exists> s \<in> \<V>.  b s >  \<epsilon> * \<gamma> \<and> resreach f s t then
                   let s = get_source_for_target state t;
                       P = get_source_target_path_b state s t;
                       f' = augment_edges f \<gamma> P;
                       b' = (\<lambda> v. if v = s then b s - \<gamma> 
                                  else if v = t then b t + \<gamma>
                                  else b v) in
                       False                    
                else
                       False)
          ) 
      else False
    ))"

lemma loopB_fail1_condE:
"loopB_fail1_cond state \<Longrightarrow>
(\<And> f b \<gamma> s. f = current_flow state \<Longrightarrow>
                    b = balance state \<Longrightarrow>
                    \<gamma> = current_\<gamma> state \<Longrightarrow>
 \<not> ( \<forall> v \<in> \<V>. b v = 0) 
 \<Longrightarrow> ( \<exists> s \<in> \<V>. b s > (1 - \<epsilon>) * \<gamma>)  \<Longrightarrow>
           s = get_source state \<Longrightarrow>
           \<not>( \<exists> t \<in> \<V>. b t < - \<epsilon> * \<gamma> \<and> resreach f s t)  \<Longrightarrow> P ) \<Longrightarrow> P"
  unfolding loopB_fail1_cond_def Let_def
  by presburger
 
definition "loopB_fail2_cond state = (let
                    f = current_flow state;
                    b = balance state;
                    \<gamma> = current_\<gamma> state
 in (if \<forall> v \<in> \<V>. b v = 0 then False
     else if \<exists> s \<in> \<V>. b s > (1 - \<epsilon>) * \<gamma> then 
          ( let s = get_source state
            in (if \<exists> t \<in> \<V>. b t < - \<epsilon> * \<gamma> \<and> resreach f s t then
                   let t = get_target_for_source state s;
                       P = get_source_target_path_a state s t;
                       f' = augment_edges f \<gamma> P;
                       b' = (\<lambda> v. if v = s then b s - \<gamma> 
                                  else if v = t then b t + \<gamma>
                                  else b v) in
                       False                
                else
                       False)) 
     else if \<exists> t \<in> \<V>. b t < - (1 -\<epsilon>) * \<gamma> then 
          ( let t = get_target state
            in (if \<exists> s \<in> \<V>.  b s > \<epsilon> * \<gamma> \<and> resreach f s t then
                   let s = get_source_for_target state t;
                       P = get_source_target_path_b state s t;
                       f' = augment_edges f \<gamma> P;
                       b' = (\<lambda> v. if v = s then b s - \<gamma> 
                                  else if v = t then b t + \<gamma>
                                  else b v) in
                       False                    
                else
                       True)
          ) 
      else False
    ))"

lemma loopB_fail2_condE:
"loopB_fail2_cond state \<Longrightarrow>
(\<And> f b \<gamma> t. f = current_flow state \<Longrightarrow>
                    b = balance state \<Longrightarrow>
                    \<gamma> = current_\<gamma> state \<Longrightarrow>
 \<not> ( \<forall> v \<in> \<V>. b v = 0) 
 \<Longrightarrow> \<not> (\<exists> s \<in> \<V>. b s > (1 - \<epsilon>) * \<gamma>)  \<Longrightarrow>
       \<exists> t \<in> \<V>. b t < - (1 -\<epsilon>) * \<gamma> \<Longrightarrow>
           t = get_target state \<Longrightarrow>
           \<not>( \<exists> s \<in> \<V>.  b s > \<epsilon> * \<gamma> \<and> resreach f s t)  \<Longrightarrow> P ) \<Longrightarrow> P"
  unfolding loopB_fail2_cond_def Let_def
  by presburger

definition "loopB_cont_cond state = (let
                    f = current_flow state;
                    b = balance state;
                    \<gamma> = current_\<gamma> state
 in (if \<forall> v \<in> \<V>. b v = 0 then False
     else if \<exists> s \<in> \<V>. b s > (1 - \<epsilon>) * \<gamma> then 
          ( let s = get_source state
            in (if \<exists> t \<in> \<V>. b t < - \<epsilon> * \<gamma> \<and> resreach f s t then
                   let t = get_target_for_source state s;
                       P = get_source_target_path_a state s t;
                       f' = augment_edges f \<gamma> P;
                       b' = (\<lambda> v. if v = s then b s - \<gamma> 
                                  else if v = t then b t + \<gamma>
                                  else b v) in
                       False                
                else
                       False)) 
     else if \<exists> t \<in> \<V>. b t < - (1 -\<epsilon>) * \<gamma> then 
          ( let t = get_target state
            in (if \<exists> s \<in> \<V>.  b s > \<epsilon> * \<gamma> \<and> resreach f s t then
                   let s = get_source_for_target state t;
                       P = get_source_target_path_b state s t;
                       f' = augment_edges f \<gamma> P;
                       b' = (\<lambda> v. if v = s then b s - \<gamma> 
                                  else if v = t then b t + \<gamma>
                                  else b v) in
                       False                    
                else
                       False)
          ) 
      else True
    ))"

lemma loopB_cont_condE:
"loopB_cont_cond state \<Longrightarrow>
(\<And> f b \<gamma> . f = current_flow state \<Longrightarrow>
                    b = balance state \<Longrightarrow>
                    \<gamma> = current_\<gamma> state \<Longrightarrow>
 \<not> ( \<forall> v \<in> \<V>. b v = 0) 
 \<Longrightarrow> \<not> (\<exists> s \<in> \<V>. b s > (1 - \<epsilon>) * \<gamma>)  \<Longrightarrow>
      \<not>( \<exists> t \<in> \<V>. b t < - (1 -\<epsilon>) * \<gamma> )  \<Longrightarrow> P ) \<Longrightarrow> P"
  unfolding loopB_cont_cond_def Let_def
  by presburger

lemma loopB_cases: 
  assumes "loopB_cont_cond  state \<Longrightarrow> P"
          "loopB_succ_cond  state \<Longrightarrow> P"
          "loopB_call1_cond  state \<Longrightarrow> P"
          "loopB_call2_cond  state \<Longrightarrow> P"
          "loopB_fail1_cond  state \<Longrightarrow> P"
          "loopB_fail2_cond  state \<Longrightarrow> P"
        shows P
proof-
  have "loopB_cont_cond  state \<or> loopB_succ_cond  state \<or>
        loopB_call1_cond  state \<or> loopB_call2_cond  state \<or>
        loopB_fail1_cond  state \<or> loopB_fail2_cond  state"
    unfolding loopB_cont_cond_def loopB_succ_cond_def
              loopB_call1_cond_def loopB_call2_cond_def
              loopB_fail1_cond_def loopB_fail2_cond_def Let_def
    by(auto split: if_split)    
  thus P
    using assms by auto
qed

definition "loopB_succ_upd state = (let
                    f = current_flow state;
                    b = balance state;
                    \<gamma> = current_\<gamma> state
 in  state \<lparr> return:=success\<rparr>)"

lemma loopB_succ_upd_changes: 
"\<FF> (loopB_succ_upd state) = \<FF> state"
"conv_to_rdg (loopB_succ_upd state) = conv_to_rdg state"
"actives (loopB_succ_upd state) = actives state"
"current_\<gamma> (loopB_succ_upd state) = current_\<gamma>  state"
"representative (loopB_succ_upd state) = representative state"
"\<F> (loopB_succ_upd state) = \<F> state"
"comp_card (loopB_succ_upd state) = comp_card state"
"\<FF>_imp (loopB_succ_upd state) = \<FF>_imp state"
"not_blocked (loopB_succ_upd state) = not_blocked state"
  unfolding loopB_succ_upd_def Let_def by auto

term "\<F> (state::('a, 'd, 'c, 'edge_type) Algo_state)"

definition "loopB_call1_upd state = (let
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
                    state \<lparr> current_flow := f', balance := b'\<rparr>)"

lemma loopB_call1_upd_changes: 
"\<FF> (loopB_call1_upd state) = \<FF> state"
"conv_to_rdg (loopB_call1_upd state) = conv_to_rdg state"
"actives (loopB_call1_upd state) = actives state"
"current_\<gamma> (loopB_call1_upd state) = current_\<gamma>  state"
"representative (loopB_call1_upd state) = representative state"
"\<F> (loopB_call1_upd state) = \<F> state"
"comp_card (loopB_call1_upd state) = comp_card state"
"\<FF>_imp (loopB_call1_upd state) = \<FF>_imp state"
"not_blocked (loopB_call1_upd state) = not_blocked state"
  unfolding loopB_call1_upd_def Let_def by auto

definition "loopB_fail_upd state = state \<lparr> return :=failure \<rparr>"

lemma loopB_fail_upd_changes: 
"\<FF> (loopB_fail_upd state) = \<FF> state"
"conv_to_rdg (loopB_fail_upd state) = conv_to_rdg state"
"actives (loopB_fail_upd state) = actives state"
"current_\<gamma> (loopB_fail_upd state) = current_\<gamma>  state"
"representative (loopB_fail_upd state) = representative state"
"\<F> (loopB_fail_upd state) = \<F> state"
"comp_card (loopB_fail_upd state) = comp_card state"
"\<FF>_imp (loopB_fail_upd state) = \<FF>_imp state"
"not_blocked (loopB_fail_upd state) = not_blocked state"
  unfolding loopB_fail_upd_def Let_def by auto

definition "loopB_call2_upd state= (let
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
                       state \<lparr> current_flow := f', balance := b'\<rparr>)"

lemma loopB_call2_upd_changes: 
"\<FF> (loopB_call2_upd state) = \<FF> state"
"conv_to_rdg (loopB_call2_upd state) = conv_to_rdg state"
"actives (loopB_call2_upd state) = actives state"
"current_\<gamma> (loopB_call2_upd state) = current_\<gamma>  state"
"representative (loopB_call2_upd state) = representative state"
"\<F> (loopB_call2_upd state) = \<F> state"
"comp_card (loopB_call2_upd state) = comp_card state"
"\<FF>_imp (loopB_call2_upd state) = \<FF>_imp state"
"not_blocked (loopB_call2_upd state) = not_blocked state"
  unfolding loopB_call2_upd_def Let_def by auto

definition "loopB_cont_upd state = state \<lparr> return := notyetterm\<rparr>"

lemma loopB_cont_upd_changes: 
"\<FF> (loopB_cont_upd state) = \<FF> state"
"conv_to_rdg (loopB_cont_upd state) = conv_to_rdg state"
"actives (loopB_cont_upd state) = actives state"
"current_\<gamma> (loopB_cont_upd state) = current_\<gamma>  state"
"representative (loopB_cont_upd state) = representative state"
"\<F> (loopB_cont_upd state) = \<F> state"
"comp_card (loopB_cont_upd state) = comp_card state"
"\<FF>_imp (loopB_cont_upd state) = \<FF>_imp state"
"not_blocked (loopB_cont_upd state) = not_blocked state"
  unfolding loopB_cont_upd_def Let_def by auto

lemma loopB_simps: 
  assumes "loopB_dom state"
  shows   "loopB_succ_cond state \<Longrightarrow> loopB state = (loopB_succ_upd state)"
          "loopB_cont_cond state \<Longrightarrow> loopB state = (loopB_cont_upd state)"
          "loopB_fail1_cond state \<Longrightarrow> loopB state = (loopB_fail_upd state)"
          "loopB_fail2_cond state \<Longrightarrow> loopB state = (loopB_fail_upd state)"
          "loopB_call1_cond state \<Longrightarrow> loopB state = loopB (loopB_call1_upd state)"
          "loopB_call2_cond state \<Longrightarrow> loopB state = loopB (loopB_call2_upd state)"
proof-
  show "loopB_succ_cond state \<Longrightarrow> local.loopB state = loopB_succ_upd state"
    using  loopB.psimps  assms
    unfolding loopB_succ_upd_def Let_def 
    by (auto elim: loopB_succ_condE)
  show "loopB_cont_cond state \<Longrightarrow> local.loopB state = loopB_cont_upd state"
    apply(subst loopB.psimps, simp add: assms)
    unfolding loopB_cont_upd_def loopB_cont_cond_def Let_def 
    by presburger
  show " loopB_fail1_cond state \<Longrightarrow> loopB state = loopB_fail_upd state"
    apply(subst loopB.psimps, simp add: assms)
    unfolding loopB_fail_upd_def loopB_fail1_cond_def Let_def 
    by presburger
  show "loopB_fail2_cond state \<Longrightarrow> loopB state = loopB_fail_upd state"
    apply(subst loopB.psimps, simp add: assms)
    unfolding loopB_fail_upd_def loopB_fail2_cond_def Let_def 
    by presburger
  show " loopB_call1_cond state \<Longrightarrow> loopB state = loopB (loopB_call1_upd state)"
  proof- 
    assume asm:"loopB_call1_cond state"
    show "loopB state = loopB (loopB_call1_upd state)"
    proof(rule loopB_call1_condE[OF asm], goal_cases)
      case (1 f b \<gamma> s t P f' b' state')
      thus ?case  
       using loopB.psimps assms
        unfolding loopB_call1_upd_def Let_def 
         by (auto elim: loopB_call1_condE)
     qed
   qed
   show " loopB_call2_cond state \<Longrightarrow> loopB state = loopB (loopB_call2_upd state)"
   proof-
    assume asm:"loopB_call2_cond state"
    show "loopB state = loopB (loopB_call2_upd state)"
    proof(rule loopB_call2_condE[OF asm], goal_cases)
      case (1 f b \<gamma> s t P f' b' state')
      thus ?case  
       using loopB.psimps assms
        unfolding loopB_call2_upd_def Let_def 
         by (auto elim: loopB_call2_condE)
     qed
   qed
 qed   
    
lemma loopB_induct:
  assumes "loopB_dom state"
 "\<And> state. \<lbrakk> loopB_dom state ; 
             loopB_call1_cond state \<Longrightarrow> P (loopB_call1_upd state);
             loopB_call2_cond state \<Longrightarrow> P (loopB_call2_upd state) \<rbrakk> \<Longrightarrow> P state"
    shows "P state"
  apply(rule loopB.pinduct[OF assms(1)])
  subgoal for state
    apply(rule assms(2), simp)
    subgoal
      apply(rule loopB_call1_condE[of state], simp)
      unfolding loopB_call1_upd_def Let_def by auto
    subgoal
      apply(rule loopB_call2_condE[of state], simp)
      unfolding loopB_call2_upd_def Let_def by auto
    done
  done

definition "get_source_target_path_a_cond state s t P b \<gamma> f \<equiv>
             get_source_target_path_a state s t = P \<and> s \<in> \<V> \<and> t \<in> \<V> \<and>  s \<noteq> t \<and>
             aux_invar state \<and> (\<forall> e \<in> \<F> state . f e > 0)\<and> resreach f s t\<and>
             b = balance state\<and> \<gamma> = current_\<gamma> state \<and> s = get_source state \<and>
             t = get_target_for_source state s \<and> f = current_flow state  \<and>
             loopB_call1_cond state \<and> invar_gamma state"

lemma get_source_target_path_a_condI:
 " \<lbrakk>get_source_target_path_a state s t = P ; s \<in> \<V> ; t \<in> \<V> ;  s \<noteq> t;
    aux_invar state; (\<forall> e \<in> \<F> state . f e > 0); resreach f s t;
    b = balance state; \<gamma> = current_\<gamma> state ;  s = get_source state ;
    t = get_target_for_source state s;
       f = current_flow state; loopB_call1_cond state; invar_gamma state\<rbrakk> 
          \<Longrightarrow> get_source_target_path_a_cond state s t P b \<gamma> f"
  by(auto simp add: get_source_target_path_a_cond_def)

definition "get_source_target_path_b_cond state s t P b \<gamma> f \<equiv>
           get_source_target_path_b state s t = P \<and> s \<in> \<V> \<and> t \<in> \<V> \<and> s \<noteq> t\<and> aux_invar state \<and>
         (\<forall> e \<in> \<F> state . f e > 0)\<and> resreach f s t\<and> b = balance state\<and> \<gamma> = current_\<gamma> state \<and>
         t = get_target state \<and>  s = get_source_for_target state t \<and> f = current_flow state \<and>
         loopB_call2_cond state \<and>  invar_gamma state"

lemma  get_source_target_path_b_condI:
       "\<lbrakk>get_source_target_path_b state s t = P; s \<in> \<V>; t \<in> \<V>; s \<noteq> t; aux_invar state;
         (\<forall> e \<in> \<F> state . f e > 0); resreach f s t; b = balance state; \<gamma> = current_\<gamma> state ;
          t = get_target state; s = get_source_for_target state t; f = current_flow state;
          loopB_call2_cond state ;  invar_gamma state\<rbrakk>
         \<Longrightarrow> get_source_target_path_b_cond state s t P b \<gamma> f"
  by(auto simp add: get_source_target_path_b_cond_def)

lemma get_source_target_path_a_condE:
 " get_source_target_path_a_cond state s t P b \<gamma> f \<Longrightarrow>
   ( \<lbrakk>get_source_target_path_a state s t = P ; s \<in> \<V> ; t \<in> \<V> ;  s \<noteq> t;
    aux_invar state; (\<forall> e \<in> \<F> state . f e > 0); resreach f s t;
    b = balance state; \<gamma> = current_\<gamma> state ;  s = get_source state ;
    t = get_target_for_source state s;
       f = current_flow state; loopB_call1_cond state; invar_gamma state\<rbrakk> 
          \<Longrightarrow> Q) \<Longrightarrow> Q"
  by(auto simp add: get_source_target_path_a_cond_def)

lemma  get_source_target_path_b_condE:
       "get_source_target_path_b_cond state s t P b \<gamma> f \<Longrightarrow>
        (\<lbrakk>get_source_target_path_b state s t = P; s \<in> \<V>; t \<in> \<V>; s \<noteq> t; aux_invar state;
         (\<forall> e \<in> \<F> state . f e > 0); resreach f s t; b = balance state; \<gamma> = current_\<gamma> state ;
          t = get_target state; s = get_source_for_target state t; f = current_flow state;
          loopB_call2_cond state ;  invar_gamma state\<rbrakk>
         \<Longrightarrow> Q) \<Longrightarrow> Q"
  by(auto simp add: get_source_target_path_b_cond_def)
end
locale loopB_Reasoning = loopB +
assumes get_source_target_path_a_axioms:                         
     "\<And> state s t P b \<gamma> f. get_source_target_path_a_cond state s t P b \<gamma> f \<Longrightarrow> Rcap f (set P) > 0"
     "\<And> state s t P b \<gamma> f. get_source_target_path_a_cond state s t P b \<gamma> f \<Longrightarrow> invar_isOptflow state
                            \<Longrightarrow> is_min_path f s t P"
     "\<And> state s t P b \<gamma> f. get_source_target_path_a_cond state s t P b \<gamma> f
                            \<Longrightarrow> oedge ` set P \<subseteq> to_set (actives state) \<union> \<F> state"
     "\<And> state s t P b \<gamma> f. get_source_target_path_a_cond state s t P b \<gamma> f \<Longrightarrow>  distinct P"
and get_source_target_path_b_axioms:
   "\<And> state s t P b \<gamma> f. get_source_target_path_b_cond state s t P b \<gamma> f \<Longrightarrow> Rcap f (set P) > 0"
   "\<And> state s t P b \<gamma> f. get_source_target_path_b_cond state s t P b \<gamma> f  \<Longrightarrow> invar_isOptflow state 
                          \<Longrightarrow> is_min_path f s t P"
   "\<And> state s t P b \<gamma> f. get_source_target_path_b_cond state s t P b \<gamma> f 
                          \<Longrightarrow> oedge ` set P \<subseteq> to_set (actives state) \<union> \<F> state"
   "\<And> state s t P b \<gamma> f. get_source_target_path_b_cond state s t P b \<gamma> f \<Longrightarrow> distinct P"
and get_source_axioms:
   "\<And> s state b \<gamma>. \<lbrakk>b = balance state; \<gamma> = current_\<gamma> state;  s = get_source state;
                    loopB_call1_cond state \<or> loopB_fail1_cond state\<rbrakk> 
                    \<Longrightarrow> s \<in> \<V> \<and> b s > (1 - \<epsilon>) * \<gamma>"
and get_target_axioms:
   "\<And> t state b \<gamma>. \<lbrakk>b = balance state ; \<gamma> = current_\<gamma> state; t = get_target state;
                     loopB_call2_cond state \<or> loopB_fail2_cond state\<rbrakk> 
                    \<Longrightarrow> t \<in> \<V> \<and> b t < - (1 -\<epsilon>) * \<gamma>"
and get_target_for_source_axioms:
    "\<And> s t state b \<gamma> f. \<lbrakk>b = balance state; \<gamma> = current_\<gamma> state; f = current_flow state; s = get_source state; 
                         t = get_target_for_source state s; loopB_call1_cond state; invar_gamma state\<rbrakk>
                        \<Longrightarrow> t \<in> \<V> \<and> b t < - \<epsilon> * \<gamma> \<and> resreach f s t "
and get_source_for_target_axioms:
    "\<And> s t state b \<gamma> f. \<lbrakk> b = balance state; \<gamma> = current_\<gamma> state; f = current_flow state;
                          t = get_target state; s = get_source_for_target state t; loopB_call2_cond state ; invar_gamma  state\<rbrakk>
                        \<Longrightarrow> s \<in> \<V> \<and> b s >  \<epsilon> * \<gamma> \<and> resreach f s t"
begin

lemma loopB_call1_invar_aux12_pres:
  assumes "loopB_call1_cond state"
          "invar_aux12 state"
          "invar_gamma state"
    shows "invar_aux12 (loopB_call1_upd state)"
proof(rule loopB_call1_condE[OF assms(1)], goal_cases)
  case (1 f b \<gamma> s t P f' b' state')
  note unf = this
  hence s_prop:"(1 - \<epsilon>) * \<gamma> < b s " "s \<in> \<V>"
    using assms(1) get_source_axioms by blast+
  have t_prop:" b t < - \<epsilon> * \<gamma> " "resreach f s t " " t \<in> \<V>"
    using 1 get_target_for_source_axioms assms(1,3) by blast+
  have b_s: "b s > 0"
    using s_prop assms(3)
    unfolding invar_gamma_def unf 
    by (smt (verit, ccfv_SIG) \<epsilon>_axiom(2) add_divide_distrib divide_eq_1_iff mul_zero_cancel)
  have b_t: "b t < 0"
    using t_prop assms(3)
    unfolding invar_gamma_def unf
    by (smt (verit, del_insts) \<epsilon>_axiom(1) mult_neg_pos)
  have s_rep: "representative state s = s" 
    using s_prop assms(2) b_s unf
    unfolding invar_aux12_def by fastforce
  have t_rep: "representative state t = t" 
    using t_prop assms(2) b_t unf
    unfolding invar_aux12_def by fastforce
  show ?case 
  proof(rule invar_aux12I, goal_cases)
    case (1 v)
    have same_rep:"representative (loopB_call1_upd state) v = representative state v"
      unfolding loopB_call1_upd_def Let_def by simp
    have b_b': "b' = balance (loopB_call1_upd state)" 
      unfolding unf loopB_call1_upd_def Let_def by simp
    then show ?case 
    proof(cases "v = s")
      case True
      show ?thesis 
        using assms(2) 1 same_rep True s_rep
        unfolding invar_aux12_def
        by auto
    next
      case False
      note false = this
      then show ?thesis 
      proof(cases "v = t")
        case True
        then show ?thesis 
        using assms(2) 1 same_rep True t_rep
        unfolding invar_aux12_def
        by auto
      next
        case False
        hence "b' v = b v" using false unfolding unf(11) by simp
        hence "b v \<noteq> 0" using 1 b_b' by simp
        hence "representative state v = v"
          using assms(2) 1 unfolding invar_aux12_def unf by simp
        then show ?thesis  unfolding loopB_call1_upd_def Let_def by simp
      qed
    qed
  qed
qed

lemma loopB_call2_invar_aux12_pres:
  assumes "loopB_call2_cond state"
          "invar_aux12 state"
          "invar_gamma state"
    shows "invar_aux12 (loopB_call2_upd state)"
proof(rule loopB_call2_condE[OF assms(1)], goal_cases)
  case (1 f b \<gamma> t s P f' b' state')
  note unf = this
  have t_prop:" b t < - (1-\<epsilon>) * \<gamma> "  " t \<in> \<V>"
    using 1 get_target_axioms assms(1) by blast+
  hence s_prop:"\<epsilon> * \<gamma> < b s " "s \<in> \<V>" "resreach f s t " 
    using  get_source_for_target_axioms[OF 1(2) 1(3) 1(1) 1(7) 1(9) assms(1,3)] by auto
  have b_s: "b s > 0"
    using s_prop assms(3)
    unfolding invar_gamma_def unf 
    by (smt (verit) \<epsilon>_axiom(1) mult_pos_pos)
  have b_t: "b t < 0"
    using t_prop assms(3)
    unfolding invar_gamma_def unf 
    by (smt (verit, ccfv_SIG) mult_minus_left mult_pos_pos unf(3) unf(5) unf(8))
  have s_rep: "representative state s = s" 
    using s_prop assms(2) b_s unf
    unfolding invar_aux12_def by fastforce
  have t_rep: "representative state t = t" 
    using t_prop assms(2) b_t unf
    unfolding invar_aux12_def by fastforce
  show ?case 
  proof(rule invar_aux12I, goal_cases)
    case (1 v)
    have same_rep:"representative (loopB_call2_upd state) v = representative state v"
      unfolding loopB_call2_upd_def Let_def by simp
    have b_b': "b' = balance (loopB_call2_upd state)" 
      unfolding unf loopB_call2_upd_def Let_def by simp
    then show ?case 
    proof(cases "v = s")
      case True
      show ?thesis 
        using assms(2) 1 same_rep True s_rep
        unfolding invar_aux12_def
        by auto
    next
      case False
      note false = this
      then show ?thesis 
      proof(cases "v = t")
        case True
        then show ?thesis 
        using assms(2) 1 same_rep True t_rep
        unfolding invar_aux12_def
        by auto
      next
        case False
        hence "b' v = b v" using false unfolding unf(12) by simp
        hence "b v \<noteq> 0" using 1 b_b' by simp
        hence "representative state v = v"
          using assms(2) 1 unfolding invar_aux12_def unf by simp
        then show ?thesis  unfolding loopB_call2_upd_def Let_def by simp
      qed
    qed
  qed
qed

theorem loopB_invar_aux_pres: 
  assumes "loopB_dom state" "aux_invar state" "invar_gamma state"
  shows   "aux_invar (loopB state)"
  using assms(2, 3) 
proof(induction rule: loopB_induct[OF assms(1)])
  case (1 state)
  note "1a" = this
  then show ?case 
  proof(cases rule: loopB_cases[of state])
    case 1
    show ?thesis 
      apply(subst loopB_simps(2), simp add: 1 "1a" , simp add: 1 "1a")
      apply(rule aux_invar_pres[of state ]) 
      by(auto simp add: loopB_cont_upd_def[of state] 1 "1a" validF_def )
  next
    case 2
    show ?thesis
      apply(subst loopB_simps(1), simp add: 1 2, simp add: 1 2)
      apply(rule aux_invar_pres[of state ]) 
      by(auto simp add: loopB_succ_upd_def[of state] 1 2 validF_def)
  next 
    case 3
    have invar_gamma:"invar_gamma (loopB_call1_upd state)" 
      using 1(5) unfolding invar_gamma_def loopB_call1_upd_def Let_def by simp
    show ?thesis
        apply(subst loopB_simps(5)[OF 1(1) 3])
        apply(rule 1(2)[OF 3 _ invar_gamma])
        apply(rule aux_invar_pres[of state ])      
         using loopB_call1_upd_changes[of state] 1 
         by(auto elim: invar_aux12E[OF loopB_call1_invar_aux12_pres[OF 3 _ 1(5)]] 
             simp add: validF_def) 
   next 
     case 4
      have invar_gamma:"invar_gamma (loopB_call2_upd state)" 
      using 1(5) unfolding invar_gamma_def loopB_call2_upd_def Let_def by simp
    show ?thesis
        apply(subst loopB_simps(6)[OF 1(1) 4])
        apply(rule 1(3)[OF 4 _ invar_gamma])
        apply(rule aux_invar_pres)      
         using loopB_call2_upd_changes[of state] 1 
         by (auto elim: invar_aux12E[OF loopB_call2_invar_aux12_pres[OF 4 _ 1(5)]] 
              simp add: validF_def)
    next
      case 5
      show ?thesis
      apply(subst loopB_simps(3), simp add: 5 "1a" , simp add: 5 "1a")
      apply(rule aux_invar_pres[of state ]) 
        by(auto simp add: loopB_fail_upd_def[of state] 5 "1a" validF_def)
    next
      case 6
      show ?thesis
      apply(subst loopB_simps(4), simp add: 6 "1a" , simp add: 6 "1a")
      apply(rule aux_invar_pres[of state ]) 
      by(auto simp add: loopB_fail_upd_def[of state] 6 "1a" validF_def)
  qed
qed

lemma invar_aux_pres_call1:
  assumes "loopB_call1_cond state"
          "aux_invar state"
          "invar_gamma state"
    shows "aux_invar (loopB_call1_upd state)"
    apply(rule aux_invar_pres[of state, OF assms(2)])      
         using loopB_call1_upd_changes[of state]
         by(auto elim: invar_aux12E[OF loopB_call1_invar_aux12_pres[OF assms(1) _ assms(3)]]
              simp add: validF_def) 

lemma invar_aux_pres_call2:
  assumes "loopB_call2_cond state"
          "aux_invar state"
          "invar_gamma state"
    shows "aux_invar (loopB_call2_upd state)"
    apply(rule aux_invar_pres[of state, OF assms(2)])      
         using loopB_call2_upd_changes[of state]
         by(auto elim: invar_aux12E[OF loopB_call2_invar_aux12_pres[OF assms(1) _ assms(3)]]
              simp add: validF_def) 

lemma invar_gamma_pres_succ:
"invar_gamma state \<Longrightarrow> invar_gamma (loopB_succ_upd state)"
  unfolding loopB_succ_upd_def invar_gamma_def by simp

lemma invar_gamma_pres_cont:
"invar_gamma state \<Longrightarrow> invar_gamma (loopB_cont_upd state)"
  unfolding loopB_cont_upd_def invar_gamma_def by simp

lemma invar_gamma_pres_fail:
"invar_gamma state \<Longrightarrow> invar_gamma (loopB_fail_upd state)"
  unfolding loopB_fail_upd_def invar_gamma_def by simp

lemma invar_gamma_pres_call1:
"invar_gamma state \<Longrightarrow> invar_gamma (loopB_call1_upd state)"
  unfolding loopB_call1_upd_def invar_gamma_def Let_def by simp

lemma invar_gamma_pres_call2:
"invar_gamma state \<Longrightarrow> invar_gamma (loopB_call2_upd state)"
  unfolding loopB_call2_upd_def invar_gamma_def Let_def by simp

theorem loopB_invar_gamma_pres: 
  assumes "loopB_dom state" "invar_gamma state"
  shows   "invar_gamma (loopB state)"
  using assms(2) 
proof(induction rule: loopB_induct[OF assms(1)])
  case (1 state)
  note "1a" = this
  then show ?case 
  proof(cases rule: loopB_cases[of state])
    case 1
    show ?thesis 
      apply(subst loopB_simps(2), simp add: 1 "1a" , simp add: 1 "1a")
      apply(rule invar_gamma_pres_cont[of state ]) 
      by(auto simp add: loopB_cont_upd_def[of state] 1 "1a")
  next
    case 2
    show ?thesis
      apply(subst loopB_simps(1), simp add: 1 2, simp add: 1 2)
      apply(rule invar_gamma_pres_succ[of state ]) 
      by(auto simp add: loopB_succ_upd_def[of state] 1 2)
  next 
    case 3
    show ?thesis
        apply(subst loopB_simps(5)[OF 1(1) 3])
        apply(rule 1(2)[OF 3])
        apply(rule invar_gamma_pres_call1)      
        using loopB_call1_upd_changes[of state] 1 
        by auto
   next 
    case 4
    show ?thesis
        apply(subst loopB_simps(6)[OF 1(1) 4])
        apply(rule 1(3)[OF 4])
        apply(rule invar_gamma_pres_call2)      
        using loopB_call2_upd_changes[of state] 1 
        by auto
    next
      case 5
      show ?thesis
      apply(subst loopB_simps(3), simp add: 5 "1a" , simp add: 5 "1a")
      apply(rule invar_gamma_pres_fail[of state ]) 
        by(auto simp add: loopB_fail_upd_def[of state] 5 "1a")
    next
      case 6
      show ?thesis
      apply(subst loopB_simps(4), simp add: 6 "1a" , simp add: 6 "1a")
      apply(rule invar_gamma_pres_fail[of state ]) 
      by(auto simp add: loopB_fail_upd_def[of state] 6 "1a")
  qed
qed


lemma loopB_changes_\<FF>: 
  assumes "loopB_dom state"
  shows "\<FF> (loopB state) = \<FF> state"
proof(induction rule: loopB_induct[OF assms(1)])
  case (1 state)
  note IH = this
  show ?case
  proof(cases rule: loopB_cases[of state])
    case 1
    then show ?thesis 
      apply(subst loopB_simps(2)[OF IH(1) 1])
      using loopB_cont_upd_changes[of state] by simp
  next
    case 2
    then show ?thesis
      apply(subst loopB_simps(1)[OF IH(1) 2])
      using loopB_succ_upd_changes[of state] by simp
  next
    case 3
    then show ?thesis 
      using loopB_simps(5)[OF IH(1) 3] IH loopB_call1_upd_changes 
      by auto
  next
    case 4
    then show ?thesis 
      using loopB_simps(6)[OF IH(1) 4] IH loopB_call2_upd_changes 
      by auto
  next
    case 5
    then show ?thesis 
      apply(subst loopB_simps(3)[OF IH(1) 5])
      using loopB_fail_upd_changes[of state] by simp
  next
    case 6
    then show ?thesis
      apply(subst loopB_simps(4)[OF IH(1) 6])
      using loopB_fail_upd_changes[of state] by simp
  qed
qed

lemma loopB_changes_conv_to_rdg: 
  assumes "loopB_dom state"
  shows "conv_to_rdg (loopB state) = conv_to_rdg state"
proof(induction rule: loopB_induct[OF assms(1)])
  case (1 state)
  note IH = this
  show ?case
  proof(cases rule: loopB_cases[of state])
    case 1
    then show ?thesis 
      apply(subst loopB_simps(2)[OF IH(1) 1])
      using loopB_cont_upd_changes[of state] by simp
  next
    case 2
    then show ?thesis
      apply(subst loopB_simps(1)[OF IH(1) 2])
      using loopB_succ_upd_changes[of state] by simp
  next
    case 3
    then show ?thesis 
      using loopB_simps(5)[OF IH(1) 3] IH loopB_call1_upd_changes 
      by auto
  next
    case 4
    then show ?thesis 
      using loopB_simps(6)[OF IH(1) 4] IH loopB_call2_upd_changes 
      by auto
  next
    case 5
    then show ?thesis 
      apply(subst loopB_simps(3)[OF IH(1) 5])
      using loopB_fail_upd_changes[of state] by simp
  next
    case 6
    then show ?thesis
      apply(subst loopB_simps(4)[OF IH(1) 6])
      using loopB_fail_upd_changes[of state] by simp
  qed
qed

lemma loopB_changes_actives: 
  assumes "loopB_dom state"
  shows "actives (loopB state) = actives state"
proof(induction rule: loopB_induct[OF assms(1)])
  case (1 state)
  note IH = this
  show ?case
  proof(cases rule: loopB_cases[of state])
    case 1
    then show ?thesis 
      apply(subst loopB_simps(2)[OF IH(1) 1])
      using loopB_cont_upd_changes[of state] by simp
  next
    case 2
    then show ?thesis
      apply(subst loopB_simps(1)[OF IH(1) 2])
      using loopB_succ_upd_changes[of state] by simp
  next
    case 3
    then show ?thesis 
      using loopB_simps(5)[OF IH(1) 3] IH loopB_call1_upd_changes 
      by auto
  next
    case 4
    then show ?thesis 
      using loopB_simps(6)[OF IH(1) 4] IH loopB_call2_upd_changes 
      by auto
  next
    case 5
    then show ?thesis 
      apply(subst loopB_simps(3)[OF IH(1) 5])
      using loopB_fail_upd_changes[of state] by simp
  next
    case 6
    then show ?thesis
      apply(subst loopB_simps(4)[OF IH(1) 6])
      using loopB_fail_upd_changes[of state] by simp
  qed
qed

lemma loopB_changes_current_\<gamma>: 
  assumes "loopB_dom state"
  shows "current_\<gamma> (loopB state) = current_\<gamma> state"
proof(induction rule: loopB_induct[OF assms(1)])
  case (1 state)
  note IH = this
  show ?case
  proof(cases rule: loopB_cases[of state])
    case 1
    then show ?thesis 
      apply(subst loopB_simps(2)[OF IH(1) 1])
      using loopB_cont_upd_changes[of state] by simp
  next
    case 2
    then show ?thesis
      apply(subst loopB_simps(1)[OF IH(1) 2])
      using loopB_succ_upd_changes[of state] by simp
  next
    case 3
    then show ?thesis 
      using loopB_simps(5)[OF IH(1) 3] IH loopB_call1_upd_changes 
      by auto
  next
    case 4
    then show ?thesis 
      using loopB_simps(6)[OF IH(1) 4] IH loopB_call2_upd_changes 
      by auto
  next
    case 5
    then show ?thesis 
      apply(subst loopB_simps(3)[OF IH(1) 5])
      using loopB_fail_upd_changes[of state] by simp
  next
    case 6
    then show ?thesis
      apply(subst loopB_simps(4)[OF IH(1) 6])
      using loopB_fail_upd_changes[of state] by simp
  qed
qed

lemma loopB_changes_representative: 
  assumes "loopB_dom state"
  shows "representative (loopB state) = representative state"
proof(induction rule: loopB_induct[OF assms(1)])
  case (1 state)
  note IH = this
  show ?case
  proof(cases rule: loopB_cases[of state])
    case 1
    then show ?thesis 
      apply(subst loopB_simps(2)[OF IH(1) 1])
      using loopB_cont_upd_changes[of state] by simp
  next
    case 2
    then show ?thesis
      apply(subst loopB_simps(1)[OF IH(1) 2])
      using loopB_succ_upd_changes[of state] by simp
  next
    case 3
    then show ?thesis 
      using loopB_simps(5)[OF IH(1) 3] IH loopB_call1_upd_changes 
      by auto
  next
    case 4
    then show ?thesis 
      using loopB_simps(6)[OF IH(1) 4] IH loopB_call2_upd_changes 
      by auto
  next
    case 5
    then show ?thesis 
      apply(subst loopB_simps(3)[OF IH(1) 5])
      using loopB_fail_upd_changes[of state] by simp
  next
    case 6
    then show ?thesis
      apply(subst loopB_simps(4)[OF IH(1) 6])
      using loopB_fail_upd_changes[of state] by simp
  qed
qed

lemma loopB_changes_comp_card: 
  assumes "loopB_dom state"
  shows "comp_card (loopB state) = comp_card state"
proof(induction rule: loopB_induct[OF assms(1)])
  case (1 state)
  note IH = this
  show ?case
  proof(cases rule: loopB_cases[of state])
    case 1
    then show ?thesis 
      apply(subst loopB_simps(2)[OF IH(1) 1])
      using loopB_cont_upd_changes[of state] by simp
  next
    case 2
    then show ?thesis
      apply(subst loopB_simps(1)[OF IH(1) 2])
      using loopB_succ_upd_changes[of state] by simp
  next
    case 3
    then show ?thesis 
      using loopB_simps(5)[OF IH(1) 3] IH loopB_call1_upd_changes 
      by auto
  next
    case 4
    then show ?thesis 
      using loopB_simps(6)[OF IH(1) 4] IH loopB_call2_upd_changes 
      by auto
  next
    case 5
    then show ?thesis 
      apply(subst loopB_simps(3)[OF IH(1) 5])
      using loopB_fail_upd_changes[of state] by simp
  next
    case 6
    then show ?thesis
      apply(subst loopB_simps(4)[OF IH(1) 6])
      using loopB_fail_upd_changes[of state] by simp
  qed
qed

lemma loopB_changes_\<FF>_imp: 
  assumes "loopB_dom state"
  shows "\<FF>_imp (loopB state) = \<FF>_imp state"
proof(induction rule: loopB_induct[OF assms(1)])
  case (1 state)
  note IH = this
  show ?case
  proof(cases rule: loopB_cases[of state])
    case 1
    then show ?thesis 
      apply(subst loopB_simps(2)[OF IH(1) 1])
      using loopB_cont_upd_changes[of state] by simp
  next
    case 2
    then show ?thesis
      apply(subst loopB_simps(1)[OF IH(1) 2])
      using loopB_succ_upd_changes[of state] by simp
  next
    case 3
    then show ?thesis 
      using loopB_simps(5)[OF IH(1) 3] IH loopB_call1_upd_changes 
      by auto
  next
    case 4
    then show ?thesis 
      using loopB_simps(6)[OF IH(1) 4] IH loopB_call2_upd_changes 
      by auto
  next
    case 5
    then show ?thesis 
      apply(subst loopB_simps(3)[OF IH(1) 5])
      using loopB_fail_upd_changes[of state] by simp
  next
    case 6
    then show ?thesis
      apply(subst loopB_simps(4)[OF IH(1) 6])
      using loopB_fail_upd_changes[of state] by simp
  qed
qed

lemma loopB_changes_\<F>: 
  assumes "loopB_dom state"
  shows "\<F> (loopB state) = \<F> state"
proof(induction rule: loopB_induct[OF assms(1)])
  case (1 state)
  note IH = this
  show ?case
  proof(cases rule: loopB_cases[of state])
    case 1
    then show ?thesis 
      apply(subst loopB_simps(2)[OF IH(1) 1])+
      using loopB_cont_upd_changes[of state] by simp
  next
    case 2
    then show ?thesis
      apply(subst loopB_simps(1)[OF IH(1) 2])+
      using loopB_succ_upd_changes[of state] by simp
  next
    case 3
    then show ?thesis 
      using loopB_simps(5)[OF IH(1) 3] IH loopB_call1_upd_changes 
      by auto
  next
    case 4
    then show ?thesis 
      using loopB_simps(6)[OF IH(1) 4] IH loopB_call2_upd_changes 
      by auto
  next
    case 5
    then show ?thesis 
      apply(subst loopB_simps(3)[OF IH(1) 5])+
      using loopB_fail_upd_changes[of state] by simp
  next
    case 6
    then show ?thesis
      apply(subst loopB_simps(4)[OF IH(1) 6])+
      using loopB_fail_upd_changes[of state] by simp
  qed
qed

lemma loopB_changes_not_blocked: 
  assumes "loopB_dom state"
  shows "not_blocked (loopB state) = not_blocked state"
proof(induction rule: loopB_induct[OF assms(1)])
  case (1 state)
  note IH = this
  show ?case
  proof(cases rule: loopB_cases[of state])
    case 1
    then show ?thesis 
      apply(subst loopB_simps(2)[OF IH(1) 1])+
      using loopB_cont_upd_changes[of state] by simp
  next
    case 2
    then show ?thesis
      apply(subst loopB_simps(1)[OF IH(1) 2])+
      using loopB_succ_upd_changes[of state] by simp
  next
    case 3
    then show ?thesis 
      using loopB_simps(5)[OF IH(1) 3] IH loopB_call1_upd_changes 
      by auto
  next
    case 4
    then show ?thesis 
      using loopB_simps(6)[OF IH(1) 4] IH loopB_call2_upd_changes 
      by auto
  next
    case 5
    then show ?thesis 
      apply(subst loopB_simps(3)[OF IH(1) 5])+
      using loopB_fail_upd_changes[of state] by simp
  next
    case 6
    then show ?thesis
      apply(subst loopB_simps(4)[OF IH(1) 6])+
      using loopB_fail_upd_changes[of state] by simp
  qed
qed

lemma loopB_call1_cond_Phi_decr:
  assumes "loopB_call1_cond state" "invar_gamma state"
  shows "\<Phi> (loopB_call1_upd state) \<le> \<Phi> state - 1"
proof(rule loopB_call1_condE[OF assms(1)], goal_cases)
  case (1 f b \<gamma> s t P f' b' state')
  hence "state' = loopB_call1_upd state" 
    unfolding loopB_call1_upd_def  Let_def by fast
  have gamma_0: "\<gamma> > 0" using assms unfolding 1 invar_gamma_def by simp
  have sP: "(1 - \<epsilon>) * \<gamma> < b s"  "s \<in> \<V>" unfolding 1(6)
    using get_source_axioms 1  assms(1) by blast+
  have tP: "b t < - \<epsilon> * \<gamma>" "resreach f s t" "t \<in> \<V>" 
    using 1 get_target_for_source_axioms  assms(1,2) by blast+
  have s_neq_t:"s \<noteq> t" using sP tP gamma_0
    by (smt (verit, best) mult_less_cancel_right_disj)
  have bs_decr:"\<lceil> \<bar> b s - \<gamma>\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> \<le> \<lceil> \<bar> b s\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> - 1"
  proof(cases "b s \<ge> \<gamma>")
    case True
    hence "\<lceil> \<bar> b s - \<gamma>\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> = \<lceil> (b s - \<gamma>) / \<gamma> - (1 - \<epsilon>)\<rceil>" by simp
    also have "... = \<lceil> (b s ) / \<gamma> - (1 - \<epsilon>) - 1\<rceil>" using gamma_0
      by (smt (verit) diff_divide_distrib divide_self_if)
    also have "... = \<lceil> b s / \<gamma> - (1 - \<epsilon>)\<rceil> - 1" 
      using ceiling_diff_one[of "b s / \<gamma> - (1 - \<epsilon>)"] by simp
    also have "... = \<lceil> \<bar>b s \<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> - 1"
      apply(subst abs_of_nonneg)
      using sP gamma_0 \<epsilon>_axiom 
      using True apply linarith 
      by auto
    finally show ?thesis by simp 
  next
    case False
    have "\<lceil>\<bar>b s - \<gamma>\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> = \<lceil> (\<gamma> - b s) / \<gamma> - (1 - \<epsilon>)\<rceil>"
      using False by simp
    also have "... \<le> \<lceil> \<epsilon> - (1 - \<epsilon>)\<rceil>" 
      apply(rule ceiling_mono, simp, subst pos_divide_le_eq[OF gamma_0])
      using False sP(1) by argo
    also have "... = 0" using \<epsilon>_axiom by linarith
    also have "... \<le> 1 -  1" by simp
    also have "... \<le> \<lceil>b s / \<gamma> - (1 - \<epsilon>)\<rceil> -1"
      using sP(1) gamma_0 
      by (simp add: pos_less_divide_eq)
    also have "... = \<lceil>\<bar> b s \<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> - 1" 
      apply(simp, rule cong[of ceiling], simp)
      using sP gamma_0 \<epsilon>_axiom 
      by (smt (verit) \<open>\<lceil>\<epsilon> - (1 - \<epsilon>)\<rceil> = 0\<close> mult_less_0_iff zero_less_ceiling)
    finally show ?thesis by simp
  qed
 have bt_decr:"\<lceil> \<bar> b t + \<gamma>\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> \<le> \<lceil> \<bar> b t\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil>"
  proof(cases "b t \<le> - \<gamma>")
    case True
    hence "\<lceil> \<bar> b t + \<gamma>\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> = \<lceil> -(b t + \<gamma>) / \<gamma> - (1 - \<epsilon>)\<rceil>" by simp
    also have "... = \<lceil> - (b t ) / \<gamma> - (1 - \<epsilon>) - 1\<rceil>" using gamma_0
      by (simp add: diff_divide_distrib)
    also have "... = \<lceil> ( - b t) / \<gamma> - (1 - \<epsilon>)\<rceil> - 1" 
      using ceiling_diff_one[of "(-b t) / \<gamma> - (1 - \<epsilon>)"] by simp
    also have "... = \<lceil> \<bar>b t \<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> - 1"
      apply(subst abs_of_neg)
      using sP gamma_0 \<epsilon>_axiom 
      using True apply linarith 
      by auto
    finally show ?thesis by simp 
  next
    case False
    have "\<lceil>\<bar>b t + \<gamma>\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> = \<lceil> (\<gamma> + b t) / \<gamma> - (1 - \<epsilon>)\<rceil>"
      using False 
      by (auto intro: cong[of ceiling])
    also have "... \<le> \<lceil> (1 - \<epsilon>) - (1 - \<epsilon>)\<rceil>" 
      apply(rule ceiling_mono, simp, subst pos_divide_le_eq[OF gamma_0])
      using False tP(1) by argo
    also have "... = 0" by simp
    also have "... \<le> \<lceil> - b t / \<gamma> - (1 - \<epsilon>)\<rceil>"
      using tP(1) gamma_0 \<epsilon>_axiom
      by (smt (verit, ccfv_SIG) mult_less_0_iff pos_less_divide_eq zero_le_ceiling)
    also have "... = \<lceil>\<bar> b t \<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> "
      apply(rule cong[of ceiling], simp)
      using tP gamma_0 \<epsilon>_axiom
      by (smt (verit, del_insts) mult_neg_pos)
    finally show ?thesis by simp
  qed
  have "\<Phi> (loopB_call1_upd state) = \<Phi> state'"
    by (simp add: \<open>state' = loopB_call1_upd state\<close>)
  also have "... = (\<Sum> v \<in>  \<V>. \<lceil> \<bar> b' v\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil>)"
    using 1  unfolding \<Phi>_def by simp
  also have "... = (\<Sum> v \<in>  \<V> - {s, t}. \<lceil> \<bar> b' v\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil>) + 
                   \<lceil> \<bar> b' s\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> + \<lceil> \<bar> b' t\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil>"
    apply(rule trans[OF comm_monoid_add_class.sum.subset_diff[of "\<V> - {s, t}" \<V>]])
    using \<V>_finite  Diff_Diff_Int[of \<V>] sP(2) tP(3) s_neq_t by auto
  also have "... = (\<Sum> v \<in>  \<V> - {s, t}. \<lceil> \<bar> b v\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil>) + 
                   \<lceil> \<bar> b s - \<gamma>\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> + \<lceil> \<bar> b t + \<gamma>\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil>"
    unfolding 1(11) 
    using s_neq_t by simp
  also have "...  \<le> (\<Sum> v \<in>  \<V> - {s, t}. \<lceil> \<bar> b v\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil>) + 
                   \<lceil> \<bar> b s \<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> + \<lceil> \<bar> b t \<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> -1 "
    using bt_decr bs_decr by simp
  also have "... =  (\<Sum> v \<in>  \<V>. \<lceil> \<bar> b v\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil>) - 1" apply simp
    apply(rule trans[OF _ sym[OF comm_monoid_add_class.sum.subset_diff[of "\<V> - {s, t}" \<V>]]])
    using \<V>_finite  Diff_Diff_Int[of \<V>] sP(2) tP(3) s_neq_t by auto
  also have "... = \<Phi> state - 1"
    unfolding 1 \<Phi>_def by simp
   finally show ?case by simp
qed
  
lemma loopB_call2_cond_Phi_decr:
  assumes "loopB_call2_cond state" "invar_gamma state"
  shows "\<Phi> (loopB_call2_upd state) \<le> \<Phi> state - 1"
proof(rule loopB_call2_condE[OF assms(1)], goal_cases)
  case (1 f b \<gamma> t s P f' b' state')
  hence "state' = loopB_call2_upd state" 
    unfolding loopB_call2_upd_def  Let_def by fast
  have gamma_0: "\<gamma> > 0" using assms unfolding 1 invar_gamma_def by simp
  have sP: "\<epsilon> * \<gamma> < b s" "resreach f s t"  "s \<in> \<V>" 
    using get_source_for_target_axioms[OF 1(2) 1(3) 1(1)  1(7) 1(9) assms(1,2)]
    by auto
  have tP: "b t < - (1-\<epsilon>) * \<gamma>"  "t \<in> \<V>" 
    using 1 get_target_axioms assms(1) by blast+
  have s_neq_t:"s \<noteq> t" using sP tP gamma_0
    by (smt (verit, best) mult_less_cancel_right_disj)
  have bt_decr:"\<lceil> \<bar> b t + \<gamma>\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> \<le> \<lceil> \<bar> b t\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> - 1"
  proof(cases "b t \<le> - \<gamma>")
    case True
    hence "\<lceil> \<bar> b t + \<gamma>\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> = \<lceil> -(b t + \<gamma>) / \<gamma> - (1 - \<epsilon>)\<rceil>" by simp
    also have "... = \<lceil> (- b t ) / \<gamma> - (1 - \<epsilon>) - 1\<rceil>" using gamma_0
      by (simp add: diff_divide_distrib)
    also have "... = \<lceil> (- b t) / \<gamma> - (1 - \<epsilon>)\<rceil> - 1" 
      using ceiling_diff_one[of "(- b t) / \<gamma> - (1 - \<epsilon>)"] by simp
    also have "... = \<lceil> \<bar>b t \<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> - 1"
      apply(subst abs_of_neg)
      using sP gamma_0 \<epsilon>_axiom 
      using True apply linarith 
      by auto
    finally show ?thesis by simp 
  next
    case False
    have "\<lceil>\<bar>b t + \<gamma>\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> = \<lceil> (\<gamma> + b t) / \<gamma> - (1 - \<epsilon>)\<rceil>"
      using False 
      by (smt (verit, best))
    also have "... \<le> \<lceil> \<epsilon> - (1 - \<epsilon>)\<rceil>" 
      apply(rule ceiling_mono, simp, subst pos_divide_le_eq[OF gamma_0])
      using False tP(1) by argo
    also have "... = 0" using \<epsilon>_axiom by linarith
    also have "... \<le> 1 -  1" by simp
    also have "... \<le> \<lceil> (- b t) / \<gamma> - (1 - \<epsilon>)\<rceil> -1"
      using tP(1) gamma_0 
      by (smt (verit) mult_minus_left one_le_ceiling pos_less_divide_eq)
    also have "... = \<lceil>\<bar> b t \<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> - 1" 
      apply(simp, rule cong[of ceiling], simp)
      using tP gamma_0 \<epsilon>_axiom 
      by (smt (verit) "1"(5) divide_minus_left mult_less_cancel_right_disj mult_minus_left)
    finally show ?thesis by simp
  qed
 have bs_decr:"\<lceil> \<bar> b s - \<gamma>\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> \<le> \<lceil> \<bar> b s\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil>"
  proof(cases "b s \<ge> \<gamma>")
    case True
    hence "\<lceil> \<bar> b s - \<gamma>\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> = \<lceil> (b s - \<gamma>) / \<gamma> - (1 - \<epsilon>)\<rceil>" by simp
    also have "... = \<lceil> (b s ) / \<gamma> - (1 - \<epsilon>) - 1\<rceil>" using gamma_0
      by (simp add: diff_divide_distrib)
    also have "... = \<lceil> (b s) / \<gamma> - (1 - \<epsilon>)\<rceil> - 1" 
      using ceiling_diff_one[of "(b s) / \<gamma> - (1 - \<epsilon>)"] by simp
    also have "... = \<lceil> \<bar>b s \<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> - 1"
      apply(subst abs_of_nonneg)
      using sP gamma_0 \<epsilon>_axiom 
      using True apply linarith 
      by auto
    finally show ?thesis by simp 
  next
    case False
    have "\<lceil>\<bar>b s - \<gamma>\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> = \<lceil> ( \<gamma> - b s ) / \<gamma> - (1 - \<epsilon>)\<rceil>"
      using False 
      by (auto intro: cong[of ceiling])
    also have "... \<le> \<lceil> (1 - \<epsilon>) - (1 - \<epsilon>)\<rceil>" 
      apply(rule ceiling_mono, simp, subst pos_divide_le_eq[OF gamma_0])
      using False sP(1) by argo
    also have "... = 0" by simp
    also have "... \<le> \<lceil> b s / \<gamma> - (1 - \<epsilon>)\<rceil>"
      using sP(1) gamma_0 \<epsilon>_axiom
      by (smt (verit, ccfv_SIG) mult_less_0_iff pos_less_divide_eq zero_le_ceiling)
    also have "... = \<lceil>\<bar> b s \<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> "
      apply(rule cong[of ceiling], simp)
      using sP gamma_0 \<epsilon>_axiom 
      by (smt (verit) mult_less_0_iff)
    finally show ?thesis by simp
  qed
  have "\<Phi> (loopB_call2_upd state) = \<Phi> state'"
    by (simp add: \<open>state' = loopB_call2_upd state\<close>)
  also have "... = (\<Sum> v \<in>  \<V>. \<lceil> \<bar> b' v\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil>)"
    using 1  unfolding \<Phi>_def by simp
  also have "... = (\<Sum> v \<in>  \<V> - {s, t}. \<lceil> \<bar> b' v\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil>) + 
                   \<lceil> \<bar> b' s\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> + \<lceil> \<bar> b' t\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil>"
    apply(rule trans[OF comm_monoid_add_class.sum.subset_diff[of "\<V> - {s, t}" \<V>]])
    using \<V>_finite  Diff_Diff_Int[of \<V>] tP(2) sP(3) s_neq_t by auto
  also have "... = (\<Sum> v \<in>  \<V> - {s, t}. \<lceil> \<bar> b v\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil>) + 
                   \<lceil> \<bar> b s - \<gamma>\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> + \<lceil> \<bar> b t + \<gamma>\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil>"
    unfolding 1(12) 
    using s_neq_t by simp
  also have "...  \<le> (\<Sum> v \<in>  \<V> - {s, t}. \<lceil> \<bar> b v\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil>) + 
                   \<lceil> \<bar> b s \<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> + \<lceil> \<bar> b t \<bar> / \<gamma> - (1 - \<epsilon>)\<rceil> -1 "
    using bt_decr bs_decr by simp
  also have "... =  (\<Sum> v \<in>  \<V>. \<lceil> \<bar> b v\<bar> / \<gamma> - (1 - \<epsilon>)\<rceil>) - 1" apply simp
    apply(rule trans[OF _ sym[OF comm_monoid_add_class.sum.subset_diff[of "\<V> - {s, t}" \<V>]]])
    using \<V>_finite  Diff_Diff_Int[of \<V>] sP(3) tP(2) s_neq_t by auto
  also have "... = \<Phi> state - 1"
    unfolding 1 \<Phi>_def by simp
   finally show ?case by simp
 qed

lemma loopB_succ_upd_Phi_pres:
  shows "\<Phi> (loopB_succ_upd state) = \<Phi> state"
  unfolding \<Phi>_def loopB_succ_upd_def Let_def by simp

lemma loopB_cont_upd_Phi_pres:
  shows "\<Phi> (loopB_cont_upd state) = \<Phi> state"
  unfolding \<Phi>_def loopB_cont_upd_def Let_def by simp

lemma loopB_fail_upd_Phi_pres:
  shows "\<Phi> (loopB_fail_upd state) = \<Phi> state"
  unfolding \<Phi>_def loopB_fail_upd_def Let_def by simp

lemma loopB_cont_upd_flow_pres: "current_flow (loopB_cont_upd state) = current_flow state"
  unfolding loopB_cont_upd_def by simp

lemma loopB_succ_upd_flow_pres: "current_flow (loopB_succ_upd state) = current_flow state"
  unfolding loopB_succ_upd_def by simp

lemma loopB_fail_upd_flow_pres: "current_flow (loopB_fail_upd state) = current_flow state"
  unfolding loopB_fail_upd_def by simp

lemma loopB_dom_succ: "loopB_succ_cond state \<Longrightarrow> loopB_dom state"
  by(auto elim: loopB_succ_condE intro: loopB.domintros)

lemma loopB_dom_cont: "loopB_cont_cond state \<Longrightarrow> loopB_dom state"
  by(auto elim!: loopB_cont_condE intro: loopB.domintros)

lemma loopB_dom_fail1: "loopB_fail1_cond state \<Longrightarrow> loopB_dom state"
  by(auto elim!: loopB_fail1_condE intro: loopB.domintros)

lemma loopB_dom_fail2: "loopB_fail2_cond state \<Longrightarrow> loopB_dom state"
  by(auto elim!: loopB_fail2_condE intro: loopB.domintros)

lemma loopB_dom_call1: "loopB_call1_cond state \<Longrightarrow> (loopB_dom (loopB_call1_upd state))
                          \<Longrightarrow> loopB_dom state"
  apply(rule loopB_call1_condE, simp)
  apply(rule loopB.domintros) 
  unfolding loopB_call1_upd_def Let_def
  subgoal for f b \<gamma> s t P f' b' state' v sa ta 
    apply(rule back_subst[of loopB_dom])
    apply simp 
    apply(rule Algo_state.equality)
    by auto
  by simp

lemma loopB_dom_call2: "loopB_call2_cond state \<Longrightarrow> (loopB_dom (loopB_call2_upd state))
                          \<Longrightarrow> loopB_dom state"
  apply(rule loopB_call2_condE, simp)
  apply(rule loopB.domintros) 
  unfolding loopB_call2_upd_def Let_def
  apply simp
  subgoal for f b \<gamma> s t P f' b' state' v sa ta 
    apply(rule back_subst[of loopB_dom])
    apply simp 
    apply(rule Algo_state.equality)
    by auto
  done

lemma loopB_term:
  assumes "invar_gamma state"
          "\<phi> = nat (\<Phi> state)"
  shows "loopB_dom state"
  using assms 
proof(induction \<phi> arbitrary: state rule: less_induct)
  case (less \<phi>)
  then show ?case
  proof(cases rule: loopB_cases[of state])
    case 3
    show ?thesis 
      using loopB_call1_cond_Phi_decr[of state] 3 Phi_nonneg invar_gamma_pres_call1 less 
      by (force intro: loopB_dom_call1 less(1)[of "nat (\<Phi> (loopB_call1_upd state))"])
  next
    case 4
    show ?thesis 
      using loopB_call2_cond_Phi_decr[of state] 4 Phi_nonneg invar_gamma_pres_call2 less 
      by (force intro: loopB_dom_call2 less(1)[of "nat (\<Phi> (loopB_call2_upd state))"])
  qed (simp add: loopB_dom_succ 
                 loopB_dom_cont 
                 loopB_dom_fail1
                 loopB_dom_fail2)+
qed

lemmas loopB_termination = loopB_term[OF _ refl]

lemma orlins_entry_after_loopB:
  assumes "loopB_dom state"
          "loopB state = state'"
          "invar_gamma state"
          "return state' = notyetterm"
   shows "orlins_entry (loopB state)"
  using assms(2-4) unfolding invar_gamma_def
  apply(induction rule: loopB_induct[OF assms(1)])
  subgoal for state
    apply(cases rule: loopB_cases[of state])
    subgoal
      apply(rule loopB_cont_condE[of state], simp)
      subgoal for f b \<gamma>
        apply(subst loopB_simps(2), simp, simp)
        unfolding loopB_cont_upd_def orlins_entry_def apply simp
        by (smt (verit, ccfv_threshold) \<epsilon>_axiom(1) minus_mult_minus mult_le_cancel_right1 mult_minus_right)
      done
    using loopB_simps(1)[of state] loopB_simps(3)[of state] loopB_simps(4)[of state]
          loopB_simps(5)[of state] invar_gamma_pres_call1[of state, simplified invar_gamma_def]
          loopB_simps(6)[of state] invar_gamma_pres_call2[of state, simplified invar_gamma_def]            
    unfolding loopB_fail_upd_def loopB_succ_upd_def Let_def by auto
  done

lemma remaining_balance_after_loopB:
  assumes "loopB_dom state"
          "loopB state = state'"
          "return state' = notyetterm"
   shows "invar_non_zero_b (loopB state)"
  using assms(2-) unfolding invar_gamma_def invar_non_zero_b_def
  apply(induction rule: loopB_induct[OF assms(1)])
  subgoal for state
    apply(cases rule: loopB_cases[of state])
    subgoal
      apply(rule loopB_cont_condE[of state], simp)
      subgoal for f b \<gamma>
        apply(subst loopB_simps(2), simp, simp)
        unfolding loopB_cont_upd_def orlins_entry_def by simp
      done
    using loopB_simps(1)[of state] loopB_simps(3)[of state] loopB_simps(4)[of state]
          loopB_simps(5)[of state] invar_gamma_pres_call1[of state, simplified invar_gamma_def]
          loopB_simps(6)[of state] invar_gamma_pres_call2[of state, simplified invar_gamma_def]            
    unfolding loopB_fail_upd_def loopB_succ_upd_def Let_def by auto
  done

lemma loopB_call1_cond_flow_Phi:
  assumes "loopB_call1_cond state"
          "state' = loopB_call1_upd state"
          "invar_gamma state" "(\<forall> e \<in> \<F> state . current_flow state e > 0)" "aux_invar state"
     shows"current_flow  state' e \<ge> current_flow state e - (\<Phi> state - \<Phi> state')*current_\<gamma> state'"
  unfolding assms(2)
proof(rule loopB_call1_condE[OF assms(1)], goal_cases)
  case (1 f b \<gamma> s t P f' b' state')
  have gamma_0:"\<gamma> > 0" using assms unfolding 1 invar_gamma_def by simp
  have s_not_t: " s \<noteq> t "
    using get_target_for_source_axioms[OF 1(2,3,1,6,7) assms(1,3)]
          get_source_axioms[OF 1(2,3,6)] assms(1) \<epsilon>_axiom gamma_0
    by (smt (verit, ccfv_SIG) mult_less_cancel_right_disj)
  have s_V: " s \<in> \<V>"
    using 1 get_source_axioms assms(1) by blast
  have t_V: "t \<in> \<V>"
    using get_target_for_source_axioms[OF 1(2,3,1,6,7)] assms(1,3) by simp
  have resreach: "resreach f s t"
    using get_target_for_source_axioms[OF 1(2,3,1,6,7)] assms(1,3) by simp
  have "f e- \<gamma> \<le> f' e" 
    using invar_gamma_def  distinct_path_augment[of P \<gamma> f e]
          get_source_target_path_a_axioms(4) s_V t_V s_not_t  assms(3-5) resreach 1
          assms(1)
    by (fastforce intro!: get_source_target_path_a_condI)
  moreover have "\<Phi> state - \<Phi> (loopB_call1_upd state) \<ge> 1"
    using loopB_call1_cond_Phi_decr[of state, OF assms(1) assms(3)] by simp
  ultimately have "f' e \<ge> f e - \<gamma> * (\<Phi> state - \<Phi> (loopB_call1_upd state))"
    using gamma_0 
    by (smt (verit) mult_less_cancel_left2 of_int_less_1_iff)
  moreover have "current_\<gamma> (loopB_call1_upd state) = \<gamma>"
    by (simp add: "1"(3) loopB_call1_upd_changes(4))
  moreover have "current_flow (loopB_call1_upd state) = f'"
    unfolding 1 loopB_call1_upd_def Let_def by simp
  ultimately show ?case unfolding 1(1) 1(3) 
    by (simp add: mult.commute) 
qed

lemma loopB_call2_cond_flow_Phi:
  assumes "loopB_call2_cond state"
          "state' = loopB_call2_upd state"
          "invar_gamma state" "(\<forall> e \<in> \<F> state . current_flow state e > 0)" "aux_invar state"
     shows"current_flow  state' e \<ge> current_flow state e - (\<Phi> state - \<Phi> state')*current_\<gamma> state'"
  unfolding assms(2)
proof(rule loopB_call2_condE[OF assms(1)], goal_cases)
  case (1 f b \<gamma> s t P f' b' state')
  have gamma_0:"\<gamma> > 0" using assms unfolding 1 invar_gamma_def by simp
  have s_not_t: " t \<noteq> s "
    apply(rule bexE[OF 1(6)], rule bexE[OF 1(8)])
    subgoal for ss tt     
      using get_source_for_target_axioms[OF 1(2,3,1,7,9)]
            get_target_axioms[OF 1(2,3,7)] \<epsilon>_axiom(1) gamma_0 assms(1,3)
      by (smt (verit, ccfv_SIG) "1"(5) zero_less_mult_iff)
    done
  have s_V: "s \<in> \<V>"
    using get_target_axioms[OF 1(2,3,7) ] assms(1)
    by auto
  have t_V: "t \<in> \<V>"
    using get_source_for_target_axioms[OF 1(2,3,1,7,9)] assms(1,3)
    by auto
  have resreach: "resreach f t s"
    using get_source_for_target_axioms[OF 1(2,3,1,7,9)] assms(1,3)
    by auto
  have "f e- \<gamma> \<le> f' e"
     using  assms(3,4,5) invar_gamma_def  distinct_path_augment[of P \<gamma> f e] 1
            get_source_target_path_b_axioms(4) s_not_t t_V s_V resreach assms(1)
    by (fastforce intro!: get_source_target_path_b_condI)
  moreover have "\<Phi> state - \<Phi> (loopB_call2_upd state) \<ge> 1"
    using loopB_call2_cond_Phi_decr[of state, OF assms(1) assms(3)] by simp
  ultimately have "f' e \<ge> f e - \<gamma> * (\<Phi> state - \<Phi> (loopB_call2_upd state))"
    using gamma_0 
    by (smt (verit) mult_less_cancel_left2 of_int_less_1_iff)
  moreover have "current_\<gamma> (loopB_call2_upd state) = \<gamma>"
    by (simp add: "1"(3) loopB_call2_upd_changes(4))
  moreover have "current_flow (loopB_call2_upd state) = f'"
    unfolding 1 loopB_call2_upd_def Let_def by simp
  ultimately show ?case unfolding 1(1) 1(3) 
    by (simp add: mult.commute) 
qed


theorem loopB_flow_Phi:
  assumes "loopB_dom state"
          "state' = loopB state"
          "invar_gamma state"
          "\<And> e. e \<in> \<F> state \<Longrightarrow> current_flow state e \<ge>
                                 6*N*current_\<gamma> state - (2*N  - \<Phi> state)*current_\<gamma> state"
          "aux_invar state"
     shows"current_flow  state' e \<ge> current_flow state e - (\<Phi> state - \<Phi> state')*current_\<gamma> state'"
  unfolding assms(2)
  using assms(3-5)
proof(induction rule: loopB_induct[OF assms(1)])
  case (1 state)
  note IH = this
  have gamma_0: "current_\<gamma> state > 0" using IH unfolding invar_gamma_def by auto
  have gamma_flow:"e \<in> \<F> state \<Longrightarrow> current_\<gamma> state \<le> current_flow state e" for e
    apply(rule order.trans[of _ "4*N*current_\<gamma> state"])
    using  gamma_0  N_gtr_0 apply simp
    using  gamma_0 Phi_nonneg[of state, OF IH(4)] N_gtr_0 
    by(intro order.trans[OF _ IH(5)[of e]])(auto simp add: mult.commute right_diff_distrib)
  have flowF: "\<forall>e\<in>\<F> state. 0 < current_flow state e "
    using gamma_0 gamma_flow by force
  show ?case 
  proof(cases rule: loopB_cases[of state])
    case 3
    have invar_gamma_ud:"invar_gamma (loopB_call1_upd state)" 
      using invar_gamma_pres_call1 IH by simp
    hence gamma_0:"current_\<gamma> (local.loopB (loopB_call1_upd state)) > 0"
      using  invar_gamma_def loopB_changes_current_\<gamma> loopB_termination 
      by auto
    have gamma_same: "current_\<gamma> (local.loopB (loopB_call1_upd state)) = 
                      current_\<gamma> (loopB_call1_upd state)" 
      by (simp add: invar_gamma_ud loopB_changes_current_\<gamma> loopB_termination)  
    have invar_gamma: "invar_gamma (loopB_call1_upd state)"
      using IH
      unfolding loopB_call1_upd_def Let_def invar_gamma_def by simp
    have gamma_Phi_flow: "e \<in> \<F> (loopB_call1_upd state) \<Longrightarrow>
         real (6 * N) * current_\<gamma> (loopB_call1_upd state) -
         real_of_int (int (2 * N) - \<Phi> (loopB_call1_upd state)) * current_\<gamma> (loopB_call1_upd state)
         \<le> current_flow (loopB_call1_upd state) e" for e
         apply(rule order.trans) defer
         apply(rule loopB_call1_cond_flow_Phi[OF 3], simp, simp add: IH)
         using IH(4)  IH(5)[of e] loopB_call1_upd_changes(6)[of state] 
               loopB_call1_upd_changes(4)[of state]  loopB_call1_cond_Phi_decr[OF 3 IH(4)] IH(6)
         by (auto  simp add: left_diff_distrib' flowF)
    show ?thesis
      using  loopB_simps(5)[of state] 3 invar_gamma_ud IH 
             loopB_call1_cond_flow_Phi[of state "loopB_call1_upd state" e] gamma_Phi_flow flowF
             invar_aux_pres_call1
      by (auto simp add: gamma_same left_diff_distrib)
  next
    case 4
    have invar_gamma_ud:"invar_gamma (loopB_call2_upd state)" 
      using invar_gamma_pres_call2 IH by simp
    hence gamma_0:"current_\<gamma> (local.loopB (loopB_call2_upd state)) > 0"
      using  invar_gamma_def loopB_changes_current_\<gamma> loopB_termination 
      by auto
    have gamma_same: "current_\<gamma> (local.loopB (loopB_call2_upd state)) = 
                      current_\<gamma> (loopB_call2_upd state)" 
      by (simp add: invar_gamma_ud loopB_changes_current_\<gamma> loopB_termination)      
    have invar_gamma: "invar_gamma (loopB_call2_upd state)"
         using IH
         unfolding loopB_call2_upd_def Let_def invar_gamma_def by simp
    have gamma_Phi_flow: "e \<in> \<F> (loopB_call2_upd state) \<Longrightarrow>
         real (6 * N) * current_\<gamma> (loopB_call2_upd state) -
         real_of_int (int (2 * N) - \<Phi> (loopB_call2_upd state)) * current_\<gamma> (loopB_call2_upd state)
         \<le> current_flow (loopB_call2_upd state) e" for e
         apply(rule order.trans) defer
         apply(rule loopB_call2_cond_flow_Phi[OF 4], simp, simp add: IH)
         using IH(4)  IH(5)[of e] loopB_call2_upd_changes(6)[of state] 
               loopB_call2_upd_changes(4)[of state]  loopB_call2_cond_Phi_decr[OF 4 IH(4)] IH(6)
         by (auto intro:  simp add: left_diff_distrib' flowF)
    show ?thesis 
      using  loopB_simps(6)[of state] 4 invar_gamma_ud IH 
             loopB_call2_cond_flow_Phi[of state "loopB_call2_upd state" e] gamma_Phi_flow flowF
             invar_aux_pres_call2
      by (auto simp add: gamma_same left_diff_distrib)
  qed (auto simp add: loopB_simps IH
                      loopB_cont_upd_Phi_pres[of state] loopB_cont_upd_flow_pres[of state]
                      loopB_succ_upd_Phi_pres[of state] loopB_succ_upd_flow_pres[of state]
                      loopB_fail_upd_Phi_pres[of state] loopB_fail_upd_flow_pres[of state])
qed

lemma loopB_flow_Phi_final:
  assumes "loopB_dom state"
          "state' = loopB state"
          "invar_gamma state"
          "\<And> e. e \<in> \<F> state \<Longrightarrow> current_flow state e \<ge>
                                 6*N*current_\<gamma> state - (2*N  - \<Phi> state)*current_\<gamma> state"
          "aux_invar state"
     shows"current_flow  state' e \<ge> current_flow state e - \<Phi> state*current_\<gamma> state'"
  using loopB_flow_Phi[of state state' e] Phi_nonneg[of state] assms
  by (smt (verit, best) invar_gamma_def loopB_invar_gamma_pres Phi_nonneg loopB_axioms 
                     loopB_flow_Phi mult_less_cancel_right_disj of_int_le_iff)

lemma loopB_call1_invar_integral_pres:
  assumes "loopB_call1_cond state"
          "invar_integral state"
          "aux_invar state"
          "invar_gamma state"
          " \<forall>e\<in>\<F> state. 0 < current_flow state e"
    shows "invar_integral (loopB_call1_upd state)"
proof(rule loopB_call1_condE[OF assms(1)], goal_cases)
  case (1 f b \<gamma> s t P f' b' state')
  have gamma_0:"\<gamma> > 0" using assms unfolding 1 invar_gamma_def by simp
  have s_not_t: " s \<noteq> t "
    using get_target_for_source_axioms[OF 1(2,3,1,6,7)]
          get_source_axioms[OF 1(2,3,6)] \<epsilon>_axiom gamma_0 assms(1,4)
      by (smt (verit, ccfv_SIG) mult_less_cancel_right_disj)
  have s_V: "s \<in> \<V>"
    using 1 get_source_axioms assms(1) by blast
  have t_V: "t \<in> \<V>"
    using get_target_for_source_axioms[OF 1(2,3,1,6,7)] assms(1,4)
    by simp
   have resreach: "resreach f s t"
    using get_target_for_source_axioms[OF 1(2,3,1,6,7)] assms(1,4)
    by simp
  have distinctP: "distinct P" 
    using "1"(9)  get_source_target_path_a_axioms(4)[ OF
         get_source_target_path_a_condI[OF _ s_V t_V s_not_t _ _ _ 1(2,3,6,7)]] 
        resreach 1(1) assms by auto
  have gamma_same: "current_\<gamma> (loopB_call1_upd state) = current_\<gamma> state" 
    using loopB_call1_upd_changes(4) by auto
  show ?case  unfolding invar_integral_def
  proof
    fix e
    assume "e \<in> to_set (actives (loopB_call1_upd state))"
    moreover have "actives (loopB_call1_upd state) = 
                   actives state" 
      by (simp add: loopB_call1_upd_changes(3))
    ultimately have "e \<in> to_set (actives state)" by simp
    then obtain x where x_prop:" current_flow state e = real (x::nat) * \<gamma>"
      using assms(2) unfolding invar_integral_def 1 by auto
    have f': "f' = current_flow (loopB_call1_upd state)"
      unfolding 1 loopB_call1_upd_def Let_def by simp
    show "\<exists>x. current_flow (loopB_call1_upd state) e = real x * current_\<gamma> (loopB_call1_upd state)"
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
        hence rcap:"rcap f (B e) = 0"
          using x_prop 1 by simp        
        have "Rcap f (set P) \<le> 0"
          unfolding Rcap_def
          using asm(1) rcap 
          by (force intro!: Min.coboundedI)
        thus False 
          using get_source_target_path_a_axioms(1)[of state s t P, 
                         OF  get_source_target_path_a_condI[OF _ _ _ s_not_t]] 1
                get_target_for_source_axioms assms(5) get_source_axioms assms(1) assms(4)
          unfolding is_s_t_path_def augpath_def
          by (metis (no_types, lifting) assms(3) linorder_not_less)
      qed
      show ?thesis
        apply(cases rule: disjE[OF e_erev])
        subgoal 
          using e_rev_in_es_flow_change[of e P  f \<gamma>, OF _ _ distinctP] x_prop 
          unfolding 1(1) sym[OF f'] 1(10) gamma_same 1(3) 
          by (auto intro: exI[of _ "x+1"] simp add: distrib_left mult.commute)
        apply(cases rule: disjE[where P="F e \<notin> set P \<and> B e \<in> set P"], simp)
        subgoal 
          apply(rule exI[of _ "x-1"])
          using rev_e_in_es_flow_change[of e P  f \<gamma>, OF _ _ distinctP, simplified] 
                x_prop x_0 
          unfolding 1(1) sym[OF f'] 1(10) gamma_same 1(3) 
          by (metis Suc_eq_plus1_left Suc_pred' add_diff_cancel_right' diff_le_self left_diff_distrib 
             mult_cancel_right1 of_nat_1 of_nat_diff )
        subgoal
          using there_and_back_flow_not_change[of e P  f \<gamma>, OF _ _ distinctP, simplified] 
                x_prop 
          unfolding 1(1) sym[OF f'] 1(10) gamma_same 1(3)
          by auto
        done
    next
      case False
      thus ?thesis
         using e_not_in_es_flow_not_change[of P e f \<gamma>] x_prop 
         unfolding 1(1) sym[OF f'] 1(10) gamma_same 1(3) by auto
    qed
  qed
qed

lemma loopB_call2_invar_integral_pres:
  assumes "loopB_call2_cond state"
          "invar_integral state"
          "aux_invar state"
          "invar_gamma state"
          "\<forall>e\<in>\<F> state. 0 < current_flow state e"
    shows "invar_integral (loopB_call2_upd state)"
proof(rule loopB_call2_condE[OF assms(1)], goal_cases)
  case (1 f b \<gamma> s t P f' b' state')
  have gamma_0:"\<gamma> > 0" using assms unfolding 1 invar_gamma_def by simp
  have s_not_t: " t \<noteq> s "
    using get_source_for_target_axioms[OF 1(2,3,1,7,9)]
          get_target_axioms[OF 1(2,3,7)] \<epsilon>_axiom gamma_0 assms(1,4)
      by (smt (verit, ccfv_SIG) mult_less_cancel_right_disj)
 have s_V: "s \<in> \<V> "
      using get_target_axioms[OF 1(2,3,7)] assms(1) by simp
 have t_V: "t \<in> \<V> "
      using get_source_for_target_axioms[OF 1(2,3,1,7,9)] assms(1,4) by simp
 have resreach: "resreach f t s"
     using get_source_for_target_axioms[OF 1(2,3,1,7,9)] assms(1,4) by simp
  have distinctP: "distinct P" 
    using  get_source_target_path_b_axioms(4)  s_not_t t_V s_V assms(1,5,3,4) resreach 1 
    by (fastforce intro!: get_source_target_path_b_condI)
  have gamma_same: "current_\<gamma> (loopB_call2_upd state) = current_\<gamma> state" 
    using loopB_call2_upd_changes(4) by auto
  show ?case unfolding invar_integral_def
  proof
    fix e
    assume "e \<in> to_set (actives (loopB_call2_upd state))"
    moreover have "actives (loopB_call2_upd state) = 
                   actives state" 
      by (simp add: loopB_call2_upd_changes(3))
    ultimately have "e \<in> to_set (actives state)" by simp
    then obtain x where x_prop:" current_flow state e = real (x::nat) * \<gamma>"
      using assms(2) unfolding invar_integral_def 1 by auto
    have f': "f' = current_flow (loopB_call2_upd state)"
      unfolding 1 loopB_call2_upd_def Let_def by simp
    show "\<exists>x. current_flow (loopB_call2_upd state) e = real x * current_\<gamma> (loopB_call2_upd state)"
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
        hence rcap:"rcap f (B e) = 0"
          using x_prop 1 by auto         
        have "Rcap f (set P) \<le> 0"
          unfolding Rcap_def
          using asm(1) rcap 
          by (force intro!: Min.coboundedI)
        thus False
          using get_source_target_path_b_axioms(1)[of state t s P] s_not_t 1 
                assms(5) get_source_for_target_axioms[OF 1(2,3,1,7,9)]
                get_target_axioms[OF 1(2,3,7)] assms(3) linorder_not_le
          unfolding is_s_t_path_def augpath_def
          by (fastforce intro: get_source_target_path_b_condI assms(1,4))
       qed
      show ?thesis
        apply(cases rule: disjE[OF e_erev])
        subgoal 
          using e_rev_in_es_flow_change[of e P  f \<gamma>, OF _ _ distinctP] x_prop 
          unfolding 1(1) sym[OF f'] 1(11) gamma_same 1(3) 
          by (auto intro: exI[of _ "x+1"] simp add: distrib_left mult.commute)
        apply(cases rule: disjE[where P="F e \<notin> set P \<and> B e \<in> set P"], simp)
        subgoal 
          apply(rule exI[of _ "x-1"])
          using rev_e_in_es_flow_change[of e P  f \<gamma>, OF _ _ distinctP, simplified] 
                x_prop x_0 
          unfolding 1(1) sym[OF f'] 1(11) gamma_same 1(3) 
          by (metis Suc_eq_plus1_left Suc_pred' add_diff_cancel_right' diff_le_self left_diff_distrib 
             mult_cancel_right1 of_nat_1 of_nat_diff)
        subgoal
          using there_and_back_flow_not_change[of e P  f \<gamma>, OF _ _ distinctP, simplified] 
                x_prop 
          unfolding 1(1) sym[OF f'] 1(11) gamma_same 1(3)
          by auto
        done
    next
      case False
      thus ?thesis
         using e_not_in_es_flow_not_change[of P e f \<gamma>] x_prop 
         unfolding 1(1) sym[OF f'] 1(11) gamma_same 1(3) by auto
    qed
  qed
qed

lemma loopB_cont_invar_integral_pres:
  "invar_integral state \<Longrightarrow> invar_integral (loopB_cont_upd state)"
  unfolding loopB_cont_upd_def invar_integral_def by simp

lemma loopB_fail_invar_integral_pres:
  "invar_integral state \<Longrightarrow> invar_integral (loopB_fail_upd state)"
  unfolding loopB_fail_upd_def invar_integral_def by simp

lemma loopB_succ_invar_integral_pres:
  "invar_integral state \<Longrightarrow> invar_integral (loopB_succ_upd state)"
  unfolding loopB_succ_upd_def invar_integral_def by simp

theorem loopB_invar_integral_pres:
  assumes "loopB_dom state"
          "aux_invar state"
          "invar_integral state"
          "invar_gamma state"
          "\<And> e. e \<in> \<F> state \<Longrightarrow> current_flow state e \<ge>
                                 6*N*current_\<gamma> state - (2*N  - \<Phi> state)*current_\<gamma> state"
    shows "invar_integral (loopB state)"
  using assms(2-)
proof(induction rule: loopB_induct[OF assms(1)])
  case (1 state)
  note IH=this
  have gamma_0: "current_\<gamma> state > 0" using IH unfolding invar_gamma_def by auto
  have gamma_flow:"e \<in> \<F> state \<Longrightarrow> current_\<gamma> state \<le> current_flow state e" for e
    apply(rule order.trans[of _ "4*N*current_\<gamma> state"])
    using  gamma_0  N_gtr_0 apply simp  
    using  gamma_0 Phi_nonneg[of state, OF IH(6)] N_gtr_0
    by (intro order.trans[OF _ IH(7)[of e]])(auto simp add: mult.commute right_diff_distrib')
  have flowF: "\<forall>e\<in>\<F> state. 0 < current_flow state e "
    using gamma_0 gamma_flow by force
  then show ?case 
  proof(cases rule: loopB_cases[of state])
    case 3
    have invar_gamma: "invar_gamma (loopB_call1_upd state)"
      using IH
      unfolding loopB_call1_upd_def Let_def invar_gamma_def by simp
    have gamma_Phi_flow: "e \<in> \<F> (loopB_call1_upd state) \<Longrightarrow>
         real (6 * N) * current_\<gamma> (loopB_call1_upd state) -
         real_of_int (int (2 * N) - \<Phi> (loopB_call1_upd state)) * current_\<gamma> (loopB_call1_upd state)
         \<le> current_flow (loopB_call1_upd state) e" for e
         apply(rule order.trans) defer
         apply(rule loopB_call1_cond_flow_Phi[OF 3], simp, simp add: IH)
         using IH(4)  IH(7)[of e] loopB_call1_upd_changes(6)[of state] 
               loopB_call1_upd_changes(4)[of state]  loopB_call1_cond_Phi_decr[OF 3 IH(6)]
         by (auto  simp add: left_diff_distrib' flowF)
       show ?thesis 
         apply(subst loopB_simps(5))
         using 3 IH loopB_call1_cond_flow_Phi[OF 3, of "loopB_call1_upd state"] gamma_Phi_flow
         by (intro IH(2)[OF 3 _ _ invar_gamma]| 
             auto intro: IH(2)[OF 3 _ _ invar_gamma] loopB_call1_invar_integral_pres[of state, OF _ _ _ _ flowF]
             invar_aux_pres_call1)+
    next
      case 4
        have invar_gamma: "invar_gamma (loopB_call2_upd state)"
         using IH
         unfolding loopB_call2_upd_def Let_def invar_gamma_def by simp
          have gamma_Phi_flow: "e \<in> \<F> (loopB_call2_upd state) \<Longrightarrow>
         real (6 * N) * current_\<gamma> (loopB_call2_upd state) -
         real_of_int (int (2 * N) - \<Phi> (loopB_call2_upd state)) * current_\<gamma> (loopB_call2_upd state)
         \<le> current_flow (loopB_call2_upd state) e" for e
         apply(rule order.trans) defer
         apply(rule loopB_call2_cond_flow_Phi[OF 4], simp, simp add: IH)
         using IH(4)  IH(7)[of e] loopB_call2_upd_changes(6)[of state] 
               loopB_call2_upd_changes(4)[of state]  loopB_call2_cond_Phi_decr[OF 4 IH(6)]
         by (auto intro:  simp add: left_diff_distrib' flowF)
       show ?thesis 
         apply(subst loopB_simps(6))
         using 4 IH loopB_call2_cond_flow_Phi[OF 4, of "loopB_call2_upd state"] gamma_Phi_flow
         by (intro IH(3)[OF 4 _ _ invar_gamma]| 
             auto intro: IH(3)[OF 4  _ _ invar_gamma] loopB_call2_invar_integral_pres[of state, OF _ _ _ _ flowF]
             invar_aux_pres_call2)+
  qed (auto simp add: loopB_simps      IH      loopB_fail_invar_integral_pres
                      loopB_succ_invar_integral_pres loopB_cont_invar_integral_pres) 
qed

lemma outside_actives_and_F_no_change_succ:
  assumes "e \<notin> to_set (actives state)" "e \<notin> \<F> state"
  shows   "current_flow state e = current_flow (loopB_succ_upd state) e"
  unfolding loopB_succ_upd_def Let_def by simp

lemma outside_actives_and_F_no_change_cont:
  assumes "e \<notin> to_set (actives state)" "e \<notin> \<F> state"
  shows   "current_flow state e = current_flow (loopB_cont_upd state) e"
  unfolding loopB_cont_upd_def Let_def by simp

lemma outside_actives_and_F_no_change_fail:
  assumes "e \<notin> to_set (actives state)" "e \<notin> \<F> state"
  shows   "current_flow state e = current_flow (loopB_fail_upd state) e"
  unfolding loopB_fail_upd_def Let_def by simp
  
lemma outside_actives_and_F_no_change_call1:
  assumes "loopB_call1_cond state" "e \<notin> to_set (actives state)" "e \<notin> \<F> state"
          "invar_gamma state" "(\<forall> e \<in> \<F> state . current_flow state e > 0)" "aux_invar state"
  shows   "current_flow state e = current_flow (loopB_call1_upd state) e"
proof(rule loopB_call1_condE[OF assms(1)], goal_cases)
  case (1 f b \<gamma> s t P f' b' state')
  have gamma_0:"\<gamma> > 0" using assms unfolding 1 invar_gamma_def by simp
  have s_not_t: " s \<noteq> t "
    using get_target_for_source_axioms[OF 1(2) 1(3) 1(1)  1(6)1(7)]
          get_source_axioms[OF 1(2) 1(3)  1(6)] \<epsilon>_axiom gamma_0 assms(1,4)
      by (smt (verit, ccfv_SIG) mult_less_cancel_right_disj)
  have s_V: " s \<in> \<V> "
    using get_source_axioms 1 assms(1) by simp
  have t_V: " t \<in> \<V> "
    using get_target_for_source_axioms[OF 1(2) 1(3) 1(1) 1(6) 1(7)] assms(1,4) by simp
  have resreach: "resreach f s t "
    using get_target_for_source_axioms[OF 1(2) 1(3) 1(1) 1(6) 1(7)] assms(1,4) by simp
  have f': "f' = current_flow (loopB_call1_upd state)"
    unfolding 1 loopB_call1_upd_def Let_def by simp
  show ?case 
    using f' assms(2-3) get_source_target_path_a_axioms(3)[of state s t P]
          get_source_target_path_a_condI[OF _ s_V t_V s_not_t assms(6) assms(5)] assms(4)
          1 resreach assms(1)
    by (fastforce intro:  sym[OF e_not_in_es_flow_not_change])
qed
  
lemma outside_actives_and_F_no_change_call2:
  assumes "loopB_call2_cond state" "e \<notin> to_set (actives state)" "e \<notin> \<F> state"
          "invar_gamma state" "(\<forall> e \<in> \<F> state . current_flow state e > 0)" "aux_invar state"
  shows   "current_flow state e = current_flow (loopB_call2_upd state) e"
proof(rule loopB_call2_condE[OF assms(1)], goal_cases)
  case (1 f b \<gamma> t s P f' b' state')
  have gamma_0:"\<gamma> > 0" using assms unfolding 1 invar_gamma_def by simp
  have s_not_t: " t \<noteq> s "
    using get_source_for_target_axioms[OF 1(2,3,1,7,9)]
          get_target_axioms[OF 1(2,3,7)] \<epsilon>_axiom gamma_0 assms(1,4)
      by (smt (verit, ccfv_SIG) mult_less_cancel_right_disj)
    have s_V: "s \<in> \<V> "
      using get_source_for_target_axioms[OF 1(2,3,1,7,9)] assms(1,4) by simp
    have t_V: "t \<in> \<V> "
      using get_target_axioms[OF 1(2,3,7)] assms(1) by simp
    have resreach: "resreach f s t"
      using get_source_for_target_axioms[OF 1(2,3,1,7,9)]  assms(1,4) by simp
  have f': "f' = current_flow (loopB_call2_upd state)"
    unfolding 1 loopB_call2_upd_def Let_def by simp
  show ?case 
    using f'  assms(2-4) get_source_target_path_b_axioms(3)
          get_source_target_path_b_condI[OF _ s_V t_V _ assms(6,5)]  resreach  1 s_not_t assms(1)
    by (fastforce intro:  sym[OF e_not_in_es_flow_not_change])
qed

theorem outside_actives_and_F_no_change:
  assumes "loopB_dom state"
          "e \<notin> to_set (actives state)" "e \<notin> \<F> state"
          "invar_gamma state" 
          "\<And> e. e \<in> \<F> state \<Longrightarrow> current_flow state e \<ge>
                                 6*N*current_\<gamma> state - (2*N  - \<Phi> state)*current_\<gamma> state"
          "aux_invar state"
    shows "current_flow state e = current_flow (loopB state) e"
  using assms(2-6)
proof(induction rule: loopB_induct[OF assms(1)])
  case (1 state)
    note IH=this
  have gamma_0: "current_\<gamma> state > 0" using IH unfolding invar_gamma_def by auto
  have gamma_flow:"e \<in> \<F> state \<Longrightarrow> current_\<gamma> state \<le> current_flow state e" for e
    apply(rule order.trans[of _ "4*N*current_\<gamma> state"])
    using  gamma_0  N_gtr_0 apply simp
    using  gamma_0 Phi_nonneg[of state, OF IH(6)] N_gtr_0 
    by (intro  order.trans[OF _ IH(7)[of e]])(auto simp add: mult.commute right_diff_distrib)
  have flowF: "\<forall>e\<in>\<F> state. 0 < current_flow state e "
    using gamma_0 gamma_flow by force
  show ?case 
  proof(cases rule: loopB_cases[of state])
    case 3
    have invar_gamma: "invar_gamma (loopB_call1_upd state)"
      using IH
      unfolding loopB_call1_upd_def Let_def invar_gamma_def by simp
    have gamma_Phi_flow: "e \<in> \<F> (loopB_call1_upd state) \<Longrightarrow>
         real (6 * N) * current_\<gamma> (loopB_call1_upd state) -
         real_of_int (int (2 * N) - \<Phi> (loopB_call1_upd state)) * current_\<gamma> (loopB_call1_upd state)
         \<le> current_flow (loopB_call1_upd state) e" for e
         apply(rule order.trans) defer
         apply(rule loopB_call1_cond_flow_Phi[OF 3], simp, simp add: IH)
         using IH(4)  IH(7)[of e] loopB_call1_upd_changes(6)[of state] 
               loopB_call1_upd_changes(4)[of state]  loopB_call1_cond_Phi_decr[OF 3 IH(6)] IH(8)
         by (auto  simp add: left_diff_distrib' flowF)
    moreover have "current_flow state e = current_flow (loopB_call1_upd state) e"
         using IH 3 loopB_call1_upd_changes invar_gamma 
         using flowF by (auto intro: outside_actives_and_F_no_change_call1)
    ultimately show ?thesis 
         using loopB_simps(5) IH 3 loopB_call1_upd_changes invar_gamma invar_aux_pres_call1
         by (auto intro: IH(2))
  next
    case 4
    have invar_gamma: "invar_gamma (loopB_call2_upd state)"
      using IH
      unfolding loopB_call2_upd_def Let_def invar_gamma_def by simp
    have gamma_Phi_flow: "e \<in> \<F> (loopB_call2_upd state) \<Longrightarrow>
         real (6 * N) * current_\<gamma> (loopB_call2_upd state) -
         real_of_int (int (2 * N) - \<Phi> (loopB_call2_upd state)) * current_\<gamma> (loopB_call2_upd state)
         \<le> current_flow (loopB_call2_upd state) e" for e
         apply(rule order.trans) defer
         apply(rule loopB_call2_cond_flow_Phi[OF 4], simp, simp add: IH)
         using IH(4)  IH(7)[of e] loopB_call2_upd_changes(6)[of state] 
               loopB_call2_upd_changes(4)[of state]  loopB_call2_cond_Phi_decr[OF 4 IH(6)] IH(8)
         by (auto simp add: left_diff_distrib' flowF)
    moreover have "current_flow state e = current_flow (loopB_call2_upd state) e"
         using IH 4 loopB_call2_upd_changes invar_gamma 
         using flowF by (auto intro: outside_actives_and_F_no_change_call2)
    ultimately show ?thesis 
         using loopB_simps(6) IH 4 loopB_call2_upd_changes invar_gamma invar_aux_pres_call2
         by (auto intro: IH(2))
     next
       case 1
       then show ?thesis
         by(auto simp add:
          outside_actives_and_F_no_change_cont[of e state] 
          loopB_simps[of state] IH)
     next
       case 2
       then show ?thesis
         using 
          outside_actives_and_F_no_change_succ[of  e state]
          loopB_simps[of state] IH by simp
     next
       case 5
       thus ?thesis
         using 
          outside_actives_and_F_no_change_fail[of e state]
          loopB_simps[of state] IH
         by simp
     next
       case 6
       thus ?thesis
         using 
          outside_actives_and_F_no_change_fail[of e state]
          loopB_simps[of state] IH
         by simp
     qed
   qed

lemma loopB_invar_isOptflow_call1:
  assumes "loopB_call1_cond state" "aux_invar state" 
          "invar_gamma state" "invar_integral state"
          "invar_isOptflow state"  
          "\<And> e. e \<in> \<F> state \<Longrightarrow> current_flow state e \<ge> current_\<gamma> state"
    shows "invar_isOptflow (loopB_call1_upd state)"
proof(rule loopB_call1_condE[OF assms(1)], goal_cases)
  case (1 f b \<gamma> s t P f' b' state')
  note basics = this
  have gamma_0: "\<gamma> > 0" using assms unfolding 1 invar_gamma_def by simp
  have state_cond:"state' = loopB_call1_upd state"
    unfolding 1 loopB_call1_upd_def Let_def by simp
  have sP: "(1 - \<epsilon>) * \<gamma> < b s"  "s \<in> \<V>" using 1 get_source_axioms assms(1)
    by blast+
  have tP: "b t < - \<epsilon> * \<gamma>" "resreach f s t" "t \<in> \<V>"
    using 1 get_target_for_source_axioms  assms(1,3)
    by (metis (no_types, lifting))+
  have s_neq_t: "s \<noteq> t" using sP tP \<epsilon>_axiom gamma_0 
    by (smt (verit, best) mult_less_cancel_right_disj)
  have flowF:"(\<forall> e \<in> \<F> state . current_flow state e > 0)"
    using assms(3) assms(6) invar_gamma_def by fastforce
  have min_path: "is_min_path f s t P" 
    using get_source_target_path_a_axioms(2)  sP(2) tP s_neq_t assms(1,2,5) flowF 1 assms(3)
    by (fastforce intro!: get_source_target_path_a_condI)
  have hdP: "fstv (hd P) = s" 
    using min_path unfolding is_min_path_def is_s_t_path_def by simp
  have lastP: "sndv (last P) = t" 
    using min_path unfolding is_min_path_def is_s_t_path_def by simp
  have egtr0:"e \<in> set P \<Longrightarrow> rcap f e > 0" for e    
    by (meson algo_axioms  algo_axioms augpath_rcap_pos_strict' is_min_path_def min_path is_s_t_path_def)
  have e_gamma:"e \<in> set P \<Longrightarrow> rcap f e \<ge> \<gamma>" for e
  proof-
    assume asm:"e \<in> set P"
    hence oedge:"oedge e \<in> to_set (actives state) \<union> \<F> state"
      using get_source_target_path_a_axioms(3) get_source_target_path_a_condI
            sP(2) tP s_neq_t assms(2) flowF  1assms(1) assms(3)  by blast
    show "ereal \<gamma> \<le> \<uu>\<^bsub>f\<^esub>e"
    proof(rule UnE[OF oedge], goal_cases)
      case 1
      have rcap0:"rcap f e > 0" 
        using asm egtr0 by auto
      moreover obtain rc where  "f (oedge e) = (rc::nat) * \<gamma>"
        using assms(4) 1 unfolding basics invar_integral_def by auto   
      ultimately show ?case 
        apply(cases rule: erev.cases[of e])
        using infinite_u[of "oedge e"] gamma_0 
        by(simp, cases rc, auto)
    next
      case 2
      then show ?case 
        using assms(6)[of "oedge e"] infinite_u[of "oedge e"] gamma_0 
        unfolding 1
        by(cases rule: erev.cases[of e], auto) 
    qed
  qed
  have gamma_Rcap:"ereal \<gamma> \<le> Rcap f (set P)"
    using min_path e_gamma
    unfolding is_min_path_def is_s_t_path_def augpath_def prepath_def Rcap_def 
    by (auto intro: Min.boundedI)
  show ?case 
    unfolding invar_isOptflow_def sym[OF state_cond] 1(12) 
    using assms(5) gamma_Rcap gamma_0 min_path  hdP lastP s_neq_t 1 invar_isOptflow_def[of state]
    by(auto intro!: path_aug_opt_pres[of s t "\<b> -b" f \<gamma> P] split: if_split)
qed
 
lemma loopB_invar_isOptflow_call2:
  assumes "loopB_call2_cond state" "aux_invar state" "invar_gamma state" "invar_integral state"
          "invar_isOptflow state"  "\<And> e. e \<in> \<F> state \<Longrightarrow> current_flow state e \<ge> current_\<gamma> state"
    shows "invar_isOptflow (loopB_call2_upd state)"
proof(rule loopB_call2_condE[OF assms(1)], goal_cases)
  case (1 f b \<gamma> t s P f' b' state')
  note basics = this
  have gamma_0: "\<gamma> > 0" using assms unfolding 1 invar_gamma_def by simp
  have state_cond:"state' = loopB_call2_upd state"
    unfolding 1 loopB_call2_upd_def Let_def by simp
  have tP: "b t < - (1-\<epsilon>) * \<gamma>"  "t \<in> \<V>"
    using get_target_axioms[OF 1(2,3,7)] assms(1) by auto
  have sP: "\<epsilon> * \<gamma> < b s"  "s \<in> \<V>" "resreach f s t" 
    using get_source_for_target_axioms[OF 1(2,3,1,7,9)] assms(1,3) by auto
  have s_neq_t: "s \<noteq> t" using sP tP \<epsilon>_axiom gamma_0 
    by (smt (verit, best) mult_less_cancel_right_disj)
  have flowF:"(\<forall> e \<in> \<F> state . current_flow state e > 0)"
    using assms(3) assms(6) invar_gamma_def by fastforce
  have min_path: "is_min_path f s t P"
    using assms sP tP 1 s_neq_t
    by (auto intro!: get_source_target_path_b_axioms(2) get_source_target_path_b_condI simp add: flowF )
  have hdP: "fstv (hd P) = s" 
    using min_path unfolding is_min_path_def is_s_t_path_def by simp
  have lastP: "sndv (last P) = t" 
    using min_path unfolding is_min_path_def is_s_t_path_def by simp
  have egtr0:"e \<in> set P \<Longrightarrow> rcap f e > 0" for e
    by (meson algo_axioms algo_def algo_axioms algo_def augpath_rcap_pos_strict' is_min_path_def min_path is_s_t_path_def)
  have e_gamma:"e \<in> set P \<Longrightarrow> rcap f e \<ge> \<gamma>" for e
  proof-
    assume asm:"e \<in> set P"
    hence oedge:"oedge e \<in> to_set (actives state) \<union> \<F> state"
      using get_source_target_path_b_axioms(3)[of state s t P] 
            sP(3) s_neq_t flowF assms(2) sP tP 1 assms(1,3) 
      by (fastforce intro: get_source_target_path_b_condI)
    show "ereal \<gamma> \<le> \<uu>\<^bsub>f\<^esub>e"
    proof(rule UnE[OF oedge], goal_cases)
      case 1
      have rcap0:"rcap f e > 0" 
        using asm egtr0 by auto
      moreover obtain rc where  "f (oedge e) = (rc::nat) * \<gamma>"
        using assms(4) 1 unfolding basics invar_integral_def by auto   
      ultimately show ?case 
        apply(cases rule: erev.cases[of e])
        using infinite_u[of "oedge e"] gamma_0 
        by(simp, cases rc, auto)
    next
      case 2
      then show ?case 
        using assms(6)[of "oedge e"] infinite_u[of "oedge e"] gamma_0 
        unfolding 1
        by(cases rule: erev.cases[of e], auto) 
    qed
  qed
  have gamma_Rcap:"ereal \<gamma> \<le> Rcap f (set P)"
    using min_path e_gamma
    unfolding is_min_path_def is_s_t_path_def augpath_def prepath_def Rcap_def 
    by (auto intro: Min.boundedI)
  show ?case 
    unfolding invar_isOptflow_def sym[OF state_cond] 1(12) 
    using assms(5) gamma_Rcap gamma_0 min_path  hdP lastP s_neq_t 1 invar_isOptflow_def[of state]
    by(auto intro!: path_aug_opt_pres[of s t "\<b> -b" f \<gamma> P] split: if_split)
qed

lemma loopB_invar_isOptflow_cont:
  assumes "invar_isOptflow state"  
    shows "invar_isOptflow (loopB_cont_upd state)"
  using assms unfolding loopB_cont_upd_def invar_isOptflow_def by simp

lemma loopB_invar_isOptflow_succ:
  assumes "invar_isOptflow state"  
    shows "invar_isOptflow (loopB_succ_upd state)"
  using assms unfolding loopB_succ_upd_def invar_isOptflow_def by simp

lemma loopB_invar_isOptflow_fail:
  assumes "invar_isOptflow state"  
    shows "invar_isOptflow (loopB_fail_upd state)"
  using assms unfolding loopB_fail_upd_def invar_isOptflow_def by simp

theorem loopB_invar_isOpt_pres:
  assumes "loopB_dom state"
          "aux_invar state" "invar_gamma state" "invar_integral state"
          "invar_isOptflow state"
          "\<And> e. e \<in> \<F> state \<Longrightarrow> current_flow state e \<ge>
                                 6*N*current_\<gamma> state - (2*N  - \<Phi> state)*current_\<gamma> state"
        shows "invar_isOptflow (loopB state)"
  using assms(2-)
proof(induction rule: loopB_induct[OF assms(1)])
  case (1 state)
  note IH = this    
  have gamma_0: "current_\<gamma> state > 0" 
    using IH(5) invar_gamma_def by blast
  have gamma_flow:"e \<in> \<F> state \<Longrightarrow> current_\<gamma> state \<le> current_flow state e" for e
    apply(rule order.trans[of _ "4*N*current_\<gamma> state"])
    using IH(8)[of e] gamma_0 Phi_nonneg[of state, OF IH(5)] N_gtr_0 apply simp
    using  gamma_0 Phi_nonneg[of state, OF IH(5)] N_gtr_0 
    by(intro order.trans[OF _ IH(8)[of e]])(auto simp add: mult.commute right_diff_distrib')
  show ?case 
  proof(cases rule: loopB_cases[of state])
    case 3
    have a1: "aux_invar (loopB_call1_upd state)"
      using invar_aux_pres_call1[of state] IH 3 by simp
    have flowF:  " \<forall>e\<in>\<F> state. 0 < current_flow state e"
      using gamma_0 gamma_flow by fastforce
    have gamma_Phi_flow: "e \<in> \<F> (loopB_call1_upd state) \<Longrightarrow>
         real (6 * N) * current_\<gamma> (loopB_call1_upd state) -
         real_of_int (int (2 * N) - \<Phi> (loopB_call1_upd state)) * current_\<gamma> (loopB_call1_upd state)
         \<le> current_flow (loopB_call1_upd state) e" for e
         apply(rule order.trans) defer
         apply(rule loopB_call1_cond_flow_Phi[OF 3])
         using IH(5)  IH(8)[of e] loopB_call1_upd_changes(6)[of state] 
               loopB_call1_upd_changes(4)[of state]  loopB_call1_cond_Phi_decr[OF 3 IH(5)] IH(4)
         by (auto simp add: left_diff_distrib' flowF)
    have opt:"invar_isOptflow (loopB_call1_upd state)"
       apply(rule loopB_invar_isOptflow_call1)
      using 3  IH   gamma_flow  gamma_Phi_flow by auto
    show ?thesis 
      using a1 invar_gamma_pres_call1[of state]  loopB_call1_invar_integral_pres[of state, OF _ _ _ _ flowF] 3 
            IH gamma_flow gamma_Phi_flow opt loopB_simps(5)[OF IH(1) 3]
      by (auto intro: IH(2))
  next
    case 4
    have a1: "aux_invar (loopB_call2_upd state)"
      using invar_aux_pres_call2[of state] IH 4 by simp
    have flowF:  " \<forall>e\<in>\<F> state. 0 < current_flow state e"
      using gamma_0 gamma_flow by fastforce
    have gamma_Phi_flow: "e \<in> \<F> (loopB_call2_upd state) \<Longrightarrow>
         real (6 * N) * current_\<gamma> (loopB_call2_upd state) -
         real_of_int (int (2 * N) - \<Phi> (loopB_call2_upd state)) * current_\<gamma> (loopB_call2_upd state)
         \<le> current_flow (loopB_call2_upd state) e" for e
         apply(rule order.trans) defer
         apply(rule loopB_call2_cond_flow_Phi[OF 4])
         using IH(5)  IH(8)[of e] loopB_call2_upd_changes(6)[of state] 
               loopB_call2_upd_changes(4)[of state]  loopB_call2_cond_Phi_decr[OF 4 IH(5)] IH(4)
         by (auto simp add: left_diff_distrib' flowF)
    have opt:"invar_isOptflow (loopB_call2_upd state)"
       apply(rule loopB_invar_isOptflow_call2)
      using 4 IH gamma_flow  gamma_Phi_flow by auto
    show ?thesis 
      using a1 invar_gamma_pres_call2[of state]  loopB_call2_invar_integral_pres[of state, OF _ _ _ _ flowF] 4
            IH gamma_flow gamma_Phi_flow opt loopB_simps(6)[OF IH(1) 4]
      by (auto intro: IH(3))
  qed (auto simp add: IH loopB_simps loopB_invar_isOptflow_fail 
                      loopB_invar_isOptflow_succ
                      loopB_invar_isOptflow_cont)
qed

lemma loopB_succ_balance: 
  assumes "loopB_dom state"
          "return (loopB state) = success"
        shows "\<forall> v \<in> \<V>. balance (loopB state) v = 0"
  using assms(2)
proof(induction rule : loopB_induct[OF assms(1)])
  case (1 state)
  note IH =this
  then show ?case 
  proof(cases rule: loopB_cases[of state])
    case 1
    show ?thesis 
      using loopB_simps(2)[OF IH(1) 1] IH(4) 
      by (auto simp add: loopB_cont_upd_def)
  next
    case 2
    then show ?thesis 
      using loopB_simps(1)[OF IH(1) 2] IH(4) 
      unfolding loopB_succ_upd_def Let_def
      by (auto elim: loopB_succ_condE)
  next
    case 3
    then show ?thesis 
      using IH(4)
      apply(subst loopB_simps(5)[OF IH(1) 3], subst (asm) loopB_simps(5)[OF IH(1) 3])
      by(rule IH(2), auto)
  next
    case 4
    then show ?thesis 
      using IH(4)
      apply(subst loopB_simps(6)[OF IH(1) 4], subst (asm) loopB_simps(6)[OF IH(1) 4])
      by(rule IH(3), auto)
  next
    case 5
    then show ?thesis 
      using loopB_simps(3)[OF IH(1) 5] IH(4) 
      by (auto simp add: loopB_fail_upd_def)
  next
    case 6
    then show ?thesis 
      using loopB_simps(4)[OF IH(1) 6] IH(4) 
      by (auto simp add: loopB_fail_upd_def)
  qed
qed

theorem loopB_correctness:
  assumes "loopB_dom state" 
          "aux_invar state"
          "invar_gamma state"
          "invar_integral state"
          "loopB_entryF state"
          "invar_isOptflow state"
          "\<Phi> state \<le> 2*N"
          "return (loopB state) = success"
  shows   "is_Opt \<b> (current_flow (loopB state))"
proof-
  have "\<forall> v \<in> \<V>. balance (loopB state) v = 0"
    using loopB_succ_balance[of state] assms by simp
  moreover have "is_Opt (\<b> - balance (loopB state)) (current_flow (loopB state))"
    apply(rule loopB_invar_isOpt_pres[OF assms(1,2,3,4,6), simplified invar_isOptflow_def])
    using assms(5) assms(3) assms(7) unfolding loopB_entryF_def invar_gamma_def 
    by (smt (verit, ccfv_threshold) mult_nonneg_nonneg of_int_nonneg)
  ultimately show ?thesis
    unfolding is_Opt_def isbflow_def by simp
qed

lemma loopB_fail_balance: 
  assumes "loopB_dom state"
          "state' = loopB state"
          "return (loopB state) = failure"
        shows "(\<exists> s \<in> \<V>. (balance state' s > (1 - \<epsilon>) * current_\<gamma> state' \<and>
                     (\<forall> t \<in> \<V>. resreach (current_flow state') s t \<longrightarrow>
                               balance state' t \<ge> - \<epsilon> * current_\<gamma> state'))) \<or>

              (\<exists> t \<in> \<V>. (balance state' t < - (1 - \<epsilon>) * current_\<gamma> state' \<and>
                     (\<forall> s \<in> \<V>. resreach (current_flow state') s t \<longrightarrow>
                               balance state' s \<le>  \<epsilon> * current_\<gamma> state')))"
  using assms(2, 3)
proof(induction rule : loopB_induct[OF assms(1)])
  case (1 state)
  note IH =this
  then show ?case 
  proof(cases rule: loopB_cases[of state])
    case 1
    show ?thesis 
      using IH(5) loopB_simps(2)[OF IH(1) 1]
      unfolding loopB_cont_upd_def IH(4) by simp     
  next
    case 2
    then show ?thesis 
      using IH(5) loopB_simps(1)[OF IH(1) 2]
      unfolding loopB_succ_upd_def IH(4) by simp 
  next
    case 3
    then show ?thesis 
      apply(rule IH(2))
      using loopB_simps(5)[OF IH(1) 3] IH(4) IH(5) 
      by auto
  next
    case 4
    then show ?thesis 
      apply(rule IH(3))
      using loopB_simps(6)[OF IH(1) 4] IH(4) IH(5) 
      by auto
  next
    case 5
    show ?thesis 
    proof(rule loopB_fail1_condE[OF 5], goal_cases)
      case (1 f b \<gamma> s)
      have "(1 - \<epsilon>) * \<gamma> < b s" "s \<in> \<V>"
        using 1 get_source_axioms 5
        by (metis (no_types, lifting))+
      moreover have "(\<forall>t\<in>\<V>. resreach (current_flow state') s t \<longrightarrow>
                       - \<epsilon> * current_\<gamma> state' \<le> balance state' t)"
        using  1(7)  IH(4) loopB_simps(3)[OF IH(1) 5] 
        unfolding 1(1-3) loopB_fail_upd_def by auto
      ultimately show ?case 
        using  IH(4) loopB_simps(3)[OF IH(1) 5] 
        unfolding 1(1-3) loopB_fail_upd_def by auto
    qed
  next
    case 6
    show ?thesis 
    proof(rule loopB_fail2_condE[OF 6], goal_cases)
      case (1 f b \<gamma> t)
      have "b t < - (1 - \<epsilon>) * \<gamma> " "t \<in> \<V>"
        using 1 get_target_axioms 6
        by (metis (no_types, lifting))+
      moreover have "(\<forall>s\<in>\<V>. resreach (current_flow state') s t \<longrightarrow>
                       \<epsilon> * current_\<gamma> state' \<ge> balance state' s)"
        using  1(8)  IH(4) loopB_simps(4)[OF IH(1) 6] 
        unfolding 1(1-3) loopB_fail_upd_def by auto
      ultimately show ?case 
        using  IH(4) loopB_simps(4)[OF IH(1) 6] 
        unfolding 1(1-3) loopB_fail_upd_def by auto
    qed
  qed
qed

theorem loopB_completeness:
  assumes "loopB_dom state" 
          "aux_invar state"
          "invar_gamma state"
          "invar_integral state"
          "loopB_entryF state"
          "invar_isOptflow state"
          "\<Phi> state \<le> 2*N"
          "return (loopB state) = failure"
  shows   "\<nexists> f. (f is  \<b> flow)"
proof-
  define state' where "state' = loopB state"
  have s_and_t:"(\<exists> s \<in> \<V>. (balance state' s > (1 - \<epsilon>) * current_\<gamma> state' \<and>
                     (\<forall> t \<in> \<V>. resreach (current_flow state') s t \<longrightarrow>
                               balance state' t \<ge> - \<epsilon> * current_\<gamma> state'))) \<or>

        (\<exists> t \<in> \<V>. (balance state' t < - (1 - \<epsilon>) * current_\<gamma> state' \<and>
                     (\<forall> s \<in> \<V>. resreach (current_flow state') s t \<longrightarrow>
                               balance state' s \<le>  \<epsilon> * current_\<gamma> state')))"
    using loopB_fail_balance[of state state', simplified state'_def, OF assms(1) refl assms(8)]
    unfolding state'_def by simp
  moreover have is_Opt:"is_Opt (\<b> - balance (loopB state)) (current_flow (loopB state))"
    apply(rule loopB_invar_isOpt_pres[OF assms(1,2,3,4,6), simplified invar_isOptflow_def])
    using assms(5) assms(3) assms(7) unfolding loopB_entryF_def invar_gamma_def 
    by (smt (verit, ccfv_threshold) mult_nonneg_nonneg of_int_nonneg)
  have gamma_0: "current_\<gamma> state' > 0"
    unfolding state'_def using assms
    by (simp add: invar_gamma_def loopB_changes_current_\<gamma>)
  have gamma_same: "current_\<gamma> state' = current_\<gamma> state"
    by (simp add: assms(1) loopB_changes_current_\<gamma> state'_def)
  have eps_card_V:"0 \<le> - real (card \<V>) * \<epsilon> + 1"
     using  \<epsilon>_axiom cardV_0 unfolding N_def 
     by (metis (no_types, opaque_lifting) add.inverse_inverse linorder_not_le mult.commute 
          mult_minus_right nonzero_mult_div_cancel_left of_nat_0_le_iff of_nat_less_iff 
      ordered_comm_semiring_class.comm_mult_left_mono real_0_le_add_iff times_divide_eq_right)
   have eps_card_V':"real (card \<V> ) * \<epsilon> - 1 \<le> 0"
     using eps_card_V by linarith
   have eps_card_rewrite:"- real (card \<V>) * \<epsilon> + 1 \<le> - real (card \<V> - 1) * \<epsilon> + 1 - \<epsilon>"
     by(auto simp add: algebra_simps)
       (metis Suc_diff_Suc cardV_0 minus_nat.diff_0 mult.right_neutral of_nat_Suc order.refl ring_class.ring_distribs(1))
  show ?thesis
  proof(rule disjE[OF s_and_t], goal_cases)
    case 1
    then obtain s where s_prop:"s \<in> \<V> " "(1 - \<epsilon>) * current_\<gamma> state' < balance state' s"
         "\<forall>t\<in>\<V>. resreach (current_flow state') s t \<longrightarrow> - \<epsilon> * current_\<gamma> state' \<le> balance state' t"
      by auto
    have "(\<Sum> x \<in> Rescut (current_flow state') s. balance state' x) =
         (\<Sum> x \<in> Rescut (current_flow state') s - {s}. balance state' x) + balance state' s"
      apply(rule trans, rule sum.subset_diff[where B="{s}"])
      using finite_Rescut s_prop(1)
      by (auto simp add: Rescut_def)
    also have "... > (N - 1) * ( - \<epsilon> * current_\<gamma> state') + (1 - \<epsilon>) * current_\<gamma> state' "
      apply(rule add_le_less_mono)
       apply(rule order.trans) defer
        apply(rule sum_bounded_below[of _ "-\<epsilon> *  current_\<gamma> state'"])
      subgoal
        using s_prop(3) 
      by (metis (no_types, lifting) DiffD1 Diff_insert_absorb Rescut_around_in_V Rescut_def insert_absorb mem_Collect_eq s_prop(1) subsetD)
    using s_prop  Rescut_around_in_V[of s "current_flow state'"] gamma_0 \<epsilon>_axiom \<V>_finite card_Diff_singleton
    unfolding N_def 
    by  (simp, subst card_Diff_singleton,
         auto intro: mult_right_mono_neg simp add: Rescut_def card_mono diff_le_mono s_prop(1))
   finally have 11: "real (N - 1) * (- \<epsilon> * current_\<gamma> state') + (1 - \<epsilon>) * current_\<gamma> state'
  < sum (balance state') (Rescut (current_flow state') s ) " by simp
   have residual_balance:"(\<Sum> x \<in> Rescut (current_flow state') s. balance state' x) > 0"
     apply(rule xt1(7), rule 11)
     apply(rule order.trans[of _ " (- real (card \<V> - 1) *  \<epsilon>  + 1 - \<epsilon>) * current_\<gamma> state'"])
     apply(subst sym[OF mult_zero_left[of "current_\<gamma> state'"]])
     using N_def  eps_card_V eps_card_rewrite   gamma_0 gamma_same 
     by(intro mult_right_mono[where c="current_\<gamma> state'"],
         auto simp add: algebra_simps)
   have Rescut_fV: "Rescut (current_flow state') s \<subseteq> \<V>" 
     by (simp add: Rescut_around_in_V s_prop(1))
   show ?case 
   proof(rule ccontr, auto, goal_cases)
     case (1 f)
     have " (\<Sum> v \<in> Rescut (current_flow state') s. ereal (\<b> v)) \<le> Cap (Rescut (current_flow state') s)"
       using flow_less_cut[OF 1 Rescut_fV] by simp
     also have "... =  (\<Sum> v \<in> Rescut (current_flow state') s. ereal (\<b> v - balance state' v))"
       using flow_saturates_res_cut[of "current_flow state'" " \<b> - balance state'" s] is_Opt
             Rescut_fV unfolding is_Opt_def state'_def by simp 
     also have "... = (\<Sum> v \<in> Rescut (current_flow state') s. \<b> v ) -
                         (\<Sum> v \<in> Rescut (current_flow state') s. balance state' v)"
       by (simp add: sum_subtractf)
     also have "...  < (\<Sum> v \<in> Rescut (current_flow state') s. \<b> v ) "
       using residual_balance by simp
     finally show False by simp
   qed
  next
    case 2
    then obtain t where t_prop: "balance state' t < - (1 - \<epsilon>) * current_\<gamma> state'" "t \<in> \<V>"
         "(\<forall>s\<in>\<V>. resreach (current_flow state') s t \<longrightarrow> balance state' s \<le> \<epsilon> * current_\<gamma> state')"
      by auto
    have "(\<Sum> x \<in> ARescut (current_flow state') t. balance state' x) =
         (\<Sum> x \<in> ARescut (current_flow state') t - {t}. balance state' x) + balance state' t"
      apply(rule trans, rule sum.subset_diff[where B="{t}"])
      using finite_ARescut t_prop(2)
      by (auto simp add: ARescut_def)
    also have "... < (N - 1) * ( \<epsilon> * current_\<gamma> state') + (- (1 - \<epsilon>) * current_\<gamma> state') "
      apply(rule add_le_less_mono)
      apply(rule order.trans) defer
      apply(rule order.trans, rule sum_bounded_above[of 
           "ARescut (current_flow state') t - {t}" "balance state'" "\<epsilon> *  current_\<gamma> state'"]) 
      using  ARescut_def  N_def  t_prop  ARescut_around_in_V[of t "current_flow state'"]
             gamma_0 \<epsilon>_axiom \<V>_finite       
         by (blast, subst card_Diff_singleton, 
             auto intro: mult_right_mono simp add: ARescut_def card_mono diff_le_mono)
    finally have 11: "real (N - 1) * ( \<epsilon> * current_\<gamma> state') - (1 - \<epsilon>) * current_\<gamma> state'
                       > sum (balance state') (ARescut (current_flow state') t ) " 
      by linarith
   have residual_balance:"(\<Sum> x \<in> ARescut (current_flow state') t. balance state' x) < 0"
     apply(rule xt1(8)) defer
     apply(rule 11, rule order.trans[of _ " ( real (card \<V> - 1) *  \<epsilon>  - ( 1 - \<epsilon>)) * current_\<gamma> state'"])
     using N_def eps_card_V eps_card_rewrite gamma_0 gamma_same eps_card_V gamma_0 eps_card_rewrite 
     by (simp add: algebra_simps, subst sym[OF mult_zero_left[of "current_\<gamma> state'"]], 
         intro  mult_right_mono[where c="current_\<gamma> state'"], auto)
   have ARescut_fV: "ARescut (current_flow state') t \<subseteq> \<V>" 
     by (simp add: ARescut_around_in_V t_prop)
   show ?case 
   proof(rule ccontr, auto, goal_cases)
     case (1 f)
     have " - (\<Sum> v \<in> ARescut (current_flow state') t. ereal (\<b> v)) \<le>
             ACap (ARescut (current_flow state') t)"
       using minus_leq_flip[OF flow_less_acut[OF 1 ARescut_fV]] by simp 
     also have "... =  - (\<Sum> v \<in> ARescut (current_flow state') t. ereal (\<b> v - balance state' v))"
       using flow_saturates_ares_cut[of "current_flow state'" " \<b> - balance state'" t,
             simplified, OF _ ARescut_fV ] is_Opt  unfolding is_Opt_def state'_def
       by (metis sum_ereal uminus_ereal.simps(1))    
     also have "... = - ((\<Sum> v \<in> ARescut (current_flow state') t. \<b> v ) -
                         (\<Sum> v \<in> ARescut (current_flow state') t. balance state' v))"
       by (simp add: sum_subtractf)
     also have "...  < - (\<Sum> v \<in> ARescut (current_flow state') t. \<b> v ) "
       using residual_balance
       by simp
     finally show False by simp
   qed
  qed
qed

lemma loopB_simps': 
  shows   "loopB_succ_cond state \<Longrightarrow> loopB state = (loopB_succ_upd state)"
          "loopB_cont_cond state \<Longrightarrow> loopB state = (loopB_cont_upd state)"
          "loopB_fail1_cond state \<Longrightarrow> loopB state = (loopB_fail_upd state)"
          "loopB_fail2_cond state \<Longrightarrow> loopB state = (loopB_fail_upd state)"
proof-
  show "loopB_succ_cond state \<Longrightarrow> local.loopB state = loopB_succ_upd state"
    using  loopB.psimps  loopB_dom_succ[of state]
    unfolding loopB_succ_upd_def Let_def 
    by (auto elim: loopB_succ_condE)
  show "loopB_cont_cond state \<Longrightarrow> local.loopB state = loopB_cont_upd state"
    apply(subst loopB.psimps, simp add:  loopB_dom_cont[of state])
    unfolding loopB_cont_upd_def loopB_cont_cond_def Let_def 
    by presburger
  show " loopB_fail1_cond state \<Longrightarrow> loopB state = loopB_fail_upd state"
    apply(subst loopB.psimps, simp add:  loopB_dom_fail1[of state])
    unfolding loopB_fail_upd_def loopB_fail1_cond_def Let_def 
    by presburger
  show "loopB_fail2_cond state \<Longrightarrow> loopB state = loopB_fail_upd state"
    apply(subst loopB.psimps, simp add:  loopB_dom_fail2[of state])
    unfolding loopB_fail_upd_def loopB_fail2_cond_def Let_def 
    by presburger
 qed    

lemma loopB_nothing_done: 
  assumes "\<not> (\<forall> v \<in> \<V>. balance  state v = 0)"
          "\<not> (\<exists> v \<in> \<V>. \<bar> balance state v\<bar> > (1- \<epsilon>) * current_\<gamma> state)"
    shows "loopB state = state\<lparr> return:= notyetterm\<rparr>"
  apply(subst loopB_cases[of state])
  subgoal
    using loopB_cont_upd_def loopB_simps'(2) 
    by (auto intro: loopB_cont_condE)
  using assms by(fastforce elim: loopB_call1_condE loopB_call2_condE loopB_fail1_condE
                               loopB_succ_condE loopB_fail2_condE)+
    
lemma loopB_forest_no_change:
  assumes "loopB_dom state"
  shows "(loopB state) \<lparr>  current_flow := current_flow state,
                          balance := balance state,
                          return:= return state\<rparr> = state"
  using assms by(intro Algo_state.equality, 
                 auto intro!: loopB_changes_\<FF> loopB_changes_conv_to_rdg
                              loopB_changes_actives loopB_changes_current_\<gamma>
                              loopB_changes_representative
                              loopB_changes_comp_card
                              loopB_changes_\<FF>_imp
                              loopB_changes_not_blocked)
end
end