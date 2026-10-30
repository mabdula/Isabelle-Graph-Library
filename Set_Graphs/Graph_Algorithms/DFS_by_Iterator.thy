theory DFS_by_Iterator
  imports DFS Data_Structures.Iterable_Set_Specs Data_Structures.Fixed_Univ_Set_Specs
begin

provenance ai


section \<open>Depth-First Search by Neighbourhood Iterators\<close>

text \<open>The neighbourhoods are additionally presented by an @{locale indexed_iterable_set} over the
      vertices. Initially, the unused part of the iterator at a vertex is its whole
      neighbourhood.\<close>

record ('ver, 'sset, 'nbs) DFS_it_state = "('ver, 'sset) DFS_state" + its:: "'nbs"

locale \<^marker>\<open>provenance ai_human\<close> DFS_by_Iterator =
  DFS where lookup = lookup +
  nbs: indexed_iterable_set where
      idx_invar     = nbs_invar and
      idx_abstract  = nbs_abstract and
      idx_current   = nbs_current and
      idx_has       = nbs_has and
      idx_iterated  = nbs_iterated and
      idx_remaining = nbs_remaining and
      idx_move      = nbs_move and
      idx_reset     = nbs_reset and
      K = K +
  seen_set: fixed_univ_set where U = U
      and fixed_univ_set_invar = seen_invar and fixed_univ_set_abstract = seen_abstract
      and fixed_univ_set_empty = seen_empty and fixed_univ_set_insert = seen_insert
      and fixed_univ_set_delete = seen_delete and fixed_univ_set_isin = seen_isin
  for lookup :: "'adjmapmap \<Rightarrow> 'v \<Rightarrow> 'vset option"
  and nbs_invar     :: "'nbs \<Rightarrow> bool"
  and nbs_abstract  :: "'nbs \<Rightarrow> 'v \<Rightarrow> 'v set"
  and nbs_current   :: "'nbs \<Rightarrow> 'v \<Rightarrow> 'v"
  and nbs_has       :: "'nbs \<Rightarrow> 'v \<Rightarrow> bool"
  and nbs_iterated  :: "'nbs \<Rightarrow> 'v \<Rightarrow> 'v set"
  and nbs_remaining :: "'nbs \<Rightarrow> 'v \<Rightarrow> 'v set"
  and nbs_move      :: "'nbs \<Rightarrow> 'v \<Rightarrow> 'nbs"
  and nbs_reset     :: "'nbs \<Rightarrow> 'v \<Rightarrow> 'nbs"
  and seen_invar    :: "'sset \<Rightarrow> bool"
  and seen_abstract :: "'sset \<Rightarrow> 'v set"
  and seen_empty    :: "'sset"
  and seen_insert   :: "'v \<Rightarrow> 'sset \<Rightarrow> 'sset"
  and seen_delete   :: "'v \<Rightarrow> 'sset \<Rightarrow> 'sset"
  and seen_isin     :: "'sset \<Rightarrow> 'v \<Rightarrow> bool"
  and U             :: "'v set"
  and K             :: "'v set" +
  fixes nbs_init :: "'nbs"
begin

subsection \<open>Using the function package to model while-loops\<close>

text \<open>The iterator at the top vertex is moved past already seen neighbours. The first unseen
      neighbour is pushed.\<close>

function \<^marker>\<open>provenance ai_human\<close> (domintros) DFS_it::"('v, 'sset, 'nbs) DFS_it_state \<Rightarrow> ('v, 'sset, 'nbs) DFS_it_state" where
  "DFS_it dfs_state = 
     (case (stack dfs_state) of (v # stack_tl) \<Rightarrow>
       (if v = t then 
          (dfs_state \<lparr>return := Reachable\<rparr>)
        else (if nbs_has (its dfs_state) v then
                let u = nbs_current (its dfs_state) v;
                    its' = nbs_move (its dfs_state) v
                in
                  (if seen_isin (seen dfs_state) u then
                     DFS_it (dfs_state \<lparr>its := its'\<rparr>)
                   else
                     DFS_it (dfs_state \<lparr>stack := u # (stack dfs_state),
                                        seen := seen_insert u (seen dfs_state), its := its'\<rparr>))
              else
                DFS_it (dfs_state \<lparr>stack := stack_tl\<rparr>))
      )
     | _ \<Rightarrow> (dfs_state \<lparr>return := NotReachable\<rparr>)
    )"
  by pat_completeness auto

definition "initial_state_it =
  \<lparr>stack = [s], seen = seen_insert s seen_empty, return = NotReachable, its = nbs_init\<rparr>"

definition "DFS_it_call_1_conds dfs_state = 
    (case stack dfs_state of (v # stack_tl) \<Rightarrow>
       v \<noteq> t \<and> nbs_has (its dfs_state) v \<and>
       \<not> (seen_isin (seen dfs_state) (nbs_current (its dfs_state) v))
     | _ \<Rightarrow> False)"

lemma DFS_it_call_1_conds[call_cond_elims]: 
  "DFS_it_call_1_conds dfs_state \<Longrightarrow> 
   \<lbrakk>\<lbrakk>\<exists>v stack_tl. stack dfs_state = v # stack_tl;
    hd (stack dfs_state) \<noteq> t;
    nbs_has (its dfs_state) (hd (stack dfs_state));
    \<not> (seen_isin (seen dfs_state) (nbs_current (its dfs_state) (hd (stack dfs_state))))\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> 
   P"
  by(auto simp: DFS_it_call_1_conds_def split: list.splits)

definition "DFS_it_upd1 dfs_state = (
    let
      v = hd (stack dfs_state);
      u = nbs_current (its dfs_state) v
    in
      dfs_state \<lparr>stack := u # (stack dfs_state), seen := seen_insert u (seen dfs_state),
                 its := nbs_move (its dfs_state) v\<rparr>)" 

definition "DFS_it_call_2_conds dfs_state = 
    (case stack dfs_state of (v # stack_tl) \<Rightarrow>
       v \<noteq> t \<and> nbs_has (its dfs_state) v \<and>
       seen_isin (seen dfs_state) (nbs_current (its dfs_state) v)
     | _ \<Rightarrow> False)"

lemma DFS_it_call_2_conds[call_cond_elims]: 
  "DFS_it_call_2_conds dfs_state \<Longrightarrow> 
   \<lbrakk>\<lbrakk>\<exists>v stack_tl. stack dfs_state = v # stack_tl;
    hd (stack dfs_state) \<noteq> t;
    nbs_has (its dfs_state) (hd (stack dfs_state));
    seen_isin (seen dfs_state) (nbs_current (its dfs_state) (hd (stack dfs_state)))\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> 
   P"
  by(auto simp: DFS_it_call_2_conds_def split: list.splits)

definition "DFS_it_upd2 dfs_state = 
  (dfs_state \<lparr>its := nbs_move (its dfs_state) (hd (stack dfs_state))\<rparr>)"

definition "DFS_it_call_3_conds dfs_state = 
    (case stack dfs_state of (v # stack_tl) \<Rightarrow>
       v \<noteq> t \<and> \<not> nbs_has (its dfs_state) v
     | _ \<Rightarrow> False)"

lemma DFS_it_call_3_conds[call_cond_elims]: 
  "DFS_it_call_3_conds dfs_state \<Longrightarrow> 
   \<lbrakk>\<lbrakk>\<exists>v stack_tl. stack dfs_state = v # stack_tl;
    hd (stack dfs_state) \<noteq> t;
    \<not> nbs_has (its dfs_state) (hd (stack dfs_state))\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> 
   P"
  by(auto simp: DFS_it_call_3_conds_def split: list.splits)

definition "DFS_it_upd3 dfs_state = 
  (dfs_state \<lparr>stack := tl (stack dfs_state)\<rparr>)"

definition "DFS_it_ret_1_conds dfs_state = (stack dfs_state = [])"

lemma DFS_it_ret_1_conds[call_cond_elims]:
  "DFS_it_ret_1_conds dfs_state \<Longrightarrow> 
   \<lbrakk>\<lbrakk>stack dfs_state = []\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> 
   P"
  by(auto simp: DFS_it_ret_1_conds_def)

lemma DFS_it_ret_1_condsI[call_cond_intros]:
  "\<lbrakk>stack dfs_state = []\<rbrakk> \<Longrightarrow> DFS_it_ret_1_conds dfs_state"
  by(auto simp: DFS_it_ret_1_conds_def)

definition "DFS_it_ret1 dfs_state = (dfs_state \<lparr>return := NotReachable\<rparr>)"

definition "DFS_it_ret_2_conds dfs_state =
   (case stack dfs_state of (v # stack_tl) \<Rightarrow> v = t
     | _ \<Rightarrow> False)"

lemma DFS_it_ret_2_conds[call_cond_elims]:
  "DFS_it_ret_2_conds dfs_state \<Longrightarrow> 
   \<lbrakk>\<And>v stack_tl. \<lbrakk>stack dfs_state = v # stack_tl;
    (hd (stack dfs_state)) = t\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> 
   P"
  by(auto simp: DFS_it_ret_2_conds_def split: list.splits)

lemma DFS_it_ret_2_condsI[call_cond_intros]:
  "\<And>v stack_tl. \<lbrakk>stack dfs_state = v # stack_tl; (hd (stack dfs_state)) = t\<rbrakk> \<Longrightarrow>
     DFS_it_ret_2_conds dfs_state"
  by(auto simp: DFS_it_ret_2_conds_def)

definition "DFS_it_ret2 dfs_state = (dfs_state \<lparr>return := Reachable\<rparr>)"

lemma DFS_it_cases:
  assumes "DFS_it_call_1_conds dfs_state \<Longrightarrow> P"
      "DFS_it_call_2_conds dfs_state \<Longrightarrow> P"
      "DFS_it_call_3_conds dfs_state \<Longrightarrow> P"
      "DFS_it_ret_1_conds dfs_state \<Longrightarrow> P"
      "DFS_it_ret_2_conds dfs_state \<Longrightarrow> P"
  shows "P"
proof-
  have "DFS_it_call_1_conds dfs_state \<or> DFS_it_call_2_conds dfs_state \<or>
        DFS_it_call_3_conds dfs_state \<or>
        DFS_it_ret_1_conds dfs_state \<or> DFS_it_ret_2_conds dfs_state"
    by (auto simp add: DFS_it_call_1_conds_def DFS_it_call_2_conds_def DFS_it_call_3_conds_def
                       DFS_it_ret_1_conds_def DFS_it_ret_2_conds_def
           split: list.split_asm)
  then show ?thesis
    using assms
    by auto
qed

lemma DFS_it_simps:
  assumes "DFS_it_dom dfs_state" 
  shows"DFS_it_call_1_conds dfs_state \<Longrightarrow> DFS_it dfs_state = DFS_it (DFS_it_upd1 dfs_state)"
      "DFS_it_call_2_conds dfs_state \<Longrightarrow> DFS_it dfs_state = DFS_it (DFS_it_upd2 dfs_state)"
      "DFS_it_call_3_conds dfs_state \<Longrightarrow> DFS_it dfs_state = DFS_it (DFS_it_upd3 dfs_state)"
      "DFS_it_ret_1_conds dfs_state \<Longrightarrow> DFS_it dfs_state = DFS_it_ret1 dfs_state"
      "DFS_it_ret_2_conds dfs_state \<Longrightarrow> DFS_it dfs_state = DFS_it_ret2 dfs_state"
  by (auto simp add: DFS_it.psimps[OF assms] Let_def
                     DFS_it_call_1_conds_def DFS_it_upd1_def DFS_it_call_2_conds_def DFS_it_upd2_def
                     DFS_it_call_3_conds_def DFS_it_upd3_def
                     DFS_it_ret_1_conds_def DFS_it_ret1_def
                     DFS_it_ret_2_conds_def DFS_it_ret2_def
            split: list.splits)

lemma DFS_it_induct: 
  assumes "DFS_it_dom dfs_state"
  assumes "\<And>dfs_state. \<lbrakk>DFS_it_dom dfs_state;
                        DFS_it_call_1_conds dfs_state \<Longrightarrow> P (DFS_it_upd1 dfs_state);
                        DFS_it_call_2_conds dfs_state \<Longrightarrow> P (DFS_it_upd2 dfs_state);
                        DFS_it_call_3_conds dfs_state \<Longrightarrow> P (DFS_it_upd3 dfs_state)\<rbrakk>
                \<Longrightarrow> P dfs_state"
  shows "P dfs_state"
  apply(rule DFS_it.pinduct[OF assms(1)])
  apply(rule assms(2)[simplified DFS_it_call_1_conds_def DFS_it_upd1_def DFS_it_call_2_conds_def
                                 DFS_it_upd2_def DFS_it_call_3_conds_def DFS_it_upd3_def])
  by (auto simp: Let_def split: list.splits)

lemma DFS_it_domintros: 
  assumes "DFS_it_call_1_conds dfs_state \<Longrightarrow> DFS_it_dom (DFS_it_upd1 dfs_state)"
  assumes "DFS_it_call_2_conds dfs_state \<Longrightarrow> DFS_it_dom (DFS_it_upd2 dfs_state)"
  assumes "DFS_it_call_3_conds dfs_state \<Longrightarrow> DFS_it_dom (DFS_it_upd3 dfs_state)"
  shows "DFS_it_dom dfs_state"
proof(rule DFS_it.domintros, goal_cases)
  case (1 x21 x22)
  then show ?case
    using assms(2)[simplified DFS_it_call_2_conds_def DFS_it_upd2_def]
    by (force simp: Let_def)
next
  case (2 x21 x22)
  then show ?case
    using assms(1)[simplified DFS_it_call_1_conds_def DFS_it_upd1_def]
    by (force simp: Let_def)
next
  case (3 x21 x22)
  then show ?case
    using assms(3)[simplified DFS_it_call_3_conds_def DFS_it_upd3_def]
    by force
qed

text \<open>One step of the loop. The states reached from the initial state by steps are those the
      run passes through.\<close>

definition "DFS_it_step dfs_state dfs_state' =
  ((DFS_it_call_1_conds dfs_state \<and> dfs_state' = DFS_it_upd1 dfs_state) \<or>
   (DFS_it_call_2_conds dfs_state \<and> dfs_state' = DFS_it_upd2 dfs_state) \<or>
   (DFS_it_call_3_conds dfs_state \<and> dfs_state' = DFS_it_upd3 dfs_state))"

subsection \<open>Invariants and relation to the original DFS\<close>

definition "invar_it dfs_state =
  (seen_invar (seen dfs_state) \<and> nbs_invar (its dfs_state) \<and>
   distinct (stack dfs_state) \<and> set (stack dfs_state) \<subseteq> seen_abstract (seen dfs_state) \<and>
   seen_abstract (seen dfs_state) \<subseteq> dVs (Graph.digraph_abs G) \<and>
   (\<forall>v\<in>K. nbs_abstract (its dfs_state) v = t_set (\<N>\<^sub>G v) \<and>
           nbs_iterated (its dfs_state) v \<subseteq> seen_abstract (seen dfs_state)))"

definition "state_rel_it dfs_state dfs_it_state =
  (stack dfs_state = stack dfs_it_state \<and> return dfs_state = return dfs_it_state \<and>
   t_set (seen dfs_state) = seen_abstract (seen dfs_it_state))"

end

locale \<^marker>\<open>provenance ai_human\<close> DFS_by_Iterator_thms = DFS_by_Iterator + DFS_thms where lookup = lookup +
  assumes vertices_in_U: "dVs (Graph.digraph_abs G) \<subseteq> U"
    and vertices_in_K: "dVs (Graph.digraph_abs G) \<subseteq> K"
    and nbs_init_invar: "nbs_invar nbs_init"
    and nbs_init_iterated: "\<And>v. v \<in> K \<Longrightarrow> nbs_iterated nbs_init v = {}"
    and nbs_init_remaining:
      "\<And>v. v \<in> K \<Longrightarrow> nbs_remaining nbs_init v = t_set (\<N>\<^sub>G v)"
begin

subsubsection \<open>The invariant\<close>

lemma invar_it_move:
  assumes "invar_it st" "v \<in> K" "nbs_remaining (its st) v \<noteq> {}"
          "its st' = nbs_move (its st) v" "seen_invar (seen st')"
          "seen_abstract (seen st) \<subseteq> seen_abstract (seen st')"
          "nbs_current (its st) v \<in> seen_abstract (seen st')"
          "distinct (stack st')" "set (stack st') \<subseteq> seen_abstract (seen st')"
          "seen_abstract (seen st') \<subseteq> dVs (Graph.digraph_abs G)"
  shows "invar_it st'"
proof-
  have C: "nbs_invar (its st)"
    and abs: "\<And>w. w \<in> K \<Longrightarrow> nbs_abstract (its st) w = t_set (\<N>\<^sub>G w)"
    and it: "\<And>w. w \<in> K \<Longrightarrow> nbs_iterated (its st) w \<subseteq> seen_abstract (seen st)"
    using assms(1) by (auto simp: invar_it_def)
  have "nbs_iterated (its st') w \<subseteq> seen_abstract (seen st')" if "w \<in> K" for w
    using it[OF that] assms(6,7) nbs.idx_move_iterated[OF C assms(2,3)]
          nbs.idx_move_iterated_other[OF C assms(2,3)]
    by (cases "w = v") (auto simp: assms(4))
  thus ?thesis
    using abs assms(5,8-10) nbs.idx_move_invar[OF C assms(2)] nbs.idx_move_abstract[OF C assms(2,3)]
    by (auto simp: invar_it_def assms(4))
qed

lemma top_in_K:
  assumes "invar_it st" "stack st = v # stack_tl"
  shows "v \<in> K"
  using assms vertices_in_K by (auto simp: invar_it_def)

lemma current_in_neighbourhood:
  assumes "invar_it st" "v \<in> K" "nbs_has (its st) v"
  shows "nbs_remaining (its st) v \<noteq> {}" "nbs_current (its st) v \<in> t_set (\<N>\<^sub>G v)"
proof-
  have C: "nbs_invar (its st)" "nbs_abstract (its st) v = t_set (\<N>\<^sub>G v)"
    using assms(1,2) by (auto simp: invar_it_def)
  show rem: "nbs_remaining (its st) v \<noteq> {}"
    using nbs.idx_has[OF C(1) assms(2)] assms(3) by simp
  show "nbs_current (its st) v \<in> t_set (\<N>\<^sub>G v)"
    using nbs.idx_current[OF C(1) assms(2) rem] nbs.idx_partition_union[OF C(1) assms(2)] C(2)
    by blast
qed

lemma invar_it_holds:
  assumes "invar_it st"
  shows "DFS_it_call_1_conds st \<Longrightarrow> invar_it (DFS_it_upd1 st)"
        "DFS_it_call_2_conds st \<Longrightarrow> invar_it (DFS_it_upd2 st)"
        "DFS_it_call_3_conds st \<Longrightarrow> invar_it (DFS_it_upd3 st)"
proof-
  have invs: "seen_invar (seen st)" "distinct (stack st)"
    "set (stack st) \<subseteq> seen_abstract (seen st)" "seen_abstract (seen st) \<subseteq> dVs (Graph.digraph_abs G)"
    using assms by (auto simp: invar_it_def)
  show "invar_it (DFS_it_upd1 st)" if c: "DFS_it_call_1_conds st"
  proof-
    obtain v stack_tl where stack: "stack st = v # stack_tl" and has: "nbs_has (its st) v"
      and unseen: "\<not> seen_isin (seen st) (nbs_current (its st) v)"
      using c by (auto simp: DFS_it_call_1_conds_def split: list.splits)
    define u where "u = nbs_current (its st) v"
    have K: "v \<in> K"
      using top_in_K[OF assms stack] .
    have rem: "nbs_remaining (its st) v \<noteq> {}" and u_G: "u \<in> dVs (Graph.digraph_abs G)"
      using current_in_neighbourhood[OF assms K has] by (auto simp: u_def)
    have U: "u \<in> U"
      using u_G vertices_in_U by blast
    have "u \<notin> seen_abstract (seen st)"
      using unseen seen_set.fixed_univ_set_isin[OF invs(1)] by (simp add: u_def)
    thus ?thesis
      using invs u_G seen_set.fixed_univ_set_insert[OF invs(1) U]
      by (intro invar_it_move[OF assms K rem])
         (auto simp: DFS_it_upd1_def Let_def stack u_def[symmetric])
  qed
  show "invar_it (DFS_it_upd2 st)" if c: "DFS_it_call_2_conds st"
  proof-
    obtain v stack_tl where stack: "stack st = v # stack_tl" and has: "nbs_has (its st) v"
      and seen: "seen_isin (seen st) (nbs_current (its st) v)"
      using c by (auto simp: DFS_it_call_2_conds_def split: list.splits)
    have K: "v \<in> K"
      using top_in_K[OF assms stack] .
    show ?thesis
      using invs current_in_neighbourhood(1)[OF assms K has] seen
      by (intro invar_it_move[OF assms K])
         (auto simp: DFS_it_upd2_def stack seen_set.fixed_univ_set_isin)
  qed
  show "invar_it (DFS_it_upd3 st)" if c: "DFS_it_call_3_conds st"
    using assms c by (auto simp: invar_it_def DFS_it_upd3_def elim!: call_cond_elims)
qed

lemma invar_it_initial: "invar_it initial_state_it"
proof-
  have U: "s \<in> U"
    using vertices_in_U by blast
  have C: "nbs_abstract nbs_init v = t_set (\<N>\<^sub>G v)" "nbs_iterated nbs_init v = {}" if "v \<in> K" for v
    using nbs.idx_partition_union[OF nbs_init_invar that] nbs_init_iterated[OF that]
          nbs_init_remaining[OF that]
    by auto
  show "invar_it initial_state_it"
    using C seen_set.fixed_univ_set_insert[OF seen_set.fixed_univ_set_empty(1) U]
    by (simp add: invar_it_def initial_state_it_def nbs_init_invar seen_set.fixed_univ_set_empty(2))
qed

text \<open>A vertex is only pushed if it is unseen, so the stack is shorter than the number of
      vertices.\<close>

lemma DFS_it_push_length:
  assumes "invar_it st" "DFS_it_call_1_conds st"
  shows "length (stack st) < card (dVs (Graph.digraph_abs G))"
proof-
  have "distinct (stack (DFS_it_upd1 st))" "set (stack (DFS_it_upd1 st)) \<subseteq> dVs (Graph.digraph_abs G)"
    using invar_it_holds(1)[OF assms] by (auto simp: invar_it_def)
  thus ?thesis
    using card_mono[OF Graph.finite_vertices[OF graph_inv], of "set (stack (DFS_it_upd1 st))"]
          distinct_card[of "stack (DFS_it_upd1 st)"]
    by (auto simp: DFS_it_upd1_def Let_def)
qed

subsubsection \<open>Termination\<close>

text \<open>Pushing shrinks the unseen vertices, skipping shrinks the unused parts of the iterators,
      popping shrinks the stack.\<close>

lemma DFS_it_terminates:
  assumes "invar_it st"
  shows "DFS_it_dom st"
  using assms
proof(induction st rule: wf_induct_rule[OF wf_measures[of
      "[\<lambda>st. card (dVs (Graph.digraph_abs G) - seen_abstract (seen st)),
        \<lambda>st. \<Sum>v\<in>dVs (Graph.digraph_abs G). card (nbs_remaining (its st) v),
        \<lambda>st. length (stack st)]"]])
  case IH: (1 st)
  have invs: "seen_invar (seen st)" "set (stack st) \<subseteq> seen_abstract (seen st)"
    "seen_abstract (seen st) \<subseteq> dVs (Graph.digraph_abs G)"
    using IH(2) by (auto simp: invar_it_def)
  show ?case
  proof(rule DFS_it_domintros)
    assume c: "DFS_it_call_1_conds st"
    obtain v stack_tl where stack: "stack st = v # stack_tl" and has: "nbs_has (its st) v"
      and unseen: "\<not> seen_isin (seen st) (nbs_current (its st) v)"
      using c by (auto simp: DFS_it_call_1_conds_def split: list.splits)
    define u where "u = nbs_current (its st) v"
    have u_G: "u \<in> dVs (Graph.digraph_abs G)"
      using current_in_neighbourhood(2)[OF IH(2) top_in_K[OF IH(2) stack] has] by (auto simp: u_def)
    have "u \<notin> seen_abstract (seen st)"
      using unseen seen_set.fixed_univ_set_isin[OF invs(1)] by (simp add: u_def)
    hence "dVs (Graph.digraph_abs G) - seen_abstract (seen (DFS_it_upd1 st))
           \<subset> dVs (Graph.digraph_abs G) - seen_abstract (seen st)"
      using u_G vertices_in_U seen_set.fixed_univ_set_insert(2)[OF invs(1), of u]
      by (auto simp: DFS_it_upd1_def Let_def stack u_def[symmetric])
    hence "card (dVs (Graph.digraph_abs G) - seen_abstract (seen (DFS_it_upd1 st)))
           < card (dVs (Graph.digraph_abs G) - seen_abstract (seen st))"
      using Graph.finite_vertices[OF graph_inv] by (auto intro: psubset_card_mono)
    thus "DFS_it_dom (DFS_it_upd1 st)"
      by (intro IH(1)[OF _ invar_it_holds(1)[OF IH(2) c]]) simp
  next
    assume c: "DFS_it_call_2_conds st"
    obtain v stack_tl where stack: "stack st = v # stack_tl" and has: "nbs_has (its st) v"
      using c by (auto simp: DFS_it_call_2_conds_def split: list.splits)
    have K: "v \<in> K"
      using top_in_K[OF IH(2) stack] .
    have V: "v \<in> dVs (Graph.digraph_abs G)"
      using stack invs by auto
    have C: "nbs_invar (its st)" "nbs_abstract (its st) v = t_set (\<N>\<^sub>G v)"
      using IH(2) K by (auto simp: invar_it_def)
    have rem: "nbs_remaining (its st) v \<noteq> {}"
      using current_in_neighbourhood(1)[OF IH(2) K has] .
    have "finite (nbs_remaining (its st) v)"
      using nbs.idx_partition_union[OF C(1) K] C(2) Graph.finite_neighbourhoods[OF graph_inv(3)]
      by (metis finite_Un)
    hence "card (nbs_remaining (its (DFS_it_upd2 st)) v) < card (nbs_remaining (its st) v)"
      using card_Diff1_less[OF _ nbs.idx_current[OF C(1) K rem]] nbs.idx_move_remaining[OF C(1) K rem]
      by (simp add: DFS_it_upd2_def stack)
    moreover have "nbs_remaining (its (DFS_it_upd2 st)) w = nbs_remaining (its st) w"
      if "w \<noteq> v" for w
      using nbs.idx_move_remaining_other[OF C(1) K rem that] by (simp add: DFS_it_upd2_def stack)
    ultimately have "(\<Sum>w\<in>dVs (Graph.digraph_abs G). card (nbs_remaining (its (DFS_it_upd2 st)) w))
                     < (\<Sum>w\<in>dVs (Graph.digraph_abs G). card (nbs_remaining (its st) w))"
      using V Graph.finite_vertices[OF graph_inv]
      by (intro sum_strict_mono_ex1) (assumption, metis less_imp_le order.refl, blast)
    thus "DFS_it_dom (DFS_it_upd2 st)"
      by (intro IH(1)[OF _ invar_it_holds(2)[OF IH(2) c]]) (simp add: DFS_it_upd2_def)
  next
    assume c: "DFS_it_call_3_conds st"
    show "DFS_it_dom (DFS_it_upd3 st)"
      using c
      by (intro IH(1)[OF _ invar_it_holds(3)[OF IH(2) c]])
         (auto simp: DFS_it_upd3_def elim!: call_cond_elims)
  qed
qed

subsubsection \<open>Relation to the original DFS\<close>

text \<open>If, in the states the run passes through, the iterators choose the neighbour that the original
      DFS selects, the iterator version simulates the original one and inherits its correctness.\<close>

context
  assumes nbs_sel:
      "\<And>st v stack_tl X. \<lbrakk>DFS_it_step\<^sup>*\<^sup>* initial_state_it st; DFS_it_call_1_conds st;
         stack st = v # stack_tl; vset_inv X; t_set X = seen_abstract (seen st)\<rbrakk> \<Longrightarrow>
         nbs_current (its st) v = sel (\<N>\<^sub>G v -\<^sub>G X)"
begin

lemma DFS_it_call_1_step:
  assumes "DFS_it_call_1_conds st" "invar_it st" "DFS_it_step\<^sup>*\<^sup>* initial_state_it st"
          "state_rel_it ds st" "invar_1 ds"
  shows "DFS_call_1_conds ds" "state_rel_it (DFS_upd1 ds) (DFS_it_upd1 st)"
proof-
  obtain v stack_tl where stack: "stack st = v # stack_tl" and "v \<noteq> t"
    and has: "nbs_has (its st) v" and unseen: "\<not> seen_isin (seen st) (nbs_current (its st) v)"
    using assms(1) by (auto simp: DFS_it_call_1_conds_def split: list.splits)
  define u where "u = nbs_current (its st) v"
  have K: "v \<in> K"
    using top_in_K[OF assms(2) stack] .
  have invs: "seen_invar (seen st)"
    using assms(2) by (auto simp: invar_it_def)
  have u_N: "u \<in> t_set (\<N>\<^sub>G v)"
    using current_in_neighbourhood(2)[OF assms(2) K has] by (auto simp: u_def)
  have seen_rel: "t_set (seen ds) = seen_abstract (seen st)" "stack ds = stack st"
    using assms(4) by (auto simp: state_rel_it_def)
  have u_unseen: "u \<notin> t_set (seen ds)"
    using unseen seen_set.fixed_univ_set_isin[OF invs(1)] seen_rel(1) by (simp add: u_def)
  have seen_inv: "vset_inv (seen ds)"
    using assms(5) by (auto elim!: invar_props_elims)
  have diff: "t_set (\<N>\<^sub>G v -\<^sub>G seen ds) = t_set (\<N>\<^sub>G v) - t_set (seen ds)"
    using set_ops.set_diff[OF _ seen_inv] by simp
  hence "\<N>\<^sub>G v -\<^sub>G seen ds \<noteq> \<emptyset>\<^sub>N"
    using u_N u_unseen Graph.vset.emptyD(1) by blast
  thus "DFS_call_1_conds ds"
    using stack \<open>v \<noteq> t\<close> seen_rel(2) by (simp add: DFS_call_1_conds_def)
  have u_sel: "u = sel (\<N>\<^sub>G v -\<^sub>G seen ds)"
    using nbs_sel[OF assms(3,1) stack seen_inv seen_rel(1)] by (simp add: u_def)
  have U: "u \<in> U"
    using u_N vertices_in_U by auto
  have new_seen: "seen_abstract (seen_insert u (seen st)) = Set.insert u (seen_abstract (seen st))"
    using seen_set.fixed_univ_set_insert(2)[OF invs(1) U] .
  show "state_rel_it (DFS_upd1 ds) (DFS_it_upd1 st)"
    using seen_rel assms(4) new_seen
    by (simp add: state_rel_it_def DFS_upd1_def DFS_it_upd1_def Let_def stack
                  u_def[symmetric] u_sel[symmetric] Graph.vset.set.set_insert[OF seen_inv])
qed

lemma DFS_it_call_3_step:
  assumes "DFS_it_call_3_conds st" "invar_it st" "state_rel_it ds st" "invar_1 ds"
  shows "DFS_call_2_conds ds" "state_rel_it (DFS_upd2 ds) (DFS_it_upd3 st)"
proof-
  obtain v stack_tl where stack: "stack st = v # stack_tl" and "v \<noteq> t"
    and has: "\<not> nbs_has (its st) v"
    using assms(1) by (auto simp: DFS_it_call_3_conds_def split: list.splits)
  have K: "v \<in> K"
    using top_in_K[OF assms(2) stack] .
  have invs: "nbs_invar (its st)" "nbs_abstract (its st) v = t_set (\<N>\<^sub>G v)"
    "nbs_iterated (its st) v \<subseteq> seen_abstract (seen st)"
    using assms(2) K by (auto simp: invar_it_def)
  have seen_inv: "vset_inv (seen ds)"
    using assms(4) by (auto elim!: invar_props_elims)
  have "t_set (\<N>\<^sub>G v) \<subseteq> t_set (seen ds)"
    using nbs.idx_has[OF invs(1) K] nbs.idx_partition_union[OF invs(1) K] has invs(2,3) assms(3)
    by (auto simp: state_rel_it_def)
  hence "t_set (\<N>\<^sub>G v -\<^sub>G seen ds) = {}"
    using set_ops.set_diff[OF Graph.neighbourhood_invars'[OF graph_inv(1)] seen_inv] by auto
  hence "\<N>\<^sub>G v -\<^sub>G seen ds = \<emptyset>\<^sub>N"
    using Graph.vset.emptyD(2)[OF _ set_ops.invar_diff[OF Graph.neighbourhood_invars'[OF graph_inv(1)]
                                                           seen_inv]]
    by blast
  thus "DFS_call_2_conds ds"
    using stack \<open>v \<noteq> t\<close> assms(3) by (simp add: DFS_call_2_conds_def state_rel_it_def)
  show "state_rel_it (DFS_upd2 ds) (DFS_it_upd3 st)"
    using assms(3) by (simp add: state_rel_it_def DFS_upd2_def DFS_it_upd3_def)
qed

lemma DFS_it_ret_1_step:
  assumes "DFS_it_ret_1_conds st" "state_rel_it ds st"
  shows "DFS_ret_1_conds ds" "state_rel_it (DFS_ret1 ds) (DFS_it_ret1 st)"
  using assms
  by (auto simp: DFS_it_ret_1_conds_def state_rel_it_def DFS_ret1_def DFS_it_ret1_def
          intro: call_cond_intros)

lemma DFS_it_ret_2_step:
  assumes "DFS_it_ret_2_conds st" "state_rel_it ds st"
  shows "DFS_ret_2_conds ds" "state_rel_it (DFS_ret2 ds) (DFS_it_ret2 st)"
  using assms
  by (auto simp: DFS_it_ret_2_conds_def state_rel_it_def DFS_ret2_def DFS_it_ret2_def
          intro: call_cond_intros split: list.splits)

lemma state_rel_it_holds:
  assumes "DFS_it_dom st" "invar_it st" "DFS_it_step\<^sup>*\<^sup>* initial_state_it st" "state_rel_it ds st"
          "invar_1 ds" "invar_seen_stack ds"
  shows "state_rel_it (DFS ds) (DFS_it st)"
  using assms(2-)
proof(induction arbitrary: ds rule: DFS_it_induct[OF assms(1)])
  case IH: (1 st)
  have dom: "DFS_dom ds"
    using IH(8,9) by (rule DFS_terminates)
  have reach: "DFS_it_step\<^sup>*\<^sup>* initial_state_it st'" if "DFS_it_step st st'" for st'
    using IH(6) that by (rule rtranclp.rtrancl_into_rtrancl)
  show ?case
  proof(rule DFS_it_cases[where dfs_state = st])
    assume c: "DFS_it_call_1_conds st"
    note s = DFS_it_call_1_step[OF c IH(5-8)]
    show ?thesis
      using IH(2)[OF c invar_it_holds(1)[OF IH(5) c] reach s(2) invar_1_holds_1[OF s(1) IH(8)]
                     invar_seen_stack_holds_1[OF s(1) IH(8,9)]] c
      by (simp add: DFS_it_simps(1)[OF IH(1) c] DFS_simps(1)[OF dom s(1)] DFS_it_step_def)
  next
    assume c: "DFS_it_call_2_conds st"
    show ?thesis
      using IH(3)[OF c invar_it_holds(2)[OF IH(5) c] reach _ IH(8,9)] IH(7) c
      by (simp add: DFS_it_simps(2)[OF IH(1) c] state_rel_it_def DFS_it_upd2_def DFS_it_step_def)
  next
    assume c: "DFS_it_call_3_conds st"
    note s = DFS_it_call_3_step[OF c IH(5,7,8)]
    show ?thesis
      using IH(4)[OF c invar_it_holds(3)[OF IH(5) c] reach s(2) invar_1_holds_2[OF s(1) IH(8)]
                     invar_seen_stack_holds_2[OF s(1) IH(8,9)]] c
      by (simp add: DFS_it_simps(3)[OF IH(1) c] DFS_simps(2)[OF dom s(1)] DFS_it_step_def)
  next
    assume c: "DFS_it_ret_1_conds st"
    note s = DFS_it_ret_1_step[OF c IH(7)]
    show ?thesis
      using s(2) by (simp add: DFS_it_simps(4)[OF IH(1) c] DFS_simps(3)[OF dom s(1)])
  next
    assume c: "DFS_it_ret_2_conds st"
    note s = DFS_it_ret_2_step[OF c IH(7)]
    show ?thesis
      using s(2) by (simp add: DFS_it_simps(5)[OF IH(1) c] DFS_simps(4)[OF dom s(1)])
  qed
qed

lemma initial_state_it_rel: "state_rel_it initial_state initial_state_it"
proof-
  have U: "s \<in> U"
    using vertices_in_U by blast
  show ?thesis
    using seen_set.fixed_univ_set_insert(2)[OF seen_set.fixed_univ_set_empty(1) U]
    by (simp add: state_rel_it_def initial_state_def initial_state_it_def
                  seen_set.fixed_univ_set_empty(2) Graph.vset.set.set_insert Graph.vset.set.invar_empty
                  Graph.vset.set.set_empty)
qed

lemma DFS_it_simulates_DFS:
  "state_rel_it (DFS initial_state) (DFS_it initial_state_it)"
  using state_rel_it_holds[OF DFS_it_terminates[OF invar_it_initial] invar_it_initial rtranclp.rtrancl_refl
                              initial_state_it_rel initial_state_props(1,3)] .

subsubsection \<open>Correctness\<close>

lemma DFS_it_correct_1:
  assumes "return (DFS_it initial_state_it) = NotReachable"
  shows   "\<nexists>p. distinct p \<and> vwalk_bet (Graph.digraph_abs G) s p t"
  using DFS_correct_1 assms DFS_it_simulates_DFS by (simp add: state_rel_it_def)

lemma DFS_it_correct_1_strong:
  assumes "return (DFS_it initial_state_it) = NotReachable"
  shows   "\<nexists>p. vwalk_bet (Graph.digraph_abs G) s p t"
  using DFS_correct_1_strong assms DFS_it_simulates_DFS by (simp add: state_rel_it_def)

lemma DFS_it_correct_2:
  assumes "return (DFS_it initial_state_it) = Reachable"
  shows "vwalk_bet (Graph.digraph_abs G) s (rev (stack (DFS_it initial_state_it))) t"
        "distinct (rev (stack (DFS_it initial_state_it)))"
  using DFS_correct_2 assms DFS_it_simulates_DFS by (simp add: state_rel_it_def)+

end

end

end
