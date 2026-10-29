theory BFS_3
  imports Directed_Set_Graphs.Pair_Graph_Specs "HOL-Eisbach.Eisbach_Tools" Directed_Set_Graphs.Dist
          Data_Structures.Set2_Addons Data_Structures.More_Lists
          Parent_Map_Spec
begin

hide_const  Undirected_Set_Graphs.neighbourhood

record ('parents, 'vset) BFS_state = parents:: "'parents" current:: "'vset" visited:: "'vset"

locale BFS =
  Graph: Pair_Graph_Specs
    where lookup = lookup +
  set_ops: Set2 vset_empty vset_delete _ t_set vset_inv insert
  
for lookup :: "'adjmap \<Rightarrow> 'ver \<Rightarrow> 'vset option" +

fixes  
srcs::"'vset" and
G::"'adjmap" and expand_tree::"'adjmap \<Rightarrow> 'vset \<Rightarrow> 'vset \<Rightarrow> 'adjmap" and
next_frontier_and_current::"'vset \<Rightarrow> 'vset \<Rightarrow> ('vset \<times> 'vset )" and
vset_inv2::"'vset \<Rightarrow> bool"


assumes
   expand_tree[simp]:
     "\<lbrakk>Graph.graph_inv BFS_tree; vset_inv2 frontier; vset_inv vis; Graph.graph_inv G; t_set frontier \<subseteq> t_set vis;
       t_set vis \<subseteq> dVs (Graph.digraph_abs G)\<rbrakk> \<Longrightarrow> 
       Graph.graph_inv (expand_tree BFS_tree frontier vis)"
     "\<lbrakk>Graph.graph_inv BFS_tree; vset_inv2 frontier; vset_inv vis; Graph.graph_inv G; t_set frontier \<subseteq> t_set vis;
      t_set vis \<subseteq> dVs (Graph.digraph_abs G)\<rbrakk> \<Longrightarrow>
        Graph.digraph_abs (expand_tree BFS_tree frontier vis) = 
         (Graph.digraph_abs BFS_tree) \<union> 
         {(u,v) | u v. u \<in> t_set (frontier) \<and> 
                       v \<in> (Pair_Graph.neighbourhood (Graph.digraph_abs G) u -
                       t_set vis)}"
    "\<lbrakk>Graph.graph_inv BFS_tree; vset_inv2 frontier; vset_inv vis; Graph.graph_inv G;
        Graph.finite_graph BFS_tree; t_set frontier \<subseteq> t_set vis; t_set vis \<subseteq> dVs (Graph.digraph_abs G)\<rbrakk> \<Longrightarrow> 
        Graph.finite_graph (expand_tree BFS_tree frontier vis)"
   and next_frontier:
    "\<And> front' vis'. \<lbrakk>vset_inv2 frontier; vset_inv vis; Graph.graph_inv G; t_set frontier \<subseteq> t_set vis;
      next_frontier_and_current frontier vis = (front', vis');t_set vis \<subseteq> dVs (Graph.digraph_abs G)\<rbrakk>
       \<Longrightarrow>  vset_inv2 front'"
    "\<And> front' vis'. \<lbrakk>vset_inv2 frontier; vset_inv vis; Graph.graph_inv G; t_set frontier \<subseteq> t_set vis;
     next_frontier_and_current frontier vis = (front', vis'); t_set vis \<subseteq> dVs (Graph.digraph_abs G)\<rbrakk> \<Longrightarrow>
       t_set front' =
         (\<Union> {Pair_Graph.neighbourhood (Graph.digraph_abs G) u | u . u \<in> t_set frontier}) - t_set vis"
  and next_vis:
    "\<And> front' vis'. \<lbrakk>vset_inv2 frontier; vset_inv vis; Graph.graph_inv G; t_set frontier \<subseteq> t_set vis;
     next_frontier_and_current frontier vis = (front', vis'); t_set vis \<subseteq> dVs (Graph.digraph_abs G)\<rbrakk> 
      \<Longrightarrow> vset_inv vis'"
    "\<And> front' vis'. \<lbrakk>vset_inv2 frontier; vset_inv vis; Graph.graph_inv G; t_set frontier \<subseteq> t_set vis;
     next_frontier_and_current frontier vis = (front', vis');t_set vis \<subseteq> dVs (Graph.digraph_abs G)\<rbrakk> \<Longrightarrow>
       t_set vis' = t_set vis \<union> t_set front'"
and vset_inv2[intro]: "\<And> S. vset_inv2 S \<Longrightarrow> vset_inv S"
begin

definition "BFS_axiom \<longleftrightarrow>
  Graph.graph_inv G \<and> Graph.finite_graph G \<and> Graph.finite_vsets G \<and>
  t_set srcs \<subseteq> dVs (Graph.digraph_abs G) \<and>
  (\<forall>u. finite (Pair_Graph.neighbourhood (Graph.digraph_abs G) u)) \<and>
  t_set srcs \<noteq> {} \<and> vset_inv2 srcs"

abbreviation "neighbourhood' \<equiv> Graph.neighbourhood G" 
notation "neighbourhood'" ("\<N>\<^sub>G _" 100)


function (domintros) BFS::"('adjmap, 'vset) BFS_state \<Rightarrow> ('adjmap, 'vset) BFS_state" where
  "BFS BFS_state = 
     (
        if current BFS_state \<noteq> \<emptyset>\<^sub>N then
          let
          parents' = expand_tree (parents BFS_state) (current BFS_state) (visited BFS_state);
          (current', visited') =  next_frontier_and_current (current BFS_state)  (visited BFS_state)
          in 
            BFS (BFS_state \<lparr>parents:= parents', visited := visited', current := current'\<rparr>)
         else
          BFS_state)"
  by pat_completeness auto

partial_function (tailrec) BFS_impl::"('adjmap, 'vset) BFS_state \<Rightarrow> ('adjmap, 'vset) BFS_state" where
  "BFS_impl BFS_state = 
     (
        if current BFS_state \<noteq> \<emptyset>\<^sub>N then
          let
          parents' = expand_tree (parents BFS_state) (current BFS_state) (visited BFS_state);
          (current', visited') =  next_frontier_and_current (current BFS_state)  (visited BFS_state)
          in 
            BFS_impl (BFS_state \<lparr>parents:= parents', visited := visited', current := current'\<rparr>)
         else
          BFS_state)"

lemma BFS_impl_same:
  assumes "BFS_dom state" 
  shows "BFS_impl state = BFS state"
proof(induction rule: BFS.pinduct[OF assms])
  case (1 BFS_state)
  show ?case
  proof(cases "next_frontier_and_current  (current BFS_state) (visited BFS_state)")
    case (Pair current' visited')
    then show ?thesis
      by(auto intro!: 1(2) simp add: BFS_impl.simps[of BFS_state] BFS.psimps[OF 1(1)] Let_def)
  qed
qed

definition "BFS_call_1_conds bfs_state = ( (current bfs_state) \<noteq> \<emptyset>\<^sub>N)"

definition "BFS_upd1 BFS_state =
(        let
          parents' = expand_tree (parents BFS_state) (current BFS_state) (visited BFS_state);
          (current', visited') =  next_frontier_and_current (current BFS_state)  (visited BFS_state)
        in 
          BFS_state \<lparr>parents:= parents', visited := visited', current := current'\<rparr>

)" 


definition "BFS_ret_1_conds bfs_state = ((current bfs_state) = \<emptyset>\<^sub>N)"

abbreviation "BFS_ret1 bfs_state \<equiv> bfs_state"


definition "invar_1 bfs_state = (
              vset_inv (visited bfs_state) \<and> vset_inv2 (current bfs_state) \<and>
              Graph.graph_inv (parents bfs_state) \<and> 
              Graph.finite_graph (parents bfs_state) \<and>
              finite (t_set (current bfs_state)) \<and> finite (t_set (visited bfs_state)))"

lemma invar_1D:
  "invar_1 bfs_state \<Longrightarrow> vset_inv (visited bfs_state)"
  "invar_1 bfs_state \<Longrightarrow> vset_inv2 (current bfs_state)"
  "invar_1 bfs_state \<Longrightarrow> Graph.graph_inv (parents bfs_state)"
  "invar_1 bfs_state \<Longrightarrow> Graph.finite_graph (parents bfs_state)"
  "invar_1 bfs_state \<Longrightarrow> finite (t_set (current bfs_state))"
  "invar_1 bfs_state \<Longrightarrow> finite (t_set (visited bfs_state))"
  unfolding invar_1_def by auto

definition "invar_2 bfs_state = ( 
  Graph.digraph_abs (parents bfs_state) \<subseteq> Graph.digraph_abs G \<and> 
  t_set (visited bfs_state) \<subseteq> dVs (Graph.digraph_abs G) \<and> 
  t_set (current bfs_state) \<subseteq> dVs (Graph.digraph_abs G) \<and> 
  dVs (Graph.digraph_abs (parents bfs_state)) \<subseteq> t_set (visited bfs_state)  \<and>
  t_set srcs \<subseteq> t_set (visited bfs_state) 
  \<and> t_set (current bfs_state) \<subseteq> t_set (visited bfs_state))"

definition "invar_3_1 bfs_state = 
  (\<forall>v\<in>t_set (current bfs_state). \<forall>u. u \<in> t_set (current bfs_state) \<longleftrightarrow> 
      distance_set (Graph.digraph_abs G) (t_set srcs) v =
                           distance_set (Graph.digraph_abs G) (t_set srcs) u)"

definition "invar_3_2 bfs_state = 
  (\<forall>v\<in>t_set (current bfs_state). \<forall>u \<in> t_set (visited bfs_state) .
     distance_set (Graph.digraph_abs G) (t_set srcs) u \<le>
       distance_set (Graph.digraph_abs G) (t_set srcs) v)"

definition "invar_3_3 bfs_state = 
  (\<forall>v\<in>t_set (visited bfs_state) -  t_set (current bfs_state).
     neighbourhood (Graph.digraph_abs G) v \<subseteq> t_set (visited bfs_state))"

definition "invar_3_4 bfs_state = 
  (\<forall>v\<in> t_set (visited bfs_state) \<union> t_set (current bfs_state).
     \<forall>u. distance_set (Graph.digraph_abs G) (t_set srcs) u \<le>
           distance_set (Graph.digraph_abs G) (t_set srcs) v
             \<longrightarrow> u \<in> t_set (visited bfs_state) \<union> t_set (current bfs_state))"

definition "invar_goes_through_current bfs_state =
         (\<forall>u\<in>t_set (visited bfs_state) \<union> t_set (current bfs_state). 
            \<forall>v. v \<notin> t_set (visited bfs_state) \<union> t_set (current bfs_state) \<longrightarrow>
              (\<forall>p. Vwalk.vwalk_bet (Graph.digraph_abs G) u p v \<longrightarrow> 
                     set p \<inter> t_set (current bfs_state) \<noteq> {}))"

definition "invar_dist' bfs_state =
  (\<forall>v \<in> dVs (Graph.digraph_abs G) - t_set srcs.
     (v \<in> (t_set (visited bfs_state) \<union> t_set (current bfs_state)) \<longrightarrow> distance_set (Graph.digraph_abs G) (t_set srcs) v =
         distance_set (Graph.digraph_abs (parents bfs_state)) (t_set srcs) v))"

definition "invar_parents_shortest_paths bfs_state =
  (\<forall>u\<in>t_set srcs.
      \<forall> p v. Vwalk.vwalk_bet (Graph.digraph_abs (parents bfs_state)) u p v \<longrightarrow>
         length p - 1 = distance_set (Graph.digraph_abs G) (t_set srcs) v)"

definition "invar_parents_in_level_graph state = 
           ((Graph.digraph_abs (parents state)) \<subseteq>
             level_graph (Graph.digraph_abs G) (t_set srcs))"

definition "call_1_measure_1 BFS_state=
  card (dVs (Graph.digraph_abs G) - (t_set (visited BFS_state)))"

definition "call_1_measure_2 BFS_state =
  card (t_set (current BFS_state))"

definition
  "BFS_term_rel' = call_1_measure_1 <*mlex*> call_1_measure_2 <*mlex*> {}"

definition "initial_state = \<lparr>parents =  empty, current = srcs, visited = srcs\<rparr>"

lemmas[code] = BFS_impl.simps initial_state_def

context
  includes Graph.adjmap.automation and Graph.vset.set.automation and set_ops.automation2
  assumes BFS_axiom  
begin

lemma graph_inv[simp]:
     "Graph.graph_inv G" 
     "Graph.finite_graph G"
     "Graph.finite_vsets G" and
   srcs_in_G[simp,intro]: 
     "t_set srcs \<subseteq> dVs (Graph.digraph_abs G)" and
   finite_vset:
     "finite (Pair_Graph.neighbourhood (Graph.digraph_abs G) u)" and
  srcs_invar[simp]:
     "t_set srcs \<noteq> {}" 
     "vset_inv2 srcs"
  using \<open>BFS_axiom\<close>
  by (auto simp: BFS_axiom_def)

named_theorems call_cond_elims
named_theorems call_cond_intros
named_theorems ret_holds_intros
named_theorems invar_props_intros
named_theorems invar_props_elims
named_theorems invar_holds_intros
named_theorems state_rel_intros
named_theorems state_rel_holds_intros


lemma BFS_call_1_conds[call_cond_elims]: 
  "BFS_call_1_conds bfs_state \<Longrightarrow> 
   \<lbrakk>(current bfs_state) \<noteq> \<emptyset>\<^sub>N \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by(auto simp: BFS_call_1_conds_def split: list.splits option.splits if_splits)


lemma BFS_ret_1_conds[call_cond_elims]:
  "BFS_ret_1_conds bfs_state \<Longrightarrow> 
   \<lbrakk>(current bfs_state) = \<emptyset>\<^sub>N \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by(auto simp: BFS_ret_1_conds_def split: list.splits option.splits if_splits)

lemma BFS_ret_1_condsI[call_cond_intros]:
  "\<lbrakk>(current bfs_state) = \<emptyset>\<^sub>N\<rbrakk> \<Longrightarrow> BFS_ret_1_conds bfs_state"
  by(auto simp: BFS_ret_1_conds_def split: list.splits option.splits if_splits)

lemma BFS_cases:
  assumes "BFS_call_1_conds bfs_state \<Longrightarrow> P"
      "BFS_ret_1_conds bfs_state \<Longrightarrow> P"
  shows "P"
proof-
  have "BFS_call_1_conds bfs_state \<or>
        BFS_ret_1_conds bfs_state"
    by (auto simp add: BFS_call_1_conds_def
                        BFS_ret_1_conds_def
           split: list.split_asm option.split_asm if_splits)
  then show ?thesis
    using assms
    by auto
qed

lemma BFS_simps:
  assumes "BFS_dom BFS_state" 
  shows"BFS_call_1_conds BFS_state \<Longrightarrow> BFS BFS_state = BFS (BFS_upd1 BFS_state)"
      "BFS_ret_1_conds BFS_state \<Longrightarrow> BFS BFS_state = BFS_ret1 BFS_state"
  by (auto simp add: BFS.psimps[OF assms]
                     BFS_call_1_conds_def BFS_upd1_def 
                     BFS_ret_1_conds_def Let_def
            split: list.splits option.splits if_splits prod.split)

lemma BFS_induct: 
  assumes "BFS_dom bfs_state"
  assumes "\<And>bfs_state. \<lbrakk>BFS_dom bfs_state;
                        (BFS_call_1_conds bfs_state \<Longrightarrow> P (BFS_upd1 bfs_state))\<rbrakk>
              \<Longrightarrow> P bfs_state"
  shows "P bfs_state"
  apply(rule BFS.pinduct)
  subgoal using assms(1) .
  apply(rule assms(2))
  by (auto simp add: BFS_call_1_conds_def BFS_upd1_def Let_def
           split: list.splits option.splits if_splits prod.split)

lemma BFS_domintros: 
  assumes "BFS_call_1_conds BFS_state \<Longrightarrow> BFS_dom (BFS_upd1 BFS_state)"
  shows "BFS_dom BFS_state"
proof(rule BFS.domintros, goal_cases)
  case (1 a b xb ya)
  show ?case
    using assms(1)[simplified BFS_call_1_conds_def BFS_upd1_def] 1(1,3)
    by (force simp add: Let_def 1(2)[symmetric] split: list.splits option.splits if_splits)
qed

lemma invar_1_props[invar_props_elims]: 
  "invar_1 bfs_state \<Longrightarrow> 
  (\<lbrakk>vset_inv (visited bfs_state) ; vset_inv2 (current bfs_state) ;
    Graph.graph_inv (parents bfs_state); 
    finite (t_set (current bfs_state)); finite (t_set (visited bfs_state));
    Graph.finite_graph (parents bfs_state)\<rbrakk> \<Longrightarrow> P)
     \<Longrightarrow> P"
  by (auto simp: invar_1_def)

lemma invar_2_props[invar_props_elims]: 
  "invar_2 bfs_state \<Longrightarrow> 
  (\<lbrakk>Graph.digraph_abs (parents bfs_state) \<subseteq> Graph.digraph_abs G;
    t_set (visited bfs_state) \<subseteq> dVs (Graph.digraph_abs G);
    t_set (current bfs_state) \<subseteq> dVs (Graph.digraph_abs G);
    dVs (Graph.digraph_abs (parents bfs_state)) \<subseteq> t_set (visited bfs_state) ;
     dVs (Graph.digraph_abs (parents bfs_state)) \<subseteq> t_set (visited bfs_state) \<union> t_set (current bfs_state);
    t_set srcs \<subseteq> t_set (visited bfs_state); t_set srcs \<subseteq> t_set (visited bfs_state) \<union> t_set (current bfs_state);
      t_set (current bfs_state) \<subseteq> t_set (visited bfs_state)\<rbrakk> \<Longrightarrow> P)
     \<Longrightarrow> P"
  by (force simp: invar_2_def)

lemma invar_1_intro[invar_props_intros]:
  "\<lbrakk>vset_inv (visited bfs_state); vset_inv2 (current bfs_state);
    Graph.graph_inv (parents bfs_state);
    finite (t_set (current bfs_state)); finite (t_set (visited bfs_state));
    Graph.finite_graph (parents bfs_state)\<rbrakk> 
    \<Longrightarrow> invar_1 bfs_state"
  by (auto simp: invar_1_def)

lemma finite_simp:
   "{(u,v). u \<in> front \<and> v \<in> (Pair_Graph.neighbourhood (Graph.digraph_abs G) u) \<and> v \<notin> vis} = 
       {(u,v). u \<in> front} \<inter> {(u,v). v \<in> (Pair_Graph.neighbourhood (Graph.digraph_abs G) u)} - {(u,v) . v \<in> vis}"
   "finite {(u, v)| v . v \<in> (s u)} = finite (s u)"
  using finite_image_iff[where f = snd and A = "{(u, v) |v. v \<in> s u}"]
  by (auto simp: inj_on_def image_def)
  
lemma invar_1_holds_upd1[invar_holds_intros]:
  "\<lbrakk>BFS_call_1_conds bfs_state; invar_1 bfs_state; invar_2 bfs_state\<rbrakk> \<Longrightarrow> invar_1 (BFS_upd1 bfs_state)"
  using finite_vset
proof(cases "next_frontier_and_current (current bfs_state) (visited bfs_state)", goal_cases)
  case (1 front' vis')
  note next_vis = next_vis[OF _ _ _ _ 1(5)]
  note next_front = next_frontier[OF _ _ _ _ 1(5)]
  show ?case
    using 1
    by(auto elim!: invar_1_props invar_2_props call_cond_elims 
             simp: Let_def BFS_upd1_def BFS_call_1_conds_def  next_vis next_front 
           intro!: invar_props_intros
            split: prod.split)+
qed

lemma invar_1_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_1 bfs_state\<rbrakk> \<Longrightarrow> invar_1 (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)
  
lemma invar_2_intro[invar_props_intros]:
   "\<lbrakk>Graph.digraph_abs (parents bfs_state) \<subseteq> Graph.digraph_abs G;
     t_set (visited bfs_state) \<subseteq> dVs (Graph.digraph_abs G);
     t_set (current bfs_state) \<subseteq> dVs (Graph.digraph_abs G);
     dVs (Graph.digraph_abs (parents bfs_state)) \<subseteq> t_set (visited bfs_state) \<union> t_set (current bfs_state);
     t_set srcs \<subseteq> t_set (visited bfs_state) \<union> t_set (current bfs_state);
     t_set (current bfs_state) \<subseteq> t_set (visited bfs_state) \<rbrakk>
     \<Longrightarrow> invar_2 bfs_state"
  by (auto simp: invar_2_def)

lemma invar_2_holds_upd1[invar_holds_intros]: 
  "\<lbrakk>BFS_call_1_conds bfs_state; invar_1 bfs_state; invar_2 bfs_state\<rbrakk> \<Longrightarrow> invar_2 (BFS_upd1 bfs_state)"
proof(cases "next_frontier_and_current (current bfs_state) (visited bfs_state)", goal_cases)
  case (1 front' vis')
  note next_vis[simp] = next_vis[OF _ _ _ _ 1(4)]
  note next_front[simp] = next_frontier[OF _ _ _ _ 1(4)]
  show ?case
    using 1
  apply(auto elim!: call_cond_elims invar_1_props invar_2_props
            intro!: invar_props_intros 
              simp: BFS_upd1_def Let_def )
   apply(auto simp: dVs_def) 
  by blast+
qed

lemma invar_2_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_2 bfs_state\<rbrakk> \<Longrightarrow> invar_2 (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_1_holds[invar_holds_intros]:
   assumes "BFS_dom bfs_state" "invar_1 bfs_state" "invar_2 bfs_state"
   shows "invar_1 (BFS bfs_state)"
  using assms(2-)
proof(induction rule: BFS_induct[OF assms(1)])
  case IH: (1 bfs_state)
  show ?case
    apply(rule BFS_cases[where bfs_state = bfs_state])
    by (auto intro!: IH(2-) intro: invar_holds_intros  simp: BFS_simps[OF IH(1)])
qed

lemma invar_2_holds[invar_holds_intros]:
   assumes "BFS_dom bfs_state" "invar_1 bfs_state" "invar_2 bfs_state"
   shows "invar_2 (BFS bfs_state)"
  using assms(2-)
proof(induction rule: BFS_induct[OF assms(1)])
  case IH: (1 bfs_state)
  show ?case
    apply(rule BFS_cases[where bfs_state = bfs_state])
    by (auto intro!: IH(2-) intro: invar_holds_intros  simp: BFS_simps[OF IH(1)])
qed

\<comment> \<open>This is invar\_100 on the board\<close>

lemma invar_3_1_props[invar_props_elims]: 
  "invar_3_1 bfs_state \<Longrightarrow>
  (\<lbrakk>\<lbrakk>v \<in> t_set (current bfs_state); u \<in> t_set (current bfs_state)\<rbrakk> \<Longrightarrow>
            distance_set (Graph.digraph_abs G) (t_set srcs) v =
                 distance_set (Graph.digraph_abs G) (t_set srcs) u;
    \<lbrakk>v \<in> t_set (current bfs_state);
            distance_set (Graph.digraph_abs G) (t_set srcs) v = 
              distance_set (Graph.digraph_abs G) (t_set srcs) u\<rbrakk> \<Longrightarrow>
            u \<in> t_set (current bfs_state)\<rbrakk> \<Longrightarrow> P)
     \<Longrightarrow> P"
  unfolding invar_3_1_def
  by blast

lemma invar_3_1_intro[invar_props_intros]:
   "\<lbrakk>\<And>u v. \<lbrakk>v \<in> t_set (current bfs_state); u \<in> t_set (current bfs_state)\<rbrakk> \<Longrightarrow>
            distance_set (Graph.digraph_abs G) (t_set srcs) v =
                           distance_set (Graph.digraph_abs G) (t_set srcs) u;
     \<And>u v. \<lbrakk>v \<in> t_set (current bfs_state); distance_set (Graph.digraph_abs G) (t_set srcs) v =
                 distance_set (Graph.digraph_abs G) (t_set srcs) u\<rbrakk> \<Longrightarrow>
            u \<in> t_set (current bfs_state)\<rbrakk>
    \<Longrightarrow> invar_3_1 bfs_state"
  unfolding invar_3_1_def
  by blast

lemma invar_3_2_props[elim]: 
  "invar_3_2 bfs_state \<Longrightarrow> 
  (\<lbrakk>\<And>v u. \<lbrakk>v\<in>t_set (current bfs_state); u \<in> t_set (visited bfs_state)\<rbrakk> \<Longrightarrow>
          distance_set (Graph.digraph_abs G) (t_set srcs) u \<le>
       distance_set (Graph.digraph_abs G) (t_set srcs) v\<rbrakk> \<Longrightarrow> P)
     \<Longrightarrow> P"
  unfolding invar_3_2_def
  by blast

lemma invar_3_2_intro[invar_props_intros]:
   "\<lbrakk>\<And>v u. \<lbrakk>v\<in>t_set (current bfs_state); u \<in> t_set (visited bfs_state) \<union> t_set (current bfs_state)\<rbrakk> \<Longrightarrow>
          distance_set (Graph.digraph_abs G) (t_set srcs) u \<le>
       distance_set (Graph.digraph_abs G) (t_set srcs) v\<rbrakk>
    \<Longrightarrow> invar_3_2 bfs_state"
  unfolding invar_3_2_def
  by blast

lemma invar_3_3_props[invar_props_elims]: 
  "invar_3_3 bfs_state \<Longrightarrow> 
  (\<lbrakk>\<And>v. \<lbrakk>v \<in> t_set (visited bfs_state); v \<notin> t_set (current bfs_state)\<rbrakk> \<Longrightarrow>
          neighbourhood (Graph.digraph_abs G) v \<subseteq> t_set (visited bfs_state) \<union> t_set (current bfs_state)\<rbrakk> \<Longrightarrow> P)
     \<Longrightarrow> P"
  unfolding invar_3_3_def
  by blast

lemma invar_3_3_intro[invar_props_intros]:
   "\<lbrakk>\<And>v. \<lbrakk>v \<in> t_set (visited bfs_state); v \<notin> t_set (current bfs_state)\<rbrakk> \<Longrightarrow>
          neighbourhood (Graph.digraph_abs G) v \<subseteq> t_set (visited bfs_state)\<rbrakk>
    \<Longrightarrow> invar_3_3 bfs_state"
  unfolding invar_3_3_def 
  by blast

\<comment> \<open>This is invar 4 on the board\<close>


lemma invar_3_4_props[invar_props_elims]: 
  "invar_3_4 bfs_state \<Longrightarrow> 
  (\<lbrakk>\<And>u v. \<lbrakk>v\<in> t_set (visited bfs_state) \<union> t_set (current bfs_state);
             distance_set (Graph.digraph_abs G) (t_set srcs) u \<le> distance_set (Graph.digraph_abs G) (t_set srcs) v\<rbrakk> \<Longrightarrow>
            u \<in> t_set (visited bfs_state) \<union> t_set (current bfs_state)\<rbrakk> \<Longrightarrow> P)
     \<Longrightarrow> P"
  unfolding invar_3_4_def
  by blast

lemma invar_3_4_intro[invar_props_intros]:
   "\<lbrakk>\<And>u v. \<lbrakk>v\<in> t_set (visited bfs_state) \<union> t_set (current bfs_state);
               distance_set (Graph.digraph_abs G) (t_set srcs) u \<le> distance_set (Graph.digraph_abs G) (t_set srcs) v\<rbrakk> \<Longrightarrow>
            u \<in> t_set (visited bfs_state) \<union> t_set (current bfs_state)\<rbrakk>
    \<Longrightarrow> invar_3_4 bfs_state"
  unfolding invar_3_4_def
  by blast

definition "invar_current_reachable bfs_state =
  (\<forall>v\<in> t_set (visited bfs_state) \<union> t_set (current bfs_state).
     distance_set (Graph.digraph_abs G) (t_set srcs) v < \<infinity>)"

lemma invar_current_reachable_props[invar_props_elims]: 
  "invar_current_reachable bfs_state \<Longrightarrow> 
  (\<lbrakk>\<And>v. \<lbrakk>v \<in> t_set (visited bfs_state) \<union> t_set (current bfs_state)\<rbrakk> \<Longrightarrow> 
         distance_set (Graph.digraph_abs G) (t_set srcs) v < \<infinity>\<rbrakk> \<Longrightarrow> P)
     \<Longrightarrow> P"
  by(auto simp: invar_current_reachable_def)

lemma invar_current_reachable_intro[invar_props_intros]:
   "\<lbrakk>\<And>v. \<lbrakk>v \<in> t_set (visited bfs_state) \<union> t_set (current bfs_state)\<rbrakk> \<Longrightarrow>
         distance_set (Graph.digraph_abs G) (t_set srcs) v < \<infinity>\<rbrakk> 
    \<Longrightarrow> invar_current_reachable bfs_state"
  by(auto simp add: invar_current_reachable_def)

lemma new_visited_simp:
  "\<lbrakk>invar_1 bfs_state; invar_2 bfs_state;
    next_frontier_and_current (current bfs_state) (visited bfs_state) = (x, y)\<rbrakk> \<Longrightarrow> 
   [visited bfs_state \<union>\<^sub>G x]\<^sub>s = 
   [visited bfs_state]\<^sub>s \<union> [x]\<^sub>s"
proof( goal_cases)
  case (1)
  note next_frontier[simp] = next_frontier[OF _ _ _ _ 1(3)]
  show ?case
    using 1
    by(subst set_ops.set_union)
      (auto intro!: next_frontier(1) elim!: invar_1_props invar_2_props)
qed

lemma invar_current_reachable_holds_upd1[invar_holds_intros]: 
  "\<lbrakk>BFS_call_1_conds bfs_state; invar_1 bfs_state; invar_2 bfs_state; invar_current_reachable bfs_state\<rbrakk>
     \<Longrightarrow> invar_current_reachable (BFS_upd1 bfs_state)"
proof(cases "next_frontier_and_current (current bfs_state) (visited bfs_state)",
      rule invar_props_intros, goal_cases)
  case assms: (1 front' vis' v)
  note new_visited_simp =  new_visited_simp[OF assms(2,3,5)]
  note next_vis[simp] = next_vis[OF _ _ _ _ assms(5)]
  note next_front[simp] = next_frontier[OF _ _ _ _ assms(5)]
  have ?case (is "?dist v < \<infinity>") if "v \<notin> t_set (visited bfs_state)"
  proof-
    have "v \<in> t_set (current (BFS_upd1 bfs_state))"
      using that assms
      by (auto simp add: BFS_upd1_def Let_def new_visited_simp elim!: invar_props_elims)
    then obtain u where "v \<in> t_set (\<N>\<^sub>G u)" "u \<in> t_set (current bfs_state)"
      using assms
      by (auto simp: BFS_upd1_def Let_def elim!: invar_props_elims)
    hence "?dist u < \<infinity>"
      using \<open>invar_2 bfs_state\<close> \<open>invar_current_reachable bfs_state\<close>
      by (auto elim!: invar_props_elims)
    hence "?dist v \<le> ?dist u + 1"
      using \<open>v \<in> t_set (\<N>\<^sub>G u)\<close>
      by (auto intro!: distance_set_neighbourhood)
    thus ?thesis
      using add_mono1[OF \<open>?dist u < \<infinity>\<close>] linorder_not_less
      by fastforce
  qed
  thus ?case
    using assms
    by(force elim!: call_cond_elims invar_props_elims intro!: invar_props_intros simp: BFS_upd1_def Let_def)
qed

lemma invar_current_reachable_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_current_reachable bfs_state\<rbrakk> \<Longrightarrow> invar_current_reachable (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_current_reachable_holds:
  assumes "BFS_dom state" "invar_1 state" "invar_2 state" "invar_current_reachable state"
  shows   "invar_current_reachable (BFS state)"
  using assms(2-)
proof(induction rule: BFS_induct[OF assms(1)])
  case IH: (1 bfs_state)
  show ?case
    apply(rule BFS_cases[where bfs_state = bfs_state])
    by (auto intro!: IH(2-) intro: invar_holds_intros  simp: BFS_simps[OF IH(1)])
qed

lemma dist_current_plus_1_new:                                               
  assumes
    "invar_1 bfs_state" "invar_2 bfs_state" "invar_3_4 bfs_state" 
    "v \<in> neighbourhood (Graph.digraph_abs G) v'" 
    "v' \<in> t_set (current bfs_state)"
    "v \<in> t_set (current (BFS_upd1 bfs_state))"
  shows  "distance_set (Graph.digraph_abs G) (t_set srcs) v = 
            distance_set (Graph.digraph_abs G) (t_set srcs) v' + 1" (is "?dv = ?dv' + 1")
proof(cases "next_frontier_and_current (current bfs_state) (visited bfs_state)", goal_cases)
  case (1 front' vis')
  note next_vis = next_vis[OF _ _ _ _ 1(1)]
  note next_front[simp] = next_frontier[OF _ _ _ _ 1(1)]
    have False if "?dv > ?dv' + 1"
      using distance_set_neighbourhood[OF \<open>v \<in> neighbourhood (Graph.digraph_abs G) v'\<close>] that
      by (simp add: leD)


    moreover have False if "?dv < ?dv' + 1"
    proof-
      have "?dv \<le> ?dv'"
        using that eSuc_plus_1 ileI1
        by force
      moreover have "?dv \<noteq> \<infinity>"
        using that enat_ord_simps(4) 
        by fastforce
      moreover have "v \<notin> t_set (visited bfs_state) \<union> t_set (current bfs_state)"
        using assms
        by (auto simp: BFS_upd1_def Let_def 1 elim!: invar_1_props invar_2_props )
 
      moreover have "v' \<in> t_set (visited bfs_state) \<union> t_set (current bfs_state)"
        using \<open>v' \<in> t_set (current bfs_state)\<close> \<open>invar_2 bfs_state\<close>
        by (auto elim!: invar_2_props)

      ultimately show False
        using \<open>invar_3_4 bfs_state\<close>
        apply(elim invar_props_elims)
        apply(drule dist_set_not_inf)
        using dual_order.trans dist_set_mem
        by (smt (verit, best))
    qed
    ultimately show ?thesis
      by force
  qed

lemma plus_lt_enat: "\<lbrakk>(a::enat) \<noteq> \<infinity>; b < c\<rbrakk> \<Longrightarrow> a + b < a + c"
  using enat_add_left_cancel_less
  by presburger

lemma plus_one_side_lt_enat: "\<lbrakk>(a::enat) \<noteq> \<infinity>; 0 < b\<rbrakk> \<Longrightarrow> a < a + b"
  using plus_lt_enat
  by auto

lemma invar_3_1_holds_upd1_new[invar_holds_intros]: 
  "\<lbrakk>BFS_call_1_conds bfs_state; invar_1 bfs_state; invar_2 bfs_state ; invar_3_1 bfs_state;
    invar_3_2 bfs_state; invar_3_4 bfs_state; invar_current_reachable bfs_state\<rbrakk>
     \<Longrightarrow> invar_3_1 (BFS_upd1 bfs_state)"
proof(cases "next_frontier_and_current (current bfs_state) (visited bfs_state)",
      intro invar_props_intros, goal_cases)
  case assms: (1 front' vis' u v)
  have current_in_vis:"t_set (current bfs_state) \<subseteq> t_set (visited bfs_state)" 
    using assms(3) by(auto elim: invar_2_props)
  have vis_in_G: "[visited bfs_state]\<^sub>s \<subseteq> dVs [G]\<^sub>g" 
    using assms(3) by(auto elim!: invar_2_props)
  note next_frontier[simp] = next_frontier(2)[OF _ _ _ current_in_vis assms(8) vis_in_G]
  obtain u' v' where
    uv'[intro]: "u \<in> neighbourhood (Graph.digraph_abs G) u'" "u' \<in> t_set (current bfs_state)" 
                "v \<in> neighbourhood (Graph.digraph_abs G) v'" "v' \<in> t_set (current bfs_state)"
    using assms(1,2,9,10) 
    by (auto simp: BFS_upd1_def Let_def assms(8) elim!: invar_1_props)
  moreover hence "distance_set (Graph.digraph_abs G) (t_set srcs) v' =
                    distance_set (Graph.digraph_abs G) (t_set srcs) u'" (is "?d v' = ?d u'")
    using \<open>invar_3_1 bfs_state\<close>
    by (auto elim: invar_props_elims)
  moreover have "distance_set (Graph.digraph_abs G) (t_set srcs) v = ?d v' + 1"
    using assms               
    by (auto intro!: dist_current_plus_1_new)
  moreover have "distance_set (Graph.digraph_abs G) (t_set srcs) u = ?d u' + 1"
    using assms
    by (auto intro!: dist_current_plus_1_new)
  ultimately show ?case
    by auto
next
  case (2 front' vis' u v)
  note next_frontier[simp] = next_frontier(2)[OF _ _ _ _ 2(8)]
  from 2 obtain v' where uv'[intro]:
    "v \<in> neighbourhood (Graph.digraph_abs G) v'" "v' \<in> t_set (current bfs_state)"    
    by (auto simp add: BFS_upd1_def Let_def elim!: invar_1_props invar_2_props)
  hence "distance_set (Graph.digraph_abs G) (t_set srcs) v = 
           distance_set (Graph.digraph_abs G) (t_set srcs) v' + 1" (is "?d v = ?d v' + _")
    using 2
    by(fastforce intro!: dist_current_plus_1_new)

  show ?case
  proof(cases "0 < ?d u")
    case in_srcs: True
    moreover have "?d v' < \<infinity>"
      using \<open>?d v = ?d u\<close> \<open>invar_1 bfs_state\<close> \<open>invar_2 bfs_state\<close> \<open>v' \<in> t_set (current bfs_state)\<close>
            \<open>invar_current_reachable bfs_state\<close>
      by (auto elim!: invar_1_props invar_2_props invar_current_reachable_props)
    hence "?d v < \<infinity>"
      using \<open>?d v = ?d v' + 1\<close>
      by (simp add: plus_eq_infty_iff_enat)
    hence "?d u < \<infinity>"
      using \<open>?d v = ?d u\<close>
      by auto
    ultimately obtain u' where "?d u' + 1 = ?d u" "u \<in> neighbourhood (Graph.digraph_abs G) u'"
      using distance_set_parent'
      by (metis srcs_invar(1))
    hence "?d u' = ?d v'"
      using \<open>?d v = ?d v' + 1\<close> \<open>?d v = ?d u\<close>
      by auto
    hence "u' \<in> t_set (current bfs_state)"
      using \<open>invar_3_1 bfs_state\<close>
            \<open>v' \<in> t_set (current bfs_state)\<close>
      by (auto elim!: invar_3_1_props)
    moreover have "?d u' < ?d u"
      using \<open>?d u < \<infinity>\<close> 
      using zero_less_one not_infinity_eq 
      by (fastforce intro!: plus_one_side_lt_enat simp: \<open>?d u' + 1 = ?d u\<close>[symmetric])
    hence "u \<notin> t_set (visited bfs_state) "
      using \<open>invar_3_2 bfs_state\<close> \<open>u' \<in> t_set (current bfs_state)\<close> 
      by (auto elim!: invar_3_2_props dest: leD)
    ultimately show ?thesis
      using \<open>invar_1 bfs_state\<close> \<open>invar_2 bfs_state\<close> \<open>u \<in> neighbourhood (Graph.digraph_abs G) u'\<close>
      apply(auto simp add: BFS_upd1_def Let_def 2(8) elim!: invar_1_props invar_2_props)
      by blast
  next
    case not_in_srcs: False
    text \<open>Contradiction because if \<open>u \<in> srcs\<close> then distance srcs to a vertex in srcs is > 0. This is
          because the distance from srcs to \<open>u\<close> is the same as that to \<open>v\<close>.\<close>
    then show ?thesis
      using \<open>?d v = ?d u\<close> \<open>?d v = ?d v' + 1\<close>
      by auto
  qed
qed 

lemma invar_3_1_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_3_3 bfs_state\<rbrakk> \<Longrightarrow> invar_3_3 (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_3_2_holds_upd1_new[invar_holds_intros]: 
  "\<lbrakk>BFS_call_1_conds bfs_state; invar_1 bfs_state; invar_2 bfs_state ; invar_3_1 bfs_state; 
    invar_3_2 bfs_state; invar_3_4 bfs_state; invar_current_reachable bfs_state\<rbrakk>
   \<Longrightarrow> invar_3_2 (BFS_upd1 bfs_state)"
proof(cases "next_frontier_and_current (current bfs_state) (visited bfs_state)",goal_cases)
  case (1 front' vis')
  thus ?case
proof(intro invar_props_intros, goal_cases)                                                                          
  case assms: (1 u v)
  show ?case
  proof(cases "v \<in> t_set (current (BFS_upd1 bfs_state))")
    case v_in_current: True
    moreover have "invar_3_1 (BFS_upd1 bfs_state)"
      using assms
      by (auto intro: invar_holds_intros)
    ultimately show ?thesis
      using \<open>u \<in> t_set (current (BFS_upd1 bfs_state))\<close>
      by (fastforce elim: invar_props_elims)
  next                     
    case v_not_in_current: False
    have current_in_vis:"t_set (current bfs_state) \<subseteq> t_set (visited bfs_state)" 
      using assms(3) by(auto elim: invar_2_props)
  have vis_in_G: "[visited bfs_state]\<^sub>s \<subseteq> dVs [G]\<^sub>g" 
    using assms(3) by(auto elim!: invar_2_props)
    note next_frontier[simp] = next_frontier(2)[OF _ _ _ current_in_vis 1(8) vis_in_G]
      note next_vis[simp] = next_vis[OF _ _ _ current_in_vis 1(8) vis_in_G]
    from v_not_in_current have "v \<in> t_set (visited bfs_state)"
      using assms(1,2,3,10) 
      by (auto simp add: BFS_upd1_def Let_def new_visited_simp 1(8) elim!: invar_1_props)+
    moreover obtain u' where uv'[intro]: "u \<in> neighbourhood (Graph.digraph_abs G) u'" "u' \<in> t_set (current bfs_state)" 
      using assms(1,2,3,8,9)    
      by (auto simp: BFS_upd1_def Let_def new_visited_simp elim!: invar_1_props)
    ultimately have "distance_set (Graph.digraph_abs G) (t_set srcs) v \<le>
                       distance_set (Graph.digraph_abs G) (t_set srcs) u'"
      using \<open>invar_3_2 bfs_state\<close>
      by (auto elim!: invar_3_2_props)
    moreover have "distance_set (Graph.digraph_abs G) (t_set srcs) u = 
           distance_set (Graph.digraph_abs G) (t_set srcs) u' + 1" (is "?d u = ?d u' + _")
      using assms
      by(fastforce intro!: dist_current_plus_1_new)
    ultimately show ?thesis
      by (metis le_iff_add order.trans)
  qed
qed
qed

lemma invar_3_2_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_3_3 bfs_state\<rbrakk> \<Longrightarrow> invar_3_3 (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_3_3_holds_upd1[invar_holds_intros]: 
  "\<lbrakk>BFS_call_1_conds bfs_state; invar_1 bfs_state; invar_2 bfs_state; invar_3_3 bfs_state\<rbrakk> 
   \<Longrightarrow> invar_3_3 (BFS_upd1 bfs_state)"
proof(cases "next_frontier_and_current (current bfs_state) (visited bfs_state)", goal_cases)
  case (1 front' vis')
    note next_frontier[simp] = next_frontier(2)[OF _ _ _ _ 1(5)]
      note next_vis[simp] = next_vis[OF _ _ _ _ 1(5)]
      thus ?case
        using 1(1-4)
  by(auto elim!: call_cond_elims invar_1_props invar_2_props invar_3_3_props 
            intro!: invar_props_intros simp: BFS_upd1_def Let_def 1(5))
    (metis in_mono sup.order_iff)+
qed

lemma invar_3_3_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_3_3 bfs_state\<rbrakk> \<Longrightarrow> invar_3_3 (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_3_4_holds_upd1[invar_holds_intros]: 
  "\<lbrakk>BFS_call_1_conds bfs_state; invar_1 bfs_state; invar_2 bfs_state;
    invar_3_1 bfs_state; invar_3_2 bfs_state; invar_3_3 bfs_state; invar_3_4 bfs_state;
    invar_current_reachable bfs_state\<rbrakk> \<Longrightarrow> 
    invar_3_4 (BFS_upd1 bfs_state)"
proof(cases "next_frontier_and_current (current bfs_state) (visited bfs_state)",goal_cases)
  case (1 front' vis')
  have current_in_vis:"t_set (current bfs_state) \<subseteq> t_set (visited bfs_state)" 
and  vis_in_G: "[visited bfs_state]\<^sub>s \<subseteq> dVs [G]\<^sub>g" 
      using 1 by(auto elim: invar_2_props)
    note next_frontier[simp] = next_frontier(2)[OF _ _ _ current_in_vis 1(9) vis_in_G]
      note next_vis[simp] = next_vis[OF _ _ _ current_in_vis 1(9) vis_in_G]
    from 1 show ?case
proof(intro invar_props_intros, goal_cases)                                                                                                    
  case assms: (1 u v)
  have current_in_vis:"t_set (current bfs_state) \<subseteq> t_set (visited bfs_state)" 
      using assms(3) by(auto elim: invar_2_props)
  show ?case
  proof(cases \<open>v \<in> t_set (visited bfs_state) \<close>)
    case v_visited: True
    hence "u \<in> t_set (visited bfs_state) \<union> t_set (current bfs_state)"
      using \<open>invar_3_4 bfs_state\<close> assms
      by (auto elim!: invar_3_4_props)
    then show ?thesis 
      using \<open>invar_1 bfs_state\<close> \<open>v \<in> t_set (visited (BFS_upd1 bfs_state)) \<union> t_set (current (BFS_upd1 bfs_state))\<close>
            assms(2,3,9)
      by (auto simp: BFS_upd1_def Let_def new_visited_simp elim!: invar_props_elims)
  next
    case v_not_visited: False
    hence "v \<in> t_set (current (BFS_upd1 bfs_state))"
      using \<open>invar_1 bfs_state\<close> \<open>v \<in> t_set (visited (BFS_upd1 bfs_state)) \<union> t_set (current (BFS_upd1 bfs_state))\<close>
            assms(2,3,9)
      by (auto simp: BFS_upd1_def Let_def new_visited_simp elim!: invar_props_elims)
    then obtain v' where v'[intro]:
      "v \<in> neighbourhood (Graph.digraph_abs G) v'" "v' \<in> t_set (current bfs_state)"
      using  \<open>invar_1 bfs_state\<close> assms(9)
      by (auto simp: BFS_upd1_def Let_def  elim!: invar_1_props)
    have "distance_set (Graph.digraph_abs G) (t_set srcs) v = 
            distance_set (Graph.digraph_abs G) (t_set srcs) v' + 1" (is "?dv = ?dv' + 1")
      using assms \<open>v \<in> t_set (current (BFS_upd1 bfs_state))\<close>
      by (auto intro!: dist_current_plus_1_new)
    moreover have "u \<in> t_set (visited (BFS_upd1 bfs_state)) \<union> t_set (current (BFS_upd1 bfs_state))"
      if "distance_set (Graph.digraph_abs G) (t_set srcs) u \<le> ?dv'" (is "?du \<le> ?dv'")
      using that \<open>invar_1 bfs_state\<close> \<open>invar_2 bfs_state\<close> \<open>invar_3_4 bfs_state\<close> assms(9)
      by (auto simp: BFS_upd1_def Let_def elim!: invar_1_props invar_2_props invar_3_4_props)
          blast
    moreover have "u \<in> t_set (visited (BFS_upd1 bfs_state)) \<union> t_set (current (BFS_upd1 bfs_state))"
      if "distance_set (Graph.digraph_abs G) (t_set srcs) u = ?dv"
    proof-
      have "invar_3_1 (BFS_upd1 bfs_state)"
        by (auto intro: assms invar_holds_intros)
      hence "u \<in> t_set (current (BFS_upd1 bfs_state))"
        using that \<open>invar_3_1 bfs_state\<close> \<open>v \<in> t_set (current (BFS_upd1 bfs_state))\<close>
        by (auto elim!: invar_3_1_props)
      moreover have "invar_1 (BFS_upd1 bfs_state)" "invar_2 (BFS_upd1 bfs_state)"
        using \<open>BFS_call_1_conds bfs_state\<close> \<open>invar_1 bfs_state\<close> \<open>invar_2 bfs_state\<close>
        by(auto intro!: invar_1_holds_upd1 invar_2_holds_upd1)
      ultimately show ?thesis
        by (auto elim!: invar_props_elims)
    qed
    ultimately show ?thesis
      using \<open>?du \<le> ?dv\<close> ileI1 linorder_not_less plus_1_eSuc(2)
      by fastforce
  qed
qed
qed

lemma invar_3_4_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_3_4 bfs_state\<rbrakk> \<Longrightarrow> invar_3_4 (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

                                      
lemma invar_dist'_props[invar_props_elims]: 
  "invar_dist' bfs_state \<Longrightarrow> v \<in> dVs (Graph.digraph_abs G) - t_set srcs \<Longrightarrow> 
   \<lbrakk>
     \<lbrakk>v \<in> (t_set (visited bfs_state) \<union> t_set (current bfs_state)) \<Longrightarrow> distance_set (Graph.digraph_abs G) (t_set srcs) v =
         distance_set (Graph.digraph_abs (parents bfs_state)) (t_set srcs) v\<rbrakk> \<Longrightarrow> P
   \<rbrakk>
   \<Longrightarrow> P"
  unfolding invar_dist'_def
  by auto

lemma invar_dist'_intro[invar_props_intros]:
   "\<lbrakk>\<And>v. \<lbrakk>v \<in> dVs (Graph.digraph_abs G) - t_set srcs; v \<in> t_set (visited bfs_state) \<union> t_set (current bfs_state)\<rbrakk> \<Longrightarrow> 
           (distance_set (Graph.digraph_abs G) (t_set srcs) v =
             distance_set (Graph.digraph_abs (parents bfs_state)) (t_set srcs) v)\<rbrakk>
        
    \<Longrightarrow> invar_dist' bfs_state"
  unfolding invar_dist'_def
  by auto

lemma invar_goes_through_current_props[invar_props_elims]: 
  "invar_goes_through_current  bfs_state \<Longrightarrow> 
   \<lbrakk>\<lbrakk>\<And>u v p. \<lbrakk>u \<in>t_set (visited bfs_state) \<union> t_set (current bfs_state);
              v \<notin> t_set (visited bfs_state) \<union> t_set (current bfs_state); 
              Vwalk.vwalk_bet (Graph.digraph_abs G) u p v\<rbrakk>
      \<Longrightarrow> set p \<inter> t_set (current bfs_state) \<noteq> {}\<rbrakk>
     \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  unfolding invar_goes_through_current_def
  by auto

lemma invar_goes_through_current_intro[invar_props_intros]:
  "\<lbrakk>\<And>u v p. \<lbrakk>u \<in>t_set (visited bfs_state) \<union> t_set (current bfs_state);
             v \<notin> t_set (visited bfs_state) \<union> t_set (current bfs_state); 
              Vwalk.vwalk_bet (Graph.digraph_abs G) u p v\<rbrakk>
      \<Longrightarrow> set p \<inter> t_set (current bfs_state) \<noteq> {}\<rbrakk>
    \<Longrightarrow> invar_goes_through_current bfs_state"
  unfolding invar_goes_through_current_def
  by auto

lemma invar_goes_through_active_holds_upd1[invar_holds_intros]: 
  "\<lbrakk>BFS_call_1_conds bfs_state; invar_1 bfs_state; invar_2 bfs_state; 
    invar_goes_through_current bfs_state\<rbrakk> 
    \<Longrightarrow> invar_goes_through_current (BFS_upd1 bfs_state)"
proof(cases "next_frontier_and_current (current bfs_state) (visited bfs_state)",goal_cases)
  case (1 front' vis')
  have current_in_vis:"t_set (current bfs_state) \<subseteq> t_set (visited bfs_state)" 
and  vis_in_G: "[visited bfs_state]\<^sub>s \<subseteq> dVs [G]\<^sub>g" 
      using 1 by(auto elim: invar_2_props)
    note next_frontier[simp] = next_frontier(2)[OF _ _ _ current_in_vis 1(5) vis_in_G]
      note next_vis[simp] = next_vis[OF _ _ _ current_in_vis 1(5) vis_in_G]
    from 1 show ?case
proof(intro invar_props_intros, goal_cases)
  case (1 u v p)
  hence "v \<notin> t_set (visited bfs_state) \<union> t_set (current bfs_state)"
    by (auto simp: Let_def BFS_upd1_def elim!: invar_1_props invar_2_props)
  show ?case
  proof(cases "u \<in> t_set (visited bfs_state) \<union> t_set (current bfs_state)")
    case u_in_visited: True
      have "Vwalk.vwalk_bet (Graph.digraph_abs G) u p v" "set p \<inter> t_set (current bfs_state) \<noteq> {}"
        using \<open>invar_goes_through_current bfs_state\<close>
              \<open>v \<notin> t_set (visited bfs_state) \<union> t_set (current bfs_state)\<close>
          \<open>vwalk_bet (Graph.digraph_abs G) u p v\<close> u_in_visited
        by (auto elim!: invar_goes_through_current_props)
      moreover have "u \<in> set p"
        using \<open>Vwalk.vwalk_bet (Graph.digraph_abs G) u p v\<close>
        by(auto intro: hd_of_vwalk_bet'')
      ultimately have "\<exists> p1 x p2. p = p1 @ [x] @ p2 \<and>
                          x \<in> t_set (current bfs_state) \<and> 
                          (\<forall>y\<in>set p2. y \<notin> (t_set (visited bfs_state) \<union> t_set (current bfs_state)) \<and>
                                      y \<notin> (t_set (current bfs_state)))"
        using \<open>invar_goes_through_current bfs_state\<close> u_in_visited
              \<open>v \<notin> t_set (visited bfs_state) \<union> t_set (current bfs_state)\<close>
          \<open>invar_1 bfs_state\<close> \<open>invar_2 bfs_state\<close>
        apply (intro list_2_preds[where ?P2.0 = "(\<lambda>x. x \<in> t_set (current bfs_state))",
              simplified list_inter_mem_iff[symmetric]])
        by (fastforce elim!: invar_goes_through_current_props dest!: vwalk_bet_suff split_vwalk)+

    then obtain p1 x p2 where "p = p1 @ x # p2" and
      "x \<in> t_set (current bfs_state)" and
      unvisited:
      "(\<And>y. y\<in>set p2 \<Longrightarrow> y \<notin> t_set (visited bfs_state) \<union> t_set (current bfs_state))"
      by auto
    moreover have "last p = v"
      using \<open>vwalk_bet (Graph.digraph_abs G) u p v\<close>
      by auto
    ultimately have "v \<in> set p2"
      using \<open>v \<notin> t_set (visited bfs_state) \<union> t_set (current bfs_state)\<close> 
            \<open>invar_1 bfs_state\<close> \<open>invar_2 bfs_state\<close>
      by (auto elim: invar_props_elims)
    then obtain v' p2' where "p2 = v' # p2'"
      by (cases p2) auto
    hence "v' \<in> neighbourhood (Graph.digraph_abs G) x"
      using \<open>p = p1 @ x # p2\<close> \<open>Vwalk.vwalk_bet (Graph.digraph_abs G) u p v\<close>
        split_vwalk
      by fastforce
    moreover have "v' \<in> set p2"
      using \<open>p2 = v' # p2'\<close>
      by auto
    ultimately have "v' \<in> t_set (current (BFS_upd1 bfs_state))"
      using \<open>invar_1 bfs_state\<close> \<open>invar_2 bfs_state\<close> \<open>x \<in> t_set (current bfs_state)\<close> 1(5)
      by(fastforce simp: BFS_upd1_def Let_def elim!: invar_1_props invar_2_props dest!: unvisited)
    then show ?thesis
      by(auto intro!: invar_goes_through_current_intro simp: \<open>p = p1 @ x # p2\<close> \<open>p2 = v' # p2'\<close>) 
next
  case u_not_in_visited: False
  hence "u \<in> t_set (current (BFS_upd1 bfs_state))"
    using \<open>invar_1 bfs_state\<close> \<open>invar_2 bfs_state\<close>
      \<open>u \<in> t_set (visited (BFS_upd1 bfs_state)) \<union> t_set (current (BFS_upd1 bfs_state))\<close> 1(5)
    by (auto simp: BFS_upd1_def Let_def new_visited_simp elim: invar_props_elims)
  moreover have "u \<in> set p"
    using \<open>Vwalk.vwalk_bet (Graph.digraph_abs G) u p v\<close>
    by (auto intro: hd_of_vwalk_bet'')
  ultimately show ?thesis
    by(auto intro!: invar_goes_through_current_intro)
qed
qed
qed

lemma invar_goes_through_current_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_goes_through_current bfs_state\<rbrakk> \<Longrightarrow> invar_goes_through_current (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_goes_through_current_holds[invar_holds_intros]: 
   assumes "BFS_dom bfs_state" "invar_1 bfs_state" "invar_2 bfs_state"
            "invar_goes_through_current bfs_state"
   shows "invar_goes_through_current (BFS bfs_state)"
  using assms(2-)
proof(induction rule: BFS_induct[OF assms(1)])
  case IH: (1 bfs_state)
  show ?case
    apply(rule BFS_cases[where bfs_state = bfs_state])
    by (auto intro!: IH(2-) intro: invar_holds_intros  simp: BFS_simps[OF IH(1)])
qed

lemma invar_dist'_holds_upd1_new[invar_holds_intros]: 
  "\<lbrakk>BFS_call_1_conds bfs_state; invar_1 bfs_state; invar_2 bfs_state;
    invar_3_4 bfs_state; invar_dist' bfs_state\<rbrakk> 
    \<Longrightarrow> invar_dist' (BFS_upd1 bfs_state)"
proof(cases "next_frontier_and_current (current bfs_state) (visited bfs_state)",goal_cases)
  case (1 front' vis')
    have current_in_vis:"t_set (current bfs_state) \<subseteq> t_set (visited bfs_state)" 
      using 1 by(auto elim: invar_2_props)
    note next_frontier[simp] = next_frontier(2)[OF _ _ _ current_in_vis 1(6)]
      note next_vis[simp] = next_vis[OF _ _ _ current_in_vis 1(6)]
    from 1 show ?case
proof(intro invar_props_intros, goal_cases)
  define bfs_state' where "bfs_state' = BFS_upd1 bfs_state"
  let ?dSrcsG = "distance_set (Graph.digraph_abs G) (t_set srcs)"
  let ?dSrcsT = "distance_set (Graph.digraph_abs (parents bfs_state)) (t_set srcs)"
  let ?dSrcsT' = "distance_set (Graph.digraph_abs (parents bfs_state')) (t_set srcs)"
  let ?dCurrG = "distance_set (Graph.digraph_abs G)  (t_set (current bfs_state))"
  case (1 v)
  note one = this
  then show ?case
  proof(cases "distance_set (Graph.digraph_abs G) (t_set srcs) v = \<infinity>")
    case infinite: True
    moreover have "?dSrcsG v \<le> ?dSrcsT' v"
      using \<open>invar_1 bfs_state\<close> \<open>invar_2 bfs_state\<close> 1(6)
      by(fastforce simp: bfs_state'_def BFS_upd1_def Let_def intro: distance_set_subset
                   elim: invar_props_elims)    
    ultimately show ?thesis
      by (simp add: bfs_state'_def)
  next
    case finite: False
    show ?thesis
    proof(cases "v \<in> t_set (visited bfs_state) \<union> t_set (current bfs_state)")
      case v_in_tree: True
      hence "?dSrcsT v = ?dSrcsG v"
        using \<open>invar_dist' bfs_state\<close> \<open>invar_1 bfs_state\<close> \<open>invar_2 bfs_state\<close>
              \<open>v \<in> dVs (Graph.digraph_abs G) - t_set srcs\<close>
        by (auto elim!: invar_dist'_props invar_1_props invar_2_props)

      moreover have "?dSrcsT v = ?dSrcsT' v"
      proof-
        have "?dSrcsT' v \<le> ?dSrcsT v"
          using \<open>invar_1 bfs_state\<close> \<open>invar_2 bfs_state\<close> 1(6)
          by(fastforce simp: bfs_state'_def BFS_upd1_def Let_def
                       intro: distance_set_subset elim: invar_props_elims)

        moreover have "?dSrcsG v \<le> ?dSrcsT' v"
          using \<open>invar_1 bfs_state\<close> \<open>invar_2 bfs_state\<close> 1(6)
          by(fastforce simp: bfs_state'_def BFS_upd1_def Let_def intro: distance_set_subset
                       elim: invar_props_elims)

        ultimately show ?thesis
          using \<open>?dSrcsT v = ?dSrcsG v\<close>
          by auto
      qed
      ultimately show ?thesis
        by (auto simp: bfs_state'_def)
    next
      case v_not_in_tree: False
      have current_in_vis:"t_set (current bfs_state) \<subseteq> t_set (visited bfs_state)" 
and  vis_in_G: "[visited bfs_state]\<^sub>s \<subseteq> dVs [G]\<^sub>g" 
        using \<open>invar_2 bfs_state\<close> by(auto elim: invar_2_props)
      note expand_tree[simp] = expand_tree(1,2)[OF _ _ _ _ current_in_vis vis_in_G]
         expand_tree(3)[OF _ _ _ _ _ current_in_vis vis_in_G]

      show ?thesis
      proof(rule ccontr, goal_cases)
        case 1
        moreover have \<open>invar_2 bfs_state'\<close>
          using \<open>BFS_call_1_conds bfs_state\<close> \<open>invar_1 bfs_state\<close> \<open>invar_2 bfs_state\<close>
          by (auto intro!: invar_2_holds_upd1 simp: bfs_state'_def)
        hence \<open>Graph.digraph_abs (parents bfs_state') \<subseteq> Graph.digraph_abs G\<close>
          by (auto elim: invar_props_elims)
        ultimately have "?dSrcsG v < ?dSrcsT' v"
          by (simp add: distance_set_subset order_less_le bfs_state'_def)
        hence "?dSrcsG v < ?dSrcsT' v"
          text \<open>because the tree is a subset of the Graph, which invar?\<close>
          by (simp add: distance_set_subset order_less_le bfs_state'_def)

        have "v \<in> t_set (current (BFS_upd1 bfs_state))"
          using \<open>v \<in> t_set (visited (BFS_upd1 bfs_state)) \<union> t_set (current (BFS_upd1 bfs_state))\<close> 
                v_not_in_tree \<open>invar_1 bfs_state\<close> \<open>invar_2 bfs_state\<close> one(6) vis_in_G
          by (auto simp: BFS_upd1_def Let_def new_visited_simp elim: invar_props_elims)
        moreover then  obtain v' where v'[intro]: 
          "v \<in> neighbourhood (Graph.digraph_abs G) v'"
          "v' \<in> t_set (current bfs_state)"
          "v \<in> neighbourhood (Graph.digraph_abs (parents bfs_state')) v'"
          using v_not_in_tree \<open>invar_1 bfs_state\<close> one(6) vis_in_G
          by (auto simp: neighbourhoodD BFS_upd1_def Let_def bfs_state'_def elim!: invar_1_props)
        ultimately have "?dSrcsG v = ?dSrcsG v' + 1"
          using \<open>invar_1 bfs_state\<close> \<open>invar_3_4 bfs_state\<close> \<open>invar_2 bfs_state\<close>
          by (auto intro!: dist_current_plus_1_new)
        show False
        proof(cases "v' \<in> t_set srcs")
          case v'_in_srcs: True
          hence "?dSrcsT' v' = 0"
            by (meson dVsI(1) distance_set_0 neighbourhoodI v'(3))
          moreover have "?dSrcsG v' = 0"
            using v'_in_srcs
            by (metis \<open>distance_set (Graph.digraph_abs G) (t_set srcs) v = distance_set (Graph.digraph_abs G) (t_set srcs) v' + 1\<close> add.commute add.right_neutral dist_set_inf dist_set_mem distance_0 enat_add_left_cancel le_iff_add local.finite order_antisym)
          then show ?thesis
            by (metis \<open>distance_set (Graph.digraph_abs G) (t_set srcs) v < distance_set (Graph.digraph_abs (parents bfs_state')) (t_set srcs) v\<close> \<open>distance_set (Graph.digraph_abs G) (t_set srcs) v = distance_set (Graph.digraph_abs G) (t_set srcs) v' + 1\<close> calculation distance_set_neighbourhood leD srcs_invar(1) v'(3))
        next
          case v'_not_in_srcs: False
          have "?dSrcsG v = ?dSrcsG v' + 1"
            using \<open>?dSrcsG v = ?dSrcsG v' + 1\<close> .
          also have "... = ?dSrcsT v' + 1"
            text \<open>From this current invariant\<close>
            using \<open>invar_dist' bfs_state\<close> \<open>v' \<in> t_set (current bfs_state)\<close> \<open>invar_1 bfs_state\<close>
              \<open>invar_2 bfs_state\<close> v'_not_in_srcs 
            by (force elim!: invar_1_props invar_2_props invar_dist'_props)
          also have "... = ?dSrcsT' v' + 1"
          proof-
            have "?dSrcsT v' = ?dSrcsT' v'"
            proof-
              have "?dSrcsT' v' \<le> ?dSrcsT v'"
                using \<open>invar_1 bfs_state\<close> one(6)
                by(fastforce simp: bfs_state'_def BFS_upd1_def Let_def 
                    intro: distance_set_subset elim: invar_props_elims)

              moreover have "?dSrcsG v' \<le> ?dSrcsT' v'"
                using \<open>invar_1 bfs_state\<close> \<open>invar_2 bfs_state\<close> one(6)
                by(fastforce simp: bfs_state'_def BFS_upd1_def Let_def intro: distance_set_subset
                    elim: invar_props_elims)
              moreover have \<open>?dSrcsT v' = ?dSrcsG v'\<close>
                using \<open>invar_dist' bfs_state\<close> \<open>v' \<in> t_set (current bfs_state)\<close> \<open>invar_1 bfs_state\<close>
                  \<open>invar_2 bfs_state\<close> v'_not_in_srcs
                by (force elim!: invar_1_props invar_2_props invar_dist'_props)
              ultimately show ?thesis
                by auto
            qed
            then show ?thesis
              by auto
          qed
          finally have "?dSrcsG v = ?dSrcsT' v' + 1"
            by auto
          hence "?dSrcsT' v' + 1 < ?dSrcsT' v"
            using \<open>?dSrcsG v < ?dSrcsT' v\<close>
            by auto
          moreover have "v \<in> neighbourhood (Graph.digraph_abs (parents bfs_state')) v'"
            using \<open>v \<in> neighbourhood (Graph.digraph_abs (parents bfs_state')) v'\<close> .
          hence "?dSrcsT' v \<le> ?dSrcsT' v' + 1"
            by (auto intro!: distance_set_neighbourhood)

          ultimately show False
            text \<open>From the triangle ineq\<close>
            by auto
        qed
      qed
    qed
  qed
qed
qed

lemma invar_dist'_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_dist' bfs_state\<rbrakk> \<Longrightarrow> invar_dist' (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_dist'_holds[invar_holds_intros]: 
   assumes "BFS_dom bfs_state" "invar_1 bfs_state" "invar_2 bfs_state"
           "invar_3_1 bfs_state" "invar_3_2 bfs_state" "invar_3_3 bfs_state" "invar_3_4 bfs_state"
            "invar_dist' bfs_state" "invar_current_reachable bfs_state"
   shows "invar_dist' (BFS bfs_state)"
  using assms(2-)
proof(induction rule: BFS_induct[OF assms(1)])
  case IH: (1 bfs_state)
  show ?case
    apply(rule BFS_cases[where bfs_state = bfs_state])
    by (auto intro!: IH(2-) intro: invar_holds_intros  simp: BFS_simps[OF IH(1)])
qed

definition "invar_current_no_out bfs_state =
  (\<forall>u\<in>t_set(current bfs_state). 
     \<forall>v. (u,v) \<notin> Graph.digraph_abs (parents bfs_state))"

lemma invar_current_no_out_props[invar_props_elims]: 
  "invar_current_no_out bfs_state \<Longrightarrow> 
  (\<lbrakk>\<And>u v. u\<in>t_set(current bfs_state) \<Longrightarrow> (u,v) \<notin> Graph.digraph_abs (parents bfs_state)\<rbrakk> \<Longrightarrow> P)
     \<Longrightarrow> P"
  by (auto simp: invar_current_no_out_def)

lemma invar_current_no_out_intro[invar_props_intros]:
   "\<lbrakk>\<And>u v. u\<in>t_set(current bfs_state) \<Longrightarrow> (u,v) \<notin> Graph.digraph_abs (parents bfs_state)\<rbrakk>
     \<Longrightarrow> invar_current_no_out bfs_state"
   by (auto simp: invar_current_no_out_def)

lemma invar_current_no_out_holds_upd1[invar_holds_intros]: 
  "\<lbrakk>BFS_call_1_conds bfs_state; invar_1 bfs_state; invar_2 bfs_state; invar_current_no_out bfs_state\<rbrakk>
     \<Longrightarrow> invar_current_no_out (BFS_upd1 bfs_state)"
proof(cases "next_frontier_and_current (current bfs_state) (visited bfs_state)",goal_cases)
  case (1 front' vis')
    have current_in_vis:"t_set (current bfs_state) \<subseteq> t_set (visited bfs_state)" 
      using 1 by(auto elim: invar_2_props)
    note next_frontier[simp] = next_frontier(2)[OF _ _ _ current_in_vis 1(5)]
      note next_vis[simp] = next_vis[OF _ _ _ current_in_vis 1(5)]
    from 1 show ?case
     by(auto elim!: call_cond_elims invar_1_props invar_2_props 
                intro!: invar_props_intros 
                  simp: BFS_upd1_def Let_def)
       blast+
 qed

lemma invar_current_no_out_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_current_no_out bfs_state\<rbrakk> \<Longrightarrow> invar_current_no_out (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_current_no_out_holds[invar_holds_intros]: 
   assumes "BFS_dom bfs_state" "invar_1 bfs_state" "invar_2 bfs_state" "invar_current_no_out bfs_state"
   shows "invar_current_no_out (BFS bfs_state)"
  using assms(2-)
proof(induction rule: BFS_induct[OF assms(1)])
  case IH: (1 bfs_state)
  show ?case
    apply(rule BFS_cases[where bfs_state = bfs_state])
    by (auto intro!: IH(2-) intro: invar_holds_intros  simp: BFS_simps[OF IH(1)])
qed
 
lemma invar_parents_shortest_paths_props[invar_props_elims]: 
  "invar_parents_shortest_paths bfs_state \<Longrightarrow> 
  (\<lbrakk>\<And>u p v. \<lbrakk>u \<in> t_set srcs; Vwalk.vwalk_bet (Graph.digraph_abs (parents bfs_state)) u p v\<rbrakk> \<Longrightarrow>
         length p - 1 = distance_set (Graph.digraph_abs G) (t_set srcs) v\<rbrakk> \<Longrightarrow> P)
     \<Longrightarrow> P"
  by (auto simp: invar_parents_shortest_paths_def)

lemma invar_parents_shortest_paths_intro[invar_props_intros]:
  "\<lbrakk>\<And>u p v. \<lbrakk>u \<in> t_set srcs; Vwalk.vwalk_bet (Graph.digraph_abs (parents bfs_state)) u p v\<rbrakk> \<Longrightarrow>
         length p - 1 = distance_set (Graph.digraph_abs G) (t_set srcs) v\<rbrakk>
     \<Longrightarrow> invar_parents_shortest_paths bfs_state"
  by (auto simp: invar_parents_shortest_paths_def)

lemma invar_parents_shortest_paths_holds_upd1[invar_holds_intros]: 
  "\<lbrakk>BFS_call_1_conds bfs_state; invar_1 bfs_state; invar_2 bfs_state; invar_current_no_out bfs_state;
    invar_3_4 bfs_state; invar_parents_shortest_paths bfs_state\<rbrakk>
     \<Longrightarrow> invar_parents_shortest_paths (BFS_upd1 bfs_state)"
proof(cases "next_frontier_and_current (current bfs_state) (visited bfs_state)",goal_cases)
  case (1 front' vis')
  have current_in_vis:"t_set (current bfs_state) \<subseteq> t_set (visited bfs_state)"
and  vis_in_G: "[visited bfs_state]\<^sub>s \<subseteq> dVs [G]\<^sub>g" 
      using 1 by(auto elim: invar_2_props)
    note next_frontier[simp] = next_frontier(2)[OF _ _ _ current_in_vis 1(7) vis_in_G]
      note next_vis[simp] = next_vis[OF _ _ _ current_in_vis 1(7) vis_in_G]
    from 1 show ?case
proof(intro invar_props_intros, goal_cases)
  case assms: (1 u p v)

  define bfs_state' where "bfs_state' = BFS_upd1 bfs_state"

  have "invar_2 bfs_state'"
    using assms
    by (auto intro: invar_holds_intros simp: bfs_state'_def)

  hence ?case if "length p \<le> 1"
    using \<open>length p \<le> 1\<close> assms(7,8,9) \<open>invar_2 bfs_state\<close> 
    by(cases p) (auto elim!: Vwalk.vwalk_bet_props invar_props_elims dest!: dVs_subset
                      simp: bfs_state'_def[symmetric] zero_enat_def[symmetric])

  have "invar_current_no_out bfs_state'"
    using assms 
    by(auto intro: invar_holds_intros simp: bfs_state'_def)

  have **: "u \<in> t_set (current bfs_state') \<or> v \<in> t_set (current bfs_state')"
    if "(u,v) \<in> (Graph.digraph_abs (parents bfs_state')) -
              (Graph.digraph_abs (parents bfs_state))" for u v
    using \<open>invar_1 bfs_state\<close> \<open>invar_2 bfs_state\<close> dVsI that assms(7)
    by(fastforce dest: dVsI simp: bfs_state'_def dVs_def BFS_upd1_def Let_def
               elim!: invar_1_props invar_2_props)

  have ?case if "length p > 1" 
  proof-
    have "u \<in> t_set (visited bfs_state) \<union> t_set (current bfs_state)"
    proof(rule ccontr, goal_cases)
      have "u \<in> dVs (Graph.digraph_abs (parents bfs_state'))"
        using assms(7,9)
        by (auto simp: bfs_state'_def)
      hence "u \<in> t_set (visited bfs_state') \<union> t_set (current bfs_state')"
        using \<open>invar_2 bfs_state'\<close>
        by (auto elim: invar_props_elims)
      moreover case 1
      ultimately have "u \<in> t_set (current bfs_state')"
        using assms
        by(auto simp: Let_def bfs_state'_def BFS_upd1_def elim!: invar_1_props invar_2_props)
      moreover obtain u' where "(u,u') \<in> Graph.digraph_abs (parents bfs_state')"
        using \<open>length p > 1\<close> assms(7,9) \<open>invar_2 bfs_state\<close>
        by (auto elim!: Vwalk.vwalk_bet_props 
            simp: eval_nat_numeral Suc_le_length_iff Suc_le_eq[symmetric] bfs_state'_def
            split: if_splits)
      ultimately show ?case
        using \<open>invar_current_no_out bfs_state'\<close>
        by (auto elim!: invar_current_no_out_props)
    qed

    show ?thesis
    proof(cases "v \<notin> t_set (visited bfs_state) \<union> t_set (current bfs_state)")
      case v_not_visited: True
      show ?thesis
      proof(rule ccontr, goal_cases)
        case 1

        moreover have "vwalk_bet (Graph.digraph_abs G) u p v"
          by (metis \<open>invar_2 bfs_state'\<close> assms(9) bfs_state'_def invar_2_props vwalk_bet_subset)

        ultimately have "length p - 1 > distance_set (Graph.digraph_abs G) (t_set srcs) v"
          using \<open>u \<in> t_set srcs\<close> 1
          by (auto dest: vwalk_bet_dist_set[of "[G]\<^sub>g" u p v "[srcs]\<^sub>s"])

        hence "length p - 2 \<ge>  distance_set (Graph.digraph_abs G) (t_set srcs) v"
          using \<open>length p > 1\<close> Suc_ile_eq[of "length p - Suc (Suc 0)" "distance_set [G]\<^sub>g [srcs]\<^sub>s v"]
                Suc_diff_Suc[of "Suc 0" "length p"]
          by (auto simp: eval_nat_numeral)
        moreover obtain p' v' where "p = p' @ [v', v]"
          using \<open>length p > 1\<close> assms(7,9)
          by(cases p rule: rev_cases3)
            (auto  simp: eval_nat_numeral Suc_le_length_iff Suc_le_eq[symmetric] vwalk_bet_def
                  split: if_splits)
        have "vwalk_bet (Graph.digraph_abs (parents bfs_state)) u (p' @ [v']) v'"
        proof(rule ccontr, goal_cases)
          case 1
          moreover have "vwalk_bet (Graph.digraph_abs (parents (BFS_upd1 bfs_state))) u (p' @ [v']) v'"
            using assms(9) \<open>p = p' @ [v', v]\<close>
            by (simp add: vwalk_bet_pref)
          ultimately show ?case
          proof(elim vwalk_bet_not_vwalk_bet_elim_2[OF _ "1"], goal_cases)
            case 1
            then show ?case
              using v_not_visited zero_enat_def \<open>p = p' @[v',v]\<close> not_less_eq_eq[of "2" "Suc (length p')"]
                \<open>distance_set(Graph.digraph_abs G)(t_set srcs)v \<le> enat(length p - 2)\<close> 
                \<open>vwalk_bet(Graph.digraph_abs G)u p v\<close> assms(3) distance_set_0[of v "[G]\<^sub>g" "[srcs]\<^sub>s"] 
              by (auto elim!: invar_2_props vwalk_bet_vertex_decompE[of "[G]\<^sub>g" u "p' @ [v', v]" v p' v' "[v]"])
          next
            case (2 u'' v'')
            moreover hence "u'' \<notin> t_set (current bfs_state')"
              using \<open>invar_current_no_out bfs_state'\<close> \<open>invar_2 bfs_state'\<close>
              by (auto simp: bfs_state'_def[symmetric] elim: invar_props_elims)
            ultimately have "v'' \<in> t_set (current bfs_state')"
              using ** \<open>invar_2 bfs_state'\<close>
              by (auto simp: bfs_state'_def[symmetric])
            moreover hence no_outgoing_v'': "(v'',u'') \<notin> Graph.digraph_abs (parents bfs_state')"
              for u''
              using \<open>invar_current_no_out bfs_state'\<close> that 
              by (auto elim: invar_props_elims)
            hence "last (p @ [v']) = v''"
              using that \<open>vwalk_bet (Graph.digraph_abs (parents (BFS_upd1 bfs_state))) u (p' @ [v']) v'\<close>[simplified bfs_state'_def[symmetric]]
                    "2"(2) no_outgoing_last[of "[parents bfs_state']\<^sub>g" "p' @ [v']" v'']
                    v_in_edge_in_vwalk(2)[of u'' v'' "p' @ [v']"]
              by (auto dest: v_in_edge_in_vwalk elim!: vwalk_bet_props intro!: no_outgoing_last)
            hence "v' = v''"
              using that
              by auto
            moreover have "(v',v) \<in> Graph.digraph_abs (parents bfs_state')"
              using \<open>p = p' @ [v', v]\<close> assms(9)
              by (fastforce simp: bfs_state'_def [symmetric] dest: split_vwalk)
            ultimately show ?case
              using that no_outgoing_v''
              by auto
          qed
        qed
        hence "length (p' @ [v']) - 1 = distance_set (Graph.digraph_abs G) (t_set srcs) v'"
          using \<open>invar_parents_shortest_paths bfs_state\<close> \<open>u \<in> t_set srcs\<close>
          by (force elim!: invar_props_elims)
        hence "length p - 2 = distance_set (Graph.digraph_abs G) (t_set srcs) v'" (is "_ = ?dist v'")
          by (auto simp: \<open>p = p' @ [v', v]\<close>)
        hence "?dist v \<le> ?dist v'"
          using \<open>?dist v \<le> length p - 2\<close> dual_order.trans
          by presburger
        hence "v \<in> t_set (visited bfs_state) \<union> t_set (current bfs_state) "
          using \<open>invar_2 bfs_state\<close> \<open>invar_3_4 bfs_state\<close> \<open>u \<in> t_set srcs\<close>
                \<open>vwalk_bet (Graph.digraph_abs (parents bfs_state)) u (p' @ [v']) v'\<close>
          by(blast elim!: invar_props_elims dest!: vwalk_bet_endpoints(2))
        thus ?case
          using v_not_visited
          by auto
      qed
    next
      case v_visited: False
      have "Vwalk.vwalk_bet (Graph.digraph_abs (parents bfs_state)) u p v"
      proof(rule ccontr, goal_cases)
        case 1
        thus ?case
        proof(elim vwalk_bet_not_vwalk_bet_elim_2[OF assms(9)], goal_cases)
          case 1
          then show ?case
            using that by auto
        next
          case (2 u' v')
          moreover hence "u' \<notin> t_set (current bfs_state')"
            using \<open>invar_current_no_out bfs_state'\<close> \<open>invar_2 bfs_state'\<close>
            by (auto simp: bfs_state'_def[symmetric] elim: invar_props_elims)
          ultimately have "v' \<in> t_set (current bfs_state')"
            using ** \<open>invar_2 bfs_state'\<close>
            by (auto simp: bfs_state'_def[symmetric])
          moreover hence "(v',u') \<notin> Graph.digraph_abs (parents bfs_state')" for u'
            using \<open>invar_current_no_out bfs_state'\<close> 
            by (auto elim: invar_props_elims)
          hence "last p = v'"
            using \<open>vwalk_bet (Graph.digraph_abs (parents (BFS_upd1 bfs_state))) u p v\<close>[simplified bfs_state'_def[symmetric]]
              \<open>(u',v') \<in> set (edges_of_vwalk p)\<close>
            by (auto dest: v_in_edge_in_vwalk elim!: vwalk_bet_props intro!: no_outgoing_last)
          hence "v' = v"
            using \<open>vwalk_bet (Graph.digraph_abs (parents (BFS_upd1 bfs_state))) u p v\<close>
            by auto
          ultimately show ?case
            using v_visited \<open>invar_1 bfs_state\<close> \<open>invar_2 bfs_state\<close> assms(7)
            by (auto simp: bfs_state'_def BFS_upd1_def Let_def elim!: invar_props_elims)
        qed
      qed
      then show ?thesis
        using \<open>invar_parents_shortest_paths bfs_state\<close> \<open>u \<in> t_set srcs\<close>
        by (auto elim!: invar_props_elims)
    qed
  qed
  show ?case
    using \<open>1 < length p \<Longrightarrow> length p - 1 = distance_set (Graph.digraph_abs G) (t_set srcs) v\<close>
          \<open>length p \<le> 1 \<Longrightarrow> length p - 1 = distance_set (Graph.digraph_abs G) (t_set srcs) v\<close>
    by fastforce
qed
qed

lemma invar_parents_shortest_paths_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_parents_shortest_paths bfs_state\<rbrakk> \<Longrightarrow> 
     invar_parents_shortest_paths (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_parents_shortest_paths_holds[invar_holds_intros]: 
   assumes "BFS_dom bfs_state" "invar_1 bfs_state" "invar_2 bfs_state"
           "invar_current_no_out bfs_state" "invar_3_1 bfs_state"
           "invar_3_2 bfs_state" "invar_3_3 bfs_state"
           "invar_3_4 bfs_state" "invar_current_reachable bfs_state" 
           "invar_parents_shortest_paths bfs_state"
   shows "invar_parents_shortest_paths (BFS bfs_state)"
  using assms(2-)
proof(induction rule: BFS_induct[OF assms(1)])
  case IH: (1 bfs_state)
  show ?case
    apply(rule BFS_cases[where bfs_state = bfs_state])
    by (auto intro!: IH(2-) intro: invar_holds_intros  simp: BFS_simps[OF IH(1)])
qed

lemma BFS_ret_1[ret_holds_intros]:
  "BFS_ret_1_conds (bfs_state) \<Longrightarrow> BFS_ret_1_conds (BFS_ret1 bfs_state)"
  by (auto simp: elim!: call_cond_elims intro!: call_cond_intros)

lemma ret1_holds[ret_holds_intros]:
   assumes "BFS_dom bfs_state" 
   shows "BFS_ret_1_conds (BFS bfs_state)" 
proof(induction  rule: BFS_induct[OF assms(1)])
  case IH: (1 bfs_state)
  show ?case
    apply(rule BFS_cases[where bfs_state = bfs_state])
    by (auto intro: ret_holds_intros intro!: IH(2-)
             simp: BFS_simps[OF IH(1)])
qed

lemma BFS_correct_1_ret_1:
  "\<lbrakk>invar_2 bfs_state; invar_goes_through_current bfs_state; BFS_ret_1_conds bfs_state;
    u \<in> t_set srcs; t \<notin> t_set (visited bfs_state)\<rbrakk>
         \<Longrightarrow> \<nexists>p. vwalk_bet (Graph.digraph_abs G) u p t"
    by (force elim!: call_cond_elims invar_props_elims)

lemma BFS_correct_2_ret_1:
  "\<lbrakk>invar_1 bfs_state; invar_2 bfs_state; invar_dist' bfs_state; BFS_ret_1_conds bfs_state;
    t \<in> t_set (visited bfs_state) - t_set srcs\<rbrakk>
         \<Longrightarrow> distance_set (Graph.digraph_abs G) (t_set srcs) t =
         distance_set (Graph.digraph_abs (parents bfs_state)) (t_set srcs) t"
  apply(erule invar_props_elims)+
  by (auto elim!: call_cond_elims invar_props_elims)

lemma BFS_correct_3_ret_1:
  "\<lbrakk>invar_parents_shortest_paths bfs_state; BFS_ret_1_conds bfs_state;
    u \<in> t_set srcs; Vwalk.vwalk_bet (Graph.digraph_abs (parents bfs_state)) u p v\<rbrakk>
         \<Longrightarrow> length p - 1 = distance_set (Graph.digraph_abs G) (t_set srcs) v"
  apply(erule invar_props_elims)+
  by (auto elim!: call_cond_elims invar_props_elims)

lemma BFS_correct_4_ret_1:
  "\<lbrakk>invar_2 bfs_state; BFS_ret_1_conds bfs_state\<rbrakk> \<Longrightarrow>
    (Graph.digraph_abs (parents bfs_state))\<subseteq> Graph.digraph_abs G"
  apply(erule invar_props_elims)+
  by (auto elim!: call_cond_elims invar_props_elims)

subsection \<open>Termination\<close>

named_theorems termination_intros

declare termination_intros[intro!]

lemma in_prod_relI[intro!,termination_intros]:
  "\<lbrakk>f1 a = f1 a'; (a, a') \<in> f2 <*mlex*> r\<rbrakk> \<Longrightarrow> (a,a') \<in> (f1 <*mlex*> f2 <*mlex*> r)"
   by (simp add: mlex_iff)+

definition "less_rel = {(x::nat, y::nat). x < y}"

lemma wf_less_rel[intro!]: "wf less_rel"
  by(auto simp: less_rel_def wf_less)

definition "state_measure_rel call_measure = inv_image less_rel call_measure"

lemma call_1_measure_nonsym[simp]:
  "(call_1_measure_1 BFS_state, call_1_measure_1 BFS_state) \<notin> less_rel"
  by (auto simp: less_rel_def)

lemma call_1_terminates[termination_intros]:
  assumes  "BFS_call_1_conds BFS_state" "invar_1 BFS_state" "invar_2 BFS_state"
           "invar_current_no_out BFS_state"
  shows "(BFS_upd1 BFS_state, BFS_state) \<in>
           call_1_measure_1 <*mlex*> call_1_measure_2 <*mlex*> r"
proof(cases "next_frontier_and_current (current BFS_state) (visited BFS_state)",goal_cases)
  case (1 front' vis')
  have current_in_vis:"t_set (current BFS_state) \<subseteq> t_set (visited BFS_state)" 
and  vis_in_G: "[visited BFS_state]\<^sub>s \<subseteq> dVs [G]\<^sub>g" 
      using assms by(auto elim: invar_2_props)
    note next_frontier[simp] = next_frontier(2)[OF _ _ _ current_in_vis 1(1) vis_in_G]
      note next_vis[simp] = next_vis[OF _ _ _ current_in_vis 1(1) vis_in_G]
    from 1 show ?case
proof(cases "t_set front' = {}")
  case True
  hence "t_set (visited (BFS_upd1 BFS_state))  =
           t_set (visited BFS_state)"
    using \<open>invar_1 BFS_state\<close> \<open>invar_2 BFS_state\<close> 1
    by (fastforce simp: BFS_upd1_def Let_def elim!: invar_props_elims)
  hence "call_1_measure_1 (BFS_upd1 BFS_state) = call_1_measure_1 BFS_state"
    by (auto simp: call_1_measure_1_def)
  moreover have "t_set (current (BFS_upd1 BFS_state)) = {}"
    using True 1
    by (auto simp: BFS_upd1_def Let_def)
  ultimately show ?thesis
    using assms
  by(fastforce elim!: invar_props_elims call_cond_elims
          simp add: call_1_measure_2_def 
          intro!: psubset_card_mono 
          intro: mlex_less)
next
  case False
  have *: "{{v1, v2} |v1 v2. (v1, v2) \<in> [G]\<^sub>g}
                 \<subseteq> (\<lambda>(x,y). {x,y} ) ` ({v. \<exists>y. lookup G v = Some y} \<times>
                                        (\<Union> {t_set N | v N. lookup G v = Some N}))"
    including Graph.adjmap.automation and Graph.vset.set.automation
    apply (auto simp: Graph.digraph_abs_def Graph.neighbourhood_def image_def
                split: option.splits)
    by (metis Graph.graph_invE Graph.vset.set.set_isin graph_inv(1))
  moreover have "{uu. \<exists>v N. uu = t_set N \<and> lookup G v = Some N} = 
                   ((t_set o the o (lookup G)) ` {v | N v. lookup G v = Some N})"
    by (force simp: image_def)
  hence "finite (\<Union> {t_set N | v N. lookup G v = Some N})"
    using graph_inv(1,2,3)
    apply(subst (asm) Graph.finite_vsets_def )
    by (auto simp: Graph.finite_graph_def Graph.graph_inv_def
             split: option.splits)
  ultimately have "finite {{v1, v2} |v1 v2. (v1,v2) \<in> [G]\<^sub>g}"
    using graph_inv(2)
    by (auto simp: Graph.finite_graph_def intro!: finite_subset[OF *])
  moreover have "finite {neighbourhood (Graph.digraph_abs G) u |u. u \<in> t_set (current BFS_state)}"
    using assms(3)
    by (auto intro!: finite_imageI finite_subset[of "[current BFS_state]\<^sub>s" "dVs [G]\<^sub>g"] 
           simp add: Graph.finite_vertices invar_2_def Setcompr_eq_image)
  moreover have "t_set (visited (BFS_upd1 BFS_state)) \<union> t_set (current (BFS_upd1 BFS_state)) \<subseteq> dVs (Graph.digraph_abs G)"
    using \<open>invar_1 BFS_state\<close> \<open>invar_2 BFS_state\<close>  1
    by(auto elim!: invar_props_elims call_cond_elims
          simp add: BFS_upd1_def Let_def dVs_def 
          intro!: mlex_less psubset_card_mono)+
  moreover have "t_set (visited (BFS_upd1 BFS_state))  \<noteq> 
                   t_set (visited BFS_state) "
    using \<open>BFS_call_1_conds BFS_state\<close> \<open>invar_1 BFS_state\<close> \<open>invar_2 BFS_state\<close> 
          \<open>invar_current_no_out BFS_state\<close> False 1
    by(fastforce elim!: invar_props_elims call_cond_elims
                 simp add: BFS_upd1_def Let_def dVs_def 
                 intro!: mlex_less psubset_card_mono)

  ultimately have **: "dVs (Graph.digraph_abs G) - (t_set (visited (BFS_upd1 BFS_state)))\<noteq>
                          dVs (Graph.digraph_abs G) - (t_set (visited BFS_state) )"
    using \<open>BFS_call_1_conds BFS_state\<close> \<open>invar_1 BFS_state\<close> \<open>invar_2 BFS_state\<close> 1
    by(auto elim!: invar_props_elims call_cond_elims
          simp add: BFS_upd1_def Let_def dVs_def
          intro!: mlex_less psubset_card_mono)

  hence "call_1_measure_1 (BFS_upd1 BFS_state) < call_1_measure_1 BFS_state"
    using assms 1
    by(auto elim!: invar_props_elims call_cond_elims
          simp add: call_1_measure_1_def BFS_upd1_def Let_def 
          intro!: psubset_card_mono)
  thus ?thesis
    by(auto intro!: mlex_less psubset_card_mono)
qed
qed

lemma wf_term_rel: "wf BFS_term_rel'"
  by(auto simp: wf_mlex BFS_term_rel'_def)

lemma in_BFS_term_rel'[termination_intros]:
  "\<lbrakk>BFS_call_1_conds BFS_state; invar_1 BFS_state; invar_2 BFS_state; invar_current_no_out BFS_state\<rbrakk> \<Longrightarrow>
            (BFS_upd1 BFS_state, BFS_state) \<in> BFS_term_rel'" 
  by (simp add: BFS_term_rel'_def termination_intros)+

lemma BFS_terminates[termination_intros]:
  assumes "invar_1 BFS_state" "invar_2 BFS_state" "invar_current_no_out BFS_state"
  shows "BFS_dom BFS_state"
  using wf_term_rel assms
proof(induction rule: wf_induct_rule)
  case (less x)
  show ?case
    apply (rule BFS_domintros)
    by (auto intro: invar_holds_intros intro!: termination_intros less)
qed

lemma not_vwalk_bet_empty[simp]: "\<not> Vwalk.vwalk_bet (Graph.digraph_abs empty) u p v"
  using not_vwalk_bet_empty
  by (force simp add: Graph.digraph_abs_def Graph.neighbourhood_def)+

lemma not_edge_in_empty[simp]: "(u,v) \<notin> (Graph.digraph_abs empty)"
  by (force simp add: Graph.digraph_abs_def Graph.neighbourhood_def)+

lemma initial_state_props[invar_holds_intros, termination_intros, simp]:
  "invar_1 (initial_state)" (is ?g1)
  "invar_2 (initial_state)" (is ?g2)
  "invar_current_no_out (initial_state)" (is ?g3)
  "BFS_dom initial_state" (is ?g4)
  "invar_dist' initial_state" (is ?g5)
  "invar_3_1 initial_state"
  "invar_3_2 initial_state"
  "invar_3_3 initial_state"
  "invar_3_4 initial_state"
  "invar_current_reachable initial_state"
  "invar_goes_through_current initial_state"
  "invar_current_no_out initial_state"
  "invar_parents_shortest_paths initial_state"
proof-
  show ?g1
    using graph_inv(3)
    by (auto simp: initial_state_def dVs_def 
        intro!: invar_props_intros finite_subset[OF srcs_in_G])

  have "t_set (visited initial_state)\<union> t_set (current initial_state) \<subseteq> dVs (Graph.digraph_abs G)"
    using srcs_in_G
    by(simp add: initial_state_def)
  thus ?g2 ?g3
    by(force  simp: initial_state_def dVs_def Graph.digraph_abs_def Graph.neighbourhood_def 
                  intro!: invar_props_intros)+

  show ?g4
    using \<open>?g1\<close> \<open>?g2\<close> \<open>?g3\<close>
    by (auto intro!: termination_intros)

  show ?g5 "invar_3_3 initial_state" "invar_parents_shortest_paths initial_state"
       "invar_current_no_out initial_state"
    using not_vwalk_bet_empty
    by(auto simp add: initial_state_def  intro!: invar_props_intros)

  have *: "distance_set (Graph.digraph_abs G) (t_set srcs) v = 0" if "v \<in> t_set srcs" for v
    using that srcs_in_G
    by (fastforce intro: iffD2[OF distance_set_0[ where G = "(Graph.digraph_abs G)"]])
  moreover have **: "v \<in> t_set srcs" if "distance_set (Graph.digraph_abs G) (t_set srcs) v = 0" for v
    using dist_set_inf i0_ne_infinity that
    by (force intro: iffD1[OF distance_set_0[ where G = "(Graph.digraph_abs G)"]])
  ultimately show "invar_3_1 initial_state" "invar_3_2 initial_state" "invar_3_4 initial_state"
                  "invar_current_reachable initial_state"
    using dist_set_inf
    by(auto simp add: initial_state_def  intro!: invar_props_intros dest!:)

  show "invar_goes_through_current initial_state"
    by (auto simp add: initial_state_def dest:  hd_of_vwalk_bet'' intro!: invar_props_intros)
qed

lemma BFS_correct_1:
  "\<lbrakk>u \<in> t_set srcs; t \<notin> t_set (visited (BFS initial_state))\<rbrakk>
         \<Longrightarrow> \<nexists>p. vwalk_bet (Graph.digraph_abs G) u p t"
  apply(intro BFS_correct_1_ret_1[where bfs_state = "BFS initial_state"])
  by(auto intro: invar_holds_intros ret_holds_intros)

lemma BFS_correct_2:
  "\<lbrakk>t \<in> t_set (visited (BFS initial_state)) - t_set srcs\<rbrakk>
         \<Longrightarrow> distance_set (Graph.digraph_abs G) (t_set srcs) t =
         distance_set (Graph.digraph_abs (parents (BFS initial_state))) (t_set srcs) t"
  apply(intro BFS_correct_2_ret_1[where bfs_state = "BFS initial_state"])
  by(auto intro: invar_holds_intros ret_holds_intros)

lemma BFS_correct_3:
  "\<lbrakk>u \<in> t_set srcs; Vwalk.vwalk_bet (Graph.digraph_abs (parents (BFS initial_state))) u p v\<rbrakk>
         \<Longrightarrow> length p - 1 = distance_set (Graph.digraph_abs G) (t_set srcs) v"
  apply(intro BFS_correct_3_ret_1[where bfs_state = "BFS initial_state"])
  by(auto intro: invar_holds_intros ret_holds_intros)

lemma BFS_correct_4:
  "(Graph.digraph_abs (parents (BFS initial_state))) \<subseteq> (Graph.digraph_abs G)"
  apply(intro BFS_correct_4_ret_1[where bfs_state = "BFS initial_state"])
  by(auto intro: invar_holds_intros ret_holds_intros)

lemma BFS_graph_path_implies_parent_path:
  assumes "s \<in> t_set srcs" "vwalk_bet (Graph.digraph_abs G) s p t"  "t \<notin> t_set srcs"
  shows   "\<exists> q s'. vwalk_bet (Graph.digraph_abs (parents (BFS initial_state))) s' q t
                 \<and> s' \<in> t_set srcs \<and> length q \<le> length p"
    using BFS_correct_1[OF assms(1), of t] assms(2,3)  
    by(fastforce intro!: exists_shorter_path_in_level_compliant_graph[OF _ _ assms(1,3,2)] 
                 intro: BFS_correct_3 BFS_correct_2)

lemma parent_path_cheaper:
  assumes "s \<in> t_set srcs" "vwalk_bet (Graph.digraph_abs G) s p t" "t \<notin> t_set srcs"
          "vwalk_bet (Graph.digraph_abs (parents (BFS initial_state))) s q t"
        shows "length q \<le> length p" 
  by(auto intro!: shorter_path_in_level_compliant_graph[OF _  assms(1,3,2,4,1)] BFS_correct_3)
                                                            
lemma source_in_bfs_tree: 
  assumes "(s, x) \<in> (Graph.digraph_abs G)" "s \<in> t_set srcs" "x \<notin> t_set srcs"
  shows "\<exists> s'. s' \<in> t_set srcs 
             \<and> s' \<in> dVs ((Graph.digraph_abs (parents (BFS initial_state))))" 
  using BFS_graph_path_implies_parent_path[OF assms(2) edges_are_vwalk_bet assms(3)] 
        assms(1) vwalk_bet_endpoints(1)[OF ] by auto

subsection \<open>BFS and the Level Graph\<close>

lemma invar_parents_in_level_graphI: 
  "(Graph.digraph_abs (parents state)) \<subseteq>  level_graph (Graph.digraph_abs G) (t_set srcs) 
  \<Longrightarrow> invar_parents_in_level_graph state"
  by(auto simp add: invar_parents_in_level_graph_def)

lemma invar_parents_in_level_graphE: 
  "\<lbrakk>invar_parents_in_level_graph state;
    ((Graph.digraph_abs (parents state)) \<subseteq>  level_graph (Graph.digraph_abs G) (t_set srcs) \<Longrightarrow> P)\<rbrakk>
    \<Longrightarrow> P"
  by(auto simp add: invar_parents_in_level_graph_def)

lemma invar_parents_in_level_graph_holds_ret1[invar_holds_intros]:
  "invar_parents_in_level_graph state \<Longrightarrow> invar_parents_in_level_graph (BFS_ret1 state)"
  by(auto intro!: invar_parents_in_level_graphI)

lemma invar_parents_in_level_graph_holds_upd1[invar_holds_intros]:
  assumes  "BFS_call_1_conds state" "invar_parents_in_level_graph state"
           "invar_1 state" "invar_3_2 state" "invar_2 state" "invar_3_1 state" "invar_3_4 state"
           "invar_current_reachable state" 
   shows   "invar_parents_in_level_graph (BFS_upd1 state)"
proof(cases "next_frontier_and_current (current state) (visited state)",goal_cases)
  case (1 front' vis')
  note one = this
  have current_in_vis:"t_set (current state) \<subseteq> t_set (visited state)" 
and  vis_in_G: "[visited state]\<^sub>s \<subseteq> dVs [G]\<^sub>g" 
      using assms by(auto elim: invar_2_props)
    note next_frontier[simp] = next_frontier(2)[OF _ _ _ current_in_vis 1(1) vis_in_G]
      note next_vis[simp] = next_vis[OF _ _ _ current_in_vis 1(1) vis_in_G]
  have others: "vset_inv2 (current state)" "vset_inv (visited state)" "Graph.graph_inv G"
    using assms(3) by(auto elim: invar_1_props)
  note next_frontier= next_frontier[OF others]
  have "(x, y) \<in> [expand_tree (parents state) (current state) (visited state )]\<^sub>g 
         \<Longrightarrow> (x, y) \<in> level_graph [G]\<^sub>g [srcs]\<^sub>s" for x y
  proof(subst (asm) expand_tree(2)[OF _ _ _ _ current_in_vis vis_in_G] , goal_cases)
    case 5
    show ?thesis
    proof(cases "(x, y)  \<in> [parents state]\<^sub>g")
      case True
      then show ?thesis 
        using assms(2) by (auto elim: invar_parents_in_level_graphE)
    next
      case False
      hence x_y_props:"x \<in> [current state]\<^sub>s" "y \<in> neighbourhood [G]\<^sub>g x - [visited state]\<^sub>s"
        using "5" current_in_vis assms(3)  by (auto elim!: invar_1_props)
    have edges_in_G:"(x, y) \<in> [G]\<^sub>g"
      using "5" assms(5) invar_2_def  by fastforce
    have dist_x_le_pinfty:"distance_set [G]\<^sub>g [srcs]\<^sub>s x < \<infinity>" 
      using  "5"  assms(5,8) dVsI(1)
      by(auto simp add: invar_2_def invar_current_reachable_def)
    have y_in_next_frontier: "y\<in> [front']\<^sub>s"
      using x_y_props current_in_vis
      by(subst next_frontier)(auto intro: invar_1_props[OF assms(3)])
    have "distance_set [G]\<^sub>g [srcs]\<^sub>s y = distance_set [G]\<^sub>g [srcs]\<^sub>s x + 1"
    proof(rule eqI_strict_less_contradiction_cases, goal_cases)
      case 1
      hence y_leq_x:"distance_set [G]\<^sub>g [srcs]\<^sub>s y \<le> distance_set [G]\<^sub>g [srcs]\<^sub>s x"
        using  ileI1 
        by(force simp add: plus_1_eSuc(1)[symmetric])
      moreover hence x_leq_y:"distance_set [G]\<^sub>g [srcs]\<^sub>s x \<le> distance_set [G]\<^sub>g [srcs]\<^sub>s y"
        using  invar_3_2_holds_upd1_new[OF assms(1,3,5,6,4,7,8)]  x_y_props(1) y_in_next_frontier 
              assms(3,8) x_y_props(2) current_in_vis one(1) others(1,2,3) 
          leD[of "distance_set [G]\<^sub>g [srcs]\<^sub>s x" "distance_set [G]\<^sub>g [srcs]\<^sub>s y"]
          in_mono[of "[current state]\<^sub>s" "[visited state]\<^sub>s" x]
        by (auto intro: invar_1_props[OF  assms(3)] 
              simp add: invar_3_2_def BFS_upd1_def Let_def new_visited_simp[OF assms(3,5)] 
              simp del: next_frontier
                  elim: invar_3_4_props)  
     ultimately have dist_eq:"distance_set [G]\<^sub>g [srcs]\<^sub>s x = distance_set [G]\<^sub>g [srcs]\<^sub>s y" by simp
     thus ?case
       using x_y_props(1,2) current_in_vis
       by(auto intro: invar_3_1_props[OF assms(6), of x y]  invar_1_props[OF assms(3)]) 
    next
      case 2
      then show ?case 
        using  srcs_invar(1) x_y_props(2) 
               distance_set_neighbourhood[of y "[G]\<^sub>g" x "t_set srcs"] 
        by auto
    qed
    thus ?thesis 
      by (simp add: edges_in_G in_level_graphI)
  qed
  qed (auto intro: invar_1_props[OF assms(3)] invar_parents_in_level_graphE[OF assms(2)])
  thus ?thesis
    using one
    by(auto intro: invar_parents_in_level_graphI simp add: BFS_upd1_def Let_def)
qed

lemma invar_parents_in_level_graph_holds:
  assumes  "BFS_dom state" "invar_parents_in_level_graph state"
           "invar_1 state" "invar_2 state" "invar_3_1 state"  
           "invar_3_2 state"  "invar_3_3 state" "invar_3_4 state"
           "invar_current_reachable state" 
  shows    "invar_parents_in_level_graph (BFS state)"
  using assms(2-)
proof(induction rule: BFS_induct[OF assms(1)])
  case IH: (1 bfs_state)
  show ?case
    by(rule BFS_cases[where bfs_state = bfs_state])
      (auto intro!: IH(2-)  intro: invar_holds_intros  simp: BFS_simps[OF IH(1)])
qed

lemma invar_parents_in_level_graph_initial:
  "invar_parents_in_level_graph initial_state"
  by (simp add: Graph.digraph_abs_empty initial_state_def invar_parents_in_level_graph_def)

lemma invar_parents_in_level_graph_final:
  "invar_parents_in_level_graph (BFS initial_state)"
  by (simp add: invar_parents_in_level_graph_holds invar_parents_in_level_graph_initial)

definition "invar_level_so_far_in_parents state =
  (\<forall> u v. u \<in> (t_set (visited state)) \<and> 
         v \<in>  (t_set (visited state)) \<and>
         (u, v) \<in> Graph.digraph_abs G \<and>
         distance_set (Graph.digraph_abs G) (t_set srcs) v 
         =  distance_set (Graph.digraph_abs G) (t_set srcs) u + 1
          \<longrightarrow> (u, v) \<in> Graph.digraph_abs (parents state))"

lemma invar_level_so_far_in_parentsI:
  "(\<And> u v. \<lbrakk>u \<in> (t_set (visited state) \<union> t_set (current state));
            v \<in> (t_set (visited state) \<union> t_set (current state));
            (u, v) \<in> Graph.digraph_abs G;
            distance_set (Graph.digraph_abs G) (t_set srcs) v 
            = distance_set (Graph.digraph_abs G) (t_set srcs) u + 1\<rbrakk>
             \<Longrightarrow> (u, v) \<in> Graph.digraph_abs (parents state))
   \<Longrightarrow> invar_level_so_far_in_parents state"
  by(auto simp add: invar_level_so_far_in_parents_def)

lemma invar_level_so_far_in_parentsE:
  "invar_level_so_far_in_parents state \<Longrightarrow>
    ((\<And> u v. \<lbrakk>u \<in> (t_set (visited state) );
              v \<in> (t_set (visited state));
              (u, v) \<in> Graph.digraph_abs G;
              distance_set (Graph.digraph_abs G) (t_set srcs) v 
              = distance_set (Graph.digraph_abs G) (t_set srcs) u + 1\<rbrakk>
             \<Longrightarrow> (u, v) \<in> Graph.digraph_abs (parents state))
        \<Longrightarrow> P) 
     \<Longrightarrow> P"
  by(auto simp add: invar_level_so_far_in_parents_def)

lemma invar_level_so_far_in_parents_ret1_holds[invar_holds_intros]:
  "invar_level_so_far_in_parents state \<Longrightarrow> invar_level_so_far_in_parents (BFS_ret1 state)"
  by(auto elim: invar_level_so_far_in_parentsE intro: invar_level_so_far_in_parentsI)

lemma invar_level_so_far_in_parents_upd1_holds[invar_holds_intros]:
  assumes "BFS_call_1_conds state" "invar_level_so_far_in_parents state"
          "invar_1 state" "invar_3_1 state" "invar_3_2 state" "invar_3_3 state"
          "invar_3_4 state" "invar_2 state"
  shows   "invar_level_so_far_in_parents (BFS_upd1 state)"  
proof(cases "next_frontier_and_current (current state) (visited state)",goal_cases)
  case (1 front' vis')
  note One = this
  have current_in_vis:"t_set (current state) \<subseteq> t_set (visited state)" 
and  vis_in_G: "[visited state]\<^sub>s \<subseteq> dVs [G]\<^sub>g" 
      using assms by(auto elim: invar_2_props)
    note next_frontier[simp] = next_frontier(2)[OF _ _ _ current_in_vis 1(1) vis_in_G]
    note next_vis[simp] = next_vis[OF _ _ _ current_in_vis 1(1) vis_in_G]
    have vis'_is: " [vis']\<^sub>s = [visited state]\<^sub>s \<union> [front']\<^sub>s" 
      using assms(3) graph_inv(1) invar_1_def next_vis(2) by blast
  have next_frontier_is:"[front']\<^sub>s
      = \<Union> {neighbourhood [G]\<^sub>g u |u. u \<in> [current state]\<^sub>s} - [visited state]\<^sub>s" 
    by(intro  next_frontier)(auto intro: invar_1_props[OF assms(3)] invar_2_props[OF assms(8)])
  have new_parents_are: "[expand_tree (parents state) (current state) (visited state)]\<^sub>g
      = [parents state]\<^sub>g \<union>
        {(u, v) |u v.
         u \<in> [current state]\<^sub>s \<and> v \<in> neighbourhood [G]\<^sub>g u - [visited state]\<^sub>s}"
    by(intro expand_tree(2))(auto intro: invar_1_props[OF assms(3)] invar_2_props[OF assms(8)])
  have new_visited_are:"[visited state \<union>\<^sub>G current state]\<^sub>s = [visited state]\<^sub>s \<union> [current state]\<^sub>s"
    by(subst set_ops.set_union)(auto intro: invar_1_props[OF assms(3)])
  have currents_are_visited: "t_set (current state) \<subseteq> t_set (visited state)" 
    using assms(8) by(auto elim: invar_2_props)
  show ?thesis
  proof(rule invar_level_so_far_in_parentsI, goal_cases)
    case (1 u v)
    note one = this
    have case1: "u \<in> [current state]\<^sub>s"
      if asm: "u \<in> [visited state]\<^sub>s"  "(u, v) \<notin> [parents state]\<^sub>g" 
      apply(rule invar_3_3_props[OF assms(6)], rule invar_level_so_far_in_parentsE[OF assms(2)])
      using "1"(4) asm neighbourhoodD[OF 1(3)] currents_are_visited by blast
    have case2: "u \<in> [current state]\<^sub>s"
      if asm: "v \<in> [visited state]\<^sub>s" "(u, v) \<notin> [parents state]\<^sub>g" 
      apply(rule invar_3_4_props[OF assms(7)])
      using "1"(3,4) asm currents_are_visited assms(2) sup.order_iff[of "[current state]\<^sub>s" "[visited state]\<^sub>s"] 
      by (force elim!: invar_level_so_far_in_parentsE)
    have case3: False
      if asm: "ua \<in> [current state]\<^sub>s" "(u, v) \<notin> [parents state]\<^sub>g" "v \<in> [visited state]\<^sub>s"for ua
    proof-
      have "distance_set  [G]\<^sub>g (t_set srcs) v \<le> distance_set  [G]\<^sub>g (t_set srcs) ua"
        using assms(5) that(1,3) by auto
      hence "distance_set  [G]\<^sub>g (t_set srcs) v \<le> distance_set  [G]\<^sub>g (t_set srcs) u"
        using assms(5) case2 that(2,3) by blast
      moreover have "distance_set [G]\<^sub>g [srcs]\<^sub>s u < \<infinity>"
        using   one(3,4) that(2,3)  assms(2) case2 currents_are_visited 
        by (auto elim!: invar_level_so_far_in_parentsE) 
      ultimately show False 
        using one(4) by simp
    qed
    have case4: "u \<in> [current state]\<^sub>s"
      if "v \<in> [current state]\<^sub>s"  "(u, v) \<notin> [parents state]\<^sub>g"
      apply(rule invar_3_4_props[OF assms(7)])
      using  case1  le_iff_add one(4) that(1,2) 
      by fastforce
    have case5: False if
        asm:  "(u, v) \<notin> [parents state]\<^sub>g" " v \<in> [current state]\<^sub>s"
      using 1(3,4) UnI2 asm  case4  that assms(2) currents_are_visited
      by(auto elim!: invar_level_so_far_in_parentsE simp add: in_mono)
    have case6: "u \<in> [current state]\<^sub>s"
      if asm: "v \<in> neighbourhood [G]\<^sub>g uaa"  "uaa \<in> [current state]\<^sub>s" 
              "(u, v) \<notin> [parents state]\<^sub>g" for uaa
    proof-
      have v_not_in:"v \<notin> [current state]\<^sub>s" "v \<notin> [visited state]\<^sub>s"
        using case2 case3 case5 that(3) by auto
      have "distance_set  [G]\<^sub>g (t_set srcs) uaa + 1 = distance_set [G]\<^sub>g (t_set srcs) v"
        using  case1 distance_set_neighbourhood[OF that(1)  srcs_invar(1)]
               one(4) that(2,3) 
        by (auto intro: invar_3_4_props[OF assms(7)] invar_3_1_props[OF assms(4), of uaa u])
      thus ?thesis 
        using  one(4) that(2) 
        by(auto intro:   invar_3_1_props[OF assms(4), of uaa u])
    qed
    show ?case 
      using one(1,2,3,4) assms(3,8) One
      by(auto intro: invar_level_so_far_in_parentsE[OF assms(2)] case1 case2 case3 case4 case5 case6
            simp add: BFS_upd1_def Let_def next_frontier_is new_parents_are
                      new_visited_are new_visited_simp vis'_is)
      
 qed
qed

lemma invar_level_so_far_in_parents_holds:
  assumes  "BFS_dom state" "invar_level_so_far_in_parents state"
           "invar_1 state" "invar_2 state" "invar_3_1 state"  
           "invar_3_2 state"  "invar_3_3 state" "invar_3_4 state"
           "invar_current_reachable state" 
  shows    "invar_level_so_far_in_parents (BFS state)"
  using assms(2-)
proof(induction rule: BFS_induct[OF assms(1)])
  case IH: (1 bfs_state)
  show ?case
    by(rule BFS_cases[where bfs_state = bfs_state])
      (auto intro!: IH(2-)  intro: invar_holds_intros  simp: BFS_simps[OF IH(1)])
qed

lemma invar_level_so_far_in_parents_initial: 
  "invar_level_so_far_in_parents initial_state" 
proof(rule invar_level_so_far_in_parentsI, goal_cases)
  case (1 u v)
  moreover hence v_in_G:"v \<in> dVs [G]\<^sub>g" 
    by auto
  ultimately show ?case 
    by(auto simp add: distance_set_0[symmetric, OF v_in_G] Graph.digraph_abs_empty initial_state_def)
qed

lemma invar_level_so_far_in_parents_final:
  "invar_level_so_far_in_parents (BFS initial_state)"
  by (simp add: invar_level_so_far_in_parents_holds invar_level_so_far_in_parents_initial)

lemma no_parent_edges_unreachable:
  "(Graph.digraph_abs (parents (BFS initial_state))) \<inter>
   { (u, v) | u v. distance_set (Graph.digraph_abs G) (t_set srcs) u = \<infinity>} = {}"
proof-
  have "\<lbrakk>(u, v) \<in> [parents (local.BFS initial_state)]\<^sub>g ; distance_set [G]\<^sub>g [srcs]\<^sub>s u = \<infinity>\<rbrakk>
         \<Longrightarrow> False" for u v
  proof(goal_cases)
    case 1
    have u_seen: "u \<in>
         [visited (local.BFS initial_state)]\<^sub>s \<union> [current (local.BFS initial_state)]\<^sub>s"
      using invar_2_props[OF invar_2_holds[OF initial_state_props(4,1,2)]]  "1"(1) dVsI(1) by auto
    hence "distance_set [G]\<^sub>g [srcs]\<^sub>s u < \<infinity>"
      using invar_current_reachable_holds[OF initial_state_props(4,1,2,10)]
      by(auto intro: invar_current_reachable_props)
    thus False
      by (simp add: "1"(2))
  qed
  thus ?thesis
    by auto
qed

lemma BFS_level_graph:
  "(Graph.digraph_abs (parents (BFS initial_state)))
   = level_graph (Graph.digraph_abs G) (t_set srcs)
          - {(u, v) | u v. distance_set (Graph.digraph_abs G) (t_set srcs) u = \<infinity>}"
proof(rule, goal_cases)
  case 1
  then show ?case 
    using  invar_parents_in_level_graph_final no_parent_edges_unreachable
    by(auto simp add: invar_parents_in_level_graph_def)
next
  case 2
  show ?case
  proof(rule, goal_cases)
    case (1 e)
    then obtain x y where xy_prop:"e = (x, y)" "(x, y) \<in> level_graph [G]\<^sub>g [srcs]\<^sub>s"
                                  "distance_set [G]\<^sub>g [srcs]\<^sub>s x < \<infinity>"
      by(cases e) auto
    obtain p s where s_p_x_path: "s \<in> [srcs]\<^sub>s" "distance_set [G]\<^sub>g [srcs]\<^sub>s x = length p -1" 
                          "vwalk_bet [G]\<^sub>g s p x" 
      using  dist_not_inf'[OF xy_prop(3)[ simplified  enat_ord_simps(4)]] reachable_dist_2
      by force
    moreover have lg_unfolded: "(x, y) \<in>  [G]\<^sub>g" "distance_set [G]\<^sub>g [srcs]\<^sub>s x + 1= distance_set [G]\<^sub>g [srcs]\<^sub>s y" 
      using xy_prop(2) by(auto simp add: level_graph_def)
    ultimately have  s_p_y_path: "vwalk_bet [G]\<^sub>g s (p@[y]) y"
      by(auto intro!: vwalk_append_intermediate_edge) 
    have "x \<in> [visited (local.BFS initial_state)]\<^sub>s \<union> [current (local.BFS initial_state)]\<^sub>s"
      using  BFS_correct_1 s_p_x_path(1,3)
      by auto
    moreover have "y \<in> [visited (local.BFS initial_state)]\<^sub>s \<union> [current (local.BFS initial_state)]\<^sub>s"
      using  BFS_correct_1 s_p_x_path(1) s_p_y_path
      by auto
    moreover have "[current (local.BFS initial_state)]\<^sub>s \<subseteq> [visited (local.BFS initial_state)]\<^sub>s"
      using invar_2_holds[OF initial_state_props(4, 1,2)]
      by(auto elim: invar_2_props)
    ultimately show ?case 
      using lg_unfolded invar_level_so_far_in_parents_final  
      by(force elim!: invar_level_so_far_in_parentsE simp add: xy_prop(1))
  qed
qed

end text \<open>context\<close>
end text \<open>locale @{const BFS}\<close>

record ('parents, 'vset) BFS_dist_state = dists:: "'parents" current:: "'vset" visited:: "'vset" current_dist::nat

locale BFS_distance =
 BFS
 where lookup = lookup for lookup :: "'adjmap \<Rightarrow> 'ver \<Rightarrow> 'vset option" +
 fixes some_dist::'dist
  and set_all_dists_in_set::"'dist \<Rightarrow> 'vset \<Rightarrow> nat \<Rightarrow> 'dist"
  and dist_lookup::"'dist \<Rightarrow> 'ver \<Rightarrow> nat"
  and dist_invar::"'dist \<Rightarrow> 'ver set \<Rightarrow> bool"
  assumes set_all_dists_in_set:
    "\<And> dists front S n. \<lbrakk>vset_inv front; t_set front \<subseteq> dVs (Graph.digraph_abs G); dist_invar dists S\<rbrakk> \<Longrightarrow> 
                    dist_invar (set_all_dists_in_set dists front n) (S \<union> t_set front)"
    "\<And> dists front S n x. \<lbrakk>vset_inv front; t_set front \<subseteq> dVs (Graph.digraph_abs G); 
          dist_invar dists S; x \<in> t_set front\<rbrakk> \<Longrightarrow> 
          dist_lookup (set_all_dists_in_set dists front n) x = n"
    "\<And> dists front S n x. \<lbrakk>vset_inv front; t_set front \<subseteq> dVs (Graph.digraph_abs G); 
                       dist_invar dists S; x \<in> S - t_set front\<rbrakk> \<Longrightarrow> 
          dist_lookup (set_all_dists_in_set dists front n) x = dist_lookup dists x"
  and some_dist: "dist_invar some_dist {}"
begin


definition "initial_dist_state = 
      \<lparr>dists = set_all_dists_in_set some_dist srcs 0, current = srcs, visited = srcs, current_dist = 0\<rparr>"

function (domintros) BFS_dist::"('dist, 'vset) BFS_dist_state \<Rightarrow> ('dist, 'vset) BFS_dist_state" where
  "BFS_dist BFS_state = 
     (
        if current BFS_state \<noteq> \<emptyset>\<^sub>N then
          let
          (current', visited') =  next_frontier_and_current (current BFS_state)  (visited BFS_state);
           d = current_dist BFS_state;
           dist' = set_all_dists_in_set (dists BFS_state) current' (Suc (current_dist BFS_state))
          in 
            BFS_dist (BFS_state \<lparr>dists:= dist', visited := visited', current := current',
                                 current_dist := Suc d\<rparr>)
         else
          BFS_state)"
  by pat_completeness auto

partial_function (tailrec) BFS_dist_impl::
   "('dist, 'vset) BFS_dist_state \<Rightarrow> ('dist, 'vset) BFS_dist_state" where
  "BFS_dist_impl BFS_state = 
     (
        if current BFS_state \<noteq> \<emptyset>\<^sub>N then
          let
          (current', visited') =  next_frontier_and_current (current BFS_state)  (visited BFS_state);
           d = current_dist BFS_state;
           dist' = set_all_dists_in_set (dists BFS_state) current' (Suc d)
          in 
            BFS_dist_impl (BFS_state \<lparr>dists:= dist', visited := visited', current := current',
                   current_dist := Suc d\<rparr>)
         else
          BFS_state)"

lemma BFS_dist_impl_same:
 "BFS_dist_dom state \<Longrightarrow>  BFS_dist_impl state = BFS_dist state"
proof(induction rule: BFS_dist.pinduct)
  case (1 BFS_state)
  then show ?case
    by(auto simp add: BFS_dist_impl.simps[of BFS_state] BFS_dist.psimps Let_def split: if_split prod.split)
qed

lemma BFS_dist_same_dom:
  assumes "BFS_state.current state = current state'" "BFS_state.visited state = visited state'"
  shows "BFS_dist_dom state' = BFS_dom state"
proof(rule, goal_cases)
  case 1
  then show ?case 
    using assms
proof(induction arbitrary: state rule: BFS_dist.pinduct)
  case (1 BFS_state)
  show ?case
    apply(rule BFS.domintros)
    apply(rule 1(2))
    using 1(3,4) 
    by auto
qed    
next
  case 2
  then show ?case 
    using assms
proof(induction arbitrary: state' rule: BFS.pinduct)
  case (1 BFS_state)
  show ?case
    apply(rule BFS_dist.domintros)
    apply(rule 1(2))
    using 1(3,4) 
    by auto
qed    
qed

definition BFS_dist_cond_cont :: "('dist, 'vset) BFS_dist_state \<Rightarrow> bool" where
  "BFS_dist_cond_cont s \<longleftrightarrow> current s \<noteq> \<emptyset>\<^sub>N"

definition BFS_dist_cond_ret :: "('dist, 'vset) BFS_dist_state \<Rightarrow> bool" where
  "BFS_dist_cond_ret s \<longleftrightarrow> current s = \<emptyset>\<^sub>N"

definition BFS_dist_upd :: "('dist, 'vset) BFS_dist_state \<Rightarrow> ('dist, 'vset) BFS_dist_state" where
  "BFS_dist_upd s = 
    (let 
       (current', visited') = next_frontier_and_current (current s) (visited s);
       d = current_dist s;
       dist' = set_all_dists_in_set (dists s) current' (Suc d)
     in 
       s\<lparr>dists := dist', visited := visited', current := current', current_dist := Suc d\<rparr>)"

definition BFS_dist_ret :: "('dist, 'vset) BFS_dist_state \<Rightarrow> ('dist, 'vset) BFS_dist_state" where
  "BFS_dist_ret s = s"

lemma dom_if_ret: "BFS_dist_cond_ret s \<Longrightarrow> BFS_dist_dom s"
  by(rule BFS_dist.domintros)(auto simp add: BFS_dist_cond_ret_def)

lemma BFS_dist_simps:
  "\<lbrakk>BFS_dist_cond_cont s; BFS_dist_dom s\<rbrakk> \<Longrightarrow> BFS_dist s = BFS_dist (BFS_dist_upd s)"
  "BFS_dist_cond_ret s \<Longrightarrow> BFS_dist s = BFS_dist_ret s"
  using dom_if_ret
  by(auto simp add: BFS_dist.psimps BFS_dist_cond_cont_def BFS_dist_cond_ret_def BFS_dist_upd_def
                    BFS_dist_ret_def Let_def  
            split: prod.split)

lemma BFS_dist_induct :
  assumes "BFS_dist_dom s"
  assumes loop: "\<And>s. \<lbrakk>BFS_dist_dom s;
                         BFS_dist_cond_cont s \<Longrightarrow> P (BFS_dist_upd s)\<rbrakk> \<Longrightarrow> P s"
  shows "P s"
using assms
proof (induct s rule: BFS_dist.pinduct)
  case (1 s)
  show ?case
  proof(cases "BFS_dist_cond_cont s")
    case True
    show ?thesis 
      apply(rule loop)
      using True 1(1)
      by (auto intro: 1(2,3) 
            simp add: BFS_dist_cond_cont_def BFS_dist_upd_def Let_def
               split: prod.split)
  next
    case False
    thus ?thesis
      using "1.hyps"(1) "1.prems"
      by(auto simp add: BFS_dist_cond_ret_def)
qed
qed

context 
  assumes BFS_axiom: BFS_axiom
begin

definition "distances_invar old_state state =
   (dist_invar (dists state) (t_set (visited state)) \<and>
   BFS_state.visited old_state = visited state \<and>
   BFS_state.current old_state = current state \<and>
    (Graph.digraph_abs (parents old_state)) = 
     {(x, y) | x y. x \<in> t_set (visited state) \<and> y \<in> t_set (visited state)
       \<and> dist_lookup (dists state) x + 1 = dist_lookup (dists state) y \<and>
      (x, y) \<in> Graph.digraph_abs G} \<and>
   (\<forall> x \<in> t_set (visited state). dist_lookup (dists state) x \<le> current_dist state) \<and>
   (\<forall> x \<in> t_set (visited state). x \<in> t_set (current state) \<longleftrightarrow> 
           dist_lookup (dists state) x = current_dist state))"

lemma distances_invarI:
  "\<lbrakk> dist_invar (dists state) (t_set (visited state));
     BFS_state.visited old_state = visited state;
     BFS_state.current old_state = current state;
     Graph.digraph_abs (parents old_state) = 
       {(x, y) | x y. x \<in> t_set (visited state) \<and> y \<in> t_set (visited state) 
         \<and> dist_lookup (dists state) x + 1 = dist_lookup (dists state) y 
          \<and> (x, y) \<in> Graph.digraph_abs G};
     \<And> x. x \<in> t_set (visited state) \<Longrightarrow> dist_lookup (dists state) x \<le> current_dist state;
     \<And> x. x \<in> t_set (visited state) \<Longrightarrow> dist_lookup (dists state) x = current_dist state \<longleftrightarrow>
            x \<in> t_set (current state) \<rbrakk>
   \<Longrightarrow> distances_invar old_state state"

and distances_invarE:
  "\<lbrakk> distances_invar old_state state;
     \<lbrakk> dist_invar (dists state) (t_set (visited state));
       BFS_state.visited old_state = visited state;
       BFS_state.current old_state = current state;
       Graph.digraph_abs (parents old_state) = 
         {(x, y) | x y. x \<in> t_set (visited state) \<and> y \<in> t_set (visited state) 
           \<and> dist_lookup (dists state) x + 1 = dist_lookup (dists state) y 
           \<and> (x, y) \<in> Graph.digraph_abs G};
       \<And> x. x \<in> t_set (visited state) \<Longrightarrow> dist_lookup (dists state) x \<le> current_dist state;
       \<And> x. x \<in> t_set (visited state) \<Longrightarrow> dist_lookup (dists state) x = current_dist state \<longleftrightarrow>
            x \<in> t_set (current state) \<rbrakk> \<Longrightarrow> P \<rbrakk>
   \<Longrightarrow> P"

and distances_invarD:
  "distances_invar old_state state \<Longrightarrow> dist_invar (dists state) (t_set (visited state))"
  "distances_invar old_state state \<Longrightarrow> BFS_state.visited old_state = visited state"
  "distances_invar old_state state \<Longrightarrow> BFS_state.current old_state = current state"
  "\<lbrakk>distances_invar old_state state; x \<in> t_set (visited state)\<rbrakk>
     \<Longrightarrow> dist_lookup (dists state) x \<le> current_dist state"
  "\<lbrakk>distances_invar old_state state; x \<in> t_set (visited state);
     dist_lookup (dists state) x = current_dist state\<rbrakk> 
     \<Longrightarrow>  x \<in> t_set (current state)"
  "\<lbrakk>distances_invar old_state state; x \<in> t_set (visited state); x \<in> t_set (current state)\<rbrakk> 
     \<Longrightarrow> dist_lookup (dists state) x = current_dist state"
  "distances_invar old_state state \<Longrightarrow> Graph.digraph_abs (parents old_state) = 
       {(x, y) | x y. x \<in> t_set (visited state) \<and> y \<in> t_set (visited state) 
         \<and> dist_lookup (dists state) x + 1 = dist_lookup (dists state) y \<and>
        (x, y) \<in> Graph.digraph_abs G}"
  unfolding distances_invar_def by auto

lemmas invar_2_props = invar_2_props[OF BFS_axiom]
lemmas invar_1_def = invar_1_def
lemmas graph_inv = graph_inv[OF BFS_axiom]
lemmas invar_3_1_props = invar_3_1_props[OF BFS_axiom]
lemmas invar_3_2_props = invar_3_2_props[OF BFS_axiom]
lemmas invar_3_3_props = invar_3_3_props[OF BFS_axiom]
lemmas invar_3_4_props = invar_3_4_props[OF BFS_axiom]
lemmas invar_1_props = invar_1_props[OF BFS_axiom]
lemmas BFS_simps = BFS_simps[OF BFS_axiom]
lemmas invar_1_holds_upd1 =  invar_1_holds_upd1[OF BFS_axiom]
lemmas invar_2_holds_upd1 =  invar_2_holds_upd1[OF BFS_axiom]
lemmas srcs_invar = srcs_invar[OF BFS_axiom]
lemmas srcs_in_G = srcs_in_G[OF BFS_axiom]
lemmas BFS_level_graph = BFS_level_graph[OF BFS_axiom]

lemma dist_invar_pres_one_step:
  assumes "BFS_call_1_conds state" "invar_1 state" 
          "invar_2 state" "distances_invar state dist_state"
    shows "distances_invar (BFS_upd1 state) (BFS_dist_upd dist_state)"
proof(cases "next_frontier_and_current (BFS_state.current state) (BFS_state.visited state)",goal_cases)
  case (1 front' vis')
  note One = this
  have current_in_vis:"t_set (BFS_state.current state) \<subseteq> t_set (BFS_state.visited state)" 
and  vis_in_G: "[BFS_state.visited state]\<^sub>s \<subseteq> dVs [G]\<^sub>g" 
      using assms by(auto elim!: invar_2_props)
    note next_frontier[simp] = next_frontier[OF _ _ _ current_in_vis 1(1) vis_in_G]
    note next_vis[simp] = next_vis[OF _ _ _ current_in_vis 1(1) vis_in_G]
    have vis'_is: " [vis']\<^sub>s = [BFS_state.visited state]\<^sub>s \<union> [front']\<^sub>s" 
      using assms(2) graph_inv(1) invar_1_def next_vis(2) by blast
    note distances_invarD = distances_invarD[OF assms(4)]
      note expand_tree[simp] = expand_tree(1,2)[OF _ _ _ _ current_in_vis]
         expand_tree(3)[OF _ _ _ _ _ current_in_vis]
    note invar_1D = invar_1D[OF assms(2)]
 
    have claim1: 
     "dist_invar (dists (BFS_dist_upd dist_state)) [BFS_dist_state.visited (BFS_dist_upd dist_state)]\<^sub>s"
    and claim2: 
      "BFS_state.visited (BFS_upd1 state) = BFS_dist_state.visited (BFS_dist_upd dist_state)"
    and claim3: 
      "BFS_state.current (BFS_upd1 state) = BFS_dist_state.current (BFS_dist_upd dist_state)"
       using One assms(2)
       by(auto intro!: set_all_dists_in_set(1) next_frontier(1)
          simp add: BFS_dist_upd_def distances_invarD(2,3) Let_def vis'_is graph_inv(1) distances_invarD(1)
                     BFS_upd1_def
             elim!: invar_1_props) 
     let "?P" = " \<lambda> x y.
         Suc (dist_lookup (set_all_dists_in_set (dists dist_state) front' (Suc (current_dist dist_state))) x) =
     dist_lookup (set_all_dists_in_set (dists dist_state) front' (Suc (current_dist dist_state))) y"

     have old_parent_not_in_new_front:
       "(x, y) \<in> [parents state]\<^sub>g \<Longrightarrow> x \<notin> t_set front'"
        and old_parent_not_in_new_front':
       "(x, y) \<in> [parents state]\<^sub>g \<Longrightarrow> y \<notin> t_set front'" for x y 
       using assms(3,2) graph_inv(1)
       by(auto elim!: invar_2_props invar_1_props)

     have new_dist_values_front':
      "x \<in> t_set front' \<Longrightarrow>
         dist_lookup (set_all_dists_in_set (dists dist_state) front' (Suc (current_dist dist_state))) x
         = Suc (current_dist dist_state)" for x
       using assms(2) graph_inv(1) distances_invarD(1)
       by(intro set_all_dists_in_set(2))(auto elim!: invar_1_props)

     have new_dist_values_old:
      "x \<in> t_set (BFS_state.visited state)  \<Longrightarrow>
         dist_lookup (set_all_dists_in_set (dists dist_state) front' (Suc (current_dist dist_state))) x
         = dist_lookup (dists dist_state) x" for x
       using assms(2) graph_inv(1)  distances_invarD(1,2)
       by(intro set_all_dists_in_set(3)[of _ _ "t_set (BFS_state.visited state)"])
         (auto elim!: invar_1_props simp add: next_frontier(1))

     have  parent_edge_visited:"(x, y) \<in> [parents state]\<^sub>g \<Longrightarrow> x \<in> [BFS_state.visited state]\<^sub>s"
           "(x, y) \<in> [parents state]\<^sub>g \<Longrightarrow> y \<in> [BFS_state.visited state]\<^sub>s" for x y
       using assms(3)  by(auto elim!: invar_2_props)
     have unvis_neighb_in_front':
        "\<lbrakk>x \<in> [BFS_state.current state]\<^sub>s ; y \<in> neighbourhood [G]\<^sub>g x; y \<notin> [BFS_state.visited state]\<^sub>s\<rbrakk> 
        \<Longrightarrow> y \<in> [front']\<^sub>s" for x y
       using assms(2) graph_inv(1) invar_1_def next_frontier(2) by fastforce
     have neihgb_unvis_self_vis_without_front:
        "\<lbrakk>x \<in> [BFS_state.current state]\<^sub>s ; y \<in> neighbourhood [G]\<^sub>g x; y \<notin> [BFS_state.visited state]\<^sub>s\<rbrakk>
           \<Longrightarrow> x \<in> [BFS_state.visited state]\<^sub>s - [front']\<^sub>s"
        for x y
       using assms(3,2) graph_inv(1) by(auto elim!: invar_2_props invar_1_props)

     have "[expand_tree (parents state) (BFS_state.current state) (BFS_state.visited state)]\<^sub>g =
    {(x, y).
     x \<in> [vis']\<^sub>s \<and>
     y \<in> [vis']\<^sub>s \<and>
     Suc (dist_lookup (set_all_dists_in_set (dists dist_state) front' (Suc (current_dist dist_state))) x) =
     dist_lookup (set_all_dists_in_set (dists dist_state) front' (Suc (current_dist dist_state))) y \<and>
     (x, y) \<in> [G]\<^sub>g}"
     proof(subst expand_tree(2)[OF invar_1D(3,2,1) graph_inv(1) vis_in_G], rule, all \<open>rule\<close>, goal_cases)
       case (1 e)
       then show ?case 
       proof(cases e, goal_cases)
         case (1 x y)
         then show ?thesis 
           using  current_in_vis neihgb_unvis_self_vis_without_front unvis_neighb_in_front'[of x y]
           by (auto simp add: distances_invarD(2,3,6) new_dist_values_old new_dist_values_front'
                                distances_invarD(7) old_parent_not_in_new_front' parent_edge_visited
                                old_parent_not_in_new_front vis'_is)
         qed
       next
       case (2 e)
       then show ?case 
         unfolding vis'_is
         proof(cases e, goal_cases)
           case (1 x y)
           thus ?case
           proof(cases "x \<in> [BFS_state.visited state]\<^sub>s", all \<open>cases "y \<in> [BFS_state.visited state]\<^sub>s"\<close>, goal_cases)
             case 1
             then show ?case
               by (auto simp add: new_dist_values_old distances_invarD(2,7))
           next
             case 2
             then show ?case
               by (auto simp add: new_dist_values_old  new_dist_values_front' distances_invarD(2,3,5))
           next
             case 3
             then show ?case 
               using Suc_n_not_le_n[of "current_dist dist_state"] 
                 Suc_leD[of "Suc (current_dist dist_state)" "current_dist dist_state"]
               by(auto simp add: new_dist_values_old  new_dist_values_front' distances_invarD(2,3,4,5))
           next
             case 4
             then show ?case
               by(auto simp add: new_dist_values_old  new_dist_values_front' distances_invarD(2,3,5))
           qed
         qed
       qed

       hence claim4: 
       "[parents (BFS_upd1 state)]\<^sub>g =
      {(x, y) |x y.
     x \<in> [BFS_dist_state.visited (BFS_dist_upd dist_state)]\<^sub>s \<and>
     y \<in> [BFS_dist_state.visited (BFS_dist_upd dist_state)]\<^sub>s \<and>
     dist_lookup (dists (BFS_dist_upd dist_state)) x + 1 = dist_lookup (dists (BFS_dist_upd dist_state)) y
         \<and> (x, y) \<in> [G]\<^sub>g}"
         using distances_invarD(2,3) One
         by(simp add: BFS_upd1_def Let_def BFS_dist_upd_def)

     have "x \<in> [vis']\<^sub>s \<Longrightarrow>
    dist_lookup (set_all_dists_in_set (dists dist_state) front' (Suc (current_dist dist_state))) x
    \<le> Suc (current_dist dist_state)" for x
     proof(goal_cases)
       case 1
       then show ?case 
         using distances_invarD(4)[of x]
         by(auto simp add: vis'_is new_dist_values_old distances_invarD(2)  new_dist_values_front')
     qed

     hence claim5:
       "x \<in> [BFS_dist_state.visited (BFS_dist_upd dist_state)]\<^sub>s \<Longrightarrow>
         dist_lookup (dists (BFS_dist_upd dist_state)) x \<le> current_dist (BFS_dist_upd dist_state)" for x
         using distances_invarD(2,3) One
         by(simp add: BFS_upd1_def Let_def BFS_dist_upd_def)

     have "x \<in> [vis']\<^sub>s \<Longrightarrow>
    (dist_lookup (set_all_dists_in_set (dists dist_state) front' (Suc (current_dist dist_state))) x =
     Suc (current_dist dist_state)) =
    (x \<in> [front']\<^sub>s)" for x
     proof(goal_cases)
       case 1
       then show ?case 
         using next_frontier(2)[OF invar_1D(2,1) graph_inv(1)] distances_invarD(2,4) 
         by (fastforce simp add: vis'_is new_dist_values_old  new_dist_values_front')+
     qed

     hence claim6: "x \<in> [BFS_dist_state.visited (BFS_dist_upd dist_state)]\<^sub>s \<Longrightarrow>
         (dist_lookup (dists (BFS_dist_upd dist_state)) x = current_dist (BFS_dist_upd dist_state)) =
         (x \<in> [BFS_dist_state.current (BFS_dist_upd dist_state)]\<^sub>s)" for x
         using distances_invarD(2,3) One
         by(simp add: BFS_upd1_def Let_def BFS_dist_upd_def)

    show ?thesis
      by(intro distances_invarI claim1 claim2 claim3 claim4 claim5 claim6 | assumption)+
  qed

lemma dist_invar_stop:
  assumes "BFS_ret_1_conds state" "distances_invar state dist_state"
  shows "distances_invar (BFS_ret1 state) (BFS_dist_ret dist_state)"
  using assms
  by(auto intro!: distances_invarI simp add:  distances_invarD BFS_dist_ret_def)

lemma same_conds: 
  assumes "distances_invar state dist_state"
  shows  "BFS_dist_cond_ret dist_state = BFS_ret_1_conds state"
         "BFS_dist_cond_cont dist_state = BFS_call_1_conds state"
  using assms
  by(auto elim!: distances_invarE 
       simp add: BFS_dist_cond_ret_def BFS_ret_1_conds_def
                 BFS_call_1_conds_def BFS_dist_cond_cont_def)

lemma note_cont_is_ret_cond:
  "(\<not> BFS_dist_cond_cont BFS_state) = BFS_dist_cond_ret BFS_state"
  by(auto simp add: BFS_dist_cond_cont_def BFS_dist_cond_ret_def)

lemma dist_invar_pres:
  assumes "BFS_dom state" "invar_1 state" 
          "invar_2 state" "distances_invar state dist_state"
        shows "distances_invar (BFS state) (BFS_dist dist_state)"
proof-
  have dom:"BFS_dist_dom dist_state" 
    using assms(1,4)
    by(subst BFS_dist_same_dom)(auto elim!: distances_invarE)
  show ?thesis
  using assms(2-)
   proof(induction arbitrary: state rule: BFS_dist_induct[OF dom], goal_cases)
     case (1 BFS_state state)
    have dom:"BFS_dom state" 
     using 1(1,5)
      by(subst (asm)  BFS_dist_same_dom)(auto elim!: distances_invarE)
     show ?case 
     proof(cases "BFS_dist_cond_cont BFS_state")
       case True
       then show ?thesis 
         using 1(1,3,4,5) same_conds[OF 1(5)] dom
         by(auto intro!: 1(2) invar_1_holds_upd1 invar_2_holds_upd1 dist_invar_pres_one_step 
               simp add: BFS_simps BFS_dist_simps)
     next
       case False
       then show ?thesis 
         using same_conds[OF 1(5)] dom 1(1,5) 
         by(auto intro!: dist_invar_stop 
                  simp add: BFS_simps BFS_dist_simps(2) note_cont_is_ret_cond)
     qed
   qed
 qed

lemma distances_invar_intial:
  "distances_invar initial_state initial_dist_state"
  using  srcs_in_G set_all_dists_in_set[OF vset_inv2[OF srcs_invar(2)] _ some_dist]
  by(auto intro!: distances_invarI 
           simp add: initial_dist_state_def initial_state_def)

lemma distances_invar_final:
  "distances_invar (local.BFS initial_state) (BFS_dist initial_dist_state)"
  by (simp add: BFS_axiom dist_invar_pres distances_invar_intial)

lemma BFS_dist_level_graph:
  assumes final_state_def: "final_state = BFS_dist initial_dist_state"
  shows
  "{(x, y) | x y. x \<in> t_set (visited final_state) \<and> y \<in> t_set (visited final_state)
       \<and> dist_lookup (dists final_state) x + 1 = dist_lookup (dists final_state) y \<and>
      (x, y) \<in> Graph.digraph_abs G}
   = level_graph (Graph.digraph_abs G) (t_set srcs)
          - {(u, v) | u v. distance_set (Graph.digraph_abs G) (t_set srcs) u = \<infinity>}"
  unfolding final_state_def
  by(subst distances_invarD(7)[symmetric], rule distances_invar_final)
    (simp add: BFS_level_graph)

end

end text \<open>locale @{const BFS}\<close>

section \<open>BFS with Distances and Parents\<close>

text \<open>The parents are built while the next frontier is computed: every vertex that is newly
      discovered from a frontier vertex \<open>u\<close> gets \<open>u\<close> as its parent. On frontier and visited set,
      the combined function behaves like @{term next_frontier_and_current}, so all results on
      distances carry over. Parents of vertices outside the visited set, and of sources,
      are unspecified.\<close>

record ('dist, 'vset, 'par) BFS_par_state = "('dist, 'vset) BFS_dist_state" + parent :: "'par"

locale BFS_distance_parents =
  BFS_distance where lookup = lookup and set_all_dists_in_set = set_all_dists_in_set
  + Parent_Map_Spec_static where U = U and to_dir_graph = parent_abstract
        and get_path = get_path and roots = roots and invar = parent_invar
  + Parent_Map_Spec_init where U = U and to_dir_graph = parent_abstract
        and roots = roots and invar = parent_invar and vset_abstract = t_set
        and init = parent_init and vset_invar = vset_inv
for lookup :: "'adjmap \<Rightarrow> 'ver \<Rightarrow> 'vset option"
  and set_all_dists_in_set :: "'dist \<Rightarrow> 'vset \<Rightarrow> nat \<Rightarrow> 'dist"
  and parent_abstract::"'par \<Rightarrow> ('ver \<times> 'ver) set"
   and parent_invar :: "'par \<Rightarrow> bool"
   and U::"'ver set"
   and get_path::"'par \<Rightarrow> 'ver \<Rightarrow> 'ver list"
   and roots::"'par \<Rightarrow> 'ver set"
   and parent_init::"'vset \<Rightarrow> 'par" +
  fixes next_frontier_current_parents :: "'vset \<Rightarrow> 'vset \<Rightarrow> 'par \<Rightarrow> 'vset \<times> 'vset \<times> 'par"
  assumes next_frontier_current_parents:
    "\<And> frontier vis par front' vis' par'.
       \<lbrakk>vset_inv2 frontier; vset_inv vis; Graph.graph_inv G; t_set frontier \<subseteq> t_set vis;
        t_set vis \<subseteq> dVs (Graph.digraph_abs G); parent_invar par;
        dVs (parent_abstract par) \<union> roots par = t_set vis;
        next_frontier_current_parents frontier vis par = (front', vis', par')\<rbrakk>
       \<Longrightarrow> next_frontier_and_current frontier vis = (front', vis')"
    "\<And> frontier vis par front' vis' par'.
       \<lbrakk>vset_inv2 frontier; vset_inv vis; Graph.graph_inv G; t_set frontier \<subseteq> t_set vis;
        t_set vis \<subseteq> dVs (Graph.digraph_abs G); parent_invar par;
        dVs (parent_abstract par) \<union> roots par = t_set vis;
        next_frontier_current_parents frontier vis par = (front', vis', par')\<rbrakk>
       \<Longrightarrow> parent_invar par'"
    "\<And> frontier vis par front' vis' par' .
       \<lbrakk>vset_inv2 frontier; vset_inv vis; Graph.graph_inv G; t_set frontier \<subseteq> t_set vis;
        t_set vis \<subseteq> dVs (Graph.digraph_abs G); parent_invar par;
        dVs (parent_abstract par) \<union> roots par = t_set vis;
        next_frontier_current_parents frontier vis par = (front', vis', par')\<rbrakk>
       \<Longrightarrow> \<exists> Ex. parent_abstract par' = parent_abstract par \<union> Ex \<and>
                ( \<forall> x \<in> t_set front'. \<exists> x' \<in> t_set frontier.
                        (x', x) \<in> Graph.digraph_abs G \<and> (x, x') \<in> Ex) \<and>
                (\<forall> x x'. (x, x') \<in> Ex \<longrightarrow> x \<in> t_set front' \<and> x' \<in> t_set frontier 
                            \<and> (x', x) \<in> Graph.digraph_abs G)"
    "\<And> frontier vis par front' vis' par'.
       \<lbrakk>vset_inv2 frontier; vset_inv vis; Graph.graph_inv G; t_set frontier \<subseteq> t_set vis;
        t_set vis \<subseteq> dVs (Graph.digraph_abs G); parent_invar par;
        dVs (parent_abstract par) \<union> roots par = t_set vis;
        next_frontier_current_parents frontier vis par = (front', vis', par')\<rbrakk>
       \<Longrightarrow> roots par' = roots par"
   and G_in_U: "dVs (Graph.digraph_abs G) \<subseteq> U"
begin

partial_function (tailrec) BFS_par_impl ::
  "('dist, 'vset, 'par) BFS_par_state \<Rightarrow> ('dist, 'vset, 'par) BFS_par_state" where
  "BFS_par_impl s =
     (if current s \<noteq> \<emptyset>\<^sub>N then
        let (current', visited', parent') =
              next_frontier_current_parents (current s) (visited s) (parent s);
            d = current_dist s;
            dist' = set_all_dists_in_set (dists s) current' (Suc d)
        in BFS_par_impl (s\<lparr>dists := dist', visited := visited', current := current',
                           current_dist := Suc d, parent := parent'\<rparr>)
      else s)"

definition "initial_par_state =
  \<lparr>dists = set_all_dists_in_set some_dist srcs 0, current = srcs, visited = srcs,
   current_dist = 0, parent = parent_init srcs\<rparr>"

definition BFS_par_upd :: "('dist, 'vset, 'par) BFS_par_state \<Rightarrow> ('dist, 'vset, 'par) BFS_par_state" where
  "BFS_par_upd s = 
    (let 
       (current', visited', parent') =
          next_frontier_current_parents (current s) (visited s) (parent s);
       d = current_dist s;
       dist' = set_all_dists_in_set (dists s) current' (Suc d)
     in 
       s\<lparr>dists := dist', visited := visited', current := current', current_dist := Suc d,
         parent := parent'\<rparr>)"

lemma BFS_par_impl_simps:
  "current s \<noteq> \<emptyset>\<^sub>N \<Longrightarrow> BFS_par_impl s = BFS_par_impl (BFS_par_upd s)"
  "current s = \<emptyset>\<^sub>N \<Longrightarrow> BFS_par_impl s = s"
  by (subst BFS_par_impl.simps, simp add: BFS_par_upd_def Let_def split: prod.split)+

context 
  assumes BFS_axiom: BFS_axiom
begin

text \<open>Every parent edge goes from a visited vertex to a visited vertex whose distance is one
      smaller and reverses an edge of the graph. Every visited vertex that is not a source has a
      parent. The roots are the sources.\<close>

definition "parents_invar s =
   (parent_invar (parent s) \<and> roots (parent s) = t_set srcs \<and>
    (\<forall> x \<in> t_set srcs. dist_lookup (dists s) x = 0) \<and>
    (\<forall> v \<in> t_set (visited s) - t_set srcs. \<exists> u. (v, u) \<in> parent_abstract (parent s)) \<and>
    (\<forall> v u. (v, u) \<in> parent_abstract (parent s) \<longrightarrow>
        v \<in> t_set (visited s) \<and> u \<in> t_set (visited s) \<and>
        dist_lookup (dists s) u + 1 = dist_lookup (dists s) v \<and>
        (u, v) \<in> Graph.digraph_abs G))"

lemma parents_invar_pres_one_step:
  assumes "BFS_call_1_conds state" "invar_1 state" "invar_2 state" 
          "distances_invar state (BFS_dist_state.truncate s)" "parents_invar s"
  shows "BFS_dist_state.truncate (BFS_par_upd s) = BFS_dist_upd (BFS_dist_state.truncate s)"
        "parents_invar (BFS_par_upd s)"
proof-
  obtain front' vis' par' where nfcp:
    "next_frontier_current_parents (current s) (visited s) (parent s) = (front', vis', par')"
    by (cases "next_frontier_current_parents (current s) (visited s) (parent s)") auto
  have vis_cur: "BFS_state.visited state = visited s" "BFS_state.current state = current s"
    using distances_invarD(2,3)[OF BFS_axiom assms(4)]
    by (simp_all add: BFS_dist_state.truncate_def)
  have pre: "vset_inv2 (current s)" "vset_inv (visited s)" "t_set (current s) \<subseteq> t_set (visited s)"
            "t_set (visited s) \<subseteq> dVs (Graph.digraph_abs G)" "parent_invar (parent s)"
    using invar_1D(1,2)[OF assms(2)] assms(3,5) vis_cur by (auto simp: invar_2_def parents_invar_def)
  have tree: "dVs (parent_abstract (parent s)) \<union> roots (parent s) = t_set (visited s)"
  proof-
    have pinv: "roots (parent s) = t_set srcs"
      "\<forall> v \<in> t_set (visited s) - t_set srcs. \<exists> u. (v, u) \<in> parent_abstract (parent s)"
      "\<forall> v u. (v, u) \<in> parent_abstract (parent s) \<longrightarrow>
        v \<in> t_set (visited s) \<and> u \<in> t_set (visited s) \<and>
        dist_lookup (dists s) u + 1 = dist_lookup (dists s) v \<and>
        (u, v) \<in> Graph.digraph_abs G"
      using assms(5) by (simp_all add: parents_invar_def)
    have srcs: "t_set srcs \<subseteq> t_set (visited s)"
      using assms(3) vis_cur by (simp add: invar_2_def)
    have "x \<in> dVs (parent_abstract (parent s)) \<union> roots (parent s)" if "x \<in> t_set (visited s)" for x
    proof(cases "x \<in> t_set srcs")
      case True
      then show ?thesis
        using pinv(1) by simp
    next
      case False
      then have "x \<in> t_set (visited s) - t_set srcs"
        using that by simp
      then obtain u where "(x, u) \<in> parent_abstract (parent s)"
        using pinv(2) by blast
      then show ?thesis
        by (simp add: dVsI)
    qed
    moreover have "fst e \<in> t_set (visited s) \<and> snd e \<in> t_set (visited s)"
      if "e \<in> parent_abstract (parent s)" for e
      using pinv(3)[rule_format, of "fst e" "snd e"] that by simp
    ultimately show ?thesis
      using pinv(1) srcs unfolding dVs_eq by blast
  qed
  note nf = next_frontier_current_parents[OF pre(1,2) graph_inv(1)[OF BFS_axiom] pre(3,4,5) tree nfcp]
  note front' = next_frontier(1,2)[OF pre(1,2) graph_inv(1)[OF BFS_axiom] pre(3) nf(1) pre(4)]
  have vis': "t_set vis' = t_set (visited s) \<union> t_set front'"
    using next_vis(2)[OF pre(1,2) graph_inv(1)[OF BFS_axiom] pre(3) nf(1) pre(4)] .
  show "BFS_dist_state.truncate (BFS_par_upd s) = BFS_dist_upd (BFS_dist_state.truncate s)"
    using nf(1) nfcp by (simp add: BFS_par_upd_def BFS_dist_upd_def BFS_dist_state.truncate_def Let_def)
  have dist_inv: "dist_invar (dists s) (t_set (visited s))"
    using distances_invarD(1)[OF BFS_axiom assms(4)] by (simp add: BFS_dist_state.truncate_def)
  have front'_G: "t_set front' \<subseteq> dVs (Graph.digraph_abs G)"
    using front'(2) by (auto simp: Pair_Graph.neighbourhood_def dVs_def)
  let ?d = "set_all_dists_in_set (dists s) front' (Suc (current_dist s))"
  have d_front': "dist_lookup ?d x = Suc (current_dist s)" if "x \<in> t_set front'" for x
    using set_all_dists_in_set(2)[OF vset_inv2[OF front'(1)] front'_G dist_inv that] .
  have d_vis: "dist_lookup ?d x = dist_lookup (dists s) x" if "x \<in> t_set (visited s)" for x
    using set_all_dists_in_set(3)[OF vset_inv2[OF front'(1)] front'_G dist_inv] that front'(2) by blast
  have d_cur: "dist_lookup (dists s) x = current_dist s" if "x \<in> t_set (current s)" for x
    using distances_invarD(6)[OF BFS_axiom assms(4)] that pre(3)
    by (auto simp: BFS_dist_state.truncate_def)
  obtain Ex where Ex: "parent_abstract par' = parent_abstract (parent s) \<union> Ex"
    "\<forall> x \<in> t_set front'. \<exists> x' \<in> t_set (current s). (x', x) \<in> Graph.digraph_abs G \<and> (x, x') \<in> Ex"
    "\<forall> x x'. (x, x') \<in> Ex \<longrightarrow>
       x \<in> t_set front' \<and> x' \<in> t_set (current s) \<and> (x', x) \<in> Graph.digraph_abs G"
    using nf(3) by blast
  have "v \<in> t_set vis' \<and> u \<in> t_set vis' \<and> dist_lookup ?d u + 1 = dist_lookup ?d v \<and>
        (u, v) \<in> Graph.digraph_abs G" if "(v, u) \<in> parent_abstract par'" for v u
  proof(cases "(v, u) \<in> parent_abstract (parent s)")
    case True
    then show ?thesis
      using assms(5) d_vis vis' by (auto simp: parents_invar_def)
  next
    case False
    then have "(v, u) \<in> Ex"
      using that Ex(1) by auto
    then show ?thesis
      using Ex(3) pre(3) d_cur d_front' d_vis[of u] vis' by auto
  qed
  moreover have "\<exists> u. (v, u) \<in> parent_abstract par'" if "v \<in> t_set vis' - t_set srcs" for v
  proof(cases "v \<in> t_set (visited s)")
    case True
    have "\<forall> v \<in> t_set (visited s) - t_set srcs. \<exists> u. (v, u) \<in> parent_abstract (parent s)"
      using assms(5) unfolding parents_invar_def by blast
    moreover have "v \<in> t_set (visited s) - t_set srcs"
      using True that by simp
    ultimately have "\<exists> u. (v, u) \<in> parent_abstract (parent s)"
      by (rule bspec)
    then obtain u where "(v, u) \<in> parent_abstract (parent s)"
      by blast
    then show ?thesis
      using Ex(1) by blast
  next
    case False
    then have "v \<in> t_set front'"
      using that vis' by blast
    then obtain u where "(v, u) \<in> Ex"
      using Ex(2) by blast
    then show ?thesis
      using Ex(1) by blast
  qed
  moreover have "dist_lookup ?d x = 0" if "x \<in> t_set srcs" for x
    using assms(3,5) vis_cur d_vis that by (auto simp: invar_2_def parents_invar_def)
  moreover have "roots par' = t_set srcs"
    using nf(4) assms(5) by (simp add: parents_invar_def)
  ultimately show "parents_invar (BFS_par_upd s)"
    using nf(2) nfcp by (simp add: parents_invar_def BFS_par_upd_def Let_def)
qed

lemma BFS_par_impl_correct:
  assumes "BFS_dom state" "invar_1 state" "invar_2 state"
          "distances_invar state (BFS_dist_state.truncate s)" "parents_invar s"
  shows "BFS_dist_state.truncate (BFS_par_impl s) = BFS_dist (BFS_dist_state.truncate s) \<and>
         parents_invar (BFS_par_impl s)"
  using assms(2-)
proof(induction arbitrary: s rule: BFS_induct[OF BFS_axiom assms(1)])
  case (1 state s)
  have cur: "BFS_state.current state = current s"
    using distances_invarD(3)[OF BFS_axiom 1(5)] by (simp add: BFS_dist_state.truncate_def)
  have dom: "BFS_dist_dom (BFS_dist_state.truncate s)"
    using 1(1) BFS_dist_same_dom distances_invarD(2,3)[OF BFS_axiom 1(5)] by blast
  show ?case
  proof(cases "BFS_call_1_conds state")
    case True
    note step = parents_invar_pres_one_step[OF True 1(3-6)]
    have "distances_invar (BFS_upd1 state) (BFS_dist_state.truncate (BFS_par_upd s))"
      using dist_invar_pres_one_step[OF BFS_axiom True 1(3-5)] step(1) by simp
    note IH = 1(2)[OF True invar_1_holds_upd1[OF BFS_axiom True 1(3,4)]
                        invar_2_holds_upd1[OF BFS_axiom True 1(3,4)] this step(2)]
    show ?thesis
      using True cur IH step(1) BFS_dist_simps(1)[OF _ dom]
      by (auto simp: BFS_par_impl_simps(1) BFS_call_1_conds_def BFS_dist_cond_cont_def
                     BFS_dist_state.truncate_def)
  next
    case False
    then show ?thesis
      using cur 1(6) BFS_dist_simps(2)
      by (auto simp: BFS_par_impl_simps(2) BFS_call_1_conds_def BFS_dist_cond_ret_def
                     BFS_dist_ret_def BFS_dist_state.truncate_def)
  qed
qed

lemma BFS_par_final:
  "BFS_dist_state.truncate (BFS_par_impl initial_par_state) = BFS_dist initial_dist_state"
  "parents_invar (BFS_par_impl initial_par_state)"
proof-
  have "BFS_dist_state.truncate initial_par_state = initial_dist_state"
    by (simp add: initial_par_state_def initial_dist_state_def BFS_dist_state.truncate_def)
  moreover have "parents_invar initial_par_state"
    using init[OF vset_inv2[OF srcs_invar(2)] order.trans[OF srcs_in_G G_in_U]]
          BFS_axiom set_all_dists_in_set(2)[OF vset_inv2[OF srcs_invar(2)] srcs_in_G some_dist]
    by (simp add: parents_invar_def initial_par_state_def)
  ultimately show "BFS_dist_state.truncate (BFS_par_impl initial_par_state) = BFS_dist initial_dist_state"
                  "parents_invar (BFS_par_impl initial_par_state)"
    using BFS_par_impl_correct[OF initial_state_props(4,1,2)[OF BFS_axiom]]
          distances_invar_intial[OF BFS_axiom] by auto
qed

lemma BFS_par_final_fields:
  "visited (BFS_par_impl initial_par_state) = visited (BFS_dist initial_dist_state)"
  "dists (BFS_par_impl initial_par_state) = dists (BFS_dist initial_dist_state)"
  using arg_cong[OF BFS_par_final(1), of visited] arg_cong[OF BFS_par_final(1), of dists]
  by (simp_all add: BFS_dist_state.truncate_def)

text \<open>Every parent edge reverses an edge of the level graph, i.e.\ following the parents yields
      shortest paths from the sources.\<close>

theorem BFS_par_parent_in_level_graph:
  assumes "final_state = BFS_par_impl initial_par_state"
          "(v, u) \<in> parent_abstract (parent final_state)"
  shows "(u, v) \<in> level_graph (Graph.digraph_abs G) (t_set srcs)"
  using BFS_par_final(2) assms BFS_dist_level_graph[OF BFS_axiom refl] BFS_par_final_fields
  by (fastforce simp: parents_invar_def)

lemma BFS_par_unvisited_unreachable:
  assumes "final_state = BFS_par_impl initial_par_state"
          "u \<in> t_set srcs" "t \<notin> t_set (visited final_state)"
  shows "\<nexists>q. vwalk_bet (Graph.digraph_abs G) u q t"
  using BFS_correct_1[OF BFS_axiom] distances_invarD(2)[OF BFS_axiom distances_invar_final[OF BFS_axiom]]
        BFS_par_final_fields(1) assms
  by simp

lemma BFS_par_has_parent:
  assumes "final_state = BFS_par_impl initial_par_state"
          "x \<in> t_set (visited final_state) - t_set srcs"
  obtains u where "(x, u) \<in> parent_abstract (parent final_state)"
proof-
  have "\<forall> v \<in> t_set (visited final_state) - t_set srcs. \<exists> u. (v, u) \<in> parent_abstract (parent final_state)"
    using BFS_par_final(2) unfolding assms(1) parents_invar_def by blast
  then have "\<exists> u. (x, u) \<in> parent_abstract (parent final_state)"
    using assms(2) by (rule bspec)
  then show ?thesis
    using that by blast
qed
lemma BFS_par_dist:
  assumes "final_state = BFS_par_impl initial_par_state" "x \<in> t_set (visited final_state)"
  shows "dist_lookup (dists final_state) x = distance_set (Graph.digraph_abs G) (t_set srcs) x"
  using assms(2)
proof(induction "dist_lookup (dists final_state) x" arbitrary: x rule: less_induct)
  case less
  show ?case
  proof(cases "x \<in> t_set srcs")
    case True
    then have "distance_set (Graph.digraph_abs G) (t_set srcs) x = 0"
      using srcs_in_G[OF BFS_axiom] by auto
    then show ?thesis
      using True BFS_par_final(2) assms(1) by (simp add: parents_invar_def zero_enat_def)
  next 
    case False
    obtain p where xp: "(x, p) \<in> parent_abstract (parent final_state)"
      using BFS_par_has_parent[OF assms(1)] less.prems False by blast
    have p: "p \<in> t_set (visited final_state)"
            "dist_lookup (dists final_state) p + 1 = dist_lookup (dists final_state) x"
      using BFS_par_final(2) xp assms(1) by (auto simp: parents_invar_def)
    have "(p, x) \<in> level_graph (Graph.digraph_abs G) (t_set srcs)"
      by (rule BFS_par_parent_in_level_graph[OF assms(1) xp])
    then have lg: "distance_set (Graph.digraph_abs G) (t_set srcs) x =
                   distance_set (Graph.digraph_abs G) (t_set srcs) p + 1"
      by (rule in_level_graphE)
    have IH: "enat (dist_lookup (dists final_state) p) = distance_set (Graph.digraph_abs G) (t_set srcs) p"
      using less.hyps[OF _ p(1)] p(2) by simp
    show ?thesis
      by (simp add: lg IH[symmetric] p(2)[symmetric] eSuc_plus_1)
  qed
qed

text \<open>A walk along the parents, reversed, is a walk in the graph, and every step along the parents
      decreases the distance by one.\<close>

lemma parent_walk:
  assumes "final_state = BFS_par_impl initial_par_state"
          "vwalk_bet (parent_abstract (parent final_state)) x p t" "t \<in> dVs (Graph.digraph_abs G)"
  shows "vwalk_bet (Graph.digraph_abs G) t (rev p) x \<and>
         dist_lookup (dists final_state) x = dist_lookup (dists final_state) t + (length p - 1)"
  using assms(2)
proof(induction p arbitrary: x)
  case Nil
  then show ?case
    by (simp add: vwalk_bet_def)
next
  case (Cons y p)
  note IH = Cons.IH and prems = Cons.prems
  show ?case
  proof(cases p)
    case Nil
    then show ?thesis
      using prems assms(3) by (auto simp: vwalk_bet_def)
  next
    case (Cons z p')
    have xz: "(x, z) \<in> parent_abstract (parent final_state)"
             "vwalk_bet (parent_abstract (parent final_state)) z p t" "y = x"
      using prems Cons by (auto simp: vwalk_bet_def)
    have e: "dist_lookup (dists final_state) z + 1 = dist_lookup (dists final_state) x"
            "(z, x) \<in> Graph.digraph_abs G"
      using BFS_par_final(2) xz(1) assms(1) by (auto simp: parents_invar_def)
    note IH' = IH[OF xz(2)]
    show ?thesis
      using vwalk_bet_transitive[OF conjunct1[OF IH'] edges_are_vwalk_bet[OF e(2)]]
            conjunct2[OF IH'] e(1) xz(3) Cons
      by simp
  qed
qed

text \<open>Path reconstruction: @{term get_path} leads from a visited vertex along the parents to a
      root, i.e.\ a source. Reversed, this is a walk from that source whose number of edges is the
      distance of the vertex.\<close>

text \<open>The preconditions of @{term get_path} hold for every visited vertex.\<close>

lemma get_path_pre:
  assumes "final_state = BFS_par_impl initial_par_state" "x \<in> t_set (visited final_state)"
  shows "parent_invar (parent final_state)"
        "x \<in> dVs (parent_abstract (parent final_state)) \<union> roots (parent final_state)"
proof-
  have inv: "parent_invar (parent final_state)" "roots (parent final_state) = t_set srcs"
    using BFS_par_final(2) assms(1) by (auto simp: parents_invar_def)
  then show "parent_invar (parent final_state)"
    by simp
  show "x \<in> dVs (parent_abstract (parent final_state)) \<union> roots (parent final_state)"
  proof(cases "x \<in> t_set srcs")
    case True
    then show ?thesis
      using inv(2) by simp
  next
    case False
    then obtain u where "(x, u) \<in> parent_abstract (parent final_state)"
      using BFS_par_has_parent[OF assms(1)] assms(2) by blast
    then show ?thesis
      by auto
  qed
qed

lemma get_path_walk:
  assumes "final_state = BFS_par_impl initial_par_state" "x \<in> t_set (visited final_state)"
  shows "\<exists>u \<in> t_set srcs.
           vwalk_bet (Graph.digraph_abs G) u (rev (get_path (parent final_state) x)) x \<and>
           length (get_path (parent final_state) x) = Suc (dist_lookup (dists final_state) x) \<and>
           distinct (get_path (parent final_state) x)"
proof-
  have inv: "parent_invar (parent final_state)" "roots (parent final_state) = t_set srcs"
            "\<forall> x \<in> t_set srcs. dist_lookup (dists final_state) x = 0"
    using BFS_par_final(2) assms(1) by (auto simp: parents_invar_def)
  note x_in = get_path_pre(2)[OF assms]
  obtain t where t: "distinct_vwalk_bet (parent_abstract (parent final_state)) x
                       (get_path (parent final_state) x) t \<or>
                     (x = t \<and> get_path (parent final_state) x = [x])" "t \<in> t_set srcs"
    using get_path[OF inv(1) x_in] inv(2) by blast
  from t(1) show ?thesis
  proof
    assume "distinct_vwalk_bet (parent_abstract (parent final_state)) x
              (get_path (parent final_state) x) t"
    then have p: "vwalk_bet (parent_abstract (parent final_state)) x (get_path (parent final_state) x) t"
                 "distinct (get_path (parent final_state) x)"
      by (simp_all add: distinct_vwalk_bet_def)
    have "get_path (parent final_state) x \<noteq> []"
      using p(1) by (simp add: vwalk_bet_def)
    then show ?thesis
      using parent_walk[OF assms(1) p(1)] srcs_in_G[OF BFS_axiom] p(2) t(2) inv(3)
      by (intro bexI[OF _ t(2)]) auto
  next
    assume "x = t \<and> get_path (parent final_state) x = [x]"
    then show ?thesis
      using t(2) inv(3) srcs_in_G[OF BFS_axiom]
      by (intro bexI[of _ x]) (auto simp: vwalk_bet_def)
  qed
qed

text \<open>The main properties of the final state: a vertex is visited iff it is reachable from a
      source, the distance computed for a visited vertex is its distance from the sources, every
      visited vertex that is not a source has a parent, every parent is visited, reached by a graph
      edge and has a distance that is one smaller, and
      the path reconstructed by @{term get_path} is a shortest path from the sources.\<close>

theorem BFS_par_correct:
  assumes "final_state = BFS_par_impl initial_par_state"
  shows "x \<in> t_set (visited final_state) \<longleftrightarrow>
           (\<exists>u \<in> t_set srcs. \<exists>q. vwalk_bet (Graph.digraph_abs G) u q x)"
    and "x \<in> t_set (visited final_state) \<Longrightarrow>
           dist_lookup (dists final_state) x = distance_set (Graph.digraph_abs G) (t_set srcs) x"
    and "x \<in> t_set (visited final_state) - t_set srcs \<Longrightarrow>
           (\<exists> u. (x, u) \<in> parent_abstract (parent final_state)) \<and>
           (\<forall> u. (x, u) \<in> parent_abstract (parent final_state) \<longrightarrow>
                u \<in> t_set (visited final_state) \<and> (u, x) \<in> Graph.digraph_abs G \<and>
                distance_set (Graph.digraph_abs G) (t_set srcs) x =
                  distance_set (Graph.digraph_abs G) (t_set srcs) u + 1)"
    and "x \<in> t_set (visited final_state) \<Longrightarrow>
           \<exists>u \<in> t_set srcs.
             vwalk_bet (Graph.digraph_abs G) u (rev (get_path (parent final_state) x)) x \<and>
             length (get_path (parent final_state) x) - 1 =
               distance_set (Graph.digraph_abs G) (t_set srcs) x"
proof-
  show path: "x \<in> t_set (visited final_state) \<Longrightarrow>
           \<exists>u \<in> t_set srcs.
             vwalk_bet (Graph.digraph_abs G) u (rev (get_path (parent final_state) x)) x \<and>
             length (get_path (parent final_state) x) - 1 =
               distance_set (Graph.digraph_abs G) (t_set srcs) x"
    using get_path_walk[OF assms, of x] BFS_par_dist[OF assms, of x] by auto
  show "x \<in> t_set (visited final_state) \<longleftrightarrow>
           (\<exists>u \<in> t_set srcs. \<exists>q. vwalk_bet (Graph.digraph_abs G) u q x)"
    using path BFS_par_unvisited_unreachable[OF assms] by blast
  show "x \<in> t_set (visited final_state) - t_set srcs \<Longrightarrow>
           (\<exists> u. (x, u) \<in> parent_abstract (parent final_state)) \<and>
           (\<forall> u. (x, u) \<in> parent_abstract (parent final_state) \<longrightarrow>
                u \<in> t_set (visited final_state) \<and> (u, x) \<in> Graph.digraph_abs G \<and>
                distance_set (Graph.digraph_abs G) (t_set srcs) x =
                  distance_set (Graph.digraph_abs G) (t_set srcs) u + 1)"
  proof-
    assume x: "x \<in> t_set (visited final_state) - t_set srcs"
    have "u \<in> t_set (visited final_state) \<and> (u, x) \<in> Graph.digraph_abs G \<and>
          distance_set (Graph.digraph_abs G) (t_set srcs) x =
            distance_set (Graph.digraph_abs G) (t_set srcs) u + 1"
      if xu: "(x, u) \<in> parent_abstract (parent final_state)" for u
    proof-
      have "distance_set (Graph.digraph_abs G) (t_set srcs) x =
            distance_set (Graph.digraph_abs G) (t_set srcs) u + 1"
        using BFS_par_parent_in_level_graph[OF assms xu] by (rule in_level_graphE)
      then show ?thesis
        using BFS_par_final(2) assms xu by (auto simp: parents_invar_def)
    qed
    moreover obtain u where "(x, u) \<in> parent_abstract (parent final_state)"
      by (rule BFS_par_has_parent[OF assms x])
    ultimately show ?thesis
      by blast
  qed
qed (rule BFS_par_dist[OF assms])

text \<open>The reconstructed path has at most as many vertices as the graph.\<close>

lemma get_path_length:
  assumes "final_state = BFS_par_impl initial_par_state" "x \<in> t_set (visited final_state)"
  shows "length (get_path (parent final_state) x) \<le> card (dVs (Graph.digraph_abs G))"
proof-
  obtain u where u: "u \<in> t_set srcs"
    and w: "vwalk_bet (Graph.digraph_abs G) u (rev (get_path (parent final_state) x)) x"
    and l: "length (get_path (parent final_state) x) - 1 =
              distance_set (Graph.digraph_abs G) (t_set srcs) x"
    using BFS_par_correct(4)[OF assms] by blast
  have fin: "distance (Graph.digraph_abs G) u x < \<infinity>"
    by (rule le_less_trans[OF vwalk_bet_dist[OF w]]) simp
  have lt: "distance (Graph.digraph_abs G) u x < card (dVs (Graph.digraph_abs G))"
    by (rule distance_less_vert_card[OF fin Graph.finite_graph[OF graph_inv(1-3)[OF BFS_axiom]]])
  have "enat (length (get_path (parent final_state) x) - 1) \<le> distance (Graph.digraph_abs G) u x"
    unfolding l by (rule dist_set_mem[OF u])
  then have "enat (length (get_path (parent final_state) x) - 1) <
             enat (card (dVs (Graph.digraph_abs G)))"
    using lt by (rule le_less_trans)
  then show ?thesis
    using get_path_walk[OF assms] by auto
qed

text \<open>The final visited set satisfies the set invariant, so membership can be tested with
      @{term isin}.\<close>

lemma BFS_par_visited_inv:
  "vset_inv (BFS_dist_state.visited (BFS_par_impl initial_par_state))"
proof-
  have "vset_inv (BFS_state.visited (local.BFS initial_state))"
    using invar_1D(1)[OF invar_1_holds[OF BFS_axiom initial_state_props(4,1,2)[OF BFS_axiom]]] .
  moreover have "BFS_state.visited (local.BFS initial_state) = 
                 BFS_dist_state.visited (BFS_dist initial_dist_state)"
    using distances_invarD(2)[OF BFS_axiom distances_invar_final[OF BFS_axiom]] .
  ultimately show ?thesis
    using BFS_par_final_fields(1) by simp
qed

text \<open>The reconstructed path is no longer than any walk from a source to the same vertex.\<close>

lemma get_path_shortest:
  assumes "final_state = BFS_par_impl initial_par_state" 
          "x \<in> t_set (BFS_dist_state.visited final_state)"
  obtains u where "u \<in> t_set srcs"
    "vwalk_bet (Graph.digraph_abs G) u (rev (get_path (parent final_state) x)) x"
    "\<And> u' p'. \<lbrakk>u' \<in> t_set srcs; vwalk_bet (Graph.digraph_abs G) u' p' x\<rbrakk> \<Longrightarrow>
        length (get_path (parent final_state) x) \<le> length p'"
proof-
  define pp where "pp = rev (get_path (parent final_state) x)"
  obtain u where u: "u \<in> t_set srcs" "vwalk_bet (Graph.digraph_abs G) u pp x"
    "enat (length pp - 1) = distance_set (Graph.digraph_abs G) (t_set srcs) x"
    using BFS_par_correct(4)[OF assms] by (auto simp add: pp_def)
  have "length pp \<le> length p'"
    if "u' \<in> t_set srcs" "vwalk_bet (Graph.digraph_abs G) u' p' x" for u' p'
  proof-
    have "enat (length pp - 1) \<le> enat (length p' - 1)"
      using vwalk_bet_dist_set[OF that(2,1)] unfolding u(3)[symmetric] .
    hence "length pp - 1 \<le> length p' - 1" 
      by simp
    moreover have "0 < length pp" "0 < length p'"
      using that(2) u(2) by (auto simp add: vwalk_bet_def)
    ultimately show ?thesis by linarith
  qed
  thus ?thesis
    using that u(1,2) by (simp add: pp_def)
qed

end
end
end
