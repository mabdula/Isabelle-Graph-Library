theory BFS_2
  imports Directed_Set_Graphs.Pair_Graph_Specs "HOL-Eisbach.Eisbach_Tools" Directed_Set_Graphs.Dist
          Directed_Set_Graphs.Set2_Addons More_Lists
begin

record ('parents, 'vset) BFS_state = parents:: "'parents" current:: "'vset" visited:: "'vset"

locale BFS =
  Graph: Pair_Graph_Specs
    where lookup = lookup +
  set_ops: Set2 vset_empty vset_delete _ t_set vset_inv insert
  
for lookup :: "'adjmap \<Rightarrow> 'ver \<Rightarrow> 'vset option" +

fixes  
srcs::"'vset" and
G::"'adjmap" and expand_tree::"'adjmap \<Rightarrow> 'vset \<Rightarrow> 'vset \<Rightarrow> 'adjmap" and
next_frontier::"'vset \<Rightarrow> 'vset \<Rightarrow> 'vset" 


assumes
   expand_tree[simp]:
     "\<lbrakk>Graph.graph_inv BFS_tree; vset_inv frontier; vset_inv vis; Graph.graph_inv G\<rbrakk> \<Longrightarrow> 
       Graph.graph_inv (expand_tree BFS_tree frontier vis)"
     "\<lbrakk>Graph.graph_inv BFS_tree; vset_inv frontier; vset_inv vis; Graph.graph_inv G\<rbrakk> \<Longrightarrow>
        Graph.digraph_abs (expand_tree BFS_tree frontier vis) = 
         (Graph.digraph_abs BFS_tree) \<union> 
         {(u,v) | u v. u \<in> t_set (frontier) \<and> 
                       v \<in> (Pair_Graph.neighbourhood (Graph.digraph_abs G) u -
                       t_set vis)}" and
   next_frontier[simp]:
    "\<lbrakk>vset_inv frontier; vset_inv vis; Graph.graph_inv G\<rbrakk> \<Longrightarrow>  vset_inv (next_frontier frontier vis)"
    "\<lbrakk>vset_inv frontier; vset_inv vis; Graph.graph_inv G\<rbrakk> \<Longrightarrow>
       t_set (next_frontier frontier vis) =
         (\<Union> {Pair_Graph.neighbourhood (Graph.digraph_abs G) u | u . u \<in> t_set frontier}) - t_set vis"

begin

definition "BFS_axiom \<longleftrightarrow>
  Graph.graph_inv G \<and> Graph.finite_graph G \<and> Graph.finite_vsets \<and>
  t_set srcs \<subseteq> dVs (Graph.digraph_abs G) \<and>
  (\<forall>u. finite (Pair_Graph.neighbourhood (Graph.digraph_abs G) u)) \<and>
  t_set srcs \<noteq> {} \<and> vset_inv srcs"

abbreviation "neighbourhood' \<equiv> Graph.neighbourhood G" 
notation "neighbourhood'" ("\<N>\<^sub>G _" 100)


function (domintros) BFS::"('adjmap, 'vset) BFS_state \<Rightarrow> ('adjmap, 'vset) BFS_state" where
  "BFS BFS_state = 
     (
        if current BFS_state \<noteq> \<emptyset>\<^sub>N then
          let
            visited' = visited BFS_state \<union>\<^sub>G current BFS_state;
            parents' = expand_tree (parents BFS_state) (current BFS_state) visited';
            current' = next_frontier (current BFS_state) visited'
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
            visited' = visited BFS_state \<union>\<^sub>G current BFS_state;
            parents' = expand_tree (parents BFS_state) (current BFS_state) visited';
            current' = next_frontier (current BFS_state) visited'
          in 
            BFS_impl (BFS_state \<lparr>parents:= parents', visited := visited', current := current'\<rparr>)
         else
          BFS_state)"

lemma BFS_impl_same:
  assumes "BFS_dom state" 
  shows "BFS_impl state = BFS state"
  by(induction rule: BFS.pinduct[OF assms])(auto simp add: BFS_impl.simps BFS.psimps)

definition "BFS_call_1_conds bfs_state = ( (current bfs_state) \<noteq> \<emptyset>\<^sub>N)"


definition "BFS_upd1 BFS_state =
(        let
          visited' = visited BFS_state \<union>\<^sub>G current BFS_state;
          parents' = expand_tree (parents BFS_state) (current BFS_state) visited';
          current' =  next_frontier (current BFS_state) visited'
        in 
          BFS_state \<lparr>parents:= parents', visited := visited', current := current'\<rparr>

)" 


definition "BFS_ret_1_conds bfs_state = ((current bfs_state) = \<emptyset>\<^sub>N)"

abbreviation "BFS_ret1 bfs_state \<equiv> bfs_state"


definition "invar_1 bfs_state = (
              vset_inv (visited bfs_state) \<and> vset_inv (current bfs_state) \<and>
              Graph.graph_inv (parents bfs_state) \<and> 
              finite (t_set (current bfs_state)) \<and> finite (t_set (visited bfs_state)))"

definition "invar_2 bfs_state = ( 
  Graph.digraph_abs (parents bfs_state) \<subseteq> Graph.digraph_abs G \<and> 
  t_set (visited bfs_state) \<subseteq> dVs (Graph.digraph_abs G) \<and> 
  t_set (current bfs_state) \<subseteq> dVs (Graph.digraph_abs G) \<and> 
  dVs (Graph.digraph_abs (parents bfs_state)) \<subseteq> t_set (visited bfs_state) \<union> t_set (current bfs_state) \<and>
  t_set srcs \<subseteq> t_set (visited bfs_state) \<union> t_set (current bfs_state))"

definition "invar_3_1 bfs_state = 
  (\<forall>v\<in>t_set (current bfs_state). \<forall>u. u \<in> t_set (current bfs_state) \<longleftrightarrow> 
      distance_set (Graph.digraph_abs G) (t_set srcs) v =
                           distance_set (Graph.digraph_abs G) (t_set srcs) u)"

definition "invar_3_2 bfs_state = 
  (\<forall>v\<in>t_set (current bfs_state). \<forall>u \<in> t_set (visited bfs_state) \<union> t_set (current bfs_state).
     distance_set (Graph.digraph_abs G) (t_set srcs) u \<le>
       distance_set (Graph.digraph_abs G) (t_set srcs) v)"

definition "invar_3_3 bfs_state = 
  (\<forall>v\<in>t_set (visited bfs_state).
     neighbourhood (Graph.digraph_abs G) v \<subseteq> t_set (visited bfs_state) \<union> t_set (current bfs_state))"

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

definition "call_1_measure_1 BFS_state=
  card (dVs (Graph.digraph_abs G) - ((t_set (visited BFS_state)) \<union> t_set (current BFS_state)))"

definition "call_1_measure_2 BFS_state =
  card (t_set (current BFS_state))"

definition
  "BFS_term_rel' = call_1_measure_1 <*mlex*> call_1_measure_2 <*mlex*> {}"

definition "initial_state = \<lparr>parents =  empty, current = srcs, visited = \<emptyset>\<^sub>N\<rparr>"

lemmas[code] = BFS_impl.simps initial_state_def

context
  includes Graph.adjmap.automation  Graph.vset.set.automation set_ops.automation
  assumes BFS_axiom  
begin

lemma graph_inv[simp]:
     "Graph.graph_inv G" 
     "Graph.finite_graph G"
     "Graph.finite_vsets" and
   srcs_in_G[simp,intro]: 
     "t_set srcs \<subseteq> dVs (Graph.digraph_abs G)" and
   finite_vset:
     "finite (Pair_Graph.neighbourhood (Graph.digraph_abs G) u)" and
  srcs_invar[simp]:
     "t_set srcs \<noteq> {}" 
     "vset_inv srcs"
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


lemma DFS_call_1_conds[call_cond_elims]: 
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
            split: list.splits option.splits if_splits)

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
           split: list.splits option.splits if_splits)

lemma BFS_domintros: 
  assumes "BFS_call_1_conds BFS_state \<Longrightarrow> BFS_dom (BFS_upd1 BFS_state)"
  shows "BFS_dom BFS_state"
proof(rule BFS.domintros, goal_cases)
  case (1)
  then show ?case
    using assms(1)[simplified BFS_call_1_conds_def BFS_upd1_def]
    by (force simp: Let_def split: list.splits option.splits if_splits)
qed

lemma invar_1_props[invar_props_elims]: 
  "invar_1 bfs_state \<Longrightarrow> 
  (\<lbrakk>vset_inv (visited bfs_state) ; vset_inv (current bfs_state) ;
    Graph.graph_inv (parents bfs_state); 
    finite (t_set (current bfs_state)); finite (t_set (visited bfs_state))\<rbrakk> \<Longrightarrow> P)
     \<Longrightarrow> P"
  by (auto simp: invar_1_def)

lemma invar_1_intro[invar_props_intros]:
  "\<lbrakk>vset_inv (visited bfs_state); vset_inv (current bfs_state);
    Graph.graph_inv (parents bfs_state);
    finite (t_set (current bfs_state)); finite (t_set (visited bfs_state))\<rbrakk> 
    \<Longrightarrow> invar_1 bfs_state"
  by (auto simp: invar_1_def)

lemma finite_simp:
   "{(u,v). u \<in> front \<and> v \<in> (Pair_Graph.neighbourhood (Graph.digraph_abs G) u) \<and> v \<notin> vis} = 
       {(u,v). u \<in> front} \<inter> {(u,v). v \<in> (Pair_Graph.neighbourhood (Graph.digraph_abs G) u)} - {(u,v) . v \<in> vis}"
   "finite {(u, v)| v . v \<in> (s u)} = finite (s u)"
  using finite_image_iff[where f = snd and A = "{(u, v) |v. v \<in> s u}"]
  by (auto simp: inj_on_def image_def)
  
lemma invar_1_holds_upd1[invar_holds_intros]:
  "\<lbrakk>BFS_call_1_conds bfs_state; invar_1 bfs_state\<rbrakk> \<Longrightarrow> invar_1 (BFS_upd1 bfs_state)"
  using finite_vset
  by(auto elim!: invar_1_props call_cond_elims simp: Let_def BFS_upd1_def BFS_call_1_conds_def intro!: invar_props_intros)+

lemma invar_1_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_1 bfs_state\<rbrakk> \<Longrightarrow> invar_1 (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_1_holds[invar_holds_intros]:
   assumes "BFS_dom bfs_state" "invar_1 bfs_state"
   shows "invar_1 (BFS bfs_state)"
  using assms(2-)
proof(induction rule: BFS_induct[OF assms(1)])
  case IH: (1 bfs_state)
  show ?case
    apply(rule BFS_cases[where bfs_state = bfs_state])
    by (auto intro!: IH(2-) intro: invar_holds_intros  simp: BFS_simps[OF IH(1)])
qed

lemma invar_2_props[invar_props_elims]: 
  "invar_2 bfs_state \<Longrightarrow> 
  (\<lbrakk>Graph.digraph_abs (parents bfs_state) \<subseteq> Graph.digraph_abs G;
    t_set (visited bfs_state) \<subseteq> dVs (Graph.digraph_abs G);
    t_set (current bfs_state) \<subseteq> dVs (Graph.digraph_abs G);
    dVs (Graph.digraph_abs (parents bfs_state)) \<subseteq> t_set (visited bfs_state) \<union> t_set (current bfs_state);
    t_set srcs \<subseteq> t_set (visited bfs_state) \<union> t_set (current bfs_state)\<rbrakk> \<Longrightarrow> P)
     \<Longrightarrow> P"
  by (auto simp: invar_2_def)

lemma invar_2_intro[invar_props_intros]:
   "\<lbrakk>Graph.digraph_abs (parents bfs_state) \<subseteq> Graph.digraph_abs G;
     t_set (visited bfs_state) \<subseteq> dVs (Graph.digraph_abs G);
     t_set (current bfs_state) \<subseteq> dVs (Graph.digraph_abs G);
     dVs (Graph.digraph_abs (parents bfs_state)) \<subseteq> t_set (visited bfs_state) \<union> t_set (current bfs_state);
     t_set srcs \<subseteq> t_set (visited bfs_state) \<union> t_set (current bfs_state)\<rbrakk>
     \<Longrightarrow> invar_2 bfs_state"
  by (auto simp: invar_2_def)

lemma invar_2_holds_upd1[invar_holds_intros]: 
  "\<lbrakk>BFS_call_1_conds bfs_state; invar_1 bfs_state; invar_2 bfs_state\<rbrakk> \<Longrightarrow> invar_2 (BFS_upd1 bfs_state)"
  apply(auto elim!: call_cond_elims invar_1_props invar_2_props intro!: invar_props_intros simp: BFS_upd1_def Let_def)
  apply(auto simp: dVs_def)
  apply (metis Un_iff dVsI(1) dVs_def in_mono)
  by (metis Un_iff dVsI(2) dVs_def in_mono)

lemma invar_2_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_2 bfs_state\<rbrakk> \<Longrightarrow> invar_2 (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

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
  (\<lbrakk>\<And>v u. \<lbrakk>v\<in>t_set (current bfs_state); u \<in> t_set (visited bfs_state) \<union> t_set (current bfs_state)\<rbrakk> \<Longrightarrow>
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
  (\<lbrakk>\<And>v. \<lbrakk>v \<in> t_set (visited bfs_state)\<rbrakk> \<Longrightarrow>
          neighbourhood (Graph.digraph_abs G) v \<subseteq> t_set (visited bfs_state) \<union> t_set (current bfs_state)\<rbrakk> \<Longrightarrow> P)
     \<Longrightarrow> P"
  unfolding invar_3_3_def
  by blast

lemma invar_3_3_intro[invar_props_intros]:
   "\<lbrakk>\<And>v. \<lbrakk>v \<in> t_set (visited bfs_state)\<rbrakk> \<Longrightarrow>
          neighbourhood (Graph.digraph_abs G) v \<subseteq> t_set (visited bfs_state) \<union> t_set (current bfs_state)\<rbrakk>
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

lemma invar_current_reachable_holds_upd1[invar_holds_intros]: 
  "\<lbrakk>BFS_call_1_conds bfs_state; invar_1 bfs_state; invar_2 bfs_state; invar_current_reachable bfs_state\<rbrakk>
     \<Longrightarrow> invar_current_reachable (BFS_upd1 bfs_state)"
proof(rule invar_props_intros, goal_cases)
  case assms: (1 v)
  have ?case (is "?dist v < \<infinity>") if "v \<notin> t_set (visited bfs_state) \<union> t_set (current bfs_state)"
  proof-
    have "v \<in> t_set (current (BFS_upd1 bfs_state))"
      using that assms
      by (auto simp: BFS_upd1_def Let_def elim: invar_props_elims)
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

lemma dist_current_plus_1_new:                                               
  assumes
    "invar_1 bfs_state" "invar_2 bfs_state" "invar_3_4 bfs_state" 
    "v \<in> neighbourhood (Graph.digraph_abs G) v'" 
    "v' \<in> t_set (current bfs_state)"
    "v \<in> t_set (current (BFS_upd1 bfs_state))"
  shows  "distance_set (Graph.digraph_abs G) (t_set srcs) v = 
            distance_set (Graph.digraph_abs G) (t_set srcs) v' + 1" (is "?dv = ?dv' + 1")
  proof-
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
        by (auto simp: BFS_upd1_def Let_def elim!: invar_1_props invar_2_props)
        
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
proof(intro invar_props_intros, goal_cases)
  case assms: (1 u v)
  obtain u' v' where
    uv'[intro]: "u \<in> neighbourhood (Graph.digraph_abs G) u'" "u' \<in> t_set (current bfs_state)" 
                "v \<in> neighbourhood (Graph.digraph_abs G) v'" "v' \<in> t_set (current bfs_state)"
    using assms(1,2,8,9)    
    by (auto simp: BFS_upd1_def Let_def elim!: invar_1_props)
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
  case (2 u v)
  then obtain v' where uv'[intro]:
    "v \<in> neighbourhood (Graph.digraph_abs G) v'" "v' \<in> t_set (current bfs_state)"    
    by (auto simp: BFS_upd1_def Let_def elim!: invar_1_props invar_2_props)
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
    hence "u \<notin> t_set (visited bfs_state) \<union> t_set (current bfs_state)"
      using \<open>invar_3_2 bfs_state\<close> \<open>u' \<in> t_set (current bfs_state)\<close> 
      by (auto elim!: invar_3_2_props dest: leD)
    ultimately show ?thesis
      using \<open>invar_1 bfs_state\<close> \<open>invar_2 bfs_state\<close> \<open>u \<in> neighbourhood (Graph.digraph_abs G) u'\<close>
      apply(auto simp: BFS_upd1_def Let_def elim!: invar_1_props invar_2_props)
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
    hence "v \<in> t_set (visited bfs_state) \<union> t_set (current bfs_state)"
      using assms(1,2,9)
      by (fastforce simp: BFS_upd1_def Let_def elim!: invar_1_props)
    moreover obtain u' where uv'[intro]: "u \<in> neighbourhood (Graph.digraph_abs G) u'" "u' \<in> t_set (current bfs_state)" 
      using assms(1,2,8,9)    
      by (auto simp: BFS_upd1_def Let_def elim!: invar_1_props)
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

lemma invar_3_2_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_3_3 bfs_state\<rbrakk> \<Longrightarrow> invar_3_3 (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_3_3_holds_upd1[invar_holds_intros]: 
  "\<lbrakk>BFS_call_1_conds bfs_state; invar_1 bfs_state; invar_2 bfs_state; invar_3_3 bfs_state\<rbrakk> \<Longrightarrow> invar_3_3 (BFS_upd1 bfs_state)"
  by(fastforce elim!: call_cond_elims invar_1_props invar_2_props invar_3_3_props intro!: invar_props_intros simp: BFS_upd1_def Let_def)

lemma invar_3_3_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_3_3 bfs_state\<rbrakk> \<Longrightarrow> invar_3_3 (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_3_4_holds_upd1[invar_holds_intros]: 
  "\<lbrakk>BFS_call_1_conds bfs_state; invar_1 bfs_state; invar_2 bfs_state;
    invar_3_1 bfs_state; invar_3_2 bfs_state; invar_3_3 bfs_state; invar_3_4 bfs_state;
    invar_current_reachable bfs_state\<rbrakk> \<Longrightarrow> 
    invar_3_4 (BFS_upd1 bfs_state)"
proof(intro invar_props_intros, goal_cases)                                                                                                    
  case assms: (1 u v)
  show ?case
  proof(cases \<open>v \<in> t_set (visited bfs_state) \<union> t_set (current bfs_state)\<close>)
    case v_visited: True
    hence "u \<in> t_set (visited bfs_state) \<union> t_set (current bfs_state)"
      using \<open>invar_3_4 bfs_state\<close> assms
      by (auto elim!: invar_3_4_props)
    then show ?thesis 
      using \<open>invar_1 bfs_state\<close> \<open>v \<in> t_set (visited (BFS_upd1 bfs_state)) \<union> t_set (current (BFS_upd1 bfs_state))\<close>
      by (auto simp: BFS_upd1_def Let_def elim: invar_props_elims)
  next
    case v_not_visited: False
    hence "v \<in> t_set (current (BFS_upd1 bfs_state))"
      using \<open>invar_1 bfs_state\<close> \<open>v \<in> t_set (visited (BFS_upd1 bfs_state)) \<union> t_set (current (BFS_upd1 bfs_state))\<close>
      by (auto simp: BFS_upd1_def Let_def elim: invar_props_elims)
    then obtain v' where v'[intro]:
      "v \<in> neighbourhood (Graph.digraph_abs G) v'" "v' \<in> t_set (current bfs_state)"
      using \<open>invar_1 bfs_state\<close>
      by (auto simp: BFS_upd1_def Let_def elim!: invar_1_props)
    have "distance_set (Graph.digraph_abs G) (t_set srcs) v = 
            distance_set (Graph.digraph_abs G) (t_set srcs) v' + 1" (is "?dv = ?dv' + 1")
      using assms \<open>v \<in> t_set (current (BFS_upd1 bfs_state))\<close>
      by (auto intro!: dist_current_plus_1_new)
    moreover have "u \<in> t_set (visited (BFS_upd1 bfs_state)) \<union> t_set (current (BFS_upd1 bfs_state))"
      if "distance_set (Graph.digraph_abs G) (t_set srcs) u \<le> ?dv'" (is "?du \<le> ?dv'")
      using that \<open>invar_1 bfs_state\<close> \<open>invar_2 bfs_state\<close> \<open>invar_3_4 bfs_state\<close> 
      by (fastforce simp: BFS_upd1_def Let_def elim!: invar_1_props invar_2_props invar_3_4_props)
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
      using \<open>invar_1 bfs_state\<close> \<open>invar_2 bfs_state\<close> \<open>x \<in> t_set (current bfs_state)\<close> 
      by(fastforce simp: BFS_upd1_def Let_def elim!: invar_1_props invar_2_props dest!: unvisited)
    then show ?thesis
      by(auto intro!: invar_goes_through_current_intro simp: \<open>p = p1 @ x # p2\<close> \<open>p2 = v' # p2'\<close>) 
next
  case u_not_in_visited: False
  hence "u \<in> t_set (current (BFS_upd1 bfs_state))"
    using \<open>invar_1 bfs_state\<close>
      \<open>u \<in> t_set (visited (BFS_upd1 bfs_state)) \<union> t_set (current (BFS_upd1 bfs_state))\<close>
    by (auto simp: BFS_upd1_def Let_def elim: invar_props_elims)
  moreover have "u \<in> set p"
    using \<open>Vwalk.vwalk_bet (Graph.digraph_abs G) u p v\<close>
    by (auto intro: hd_of_vwalk_bet'')
  ultimately show ?thesis
    by(auto intro!: invar_goes_through_current_intro)
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
proof(intro invar_props_intros, goal_cases)
  define bfs_state' where "bfs_state' = BFS_upd1 bfs_state"
  let ?dSrcsG = "distance_set (Graph.digraph_abs G) (t_set srcs)"
  let ?dSrcsT = "distance_set (Graph.digraph_abs (parents bfs_state)) (t_set srcs)"
  let ?dSrcsT' = "distance_set (Graph.digraph_abs (parents bfs_state')) (t_set srcs)"
  let ?dCurrG = "distance_set (Graph.digraph_abs G)  (t_set (current bfs_state))"
  case (1 v)
  then show ?case
  proof(cases "distance_set (Graph.digraph_abs G) (t_set srcs) v = \<infinity>")
    case infinite: True
    moreover have "?dSrcsG v \<le> ?dSrcsT' v"
      using \<open>invar_1 bfs_state\<close> \<open>invar_2 bfs_state\<close>
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
          using \<open>invar_1 bfs_state\<close>
          by(fastforce simp: bfs_state'_def BFS_upd1_def Let_def
                       intro: distance_set_subset elim: invar_props_elims)

        moreover have "?dSrcsG v \<le> ?dSrcsT' v"
          using \<open>invar_1 bfs_state\<close> \<open>invar_2 bfs_state\<close>
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
                v_not_in_tree \<open>invar_1 bfs_state\<close>
          by (auto simp: BFS_upd1_def Let_def elim: invar_props_elims)
        moreover then  obtain v' where v'[intro]: 
          "v \<in> neighbourhood (Graph.digraph_abs G) v'"
          "v' \<in> t_set (current bfs_state)"
          "v \<in> neighbourhood (Graph.digraph_abs (parents bfs_state')) v'"
          using v_not_in_tree \<open>invar_1 bfs_state\<close>
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
                using \<open>invar_1 bfs_state\<close>
                by(fastforce simp: bfs_state'_def BFS_upd1_def Let_def 
                    intro: distance_set_subset elim: invar_props_elims)

              moreover have "?dSrcsG v' \<le> ?dSrcsT' v'"
                using \<open>invar_1 bfs_state\<close> \<open>invar_2 bfs_state\<close>
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
  apply(auto elim!: call_cond_elims invar_1_props invar_2_props intro!: invar_props_intros simp: BFS_upd1_def Let_def)
  apply blast+
  done

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
proof(intro invar_props_intros, goal_cases)
  case assms: (1 u p v)

  define bfs_state' where "bfs_state' = BFS_upd1 bfs_state"

  have "invar_2 bfs_state'"
    using assms
    by (auto intro: invar_holds_intros simp: bfs_state'_def)

  hence ?case if "length p \<le> 1"
    using \<open>length p \<le> 1\<close> assms(7,8) \<open>invar_2 bfs_state\<close>
    by(cases p) (auto elim!: Vwalk.vwalk_bet_props invar_props_elims dest!: dVs_subset
                      simp: bfs_state'_def[symmetric] zero_enat_def[symmetric])

  have "invar_current_no_out bfs_state'"
    using assms 
    by(auto intro: invar_holds_intros simp: bfs_state'_def)

  have **: "u \<in> t_set (current bfs_state') \<or> v \<in> t_set (current bfs_state')"
    if "(u,v) \<in> (Graph.digraph_abs (parents bfs_state')) -
              (Graph.digraph_abs (parents bfs_state))" for u v
    using \<open>invar_1 bfs_state\<close> \<open>invar_2 bfs_state\<close> dVsI that
    by(fastforce dest: dVsI simp: bfs_state'_def dVs_def BFS_upd1_def Let_def
               elim!: invar_1_props invar_2_props)

  have ?case if "length p > 1" 
  proof-
    have "u \<in> t_set (visited bfs_state) \<union> t_set (current bfs_state)"
    proof(rule ccontr, goal_cases)
      have "u \<in> dVs (Graph.digraph_abs (parents bfs_state'))"
        using assms(8)
        by (auto simp: bfs_state'_def)
      hence "u \<in> t_set (visited bfs_state') \<union> t_set (current bfs_state')"
        using \<open>invar_2 bfs_state'\<close>
        by (auto elim: invar_props_elims)
      moreover case 1
      ultimately have "u \<in> t_set (current bfs_state')"
        using assms
        by(auto simp: Let_def bfs_state'_def BFS_upd1_def elim!: invar_1_props invar_2_props)
      moreover obtain u' where "(u,u') \<in> Graph.digraph_abs (parents bfs_state')"
        using \<open>length p > 1\<close> assms(8) \<open>invar_2 bfs_state\<close>
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
          by (metis \<open>invar_2 bfs_state'\<close> assms(8) bfs_state'_def invar_2_props vwalk_bet_subset)

        ultimately have "length p - 1 > distance_set (Graph.digraph_abs G) (t_set srcs) v"
          using \<open>u \<in> t_set srcs\<close> 1
          apply auto
          by (metis One_nat_def order_neq_le_trans vwalk_bet_dist_set)

        hence "length p - 2 \<ge>  distance_set (Graph.digraph_abs G) (t_set srcs) v"
          using \<open>length p > 1\<close>  
          apply (auto simp: eval_nat_numeral)
          by (metis leD leI Suc_diff_Suc Suc_ile_eq)
        moreover obtain p' v' where "p = p' @ [v', v]"
          using \<open>length p > 1\<close>
          apply (auto
              simp: eval_nat_numeral Suc_le_length_iff Suc_le_eq[symmetric]
              split: if_splits)
          by (metis append.right_neutral append_butlast_last_cancel assms(8) length_Cons
              length_butlast length_tl list.sel(3) list.size(3) nat.simps(3) vwalk_bet_def)
        have "vwalk_bet (Graph.digraph_abs (parents bfs_state)) u (p' @ [v']) v'"
        proof(rule ccontr, goal_cases)
          case 1
          moreover have "vwalk_bet (Graph.digraph_abs (parents (BFS_upd1 bfs_state))) u (p' @ [v']) v'"
            using assms(8) \<open>p = p' @ [v', v]\<close>
            by (simp add: vwalk_bet_pref)
          ultimately show ?case
          proof(elim vwalk_bet_not_vwalk_bet_elim_2[OF _ "1"], goal_cases)
            case 1
            then show ?case
              by (metis \<open>distance_set (Graph.digraph_abs G) (t_set srcs) v \<le> enat (length p - 2)\<close> 
                        \<open>p = p' @ [v', v]\<close> \<open>vwalk_bet (Graph.digraph_abs G) u p v\<close> assms(3)
                        diff_is_0_eq distance_set_0 invar_2_def le_zero_eq length_append_singleton
                        list.sel(3) not_less_eq_eq subset_eq v_not_visited vwalk_bet_endpoints(2) 
                        vwalk_bet_vertex_decompE zero_enat_def)
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
              apply (auto dest: v_in_edge_in_vwalk elim!: vwalk_bet_props intro!: no_outgoing_last)
               apply (metis "2"(2) last_snoc no_outgoing_last v_in_edge_in_vwalk(2))
              by (metis "2"(2) last_snoc no_outgoing_last v_in_edge_in_vwalk(2))
            hence "v' = v''"
              using that
              by auto
            moreover have "(v',v) \<in> Graph.digraph_abs (parents bfs_state')"
              using \<open>p = p' @ [v', v]\<close> assms(8)
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
        proof(elim vwalk_bet_not_vwalk_bet_elim_2[OF assms(8)], goal_cases)
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
            using v_visited \<open>invar_1 bfs_state\<close>
            by (auto simp: bfs_state'_def BFS_upd1_def Let_def elim: invar_props_elims)
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
proof(cases "t_set (next_frontier (current BFS_state) (visited BFS_state \<union>\<^sub>G current BFS_state)) = {}")
  case True
  hence "t_set (visited (BFS_upd1 BFS_state)) \<union> t_set (current (BFS_upd1 BFS_state)) =
           t_set (visited BFS_state) \<union> t_set (current BFS_state)"
    using \<open>invar_1 BFS_state\<close>
    by (fastforce simp: BFS_upd1_def Let_def elim!: invar_props_elims)
  hence "call_1_measure_1 (BFS_upd1 BFS_state) = call_1_measure_1 BFS_state"
    by (auto simp: call_1_measure_1_def)
  moreover have "t_set (current (BFS_upd1 BFS_state)) = {}"
    using True
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
    including Graph.adjmap.automation Graph.vset.set.automation
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
    using Graph.finite_vsets_def
    by (fastforce simp: ) 
  moreover have "t_set (visited (BFS_upd1 BFS_state)) \<union> t_set (current (BFS_upd1 BFS_state)) \<subseteq> dVs (Graph.digraph_abs G)"
    using \<open>invar_1 BFS_state\<close> \<open>invar_2 BFS_state\<close> 
    by(auto elim!: invar_props_elims call_cond_elims
          simp add: BFS_upd1_def Let_def dVs_def 
          intro!: mlex_less psubset_card_mono)+
  moreover have "t_set (visited (BFS_upd1 BFS_state)) \<union> t_set (current (BFS_upd1 BFS_state)) \<noteq> 
                   t_set (visited BFS_state) \<union> t_set (current BFS_state)"
    using \<open>BFS_call_1_conds BFS_state\<close> \<open>invar_1 BFS_state\<close> \<open>invar_2 BFS_state\<close> 
          \<open>invar_current_no_out BFS_state\<close> False
    by(fastforce elim!: invar_props_elims call_cond_elims
                 simp add: BFS_upd1_def Let_def dVs_def 
                 intro!: mlex_less psubset_card_mono)

  ultimately have **: "dVs (Graph.digraph_abs G) - (t_set (visited (BFS_upd1 BFS_state)) \<union>
                                                      t_set (current (BFS_upd1 BFS_state)))\<noteq>
                          dVs (Graph.digraph_abs G) - (t_set (visited BFS_state) \<union> t_set (current BFS_state))"
    using \<open>BFS_call_1_conds BFS_state\<close> \<open>invar_1 BFS_state\<close> \<open>invar_2 BFS_state\<close> 
    by(auto elim!: invar_props_elims call_cond_elims
          simp add: BFS_upd1_def Let_def dVs_def
          intro!: mlex_less psubset_card_mono)

  hence "call_1_measure_1 (BFS_upd1 BFS_state) < call_1_measure_1 BFS_state"
    using assms 
  by(auto elim!: invar_props_elims call_cond_elims
          simp add: call_1_measure_1_def BFS_upd1_def Let_def 
          intro!: psubset_card_mono)
  thus ?thesis
    by(auto intro!: mlex_less psubset_card_mono)
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
    by (fastforce simp: initial_state_def dVs_def Graph.finite_vsets_def
        intro!: invar_props_intros)

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
    by (auto simp add: initial_state_def  intro!: invar_props_intros)

  have *: "distance_set (Graph.digraph_abs G) (t_set srcs) v = 0" if "v \<in> t_set srcs" for v
    using that srcs_in_G
    by (fastforce intro: iffD2[OF distance_set_0[ where G = "(Graph.digraph_abs G)"]])
  moreover have **: "v \<in> t_set srcs" if "distance_set (Graph.digraph_abs G) (t_set srcs) v = 0" for v
    using dist_set_inf i0_ne_infinity that
    by (force intro: iffD1[OF distance_set_0[ where G = "(Graph.digraph_abs G)"]])
  ultimately show "invar_3_1 initial_state" "invar_3_2 initial_state" "invar_3_4 initial_state"
                  "invar_current_reachable initial_state"
    using dist_set_inf
    by(auto dest:  dest: simp add: initial_state_def  intro!: invar_props_intros dest!:)

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

end text \<open>context\<close>

end text \<open>locale @{const BFS}\<close>
end