theory BFS_2
  imports Directed_Set_Graphs.Pair_Graph_Specs "HOL-Eisbach.Eisbach_Tools" Directed_Set_Graphs.Dist
          Directed_Set_Graphs.Set2_Addons
begin

lemma list_2_preds_aux:
  "\<lbrakk>x' \<in> set xs; P1 x'; \<And>xs1 x xs2. \<lbrakk>xs = xs1 @ [x] @ xs2; P1 x\<rbrakk> \<Longrightarrow>
      \<exists>ys1 y ys2. x # xs2 = ys1 @ [y] @ ys2 \<and> P2 y\<rbrakk> \<Longrightarrow> 
     \<exists> xs1 x xs2. xs = xs1 @ [x] @ xs2 \<and> P2 x \<and> (\<forall>y\<in>set xs2. \<not> P1 y)"
proof(goal_cases)
  case assms: 1


  define property 
       where "property xs \<equiv>
                (\<forall>xs2 xs1 x. (xs = xs1 @ [x] @ xs2 \<and> P1 x) \<longrightarrow>
                   (\<exists>ys1 y ys2. x#xs2 = ys1 @ [y] @ ys2 \<and> P2 y))"
       for xs

  have propE: "\<lbrakk>property xs;
               (\<And>xs1 x xs2. \<lbrakk>xs = xs1 @ [x] @ xs2; P1 x\<rbrakk> \<Longrightarrow>
                  \<exists>ys1 y ys2. x#xs2 = ys1 @ [y] @ ys2 \<and> P2 y) \<Longrightarrow> P\<rbrakk>
              \<Longrightarrow> P" for xs P
    by(auto simp add: property_def)

  have property_append: "property (xs @ ys) \<Longrightarrow> property ys" for xs ys
    by(auto simp: property_def)

  have "property xs"
    using assms(3)
    by (force simp: property_def)



  thus  ?thesis
    using assms(1,2)
  proof(induction xs arbitrary: x')
    case Nil
    then show ?case 
      by auto
  next
    case (Cons a xs)
    hence "property xs" 
      by(auto intro: property_append[where xs = "[a]"])

    show ?case
    proof(cases "x' = a")
      case x_eq_a: True

      then obtain ys1 y ys2 where "x'#xs = ys1 @ [y] @ ys2" "P2 y"
        using \<open>property (a # xs)\<close> \<open>P1 x'\<close>
        by (auto 10 10 elim!: propE)

      show ?thesis
      proof(cases "ys1 = []")
        case ys1_empty: True
        hence "xs = ys2"
          using \<open>x'#xs = ys1 @ [y] @ ys2\<close>
          by auto
        then show ?thesis
        proof(cases "\<exists>x\<in>set ys2. P1 x")
          case x_in_ys2: True
          then obtain x where "x \<in> set ys2" "P1 x"
            by auto
          hence "\<exists>xs1 x xs2. xs = xs1 @ [x] @ xs2 \<and> P2 x \<and> (\<forall>y\<in>set xs2. \<not> P1 y)"
            using \<open>property xs\<close> \<open>xs = ys2\<close> \<open>P2 y\<close>
            apply(intro Cons(1))
            by auto
          then obtain xs1 x xs2 where "(a # xs) = (a #xs1) @ [x] @ xs2 \<and> P2 x \<and> (\<forall>y\<in>set xs2. \<not> P1 y)"
            by auto
          then show ?thesis
            by metis
        next
          case x_notin_ys2: False
          hence "a # xs = a#ys2 \<and> P2 y \<and> (\<forall>y\<in>set ys2. \<not> P1 y)"
            using \<open>xs = ys2\<close> \<open>P2 y\<close>
            by auto
          then show ?thesis
            using \<open>x' # xs = ys1 @ [y] @ ys2\<close> x_eq_a
            by blast
        qed
      next
        case ys2_nempty: False
        then obtain ys1' where "xs = ys1' @ [y] @ ys2"
          using \<open>x'#xs = ys1 @ [y] @ ys2\<close>
          by (auto simp: neq_Nil_conv)
        show ?thesis
        proof(cases "\<exists>x\<in>set ys2. P1 x")
          case x_in_ys2: True
          then obtain x where "x \<in> set ys2" "P1 x"
            by auto
          hence "\<exists>xs1 x xs2. xs = xs1 @ [x] @ xs2 \<and> P2 x \<and> (\<forall>y\<in>set xs2. \<not> P1 y)"
            using \<open>property xs\<close> \<open>xs = ys1' @ [y] @ ys2\<close> \<open>P2 y\<close>
            apply(intro Cons(1))
            by auto
          then obtain xs1 x xs2 where "(a # xs) = (a #xs1) @ [x] @ xs2 \<and> P2 x \<and> (\<forall>y\<in>set xs2. \<not> P1 y)"
            by auto
          then show ?thesis
            by metis
        next
          case x_notin_ys2: False
          hence "a # xs = (a# ys1') @ [y] @ ys2 \<and> P2 y \<and> (\<forall>y\<in>set ys2. \<not> P1 y)"
            using \<open>xs = ys1' @ [y] @ ys2\<close> \<open>P2 y\<close>
            by auto
          then show ?thesis
            by metis
        qed
      qed
    next
      case x_neq_a: False
      hence "x' \<in> set xs"
        using Cons
        by auto
      then obtain xs1 x xs2 where "xs = xs1 @ [x] @ xs2" "P2 x" "(\<forall>y\<in>set xs2. \<not> P1 y)"
        using Cons \<open>property xs\<close>
        by blast
      hence "a # xs = (a # xs1) @ [x] @ xs2 \<and> P2 x \<and> (\<forall>y\<in>set xs2. \<not> P1 y)"
        by auto
      thus ?thesis
        by metis
    qed
  qed
qed

lemma list_2_preds:
  "\<lbrakk> x\<in>set xs; P1 x; \<And>xs1 x xs2. \<lbrakk>xs = xs1 @ [x] @ xs2; P1 x\<rbrakk> \<Longrightarrow> \<exists>ys1 y ys2. x#xs2 = ys1 @ [y] @ ys2 \<and> P2 y\<rbrakk> \<Longrightarrow> 
     \<exists> xs1 x xs2. xs = xs1 @ [x] @ xs2 \<and> P2 x \<and> (\<forall>y\<in>set xs2. \<not> P1 y \<and> \<not> P2 y)"
proof(goal_cases)
  case assms: 1
  hence "\<exists>xs1 x xs2. xs = xs1 @ [x] @ xs2 \<and> P2 x \<and> (\<forall>y\<in>set xs2. \<not> P1 y)"
    by (fastforce intro!: list_2_preds_aux)
  then obtain xs1 x xs2 where "xs = xs1 @ [x] @ xs2" "P2 x" "(\<forall>y\<in>set xs2. \<not> P1 y)"
    by auto
  hence "\<exists>ys1 y ys2. x # xs2 = ys1 @ [y] @ ys2 \<and> P2 y \<and> (\<forall>z\<in>set ys2. \<not> P2 z)"
    by (auto intro!: split_list_last_prop)
  then obtain ys1 y ys2 where "x # xs2 = ys1 @ [y] @ ys2" "P2 y" "(\<forall>z\<in>set ys2. \<not> P2 z)"
    by auto
  hence "(\<forall>z\<in>set ys2. \<not>P1 z \<and> \<not> P2 z)"
    using \<open>(\<forall>y\<in>set xs2. \<not> P1 y)\<close> \<open>P2 x\<close>
    by (metis Un_iff insert_iff list.simps(15) set_append)
  moreover have "xs = (xs1 @ ys1) @ [y] @ ys2"
    using \<open>xs = xs1 @ [x] @ xs2\<close> \<open>x # xs2 = ys1 @ [y] @ ys2\<close>
    by auto
  ultimately show ?case
    using \<open>P2 y\<close>
    by fastforce
qed

lemma list_inter_mem_iff: "set xs \<inter> s \<noteq> {} \<longleftrightarrow> (\<exists>xs1 x xs2. xs = xs1 @ [x] @ xs2 \<and> x \<in> s)"
  by (metis append.left_neutral append_Cons disjoint_iff in_set_conv_decomp)

record ('parents, 'neighb) BFS_state = parents:: "'parents" current:: "'neighb" visited:: "'neighb"

locale BFS =
  Graph: Pair_Graph_Specs
    where lookup = lookup +
  set_ops: Set2 neighb_empty neighb_delete _ t_set neighb_inv insert
  
for lookup :: "'adj \<Rightarrow> 'ver \<Rightarrow> 'neighb option" +

fixes  
srcs::"'neighb" and
G::"'adj" and expand_tree::"'adj \<Rightarrow> 'neighb \<Rightarrow> 'neighb \<Rightarrow> 'adj" and
next_frontier::"'neighb \<Rightarrow> 'neighb \<Rightarrow> 'neighb" 


assumes
   expand_tree[simp]:
     "\<lbrakk>Graph.graph_inv BFS_tree; neighb_inv frontier; neighb_inv vis; Graph.graph_inv G\<rbrakk> \<Longrightarrow> 
       Graph.graph_inv (expand_tree BFS_tree frontier vis)"
     "\<lbrakk>Graph.graph_inv BFS_tree; neighb_inv frontier; neighb_inv vis; Graph.graph_inv G\<rbrakk> \<Longrightarrow>
        Graph.digraph_abs (expand_tree BFS_tree frontier vis) = 
         (Graph.digraph_abs BFS_tree) \<union> 
         {(u,v) | u v. u \<in> t_set (frontier) \<and> 
                       v \<in> (Pair_Graph.neighbourhood (Graph.digraph_abs G) u -
                       t_set vis)}" and
   next_frontier[simp]:
    "\<lbrakk>neighb_inv frontier; neighb_inv vis; Graph.graph_inv G\<rbrakk> \<Longrightarrow>  neighb_inv (next_frontier frontier vis)"
    "\<lbrakk>neighb_inv frontier; neighb_inv vis; Graph.graph_inv G\<rbrakk> \<Longrightarrow>
       t_set (next_frontier frontier vis) =
         (\<Union> {Pair_Graph.neighbourhood (Graph.digraph_abs G) u | u . u \<in> t_set frontier}) - t_set vis"

begin

definition "BFS_axiom \<longleftrightarrow>
  Graph.graph_inv G \<and> Graph.finite_graph G \<and> Graph.finite_neighbs \<and>
  t_set srcs \<subseteq> dVs (Graph.digraph_abs G) \<and>
  (\<forall>u. finite (Pair_Graph.neighbourhood (Graph.digraph_abs G) u)) \<and>
  t_set srcs \<noteq> {} \<and> neighb_inv srcs"

abbreviation "neighbourhood' \<equiv> Graph.neighbourhood G" 
notation "neighbourhood'" ("\<N>\<^sub>G _" 100)


function (domintros) BFS::"('adj, 'neighb) BFS_state \<Rightarrow> ('adj, 'neighb) BFS_state" where
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

partial_function (tailrec) BFS_impl::"('adj, 'neighb) BFS_state \<Rightarrow> ('adj, 'neighb) BFS_state" where
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

definition "BFS_call_1_conds bfs_state \<equiv> (current bfs_state) \<noteq> \<emptyset>\<^sub>N"


definition "BFS_upd1 BFS_state \<equiv>
(        let
          visited' = visited BFS_state \<union>\<^sub>G current BFS_state;
          parents' = expand_tree (parents BFS_state) (current BFS_state) visited';
          current' =  next_frontier (current BFS_state) visited'
        in 
          BFS_state \<lparr>parents:= parents', visited := visited', current := current'\<rparr>

)" 


definition "BFS_ret_1_conds bfs_state \<equiv>
    (current bfs_state) = \<emptyset>\<^sub>N"

abbreviation "BFS_ret1 bfs_state \<equiv> bfs_state"


definition "invar_1 bfs_state \<equiv>
              neighb_inv (visited bfs_state) \<and> neighb_inv (current bfs_state) \<and>
              Graph.graph_inv (parents bfs_state) \<and> 
              finite (t_set (current bfs_state)) \<and> finite (t_set (visited bfs_state))"

definition "invar_2 bfs_state \<equiv> 
  Graph.digraph_abs (parents bfs_state) \<subseteq> Graph.digraph_abs G \<and> 
  t_set (visited bfs_state) \<subseteq> dVs (Graph.digraph_abs G) \<and> 
  t_set (current bfs_state) \<subseteq> dVs (Graph.digraph_abs G) \<and> 
  dVs (Graph.digraph_abs (parents bfs_state)) \<subseteq> t_set (visited bfs_state) \<union> t_set (current bfs_state) \<and>
  t_set srcs \<subseteq> t_set (visited bfs_state) \<union> t_set (current bfs_state)"

definition "invar_3_1 bfs_state \<equiv> 
  (\<forall>v\<in>t_set (current bfs_state). \<forall>u. u \<in> t_set (current bfs_state) \<longleftrightarrow> 
      distance_set (Graph.digraph_abs G) (t_set srcs) v =
                           distance_set (Graph.digraph_abs G) (t_set srcs) u)"

definition "invar_3_2 bfs_state \<equiv> 
  (\<forall>v\<in>t_set (current bfs_state). \<forall>u \<in> t_set (visited bfs_state) \<union> t_set (current bfs_state).
     distance_set (Graph.digraph_abs G) (t_set srcs) u \<le>
       distance_set (Graph.digraph_abs G) (t_set srcs) v)"

definition "invar_3_3 bfs_state \<equiv> 
  (\<forall>v\<in>t_set (visited bfs_state).
     neighbourhood (Graph.digraph_abs G) v \<subseteq> t_set (visited bfs_state) \<union> t_set (current bfs_state))"

definition "invar_3_4 bfs_state \<equiv> 
  (\<forall>v\<in> t_set (visited bfs_state) \<union> t_set (current bfs_state).
     \<forall>u. distance_set (Graph.digraph_abs G) (t_set srcs) u \<le>
           distance_set (Graph.digraph_abs G) (t_set srcs) v
             \<longrightarrow> u \<in> t_set (visited bfs_state) \<union> t_set (current bfs_state))"

definition "invar_goes_through_current bfs_state \<equiv> 
         (\<forall>u\<in>t_set (visited bfs_state) \<union> t_set (current bfs_state). 
            \<forall>v. v \<notin> t_set (visited bfs_state) \<union> t_set (current bfs_state) \<longrightarrow>
              (\<forall>p. Vwalk.vwalk_bet (Graph.digraph_abs G) u p v \<longrightarrow> 
                     set p \<inter> t_set (current bfs_state) \<noteq> {}))"

definition "invar_dist' bfs_state \<equiv> 
  (\<forall>v \<in> dVs (Graph.digraph_abs G) - t_set srcs.
     (v \<in> (t_set (visited bfs_state) \<union> t_set (current bfs_state)) \<longrightarrow> distance_set (Graph.digraph_abs G) (t_set srcs) v =
         distance_set (Graph.digraph_abs (parents bfs_state)) (t_set srcs) v))"

definition "invar_parents_shortest_paths bfs_state \<equiv> 
  (\<forall>u\<in>t_set srcs.
      \<forall> p v. Vwalk.vwalk_bet (Graph.digraph_abs (parents bfs_state)) u p v \<longrightarrow>
         length p - 1 = distance_set (Graph.digraph_abs G) (t_set srcs) v)"

definition "call_1_measure_1 BFS_state\<equiv>
  card (dVs (Graph.digraph_abs G) - ((t_set (visited BFS_state)) \<union> t_set (current BFS_state)))"

definition "call_1_measure_2 BFS_state \<equiv>
  card (t_set (current BFS_state))"

definition
  "BFS_term_rel' \<equiv> call_1_measure_1 <*mlex*> call_1_measure_2 <*mlex*> {}"

definition "initial_state \<equiv> \<lparr>parents =  empty, current = srcs, visited = \<emptyset>\<^sub>N\<rparr>"

lemmas[code] = BFS_impl.simps initial_state_def

context
  includes Graph.adj.automation Graph.neighb.set.automation set_ops.automation
  assumes BFS_axiom  
begin

lemma graph_inv[simp]:
     "Graph.graph_inv G" 
     "Graph.finite_graph G"
     "Graph.finite_neighbs" and
   srcs_in_G[simp,intro]: 
     "t_set srcs \<subseteq> dVs (Graph.digraph_abs G)" and
   finite_neighb:
     "finite (Pair_Graph.neighbourhood (Graph.digraph_abs G) u)" and
  srcs_invar[simp]:
     "t_set srcs \<noteq> {}" 
     "neighb_inv srcs"
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
  (\<lbrakk>neighb_inv (visited bfs_state) ; neighb_inv (current bfs_state) ;
    Graph.graph_inv (parents bfs_state); 
    finite (t_set (current bfs_state)); finite (t_set (visited bfs_state))\<rbrakk> \<Longrightarrow> P)
     \<Longrightarrow> P"
  by (auto simp: invar_1_def)

lemma invar_1_intro[invar_props_intros]:
  "\<lbrakk>neighb_inv (visited bfs_state); neighb_inv (current bfs_state);
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
  using finite_neighb
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

definition "invar_current_reachable bfs_state \<equiv> 
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
  define bfs_state' where "bfs_state' \<equiv> BFS_upd1 bfs_state"
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

definition "invar_current_no_out bfs_state \<equiv> 
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

  define bfs_state' where "bfs_state' \<equiv> BFS_upd1 bfs_state"

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
          apply(auto elim!: invar_props_elims dest!: vwalk_bet_endpoints(2))
          by blast
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

definition "less_rel \<equiv> {(x::nat, y::nat). x < y}"

lemma wf_less_rel[intro!]: "wf less_rel"
  by(auto simp: less_rel_def wf_less)

definition "state_measure_rel call_measure \<equiv> inv_image less_rel call_measure"

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
    including Graph.adj.automation Graph.neighb.set.automation
    apply (auto simp: Graph.digraph_abs_def Graph.neighbourhood_def image_def
                split: option.splits)
    by (metis Graph.graph_invE Graph.neighb.set.set_isin graph_inv(1))
  moreover have "{uu. \<exists>v N. uu = t_set N \<and> lookup G v = Some N} = 
                   ((t_set o the o (lookup G)) ` {v | N v. lookup G v = Some N})"
    by (force simp: image_def)
  hence "finite (\<Union> {t_set N | v N. lookup G v = Some N})"
    using graph_inv(1,2,3)
    apply(subst (asm) Graph.finite_neighbs_def )
    by (auto simp: Graph.finite_graph_def Graph.graph_inv_def
             split: option.splits)
  ultimately have "finite {{v1, v2} |v1 v2. (v1,v2) \<in> [G]\<^sub>g}"
    using graph_inv(2)
    by (auto simp: Graph.finite_graph_def intro!: finite_subset[OF *])
  moreover have "finite {neighbourhood (Graph.digraph_abs G) u |u. u \<in> t_set (current BFS_state)}"
    using Graph.finite_neighbs_def
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
    by (fastforce simp: initial_state_def dVs_def Graph.finite_neighbs_def
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



(*

definition "invar_3_4' bfs_state \<equiv> 
  (\<forall>v\<in> t_set (visited bfs_state) \<union> t_set (current bfs_state). \<forall>w \<in> t_set srcs.
     \<forall>u. distance (Graph.digraph_abs G) w u \<le>
           distance (Graph.digraph_abs G) w v
             \<longrightarrow> u \<in> t_set (visited bfs_state) \<union> t_set (current bfs_state))"

lemma invar_3_4'_props[invar_props_elims]: 
  "invar_3_4' bfs_state \<Longrightarrow> 
  (\<lbrakk>\<And>u w v. \<lbrakk>v\<in> t_set (visited bfs_state) \<union> t_set (current bfs_state); w\<in> t_set srcs;
             distance (Graph.digraph_abs G) w u \<le> distance (Graph.digraph_abs G) w v\<rbrakk> \<Longrightarrow>
            u \<in> t_set (visited bfs_state) \<union> t_set (current bfs_state)\<rbrakk> \<Longrightarrow> P)
     \<Longrightarrow> P"
  unfolding invar_3_4'_def
  by blast

lemma invar_3_4'_intro[invar_props_intros]:
   "\<lbrakk>\<And>u w v. \<lbrakk>v\<in> t_set (visited bfs_state) \<union> t_set (current bfs_state); w\<in> t_set srcs;
               distance (Graph.digraph_abs G) w u \<le> distance (Graph.digraph_abs G) w v\<rbrakk> \<Longrightarrow>
            u \<in> t_set (visited bfs_state) \<union> t_set (current bfs_state)\<rbrakk>
    \<Longrightarrow> invar_3_4' bfs_state"
  unfolding invar_3_4'_def
  by blast



lemma dist_current_plus_1:                                               
  assumes
    "invar_1 bfs_state" "invar_2 bfs_state" "invar_3_4' bfs_state" 
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
        using \<open>invar_3_4' bfs_state\<close>
        apply(elim invar_props_elims)
        apply(drule dist_set_not_inf)
        using dual_order.trans dist_set_mem
        by (smt (verit, best))
    qed
    ultimately show ?thesis
      by force
  qed

lemma dist_current_plus_1':                                               
  assumes
    "invar_1 bfs_state" "invar_2 bfs_state" "invar_3_4' bfs_state" 
    "v \<in> neighbourhood (Graph.digraph_abs G) v'" 
    "v' \<in> t_set (current bfs_state)"
    "v \<in> t_set (current (BFS_upd1 bfs_state))"
    "w \<in> t_set srcs"
  shows  "distance (Graph.digraph_abs G) w v = 
            distance (Graph.digraph_abs G) w v' + 1" (is "?dv = ?dv' + 1")
  proof-
    have False if "?dv > ?dv' + 1"
      using distance_neighbourhood'[OF \<open>v \<in> neighbourhood (Graph.digraph_abs G) v'\<close>] that
      by (simp add: assms(4) leD)


    moreover have False if "?dv < ?dv' + 1"
    proof-
      have "?dv \<le> ?dv'"
        using that eSuc_plus_1 ileI1
        by force
      moreover have "v \<notin> t_set (visited bfs_state) \<union> t_set (current bfs_state)"
        using assms
        by (auto simp: BFS_upd1_def Let_def elim!: invar_1_props invar_2_props)
      moreover have "v' \<in> t_set (visited bfs_state) \<union> t_set (current bfs_state)"
        using \<open>v' \<in> t_set (current bfs_state)\<close> \<open>invar_2 bfs_state\<close>
        by (auto elim!: invar_2_props)
      ultimately show False
        using \<open>invar_3_4' bfs_state\<close> assms(7)
        by (auto elim: invar_props_elims)
    qed
    ultimately show ?thesis
      by force
  qed

lemma invar_3_1_holds_upd1[invar_holds_intros]: 
  "\<lbrakk>BFS_call_1_conds bfs_state; invar_1 bfs_state; invar_2 bfs_state ; invar_3_1 bfs_state;
    invar_3_2 bfs_state; invar_3_4' bfs_state; invar_current_reachable bfs_state\<rbrakk>
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
    by (auto intro!: dist_current_plus_1)
  moreover have "distance_set (Graph.digraph_abs G) (t_set srcs) u = ?d u' + 1"
    using assms
    by (auto intro!: dist_current_plus_1)
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
    by(fastforce intro!: dist_current_plus_1)

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




lemma invar_3_2_holds_upd1[invar_holds_intros]: 
  "\<lbrakk>BFS_call_1_conds bfs_state; invar_1 bfs_state; invar_2 bfs_state ; invar_3_1 bfs_state; 
    invar_3_2 bfs_state; invar_3_4' bfs_state; invar_current_reachable bfs_state\<rbrakk>
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
      by(fastforce intro!: dist_current_plus_1)
    ultimately show ?thesis
      by (metis le_iff_add order.trans)
  qed
qed




lemma invar_3_4'_holds_upd1[invar_holds_intros]: 
  "\<lbrakk>BFS_call_1_conds bfs_state; invar_1 bfs_state; invar_2 bfs_state;
    invar_3_1 bfs_state; invar_3_2 bfs_state; invar_3_3 bfs_state; invar_3_4' bfs_state;
    invar_current_reachable bfs_state\<rbrakk> \<Longrightarrow> 
    invar_3_4' (BFS_upd1 bfs_state)"
proof(intro invar_props_intros, goal_cases)                                                                  
  case assms: (1 u w v)
  show ?case
  proof(cases \<open>v \<in> t_set (visited bfs_state) \<union> t_set (current bfs_state)\<close>)
    case v_visited: True
    hence "u \<in> t_set (visited bfs_state) \<union> t_set (current bfs_state)"
      using \<open>invar_3_4' bfs_state\<close> assms
      by (fastforce elim: invar_props_elims)
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
    have "distance (Graph.digraph_abs G) w v = distance (Graph.digraph_abs G) w v' + 1" (is "?dv = ?dv' + 1")
      using assms \<open>v \<in> t_set (current (BFS_upd1 bfs_state))\<close>
      by (auto intro!: dist_current_plus_1')

    moreover have "u \<in> t_set (visited (BFS_upd1 bfs_state)) \<union> t_set (current (BFS_upd1 bfs_state))"
      if "distance (Graph.digraph_abs G) w u \<le> ?dv'" (is "?du \<le> ?dv'")
      using that \<open>invar_1 bfs_state\<close> \<open>invar_2 bfs_state\<close> \<open>invar_3_4' bfs_state\<close>
             \<open>w \<in> t_set srcs\<close> 
      by (fastforce simp: BFS_upd1_def Let_def elim!: invar_props_elims)

    moreover have "u \<in> t_set (visited (BFS_upd1 bfs_state)) \<union> t_set (current (BFS_upd1 bfs_state))"
      if "distance (Graph.digraph_abs G) w u = ?dv" (is "?du = _")
    proof(cases "?dv = \<infinity>")
      case dv_inf: True
      then show ?thesis
        using calculation(1) calculation(2) 
        by (simp add: plus_eq_infty_iff_enat)
    next
      case dv_not_inf: False
      hence "?dv < \<infinity>"
        by auto
      moreover have "w \<noteq> u"
      proof(rule ccontr, goal_cases)
        case 1
        moreover have "w \<in> dVs (Graph.digraph_abs G)"
          using dist_inf_2 dv_not_inf
          by force 
        ultimately have "distance (Graph.digraph_abs G) w u = 0"
          by (auto simp: distance_0[symmetric])
        then show ?case
          using \<open>distance (Graph.digraph_abs G) w v = distance (Graph.digraph_abs G) w v' + 1\<close> that
          by auto
      qed

      moreover have "distance (Graph.digraph_abs G) w u < \<infinity>"
        using calculation(1) that by auto
      ultimately obtain u' where u'[intro]:
        "u \<in> neighbourhood (Graph.digraph_abs G) u'" 
        "?du = distance (Graph.digraph_abs G) w u' + 1" (is "_ = ?du' + 1")  
        using distance_parent 
        by force
      hence "?du' = ?dv'"
        using \<open>?du = ?dv\<close> \<open>?dv = ?dv' + 1\<close>
        by auto
      hence "u' \<in> t_set (visited bfs_state) \<union> t_set (current bfs_state)" 
        using  \<open>invar_3_4' bfs_state\<close> \<open>v' \<in> t_set (current bfs_state)\<close>
          \<open>invar_2 bfs_state\<close> \<open>w \<in> t_set srcs\<close>
        apply (auto elim!: invar_props_elims)
        by (metis dual_order.refl)
      thus ?thesis
        using \<open>u \<in> neighbourhood (Graph.digraph_abs G) u'\<close> \<open>invar_1 bfs_state\<close> \<open>invar_2 bfs_state\<close>
              \<open>invar_3_3 bfs_state\<close> 
        by (fastforce simp: BFS_upd1_def Let_def elim!: invar_props_elims)
    qed
    ultimately show ?thesis
      using \<open>?du \<le> ?dv\<close> ileI1 linorder_not_less plus_1_eSuc(2)
      by fastforce
  qed
qed

lemma invar_3_4'_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_3_4' bfs_state\<rbrakk> \<Longrightarrow> invar_3_4' (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)


lemma invar_dist'_holds_upd1[invar_holds_intros]: 
  "\<lbrakk>BFS_call_1_conds bfs_state; invar_1 bfs_state; invar_2 bfs_state; invar_3_1 bfs_state;
    invar_3_2 bfs_state; invar_3_4' bfs_state; invar_dist' bfs_state\<rbrakk> 
    \<Longrightarrow> invar_dist' (BFS_upd1 bfs_state)"
proof(intro invar_props_intros, goal_cases)
  define bfs_state' where "bfs_state' \<equiv> BFS_upd1 bfs_state"
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
          using \<open>invar_1 bfs_state\<close> \<open>invar_3_4' bfs_state\<close> \<open>invar_2 bfs_state\<close>
          by (auto intro!: dist_current_plus_1)
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


*)


(*                                     
lemma list_suffix_disjoint: "\<lbrakk>set xs \<inter> s \<noteq> {}; last xs \<notin> s\<rbrakk> \<Longrightarrow> \<exists>xs1 x xs2. xs = xs1 @ x # xs2 \<and> x \<in> s \<and> set xs2 \<inter> s = {}"
proof(induction xs)
  case Nil
  then show ?case
    by auto
next
  case (Cons a xs)
  show ?case
  proof(cases "set xs \<inter> s = {}")
    case xs_disj_s: True
    show ?thesis
    proof(cases "xs = []")
      case xs_neq_Nil: False
      then have "a # xs = [] @ a # xs \<and> a \<in> s \<and> set xs \<inter> s = {}"
        using Cons xs_disj_s
        by auto
      then show ?thesis 
        by metis
    qed (insert Cons, auto)
  next
    case xs_not_disj_s: False
    then show ?thesis
    proof(cases "xs = []")
      case xs_neq_Nil: False
      then have "\<exists>xs1 x xs2. xs = xs1 @ x # xs2 \<and> x \<in> s \<and> set xs2 \<inter> s = {}"
        using Cons xs_not_disj_s
        by (auto intro!: Cons )
      then obtain xs1 x xs2 where "xs = xs1 @ x # xs2 \<and> x \<in> s \<and> set xs2 \<inter> s = {}"
        by auto
      hence "a # xs = (a # xs1) @ x # xs2 \<and> x \<in> s \<and> set xs2 \<inter> s = {}"
        by auto
      thus ?thesis
        by metis
    qed (insert Cons, auto)
  qed
qed

datatype 'a tree = Leaf | Node "'a tree" 'a "'a tree"

fun fold_tree where
"fold_tree f Leaf a = a"
| "fold_tree f (Node l x r) a = fold_tree f r (fold_tree f l a)" 

definition "invar P I f \<equiv> (\<forall>s. (P s \<and> I s) \<longrightarrow> I (f s))"

lemma invarI: "(\<And>s. \<lbrakk>P s; I s\<rbrakk> \<Longrightarrow> I (f s)) \<Longrightarrow> invar P I f"
  by (auto simp: invar_def)

lemma invarE: "invar P I f \<Longrightarrow> ((\<And>s. \<lbrakk>P s; I s\<rbrakk> \<Longrightarrow> I (f s)) \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (auto simp: invar_def)

lemma invarD: "invar P I f \<Longrightarrow> (\<And>s. \<lbrakk>P s; I s\<rbrakk> \<Longrightarrow> I (f s))"
  by (auto simp: invar_def)


definition "valid_fold set_of fold_fun \<equiv> \<forall>dom f a0. (\<exists>xs. fold_fun f dom a0 = foldr f xs a0 \<and> set xs = set_of dom)"

lemma valid_foldE:
  "valid_fold set_of fold_fun \<Longrightarrow> 
    (\<And>xs. \<lbrakk>fold_fun f domain a0 = foldr f xs a0; set_of domain = set xs\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (fastforce simp: valid_fold_def)

lemma invar_fold_conjI:
  fixes f:: "'a \<Rightarrow> 'b \<Rightarrow> 'b" and I::"'b \<Rightarrow> bool"
  assumes
    "valid_fold set_of fold_fun"
    "\<And>x. x \<in> set_of domain \<Longrightarrow> invar (\<lambda>_. True) (\<lambda>s. P s \<and> I s) (f x)"
  shows "invar P I (fold_fun f domain)"
proof-
  have "P (foldr f xs s) \<and> I (foldr f xs s)" if "(\<And>x. x \<in> set xs \<Longrightarrow> invar (\<lambda>_. True) (\<lambda>s. P s \<and> I s) (f x))" "P s" "I s" for xs s
    using that
  proof(induction xs)
    case (Cons x xs)
    hence "P (foldr f xs s)" "I (foldr f xs s)"
      by auto 
    thus ?case
      using Cons(2)[of x]
      by (auto elim!: invarE)
  qed auto
  hence "invar P I (foldr f xs)" if "(\<And>x. x \<in> set xs \<Longrightarrow> invar (\<lambda>_. True) (\<lambda>s. P s \<and> I s) (f x))" for xs
    using that
    by (auto intro!: invarI)
  thus ?thesis
    using assms
    by (smt (verit) invarE invarI valid_foldE)
qed

method elim_valid_fold for  f::"'a \<Rightarrow> 'b \<Rightarrow> 'b" = 
  ((match conclusion in "P (fold_fun f domain a0)" for a0::'b and fold_fun domain and P 
      \<Rightarrow> \<open>elim valid_foldE[where f = f and domain = domain and ?a0.0 = a0], match premises in a[thin]: 
           "fold_fun f domain a0 = foldr _ _ _"
              \<Rightarrow> \<open>subst  a\<close>\<close>))

lemma invar_foldI:
  fixes f:: "'a \<Rightarrow> 'b \<Rightarrow> 'b" and I::"'b \<Rightarrow> bool"
  assumes
    "valid_fold set_of fold_fun"
    "\<And>x. x \<in> set_of domain \<Longrightarrow> invar (\<lambda>_. True) I (f x)"
  shows "invar (\<lambda>_. True) I (fold_fun f domain)"
  using assms(2)
  by(auto intro!: invar_fold_conjI[OF assms(1), where P = "\<lambda>_. True"])

lemma invar_foldI':
  fixes f:: "'a \<Rightarrow> 'b \<Rightarrow> 'b" and I::"'b \<Rightarrow> bool"
  assumes
    "valid_fold set_of fold_fun"
    "\<And>x s. \<lbrakk>x \<in> set_of domain; I s\<rbrakk> \<Longrightarrow> I (f x s)"
    "I s"
  shows "I (fold_fun f domain s)"
  using invar_foldI[simplified invar_def, OF assms(1)] assms
  by metis

lemma invar_foldI'':
  fixes f:: "'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" and I::"'b \<Rightarrow> bool"
  assumes
    "valid_fold set_of fold_fun"
    "\<And>s x. \<lbrakk>I s; x \<in> set_of (domain s)\<rbrakk> \<Longrightarrow> invar (\<lambda>_. True) I (f s x)"
  shows "invar (\<lambda>_. True) I (\<lambda>s. fold_fun (f s) (domain s) s)"
  using invar_foldI[OF assms(1)] assms(2-)
  by (metis (no_types, lifting) invar_def)

lemma invar_fold_conjI'':
  fixes f:: "'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" and I::"'b \<Rightarrow> bool"
  assumes
    "valid_fold set_of fold_fun"
    "\<And>s x. \<lbrakk>I s; x \<in> set_of (domain s)\<rbrakk> \<Longrightarrow> invar (\<lambda>_. True) (\<lambda>s. P s \<and> I s) (f s x)"
  shows "invar P I (\<lambda>s. fold_fun (f s) (domain s) s)"
  using invar_fold_conjI[OF assms(1)] assms(2-)
  by (smt (verit, ccfv_SIG) invar_def)

lemma invar_conjI: "\<lbrakk>J; invar P (\<lambda>s. J \<and> I s) f\<rbrakk> \<Longrightarrow> invar P I f"
  by (auto simp: invar_def)
*)

(*definition "invar_3_4 bfs_state \<equiv> 
  (\<forall>v\<in> t_set (visited bfs_state).
     \<forall>u. distance_set (Graph.digraph_abs G) (t_set srcs) u \<le>
           distance_set (Graph.digraph_abs G) (t_set srcs) v
             \<longrightarrow> u \<in> t_set (visited bfs_state))"

lemma invar_3_4_props[invar_props_elims]: 
  "invar_3_4 bfs_state \<Longrightarrow> 
  (\<lbrakk>\<And>u v. \<lbrakk>v\<in> t_set (visited bfs_state); distance_set (Graph.digraph_abs G) (t_set srcs) u \<le>
           distance_set (Graph.digraph_abs G) (t_set srcs) v\<rbrakk> \<Longrightarrow>
            u \<in> t_set (visited bfs_state)\<rbrakk> \<Longrightarrow> P)
     \<Longrightarrow> P"
  by(auto simp: invar_3_4_def)

lemma invar_3_4_intro[invar_props_intros]:
   "\<lbrakk>\<And>u v. \<lbrakk>v\<in> t_set (visited bfs_state); distance_set (Graph.digraph_abs G) (t_set srcs) u \<le>
           distance_set (Graph.digraph_abs G) (t_set srcs) v\<rbrakk> \<Longrightarrow>
            u \<in> t_set (visited bfs_state)\<rbrakk>
    \<Longrightarrow> invar_3_4 bfs_state"
  by(auto simp add: invar_3_4_def)
*)

(*
lemma invar_3_4_holds_upd1[invar_holds_intros]: 
  "\<lbrakk>BFS_call_1_conds bfs_state; invar_1 bfs_state; invar_2 bfs_state;
    invar_3_1 bfs_state; invar_3_2 bfs_state; invar_3_3 bfs_state; invar_3_4 bfs_state;
    invar_current_reachable bfs_state\<rbrakk> \<Longrightarrow> 
    invar_3_4 (BFS_upd1 bfs_state)"
proof(intro invar_props_intros, goal_cases)                                                                                                    
  case assms: (1 u v)
  show ?case
  proof(cases \<open>v \<in> t_set (visited bfs_state)\<close>)
    case v_visited: True
    hence "u \<in> t_set (visited bfs_state)"
      using \<open>invar_3_4 bfs_state\<close> assms
      by (auto elim!: invar_3_4_props)
    then show ?thesis 
      using \<open>invar_1 bfs_state\<close> \<open>v \<in> t_set (visited (BFS_upd1 bfs_state))\<close>
      by (auto simp: BFS_upd1_def Let_def elim: invar_props_elims)
  next
    case v_not_visited: False
    hence "v \<in> t_set (current (BFS_upd1 bfs_state))"
      using \<open>invar_1 bfs_state\<close> \<open>v \<in> t_set (visited (BFS_upd1 bfs_state))\<close>
      by (auto simp: BFS_upd1_def Let_def elim: invar_props_elims)
    then obtain v' where v'[intro]:
      "v \<in> neighbourhood (Graph.digraph_abs G) v'" "v' \<in> t_set (current bfs_state)"
      using \<open>invar_1 bfs_state\<close>
      by (auto simp: BFS_upd1_def Let_def elim!: invar_1_props)
    have "distance_set (Graph.digraph_abs G) (t_set srcs) v = 
            distance_set (Graph.digraph_abs G) (t_set srcs) v' + 1" (is "?dv = ?dv' + 1")
      using assms \<open>v \<in> t_set (current (BFS_upd1 bfs_state))\<close>
      by (auto intro!: dist_current_plus_1)
    moreover have "u \<in> t_set (visited (BFS_upd1 bfs_state))"
      if "distance_set (Graph.digraph_abs G) (t_set srcs) u \<le> ?dv'" (is "?du \<le> ?dv'")
      using that \<open>invar_1 bfs_state\<close> \<open>invar_2 bfs_state\<close> \<open>invar_3_4 bfs_state\<close> 
      by (auto simp: BFS_upd1_def Let_def elim!: invar_1_props invar_2_props invar_3_4_props)
    moreover have "u \<in> t_set (visited (BFS_upd1 bfs_state))"
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
(*
      then obtain u' where u'[intro]:
        "u \<in> neighbourhood (Graph.digraph_abs G) u'"
        "u' \<in> t_set (current bfs_state)"
        using assms
        by (auto simp: BFS_upd1_def Let_def elim!: invar_1_props)
      hence "distance_set (Graph.digraph_abs G) (t_set srcs) u = distance_set (Graph.digraph_abs G) (t_set srcs) u' + 1"
        using assms(2,3,7) \<open>u \<in> t_set (current (BFS_upd1 bfs_state))\<close> dist_current_plus_1
        by blast
      hence "distance_set (Graph.digraph_abs G) (t_set srcs) u' \<le> distance_set (Graph.digraph_abs G) (t_set srcs) v'" (is "?du' \<le> _")
        using that \<open>?dv = ?dv' +1\<close>
        by auto
      hence "u' \<in> t_set (visited bfs_state)"
        using  assms(3) \<open>invar_3_4 bfs_state\<close>
        by (force elim: invar_props_elims)
      hence "u' \<in> t_set (current bfs_state) \<or> u' \<in> t_set (visited bfs_state) - t_set (current bfs_state)"
        by auto
      thus ?thesis
      proof(elim disjE, goal_cases)
        case 1
        thus ?case
          using \<open>u \<in> neighbourhood (Graph.digraph_abs G) u'\<close> \<open>invar_1 bfs_state\<close> \<open>invar_2 bfs_state\<close>
          by (fastforce simp: BFS_upd1_def Let_def elim!: invar_1_props invar_2_props)
      next
        case 2
        then show ?case
          using \<open>u \<in> neighbourhood (Graph.digraph_abs G) u'\<close> \<open>invar_1 bfs_state\<close>
            \<open>invar_3_3 bfs_state\<close>
          by (fastforce simp: BFS_upd1_def Let_def)
      qed*)
    qed
    ultimately show ?thesis
      using \<open>?du \<le> ?dv\<close> ileI1 linorder_not_less plus_1_eSuc(2)
      by fastforce
  qed
qed

lemma invar_3_4_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_3_4 bfs_state\<rbrakk> \<Longrightarrow> invar_3_4 (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)
*)

(*
definition "invar_forest bfs_state \<equiv> forest (Graph.digraph_abs (parents bfs_state))"

lemma invar_forest_props[elim]: 
  "invar_forest bfs_state \<Longrightarrow> 
  (forest (Graph.digraph_abs (parents bfs_state)) \<Longrightarrow> P)
     \<Longrightarrow> P"
  by (auto simp: invar_forest_def)

lemma invar_forest_intro[invar_props_intros]:
   "\<lbrakk>forest (Graph.digraph_abs (parents bfs_state))\<rbrakk>
     \<Longrightarrow> invar_forest bfs_state"
  by (auto simp: invar_forest_def)

lemma invar_forest_holds_upd1[invar_holds_intros]: 
  "\<lbrakk>BFS_call_1_conds bfs_state; invar_1 bfs_state; invar_2 bfs_state; invar_forest bfs_state\<rbrakk> \<Longrightarrow> invar_forest (BFS_upd1 bfs_state)"
  apply(auto elim!: call_cond_elims invar_1_props invar_2_props invar_forest_props intro!: invar_props_intros simp: BFS_upd1_def Let_def)
  apply(auto simp: dVs_def)
  done

lemma invar_forest_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_forest bfs_state\<rbrakk> \<Longrightarrow> invar_forest (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_forest_holds: 
   assumes "BFS_dom bfs_state" "invar_1 bfs_state" "invar_2 bfs_state" "invar_forest bfs_state"
   shows "invar_forest (BFS bfs_state)"
  using assms(2-)
proof(induction rule: BFS_induct[OF assms(1)])
  case IH: (1 bfs_state)
  show ?case
    apply(rule BFS_cases[where bfs_state = bfs_state])
    by (auto intro!: IH(2-) intro: invar_holds_intros  simp: BFS_simps[OF IH(1)])
qed

\<comment> \<open>This is equivalent to 200 on the board, except that I changed tree to G\<close>

definition "invar_3_1' bfs_state \<equiv> 
  (\<forall>v\<in>t_set (current bfs_state). \<forall>u. u \<in> t_set (current bfs_state) \<longleftrightarrow> 
      distance_set (Graph.digraph_abs (parents bfs_state)) (t_set srcs) v =
                           distance_set (Graph.digraph_abs (parents bfs_state)) (t_set srcs) u)"

lemma invar_3_1'_props[elim]: 
  "invar_3_1' bfs_state \<Longrightarrow>
  (\<lbrakk>\<lbrakk>v \<in> t_set (current bfs_state); u \<in> t_set (current bfs_state)\<rbrakk> \<Longrightarrow>
            distance_set (Graph.digraph_abs (parents bfs_state)) (t_set srcs) v =
                 distance_set (Graph.digraph_abs (parents bfs_state)) (t_set srcs) u;
    \<lbrakk>v \<in> t_set (current bfs_state);
            distance_set (Graph.digraph_abs (parents bfs_state)) (t_set srcs) v = 
              distance_set (Graph.digraph_abs (parents bfs_state)) (t_set srcs) u\<rbrakk> \<Longrightarrow>
            u \<in> t_set (current bfs_state)\<rbrakk> \<Longrightarrow> P)
     \<Longrightarrow> P"
  unfolding invar_3_1'_def
  by blast

lemma invar_3_1'_intro[invar_props_intros]:
   "\<lbrakk>\<And>u v. \<lbrakk>v \<in> t_set (current bfs_state); u \<in> t_set (current bfs_state)\<rbrakk> \<Longrightarrow>
            distance_set (Graph.digraph_abs (parents bfs_state)) (t_set srcs) v =
                           distance_set (Graph.digraph_abs (parents bfs_state)) (t_set srcs) u;
     \<And>u v. \<lbrakk>v \<in> t_set (current bfs_state); distance_set (Graph.digraph_abs (parents bfs_state)) (t_set srcs) v =
                 distance_set (Graph.digraph_abs (parents bfs_state)) (t_set srcs) u\<rbrakk> \<Longrightarrow>
            u \<in> t_set (current bfs_state)\<rbrakk>
    \<Longrightarrow> invar_3_1' bfs_state"
  unfolding invar_3_1'_def
  by blast



lemma invar_3_1'_holds_upd1[invar_holds_intros]: 
  "\<lbrakk>BFS_call_1_conds bfs_state; invar_1 bfs_state; invar_2 bfs_state ; invar_3_1' bfs_state;
    invar_3_2 bfs_state; invar_3_4 bfs_state; invar_current_reachable bfs_state\<rbrakk>
     \<Longrightarrow> invar_3_1' (BFS_upd1 bfs_state)"
proof(intro invar_props_intros, goal_cases)
  case assms: (1 u v)
  obtain u' v' where uv'[intro]: "u \<in> neighbourhood (Graph.digraph_abs (parents (BFS_upd1 bfs_state))) u'" "u' \<in> t_set (current bfs_state)" 
                          "v \<in> neighbourhood (Graph.digraph_abs (parents (BFS_upd1 bfs_state))) v'" "v' \<in> t_set (current bfs_state)"
    using assms(1,2,8,9)
    apply (auto simp: BFS_upd1_def Let_def elim!: invar_1_props)
    by (metis (no_types, lifting) case_prodI mem_Collect_eq neighbourhoodD)

  moreover hence "distance_set (Graph.digraph_abs (parents bfs_state)) (t_set srcs) v' =
                    distance_set (Graph.digraph_abs (parents bfs_state)) (t_set srcs) u'" (is "?d v' = ?d u'")
    using \<open>invar_3_1' bfs_state\<close>
    by auto
  moreover have "distance_set (Graph.digraph_abs (parents (BFS_upd1 bfs_state))) (t_set srcs) v = ?d v' + 1"
    using assms
    by (auto intro!: dist_curr ent_plus_1)
  oops

  moreover have "distance_set (Graph.digraph_abs (parents bfs_state)) (t_set srcs) u = ?d u' + 1"
    using assms
    by (auto intro!: dist_current_plus_1)
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
    by(fastforce intro!: dist_current_plus_1)

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
      by (metis srcs_nempty)
    hence "?d u' = ?d v'"
      using \<open>?d v = ?d v' + 1\<close> \<open>?d v = ?d u\<close>
      by auto
    hence "u' \<in> t_set (current bfs_state)"
      using \<open>invar_3_1' bfs_state\<close>
            \<open>v' \<in> t_set (current bfs_state)\<close>
      by (auto elim!: invar_3_1'_props)
    moreover have "?d u' < ?d u"
      using \<open>?d u < \<infinity>\<close> 
      using zero_less_one not_infinity_eq 
      by (fastforce intro!: plus_one_side_lt_enat simp: \<open>?d u' + 1 = ?d u\<close>[symmetric])
    hence "u \<notin> t_set (visited bfs_state)"
      using \<open>invar_3_2 bfs_state\<close> \<open>u' \<in> t_set (current bfs_state)\<close> 
      by (auto elim!: invar_3_2_props dest: leD)
    ultimately show ?thesis
      using \<open>invar_1 bfs_state\<close> \<open>invar_2 bfs_state\<close> \<open>u \<in> neighbourhood (Graph.digraph_abs G) u'\<close>
      by(fastforce simp: BFS_upd1_def Let_def elim!: invar_1_props invar_2_props)
  next
    case not_in_srcs: False
    text \<open>Contradiction because if \<open>u \<in> srcs\<close> then distance srcs to a vertex in srcs is > 0. This is
          because the distance from srcs to \<open>u\<close> is the same as that to \<open>v\<close>.\<close>
    then show ?thesis
      using \<open>?d v = ?d u\<close> \<open>?d v = ?d v' + 1\<close>
      by auto
  qed
qed

lemma invar_3_1'_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_3_3 bfs_state\<rbrakk> \<Longrightarrow> invar_3_3 (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)


definition "invar_dist bfs_state \<equiv> 
  (\<forall>v \<in> dVs (Graph.digraph_abs G).
     (\<comment>\<open>v \<in> t_set (visited bfs_state) \<longrightarrow> \<close>distance_set (Graph.digraph_abs G) (t_set srcs) v =
         distance_set (Graph.digraph_abs (parents bfs_state)) (t_set srcs) v) \<and>
       (\<comment>\<open>v \<notin> t_set (visited bfs_state) \<longrightarrow> \<close>(\<exists>u\<in>t_set (current bfs_state). distance_set (Graph.digraph_abs G) (t_set srcs) v =
                                        distance_set (Graph.digraph_abs (parents bfs_state)) (t_set srcs) u +
                                         distance_set (Graph.digraph_abs G) (t_set (current bfs_state)) v)))"
                                      
lemma invar_dist_props[elim]: 
  "invar_dist bfs_state \<Longrightarrow> v \<in> dVs (Graph.digraph_abs G) \<Longrightarrow> 
   \<lbrakk>
     \<lbrakk>\<comment>\<open>v \<in> t_set (visited bfs_state); \<close>distance_set (Graph.digraph_abs G) (t_set srcs) v =
         distance_set (Graph.digraph_abs (parents bfs_state)) (t_set srcs) v\<rbrakk> \<Longrightarrow> P;
     \<And>u.\<lbrakk>\<comment>\<open>v \<notin> t_set (visited bfs_state); \<close>u\<in>t_set (current bfs_state);
            distance_set (Graph.digraph_abs G) (t_set srcs) v =  
              distance_set (Graph.digraph_abs (parents bfs_state)) (t_set srcs) u +
                distance_set (Graph.digraph_abs G) (t_set (current bfs_state)) v\<rbrakk> \<Longrightarrow> P
   \<rbrakk>                                                                                              
   \<Longrightarrow> P"
  unfolding invar_dist_def
  by auto

lemma invar_dist_intro[invar_props_intros]:
   "\<lbrakk>\<And>v. \<lbrakk>v \<in> dVs (Graph.digraph_abs G)\<comment>\<open>; v \<in> t_set (visited bfs_state)\<close>\<rbrakk> \<Longrightarrow> 
           (distance_set (Graph.digraph_abs G) (t_set srcs) v =
             distance_set (Graph.digraph_abs (parents bfs_state)) (t_set srcs) v);
     \<And>v. \<lbrakk>v \<in> dVs (Graph.digraph_abs G)\<comment>\<open>; v \<notin> t_set (visited bfs_state)\<close>\<rbrakk> \<Longrightarrow>
            (\<exists>u\<in>t_set (current bfs_state).
                    distance_set (Graph.digraph_abs G) (t_set srcs) v =
                      distance_set (Graph.digraph_abs (parents bfs_state)) (t_set srcs) u +
                        distance_set (Graph.digraph_abs G) (t_set (current bfs_state)) v)\<rbrakk>
        
    \<Longrightarrow> invar_dist bfs_state"
  unfolding invar_dist_def
  by auto

lemma distance_next_frontier: 
  "\<lbrakk>invar_1 BFS_state; invar_2 BFS_state; 
        v \<in> t_set (next_frontier (current BFS_state) (visited BFS_state))\<rbrakk>
         \<Longrightarrow> distance_set (Graph.digraph_abs G) (t_set (current BFS_state)) v = 1"
proof(goal_cases)
  case assms: 1
  then obtain u where "u \<in> t_set (current BFS_state)" "v \<in> neighbourhood (Graph.digraph_abs G) u"
    by force
  hence "v \<notin> t_set (current BFS_state)"
    using assms
    by force
  hence "u \<noteq> v" if "u \<in> t_set (current BFS_state)" for u                                                                         
    using that 
    by auto
  hence "distance (Graph.digraph_abs G) u v \<noteq> 0"  if "u \<in> t_set (current BFS_state)" for u
    using distance_0 that
    by metis
  hence "distance (Graph.digraph_abs G) u v = 1"
    using distance_neighbourhood \<open>u \<in> t_set (current BFS_state)\<close>
          \<open>v \<in> neighbourhood (Graph.digraph_abs G) u\<close> iless_eSuc0 one_eSuc
    by fastforce
  thus ?thesis
    by (metis \<open>u \<in> t_set (current BFS_state)\<close> \<open>v \<notin> t_set (current BFS_state)\<close> dist_not_inf'
              dist_set_mem distance_0 iless_eSuc0 infinity_ileE one_eSuc one_enat_def
              order_le_imp_less_or_eq)
qed

lemma dist_tree_visited:
  "\<lbrakk>invar_1 bfs_state; invar_2 bfs_state; invar_dist bfs_state; v \<in> t_set (visited bfs_state)\<rbrakk> \<Longrightarrow> 
     distance_set (Graph.digraph_abs G) (t_set srcs) v = 
       distance_set (Graph.digraph_abs (parents bfs_state)) (t_set srcs) v" (is "\<lbrakk>_; _; _; _\<rbrakk> \<Longrightarrow> ?dSrcsG v = ?dSrcsT v")
proof(goal_cases)
  case 1
  have "?dSrcsG v \<le>  ?dSrcsT v"
  proof(rule ccontr, goal_cases)
    case 1
    hence "?dSrcsG v \<noteq>  ?dSrcsT v"
      by auto
    then obtain u where "u \<in> t_set (current bfs_state)"
                        "?dSrcsG v =  ?dSrcsT u +
                              distance_set (Graph.digraph_abs G) (t_set (current bfs_state)) v"
      using  \<open>invar_dist bfs_state\<close> \<open>v \<in> t_set (visited bfs_state)\<close> \<open>invar_2 bfs_state\<close>
      by (force elim!: invar_dist_props dest: dVs_subset)

    then show ?case sorry
  qed
  oops

lemma invar_dist_holds_upd1[invar_holds_intros]: 
  "\<lbrakk>BFS_call_1_conds bfs_state; invar_1 bfs_state; invar_2 bfs_state; invar_3_1 bfs_state;
    invar_3_2 bfs_state; invar_dist bfs_state\<rbrakk> 
    \<Longrightarrow> invar_dist (BFS_upd1 bfs_state)"
proof(intro invar_props_intros, goal_cases)
  define bfs_state' where "bfs_state' \<equiv> BFS_upd1 bfs_state"
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
      by(fastforce simp: bfs_state'_def BFS_upd1_def Let_def intro: distance_set_subset)    
    ultimately show ?thesis
      by (simp add: bfs_state'_def)
  next
    case finite: False
    show ?thesis
    proof(cases "v \<in> dVs (Graph.digraph_abs (parents bfs_state))")
      case v_in_tree: True
      have "?dSrcsT v = ?dSrcsG v"
      proof(rule ccontr, goal_cases)
        case 1
        moreover have \<open>Graph.digraph_abs (parents bfs_state) \<subseteq> Graph.digraph_abs G\<close>
          using \<open>invar_2 bfs_state\<close>
          by auto
        ultimately have "?dSrcsG v < ?dSrcsT v"
          text \<open>because the tree is a subset of the Graph, which invar?\<close>
          by (simp add: distance_set_subset order_less_le)
        then obtain p where p: 
          "p\<in>t_set (current bfs_state)"
          "?dSrcsG v = ?dSrcsT p + ?dCurrG v"
          using \<open>invar_dist bfs_state\<close> v_in_tree \<open>v \<in> dVs (Graph.digraph_abs G)\<close>
          by auto
        hence "?dSrcsT p + ?dCurrG v < ?dSrcsT v"
          using \<open>?dSrcsG v < ?dSrcsT v\<close>
          by simp
        hence "?dSrcsT p < ?dSrcsT v"
          by (meson le_iff_add order_le_less_trans)
        moreover have "?dSrcsT p = ?dSrcsG p "
          using \<open>p \<in> t_set (current bfs_state)\<close> \<open>invar_dist bfs_state\<close> \<open>invar_2 bfs_state\<close>
          by (metis "1" dist_set_inf invar_dist_def local.finite)
        moreover have "?dSrcsT v = ?dSrcsG v"
          using v_in_tree \<open>invar_dist bfs_state\<close> \<open>invar_2 bfs_state\<close> \<open>v\<in> dVs (Graph.digraph_abs G)\<close>
          by (metis invar_dist_def)
        ultimately have "?dSrcsG p < ?dSrcsG v"
          by auto
        then show ?case
          using \<open>invar_2 bfs_state\<close> \<open>invar_3_1 bfs_state\<close> \<open>invar_3_2 bfs_state\<close> v_in_tree
                \<open>p \<in> t_set (current bfs_state)\<close>
          by fastforce
      qed
      moreover have "?dSrcsT v = ?dSrcsT' v"
      proof-
        have "?dSrcsT' v \<le> ?dSrcsT v"
          using \<open>invar_1 bfs_state\<close>
          by(fastforce simp: bfs_state'_def BFS_upd1_def Let_def intro: distance_set_subset)

        moreover have "?dSrcsG v \<le> ?dSrcsT' v"
          using \<open>invar_1 bfs_state\<close> \<open>invar_2 bfs_state\<close>
          by(fastforce simp: bfs_state'_def BFS_upd1_def Let_def intro: distance_set_subset)

        ultimately show ?thesis
          using \<open>?dSrcsT v = ?dSrcsG v\<close>
          by auto
      qed
      ultimately show ?thesis
        by (auto simp: bfs_state'_def)
    next
      case v_not_in_tree: False
      hence "?dSrcsT v = \<infinity>"
        by(auto intro: dist_set_inf)
      hence "?dSrcsG v \<noteq> ?dSrcsT v"
        using finite
        by auto
      then obtain u where 
               "u\<in>t_set (current bfs_state)"
               "?dSrcsG v = ?dSrcsT u + ?dCurrG v"
        using \<open>invar_dist bfs_state\<close> \<open>v \<in> dVs (Graph.digraph_abs G)\<close>
        by auto
      have "?dCurrG v \<noteq> \<infinity>"
        using finite \<open>?dSrcsG v = ?dSrcsT u + ?dCurrG v\<close>
        by (simp add: plus_eq_infty_iff_enat)
      then obtain w where "w \<in> t_set (current bfs_state)" "Pair_Graph.reachable (Graph.digraph_abs G) w v"
                     "distance (Graph.digraph_abs G) w v = ?dCurrG v"
        by (meson dist_not_inf')
      find_theorems distance_set "{}"                        
      obtain p where "vwalk_bet (Graph.digraph_abs G) w (w#p) v"
                     "length p = distance (Graph.digraph_abs G) w v"
                     "set p \<inter> (t_set (current bfs_state)) = {}"
         using dist_not_inf''[OF \<open>?dCurrG v \<noteq> \<infinity>\<close> 
                                 \<open>w \<in> t_set (current bfs_state)\<close>
                                 \<open>distance (Graph.digraph_abs G) w v = ?dCurrG v\<close>]
         by auto
      hence "shortest_path (Graph.digraph_abs G) w (w#p) v"
        by (simp add: shortest_path_def)
      show ?thesis
      proof(cases "distance (Graph.digraph_abs G) w v = 0")
        case dist_w_v_0: True
        then show ?thesis sorry
      next
        case dist_w_v_not_0: False
        then obtain i where \<open>eSuc i = distance (Graph.digraph_abs G) w v\<close> 
          using \<open>length p = distance (Graph.digraph_abs G) w v\<close>
          by(cases p) (fastforce simp: enat_0)+
        then obtain x p' where "p = x # p'"
          using \<open>length p = distance (Graph.digraph_abs G) w v\<close> \<open>?dCurrG v \<noteq> \<infinity>\<close>
                \<open>distance (Graph.digraph_abs G) w v = ?dCurrG v\<close>
          by (cases p) (auto simp: neq_Nil_conv enat_0)

        define current' where "current' \<equiv> (t_set (current bfs_state)) \<union>
                                  (t_set (next_frontier (current bfs_state) (visited bfs_state)))"

        note \<open>distance (Graph.digraph_abs G) w v = ?dCurrG v\<close>
             \<open>w \<in> t_set (current bfs_state)\<close>
             \<open>invar_1 bfs_state\<close> \<open>invar_2 bfs_state\<close>
        moreover have "shortest_path (Graph.digraph_abs G) w (w#x#p') v"
          using \<open>shortest_path (Graph.digraph_abs G) w (w#p) v\<close> \<open>p = x # p'\<close>
          by auto

        find_theorems shortest_path vwalk_bet

        moreover hence "x \<in> neighbourhood (Graph.digraph_abs G) w"
          by(auto dest!: shortest_path_vwalk)



        ultimately have "distance_set (Graph.digraph_abs G) current' v =
                           distance_set (Graph.digraph_abs G) (t_set (current bfs_state)) v -
                             distance (Graph.digraph_abs G) w x"
          apply (subst current'_def)
          apply (rule shortest_path_dist_set_union[where ?p1.0 = "[w]"])
          apply auto[1]
          apply auto[1]          
          apply auto[1]
          apply (auto elim!: invar_1_props invar_2_props)
          apply auto[1]
          sorry


        then show ?thesis
          
      qed

    qed
  qed

qed







definition "invar_3 bfs_state \<equiv> 
  (\<forall>v \<in> t_set (visited bfs_state).
       distance_set (Graph.digraph_abs (parents bfs_state)) (t_set srcs) v \<le> 
         distance_set (Graph.digraph_abs G) (t_set srcs) v)"

lemma invar_3_props[elim]: 
  "invar_3 bfs_state \<Longrightarrow> 
  (\<lbrakk>\<And>v. v \<in> t_set (visited bfs_state) \<Longrightarrow> 
    distance_set (Graph.digraph_abs (parents bfs_state)) (t_set srcs) v \<le> 
         distance_set (Graph.digraph_abs G) (t_set srcs) v\<rbrakk> \<Longrightarrow> P)
     \<Longrightarrow> P"
  by (auto simp: invar_3_def)

lemma invar_3_intro[invar_props_intros]:
   "(\<And>v. v \<in> t_set (visited bfs_state) \<Longrightarrow> 
    distance_set (Graph.digraph_abs (parents bfs_state)) (t_set srcs) v \<le> 
         distance_set (Graph.digraph_abs G) (t_set srcs) v)
     \<Longrightarrow> invar_3 bfs_state"
  by (auto simp: invar_3_def)

lemma invar_3_4_holds_upd1[invar_holds_intros]: 
  "\<lbrakk>BFS_call_1_conds bfs_state; invar_1 bfs_state; invar_2 bfs_state ;
    invar_3_1 bfs_state; invar_3_3 bfs_state; invar_3_4 bfs_state; invar_3 bfs_state\<rbrakk> 
    \<Longrightarrow> invar_3 (BFS_upd1 bfs_state)"
proof(intro invar_props_intros, goal_cases)
  case (1 v)
  have ?case (is "?dT'v \<le> ?dGv")
    if "v \<notin> t_set (visited bfs_state)"
  proof-
    from 1 and that obtain v' where v'[intro]:
      "v \<in> neighbourhood (Graph.digraph_abs G) v'"
      "v' \<in> t_set (current bfs_state)" 
      "v \<in> neighbourhood (Graph.digraph_abs (parents (BFS_upd1 bfs_state))) v'"
      apply (auto simp: BFS_upd1_def Let_def elim!: invar_1_props invar_2_props)
      by (simp add: neighbourhoodD)
    hence "v' \<in> t_set (visited bfs_state)"
      using \<open>invar_1 bfs_state\<close> \<open>invar_2 bfs_state\<close>
      by (auto elim!: invar_1_props invar_2_props)
    hence "distance_set (Graph.digraph_abs (parents bfs_state)) (t_set srcs) v'
         \<le> distance_set (Graph.digraph_abs G) (t_set srcs) v'" (is "?dTv' \<le> ?dGv'")
      using \<open>invar_3 bfs_state\<close>
      by (auto elim!: invar_3_props)
    moreover have "distance_set (Graph.digraph_abs (parents (BFS_upd1 bfs_state))) (t_set srcs) v'
         \<le> ?dTv'" (is "?dT'v' \<le> _ ")
      using \<open>invar_1 bfs_state\<close> \<open>invar_2 bfs_state\<close>
      by (auto simp: BFS_upd1_def Let_def
          elim!: invar_1_props invar_2_props intro!: distance_set_subset)
    ultimately have "?dT'v' \<le> ?dGv'"
      by auto
    moreover have "v \<in> t_set (current (BFS_upd1 bfs_state))"
      using 1 \<open>v \<notin> t_set (visited bfs_state)\<close>
      by (auto si mp: BFS_upd1_def Let_def)
    hence "?dGv = ?dGv' + 1"
      using 1
      by (auto intro!: dist_current_plus_1)
    moreover have "?dT'v = ?dT'v' + 1"
    proof-
      have False if "?dT'v > ?dT'v' + 1"
        using distance_set_1[OF v'(3)] that

        
        by (metis add_0_left distance_set_ge_1E' distance_set_subset eSuc_plus_1 emptyE empty_subsetI ileI1 neighbourhoodI not_iless0 order_le_imp_less_or_eq zero_order(1))
        by (simp add: leD)
      moreover have False if "?dT'v < ?dT'v' + 1"
      proof-
        have "?dT'v \<le> ?dT'v'"
          using that eSuc_plus_1 ileI1
          by force
        moreover have "v \<notin> t_set (visited bfs_state)"
          using \<open>v \<notin> t_set (visited bfs_state)\<close>
          .

        ultimately show False
          using \<open>invar_3_4 bfs_state\<close> \<open>v' \<in> t_set (current bfs_state)\<close>
          apply(auto elim!: invar_3_4_props)
          sorry
      qed
      ultimately show ?thesis
        by force
    qed
    ultimately show ?thesis
      by auto
  qed

  oops


*)

                                                               
end
