theory DFS_Cycles
  imports DFS_Cycles_Aux
begin


lemma list_decomp:
  "x \<noteq> y \<Longrightarrow> x \<in> set l \<Longrightarrow> y \<in> set l \<Longrightarrow>
    (\<exists>xs ys zs. l = (xs @ [x] @ ys @ [y] @ zs)) \<or>
    (\<exists>xs ys zs. l = (xs @ [y] @ ys @ [x] @ zs))"
proof-
  assume "x \<noteq> y" "x \<in> set l" "y \<in> set l"

  then have "\<exists>i. i < length l \<and> l ! i = x" "\<exists>j. j < length l \<and> l ! j = y" 
    by (auto simp add: in_set_conv_nth)
  then obtain i j where
    "i < length l" "l ! i = x" "j < length l" "l ! j = y" by blast
  with \<open>x \<noteq> y\<close> have "i \<noteq> j" by blast
  
  then consider (1) "i < j" | (2) "j < i" by linarith
  then show ?thesis
  proof (cases)
    case 1
    from \<open>i < length l\<close> \<open>l ! i = x\<close>
      have "l = (take i l) @ [x] @ (drop (i + 1) l)"
      by (metis Suc_eq_plus1 append.assoc append_take_drop_id hd_drop_conv_nth take_hd_drop)

    have "j \<ge> i + 1" using \<open>i < j\<close> by auto
    with \<open>j < length l\<close> have "y \<in> set (drop (i + 1) l)"
      using \<open>l ! j = y\<close>
      by (metis Cons_nth_drop_Suc list.set_intros(1) set_drop_subset_set_drop subsetD)
    from \<open>l ! j = y\<close>
      have "\<exists>xs ys. (drop (i + 1) l) = xs @ [y] @ ys"
      by (metis \<open>y \<in> set (drop (i + 1) l)\<close> append_Cons append_Nil in_set_conv_decomp_last)
    then obtain xs ys where "(drop (i + 1) l) = xs @ [y] @ ys" by blast
    
    with \<open>l = (take i l) @ [x] @ (drop (i + 1) l)\<close>
      show ?thesis by auto
  next
    case 2
    from \<open>j < length l\<close> \<open>l ! j = y\<close>
      have "l = (take j l) @ [y] @ (drop (j + 1) l)"
      by (metis Suc_eq_plus1 append.assoc append_take_drop_id hd_drop_conv_nth take_hd_drop)

    have "i \<ge> j + 1" using \<open>j < i\<close> by auto
    with \<open>i < length l\<close> have "x \<in> set (drop (j + 1) l)"
      using \<open>l ! i = x\<close>
      by (metis Cons_nth_drop_Suc list.set_intros(1) set_drop_subset_set_drop subsetD)
    from \<open>l ! i = x\<close>
      have "\<exists>xs ys. (drop (j + 1) l) = xs @ [x] @ ys"
      by (metis \<open>x \<in> set (drop (j + 1) l)\<close> append_Cons append_Nil in_set_conv_decomp_last)
    then obtain xs ys where "(drop (j + 1) l) = xs @ [x] @ ys" by blast

    with \<open>l = (take j l) @ [y] @ (drop (j + 1) l)\<close>
      show ?thesis by auto
  qed
qed





record ('ver, 'neighb) DFS_Cycles_state = seen:: "'neighb" cycle:: bool


named_theorems call_cond_elims
named_theorems call_cond_intros
named_theorems ret_holds_intros
named_theorems invar_props_intros
named_theorems invar_props_elims
named_theorems invar_holds_intros
named_theorems state_rel_intros
named_theorems state_rel_holds_intros 

locale DFS_Cycles =
  Graph: Pair_Graph_Specs
    where lookup = lookup +
 set_ops: Set2 vset_empty vset_delete _ t_set vset_inv insert

for lookup :: "'adj \<Rightarrow> 'v \<Rightarrow> 'neighb option" +

fixes G::"'adj" and V::"'neighb"
  and dfs_aux::"'v \<Rightarrow> 'state" and seen_aux::"'state \<Rightarrow> 'neighb" and cycle_aux::"'state \<Rightarrow> bool"
begin


definition "DFS_Cycles_axioms \<equiv>
  Graph.graph_inv G \<and> Graph.finite_graph G \<and> Graph.finite_vsets \<and>
  vset_inv V \<and> (t_set V = dVs (Graph.digraph_abs G)) \<and>
  (\<forall>(x, y) \<in> (Graph.digraph_abs G). (y, x) \<in> Graph.digraph_abs G) \<and>
  (\<forall>x \<in> dVs (Graph.digraph_abs G). (x, x) \<notin> Graph.digraph_abs G)"


definition "dfs_aux_axioms \<equiv>
  (\<forall>s \<in> dVs (Graph.digraph_abs G). vset_inv (seen_aux (dfs_aux s))) \<and>
  (\<forall>s \<in> dVs (Graph.digraph_abs G). s \<in>  t_set (seen_aux (dfs_aux s))) \<and>
  (\<forall>s \<in> dVs (Graph.digraph_abs G). \<not>cycle_aux (dfs_aux s) \<longrightarrow>
    (\<nexists>c. cycle' ((Graph.digraph_abs G) \<downharpoonright> (t_set (seen_aux (dfs_aux s)))) c)) \<and>
  (\<forall>s \<in> dVs (Graph.digraph_abs G). cycle_aux (dfs_aux s) \<longrightarrow>
    (\<exists>c. cycle' (Graph.digraph_abs G) c)) \<and>
  (\<forall>s \<in> dVs (Graph.digraph_abs G). \<forall>v \<in> t_set (seen_aux (dfs_aux s)).
    (\<exists>p. awalk (Graph.digraph_abs G) s p v)) \<and>
  (\<forall>s \<in> dVs (Graph.digraph_abs G). \<not>cycle_aux (dfs_aux s) \<longrightarrow> (\<forall>v \<in> t_set (seen_aux (dfs_aux s)). (\<forall>w \<in> dVs (Graph.digraph_abs G) - t_set (seen_aux (dfs_aux s)).
    (\<nexists>p. awalk (Graph.digraph_abs G) v p w))))"


abbreviation "neighbourhood' \<equiv> Graph.neighbourhood G"

notation "neighbourhood'" ("\<N>\<^sub>G _" 100)


function (domintros) DFS_Cycles::"('v, 'neighb) DFS_Cycles_state \<Rightarrow> ('v, 'neighb) DFS_Cycles_state" where
  "DFS_Cycles dfs_cycles_state = 
    (if V -\<^sub>G (seen dfs_cycles_state) \<noteq> \<emptyset>\<^sub>N
    then 
    (let
      s = sel (V -\<^sub>G (seen dfs_cycles_state));
      dfs_aux_state = dfs_aux s;
      cycle' = cycle_aux dfs_aux_state;
      seen' = seen_aux dfs_aux_state
    in
      (if cycle'
      then dfs_cycles_state \<lparr>cycle := True\<rparr>
      else DFS_Cycles (dfs_cycles_state \<lparr>seen := seen dfs_cycles_state \<union>\<^sub>G seen'\<rparr>)))
    else
      dfs_cycles_state)"
  by pat_completeness auto

partial_function (tailrec) DFS_Cycles_impl::"('v, 'neighb) DFS_Cycles_state \<Rightarrow> ('v, 'neighb) DFS_Cycles_state" where
  "DFS_Cycles_impl dfs_cycles_state = 
    (if V -\<^sub>G (seen dfs_cycles_state) \<noteq> \<emptyset>\<^sub>N
    then 
    (let
      s = sel (V -\<^sub>G (seen dfs_cycles_state));
      dfs_aux_state = dfs_aux s;
      cycle' = cycle_aux dfs_aux_state;
      seen' = seen_aux dfs_aux_state
    in
      (if cycle'
      then dfs_cycles_state \<lparr>cycle := True\<rparr>
      else DFS_Cycles_impl (dfs_cycles_state \<lparr>seen := seen dfs_cycles_state \<union>\<^sub>G seen'\<rparr>)))
    else
      dfs_cycles_state)"

lemmas [code] = DFS_Cycles_impl.simps

lemma DFS_Cycles_impl_same: 
  assumes "DFS_Cycles_dom state"
  shows "DFS_Cycles_impl state = DFS_Cycles state"
  by(induction rule: DFS_Cycles.pinduct[OF assms])
    (subst DFS_Cycles.psimps, simp, subst DFS_Cycles_impl.simps, auto split: if_split simp add: Let_def)

definition "DFS_Cycles_call_1_conds dfs_cycles_state = 
    (if V -\<^sub>G (seen dfs_cycles_state) \<noteq> \<emptyset>\<^sub>N
    then 
    (let
      s = sel (V -\<^sub>G (seen dfs_cycles_state));
      dfs_aux_state = dfs_aux s;
      cycle' = cycle_aux dfs_aux_state
    in
      (if cycle'
      then False
      else True))
    else
      False)"

lemma DFS_Cycles_call_1_conds[call_cond_elims]:
  "DFS_Cycles_call_1_conds dfs_cycles_state \<Longrightarrow> 
   \<lbrakk>\<lbrakk>V -\<^sub>G (seen dfs_cycles_state) \<noteq> \<emptyset>\<^sub>N; \<not>cycle_aux (dfs_aux (sel (V -\<^sub>G (seen dfs_cycles_state))))\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> 
   P"
  by(auto simp: DFS_Cycles_call_1_conds_def split: if_splits)

definition "DFS_Cycles_upd1 dfs_cycles_state = 
    (let
      s = sel (V -\<^sub>G (seen dfs_cycles_state));
      dfs_aux_state = dfs_aux s;
      seen' = seen_aux dfs_aux_state
    in
      (dfs_cycles_state \<lparr>seen := seen dfs_cycles_state \<union>\<^sub>G seen'\<rparr>))"

definition "DFS_Cycles_ret_1_conds dfs_cycles_state = 
    (if V -\<^sub>G (seen dfs_cycles_state) \<noteq> \<emptyset>\<^sub>N
    then 
    (let
      s = sel (V -\<^sub>G (seen dfs_cycles_state));
      dfs_aux_state = dfs_aux s;
      cycle' = cycle_aux dfs_aux_state
    in
      (if cycle'
      then True
      else False))
    else
      False)"

lemma DFS_Cycles_ret_1_conds[call_cond_elims]:
  "DFS_Cycles_ret_1_conds dfs_cycles_state \<Longrightarrow> 
   \<lbrakk>\<lbrakk>V -\<^sub>G (seen dfs_cycles_state) \<noteq> \<emptyset>\<^sub>N; cycle_aux (dfs_aux (sel (V -\<^sub>G (seen dfs_cycles_state))))\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> 
   P"
  by(auto simp: DFS_Cycles_ret_1_conds_def split: if_splits)

lemma DFS_Cycles_ret_1_condsI[call_cond_intros]:
  "\<lbrakk>V -\<^sub>G (seen dfs_cycles_state) \<noteq> \<emptyset>\<^sub>N; cycle_aux (dfs_aux (sel (V -\<^sub>G (seen dfs_cycles_state))))\<rbrakk> \<Longrightarrow> 
    DFS_Cycles_ret_1_conds dfs_cycles_state"
  by(auto simp: DFS_Cycles_ret_1_conds_def split: if_splits)

definition "DFS_Cycles_ret1 dfs_cycles_state = (dfs_cycles_state \<lparr>cycle := True\<rparr>)"


definition "DFS_Cycles_ret_2_conds dfs_cycles_state = 
    (if V -\<^sub>G (seen dfs_cycles_state) \<noteq> \<emptyset>\<^sub>N
    then 
      False
    else
      True)"

lemma DFS_Cycles_ret_2_conds[call_cond_elims]:
  "DFS_Cycles_ret_2_conds dfs_cycles_state \<Longrightarrow> 
   \<lbrakk>\<lbrakk>V -\<^sub>G (seen dfs_cycles_state) = \<emptyset>\<^sub>N\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> 
   P"
  by(auto simp: DFS_Cycles_ret_2_conds_def split: if_splits)

lemma DFS_Cycles_ret_2_condsI[call_cond_intros]:
  "\<lbrakk>V -\<^sub>G (seen dfs_cycles_state) = \<emptyset>\<^sub>N\<rbrakk> \<Longrightarrow> DFS_Cycles_ret_2_conds dfs_cycles_state"
  by(auto simp: DFS_Cycles_ret_2_conds_def split: if_splits)

definition "DFS_Cycles_ret2 dfs_cycles_state = (dfs_cycles_state)"


lemma DFS_Cycles_cases:
  assumes "DFS_Cycles_call_1_conds dfs_cycles_state \<Longrightarrow> P"
      "DFS_Cycles_ret_1_conds dfs_cycles_state \<Longrightarrow> P"
      "DFS_Cycles_ret_2_conds dfs_cycles_state \<Longrightarrow> P"
  shows "P"
proof-
  have "DFS_Cycles_call_1_conds dfs_cycles_state \<or> 
        DFS_Cycles_ret_1_conds dfs_cycles_state \<or> DFS_Cycles_ret_2_conds dfs_cycles_state"
    by (auto simp add: DFS_Cycles_call_1_conds_def 
                        DFS_Cycles_ret_1_conds_def DFS_Cycles_ret_2_conds_def
           split: list.split_asm option.split_asm if_splits)
  then show ?thesis
    using assms
    by auto
qed


lemma DFS_Cycles_simps:
  assumes "DFS_Cycles_dom dfs_cycles_state" 
  shows"DFS_Cycles_call_1_conds dfs_cycles_state \<Longrightarrow> DFS_Cycles dfs_cycles_state = DFS_Cycles (DFS_Cycles_upd1 dfs_cycles_state)"
      "DFS_Cycles_ret_1_conds dfs_cycles_state \<Longrightarrow> DFS_Cycles dfs_cycles_state = DFS_Cycles_ret1 dfs_cycles_state"
      "DFS_Cycles_ret_2_conds dfs_cycles_state \<Longrightarrow> DFS_Cycles dfs_cycles_state = DFS_Cycles_ret2 dfs_cycles_state"
  by (auto simp add: DFS_Cycles.psimps[OF assms] Let_def
                       DFS_Cycles_call_1_conds_def DFS_Cycles_upd1_def
                       DFS_Cycles_ret_1_conds_def DFS_Cycles_ret1_def
                       DFS_Cycles_ret_2_conds_def DFS_Cycles_ret2_def
            split: list.splits option.splits if_splits )

lemma DFS_Cycles_induct: 
  assumes "DFS_Cycles_dom dfs_cycles_state"
  assumes "\<And>dfs_cycles_state. \<lbrakk>DFS_Cycles_dom dfs_cycles_state;
     DFS_Cycles_call_1_conds dfs_cycles_state \<Longrightarrow> P (DFS_Cycles_upd1 dfs_cycles_state)\<rbrakk> \<Longrightarrow> P dfs_cycles_state"
  shows "P dfs_cycles_state"
  apply(rule DFS_Cycles.pinduct[OF assms(1)])
  apply(rule assms(2)[simplified DFS_Cycles_call_1_conds_def DFS_Cycles_upd1_def])
  by (auto simp: Let_def split: list.splits option.splits if_splits)

lemma DFS_Cycles_domintros: 
  assumes "DFS_Cycles_call_1_conds dfs_cycles_state \<Longrightarrow> DFS_Cycles_dom (DFS_Cycles_upd1 dfs_cycles_state)"
  shows "DFS_Cycles_dom dfs_cycles_state"
proof(rule DFS_Cycles.domintros, goal_cases)
  case (1 xb)
  then show ?case
    using assms(1)[simplified DFS_Cycles_call_1_conds_def DFS_Cycles_upd1_def]
    by (force simp: Let_def split: list.splits option.splits if_splits)
qed


definition "call_measure dfs_cycles_state \<equiv> card (t_set (V -\<^sub>G seen dfs_cycles_state))"

definition "DFS_Cycles_term_rel' \<equiv> call_measure <*mlex*> {}"

definition "initial_state \<equiv> \<lparr>seen = \<emptyset>\<^sub>N, cycle = False\<rparr>"

lemmas [code] = initial_state_def

definition "invar_1 dfs_cycles_state \<equiv> vset_inv (seen dfs_cycles_state)"

definition "invar_seen dfs_cycles_state \<equiv>
  \<forall>v \<in> t_set (seen dfs_cycles_state). \<forall>w \<in> t_set (V -\<^sub>G (seen dfs_cycles_state)).
    ((\<nexists>p. awalk (Graph.digraph_abs G) v p w) \<and> (\<nexists>p. awalk (Graph.digraph_abs G) w p v))" 

definition "invar_seen_subset_V dfs_cycles_state \<equiv>
  t_set (seen dfs_cycles_state) \<subseteq> t_set V"          

definition "invar_cycle_false dfs_cycles_state \<equiv>
  \<not>cycle dfs_cycles_state \<longrightarrow> (\<nexists>c. cycle' ((Graph.digraph_abs G) \<downharpoonright> (t_set (seen dfs_cycles_state))) c)"

definition "invar_cycle_true dfs_cycles_state \<equiv>
  cycle dfs_cycles_state \<longrightarrow> (\<exists>c. cycle' (Graph.digraph_abs G) c)"


context
includes Graph.adj.automation Graph.vset.set.automation
assumes DFS_Cycles_axioms dfs_aux_axioms
begin

declare set_ops.set_union[simp] set_ops.set_inter[simp] 
        set_ops.set_diff[simp] set_ops.invar_union[simp]
        set_ops.invar_inter[simp] set_ops.invar_diff[simp]

lemma graph_inv[simp,intro]:
          "Graph.graph_inv G"
          "Graph.finite_graph G"
          "Graph.finite_vsets"
  using \<open>DFS_Cycles_axioms\<close>
  by (auto simp: DFS_Cycles_axioms_def)

lemma finite_neighbourhoods[simp]:                                                 
          "finite (t_set N)"
  using graph_inv(3)
  by fastforce

lemma V_inv[simp, intro]:
  "vset_inv V"
  using \<open>DFS_Cycles_axioms\<close>
  by (auto simp: DFS_Cycles_axioms_def)

lemma V_graph_verts:
  "t_set V = dVs (Graph.digraph_abs G)"
  using \<open>DFS_Cycles_axioms\<close>
  by (auto simp: DFS_Cycles_axioms_def)

lemma graph_symmetric[simp]:
  "(x, y) \<in> (Graph.digraph_abs G) \<Longrightarrow> (y, x) \<in> (Graph.digraph_abs G)"
  using \<open>DFS_Cycles_axioms\<close>
  by (auto simp: DFS_Cycles_axioms_def)

lemma graph_no_self_loops1[simp]:
  "x \<in> dVs (Graph.digraph_abs G) \<Longrightarrow> (x, x) \<notin> Graph.digraph_abs G"
  using \<open>DFS_Cycles_axioms\<close>
  by (auto simp: DFS_Cycles_axioms_def)

lemma graph_no_self_loops2[simp]:
  "(x, y) \<in> (Graph.digraph_abs G) \<Longrightarrow> x \<noteq> y"
  using graph_no_self_loops1 by blast

lemma dfs_aux_seen_inv[simp]:
  "s \<in> dVs (Graph.digraph_abs G) \<Longrightarrow> vset_inv (seen_aux (dfs_aux s))"
  using \<open>dfs_aux_axioms\<close>
  by (auto simp: dfs_aux_axioms_def)

lemma dfs_aux_s_in_seen[simp]:
  "s \<in> dVs (Graph.digraph_abs G) \<Longrightarrow> s \<in> t_set (seen_aux (dfs_aux s))"
  using \<open>dfs_aux_axioms\<close>
  by (auto simp: dfs_aux_axioms_def)

lemma dfs_aux_cycle_false[simp]:
  "s \<in> dVs (Graph.digraph_abs G) \<Longrightarrow> \<not>cycle_aux (dfs_aux s) \<Longrightarrow> (\<nexists>c. cycle' ((Graph.digraph_abs G) \<downharpoonright> (t_set (seen_aux (dfs_aux s)))) c)"
  using \<open>dfs_aux_axioms\<close>
  by (auto simp: dfs_aux_axioms_def)

lemma dfs_aux_cycle_true[simp]:
  "s \<in> dVs (Graph.digraph_abs G) \<Longrightarrow> cycle_aux (dfs_aux s) \<Longrightarrow> (\<exists>c. cycle' (Graph.digraph_abs G) c)"
  using \<open>dfs_aux_axioms\<close>
  by (auto simp: dfs_aux_axioms_def)

lemma dfs_aux_seen[simp]:
  "s \<in> dVs (Graph.digraph_abs G) \<Longrightarrow> v \<in> t_set (seen_aux (dfs_aux s)) \<Longrightarrow>
  (\<exists>p. awalk (Graph.digraph_abs G) s p v)"
  using \<open>dfs_aux_axioms\<close>
  by (auto simp: dfs_aux_axioms_def)

lemma dfs_aux_reachable[simp]:
  "s \<in> dVs (Graph.digraph_abs G) \<Longrightarrow> \<not>cycle_aux (dfs_aux s) \<Longrightarrow> v \<in> t_set (seen_aux (dfs_aux s)) \<Longrightarrow> w \<in> dVs (Graph.digraph_abs G) - t_set (seen_aux (dfs_aux s)) \<Longrightarrow>
    (\<nexists>p. awalk (Graph.digraph_abs G) v p w)"
  using \<open>dfs_aux_axioms\<close>
  by (auto simp: dfs_aux_axioms_def)

lemmas simps[simp] = Graph.neighbourhood_abs[OF graph_inv(1)] Graph.are_connected_abs[OF graph_inv(1)]

lemma invar_1_props[invar_props_elims]:
  "invar_1 dfs_cycles_state \<Longrightarrow>
     (\<lbrakk>vset_inv (seen dfs_cycles_state)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
     P"
  by (auto simp: invar_1_def)

lemma invar_1_intro[invar_props_intros]:
  "\<lbrakk>vset_inv (seen dfs_cycles_state)\<rbrakk> \<Longrightarrow> invar_1 dfs_cycles_state"
  by (auto simp: invar_1_def)

lemma invar_1_holds_upd1[invar_holds_intros]:
  "\<lbrakk>DFS_Cycles_call_1_conds dfs_cycles_state; invar_1 dfs_cycles_state\<rbrakk> \<Longrightarrow> invar_1 (DFS_Cycles_upd1 dfs_cycles_state)"
proof (intro invar_props_intros, goal_cases)
  case 1
  let ?s = "sel (V -\<^sub>G (seen dfs_cycles_state))"

  have "?s \<in> dVs (Graph.digraph_abs G)"
    using \<open>invar_1 dfs_cycles_state\<close> \<open>DFS_Cycles_call_1_conds dfs_cycles_state\<close>
    by (auto simp add: V_graph_verts elim!: invar_props_elims call_cond_elims) 

  with dfs_aux_seen_inv[OF this] show ?case
    using \<open>invar_1 dfs_cycles_state\<close>
    by (auto simp add: Let_def DFS_Cycles_upd1_def elim!: invar_props_elims)
qed

lemma invar_1_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>DFS_Cycles_ret_1_conds dfs_cycles_state; invar_1 dfs_cycles_state\<rbrakk> \<Longrightarrow> invar_1 (DFS_Cycles_ret1 dfs_cycles_state)"
  by (auto simp: DFS_Cycles_ret1_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_1_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>DFS_Cycles_ret_2_conds dfs_cycles_state; invar_1 dfs_cycles_state\<rbrakk> \<Longrightarrow> invar_1 (DFS_Cycles_ret2 dfs_cycles_state)"
  by (auto simp: DFS_Cycles_ret2_def elim!: invar_props_elims intro: invar_props_intros)

lemma invar_1_holds[invar_holds_intros]: 
   assumes "DFS_Cycles_dom dfs_cycles_state" "invar_1 dfs_cycles_state"
   shows "invar_1 (DFS_Cycles dfs_cycles_state)"
  using assms(2)
proof(induction rule: DFS_Cycles_induct[OF assms(1)])
  case IH: (1 dfs_cycles_state)
  show ?case
    apply(rule DFS_Cycles_cases[where dfs_cycles_state = dfs_cycles_state])
    by (auto intro!: IH(2-3) invar_holds_intros simp: DFS_Cycles_simps[OF IH(1)])
qed

lemma invar_seen_props[invar_props_elims]:
  "invar_seen dfs_cycles_state \<Longrightarrow>
     (\<lbrakk>\<And>v w. \<lbrakk>v \<in> t_set (seen dfs_cycles_state); w \<in> t_set (V -\<^sub>G (seen dfs_cycles_state))\<rbrakk> \<Longrightarrow>
    ((\<nexists>p. awalk (Graph.digraph_abs G) v p w) \<and> (\<nexists>p. awalk (Graph.digraph_abs G) w p v))\<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
     P"
  by (auto simp: invar_seen_def)

lemma invar_seen_intro[invar_props_intros]:
  "\<lbrakk>\<And>v w. \<lbrakk>v \<in> t_set (seen dfs_cycles_state); w \<in> t_set (V -\<^sub>G (seen dfs_cycles_state))\<rbrakk> \<Longrightarrow>
    ((\<nexists>p. awalk (Graph.digraph_abs G) v p w) \<and> (\<nexists>p. awalk (Graph.digraph_abs G) w p v))\<rbrakk> \<Longrightarrow>
     invar_seen dfs_cycles_state"
  by (auto simp: invar_seen_def)

lemma invar_seen_holds_upd1[invar_holds_intros]:
  "\<lbrakk>DFS_Cycles_call_1_conds dfs_cycles_state; invar_1 dfs_cycles_state; invar_seen dfs_cycles_state\<rbrakk> \<Longrightarrow>
    invar_seen (DFS_Cycles_upd1 dfs_cycles_state)"
proof (intro invar_props_intros, goal_cases)
  case (1 v w)

  let ?s = "sel (V -\<^sub>G (seen dfs_cycles_state))"
  let ?seen' = "t_set (seen_aux (dfs_aux ?s))"

  have "\<not>cycle_aux (dfs_aux ?s)"
    using \<open>DFS_Cycles_call_1_conds dfs_cycles_state\<close>
    by (force elim!: call_cond_elims)

  have "((Graph.digraph_abs G) \<downharpoonright> ?seen') \<subseteq> (Graph.digraph_abs G)"
    unfolding induce_subgraph_def by auto

  have "?s \<in> dVs (Graph.digraph_abs G)"
    using \<open>invar_1 dfs_cycles_state\<close> \<open>DFS_Cycles_call_1_conds dfs_cycles_state\<close>
    by (auto simp add: V_graph_verts elim!: invar_props_elims call_cond_elims) 

  have seen_expr: "t_set (seen (DFS_Cycles_upd1 dfs_cycles_state)) = 
    (t_set (seen dfs_cycles_state)) \<union> ?seen'"
    using \<open>invar_1 dfs_cycles_state\<close> \<open>?s \<in> dVs (Graph.digraph_abs G)\<close> dfs_aux_seen_inv
    by (force simp add: DFS_Cycles_upd1_def elim!: invar_props_elims)

  from invar_1_holds_upd1[OF 1(1-2)] seen_expr
    have comp_subset: "t_set (V -\<^sub>G (seen (DFS_Cycles_upd1 dfs_cycles_state))) \<subseteq> t_set (V -\<^sub>G (seen dfs_cycles_state))"
    using \<open>invar_1 dfs_cycles_state\<close>
    by (force elim!: invar_props_elims)

  from 1 seen_expr consider (a) "v \<in> t_set (seen dfs_cycles_state)" | (b) "v \<in> ?seen'" by blast
  then show ?case
  proof (cases)
    case a
    with comp_subset 1(5) show ?thesis
      using \<open>invar_seen dfs_cycles_state\<close>
      by (auto elim!: invar_props_elims)
  next
    case b
    
    with \<open>?s \<in> dVs (Graph.digraph_abs G)\<close> dfs_aux_seen
      obtain p where "awalk (Graph.digraph_abs G) ?s p v" by blast

    with 1(5) have "w \<in> dVs (Graph.digraph_abs G) - ?seen'"
      using \<open>invar_1 dfs_cycles_state\<close> \<open>?s \<in> dVs (Graph.digraph_abs G)\<close> dfs_aux_seen_inv
      by (fastforce simp add: DFS_Cycles_upd1_def Let_def V_graph_verts elim: invar_props_elims)
    with dfs_aux_reachable[OF \<open>?s \<in> dVs (Graph.digraph_abs G)\<close> \<open>\<not>cycle_aux (dfs_aux ?s)\<close> b this]
      have no_path_to_w: "\<nexists>p. awalk (Graph.digraph_abs G) v p w"
      by blast

    have "\<forall>e \<in> (Graph.digraph_abs G). prod.swap e \<in> (Graph.digraph_abs G)" by auto
    with awalk_rev no_path_to_w
      have "\<nexists>p. awalk (Graph.digraph_abs G) w p v" by metis

    with no_path_to_w show ?thesis by blast
  qed
qed

lemma invar_seen_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>DFS_Cycles_ret_1_conds dfs_cycles_state; invar_seen dfs_cycles_state\<rbrakk> \<Longrightarrow>
    invar_seen (DFS_Cycles_ret1 dfs_cycles_state)"
proof (intro invar_props_intros, goal_cases)
  case (1 v w)
  from 1 have "v \<in> t_set (DFS_Cycles_state.seen dfs_cycles_state)"
    by (auto simp add: DFS_Cycles_ret1_def)
  moreover have "w \<in> t_set (V -\<^sub>G DFS_Cycles_state.seen dfs_cycles_state)"
    using 1 by (auto simp add: DFS_Cycles_ret1_def)
  ultimately show ?case
    using \<open>invar_seen dfs_cycles_state\<close>
    by (force elim!: invar_props_elims)
qed

lemma invar_seen_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>DFS_Cycles_ret_2_conds dfs_cycles_state; invar_seen dfs_cycles_state\<rbrakk> \<Longrightarrow>
    invar_seen (DFS_Cycles_ret2 dfs_cycles_state)"
proof (intro invar_props_intros, goal_cases)
  case (1 v w)
  from 1 have "v \<in> t_set (DFS_Cycles_state.seen dfs_cycles_state)"
    by (auto simp add: DFS_Cycles_ret2_def)
  moreover have "w \<in> t_set (V -\<^sub>G DFS_Cycles_state.seen dfs_cycles_state)"
    using 1 by (auto simp add: DFS_Cycles_ret2_def)
  ultimately show ?case
    using \<open>invar_seen dfs_cycles_state\<close>
    by (force elim!: invar_props_elims)
qed

lemma invar_seen_holds[invar_holds_intros]: 
   assumes "DFS_Cycles_dom dfs_cycles_state" "invar_1 dfs_cycles_state" "invar_seen dfs_cycles_state"
   shows "invar_seen (DFS_Cycles dfs_cycles_state)"
  using assms(2-)
proof(induction rule: DFS_Cycles_induct[OF assms(1)])
  case IH: (1 dfs_cycles_state)
  show ?case
    apply(rule DFS_Cycles_cases[where dfs_cycles_state = dfs_cycles_state])
    by (auto intro!: IH(2-4) invar_holds_intros simp: DFS_Cycles_simps[OF IH(1)])
qed

lemma invar_seen_subset_V_props[invar_props_elims]:
  "invar_seen_subset_V dfs_cycles_state \<Longrightarrow>
     (\<lbrakk>t_set (seen dfs_cycles_state) \<subseteq> t_set V\<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
     P"
  by (auto simp: invar_seen_subset_V_def)

lemma invar_seen_subset_V_intro[invar_props_intros]:
  "\<lbrakk>t_set (seen dfs_cycles_state) \<subseteq> t_set V\<rbrakk> \<Longrightarrow> invar_seen_subset_V dfs_cycles_state"
  by (auto simp: invar_seen_subset_V_def)

lemma invar_seen_subset_V_holds_upd1[invar_holds_intros]:
  "\<lbrakk>DFS_Cycles_call_1_conds dfs_cycles_state; invar_1 dfs_cycles_state; invar_seen dfs_cycles_state;
     invar_seen_subset_V dfs_cycles_state\<rbrakk> \<Longrightarrow> invar_seen_subset_V (DFS_Cycles_upd1 dfs_cycles_state)"
proof (intro invar_props_intros, goal_cases)
  case 1

  let ?s = "sel (V -\<^sub>G (seen dfs_cycles_state))"
  let ?seen' = "t_set (seen_aux (dfs_aux ?s))"

  have "?s \<in> dVs (Graph.digraph_abs G)"
    using \<open>invar_1 dfs_cycles_state\<close> \<open>DFS_Cycles_call_1_conds dfs_cycles_state\<close>
    by (auto simp add: V_graph_verts elim!: invar_props_elims call_cond_elims) 

  have seen_expr: "t_set (seen (DFS_Cycles_upd1 dfs_cycles_state)) = 
    (t_set (seen dfs_cycles_state)) \<union> ?seen'"
    using \<open>invar_1 dfs_cycles_state\<close> \<open>?s \<in> dVs (Graph.digraph_abs G)\<close> dfs_aux_seen_inv
    by (force simp add: DFS_Cycles_upd1_def elim!: invar_props_elims)

  have "?s \<in> t_set (V -\<^sub>G seen dfs_cycles_state)"
    using \<open>invar_1 dfs_cycles_state\<close> \<open>DFS_Cycles_call_1_conds dfs_cycles_state\<close>
    by (auto elim!: invar_props_elims call_cond_elims) 
  have "?seen' \<subseteq> t_set (V -\<^sub>G (seen dfs_cycles_state))"
  proof
    fix v
    assume "v \<in> ?seen'"
    with \<open>?s \<in> dVs (Graph.digraph_abs G)\<close> dfs_aux_seen
      obtain p where "awalk (Graph.digraph_abs G) ?s p v" by blast
    show "v \<in> t_set (V -\<^sub>G (seen dfs_cycles_state))"
    proof (rule ccontr, goal_cases)
      case 1
      from V_graph_verts
        have "v \<in> t_set V"
        using \<open>awalk [G]\<^sub>g (sel (V -\<^sub>G DFS_Cycles_state.seen dfs_cycles_state)) p v\<close> by auto
      with 1 have "v \<in> (t_set (seen dfs_cycles_state))"
        using \<open>invar_1 dfs_cycles_state\<close>
        by (auto elim!: invar_props_elims)
      with \<open>?s \<in> t_set (V -\<^sub>G seen dfs_cycles_state)\<close> \<open>awalk (Graph.digraph_abs G) ?s p v\<close>
        show ?case using \<open>invar_seen dfs_cycles_state\<close>
        by (fastforce elim!: invar_props_elims)
    qed
  qed
  then have "?seen' \<subseteq> t_set V"
    using \<open>invar_1 dfs_cycles_state\<close>
    by (auto elim!: invar_props_elims)

  with seen_expr show ?case 
    using \<open>invar_seen_subset_V dfs_cycles_state\<close>
    by (auto elim!: invar_props_elims)
qed

lemma invar_seen_subset_V_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>DFS_Cycles_ret_1_conds dfs_cycles_state; invar_seen_subset_V dfs_cycles_state\<rbrakk> \<Longrightarrow> 
    invar_seen_subset_V (DFS_Cycles_ret1 dfs_cycles_state)"
  by (auto simp: DFS_Cycles_ret1_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_seen_subset_V_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>DFS_Cycles_ret_2_conds dfs_cycles_state; invar_seen_subset_V dfs_cycles_state\<rbrakk> \<Longrightarrow> 
    invar_seen_subset_V (DFS_Cycles_ret2 dfs_cycles_state)"
  unfolding invar_seen_subset_V_def DFS_Cycles_ret2_def by simp

lemma invar_seen_subset_V_holds[invar_holds_intros]: 
   assumes "DFS_Cycles_dom dfs_cycles_state" "invar_1 dfs_cycles_state" "invar_seen dfs_cycles_state"
     "invar_seen_subset_V dfs_cycles_state"
   shows "invar_seen_subset_V (DFS_Cycles dfs_cycles_state)"
  using assms(2-)
proof(induction rule: DFS_Cycles_induct[OF assms(1)])
  case IH: (1 dfs_cycles_state)
  show ?case
    apply(rule DFS_Cycles_cases[where dfs_cycles_state = dfs_cycles_state])
    by (auto intro!: IH(2-5) invar_holds_intros simp: DFS_Cycles_simps[OF IH(1)])
qed



lemma invar_cycle_false_props[invar_props_elims]:
  "invar_cycle_false dfs_cycles_state \<Longrightarrow>
     (\<lbrakk>\<not>cycle dfs_cycles_state \<Longrightarrow> 
      (\<nexists>c. cycle' ((Graph.digraph_abs G) \<downharpoonright> (t_set (seen dfs_cycles_state))) c)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
     P"
  by (auto simp: invar_cycle_false_def)

lemma invar_cycle_false_intro[invar_props_intros]:
  "\<lbrakk>\<not>cycle dfs_cycles_state \<Longrightarrow> 
     (\<nexists>c. cycle' ((Graph.digraph_abs G) \<downharpoonright> (t_set (seen dfs_cycles_state))) c)\<rbrakk> \<Longrightarrow>
     invar_cycle_false dfs_cycles_state"
  by (auto simp: invar_cycle_false_def)

lemma invar_cycle_false_holds_upd1[invar_holds_intros]:
  "\<lbrakk>DFS_Cycles_call_1_conds dfs_cycles_state; invar_1 dfs_cycles_state; invar_seen dfs_cycles_state;
    invar_cycle_false dfs_cycles_state\<rbrakk> \<Longrightarrow> invar_cycle_false (DFS_Cycles_upd1 dfs_cycles_state)"
proof (intro invar_props_intros, goal_cases)
  case 1

  let ?s = "sel (V -\<^sub>G (seen dfs_cycles_state))"
  let ?seen' = "t_set (seen_aux (dfs_aux ?s))"

  have "?s \<in> dVs (Graph.digraph_abs G)"
    using \<open>invar_1 dfs_cycles_state\<close> \<open>DFS_Cycles_call_1_conds dfs_cycles_state\<close>
    by (auto simp add: V_graph_verts elim!: invar_props_elims call_cond_elims)

  have seen_expr: "t_set (seen (DFS_Cycles_upd1 dfs_cycles_state)) = 
    (t_set (seen dfs_cycles_state)) \<union> ?seen'"
    using \<open>invar_1 dfs_cycles_state\<close> \<open>?s \<in> dVs (Graph.digraph_abs G)\<close> dfs_aux_seen_inv
    by (force simp add: DFS_Cycles_upd1_def elim!: invar_props_elims)

  
  have "((Graph.digraph_abs G) \<downharpoonright> ?seen') \<subseteq> (Graph.digraph_abs G)"
    unfolding induce_subgraph_def by auto

  have "?s \<in> t_set (V -\<^sub>G seen dfs_cycles_state)"
    using \<open>invar_1 dfs_cycles_state\<close> \<open>DFS_Cycles_call_1_conds dfs_cycles_state\<close>
    by (auto elim!: invar_props_elims call_cond_elims) 
  have "?seen' \<subseteq> t_set (V -\<^sub>G (seen dfs_cycles_state))"
  proof
    fix v
    assume "v \<in> ?seen'"
    with \<open>?s \<in> dVs (Graph.digraph_abs G)\<close> dfs_aux_seen
      obtain p where "awalk (Graph.digraph_abs G) ?s p v" by blast
    show "v \<in> t_set (V -\<^sub>G (seen dfs_cycles_state))"
    proof (rule ccontr, goal_cases)
      case 1
      from V_graph_verts
        have "v \<in> t_set V"
        using \<open>awalk [G]\<^sub>g (sel (V -\<^sub>G DFS_Cycles_state.seen dfs_cycles_state)) p v\<close> by auto
      with 1 have "v \<in> (t_set (seen dfs_cycles_state))"
        using \<open>invar_1 dfs_cycles_state\<close>
        by (auto elim!: invar_props_elims)
      with \<open>?s \<in> t_set (V -\<^sub>G seen dfs_cycles_state)\<close> \<open>awalk (Graph.digraph_abs G) ?s p v\<close>
        show ?case using \<open>invar_seen dfs_cycles_state\<close>
        by (fastforce elim!: invar_props_elims)
    qed
  qed

  have "cycle (DFS_Cycles_upd1 dfs_cycles_state) = cycle dfs_cycles_state"
    by (auto simp add: DFS_Cycles_upd1_def Let_def)
  with \<open>\<not>cycle (DFS_Cycles_upd1 dfs_cycles_state)\<close>
    have "\<not>cycle dfs_cycles_state" by blast
  then have prev_seen_no_cycle: 
    "(\<nexists>c. cycle' ((Graph.digraph_abs G) \<downharpoonright> (t_set (seen dfs_cycles_state))) c)"
    using \<open>invar_cycle_false dfs_cycles_state\<close>
    by (force elim!: invar_props_elims)

  have seen'_no_cycle: "(\<nexists>c. cycle' ((Graph.digraph_abs G) \<downharpoonright> ?seen') c)"
    using \<open>DFS_Cycles_call_1_conds dfs_cycles_state\<close> \<open>?s \<in> dVs (Graph.digraph_abs G)\<close> dfs_aux_cycle_false
    by (fastforce elim!: call_cond_elims)

  show ?case
  proof (rule ccontr, goal_cases)
    case 1
    let ?G_seen_new = "((Graph.digraph_abs G) \<downharpoonright> (t_set (seen (DFS_Cycles_upd1 dfs_cycles_state))))"
    have "?G_seen_new \<subseteq> (Graph.digraph_abs G)"
      unfolding induce_subgraph_def by auto

    from 1 obtain c where
      new_seen_cycle: "cycle' ?G_seen_new c"
      by blast
    with cycle'_edges_subset
      have "set c \<subseteq> ?G_seen_new"
      by blast
    from cycle'_imp_awalk[OF new_seen_cycle]
      obtain u where c_awalk:
      "awalk ?G_seen_new u c u" by blast

    from cycle'_not_subset[OF new_seen_cycle] prev_seen_no_cycle
      obtain e1 where "e1 \<in> set c" "e1 \<notin> ((Graph.digraph_abs G) \<downharpoonright> (t_set (seen dfs_cycles_state)))"
      by blast
    with \<open>set c \<subseteq> ?G_seen_new\<close> have "e1 \<in> ?G_seen_new" by blast

    from cycle'_not_subset[OF new_seen_cycle] seen'_no_cycle
      obtain e2 where "e2 \<in> set c" "e2 \<notin> ((Graph.digraph_abs G) \<downharpoonright> ?seen')"
      by blast
    with \<open>set c \<subseteq> ?G_seen_new\<close> have "e2 \<in> ?G_seen_new" by blast

    from \<open>?seen' \<subseteq> t_set (V -\<^sub>G (seen dfs_cycles_state))\<close>
      have "\<And>v. v \<in> ?seen' \<Longrightarrow> v \<notin> t_set (seen dfs_cycles_state)"
      using \<open>invar_1 dfs_cycles_state\<close>
      by (force elim!: invar_props_elims)
    then have "t_set (seen dfs_cycles_state) \<inter> ?seen' = {}" by blast

    have "(\<And>v w. (v, w) \<in> Graph.digraph_abs G \<Longrightarrow> awalk (Graph.digraph_abs G) v [(v, w)] w)"
      unfolding awalk_def by auto
    with \<open>?seen' \<subseteq> t_set (V -\<^sub>G (seen dfs_cycles_state))\<close>
      have "\<forall>v \<in> t_set (seen dfs_cycles_state). \<forall>w \<in> ?seen'. (v, w) \<notin> (Graph.digraph_abs G) \<and>
      (w, v) \<notin> (Graph.digraph_abs G)"
      using \<open>invar_seen dfs_cycles_state\<close> 
      by (meson in_mono invar_seen_props)
    with seen_expr have G_seen_new_expr: "?G_seen_new =
      ((Graph.digraph_abs G) \<downharpoonright> (t_set (seen dfs_cycles_state))) \<union> ((Graph.digraph_abs G) \<downharpoonright> ?seen')"
      unfolding induce_subgraph_def
      by blast
    
    have graphs_disjoint:
      "((Graph.digraph_abs G) \<downharpoonright> (t_set (seen dfs_cycles_state))) \<inter> ((Graph.digraph_abs G) \<downharpoonright> ?seen') = {}"
      unfolding induce_subgraph_def using \<open>t_set (seen dfs_cycles_state) \<inter> ?seen' = {}\<close> by blast

    from \<open>e1 \<in> ?G_seen_new\<close> \<open>e1 \<notin> ((Graph.digraph_abs G) \<downharpoonright> (t_set (seen dfs_cycles_state)))\<close> G_seen_new_expr
      have e1_in: "e1 \<in> ((Graph.digraph_abs G) \<downharpoonright> ?seen')" by blast
    from \<open>e2 \<in> ?G_seen_new\<close> \<open>e2 \<notin> ((Graph.digraph_abs G) \<downharpoonright> ?seen')\<close> G_seen_new_expr
      have e2_in: "e2 \<in> ((Graph.digraph_abs G) \<downharpoonright> (t_set (seen dfs_cycles_state)))" by blast

    from e1_in e2_in graphs_disjoint
      have "e1 \<noteq> e2" by auto

    from \<open>e1 \<in> ((Graph.digraph_abs G) \<downharpoonright> ?seen')\<close> have "fst e1 \<in> ?seen'" "snd e1 \<in> ?seen'"
      unfolding induce_subgraph_def by auto
    with \<open>?seen' \<subseteq> t_set (V -\<^sub>G (seen dfs_cycles_state))\<close>
      have "fst e1 \<in> t_set (V -\<^sub>G (seen dfs_cycles_state))"
      by blast
    from \<open>snd e1 \<in> ?seen'\<close> \<open>?seen' \<subseteq> t_set (V -\<^sub>G (seen dfs_cycles_state))\<close> 
      have "snd e1 \<in> t_set (V -\<^sub>G (seen dfs_cycles_state))" by blast
    from \<open>e2 \<in> ((Graph.digraph_abs G) \<downharpoonright> (t_set (seen dfs_cycles_state)))\<close>
      have "fst e2 \<in> (t_set (seen dfs_cycles_state))" "snd e2 \<in> (t_set (seen dfs_cycles_state))"
      unfolding induce_subgraph_def by auto

    from list_decomp[OF \<open>e1 \<noteq> e2\<close> \<open>e1 \<in> set c\<close> \<open>e2 \<in> set c\<close>]
      consider (1) "\<exists>xs ys zs. c = xs @ [e1] @ ys @ [e2] @ zs" | 
               (2) "\<exists>xs ys zs. c = xs @ [e2] @ ys @ [e1] @ zs"
      by blast
    then show ?case
    proof (cases)
      case 1
      then obtain xs ys zs where "c = xs @ [e1] @ ys @ [e2] @ zs" by blast
      with c_awalk awalk_append_iff
        have "awalk ?G_seen_new u (xs @ [e1]) (awlast u (xs @ [e1]))"
        by (metis append.assoc)

      have "awlast u (xs @ [e1]) = snd e1"
        by (auto simp add: awalk_verts_conv)
      with \<open>c = xs @ [e1] @ ys @ [e2] @ zs\<close> c_awalk awalk_append_iff
        have "awalk ?G_seen_new (snd e1) (ys @ [e2] @ zs) (awlast (snd e1) (ys @ [e2] @ zs))"
        by (smt (verit, best) awalkE)
      with awalk_append_iff
        have "awalk ?G_seen_new (snd e1) ys (awlast (snd e1) ys)"
        "awalk ?G_seen_new (awlast (snd e1) ys) ([e2] @ zs) (awlast (snd e1) (ys @ [e2] @ zs))"
        by auto
      then have "(awlast (snd e1) ys) = awhd (awlast (snd e1) ys) ([e2] @ zs)"
        by auto
      then have "(awlast (snd e1) ys) = fst e2"
        by (simp add: awalk_verts_conv)
      with \<open>awalk ?G_seen_new (snd e1) ys (awlast (snd e1) ys)\<close>
        have "awalk ?G_seen_new (snd e1) ys (fst e2)" by simp
      with \<open>?G_seen_new \<subseteq> (Graph.digraph_abs G)\<close>
        have "awalk (Graph.digraph_abs G) (snd e1) ys (fst e2)"
        by (meson Component_Defs.subgraphI awalk_def order.trans subgraph_dVs')
      
      then show ?thesis
        using \<open>invar_seen dfs_cycles_state\<close> \<open>snd e1 \<in> t_set (V -\<^sub>G (seen dfs_cycles_state))\<close>
          \<open>fst e2 \<in> (t_set (seen dfs_cycles_state))\<close>
        by (force elim!: invar_props_elims)
    next
      case 2
      then obtain xs ys zs where "c = xs @ [e2] @ ys @ [e1] @ zs" by blast
      with c_awalk awalk_append_iff
        have "awalk ?G_seen_new u (xs @ [e2]) (awlast u (xs @ [e2]))"
        by (metis append.assoc)
      
      have "awlast u (xs @ [e2]) = snd e2"
        by (auto simp add: awalk_verts_conv)
      with \<open>c = xs @ [e2] @ ys @ [e1] @ zs\<close> c_awalk awalk_append_iff
        have "awalk ?G_seen_new (snd e2) (ys @ [e1] @ zs) (awlast (snd e2) (ys @ [e1] @ zs))"
        by (smt (verit, best) awalkE)
      with awalk_append_iff
        have "awalk ?G_seen_new (snd e2) ys (awlast (snd e2) ys)"
        "awalk ?G_seen_new (awlast (snd e2) ys) ([e1] @ zs) (awlast (snd e2) (ys @ [e1] @ zs))"
        by auto
      then have "(awlast (snd e2) ys) = awhd (awlast (snd e2) ys) ([e1] @ zs)"
        by auto
      then have "(awlast (snd e2) ys) = fst e1"
        by (simp add: awalk_verts_conv)
      with \<open>awalk ?G_seen_new (snd e2) ys (awlast (snd e2) ys)\<close>
        have "awalk ?G_seen_new (snd e2) ys (fst e1)" by simp
      with \<open>?G_seen_new \<subseteq> (Graph.digraph_abs G)\<close>
        have "awalk (Graph.digraph_abs G) (snd e2) ys (fst e1)"
        by (meson Component_Defs.subgraphI awalk_def order.trans subgraph_dVs')

      then show ?thesis
        using \<open>invar_seen dfs_cycles_state\<close> \<open>snd e2 \<in> t_set (seen dfs_cycles_state)\<close>
          \<open>fst e1 \<in> t_set (V -\<^sub>G (seen dfs_cycles_state))\<close>
        by (force elim!: invar_props_elims)
    qed
  qed
qed

lemma invar_cycle_false_ret_1[invar_holds_intros]:
  "\<lbrakk>DFS_Cycles_ret_1_conds dfs_cycles_state; invar_cycle_false dfs_cycles_state\<rbrakk> \<Longrightarrow>
    invar_cycle_false (DFS_Cycles_ret1 dfs_cycles_state)"
  by (force simp add: DFS_Cycles_ret1_def Let_def intro!: invar_props_intros elim!: call_cond_elims invar_props_elims)

lemma invar_cycle_false_ret_2[invar_holds_intros]:
  "\<lbrakk>DFS_Cycles_ret_2_conds dfs_cycles_state; invar_cycle_false dfs_cycles_state\<rbrakk> \<Longrightarrow>
    invar_cycle_false (DFS_Cycles_ret2 dfs_cycles_state)"
  by (auto simp add: DFS_Cycles_ret2_def)

lemma invar_cycle_false_holds[invar_holds_intros]: 
   assumes "DFS_Cycles_dom dfs_cycles_state" "invar_1 dfs_cycles_state" "invar_seen dfs_cycles_state"
     "invar_cycle_false dfs_cycles_state"
   shows "invar_cycle_false (DFS_Cycles dfs_cycles_state)"
  using assms(2-)
proof(induction rule: DFS_Cycles_induct[OF assms(1)])
  case IH: (1 dfs_cycles_state)
  show ?case
    apply(rule DFS_Cycles_cases[where dfs_cycles_state = dfs_cycles_state])
    by (auto intro!: IH(2-5) invar_holds_intros simp: DFS_Cycles_simps[OF IH(1)])
qed



lemma invar_cycle_true_props[invar_props_elims]:
  "invar_cycle_true dfs_cycles_state \<Longrightarrow>
     (\<lbrakk>cycle dfs_cycles_state \<Longrightarrow> (\<exists>c. cycle' (Graph.digraph_abs G) c)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
     P"
  by (auto simp: invar_cycle_true_def)

lemma invar_cycle_true_intro[invar_props_intros]:
  "\<lbrakk>cycle dfs_cycles_state \<Longrightarrow> (\<exists>c. cycle' (Graph.digraph_abs G) c)\<rbrakk> \<Longrightarrow>
     invar_cycle_true dfs_cycles_state"
  by (auto simp: invar_cycle_true_def)

lemma invar_cycle_true_holds_upd1[invar_holds_intros]:
  "\<lbrakk>DFS_Cycles_call_1_conds dfs_cycles_state; invar_cycle_true dfs_cycles_state\<rbrakk> \<Longrightarrow>
    invar_cycle_true (DFS_Cycles_upd1 dfs_cycles_state)"
  by (force simp add: DFS_Cycles_upd1_def Let_def intro!: invar_props_intros elim!: invar_props_elims)

lemma invar_cycle_true_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>DFS_Cycles_ret_1_conds dfs_cycles_state; invar_1 dfs_cycles_state; invar_cycle_true dfs_cycles_state\<rbrakk> \<Longrightarrow>
    invar_cycle_true (DFS_Cycles_ret1 dfs_cycles_state)"
proof (intro invar_props_intros, goal_cases)
  case 1
  let ?s = "sel (V -\<^sub>G (seen dfs_cycles_state))"

  have "?s \<in> dVs (Graph.digraph_abs G)"
    using \<open>invar_1 dfs_cycles_state\<close> \<open>DFS_Cycles_ret_1_conds dfs_cycles_state\<close>
    by (auto simp add: V_graph_verts elim!: invar_props_elims call_cond_elims) 
  with dfs_aux_cycle_true show ?case
    using \<open>DFS_Cycles_ret_1_conds dfs_cycles_state\<close>
    by (auto elim!: call_cond_elims) 
qed

lemma invar_cycle_true_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>DFS_Cycles_ret_2_conds dfs_cycles_state; invar_cycle_true dfs_cycles_state\<rbrakk> \<Longrightarrow>
    invar_cycle_true (DFS_Cycles_ret2 dfs_cycles_state)"
  by (auto simp add: DFS_Cycles_ret2_def Let_def intro!: invar_props_intros)

lemma invar_cycle_true_holds[invar_holds_intros]: 
   assumes "DFS_Cycles_dom dfs_cycles_state" "invar_1 dfs_cycles_state" "invar_cycle_true dfs_cycles_state"
   shows "invar_cycle_true (DFS_Cycles dfs_cycles_state)"
  using assms(2-)
proof(induction rule: DFS_Cycles_induct[OF assms(1)])
  case IH: (1 dfs_cycles_state)
  show ?case
    apply(rule DFS_Cycles_cases[where dfs_cycles_state = dfs_cycles_state])
    by (auto intro!: IH(2-4) invar_holds_intros simp: DFS_Cycles_simps[OF IH(1)])
qed


lemma DFS_Cycles_ret_1[ret_holds_intros]:
  "DFS_Cycles_ret_1_conds (dfs_cycles_state) \<Longrightarrow> DFS_Cycles_ret_1_conds (DFS_Cycles_ret1 dfs_cycles_state)"
  by (auto simp: elim!: call_cond_elims intro!: call_cond_intros simp: DFS_Cycles_ret1_def)

lemma ret1_holds[ret_holds_intros]:
   assumes "DFS_Cycles_dom dfs_cycles_state" "cycle (DFS_Cycles dfs_cycles_state)"
     "\<not>cycle dfs_cycles_state"
   shows "DFS_Cycles_ret_1_conds (DFS_Cycles dfs_cycles_state)" 
   using assms(2-)
proof(induction rule: DFS_Cycles_induct[OF assms(1)])
  case IH: (1 dfs_cycles_state)
  show ?case
    apply(rule DFS_Cycles_cases[where dfs_cycles_state = dfs_cycles_state])
    subgoal
      using IH(3-4)
      apply (auto intro: ret_holds_intros intro!: IH(2-4) simp: DFS_Cycles_simps[OF IH(1)])
      by (simp add: DFS_Cycles_upd1_def)
    subgoal
      using IH(3-4)
      by (auto intro: ret_holds_intros intro!: IH(2-) simp: DFS_Cycles_simps[OF IH(1)] DFS_Cycles_ret2_def)
    subgoal
      using IH(3-4) assms             
      by (auto intro: ret_holds_intros intro!: IH(2-) simp: DFS_Cycles_simps[OF IH(1)] DFS_Cycles_ret2_def)
    done
qed

lemma DFS_Cycles_correct_1_ret_1:
  "\<lbrakk>DFS_Cycles_ret_1_conds dfs_cycles_state; cycle dfs_cycles_state; invar_cycle_true dfs_cycles_state\<rbrakk> \<Longrightarrow>
    (\<exists>c. cycle' (Graph.digraph_abs G) c)"
  by (auto elim!: invar_props_elims)

lemma DFS_Cycles_ret_2[ret_holds_intros]:
  "DFS_Cycles_ret_2_conds (dfs_cycles_state) \<Longrightarrow> DFS_Cycles_ret_2_conds (DFS_Cycles_ret2 dfs_cycles_state)"
  by (auto simp: DFS_Cycles_ret2_def elim!: call_cond_elims intro!: call_cond_intros)

lemma ret2_holds[ret_holds_intros]:
   assumes "DFS_Cycles_dom dfs_cycles_state" "\<not>cycle (DFS_Cycles dfs_cycles_state)"
   shows "DFS_Cycles_ret_2_conds (DFS_Cycles dfs_cycles_state)" 
   using assms(2-)
proof(induction  rule: DFS_Cycles_induct[OF assms(1)])
  case IH: (1 dfs_cycles_state)
  show ?case
    apply(rule DFS_Cycles_cases[where dfs_cycles_state = dfs_cycles_state])
    using IH(3)                                                                
    by (auto intro: ret_holds_intros intro!: IH(2-) simp: DFS_Cycles_simps[OF IH(1)] DFS_Cycles_ret1_def)
qed

lemma DFS_Cycles_correct_2_ret_2:
  "\<lbrakk>DFS_Cycles_ret_2_conds dfs_cycles_state; \<not>cycle dfs_cycles_state; invar_1 dfs_cycles_state;
    invar_seen_subset_V dfs_cycles_state; invar_cycle_false dfs_cycles_state\<rbrakk> \<Longrightarrow>
    (\<nexists>c. cycle' (Graph.digraph_abs G) c)"
proof-
  assume "DFS_Cycles_ret_2_conds dfs_cycles_state" "\<not>cycle dfs_cycles_state" "invar_1 dfs_cycles_state"
    "invar_seen_subset_V dfs_cycles_state" "invar_cycle_false dfs_cycles_state"
  then have no_cycles: "(\<nexists>c. cycle' ((Graph.digraph_abs G) \<downharpoonright> (t_set (seen dfs_cycles_state))) c)"
    by (force elim!: invar_props_elims)

  have "t_set (seen dfs_cycles_state) = t_set V"
    using \<open>invar_1 dfs_cycles_state\<close> \<open>DFS_Cycles_ret_2_conds dfs_cycles_state\<close>
      \<open>invar_seen_subset_V dfs_cycles_state\<close>
    by (force elim!: invar_props_elims call_cond_elims)
  with V_graph_verts
    have "((Graph.digraph_abs G) \<downharpoonright> (t_set (seen dfs_cycles_state))) = (Graph.digraph_abs G)"
    unfolding induce_subgraph_def dVs_def by blast
  with no_cycles show "(\<nexists>c. cycle' (Graph.digraph_abs G) c)"
    by auto
qed

subsection \<open>Termination\<close>

named_theorems termination_intros

declare termination_intros

lemma in_prod_relI[intro!,termination_intros]:
  "\<lbrakk>f1 a = f1 a'; (a, a') \<in> f2 <*mlex*> r\<rbrakk> \<Longrightarrow> (a,a') \<in> (f1 <*mlex*> f2 <*mlex*> r)"
   by (simp add: mlex_iff)+

definition "less_rel \<equiv> {(x::nat, y::nat). x < y}"

lemma wf_less_rel[intro!]: "wf less_rel"
  by(auto simp: less_rel_def wf_less)


lemma call_measure_nonsym[simp]: "(call_measure dfs_cycles_state, call_measure dfs_cycles_state) \<notin> less_rel"
  by (auto simp: less_rel_def)

lemma call_1_terminates[termination_intros]:
  "\<lbrakk>DFS_Cycles_call_1_conds dfs_cycles_state; invar_1 dfs_cycles_state; invar_seen dfs_cycles_state;
    invar_seen_subset_V dfs_cycles_state\<rbrakk> \<Longrightarrow> (DFS_Cycles_upd1 dfs_cycles_state, dfs_cycles_state) \<in> call_measure <*mlex*> r"
proof-
  assume "DFS_Cycles_call_1_conds dfs_cycles_state" "invar_1 dfs_cycles_state" "invar_seen dfs_cycles_state"
    "invar_seen_subset_V dfs_cycles_state"
  let ?s = "sel (V -\<^sub>G (seen dfs_cycles_state))"
  let ?seen' = "t_set (seen_aux (dfs_aux ?s))"

  have "?s \<in> dVs (Graph.digraph_abs G)"
    using \<open>invar_1 dfs_cycles_state\<close> \<open>DFS_Cycles_call_1_conds dfs_cycles_state\<close>
    by (auto simp add: V_graph_verts elim!: invar_props_elims call_cond_elims)

  have "t_set (V -\<^sub>G (seen dfs_cycles_state)) \<noteq> {}"
    using \<open>DFS_Cycles_call_1_conds dfs_cycles_state\<close> \<open>invar_1 dfs_cycles_state\<close>
    by (force elim!: call_cond_elims invar_props_elims)
  then have "?s \<in> t_set (V -\<^sub>G (seen dfs_cycles_state))"
    using \<open>DFS_Cycles_call_1_conds dfs_cycles_state\<close> \<open>invar_1 dfs_cycles_state\<close>
    by (force elim!: call_cond_elims invar_props_elims)
  then have "?seen' \<noteq> {}"
    using \<open>?s \<in> dVs (Graph.digraph_abs G)\<close> dfs_aux_s_in_seen[of ?s] by blast

  have seen_expr: "t_set (seen (DFS_Cycles_upd1 dfs_cycles_state)) = 
    (t_set (seen dfs_cycles_state)) \<union> ?seen'"
    using \<open>invar_1 dfs_cycles_state\<close> \<open>?s \<in> dVs (Graph.digraph_abs G)\<close> dfs_aux_seen_inv
    by (force simp add: DFS_Cycles_upd1_def elim!: invar_props_elims)
  with \<open>?seen' \<noteq> {}\<close> have "card (t_set (seen (DFS_Cycles_upd1 dfs_cycles_state))) > 
    card (t_set (seen dfs_cycles_state))"
    using \<open>DFS_Cycles_call_1_conds dfs_cycles_state\<close> \<open>invar_1 dfs_cycles_state\<close> \<open>?s \<in> dVs (Graph.digraph_abs G)\<close> dfs_aux_s_in_seen
    by (metis DiffD2 UnCI V_inv \<open>?s \<in> [V -\<^sub>G DFS_Cycles_state.seen dfs_cycles_state]\<^sub>s\<close> card_seteq
     finite_neighbourhoods inf_sup_ord(3) invar_1_props linorder_not_le set_ops.set_diff)
  moreover have "t_set (seen (DFS_Cycles_upd1 dfs_cycles_state)) \<subseteq> t_set V"
    using invar_seen_subset_V_holds_upd1[OF \<open>DFS_Cycles_call_1_conds dfs_cycles_state\<close> \<open>invar_1 dfs_cycles_state\<close>
      \<open>invar_seen dfs_cycles_state\<close> \<open>invar_seen_subset_V dfs_cycles_state\<close>]
    by (auto elim!: invar_props_elims)
  moreover have "t_set (seen dfs_cycles_state) \<subseteq> t_set V"
    using \<open>invar_seen_subset_V dfs_cycles_state\<close> by (auto elim!: invar_props_elims)
  

  ultimately have "card (t_set (V -\<^sub>G seen (DFS_Cycles_upd1 dfs_cycles_state))) < 
    card (t_set (V -\<^sub>G seen dfs_cycles_state))"
    using invar_1_holds_upd1[OF \<open>DFS_Cycles_call_1_conds dfs_cycles_state\<close> \<open>invar_1 dfs_cycles_state\<close>]
    using \<open>invar_1 dfs_cycles_state\<close>
    apply (clarsimp elim!: invar_props_elims invar_holds_intros)
    by (metis Diff_Diff_Int Diff_Un V_inv card_seteq finite_neighbourhoods inf.absorb_iff2 inf_le1
      leI nat_less_le seen_expr set_ops.set_diff)
  then show ?thesis
    by (auto simp add: call_measure_def Let_def intro!: mlex_less)
qed


lemma wf_term_rel: "wf DFS_Cycles_term_rel'"
  by (auto simp: wf_mlex DFS_Cycles_term_rel'_def)

lemma in_DFS_Cycles_term_rel'[termination_intros]:
  "\<lbrakk>DFS_Cycles_call_1_conds dfs_cycles_state; invar_1 dfs_cycles_state; invar_seen dfs_cycles_state;
    invar_seen_subset_V dfs_cycles_state\<rbrakk> \<Longrightarrow>
     (DFS_Cycles_upd1 dfs_cycles_state, dfs_cycles_state) \<in> DFS_Cycles_term_rel'" 
  by (simp add: DFS_Cycles_term_rel'_def termination_intros)+

lemma DFS_Cycles_terminates[termination_intros]:
  assumes "invar_1 dfs_cycles_state" "invar_seen dfs_cycles_state" "invar_seen_subset_V dfs_cycles_state"
  shows "DFS_Cycles_dom dfs_cycles_state"
  using wf_term_rel assms
proof(induction rule: wf_induct_rule)
  case (less x)
  show ?case
    by (rule DFS_Cycles_domintros) (auto intro!: invar_holds_intros less in_DFS_Cycles_term_rel')
qed

lemma initial_state_props[invar_holds_intros, termination_intros]:
  "invar_1 (initial_state)" "invar_seen initial_state" "invar_seen_subset_V initial_state" "invar_cycle_false initial_state" 
  "invar_cycle_true initial_state" "DFS_Cycles_dom initial_state"
  by (auto simp: initial_state_def
                 hd_of_vwalk_bet'' cycle'_def induce_subgraph_def Awalk_Defs.cycle_def Awalk_Defs.awalk_def
           elim: vwalk_betE
           intro!: termination_intros invar_props_intros)


lemma DFS_Cycles_correct_1:
  assumes "cycle (DFS_Cycles initial_state)"
  shows "(\<exists>c. cycle' (Graph.digraph_abs G) c)"
  apply (intro DFS_Cycles_correct_1_ret_1[where dfs_cycles_state = "DFS_Cycles (initial_state)"])
  subgoal
    using ret1_holds assms
    using initial_state_def initial_state_props(6) by force
  subgoal
    using assms by blast
  subgoal
    by (auto intro!: invar_holds_intros)
  done

lemma DFS_Cycles_correct_2:
  assumes "\<not>cycle (DFS_Cycles initial_state)"
  shows "\<nexists>c. cycle' (Graph.digraph_abs G) c"
  apply (intro DFS_Cycles_correct_2_ret_2[where dfs_cycles_state = "DFS_Cycles (initial_state)"])
  subgoal
    using assms by (auto intro: invar_holds_intros ret_holds_intros)
  subgoal
    using assms by blast
  subgoal
    by (auto intro!: invar_holds_intros)
  subgoal
    by (auto intro!: invar_holds_intros)
  subgoal
    by (auto intro!: invar_holds_intros)
  done

end

end

end