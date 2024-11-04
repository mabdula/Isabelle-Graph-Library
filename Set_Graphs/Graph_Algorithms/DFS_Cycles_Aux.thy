theory DFS_Cycles_Aux              
  imports Directed_Set_Graphs.Pair_Graph_Specs
    Directed_Set_Graphs.Set_Addons Directed_Set_Graphs.Component_Defs Directed_Set_Graphs.Awalk
begin

context Set2
begin

  notation "inter" (infixl "\<inter>\<^sub>G" 100)
  notation "diff" (infixl "-\<^sub>G" 100)
  notation "union" (infixl "\<union>\<^sub>G" 100)
end

lemma dfs_tree_aux1:
  assumes "l = v # l_tl" "w \<notin> (set l \<union> F)"
    "\<forall>(x, y) \<in> dG. (x \<in> F \<longrightarrow> y \<in> (set l \<union> F)) \<and> (y \<in> F \<longrightarrow> x \<in> (set l \<union> F))"
  shows
    "set (edges_of_vwalk (rev (w # l))) \<union> set (edges_of_vwalk (w # l)) \<union>
    {(x, y). (x, y) \<in> dG \<and> x \<in> set (w # l) \<and> y \<in> F} \<union>
    {(x, y). (x, y) \<in> dG \<and> x \<in> F \<and> y \<in> set (w # l)} \<union>
    {(x, y). (x, y) \<in> dG \<and> x \<in> F \<and> y \<in> F} =
    {(v, w), (w, v)} \<union>
    set (edges_of_vwalk (rev l)) \<union> set (edges_of_vwalk l) \<union>
    {(x, y). (x, y) \<in> dG \<and> x \<in> set l \<and> y \<in> F} \<union>
    {(x, y). (x, y) \<in> dG \<and> x \<in> F \<and> y \<in> set l} \<union>
    {(x, y). (x, y) \<in> dG \<and> x \<in> F \<and> y \<in> F}"
proof-
  have 1: "set (edges_of_vwalk (w # l)) = {(w, v)} \<union> set (edges_of_vwalk l)"
    using assms(1) by simp

  have "edges_of_vwalk (rev (w # l)) = (edges_of_vwalk (rev l)) @ [(v, w)]"
    using assms(1)
    by (metis edges_of_vwalk.simps(2) edges_of_vwalk.simps(3) edges_of_vwalk_append_3 last_rev
    list.sel(1) list.simps(3) rev.simps(2) rev_is_Nil_conv)
  then have 2: "set (edges_of_vwalk (rev (w # l))) = {(v, w)} \<union> set (edges_of_vwalk (rev l))" by simp

  from assms(2) assms(3)
    have 3: "{(x, y). (x, y) \<in> dG \<and> x \<in> set (w # l) \<and> y \<in> F} = 
    {(x, y). (x, y) \<in> dG \<and> x \<in> set l \<and> y \<in> F}" by auto
  from assms(2) assms(3)
    have 4: "{(x, y). (x, y) \<in> dG \<and> x \<in> F \<and> y \<in> set (w # l)} = 
    {(x, y). (x, y) \<in> dG \<and> x \<in> F \<and> y \<in> set l}" by auto

  from 1 2 3 4 show ?thesis by auto
qed

lemma dfs_tree_aux2_1:
  assumes "l = v # l_tl" "l_tl = []" "(\<forall>(x, y) \<in> dG. x \<noteq> y)"
  shows 
    "set (edges_of_vwalk (rev l_tl)) \<union> set (edges_of_vwalk l_tl) \<union>
    {(x, y). (x, y) \<in> dG \<and> x \<in> set l_tl \<and> y \<in> (insert v F)} \<union>
    {(x, y). (x, y) \<in> dG \<and> x \<in> (insert v F) \<and> y \<in> set l_tl} \<union>
    {(x, y). (x, y) \<in> dG \<and> x \<in> (insert v F) \<and> y \<in> (insert v F)} =
    set (edges_of_vwalk (rev l)) \<union> set (edges_of_vwalk l) \<union>
    {(x, y). (x, y) \<in> dG \<and> x \<in> set l \<and> y \<in> F} \<union>
    {(x, y). (x, y) \<in> dG \<and> x \<in> F \<and> y \<in> set l} \<union>
    {(x, y). (x, y) \<in> dG \<and> x \<in> F \<and> y \<in> F}"
proof-
  have 1: "set (edges_of_vwalk l_tl) = set (edges_of_vwalk l)"
    using assms(1) assms(2) by simp
  have 2: "set (edges_of_vwalk (rev l_tl)) = set (edges_of_vwalk (rev l))"
    using assms(1) assms(2) by simp
  
  have 3: "{(x, y). (x, y) \<in> dG \<and> x \<in> set l \<and> y \<in> F} =
    {(x, y). (x, y) \<in> dG \<and> x \<in> set l_tl \<and> y \<in> (insert v F)} \<union> {(x, y). (x, y) \<in> dG \<and> x = v \<and> y \<in> F}"
    using assms(1) assms(2) by simp
  
  have 4: "{(x, y). (x, y) \<in> dG \<and> x \<in> F \<and> y \<in> set l} =
    {(x, y). (x, y) \<in> dG \<and> x \<in> (insert v F) \<and> y \<in> set l_tl} \<union> {(x, y). (x, y) \<in> dG \<and> x \<in> F \<and> y = v}"
    using assms(1) assms(2) by simp
  
  have 5: "{(x, y). (x, y) \<in> dG \<and> x \<in> (insert v F) \<and> y \<in> (insert v F)} =
    {(x, y). (x, y) \<in> dG \<and> x \<in> F \<and> y \<in> F} \<union>
    {(x, y). (x, y) \<in> dG \<and> x = v \<and> y \<in> F} \<union>
    {(x, y). (x, y) \<in> dG \<and> x \<in> F \<and> y = v}" using assms(3) by auto

  from 1 2 3 4 5 show ?thesis by auto
qed

lemma dfs_tree_aux2_2:
  assumes "l = v # l_tl" "l_tl = u # l_tl_tl" "(\<forall>(x, y) \<in> dG. x \<noteq> y)" "{(u, v), (v, u)} \<subseteq> dG"
    "set l_tl \<inter> F = {}" "\<forall>(x, y) \<in> dG. (x = v \<longrightarrow> y \<noteq> u \<longrightarrow> y \<in> F) \<and> (y = v \<longrightarrow> x \<noteq> u \<longrightarrow> x \<in> F)"
  shows 
    "set (edges_of_vwalk (rev l_tl)) \<union> set (edges_of_vwalk l_tl) \<union>
    {(x, y). (x, y) \<in> dG \<and> x \<in> set l_tl \<and> y \<in> (insert v F)} \<union>
    {(x, y). (x, y) \<in> dG \<and> x \<in> (insert v F) \<and> y \<in> set l_tl} \<union>
    {(x, y). (x, y) \<in> dG \<and> x \<in> (insert v F) \<and> y \<in> (insert v F)} =
    set (edges_of_vwalk (rev l)) \<union> set (edges_of_vwalk l) \<union>
    {(x, y). (x, y) \<in> dG \<and> x \<in> set l \<and> y \<in> F} \<union>
    {(x, y). (x, y) \<in> dG \<and> x \<in> F \<and> y \<in> set l} \<union>
    {(x, y). (x, y) \<in> dG \<and> x \<in> F \<and> y \<in> F}"
proof-
  have 1: "set (edges_of_vwalk l) = {(v, u)} \<union> set (edges_of_vwalk l_tl)"
    using assms(1) assms(2) by simp

  have "edges_of_vwalk (rev l) = (edges_of_vwalk (rev l_tl)) @ [(u, v)]"
    using assms(1) assms(2)
    by (metis edges_of_vwalk.simps(2) edges_of_vwalk.simps(3) edges_of_vwalk_append_3 last_rev
    list.sel(1) list.simps(3) rev.simps(2) rev_is_Nil_conv)
  then have 2: "set (edges_of_vwalk (rev l)) = {(u, v)} \<union> set (edges_of_vwalk (rev l_tl))" by simp

  have "{(x, y). (x, y) \<in> dG \<and> x \<in> set l_tl \<and> y = v} =
    {(u, v)} \<union> {(x, y). (x, y) \<in> dG \<and> x \<in> set l_tl_tl \<and> y = v}"
    using assms(2) assms(4) by auto
  then have "{(x, y). (x, y) \<in> dG \<and> x \<in> set l_tl \<and> y = v} = {(u, v)}"
    using assms(5) assms(6) by blast
  then have 3: "{(x, y). (x, y) \<in> dG \<and> x \<in> set l_tl \<and> y \<in> (insert v F)} = 
    {(x, y). (x, y) \<in> dG \<and> x \<in> set l_tl \<and> y \<in> F} \<union> {(u, v)}" by auto
  have 4: "{(x, y). (x, y) \<in> dG \<and> x \<in> set l \<and> y \<in> F} = 
    {(x, y). (x, y) \<in> dG \<and> x \<in> set l_tl \<and> y \<in> F} \<union> {(x, y). (x, y) \<in> dG \<and> x = v \<and> y \<in> F}"
    using assms(1) by auto

  have "{(x, y). (x, y) \<in> dG \<and> x = v \<and> y \<in> set l_tl} =
    {(v, u)} \<union> {(x, y). (x, y) \<in> dG \<and> x = v \<and> y \<in> set l_tl_tl}"
    using assms(2) assms(4) by auto
  then have "{(x, y). (x, y) \<in> dG \<and> x = v \<and> y \<in> set l_tl} = {(v, u)}"
    using assms(2) assms(5) assms(6) by auto
  then have 5: "{(x, y). (x, y) \<in> dG \<and> x \<in> (insert v F) \<and> y \<in> set l_tl} = 
    {(x, y). (x, y) \<in> dG \<and> x \<in> F \<and> y \<in> set l_tl} \<union> {(v, u)}" by fast
  have 6: "{(x, y). (x, y) \<in> dG \<and> x \<in> F \<and> y \<in> set l} =
    {(x, y). (x, y) \<in> dG \<and> x \<in> F \<and> y \<in> set l_tl} \<union> {(x, y). (x, y) \<in> dG \<and> x \<in> F \<and> y = v}"
    using assms(1) by auto

  have 7: "{(x, y). (x, y) \<in> dG \<and> x \<in> (insert v F) \<and> y \<in> (insert v F)} =
    {(x, y). (x, y) \<in> dG \<and> x \<in> F \<and> y \<in> F} \<union>
    {(x, y). (x, y) \<in> dG \<and> x = v \<and> y \<in> F} \<union>
    {(x, y). (x, y) \<in> dG \<and> x \<in> F \<and> y = v}" using assms(3) by auto

  from 1 2 3 4 5 6 7 show ?thesis by auto
qed





record ('ver, 'neighb) DFS_Aux_state =
  stack:: "'ver list" seen:: "'neighb" finished:: "'neighb" cycle:: bool

named_theorems call_cond_elims
named_theorems call_cond_intros
named_theorems ret_holds_intros
named_theorems invar_props_intros
named_theorems invar_props_elims
named_theorems invar_holds_intros
named_theorems state_rel_intros
named_theorems state_rel_holds_intros 

locale DFS_Aux =
  Graph: Pair_Graph_Specs
    where lookup = lookup +
 set_ops: Set2 neighb_empty neighb_delete _ t_set neighb_inv insert


for lookup :: "'adj \<Rightarrow> 'v \<Rightarrow> 'neighb option" +

fixes G::"'adj" and s::"'v"
begin

(* We assume the graph is symmetric since we will run the algorithm on undirected graphs, and that
it has no self-loops. *)
definition "DFS_Aux_axioms \<equiv>
  Graph.graph_inv G \<and> Graph.finite_graph G \<and> Graph.finite_neighbs \<and> s \<in> dVs (Graph.digraph_abs G) \<and>
  (\<forall>(x, y) \<in> (Graph.digraph_abs G). (y, x) \<in> Graph.digraph_abs G) \<and>
  (\<forall>x \<in> dVs (Graph.digraph_abs G). (x, x) \<notin> Graph.digraph_abs G)"


abbreviation "neighbourhood' \<equiv> Graph.neighbourhood G"

notation "neighbourhood'" ("\<N>\<^sub>G _" 100)

lemmas [code] = Graph.neighbourhood_def


function (domintros) DFS_Aux::"('v, 'neighb) DFS_Aux_state \<Rightarrow> ('v, 'neighb) DFS_Aux_state" where
  "DFS_Aux dfs_aux_state = 
     (case (stack dfs_aux_state) of (v # stack_tl) \<Rightarrow>
       let 
         excl = (case stack_tl of [] \<Rightarrow> \<emptyset>\<^sub>N | u # _ \<Rightarrow> insert u \<emptyset>\<^sub>N)
       in
       (if ((\<N>\<^sub>G v) -\<^sub>G excl) \<inter>\<^sub>G (seen dfs_aux_state -\<^sub>G finished dfs_aux_state) \<noteq> \<emptyset>\<^sub>N then 
          (dfs_aux_state \<lparr>cycle := True\<rparr>)
        else ((if ((\<N>\<^sub>G v) -\<^sub>G (seen dfs_aux_state)) \<noteq> \<emptyset>\<^sub>N then
                let w = (sel ((\<N>\<^sub>G v) -\<^sub>G (seen dfs_aux_state)));
                    stack' = w # (stack dfs_aux_state);
                    seen' = insert w (seen dfs_aux_state) 
                in
                  (DFS_Aux (dfs_aux_state \<lparr>stack := stack', seen := seen' \<rparr>))
              else
                let stack' = stack_tl;
                    finished' = insert v (finished dfs_aux_state)
                in
                   DFS_Aux (dfs_aux_state \<lparr>stack := stack', finished := finished'\<rparr>))
            )
      )
     | _ \<Rightarrow> dfs_aux_state
    )"
  by pat_completeness auto

partial_function (tailrec) DFS_Aux_impl::"('v, 'neighb) DFS_Aux_state \<Rightarrow> ('v, 'neighb) DFS_Aux_state" where
  "DFS_Aux_impl dfs_aux_state = 
     (case (stack dfs_aux_state) of (v # stack_tl) \<Rightarrow>
       let 
         excl = (case stack_tl of [] \<Rightarrow> \<emptyset>\<^sub>N | u # _ \<Rightarrow> insert u \<emptyset>\<^sub>N)
       in
       (if ((\<N>\<^sub>G v) -\<^sub>G excl) \<inter>\<^sub>G (seen dfs_aux_state -\<^sub>G finished dfs_aux_state) \<noteq> \<emptyset>\<^sub>N then 
          (dfs_aux_state \<lparr>cycle := True\<rparr>)
        else ((if ((\<N>\<^sub>G v) -\<^sub>G (seen dfs_aux_state)) \<noteq> \<emptyset>\<^sub>N then
                let w = (sel ((\<N>\<^sub>G v) -\<^sub>G (seen dfs_aux_state)));
                    stack' = w # (stack dfs_aux_state);
                    seen' = insert w (seen dfs_aux_state) 
                in
                  (DFS_Aux_impl (dfs_aux_state \<lparr>stack := stack', seen := seen' \<rparr>))
              else
                let stack' = stack_tl;
                    finished' = insert v (finished dfs_aux_state)
                in
                   DFS_Aux_impl (dfs_aux_state \<lparr>stack := stack', finished := finished'\<rparr>))
            )
      )
     | _ \<Rightarrow> dfs_aux_state
    )"

lemmas [code] = DFS_Aux_impl.simps

lemma DFS_Aux_impl_same: 
  assumes "DFS_Aux_dom state"
  shows "DFS_Aux_impl state = DFS_Aux state"
  by(induction rule: DFS_Aux.pinduct[OF assms])
    (subst DFS_Aux.psimps, simp, subst DFS_Aux_impl.simps, auto split: list.split if_split simp add: Let_def)

definition "DFS_Aux_call_1_conds dfs_aux_state \<equiv> 
    (case (stack dfs_aux_state) of (v # stack_tl) \<Rightarrow>
       let 
         excl = (case stack_tl of [] \<Rightarrow> \<emptyset>\<^sub>N | u # _ \<Rightarrow> insert u \<emptyset>\<^sub>N)
       in
       (if ((\<N>\<^sub>G v) -\<^sub>G excl) \<inter>\<^sub>G (seen dfs_aux_state -\<^sub>G finished dfs_aux_state) \<noteq> \<emptyset>\<^sub>N then 
         False
       else 
         (if ((\<N>\<^sub>G v) -\<^sub>G (seen dfs_aux_state)) \<noteq> \<emptyset>\<^sub>N then True 
         else False))
     | _ \<Rightarrow> False
    )"

lemma DFS_Aux_call_1_conds[call_cond_elims]:
  "DFS_Aux_call_1_conds dfs_aux_state \<Longrightarrow> 
   \<lbrakk>\<lbrakk>\<exists>v stack_tl. stack dfs_aux_state = v # stack_tl;
    ((\<N>\<^sub>G (hd (stack dfs_aux_state))) -\<^sub>G (case (tl (stack dfs_aux_state)) of [] \<Rightarrow> \<emptyset>\<^sub>N | u # _ \<Rightarrow> insert u \<emptyset>\<^sub>N))
       \<inter>\<^sub>G (seen dfs_aux_state -\<^sub>G finished dfs_aux_state) = \<emptyset>\<^sub>N;
    ((\<N>\<^sub>G (hd (stack dfs_aux_state))) -\<^sub>G (seen dfs_aux_state)) \<noteq> \<emptyset>\<^sub>N\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> 
   P"
  by(auto simp: DFS_Aux_call_1_conds_def split: list.splits option.splits if_splits)

definition "DFS_Aux_upd1 dfs_aux_state \<equiv> (
    let
      N = (\<N>\<^sub>G (hd (stack dfs_aux_state)));
      w = (sel ((N -\<^sub>G (seen dfs_aux_state))));
      stack' = w # (stack dfs_aux_state);
      seen' = insert w (seen dfs_aux_state)
    in
      dfs_aux_state \<lparr>stack := stack', seen := seen'\<rparr>)" 

definition "DFS_Aux_call_2_conds dfs_aux_state \<equiv> 
    (case (stack dfs_aux_state) of (v # stack_tl) \<Rightarrow>
       let 
         excl = (case stack_tl of [] \<Rightarrow> \<emptyset>\<^sub>N | u # _ \<Rightarrow> insert u \<emptyset>\<^sub>N)
       in
       (if ((\<N>\<^sub>G v) -\<^sub>G excl) \<inter>\<^sub>G (seen dfs_aux_state -\<^sub>G finished dfs_aux_state) \<noteq> \<emptyset>\<^sub>N then 
         False
       else 
         (if ((\<N>\<^sub>G v) -\<^sub>G (seen dfs_aux_state)) \<noteq> \<emptyset>\<^sub>N then False 
         else True))
     | _ \<Rightarrow> False
    )"

lemma DFS_Aux_call_2_conds[call_cond_elims]:
  "DFS_Aux_call_2_conds dfs_aux_state \<Longrightarrow> 
   \<lbrakk>\<lbrakk>\<exists>v stack_tl. stack dfs_aux_state = v # stack_tl;
    ((\<N>\<^sub>G (hd (stack dfs_aux_state))) -\<^sub>G (case (tl (stack dfs_aux_state)) of [] \<Rightarrow> \<emptyset>\<^sub>N | u # _ \<Rightarrow> insert u \<emptyset>\<^sub>N))
       \<inter>\<^sub>G (seen dfs_aux_state -\<^sub>G finished dfs_aux_state) = \<emptyset>\<^sub>N;
    ((\<N>\<^sub>G (hd (stack dfs_aux_state))) -\<^sub>G (seen dfs_aux_state)) = \<emptyset>\<^sub>N\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> 
   P"
  by(auto simp: DFS_Aux_call_2_conds_def split: list.splits option.splits if_splits)

definition "DFS_Aux_upd2 dfs_aux_state \<equiv> (
    let
      stack' = tl (stack dfs_aux_state);
      finished' = insert (hd (stack dfs_aux_state)) (finished dfs_aux_state)
    in
      dfs_aux_state \<lparr>stack := stack', finished := finished'\<rparr>)" 


definition "DFS_Aux_ret_1_conds dfs_aux_state \<equiv> 
    (case (stack dfs_aux_state) of (v # stack_tl) \<Rightarrow>
       let 
         excl = (case stack_tl of [] \<Rightarrow> \<emptyset>\<^sub>N | u # _ \<Rightarrow> insert u \<emptyset>\<^sub>N)
       in
       (if ((\<N>\<^sub>G v) -\<^sub>G excl) \<inter>\<^sub>G (seen dfs_aux_state -\<^sub>G finished dfs_aux_state) \<noteq> \<emptyset>\<^sub>N then 
         True
       else 
         (if ((\<N>\<^sub>G v) -\<^sub>G (seen dfs_aux_state)) \<noteq> \<emptyset>\<^sub>N then False 
         else False))
     | _ \<Rightarrow> False
    )"

lemma DFS_Aux_ret_1_conds[call_cond_elims]:
  "DFS_Aux_ret_1_conds dfs_aux_state \<Longrightarrow> 
   \<lbrakk>\<lbrakk>\<exists>v stack_tl. stack dfs_aux_state = v # stack_tl;
    ((\<N>\<^sub>G (hd (stack dfs_aux_state))) -\<^sub>G (case (tl (stack dfs_aux_state)) of [] \<Rightarrow> \<emptyset>\<^sub>N | u # _ \<Rightarrow> insert u \<emptyset>\<^sub>N))
       \<inter>\<^sub>G (seen dfs_aux_state -\<^sub>G finished dfs_aux_state) \<noteq> \<emptyset>\<^sub>N\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> 
   P"
  by(auto simp: DFS_Aux_ret_1_conds_def split: list.splits option.splits if_splits)

lemma DFS_Aux_ret_1_condsI[call_cond_intros]:
  "\<lbrakk>\<exists>v stack_tl. stack dfs_aux_state = v # stack_tl;
    ((\<N>\<^sub>G (hd (stack dfs_aux_state))) -\<^sub>G (case (tl (stack dfs_aux_state)) of [] \<Rightarrow> \<emptyset>\<^sub>N | u # _ \<Rightarrow> insert u \<emptyset>\<^sub>N))
       \<inter>\<^sub>G (seen dfs_aux_state -\<^sub>G finished dfs_aux_state) \<noteq> \<emptyset>\<^sub>N\<rbrakk> \<Longrightarrow> DFS_Aux_ret_1_conds dfs_aux_state"
  by(auto simp: DFS_Aux_ret_1_conds_def split: list.splits option.splits if_splits)

definition "DFS_Aux_ret1 dfs_aux_state \<equiv> (dfs_aux_state \<lparr>cycle := True\<rparr>)"


definition "DFS_Aux_ret_2_conds dfs_aux_state \<equiv> 
    (case (stack dfs_aux_state) of (v # stack_tl) \<Rightarrow>
       let 
         excl = (case stack_tl of [] \<Rightarrow> \<emptyset>\<^sub>N | u # _ \<Rightarrow> insert u \<emptyset>\<^sub>N)
       in
       (if ((\<N>\<^sub>G v) -\<^sub>G excl) \<inter>\<^sub>G (seen dfs_aux_state -\<^sub>G finished dfs_aux_state) \<noteq> \<emptyset>\<^sub>N then 
         False
       else 
         (if ((\<N>\<^sub>G v) -\<^sub>G (seen dfs_aux_state)) \<noteq> \<emptyset>\<^sub>N then False 
         else False))
     | _ \<Rightarrow> True
    )"

lemma DFS_Aux_ret_2_conds[call_cond_elims]:
  "DFS_Aux_ret_2_conds dfs_aux_state \<Longrightarrow> 
   \<lbrakk>\<lbrakk>stack dfs_aux_state = []\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> 
   P"
  by(auto simp: DFS_Aux_ret_2_conds_def split: list.splits option.splits if_splits)

lemma DFS_Aux_ret_2_condsI[call_cond_intros]:
  "\<lbrakk>stack dfs_aux_state = []\<rbrakk> \<Longrightarrow> DFS_Aux_ret_2_conds dfs_aux_state"
  by(auto simp: DFS_Aux_ret_2_conds_def split: list.splits option.splits if_splits)

definition "DFS_Aux_ret2 dfs_aux_state \<equiv> dfs_aux_state"


lemma DFS_Aux_cases:
  assumes "DFS_Aux_call_1_conds dfs_aux_state \<Longrightarrow> P"
      "DFS_Aux_call_2_conds dfs_aux_state \<Longrightarrow> P"
      "DFS_Aux_ret_1_conds dfs_aux_state \<Longrightarrow> P"
      "DFS_Aux_ret_2_conds dfs_aux_state \<Longrightarrow> P"
  shows "P"
proof-
  have "DFS_Aux_call_1_conds dfs_aux_state \<or> DFS_Aux_call_2_conds dfs_aux_state \<or>
        DFS_Aux_ret_1_conds dfs_aux_state \<or> DFS_Aux_ret_2_conds dfs_aux_state"
    by (auto simp add: DFS_Aux_call_1_conds_def DFS_Aux_call_2_conds_def
                        DFS_Aux_ret_1_conds_def DFS_Aux_ret_2_conds_def
           split: list.split_asm option.split_asm if_splits)
  then show ?thesis
    using assms
    by auto
qed

lemma DFS_Aux_simps:
  assumes "DFS_Aux_dom dfs_aux_state" 
  shows"DFS_Aux_call_1_conds dfs_aux_state \<Longrightarrow> DFS_Aux dfs_aux_state = DFS_Aux (DFS_Aux_upd1 dfs_aux_state)"
      "DFS_Aux_call_2_conds dfs_aux_state \<Longrightarrow> DFS_Aux dfs_aux_state = DFS_Aux (DFS_Aux_upd2 dfs_aux_state)"
      "DFS_Aux_ret_1_conds dfs_aux_state \<Longrightarrow> DFS_Aux dfs_aux_state = DFS_Aux_ret1 dfs_aux_state"
      "DFS_Aux_ret_2_conds dfs_aux_state \<Longrightarrow> DFS_Aux dfs_aux_state = DFS_Aux_ret2 dfs_aux_state"
  by (auto simp add: DFS_Aux.psimps[OF assms] Let_def
                       DFS_Aux_call_1_conds_def DFS_Aux_upd1_def DFS_Aux_call_2_conds_def DFS_Aux_upd2_def
                       DFS_Aux_ret_1_conds_def DFS_Aux_ret1_def
                       DFS_Aux_ret_2_conds_def DFS_Aux_ret2_def
            split: list.splits option.splits if_splits )

lemma DFS_Aux_induct: 
  assumes "DFS_Aux_dom dfs_aux_state"
  assumes "\<And>dfs_aux_state. \<lbrakk>DFS_Aux_dom dfs_aux_state;
                        DFS_Aux_call_1_conds dfs_aux_state \<Longrightarrow> P (DFS_Aux_upd1 dfs_aux_state);
                        DFS_Aux_call_2_conds dfs_aux_state \<Longrightarrow> P (DFS_Aux_upd2 dfs_aux_state)\<rbrakk> \<Longrightarrow> P dfs_aux_state"
  shows "P dfs_aux_state"
  apply(rule DFS_Aux.pinduct[OF assms(1)])
  apply(rule assms(2)[simplified DFS_Aux_call_1_conds_def DFS_Aux_upd1_def DFS_Aux_call_2_conds_def DFS_Aux_upd2_def])
  by (auto simp: Let_def split: list.splits option.splits if_splits)

lemma DFS_Aux_domintros: 
  assumes "DFS_Aux_call_1_conds dfs_aux_state \<Longrightarrow> DFS_Aux_dom (DFS_Aux_upd1 dfs_aux_state)"
  assumes "DFS_Aux_call_2_conds dfs_aux_state \<Longrightarrow> DFS_Aux_dom (DFS_Aux_upd2 dfs_aux_state)"
  shows "DFS_Aux_dom dfs_aux_state"
proof(rule DFS_Aux.domintros, goal_cases)
  case (1 x21 x22)
  then show ?case
    using assms(1)[simplified DFS_Aux_call_1_conds_def DFS_Aux_upd1_def]
    by (force simp: Let_def split: list.splits option.splits if_splits)
next
  case (2 x21 x22)
  then show ?case
    using assms(2)[simplified DFS_Aux_call_2_conds_def DFS_Aux_upd2_def]
    by (force split: list.splits option.splits if_splits)
qed




definition "dfs_tree dfs_aux_state \<equiv>
  set (edges_of_vwalk (rev (stack dfs_aux_state))) \<union> set (edges_of_vwalk (stack dfs_aux_state)) \<union>
  {(x, y). (x, y) \<in> (Graph.digraph_abs G) \<and> x \<in> set (stack dfs_aux_state) \<and> y \<in> t_set (finished dfs_aux_state)} \<union>
  {(x, y). (x, y) \<in> (Graph.digraph_abs G) \<and> x \<in> t_set (finished dfs_aux_state) \<and> y \<in> set (stack dfs_aux_state)} \<union>
  {(x, y). (x, y) \<in> (Graph.digraph_abs G) \<and> x \<in> t_set (finished dfs_aux_state) \<and> y \<in> t_set (finished dfs_aux_state)}"


definition "invar_1 dfs_aux_state \<equiv> neighb_inv (seen dfs_aux_state) \<and> neighb_inv (finished dfs_aux_state)"

definition "invar_2 dfs_aux_state \<equiv> (Vwalk.vwalk (Graph.digraph_abs G) (rev (stack dfs_aux_state)))"

definition "invar_s_in_stack dfs_aux_state \<equiv>
  (stack (dfs_aux_state) \<noteq> [] \<longrightarrow> last (stack dfs_aux_state) = s)"

definition "invar_seen_stack_finished dfs_aux_state \<longleftrightarrow> 
    distinct (stack dfs_aux_state)
    \<and> set (stack dfs_aux_state) \<subseteq> t_set (seen dfs_aux_state)
    \<and> t_set (finished dfs_aux_state) \<subseteq> t_set (seen dfs_aux_state)
    \<and> t_set (finished dfs_aux_state) = t_set (seen dfs_aux_state) - set (stack dfs_aux_state)
    \<and> t_set (seen dfs_aux_state) \<subseteq> dVs (Graph.digraph_abs G)"

definition "invar_finished_neighbs dfs_aux_state \<equiv>
  (\<forall>v \<in> t_set (finished (dfs_aux_state)). t_set (\<N>\<^sub>G v) \<subseteq> t_set (seen (dfs_aux_state)))"


definition "invar_seen_reachable dfs_aux_state \<equiv>
  (\<forall>v \<in> t_set (seen dfs_aux_state). \<exists>p. awalk (Graph.digraph_abs G) s p v)"

definition "invar_visited_through_seen dfs_aux_state \<equiv>
  (\<forall>v \<in> t_set (seen dfs_aux_state). (\<forall>w \<in> dVs (Graph.digraph_abs G) - t_set (seen dfs_aux_state).
     (\<forall>p. Vwalk.vwalk_bet (Graph.digraph_abs G) v p w \<and> distinct p \<longrightarrow> (set p \<inter> set (stack dfs_aux_state) \<noteq> {}))))"

definition "invar_dfs_tree_seen_1 dfs_aux_state \<equiv> 
  (dfs_tree dfs_aux_state) = {} \<longrightarrow> t_set (seen dfs_aux_state) = {s}"

definition "invar_dfs_tree_seen_2 dfs_aux_state \<equiv> 
  (dfs_tree dfs_aux_state) \<noteq> {} \<longrightarrow> dVs (dfs_tree dfs_aux_state) = t_set (seen dfs_aux_state)"

(* If the cycle attribute is false, there does not exist a cycle in dfs_tree *)
definition "invar_cycle_false dfs_aux_state \<equiv> \<not>cycle dfs_aux_state \<longrightarrow> (\<nexists>c. cycle' (dfs_tree dfs_aux_state) c)"

(* If the cycle attribute is true, there exists a cycle in the graph *)
definition "invar_cycle_true dfs_aux_state \<equiv> cycle dfs_aux_state \<longrightarrow> (\<exists>c. cycle' (Graph.digraph_abs G) c)"

definition "call_1_measure dfs_aux_state \<equiv> card (dVs (Graph.digraph_abs G) -  t_set (seen dfs_aux_state))"

definition "call_2_measure dfs_aux_state \<equiv> card (set (stack dfs_aux_state))"

definition
  "DFS_Aux_term_rel' \<equiv> (call_1_measure) <*mlex*> (call_2_measure) <*mlex*> {}"

definition "initial_state \<equiv> \<lparr>stack = [s], seen = insert s \<emptyset>\<^sub>N, finished = \<emptyset>\<^sub>N, cycle = False\<rparr>"

lemmas [code] = initial_state_def

context
includes  Graph.adj.automation and Graph.neighb.set.automation
assumes DFS_Aux_axioms 
begin

declare set_ops.set_union[simp] set_ops.set_inter[simp] 
        set_ops.set_diff[simp] set_ops.invar_union[simp]
        set_ops.invar_inter[simp] set_ops.invar_diff[simp]

lemma graph_inv[simp,intro]:
          "Graph.graph_inv G"
          "Graph.finite_graph G"
          "Graph.finite_neighbs"
  using \<open>DFS_Aux_axioms\<close>
  by (auto simp: DFS_Aux_axioms_def)

lemma s_in_G[simp,intro]: "s \<in> dVs (Graph.digraph_abs G)"
  using \<open>DFS_Aux_axioms\<close>
  by (auto simp: DFS_Aux_axioms_def)

lemma finite_neighbourhoods[simp]:                                                 
          "finite (t_set N)"
  using graph_inv(3)
  by fastforce

lemma graph_symmetric[simp]:
  "(x, y) \<in> (Graph.digraph_abs G) \<Longrightarrow> (y, x) \<in> (Graph.digraph_abs G)"
  using \<open>DFS_Aux_axioms\<close>
  by (auto simp: DFS_Aux_axioms_def)

lemma graph_no_self_loops1[simp]:
  "x \<in> dVs (Graph.digraph_abs G) \<Longrightarrow> (x, x) \<notin> Graph.digraph_abs G"
  using \<open>DFS_Aux_axioms\<close>
  by (auto simp: DFS_Aux_axioms_def)

lemma graph_no_self_loops2[simp]:
  "(x, y) \<in> (Graph.digraph_abs G) \<Longrightarrow> x \<noteq> y"
  using graph_no_self_loops1 by blast

lemmas simps[simp] = Graph.neighbourhood_abs[OF graph_inv(1)] Graph.are_connected_abs[OF graph_inv(1)]



lemma invar_1_props[invar_props_elims]:
  "invar_1 dfs_aux_state \<Longrightarrow>
     (\<lbrakk>neighb_inv (seen dfs_aux_state); neighb_inv (finished dfs_aux_state)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
     P"
  by (auto simp: invar_1_def)

lemma invar_1_intro[invar_props_intros]:
  "\<lbrakk>neighb_inv (seen dfs_aux_state); neighb_inv (finished dfs_aux_state)\<rbrakk> \<Longrightarrow> invar_1 dfs_aux_state"
  by (auto simp: invar_1_def)

lemma invar_1_holds_upd1[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_call_1_conds dfs_aux_state; invar_1 dfs_aux_state\<rbrakk> \<Longrightarrow> invar_1 (DFS_Aux_upd1 dfs_aux_state)"
  by (auto simp: Let_def DFS_Aux_upd1_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_1_holds_upd2[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_call_2_conds dfs_aux_state; invar_1 dfs_aux_state\<rbrakk> \<Longrightarrow> invar_1 (DFS_Aux_upd2 dfs_aux_state)"
  by (auto simp: DFS_Aux_upd2_def elim!: invar_props_elims intro: invar_props_intros)

lemma invar_1_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_ret_1_conds dfs_aux_state; invar_1 dfs_aux_state\<rbrakk> \<Longrightarrow> invar_1 (DFS_Aux_ret1 dfs_aux_state)"
  by (auto simp: DFS_Aux_ret1_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_1_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_ret_2_conds dfs_aux_state; invar_1 dfs_aux_state\<rbrakk> \<Longrightarrow> invar_1 (DFS_Aux_ret2 dfs_aux_state)"
  by (auto simp: DFS_Aux_ret2_def elim!: invar_props_elims intro: invar_props_intros)

lemma invar_1_holds[invar_holds_intros]: 
   assumes "DFS_Aux_dom dfs_aux_state" "invar_1 dfs_aux_state"
   shows "invar_1 (DFS_Aux dfs_aux_state)"
  using assms(2)
proof(induction rule: DFS_Aux_induct[OF assms(1)])
  case IH: (1 dfs_aux_state)
  show ?case
    apply(rule DFS_Aux_cases[where dfs_aux_state = dfs_aux_state])
    by (auto intro!: IH(2-4) invar_holds_intros simp: DFS_Aux_simps[OF IH(1)])
qed

lemma invar_2_props[invar_props_elims]:
  "invar_2 dfs_aux_state \<Longrightarrow>
     (\<lbrakk>Vwalk.vwalk (Graph.digraph_abs G) (rev (stack dfs_aux_state))\<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
     P"
  by (auto simp: invar_2_def)

lemma invar_2_intro[invar_props_intros]:
  "\<lbrakk>Vwalk.vwalk (Graph.digraph_abs G) (rev (stack dfs_aux_state))\<rbrakk> \<Longrightarrow> invar_2 dfs_aux_state"
  by (auto simp: invar_2_def)

lemma invar_2_holds_upd1[invar_holds_intros]:
  assumes "DFS_Aux_call_1_conds dfs_aux_state" "invar_1 dfs_aux_state" "invar_2 dfs_aux_state"
  shows "invar_2 (DFS_Aux_upd1 dfs_aux_state)"
    using assms graph_inv 
    by (force simp: Let_def DFS_Aux_upd1_def elim!: call_cond_elims elim!: invar_props_elims
         intro!: Vwalk.vwalk_append2 invar_props_intros)

lemma invar_2_holds_upd2[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_call_2_conds dfs_aux_state; invar_2 dfs_aux_state\<rbrakk> \<Longrightarrow>
  invar_2 (DFS_Aux_upd2 dfs_aux_state)"
  by (auto simp: DFS_Aux_upd2_def dest!: append_vwalk_pref elim!: invar_props_elims intro!: invar_props_intros elim: call_cond_elims)

lemma invar_2_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_ret_1_conds dfs_aux_state; invar_2 dfs_aux_state\<rbrakk> \<Longrightarrow> invar_2 (DFS_Aux_ret1 dfs_aux_state)"
  by (auto simp: DFS_Aux_ret1_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_2_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_ret_2_conds dfs_aux_state; invar_2 dfs_aux_state\<rbrakk> \<Longrightarrow> invar_2 (DFS_Aux_ret2 dfs_aux_state)"
  by (auto simp: DFS_Aux_ret2_def elim!: invar_props_elims intro: invar_props_intros)

lemma invar_2_holds[invar_holds_intros]: 
   assumes "DFS_Aux_dom dfs_aux_state" "invar_1 dfs_aux_state" "invar_2 dfs_aux_state"
   shows "invar_2 (DFS_Aux dfs_aux_state)"
  using assms(2-)
proof(induction rule: DFS_Aux_induct[OF assms(1)])
  case IH: (1 dfs_aux_state)
  show ?case
    apply(rule DFS_Aux_cases[where dfs_aux_state = dfs_aux_state])
    by (auto intro!: IH(2-5) invar_holds_intros simp: DFS_Aux_simps[OF IH(1)])
qed


lemma invar_s_in_stack_props[invar_props_elims]:
  "invar_s_in_stack dfs_aux_state \<Longrightarrow>
     (\<lbrakk>(stack (dfs_aux_state) \<noteq> [] \<Longrightarrow> last (stack dfs_aux_state) = s)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
     P"
  by (auto simp: invar_s_in_stack_def)

lemma invar_s_in_stack_intro[invar_props_intros]:
  "\<lbrakk>(stack (dfs_aux_state) \<noteq> [] \<Longrightarrow> last (stack dfs_aux_state) = s)\<rbrakk> \<Longrightarrow> invar_s_in_stack dfs_aux_state"
  by (auto simp: invar_s_in_stack_def)

lemma invar_s_in_stack_holds_upd1[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_call_1_conds dfs_aux_state; invar_s_in_stack dfs_aux_state\<rbrakk> \<Longrightarrow>
  invar_s_in_stack (DFS_Aux_upd1 dfs_aux_state)"
  by (force simp: Let_def DFS_Aux_upd1_def dest!: append_vwalk_pref elim!: call_cond_elims
            elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_s_in_stack_holds_upd2[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_call_2_conds dfs_aux_state; invar_s_in_stack dfs_aux_state\<rbrakk> \<Longrightarrow>
  invar_s_in_stack (DFS_Aux_upd2 dfs_aux_state)"
  by (auto simp: DFS_Aux_upd2_def dest!: append_vwalk_pref elim!: invar_props_elims intro!: invar_props_intros elim: call_cond_elims)

lemma invar_s_in_stack_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_ret_1_conds dfs_aux_state; invar_s_in_stack dfs_aux_state\<rbrakk> \<Longrightarrow>
  invar_s_in_stack (DFS_Aux_ret1 dfs_aux_state)"
  by (auto simp: DFS_Aux_ret1_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_s_in_stack_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_ret_2_conds dfs_aux_state; invar_s_in_stack dfs_aux_state\<rbrakk> \<Longrightarrow>
  invar_s_in_stack (DFS_Aux_ret2 dfs_aux_state)"
  by (auto simp: DFS_Aux_ret2_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_s_in_stack_holds[invar_holds_intros]: 
   assumes "DFS_Aux_dom dfs_aux_state" "invar_1 dfs_aux_state" "invar_s_in_stack dfs_aux_state"
   shows "invar_s_in_stack (DFS_Aux dfs_aux_state)"
  using assms(2-)
proof(induction rule: DFS_Aux_induct[OF assms(1)])
  case IH: (1 dfs_aux_state)
  show ?case
    apply(rule DFS_Aux_cases[where dfs_aux_state = dfs_aux_state])
    by (auto intro!: IH(2-5) invar_holds_intros simp: DFS_Aux_simps[OF IH(1)])
qed


lemma invar_seen_stack_finished_props[invar_props_elims]:
  "invar_seen_stack_finished dfs_aux_state \<Longrightarrow>
     (\<lbrakk>distinct (stack dfs_aux_state); set (stack dfs_aux_state) \<subseteq> t_set (seen dfs_aux_state);
      t_set (finished dfs_aux_state) \<subseteq> t_set (seen dfs_aux_state); 
      t_set (finished dfs_aux_state) = t_set (seen dfs_aux_state) - set (stack dfs_aux_state);
      t_set (seen dfs_aux_state) \<subseteq> dVs (Graph.digraph_abs G)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
     P"
  by (auto simp: invar_seen_stack_finished_def)

lemma invar_seen_stack_finished_intro[invar_props_intros]:
  "\<lbrakk>distinct (stack dfs_aux_state); set (stack dfs_aux_state) \<subseteq> t_set (seen dfs_aux_state);
      t_set (finished dfs_aux_state) \<subseteq> t_set (seen dfs_aux_state); 
      t_set (finished dfs_aux_state) = t_set (seen dfs_aux_state) - set (stack dfs_aux_state);
      t_set (seen dfs_aux_state) \<subseteq> dVs (Graph.digraph_abs G)\<rbrakk> \<Longrightarrow> invar_seen_stack_finished dfs_aux_state"
  by (auto simp: invar_seen_stack_finished_def)

lemma invar_seen_stack_finished_holds_upd1[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_call_1_conds dfs_aux_state; invar_1 dfs_aux_state; invar_seen_stack_finished dfs_aux_state\<rbrakk> \<Longrightarrow> 
    invar_seen_stack_finished (DFS_Aux_upd1 dfs_aux_state)"
proof (intro invar_props_intros, goal_cases)
  case 1
  let ?v = "hd (stack dfs_aux_state)"
  let ?w = "sel ((\<N>\<^sub>G ?v) -\<^sub>G (seen dfs_aux_state))"

  have "?w \<in> t_set (\<N>\<^sub>G ?v) - t_set (seen dfs_aux_state)"
    using \<open>invar_1 dfs_aux_state\<close> \<open>DFS_Aux_call_1_conds dfs_aux_state\<close>
    by (auto elim!: invar_props_elims call_cond_elims)
  then have "?w \<notin> set (stack dfs_aux_state)"
    using \<open>invar_seen_stack_finished dfs_aux_state\<close>
    by (auto elim!: invar_props_elims)
  moreover have "(stack (DFS_Aux_upd1 dfs_aux_state)) = ?w # stack dfs_aux_state"
    by (auto simp add: DFS_Aux_upd1_def Let_def)
  ultimately show ?case
    using \<open>invar_seen_stack_finished dfs_aux_state\<close>
    by (auto elim!: invar_props_elims)
next
  case 2
  then show ?case
  by (force simp: Let_def DFS_Aux_upd1_def elim!: call_cond_elims
            elim!: invar_props_elims intro!: invar_props_intros)
next
  case 3
  then show ?case
  by (force simp: Let_def DFS_Aux_upd1_def elim!: call_cond_elims
            elim!: invar_props_elims intro!: invar_props_intros)
next
  case 4
  let ?v = "hd (stack dfs_aux_state)"
  let ?w = "sel ((\<N>\<^sub>G ?v) -\<^sub>G (seen dfs_aux_state))"
  have "set (stack (DFS_Aux_upd1 dfs_aux_state)) = {?w} \<union> set (stack dfs_aux_state)"
    by (auto simp add: DFS_Aux_upd1_def Let_def)
  moreover have "t_set (seen (DFS_Aux_upd1 dfs_aux_state)) = {?w} \<union> t_set (seen dfs_aux_state)"
    using \<open>invar_1 dfs_aux_state\<close>
    by (auto simp add: DFS_Aux_upd1_def Let_def elim!: invar_props_elims)
  moreover have "?w \<in> t_set (\<N>\<^sub>G ?v) - t_set (seen dfs_aux_state)"
    using \<open>invar_1 dfs_aux_state\<close> \<open>DFS_Aux_call_1_conds dfs_aux_state\<close>
    by (auto elim!: invar_props_elims call_cond_elims)
  ultimately show ?case
    using \<open>invar_seen_stack_finished dfs_aux_state\<close>
    by (auto simp add: DFS_Aux_upd1_def Let_def elim!: invar_props_elims)
next
  case 5
  let ?v = "hd (stack dfs_aux_state)"
  let ?w = "sel ((\<N>\<^sub>G ?v) -\<^sub>G (seen dfs_aux_state))"
  have "?w \<in> t_set (\<N>\<^sub>G ?v) - t_set (seen dfs_aux_state)"
    using \<open>invar_1 dfs_aux_state\<close> \<open>DFS_Aux_call_1_conds dfs_aux_state\<close>
    by (auto elim!: invar_props_elims call_cond_elims)
  then have "?w \<in> dVs (Graph.digraph_abs G)"
    by blast
  moreover have "t_set (seen (DFS_Aux_upd1 dfs_aux_state)) = {?w} \<union> t_set (seen dfs_aux_state)"
    using \<open>invar_1 dfs_aux_state\<close>
    by (auto simp add: DFS_Aux_upd1_def Let_def elim!: invar_props_elims)
  ultimately show ?case
    using \<open>invar_seen_stack_finished dfs_aux_state\<close>
    by (auto simp add: DFS_Aux_upd1_def Let_def elim!: invar_props_elims)
qed

lemma invar_seen_stack_finished_holds_upd2[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_call_2_conds dfs_aux_state; invar_1 dfs_aux_state; invar_seen_stack_finished dfs_aux_state\<rbrakk> \<Longrightarrow> 
    invar_seen_stack_finished (DFS_Aux_upd2 dfs_aux_state)"
  by (force simp: Let_def DFS_Aux_upd2_def elim!: call_cond_elims
            elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_seen_stack_finished_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_ret_1_conds dfs_aux_state; invar_seen_stack_finished dfs_aux_state\<rbrakk> \<Longrightarrow> 
    invar_seen_stack_finished (DFS_Aux_ret1 dfs_aux_state)"
  by (force simp: Let_def DFS_Aux_ret1_def elim!: call_cond_elims
            elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_seen_stack_finished_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_ret_2_conds dfs_aux_state; invar_seen_stack_finished dfs_aux_state\<rbrakk> \<Longrightarrow> 
    invar_seen_stack_finished (DFS_Aux_ret2 dfs_aux_state)"
  by (force simp: Let_def DFS_Aux_ret2_def elim!: call_cond_elims
            elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_seen_stack_finished_holds[invar_holds_intros]: 
   assumes "DFS_Aux_dom dfs_aux_state" "invar_1 dfs_aux_state" "invar_seen_stack_finished dfs_aux_state"
   shows "invar_seen_stack_finished (DFS_Aux dfs_aux_state)"
  using assms(2-)
proof(induction rule: DFS_Aux_induct[OF assms(1)])
  case IH: (1 dfs_aux_state)
  show ?case
    apply(rule DFS_Aux_cases[where dfs_aux_state = dfs_aux_state])
    by (auto intro!: IH(2-5) invar_holds_intros simp: DFS_Aux_simps[OF IH(1)])
qed


lemma invar_finished_neighbs_props[invar_props_elims]:
  "invar_finished_neighbs dfs_aux_state \<Longrightarrow>
     (\<lbrakk>\<And>v. v \<in> t_set (finished (dfs_aux_state)) \<Longrightarrow> t_set (\<N>\<^sub>G v) \<subseteq> t_set (seen (dfs_aux_state))\<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
     P"
  by (auto simp: invar_finished_neighbs_def)

lemma invar_finished_neighbs_intro[invar_props_intros]:
  "\<lbrakk>\<And>v. v \<in> t_set (finished (dfs_aux_state)) \<Longrightarrow> t_set (\<N>\<^sub>G v) \<subseteq> t_set (seen (dfs_aux_state))\<rbrakk> \<Longrightarrow>
    invar_finished_neighbs dfs_aux_state"
  by (auto simp: invar_finished_neighbs_def)

lemma invar_finished_neighbs_holds_upd1[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_call_1_conds dfs_aux_state; invar_1 dfs_aux_state; invar_finished_neighbs dfs_aux_state\<rbrakk> \<Longrightarrow> 
    invar_finished_neighbs (DFS_Aux_upd1 dfs_aux_state)"
  by (force simp: Let_def DFS_Aux_upd1_def elim!: call_cond_elims
            elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_finished_neighbs_holds_upd2[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_call_2_conds dfs_aux_state; invar_1 dfs_aux_state; invar_finished_neighbs dfs_aux_state\<rbrakk> \<Longrightarrow> 
    invar_finished_neighbs (DFS_Aux_upd2 dfs_aux_state)"
proof (intro invar_props_intros, goal_cases)
  case (1 v)
  let ?v = "hd (stack dfs_aux_state)"

  have "t_set (finished (DFS_Aux_upd2 dfs_aux_state)) = {?v} \<union> t_set (finished dfs_aux_state)"
    using \<open>invar_1 dfs_aux_state\<close>
    by (auto simp add: DFS_Aux_upd2_def Let_def elim!: invar_props_elims)
  moreover have "t_set (\<N>\<^sub>G ?v) \<subseteq> t_set (seen (dfs_aux_state))"
    using \<open>DFS_Aux_call_2_conds dfs_aux_state\<close> \<open>invar_1 dfs_aux_state\<close> 
    by (force elim!: call_cond_elims invar_props_elims)
  moreover have "t_set (seen (DFS_Aux_upd2 dfs_aux_state)) = t_set (seen dfs_aux_state)"
    by (auto simp add: DFS_Aux_upd2_def Let_def)
  ultimately show ?case
    using \<open>invar_finished_neighbs dfs_aux_state\<close> \<open>v \<in> t_set (finished (DFS_Aux_upd2 dfs_aux_state))\<close>
    by (force elim!: invar_props_elims)
qed

lemma invar_finished_neighbs_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_ret_1_conds dfs_aux_state; invar_finished_neighbs dfs_aux_state\<rbrakk> \<Longrightarrow> 
    invar_finished_neighbs (DFS_Aux_ret1 dfs_aux_state)"
  by (force simp: Let_def DFS_Aux_ret1_def elim!: call_cond_elims
            elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_finished_neighbs_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_ret_2_conds dfs_aux_state; invar_finished_neighbs dfs_aux_state\<rbrakk> \<Longrightarrow> 
    invar_finished_neighbs (DFS_Aux_ret2 dfs_aux_state)"
  by (force simp: Let_def DFS_Aux_ret2_def elim!: call_cond_elims
            elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_finished_neighbs_holds[invar_holds_intros]: 
   assumes "DFS_Aux_dom dfs_aux_state" "invar_1 dfs_aux_state" "invar_finished_neighbs dfs_aux_state"
   shows "invar_finished_neighbs (DFS_Aux dfs_aux_state)"
  using assms(2-)
proof(induction rule: DFS_Aux_induct[OF assms(1)])
  case IH: (1 dfs_aux_state)
  show ?case
    apply(rule DFS_Aux_cases[where dfs_aux_state = dfs_aux_state])
    by (auto intro!: IH(2-5) invar_holds_intros simp: DFS_Aux_simps[OF IH(1)])
qed



lemma invar_dfs_tree_seen_1_props[invar_props_elims]:
  "invar_dfs_tree_seen_1 dfs_aux_state \<Longrightarrow>
     (\<lbrakk>(dfs_tree dfs_aux_state) = {} \<Longrightarrow> t_set (seen dfs_aux_state) = {s}\<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
     P"
  by (auto simp: invar_dfs_tree_seen_1_def)

lemma invar_dfs_tree_seen_1_intro[invar_props_intros]:
  "\<lbrakk>(dfs_tree dfs_aux_state) = {} \<Longrightarrow> t_set (seen dfs_aux_state) = {s}\<rbrakk> \<Longrightarrow>
    invar_dfs_tree_seen_1 dfs_aux_state"
  by (auto simp: invar_dfs_tree_seen_1_def)

lemma invar_dfs_tree_seen_1_holds_upd1[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_call_1_conds dfs_aux_state; invar_1 dfs_aux_state; invar_seen_stack_finished dfs_aux_state;
    invar_finished_neighbs dfs_aux_state; invar_dfs_tree_seen_1 dfs_aux_state\<rbrakk> \<Longrightarrow> 
    invar_dfs_tree_seen_1 (DFS_Aux_upd1 dfs_aux_state)"
proof (intro invar_props_intros, goal_cases)
  case 1
  let ?v = "hd (stack dfs_aux_state)"
  let ?w = "sel ((\<N>\<^sub>G ?v) -\<^sub>G (seen dfs_aux_state))"

  have stack_expr: "(stack dfs_aux_state) = hd (stack dfs_aux_state) # tl (stack dfs_aux_state)"
    using \<open>DFS_Aux_call_1_conds dfs_aux_state\<close>
    by (auto elim!: call_cond_elims)
  have w_not_in_seen: "?w \<notin> set (stack dfs_aux_state) \<union> t_set (finished dfs_aux_state)"
    using \<open>invar_1 dfs_aux_state\<close> \<open>invar_seen_stack_finished dfs_aux_state\<close> \<open>DFS_Aux_call_1_conds dfs_aux_state\<close>
    by (force elim!: invar_props_elims call_cond_elims)
  have finished_neighbs: "\<forall>(x, y) \<in> (Graph.digraph_abs G).
    (x \<in> t_set (finished dfs_aux_state) \<longrightarrow> y \<in> set (stack dfs_aux_state) \<union> t_set (finished dfs_aux_state)) \<and>
    (y \<in> t_set (finished dfs_aux_state) \<longrightarrow> x \<in> set (stack dfs_aux_state) \<union> t_set (finished dfs_aux_state))"
    using \<open>invar_seen_stack_finished dfs_aux_state\<close> \<open>invar_finished_neighbs dfs_aux_state\<close>  
    graph_symmetric Graph.digraph_abs_def
    by (fastforce elim!: invar_props_elims)
  from dfs_tree_aux1[OF stack_expr w_not_in_seen finished_neighbs]
    have dfs_tree_expr:
    "dfs_tree (DFS_Aux_upd1 dfs_aux_state) =
    {(?v, ?w), (?w, ?v)} \<union> dfs_tree dfs_aux_state"
    unfolding dfs_tree_def by (auto simp add: DFS_Aux_upd1_def Let_def)
  with \<open>dfs_tree (DFS_Aux_upd1 dfs_aux_state) = {}\<close> show ?case by blast
qed

lemma invar_dfs_tree_seen_1_holds_upd2[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_call_2_conds dfs_aux_state; invar_1 dfs_aux_state; invar_2 dfs_aux_state;
    invar_seen_stack_finished dfs_aux_state;
    invar_dfs_tree_seen_1 dfs_aux_state\<rbrakk> \<Longrightarrow>
    invar_dfs_tree_seen_1 (DFS_Aux_upd2 dfs_aux_state)"
proof (intro invar_props_intros, goal_cases)
  case 1
  let ?v = "hd (stack dfs_aux_state)"

  have dfs_tree_expr: "dfs_tree (DFS_Aux_upd2 dfs_aux_state) = dfs_tree dfs_aux_state"
  proof (cases "tl (stack dfs_aux_state)")
    case Nil
    have stack_expr: "stack dfs_aux_state = ?v # (tl (stack dfs_aux_state))"
      using \<open>DFS_Aux_call_2_conds dfs_aux_state\<close>
      by (force elim!: call_cond_elims)
    from graph_no_self_loops2 have
      "\<forall>(x, y) \<in> (Graph.digraph_abs G). x \<noteq> y" by blast

    have stack_upd_expr: "stack (DFS_Aux_upd2 dfs_aux_state) = tl (stack dfs_aux_state)"
      by (auto simp add: DFS_Aux_upd2_def)
    have finished_upd_expr:
      "t_set (finished (DFS_Aux_upd2 dfs_aux_state)) = Set.insert (hd (stack dfs_aux_state)) (t_set (finished dfs_aux_state))"
      using \<open>invar_1 dfs_aux_state\<close>
      by (auto simp add: DFS_Aux_upd2_def elim!: invar_props_elims)

    show ?thesis
      unfolding dfs_tree_def
      apply (subst stack_upd_expr)+
      apply (subst finished_upd_expr)+
      using dfs_tree_aux2_1[of "stack dfs_aux_state" "?v" "tl (stack dfs_aux_state)"
      "Graph.digraph_abs G" "t_set (finished dfs_aux_state)", OF stack_expr Nil \<open>\<forall>(x, y) \<in> (Graph.digraph_abs G). x \<noteq> y\<close>] 
      by blast
  next
    case (Cons u l_tl_tl)
    have stack_expr: "stack dfs_aux_state = ?v # (tl (stack dfs_aux_state))"
      using \<open>DFS_Aux_call_2_conds dfs_aux_state\<close>
      by (force elim!: call_cond_elims)
    from graph_no_self_loops2 have
      "\<forall>(x, y) \<in> (Graph.digraph_abs G). x \<noteq> y" by blast

    from Cons have "stack dfs_aux_state = [?v, u] @ tl (tl (stack dfs_aux_state))"
      using stack_expr by fastforce
    have "Vwalk.vwalk (Graph.digraph_abs G) (rev (stack dfs_aux_state))"
      using \<open>invar_2 dfs_aux_state\<close>
      by (force elim!: invar_props_elims)
    with vwalk_rev graph_symmetric
      have "Vwalk.vwalk (Graph.digraph_abs G) (stack dfs_aux_state)"
      by (metis (no_types, lifting) case_prodI2 rev_rev_ident)
    have "(?v, u) \<in> (Graph.digraph_abs G)"
      by (metis \<open>Vwalk.vwalk (Graph.digraph_abs G) (stack dfs_aux_state)\<close> local.Cons stack_expr vwalk_2)
    then have edges_in_G: "{(u, ?v), (?v, u)} \<subseteq> (Graph.digraph_abs G)" by auto

    have "set (stack dfs_aux_state) \<subseteq> t_set (seen dfs_aux_state)"
      "t_set (finished dfs_aux_state) \<subseteq> t_set (seen dfs_aux_state)"
      "t_set (finished dfs_aux_state) = t_set (seen dfs_aux_state) - set (stack dfs_aux_state)"
      using \<open>invar_seen_stack_finished dfs_aux_state\<close> stack_expr
      by (auto elim!: invar_props_elims)
    then have
      sets_disjoint: "set (tl (stack dfs_aux_state)) \<inter> t_set (finished dfs_aux_state) = {}"
      using Vwalk.list_set_tl by fastforce

    have "t_set ((\<N>\<^sub>G ?v) -\<^sub>G (insert u \<emptyset>\<^sub>N)) \<inter> (t_set (seen dfs_aux_state -\<^sub>G finished dfs_aux_state)) = {}"
      using \<open>invar_1 dfs_aux_state\<close> \<open>DFS_Aux_call_2_conds dfs_aux_state\<close> Cons
      by (fastforce elim!: call_cond_elims invar_props_elims)
    then have "(t_set (\<N>\<^sub>G ?v) - {u}) \<inter> (t_set (seen dfs_aux_state) - t_set (finished dfs_aux_state)) = {}"
      using \<open>invar_1 dfs_aux_state\<close>
      by (force elim!: invar_props_elims)
    moreover have "(t_set (\<N>\<^sub>G ?v) - t_set (seen dfs_aux_state)) = {}"
      using \<open>DFS_Aux_call_2_conds dfs_aux_state\<close> \<open>invar_1 dfs_aux_state\<close> Cons
      by (force elim!: call_cond_elims invar_props_elims)
    ultimately have "(t_set (\<N>\<^sub>G ?v) - {u}) \<subseteq> t_set (finished dfs_aux_state)"
      by blast
    with graph_symmetric
      have v_neighbs: "\<forall>(x, y) \<in> (Graph.digraph_abs G).
        (x = ?v \<longrightarrow> y \<noteq> u \<longrightarrow> y \<in> t_set (finished dfs_aux_state)) \<and>
        (y = ?v \<longrightarrow> x \<noteq> u \<longrightarrow> x \<in> t_set (finished dfs_aux_state))"
      by blast

    have stack_upd_expr: "stack (DFS_Aux_upd2 dfs_aux_state) = tl (stack dfs_aux_state)"
      by (auto simp add: DFS_Aux_upd2_def)
    have finished_upd_expr:
      "t_set (finished (DFS_Aux_upd2 dfs_aux_state)) = Set.insert (hd (stack dfs_aux_state)) (t_set (finished dfs_aux_state))"
      using \<open>invar_1 dfs_aux_state\<close>
      by (auto simp add: DFS_Aux_upd2_def elim!: invar_props_elims)

    show ?thesis
      unfolding dfs_tree_def
      apply (subst stack_upd_expr)+
      apply (subst finished_upd_expr)+
      using dfs_tree_aux2_2[OF stack_expr Cons \<open>\<forall>(x, y) \<in> (Graph.digraph_abs G). x \<noteq> y\<close> edges_in_G
      sets_disjoint v_neighbs]
      by auto
  qed

  have seen_expr: "t_set (seen (DFS_Aux_upd2 dfs_aux_state)) = t_set (seen (dfs_aux_state))" 
    by (auto simp add: DFS_Aux_upd2_def Let_def)

  with dfs_tree_expr \<open>dfs_tree (DFS_Aux_upd2 dfs_aux_state) = {}\<close> show ?case
    using \<open>invar_dfs_tree_seen_1 dfs_aux_state\<close>  
    by (force elim!: invar_props_elims)
qed

lemma invar_dfs_tree_seen_1_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_ret_1_conds dfs_aux_state; invar_dfs_tree_seen_1 dfs_aux_state\<rbrakk> \<Longrightarrow> 
    invar_dfs_tree_seen_1 (DFS_Aux_ret1 dfs_aux_state)"
proof (intro invar_props_intros, goal_cases)
  case 1
  have "dfs_tree (DFS_Aux_ret1 dfs_aux_state) = dfs_tree dfs_aux_state"
    unfolding dfs_tree_def
    by (auto simp add: DFS_Aux_ret1_def)
  with \<open>dfs_tree (DFS_Aux_ret1 dfs_aux_state) = {}\<close> \<open>invar_dfs_tree_seen_1 dfs_aux_state\<close>
    have "t_set (seen dfs_aux_state) = {s}"
    by (force elim!: invar_props_elims)
  then show ?case
    by (auto simp add: DFS_Aux_ret1_def)
qed

lemma invar_dfs_tree_seen_1_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_ret_2_conds dfs_aux_state; invar_dfs_tree_seen_1 dfs_aux_state\<rbrakk> \<Longrightarrow> 
    invar_dfs_tree_seen_1 (DFS_Aux_ret2 dfs_aux_state)"
  unfolding DFS_Aux_ret2_def dfs_tree_def by simp

lemma invar_dfs_tree_seen_1_holds[invar_holds_intros]: 
   assumes "DFS_Aux_dom dfs_aux_state" "invar_1 dfs_aux_state" "invar_2 dfs_aux_state"
     "invar_seen_stack_finished dfs_aux_state" "invar_finished_neighbs dfs_aux_state"
     "invar_dfs_tree_seen_1 dfs_aux_state"
   shows "invar_dfs_tree_seen_1 (DFS_Aux dfs_aux_state)"
  using assms(2-)
proof(induction rule: DFS_Aux_induct[OF assms(1)])
  case IH: (1 dfs_aux_state)
  show ?case
    apply(rule DFS_Aux_cases[where dfs_aux_state = dfs_aux_state])
    by (auto intro!: IH(2-8) invar_holds_intros simp: DFS_Aux_simps[OF IH(1)])
qed


lemma invar_dfs_tree_seen_2_props[invar_props_elims]:
  "invar_dfs_tree_seen_2 dfs_aux_state \<Longrightarrow>
     (\<lbrakk>(dfs_tree dfs_aux_state) \<noteq> {} \<Longrightarrow> dVs (dfs_tree dfs_aux_state) = t_set (seen dfs_aux_state)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
     P"
  by (auto simp: invar_dfs_tree_seen_2_def)

lemma invar_dfs_tree_seen_2_intro[invar_props_intros]:
  "\<lbrakk>(dfs_tree dfs_aux_state) \<noteq> {} \<Longrightarrow> dVs (dfs_tree dfs_aux_state) = t_set (seen dfs_aux_state)\<rbrakk> \<Longrightarrow> invar_dfs_tree_seen_2 dfs_aux_state"
  by (auto simp: invar_dfs_tree_seen_2_def)

lemma invar_dfs_tree_seen_2_holds_upd1[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_call_1_conds dfs_aux_state; invar_1 dfs_aux_state; invar_seen_stack_finished dfs_aux_state;
    invar_finished_neighbs dfs_aux_state; invar_dfs_tree_seen_1 dfs_aux_state; invar_dfs_tree_seen_2 dfs_aux_state\<rbrakk> \<Longrightarrow> 
    invar_dfs_tree_seen_2 (DFS_Aux_upd1 dfs_aux_state)"
proof (intro invar_props_intros, goal_cases)
  case 1
  let ?v = "hd (stack dfs_aux_state)"
  let ?w = "sel ((\<N>\<^sub>G ?v) -\<^sub>G (seen dfs_aux_state))"

  have stack_expr: "(stack dfs_aux_state) = hd (stack dfs_aux_state) # tl (stack dfs_aux_state)"
    using \<open>DFS_Aux_call_1_conds dfs_aux_state\<close>
    by (auto elim!: call_cond_elims)
  have w_not_in_seen: "?w \<notin> set (stack dfs_aux_state) \<union> t_set (finished dfs_aux_state)"
    using \<open>invar_1 dfs_aux_state\<close> \<open>invar_seen_stack_finished dfs_aux_state\<close> \<open>DFS_Aux_call_1_conds dfs_aux_state\<close>
    by (force elim!: invar_props_elims call_cond_elims)
  have finished_neighbs: "\<forall>(x, y) \<in> (Graph.digraph_abs G).
    (x \<in> t_set (finished dfs_aux_state) \<longrightarrow> y \<in> set (stack dfs_aux_state) \<union> t_set (finished dfs_aux_state)) \<and>
    (y \<in> t_set (finished dfs_aux_state) \<longrightarrow> x \<in> set (stack dfs_aux_state) \<union> t_set (finished dfs_aux_state))"
    using \<open>invar_seen_stack_finished dfs_aux_state\<close> \<open>invar_finished_neighbs dfs_aux_state\<close>  
    graph_symmetric Graph.digraph_abs_def
    by (fastforce elim!: invar_props_elims)
  from dfs_tree_aux1[OF stack_expr w_not_in_seen finished_neighbs]
    have dfs_tree_expr:
    "dfs_tree (DFS_Aux_upd1 dfs_aux_state) =
    {(?v, ?w), (?w, ?v)} \<union> dfs_tree dfs_aux_state"
    unfolding dfs_tree_def by (auto simp add: DFS_Aux_upd1_def Let_def)

  
  have seen_expr: "t_set (seen (DFS_Aux_upd1 dfs_aux_state)) = t_set (seen (dfs_aux_state)) \<union> {?w}"
    using \<open>invar_1 dfs_aux_state\<close>  
    by (auto simp add: DFS_Aux_upd1_def Let_def elim!: invar_props_elims)

  show ?case
  proof (cases "dfs_tree dfs_aux_state = {}")
    case True
    from True have "edges_of_vwalk (stack dfs_aux_state) = []"
      unfolding dfs_tree_def by blast
  
    then have "(stack dfs_aux_state) = [?v]"
      using \<open>DFS_Aux_call_1_conds dfs_aux_state\<close> edges_of_vwalk.elims
      by (force elim!: call_cond_elims)

    from True dfs_tree_expr
      have "dfs_tree (DFS_Aux_upd1 dfs_aux_state) = {(?v, ?w), (?w, ?v)}"
      by simp

    from True 
      have "t_set (seen (dfs_aux_state)) = {s}"
      using \<open>invar_dfs_tree_seen_1 dfs_aux_state\<close>
      by (fastforce elim!: invar_props_elims)
    with \<open>(stack dfs_aux_state) = [?v]\<close>
      have "t_set (seen (dfs_aux_state)) = {?v}"
      using \<open>invar_seen_stack_finished dfs_aux_state\<close>
      unfolding invar_seen_stack_finished_def
      by (metis list.simps(15) not_Cons_self2 set_empty subset_singleton_iff)

    with seen_expr
      have "t_set (seen (DFS_Aux_upd1 dfs_aux_state)) = {?v, ?w}"
      by auto
    with \<open>dfs_tree (DFS_Aux_upd1 dfs_aux_state) = {(?v, ?w), (?w, ?v)}\<close>
      show ?thesis unfolding dVs_def by auto
  next
    case False

    have "?v \<in> dVs (dfs_tree dfs_aux_state)"
      using \<open>invar_seen_stack_finished dfs_aux_state\<close> False \<open>invar_dfs_tree_seen_2 dfs_aux_state\<close>
      \<open>DFS_Aux_call_1_conds dfs_aux_state\<close>
      by (force elim!: invar_props_elims call_cond_elims)
    have "?w \<notin> dVs (dfs_tree dfs_aux_state)"
      using \<open>invar_1 dfs_aux_state\<close> \<open>invar_dfs_tree_seen_2 dfs_aux_state\<close> \<open>DFS_Aux_call_1_conds dfs_aux_state\<close>
      by (force elim!: invar_props_elims call_cond_elims)
  
    from \<open>?v \<in> dVs (dfs_tree dfs_aux_state)\<close> \<open>?w \<notin> dVs (dfs_tree dfs_aux_state)\<close>
      have "dVs ({(?v, ?w), (?w, ?v)} \<union> dfs_tree dfs_aux_state) = dVs (dfs_tree dfs_aux_state) \<union> {?w}"
      unfolding dVs_def by blast
    with dfs_tree_expr
      have dVs_expr: "dVs (dfs_tree (DFS_Aux_upd1 dfs_aux_state)) = dVs (dfs_tree dfs_aux_state) \<union> {?w}"
      by simp
  
    from dVs_expr seen_expr False show ?thesis
      using \<open>invar_dfs_tree_seen_2 dfs_aux_state\<close>  
      by (auto elim!: invar_props_elims)
  qed
qed

lemma invar_dfs_tree_seen_2_holds_upd2[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_call_2_conds dfs_aux_state; invar_1 dfs_aux_state; invar_2 dfs_aux_state;
    invar_seen_stack_finished dfs_aux_state; invar_dfs_tree_seen_2 dfs_aux_state\<rbrakk> \<Longrightarrow>
    invar_dfs_tree_seen_2 (DFS_Aux_upd2 dfs_aux_state)"
proof (intro invar_props_intros, goal_cases)
  case 1
  let ?v = "hd (stack dfs_aux_state)"

  have dfs_tree_expr: "dfs_tree (DFS_Aux_upd2 dfs_aux_state) = dfs_tree dfs_aux_state"
  proof (cases "tl (stack dfs_aux_state)")
    case Nil
    have stack_expr: "stack dfs_aux_state = ?v # (tl (stack dfs_aux_state))"
      using \<open>DFS_Aux_call_2_conds dfs_aux_state\<close>
      by (force elim!: call_cond_elims)
    from graph_no_self_loops2 have
      "\<forall>(x, y) \<in> (Graph.digraph_abs G). x \<noteq> y" by blast

    have stack_upd_expr: "stack (DFS_Aux_upd2 dfs_aux_state) = tl (stack dfs_aux_state)"
      by (auto simp add: DFS_Aux_upd2_def)
    have finished_upd_expr:
      "t_set (finished (DFS_Aux_upd2 dfs_aux_state)) = Set.insert (hd (stack dfs_aux_state)) (t_set (finished dfs_aux_state))"
      using \<open>invar_1 dfs_aux_state\<close>
      by (auto simp add: DFS_Aux_upd2_def elim!: invar_props_elims)

    show ?thesis
      unfolding dfs_tree_def
      apply (subst stack_upd_expr)+
      apply (subst finished_upd_expr)+
      using dfs_tree_aux2_1[of "stack dfs_aux_state" "?v" "tl (stack dfs_aux_state)"
      "Graph.digraph_abs G" "t_set (finished dfs_aux_state)", OF stack_expr Nil \<open>\<forall>(x, y) \<in> (Graph.digraph_abs G). x \<noteq> y\<close>] 
      by blast
  next
    case (Cons u l_tl_tl)
    have stack_expr: "stack dfs_aux_state = ?v # (tl (stack dfs_aux_state))"
      using \<open>DFS_Aux_call_2_conds dfs_aux_state\<close>
      by (force elim!: call_cond_elims)
    from graph_no_self_loops2 have
      "\<forall>(x, y) \<in> (Graph.digraph_abs G). x \<noteq> y" by blast

    from Cons have "stack dfs_aux_state = [?v, u] @ tl (tl (stack dfs_aux_state))"
      using stack_expr by fastforce
    have "Vwalk.vwalk (Graph.digraph_abs G) (rev (stack dfs_aux_state))"
      using \<open>invar_2 dfs_aux_state\<close>
      by (force elim!: invar_props_elims)
    with vwalk_rev graph_symmetric
      have "Vwalk.vwalk (Graph.digraph_abs G) (stack dfs_aux_state)"
      by (metis (no_types, lifting) case_prodI2 rev_rev_ident)
    have "(?v, u) \<in> (Graph.digraph_abs G)"
      by (metis \<open>Vwalk.vwalk (Graph.digraph_abs G) (stack dfs_aux_state)\<close> local.Cons stack_expr vwalk_2)
    then have edges_in_G: "{(u, ?v), (?v, u)} \<subseteq> (Graph.digraph_abs G)" by auto

    have "set (stack dfs_aux_state) \<subseteq> t_set (seen dfs_aux_state)"
      "t_set (finished dfs_aux_state) \<subseteq> t_set (seen dfs_aux_state)"
      "t_set (finished dfs_aux_state) = t_set (seen dfs_aux_state) - set (stack dfs_aux_state)"
      using \<open>invar_seen_stack_finished dfs_aux_state\<close> stack_expr
      by (auto elim!: invar_props_elims)
    then have
      sets_disjoint: "set (tl (stack dfs_aux_state)) \<inter> t_set (finished dfs_aux_state) = {}"
      using Vwalk.list_set_tl by fastforce

    have "t_set ((\<N>\<^sub>G ?v) -\<^sub>G (insert u \<emptyset>\<^sub>N)) \<inter> (t_set (seen dfs_aux_state -\<^sub>G finished dfs_aux_state)) = {}"
      using \<open>invar_1 dfs_aux_state\<close> \<open>DFS_Aux_call_2_conds dfs_aux_state\<close> Cons
      by (fastforce elim!: call_cond_elims invar_props_elims)
    then have "(t_set (\<N>\<^sub>G ?v) - {u}) \<inter> (t_set (seen dfs_aux_state) - t_set (finished dfs_aux_state)) = {}"
      using \<open>invar_1 dfs_aux_state\<close>
      by (force elim!: invar_props_elims)
    moreover have "(t_set (\<N>\<^sub>G ?v) - t_set (seen dfs_aux_state)) = {}"
      using \<open>DFS_Aux_call_2_conds dfs_aux_state\<close> \<open>invar_1 dfs_aux_state\<close> Cons
      by (force elim!: call_cond_elims invar_props_elims)
    ultimately have "(t_set (\<N>\<^sub>G ?v) - {u}) \<subseteq> t_set (finished dfs_aux_state)"
      by blast
    with graph_symmetric
      have v_neighbs: "\<forall>(x, y) \<in> (Graph.digraph_abs G).
        (x = ?v \<longrightarrow> y \<noteq> u \<longrightarrow> y \<in> t_set (finished dfs_aux_state)) \<and>
        (y = ?v \<longrightarrow> x \<noteq> u \<longrightarrow> x \<in> t_set (finished dfs_aux_state))"
      by blast

    have stack_upd_expr: "stack (DFS_Aux_upd2 dfs_aux_state) = tl (stack dfs_aux_state)"
      by (auto simp add: DFS_Aux_upd2_def)
    have finished_upd_expr:
      "t_set (finished (DFS_Aux_upd2 dfs_aux_state)) = Set.insert (hd (stack dfs_aux_state)) (t_set (finished dfs_aux_state))"
      using \<open>invar_1 dfs_aux_state\<close>
      by (auto simp add: DFS_Aux_upd2_def elim!: invar_props_elims)

    show ?thesis
      unfolding dfs_tree_def
      apply (subst stack_upd_expr)+
      apply (subst finished_upd_expr)+
      using dfs_tree_aux2_2[OF stack_expr Cons \<open>\<forall>(x, y) \<in> (Graph.digraph_abs G). x \<noteq> y\<close> edges_in_G
      sets_disjoint v_neighbs]
      by auto
  qed

  have seen_expr: "t_set (seen (DFS_Aux_upd2 dfs_aux_state)) = t_set (seen (dfs_aux_state))" 
    by (auto simp add: DFS_Aux_upd2_def Let_def)

  from \<open>dfs_tree (DFS_Aux_upd2 dfs_aux_state) \<noteq> {}\<close> dfs_tree_expr seen_expr
    show ?case
    using \<open>invar_dfs_tree_seen_2 dfs_aux_state\<close>  
    by (auto elim!: invar_props_elims)
qed



lemma invar_dfs_tree_seen_2_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_ret_1_conds dfs_aux_state; invar_dfs_tree_seen_2 dfs_aux_state\<rbrakk> \<Longrightarrow> 
    invar_dfs_tree_seen_2 (DFS_Aux_ret1 dfs_aux_state)"
  unfolding invar_dfs_tree_seen_2_def DFS_Aux_ret1_def dfs_tree_def by simp

lemma invar_dfs_tree_seen_2_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_ret_2_conds dfs_aux_state; invar_dfs_tree_seen_2 dfs_aux_state\<rbrakk> \<Longrightarrow> 
    invar_dfs_tree_seen_2 (DFS_Aux_ret2 dfs_aux_state)"
  unfolding invar_dfs_tree_seen_2_def DFS_Aux_ret2_def dfs_tree_def by simp

lemma invar_dfs_tree_seen_2_holds[invar_holds_intros]: 
   assumes "DFS_Aux_dom dfs_aux_state" "invar_1 dfs_aux_state" "invar_2 dfs_aux_state"
     "invar_seen_stack_finished dfs_aux_state" "invar_finished_neighbs dfs_aux_state"
     "invar_dfs_tree_seen_1 dfs_aux_state" "invar_dfs_tree_seen_2 dfs_aux_state"
   shows "invar_dfs_tree_seen_2 (DFS_Aux dfs_aux_state)"
  using assms(2-)
proof(induction rule: DFS_Aux_induct[OF assms(1)])
  case IH: (1 dfs_aux_state)
  show ?case
    apply(rule DFS_Aux_cases[where dfs_aux_state = dfs_aux_state])
    by (auto intro!: IH(2-9) invar_holds_intros simp: DFS_Aux_simps[OF IH(1)])
qed



lemma invar_cycle_false_props[invar_props_elims]:
  "invar_cycle_false dfs_aux_state \<Longrightarrow>
     (\<lbrakk>(\<not>cycle dfs_aux_state) \<Longrightarrow> (\<nexists>c. cycle' (dfs_tree dfs_aux_state) c)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
     P"
  by (auto simp: invar_cycle_false_def)

lemma invar_cycle_false_intro[invar_props_intros]:
  "\<lbrakk>(\<not>cycle dfs_aux_state) \<Longrightarrow> (\<nexists>c. cycle' (dfs_tree dfs_aux_state) c)\<rbrakk> \<Longrightarrow> invar_cycle_false dfs_aux_state"
  by (auto simp: invar_cycle_false_def)

lemma invar_cycle_false_holds_upd1[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_call_1_conds dfs_aux_state; invar_1 dfs_aux_state; invar_seen_stack_finished dfs_aux_state;
    invar_finished_neighbs dfs_aux_state; invar_dfs_tree_seen_2 dfs_aux_state; invar_cycle_false dfs_aux_state\<rbrakk> \<Longrightarrow>
    invar_cycle_false (DFS_Aux_upd1 dfs_aux_state)"
proof (intro invar_props_intros, goal_cases)
  case 1
  let ?v = "hd (stack dfs_aux_state)"
  let ?w = "sel ((\<N>\<^sub>G ?v) -\<^sub>G (seen dfs_aux_state))"
  
  have "?v \<noteq> ?w"
    using \<open>invar_1 dfs_aux_state\<close> \<open>invar_seen_stack_finished dfs_aux_state\<close> \<open>DFS_Aux_call_1_conds dfs_aux_state\<close>
    by (force elim!: invar_props_elims call_cond_elims)

  have stack_expr: "(stack dfs_aux_state) = hd (stack dfs_aux_state) # tl (stack dfs_aux_state)"
    using \<open>DFS_Aux_call_1_conds dfs_aux_state\<close>
    by (auto elim!: call_cond_elims)
  have w_not_in_seen: "?w \<notin> set (stack dfs_aux_state) \<union> t_set (finished dfs_aux_state)"
    using \<open>invar_1 dfs_aux_state\<close> \<open>invar_seen_stack_finished dfs_aux_state\<close> \<open>DFS_Aux_call_1_conds dfs_aux_state\<close>
    by (force elim!: invar_props_elims call_cond_elims)
  have finished_neighbs: "\<forall>(x, y) \<in> (Graph.digraph_abs G).
    (x \<in> t_set (finished dfs_aux_state) \<longrightarrow> y \<in> set (stack dfs_aux_state) \<union> t_set (finished dfs_aux_state)) \<and>
    (y \<in> t_set (finished dfs_aux_state) \<longrightarrow> x \<in> set (stack dfs_aux_state) \<union> t_set (finished dfs_aux_state))"
    using \<open>invar_seen_stack_finished dfs_aux_state\<close> \<open>invar_finished_neighbs dfs_aux_state\<close>  
    graph_symmetric Graph.digraph_abs_def
    by (fastforce elim!: invar_props_elims)
  from dfs_tree_aux1[OF stack_expr w_not_in_seen finished_neighbs]
    have dfs_tree_expr:
    "dfs_tree (DFS_Aux_upd1 dfs_aux_state) =
    {(?v, ?w), (?w, ?v)} \<union> dfs_tree dfs_aux_state"
    unfolding dfs_tree_def by (auto simp add: DFS_Aux_upd1_def Let_def)

  have "cycle (DFS_Aux_upd1 dfs_aux_state) = cycle dfs_aux_state"
    by (auto simp add: DFS_Aux_upd1_def Let_def)
  with \<open>\<not>cycle (DFS_Aux_upd1 dfs_aux_state)\<close>
    have "\<not>cycle dfs_aux_state" by blast

  show ?case
  proof (rule ccontr, goal_cases)
    case 1
    then have "\<exists>c. cycle' (dfs_tree (DFS_Aux_upd1 dfs_aux_state)) c" by blast
    then obtain c where "cycle' (dfs_tree (DFS_Aux_upd1 dfs_aux_state)) c" by blast
    with cycle'_edges_subset have "set c \<subseteq> (dfs_tree (DFS_Aux_upd1 dfs_aux_state))" by blast

    from cycle'_not_subset[OF \<open>cycle' (dfs_tree (DFS_Aux_upd1 dfs_aux_state)) c\<close>]
      have "\<not>set c \<subseteq> (dfs_tree dfs_aux_state)"
      using \<open>invar_cycle_false dfs_aux_state\<close> \<open>\<not>cycle dfs_aux_state\<close>
      by (auto elim!: invar_props_elims)

    with dfs_tree_expr \<open>set c \<subseteq> (dfs_tree (DFS_Aux_upd1 dfs_aux_state))\<close>
      have "set c \<inter> {(?v, ?w), (?w, ?v)} \<noteq> {}" by blast
    then consider (1) "(?v, ?w) \<in> set c" | (2) "(?w, ?v) \<in> set c" by blast
    then show ?case
    proof (cases)
      case 1
      from cycle'_adj_edge1[OF \<open>cycle' (dfs_tree (DFS_Aux_upd1 dfs_aux_state)) c\<close> \<open>?v \<noteq> ?w\<close> 1]
        have "\<exists>z. (?w, z) \<in> set c \<and> z \<noteq> ?v" by blast
      then obtain z where "(?w, z) \<in> set c" "z \<noteq> ?v" by blast
      with \<open>set c \<subseteq> (dfs_tree (DFS_Aux_upd1 dfs_aux_state))\<close> dfs_tree_expr
        have "(?w, z) \<in> dfs_tree dfs_aux_state" by auto
      then have "?w \<in> t_set (seen dfs_aux_state)"
        using \<open>invar_dfs_tree_seen_2 dfs_aux_state\<close>
        by (auto elim!: invar_props_elims)
      then show ?thesis
        using \<open>DFS_Aux_call_1_conds dfs_aux_state\<close> \<open>invar_1 dfs_aux_state\<close>
        by (auto elim!: invar_props_elims call_cond_elims)
    next
      case 2
      from cycle'_adj_edge2[OF \<open>cycle' (dfs_tree (DFS_Aux_upd1 dfs_aux_state)) c\<close> \<open>?v \<noteq> ?w\<close> 2]
        have "\<exists>z. (z, ?w) \<in> set c \<and> z \<noteq> ?v" by blast
      then obtain z where "(z, ?w) \<in> set c" "z \<noteq> ?v" by blast
      with \<open>set c \<subseteq> (dfs_tree (DFS_Aux_upd1 dfs_aux_state))\<close> dfs_tree_expr
        have "(z, ?w) \<in> dfs_tree dfs_aux_state" by auto
      then have "?w \<in> t_set (seen dfs_aux_state)"
        using \<open>invar_dfs_tree_seen_2 dfs_aux_state\<close>
        by (auto elim!: invar_props_elims)
      then show ?thesis
        using \<open>DFS_Aux_call_1_conds dfs_aux_state\<close> \<open>invar_1 dfs_aux_state\<close>
        by (auto elim!: invar_props_elims call_cond_elims)
    qed
  qed
qed

lemma invar_cycle_false_holds_upd2[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_call_2_conds dfs_aux_state; invar_1 dfs_aux_state; invar_2 dfs_aux_state;
    invar_seen_stack_finished dfs_aux_state; invar_cycle_false dfs_aux_state\<rbrakk> \<Longrightarrow> 
    invar_cycle_false (DFS_Aux_upd2 dfs_aux_state)"
proof (intro invar_props_intros, goal_cases)
  case 1
  let ?v = "hd (stack dfs_aux_state)"

  have dfs_tree_expr: "dfs_tree (DFS_Aux_upd2 dfs_aux_state) = dfs_tree dfs_aux_state"
  proof (cases "tl (stack dfs_aux_state)")
    case Nil
    have stack_expr: "stack dfs_aux_state = ?v # (tl (stack dfs_aux_state))"
      using \<open>DFS_Aux_call_2_conds dfs_aux_state\<close>
      by (force elim!: call_cond_elims)
    from graph_no_self_loops2 have
      "\<forall>(x, y) \<in> (Graph.digraph_abs G). x \<noteq> y" by blast

    have stack_upd_expr: "stack (DFS_Aux_upd2 dfs_aux_state) = tl (stack dfs_aux_state)"
      by (auto simp add: DFS_Aux_upd2_def)
    have finished_upd_expr:
      "t_set (finished (DFS_Aux_upd2 dfs_aux_state)) = Set.insert (hd (stack dfs_aux_state)) (t_set (finished dfs_aux_state))"
      using \<open>invar_1 dfs_aux_state\<close>
      by (auto simp add: DFS_Aux_upd2_def elim!: invar_props_elims)

    show ?thesis
      unfolding dfs_tree_def
      apply (subst stack_upd_expr)+
      apply (subst finished_upd_expr)+
      using dfs_tree_aux2_1[of "stack dfs_aux_state" "?v" "tl (stack dfs_aux_state)"
      "Graph.digraph_abs G" "t_set (finished dfs_aux_state)", OF stack_expr Nil \<open>\<forall>(x, y) \<in> (Graph.digraph_abs G). x \<noteq> y\<close>] 
      by blast
  next
    case (Cons u l_tl_tl)
    have stack_expr: "stack dfs_aux_state = ?v # (tl (stack dfs_aux_state))"
      using \<open>DFS_Aux_call_2_conds dfs_aux_state\<close>
      by (force elim!: call_cond_elims)
    from graph_no_self_loops2 have
      "\<forall>(x, y) \<in> (Graph.digraph_abs G). x \<noteq> y" by blast

    from Cons have "stack dfs_aux_state = [?v, u] @ tl (tl (stack dfs_aux_state))"
      using stack_expr by fastforce
    have "Vwalk.vwalk (Graph.digraph_abs G) (rev (stack dfs_aux_state))"
      using \<open>invar_2 dfs_aux_state\<close>
      by (force elim!: invar_props_elims)
    with vwalk_rev graph_symmetric
      have "Vwalk.vwalk (Graph.digraph_abs G) (stack dfs_aux_state)"
      by (metis (no_types, lifting) case_prodI2 rev_rev_ident)
    have "(?v, u) \<in> (Graph.digraph_abs G)"
      by (metis \<open>Vwalk.vwalk (Graph.digraph_abs G) (stack dfs_aux_state)\<close> local.Cons stack_expr vwalk_2)
    then have edges_in_G: "{(u, ?v), (?v, u)} \<subseteq> (Graph.digraph_abs G)" by auto

    have "set (stack dfs_aux_state) \<subseteq> t_set (seen dfs_aux_state)"
      "t_set (finished dfs_aux_state) \<subseteq> t_set (seen dfs_aux_state)"
      "t_set (finished dfs_aux_state) = t_set (seen dfs_aux_state) - set (stack dfs_aux_state)"
      using \<open>invar_seen_stack_finished dfs_aux_state\<close> stack_expr
      by (auto elim!: invar_props_elims)
    then have
      sets_disjoint: "set (tl (stack dfs_aux_state)) \<inter> t_set (finished dfs_aux_state) = {}"
      using Vwalk.list_set_tl by fastforce

    have "t_set ((\<N>\<^sub>G ?v) -\<^sub>G (insert u \<emptyset>\<^sub>N)) \<inter> (t_set (seen dfs_aux_state -\<^sub>G finished dfs_aux_state)) = {}"
      using \<open>invar_1 dfs_aux_state\<close> \<open>DFS_Aux_call_2_conds dfs_aux_state\<close> Cons
      by (fastforce elim!: call_cond_elims invar_props_elims)
    then have "(t_set (\<N>\<^sub>G ?v) - {u}) \<inter> (t_set (seen dfs_aux_state) - t_set (finished dfs_aux_state)) = {}"
      using \<open>invar_1 dfs_aux_state\<close>
      by (force elim!: invar_props_elims)
    moreover have "(t_set (\<N>\<^sub>G ?v) - t_set (seen dfs_aux_state)) = {}"
      using \<open>DFS_Aux_call_2_conds dfs_aux_state\<close> \<open>invar_1 dfs_aux_state\<close> Cons
      by (force elim!: call_cond_elims invar_props_elims)
    ultimately have "(t_set (\<N>\<^sub>G ?v) - {u}) \<subseteq> t_set (finished dfs_aux_state)"
      by blast
    with graph_symmetric
      have v_neighbs: "\<forall>(x, y) \<in> (Graph.digraph_abs G).
        (x = ?v \<longrightarrow> y \<noteq> u \<longrightarrow> y \<in> t_set (finished dfs_aux_state)) \<and>
        (y = ?v \<longrightarrow> x \<noteq> u \<longrightarrow> x \<in> t_set (finished dfs_aux_state))"
      by blast

    have stack_upd_expr: "stack (DFS_Aux_upd2 dfs_aux_state) = tl (stack dfs_aux_state)"
      by (auto simp add: DFS_Aux_upd2_def)
    have finished_upd_expr:
      "t_set (finished (DFS_Aux_upd2 dfs_aux_state)) = Set.insert (hd (stack dfs_aux_state)) (t_set (finished dfs_aux_state))"
      using \<open>invar_1 dfs_aux_state\<close>
      by (auto simp add: DFS_Aux_upd2_def elim!: invar_props_elims)

    show ?thesis
      unfolding dfs_tree_def
      apply (subst stack_upd_expr)+
      apply (subst finished_upd_expr)+
      using dfs_tree_aux2_2[OF stack_expr Cons \<open>\<forall>(x, y) \<in> (Graph.digraph_abs G). x \<noteq> y\<close> edges_in_G
      sets_disjoint v_neighbs]
      by auto
  qed

  have "cycle (DFS_Aux_upd2 dfs_aux_state) = cycle dfs_aux_state"
    by (auto simp add: DFS_Aux_upd2_def Let_def)
  with \<open>\<not>cycle (DFS_Aux_upd2 dfs_aux_state)\<close>
    have "\<not>(cycle dfs_aux_state)" by simp

  with dfs_tree_expr show ?case
    using \<open>invar_cycle_false dfs_aux_state\<close>
    by (auto elim!: invar_props_elims)
qed

lemma invar_cycle_false_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_ret_1_conds dfs_aux_state; invar_cycle_false dfs_aux_state\<rbrakk> \<Longrightarrow> 
    invar_cycle_false (DFS_Aux_ret1 dfs_aux_state)"
  unfolding invar_cycle_false_def DFS_Aux_ret1_def dfs_tree_def by simp

lemma invar_cycle_false_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_ret_2_conds dfs_aux_state; invar_cycle_false dfs_aux_state\<rbrakk> \<Longrightarrow> 
    invar_cycle_false (DFS_Aux_ret2 dfs_aux_state)"
  unfolding invar_cycle_false_def DFS_Aux_ret2_def dfs_tree_def by simp

lemma invar_cycle_false_holds[invar_holds_intros]: 
   assumes "DFS_Aux_dom dfs_aux_state" "invar_1 dfs_aux_state" "invar_2 dfs_aux_state"
     "invar_seen_stack_finished dfs_aux_state" "invar_finished_neighbs dfs_aux_state"
     "invar_dfs_tree_seen_1 dfs_aux_state" "invar_dfs_tree_seen_2 dfs_aux_state"
     "invar_cycle_false dfs_aux_state"
   shows "invar_cycle_false (DFS_Aux dfs_aux_state)"
  using assms(2-)
proof(induction rule: DFS_Aux_induct[OF assms(1)])
  case IH: (1 dfs_aux_state)
  show ?case
    apply(rule DFS_Aux_cases[where dfs_aux_state = dfs_aux_state])
    by (auto intro!: IH(2-10) invar_holds_intros simp: DFS_Aux_simps[OF IH(1)])
qed




lemma invar_cycle_true_props[invar_props_elims]:
  "invar_cycle_true dfs_aux_state \<Longrightarrow>
     (\<lbrakk>(cycle dfs_aux_state) \<Longrightarrow> (\<exists>c. cycle' (Graph.digraph_abs G) c)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
     P"
  by (auto simp: invar_cycle_true_def)

lemma invar_cycle_true_intro[invar_props_intros]:
  "\<lbrakk>(cycle dfs_aux_state) \<Longrightarrow> (\<exists>c. cycle' (Graph.digraph_abs G) c)\<rbrakk> \<Longrightarrow> invar_cycle_true dfs_aux_state"
  by (auto simp: invar_cycle_true_def)

lemma invar_cycle_true_holds_upd1[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_call_1_conds dfs_aux_state; 
    invar_cycle_true dfs_aux_state\<rbrakk> \<Longrightarrow> invar_cycle_true (DFS_Aux_upd1 dfs_aux_state)"
proof (intro invar_props_intros, goal_cases)
  case 1
  have "cycle (DFS_Aux_upd1 dfs_aux_state) = cycle dfs_aux_state"
    by (auto simp add: DFS_Aux_upd1_def Let_def)
  with 1 show ?case
    using \<open>invar_cycle_true dfs_aux_state\<close>
    by (auto elim!: invar_props_elims)
qed

lemma invar_cycle_true_holds_upd2[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_call_2_conds dfs_aux_state; 
    invar_cycle_true dfs_aux_state\<rbrakk> \<Longrightarrow> invar_cycle_true (DFS_Aux_upd2 dfs_aux_state)"
proof (intro invar_props_intros, goal_cases)
  case 1
  have "cycle (DFS_Aux_upd2 dfs_aux_state) = cycle dfs_aux_state"
    by (auto simp add: DFS_Aux_upd2_def Let_def)
  with 1 show ?case
    using \<open>invar_cycle_true dfs_aux_state\<close>
    by (auto elim!: invar_props_elims)
qed

lemma invar_cycle_true_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_ret_1_conds dfs_aux_state; invar_1 dfs_aux_state; invar_2 dfs_aux_state; 
    invar_seen_stack_finished dfs_aux_state; invar_cycle_true dfs_aux_state\<rbrakk> \<Longrightarrow> 
    invar_cycle_true (DFS_Aux_ret1 dfs_aux_state)"
proof (intro invar_props_intros, goal_cases)
  case 1
  then show ?case
  proof (cases "tl (stack dfs_aux_state)")
    case Nil
    let ?v = "hd (stack dfs_aux_state)"
    let ?x = "sel ((\<N>\<^sub>G ?v) \<inter>\<^sub>G (seen dfs_aux_state -\<^sub>G finished dfs_aux_state))"

    have "\<exists>x. x \<in> t_set ((\<N>\<^sub>G ?v) \<inter>\<^sub>G (seen dfs_aux_state -\<^sub>G finished dfs_aux_state))"
      using \<open>DFS_Aux_ret_1_conds dfs_aux_state\<close> \<open>invar_1 dfs_aux_state\<close> Nil
      by (force elim!: invar_props_elims call_cond_elims)
    then obtain x where
      "x \<in> t_set ((\<N>\<^sub>G ?v) \<inter>\<^sub>G (seen dfs_aux_state -\<^sub>G finished dfs_aux_state))" by blast
    then have
      "x \<in> t_set (\<N>\<^sub>G ?v)" "x \<in> t_set (seen dfs_aux_state -\<^sub>G finished dfs_aux_state)"
      using \<open>invar_1 dfs_aux_state\<close>
      by (auto elim!: invar_props_elims)

    from graph_no_self_loops1 \<open>x \<in> t_set (\<N>\<^sub>G ?v)\<close>
      have "x \<noteq> ?v" by blast
    from \<open>x \<in> t_set (seen dfs_aux_state -\<^sub>G finished dfs_aux_state)\<close>
      have "x \<in> set (stack (dfs_aux_state))"   
      using \<open>invar_1 dfs_aux_state\<close> \<open>invar_seen_stack_finished dfs_aux_state\<close>
      by (force elim!: invar_props_elims)
    with Nil have "x = ?v"
      by (metis emptyE empty_set hd_Cons_tl set_ConsD)
    with \<open>x \<noteq> ?v\<close> show ?thesis by blast
  next
    case (Cons a list)
    let ?v = "hd (stack dfs_aux_state)"
    let ?x = "sel (((\<N>\<^sub>G ?v) -\<^sub>G (insert a \<emptyset>\<^sub>N)) \<inter>\<^sub>G (seen dfs_aux_state -\<^sub>G finished dfs_aux_state))"

    have "\<exists>x. x \<in> t_set (((\<N>\<^sub>G ?v) -\<^sub>G (insert a \<emptyset>\<^sub>N)) \<inter>\<^sub>G (seen dfs_aux_state -\<^sub>G finished dfs_aux_state))"
      using \<open>DFS_Aux_ret_1_conds dfs_aux_state\<close> \<open>invar_1 dfs_aux_state\<close> Cons
      by (force elim!: invar_props_elims call_cond_elims)
    then obtain x where
      "x \<in> t_set (((\<N>\<^sub>G ?v) -\<^sub>G (insert a \<emptyset>\<^sub>N)) \<inter>\<^sub>G (seen dfs_aux_state -\<^sub>G finished dfs_aux_state))" by blast
    then have
      "x \<in> t_set (\<N>\<^sub>G ?v)" "x \<notin> t_set (insert a \<emptyset>\<^sub>N)" "x \<in> t_set (seen dfs_aux_state -\<^sub>G finished dfs_aux_state)"
      using \<open>invar_1 dfs_aux_state\<close>
      by (auto elim!: invar_props_elims)

    from graph_no_self_loops1 \<open>x \<in> t_set (\<N>\<^sub>G ?v)\<close>
      have "x \<noteq> ?v" by blast
    from \<open>x \<notin> t_set (insert a \<emptyset>\<^sub>N)\<close> have "x \<noteq> a" by simp
    from \<open>x \<in> t_set (seen dfs_aux_state -\<^sub>G finished dfs_aux_state)\<close>
      have "x \<in> set (stack (dfs_aux_state))"   
      using \<open>invar_1 dfs_aux_state\<close> \<open>invar_seen_stack_finished dfs_aux_state\<close>
      by (force elim!: invar_props_elims)

    then have "\<exists>xs p_x_v. (rev (stack dfs_aux_state) = xs @ p_x_v \<and> p_x_v \<noteq> [] \<and> hd p_x_v = x)"
      by (metis list.discI list.sel(1) set_rev split_list)
    then obtain xs p_x_v where "rev (stack dfs_aux_state) = xs @ p_x_v" "p_x_v \<noteq> []" "hd p_x_v = x"
      by blast

    then have "Vwalk.vwalk (Graph.digraph_abs G) p_x_v"
      using append_vwalk_suff \<open>invar_2 dfs_aux_state\<close>
      by (force elim!: invar_props_elims)
    moreover have "last p_x_v = ?v"
      using \<open>rev (stack dfs_aux_state) = xs @ p_x_v\<close> \<open>p_x_v \<noteq> []\<close> last_rev
      by (metis last_appendR)
    ultimately have "Vwalk.vwalk_bet (Graph.digraph_abs G) x p_x_v ?v"
      using \<open>hd p_x_v = x\<close> \<open>p_x_v \<noteq> []\<close> unfolding vwalk_bet_def by blast

    from vwalk_imp_awalk[OF this]
      have "awalk (Graph.digraph_abs G) x (edges_of_vwalk p_x_v) ?v"
      by blast
    moreover have "awalk (Graph.digraph_abs G) ?v [(?v, x)] x"
      using \<open>x \<in> t_set (\<N>\<^sub>G ?v)\<close> unfolding awalk_def dVs_def by auto
    ultimately have cycle_awalk: "awalk (Graph.digraph_abs G) x ((edges_of_vwalk p_x_v) @ [(?v, x)]) x"
      using awalk_appendI by simp

    term "tl (awalk_verts x ((edges_of_vwalk p_x_v) @ [(?v, x)]))" 
    from \<open>last p_x_v = ?v\<close>
      have "(edges_of_vwalk p_x_v) @ [(?v, x)] = edges_of_vwalk (p_x_v @ [x])"
      by (simp add: \<open>p_x_v \<noteq> []\<close> edges_of_vwalk_append_3)
    with awalk_vwalk_id \<open>hd p_x_v = x\<close>
      have "awalk_verts x ((edges_of_vwalk p_x_v) @ [(?v, x)]) = p_x_v @ [x]"
      by (metis \<open>p_x_v \<noteq> []\<close> append_is_Nil_conv hd_append2)
    with \<open>hd p_x_v = x\<close>
      have "tl (awalk_verts x ((edges_of_vwalk p_x_v) @ [(?v, x)])) = tl p_x_v @ [x]"
      using \<open>p_x_v \<noteq> []\<close> by fastforce

    have "distinct (rev (stack dfs_aux_state))"
      using \<open>invar_seen_stack_finished dfs_aux_state\<close>
      by (force elim!: invar_props_elims)
    with \<open>rev (stack dfs_aux_state) = xs @ p_x_v\<close> have "distinct p_x_v"
      by force
    with \<open>hd p_x_v = x\<close>
      have "distinct (tl p_x_v @ [x])"
      by (metis \<open>p_x_v \<noteq> []\<close> distinct1_rotate list.collapse rotate1.simps(2))
    with \<open>tl (awalk_verts x ((edges_of_vwalk p_x_v) @ [(?v, x)])) = tl p_x_v @ [x]\<close>
      have distinct_verts: "distinct (tl (awalk_verts x ((edges_of_vwalk p_x_v) @ [(?v, x)])))"
      by simp

    from \<open>hd p_x_v = x\<close> \<open>last p_x_v = ?v\<close> \<open>x \<noteq> ?v\<close> \<open>p_x_v \<noteq> []\<close>
      have "length p_x_v \<ge> 2"
      by (metis Suc_1 diff_is_0_eq' length_0_conv length_tl not_less_eq_eq singleton_hd_last)

    have "\<exists>ys. stack (dfs_aux_state) = [hd (stack dfs_aux_state), hd (tl (stack dfs_aux_state))] @ ys"
      using Cons \<open>DFS_Aux_ret_1_conds dfs_aux_state\<close>
      by (force elim!: call_cond_elims)
    then have "\<exists>ys. rev (stack dfs_aux_state) = ys @ [a, ?v]"
      using Cons rev_append
      by (smt (verit, ccfv_threshold) list.sel(1) rev_eq_Cons_iff rev_singleton_conv)

    with \<open>rev (stack dfs_aux_state) = xs @ p_x_v\<close> \<open>length p_x_v \<ge> 2\<close>
      have "\<exists>ys. p_x_v = ys @ [a, ?v]"
      by (metis List.butlast_rev \<open>hd p_x_v = x\<close> \<open>p_x_v \<noteq> []\<close> \<open>x \<noteq> ?v\<close> append.right_neutral append_Nil
      append_butlast_last_cancel butlast_append last_appendR last_rev list.sel(1) local.Cons)
    then obtain ys where "p_x_v = ys @ [a, ?v]" by blast
    with \<open>hd p_x_v = x\<close> \<open>x \<noteq> a\<close>
      have "ys \<noteq> []" by auto
    from \<open>p_x_v = ys @ [a, ?v]\<close> \<open>ys \<noteq> []\<close>
      have "length p_x_v \<ge> 3"
      using Cons Suc_le_eq by auto

    with edges_of_vwalk_length_geq_2[OF this]
      have length_greater_2: "length ((edges_of_vwalk p_x_v) @ [(?v, x)]) > 2"
    by auto

    from cycle_awalk distinct_verts length_greater_2
      show ?thesis unfolding cycle'_def Awalk_Defs.cycle_def by blast
  qed
qed

lemma invar_cycle_true_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_ret_2_conds dfs_aux_state; invar_cycle_true dfs_aux_state\<rbrakk> \<Longrightarrow> 
    invar_cycle_true (DFS_Aux_ret2 dfs_aux_state)"
  unfolding invar_cycle_false_def DFS_Aux_ret2_def dfs_tree_def by simp

lemma invar_cycle_true_holds[invar_holds_intros]: 
   assumes "DFS_Aux_dom dfs_aux_state" "invar_1 dfs_aux_state" "invar_2 dfs_aux_state"
     "invar_seen_stack_finished dfs_aux_state" "invar_cycle_true dfs_aux_state"
   shows "invar_cycle_true (DFS_Aux dfs_aux_state)"
  using assms(2-)
proof(induction rule: DFS_Aux_induct[OF assms(1)])
  case IH: (1 dfs_aux_state)
  show ?case
    apply(rule DFS_Aux_cases[where dfs_aux_state = dfs_aux_state])
    by (auto intro!: IH(2-7) invar_holds_intros simp: DFS_Aux_simps[OF IH(1)])
qed


lemma invar_seen_reachable_props[invar_props_elims]:
  "invar_seen_reachable dfs_aux_state \<Longrightarrow>
     (\<lbrakk>(\<And>v. v \<in> t_set (seen dfs_aux_state) \<Longrightarrow> (\<exists>p. awalk (Graph.digraph_abs G) s p v))\<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
     P"
  by (auto simp: invar_seen_reachable_def)

lemma invar_seen_reachable_intro[invar_props_intros]:
  "\<lbrakk>(\<And>v. v \<in> t_set (seen dfs_aux_state) \<Longrightarrow> (\<exists>p. awalk (Graph.digraph_abs G) s p v))\<rbrakk> \<Longrightarrow>
  invar_seen_reachable dfs_aux_state"
  by (auto simp: invar_seen_reachable_def)

lemma invar_seen_reachable_holds_upd1[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_call_1_conds dfs_aux_state; invar_1 dfs_aux_state; invar_2 dfs_aux_state;
  invar_s_in_stack dfs_aux_state; invar_seen_stack_finished dfs_aux_state; 
  invar_seen_reachable dfs_aux_state\<rbrakk> \<Longrightarrow> invar_seen_reachable (DFS_Aux_upd1 dfs_aux_state)"
proof (intro invar_props_intros, goal_cases)
  case (1 v)
  let ?v = "hd (stack dfs_aux_state)"
  let ?w = "sel ((\<N>\<^sub>G ?v) -\<^sub>G (seen dfs_aux_state))"

  have seen_expr: "t_set (seen (DFS_Aux_upd1 dfs_aux_state)) = t_set (seen (dfs_aux_state)) \<union> {?w}"
    using \<open>invar_1 dfs_aux_state\<close>  
    by (auto simp add: DFS_Aux_upd1_def Let_def elim!: invar_props_elims)

  have "(?v, ?w) \<in> Graph.digraph_abs G"
    using \<open>invar_1 dfs_aux_state\<close> \<open>DFS_Aux_call_1_conds dfs_aux_state\<close>
    by (force elim!: invar_props_elims call_cond_elims)
  then have v_w_awalk:
    "awalk (Graph.digraph_abs G) ?v [(?v, ?w)] ?w"
    unfolding awalk_def by auto

  have "?v \<in> t_set (seen dfs_aux_state)"
    using \<open>invar_seen_stack_finished dfs_aux_state\<close> \<open>DFS_Aux_call_1_conds dfs_aux_state\<close>
    by (fastforce elim: invar_props_elims call_cond_elims)
  then obtain p_v where "awalk (Graph.digraph_abs G) s p_v ?v"
    using \<open>invar_seen_reachable dfs_aux_state\<close>
    by (force elim: invar_props_elims)
  with v_w_awalk have w_reachable:
    "\<exists>p_w. awalk (Graph.digraph_abs G) s p_w ?w"
    using awalk_appendI by meson

  show ?case
    using seen_expr \<open>invar_seen_reachable dfs_aux_state\<close> w_reachable \<open>v \<in> t_set (seen (DFS_Aux_upd1 dfs_aux_state))\<close>
    by (force elim!: invar_props_elims)
qed

lemma invar_seen_reachable_holds_upd2[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_call_2_conds dfs_aux_state; invar_1 dfs_aux_state; invar_2 dfs_aux_state;
    invar_seen_stack_finished dfs_aux_state; invar_seen_reachable dfs_aux_state\<rbrakk> \<Longrightarrow>
    invar_seen_reachable (DFS_Aux_upd2 dfs_aux_state)"
proof (intro invar_props_intros, goal_cases)
  case (1 v)
  let ?v = "hd (stack dfs_aux_state)"

  have seen_expr: "t_set (seen (DFS_Aux_upd2 dfs_aux_state)) = t_set (seen (dfs_aux_state))" 
    by (auto simp add: DFS_Aux_upd2_def Let_def)

  from seen_expr \<open>v \<in> [seen (DFS_Aux_upd2 dfs_aux_state)]\<^sub>s\<close>
    show ?case
    using \<open>invar_seen_reachable dfs_aux_state\<close>  
    by (auto elim!: invar_props_elims)
qed


lemma invar_seen_reachable_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_ret_1_conds dfs_aux_state; invar_seen_reachable dfs_aux_state\<rbrakk> \<Longrightarrow>
  invar_seen_reachable (DFS_Aux_ret1 dfs_aux_state)"
  by (auto simp: DFS_Aux_ret1_def dfs_tree_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_seen_reachable_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_ret_2_conds dfs_aux_state; invar_seen_reachable dfs_aux_state\<rbrakk> \<Longrightarrow>
  invar_seen_reachable (DFS_Aux_ret2 dfs_aux_state)"
  by (auto simp: DFS_Aux_ret2_def dfs_tree_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_seen_reachable_holds[invar_holds_intros]: 
   assumes "DFS_Aux_dom dfs_aux_state" "invar_1 dfs_aux_state" "invar_2 dfs_aux_state"
     "invar_s_in_stack dfs_aux_state" "invar_seen_stack_finished dfs_aux_state" 
     "invar_seen_reachable dfs_aux_state"
   shows "invar_seen_reachable (DFS_Aux dfs_aux_state)"
  using assms(2-)
proof(induction rule: DFS_Aux_induct[OF assms(1)])
  case IH: (1 dfs_aux_state)
  show ?case
    apply(rule DFS_Aux_cases[where dfs_aux_state = dfs_aux_state])
    by (auto intro!: IH(2-8) invar_holds_intros simp: DFS_Aux_simps[OF IH(1)])
qed


lemma invar_visited_through_seen_props[invar_props_elims]:
   "invar_visited_through_seen dfs_aux_state \<Longrightarrow> 
     (\<lbrakk>\<And>v w p. \<lbrakk>v \<in> t_set (seen dfs_aux_state); w \<in> dVs (Graph.digraph_abs G) - t_set (seen dfs_aux_state);
        (Vwalk.vwalk_bet (Graph.digraph_abs G) v p w); distinct p\<rbrakk> \<Longrightarrow>
        set p \<inter> set (stack dfs_aux_state) \<noteq> {}\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P "
  using invar_visited_through_seen_def by blast

lemma invar_visited_through_seen_intro[invar_props_intros]:
  "\<lbrakk>\<And>v w p. \<lbrakk>v \<in> t_set (seen dfs_aux_state); w \<in> dVs (Graph.digraph_abs G) - t_set (seen dfs_aux_state);
              (Vwalk.vwalk_bet (Graph.digraph_abs G) v p w); distinct p\<rbrakk> \<Longrightarrow>
              set p \<inter> set (stack dfs_aux_state) \<noteq> {}\<rbrakk> \<Longrightarrow> invar_visited_through_seen dfs_aux_state"
  by (auto simp: invar_visited_through_seen_def)

lemma invar_visited_through_seen_holds_upd1[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_call_1_conds dfs_aux_state; invar_1 dfs_aux_state; invar_seen_stack_finished dfs_aux_state;
    invar_visited_through_seen dfs_aux_state\<rbrakk> 
    \<Longrightarrow> invar_visited_through_seen (DFS_Aux_upd1 dfs_aux_state)"
proof (intro invar_props_intros, goal_cases)
  case (1 v w p)
  let ?v = "hd (stack dfs_aux_state)"
  let ?w = "sel ((\<N>\<^sub>G ?v) -\<^sub>G (seen dfs_aux_state))"

  have "w \<in> dVs (Graph.digraph_abs G) - t_set (seen dfs_aux_state)"
    using 1(6) \<open>invar_1 dfs_aux_state\<close>
    by (force simp add: DFS_Aux_upd1_def Let_def elim!: invar_props_elims)

  have seen_expr: "t_set (seen (DFS_Aux_upd1 dfs_aux_state)) = t_set (seen (dfs_aux_state)) \<union> {?w}"
    using \<open>invar_1 dfs_aux_state\<close>  
    by (auto simp add: DFS_Aux_upd1_def Let_def elim!: invar_props_elims)
  then consider (a) "v = ?w" | (b) "v \<in> t_set (seen (dfs_aux_state))"
    using 1(5) by fastforce
  then show ?case
  proof (cases)
    case a
    have stack_expr: "(stack (DFS_Aux_upd1 dfs_aux_state)) = ?w # stack (dfs_aux_state)"
      by (auto simp add: DFS_Aux_upd1_def Let_def)
    with a show ?thesis
      by (metis "1"(7) disjoint_insert(2) list.set_sel(1) list.simps(15) vwalk_bet_def)
  next
    case b
    with \<open>w \<in> dVs (Graph.digraph_abs G) - t_set (seen dfs_aux_state)\<close> 1(7-8)
      have "set p \<inter> set (stack dfs_aux_state) \<noteq> {}"
      using \<open>invar_visited_through_seen dfs_aux_state\<close>
      by (fast elim!: invar_props_elims)
    then show ?thesis
      by (auto simp add: DFS_Aux_upd1_def Let_def)
  qed
qed

lemma invar_visited_through_seen_holds_upd2[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_call_2_conds dfs_aux_state; invar_1 dfs_aux_state; invar_seen_stack_finished dfs_aux_state;
    invar_visited_through_seen dfs_aux_state\<rbrakk> 
    \<Longrightarrow> invar_visited_through_seen (DFS_Aux_upd2 dfs_aux_state)"
proof(rule invar_props_intros, elim invar_visited_through_seen_props call_cond_elims exE,  goal_cases)
  case (1 v w p v' stack_tl)
  hence "set p \<inter> set (stack dfs_aux_state) \<noteq> {}"
    by (auto simp: DFS_Aux_upd2_def)
  then obtain u where "u \<in> set p \<inter> set (stack dfs_aux_state)"
    by auto
  show ?case
  proof(cases "u \<in> set stack_tl")
    case True
    thus ?thesis
      using 1 \<open>u \<in> set p \<inter> set (stack dfs_aux_state)\<close>
      by (auto simp: DFS_Aux_upd2_def)
  next
    case False
    hence "u = v'"
      using 1 \<open>u \<in> set p \<inter> set (stack dfs_aux_state)\<close>
      by auto
    then obtain p1 p2 where [simp]: "p = p1 @ [v'] @ p2"
      using \<open>u \<in> set p \<inter> set (stack dfs_aux_state)\<close>
      by (auto simp: in_set_conv_decomp)
    hence "set (v' # p2) \<inter> set (stack dfs_aux_state) \<noteq> {}"
      using 1
      by (auto simp: DFS_Aux_upd2_def)
    show ?thesis
    proof(cases "p2 = []")
      case True
      with \<open>p = p1 @ [v'] @ p2\<close> 1(5) have "v' = w"
        by (simp add: vwalk_bet_snoc)
      with 1(4) have "v' \<notin> t_set (seen (dfs_aux_state))"
        using \<open>invar_1 dfs_aux_state\<close>
        by (auto simp add: DFS_Aux_upd2_def elim!: invar_props_elims)
      moreover have "v' \<in> t_set (seen dfs_aux_state)"
        using 1(2) 1(10) by (auto elim!: invar_props_elims)
      ultimately show ?thesis by blast
    next
      case False
      hence "hd p2 \<in> t_set (\<N>\<^sub>G v')"
        using \<open>vwalk_bet (Graph.digraph_abs G) v p w\<close> 
        by (auto dest!: split_vwalk simp:  neq_Nil_conv)
      hence "hd p2 \<in> t_set (seen dfs_aux_state)"
        using 1
        by (metis DFS_Aux.invar_1_props DFS_Aux_axioms DFS_Aux_axioms_def Diff_iff
         Graph.neighb.set.set_empty Graph.neighbourhood_invars' \<open>DFS_Aux_axioms\<close>
         empty_iff list.sel(1) set_ops.set_diff)
      
      have "v' \<in> t_set (seen dfs_aux_state)"
        using 1(10) \<open>invar_seen_stack_finished dfs_aux_state\<close>
        by (force elim!: invar_props_elims)

      from split_vwalk 1(5) \<open>p = p1 @ [v'] @ p2\<close>
        have "Vwalk.vwalk_bet (Graph.digraph_abs G) v' (v' # p2) w" by force
      from 1(6) have "distinct (v' # p2)" by simp
      from 1(4)
        have "w \<in> dVs (Graph.digraph_abs G) - t_set (seen dfs_aux_state)"
        by (auto simp: DFS_Aux_upd2_def)
      
      from 1(7)[OF \<open>v' \<in> t_set (seen dfs_aux_state)\<close> this \<open>Vwalk.vwalk_bet (Graph.digraph_abs G) v' (v' # p2) w\<close>
        \<open>distinct (v' # p2)\<close>]
        have "set (v' # p2) \<inter> set (stack dfs_aux_state) \<noteq> {}" by simp
      then have "set p2 \<inter> set (stack dfs_aux_state) \<noteq> {}"
        by (meson "1"(7) False \<open>distinct (v' # p2)\<close> \<open>hd p2 \<in> [seen dfs_aux_state]\<^sub>s\<close>
        \<open>vwalk_bet [G]\<^sub>g v' (v' # p2) w\<close> \<open>w \<in> dVs [G]\<^sub>g - [seen dfs_aux_state]\<^sub>s\<close> distinct.simps(2) vwalk_bet_cons)
      moreover have "v' \<notin> set p2"
        using \<open>distinct p\<close>
        by auto
      ultimately have "set p2 \<inter> set (stack (DFS_Aux_upd2 dfs_aux_state)) \<noteq> {}" 
        using 1 
        by (auto simp: DFS_Aux_upd2_def)
      then show ?thesis by auto
    qed
  qed
qed

lemma invar_visited_through_seen_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_ret_1_conds dfs_aux_state; invar_visited_through_seen dfs_aux_state\<rbrakk> \<Longrightarrow>
    invar_visited_through_seen (DFS_Aux_ret1 dfs_aux_state)"
proof (intro invar_props_intros, goal_cases)
  case (1 v w p)
  from 1(3) have "v \<in> t_set (seen dfs_aux_state)"
    by (auto simp add: DFS_Aux_ret1_def Let_def)
  moreover have "w \<in> dVs (Graph.digraph_abs G) - t_set (seen dfs_aux_state)"
    using 1(4) by (auto simp add: DFS_Aux_ret1_def Let_def)
  ultimately have "set p \<inter> set (stack (dfs_aux_state)) \<noteq> {}"
    using 1(2) 1(5-6) unfolding invar_visited_through_seen_def
    by force
  then show ?case
    by (auto simp add: DFS_Aux_ret1_def Let_def)
qed

lemma invar_visited_through_seen_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>DFS_Aux_ret_2_conds dfs_aux_state; invar_visited_through_seen dfs_aux_state\<rbrakk> \<Longrightarrow>
    invar_visited_through_seen (DFS_Aux_ret2 dfs_aux_state)"
  by (auto simp: intro: invar_props_intros simp: DFS_Aux_ret2_def)

lemma invar_visited_through_seen_holds[invar_holds_intros]: 
   assumes "DFS_Aux_dom dfs_aux_state" "invar_1 dfs_aux_state"
     "invar_seen_stack_finished dfs_aux_state" "invar_visited_through_seen dfs_aux_state"
   shows "invar_visited_through_seen (DFS_Aux dfs_aux_state)"
  using assms(2-)
proof(induction rule: DFS_Aux_induct[OF assms(1)])
  case IH: (1 dfs_aux_state)
  show ?case
    apply(rule DFS_Aux_cases[where dfs_aux_state = dfs_aux_state])
    by (auto intro!: IH(2-6) invar_holds_intros simp: DFS_Aux_simps[OF IH(1)])
qed


definition "state_rel_1 dfs_aux_state_1 dfs_aux_state_2 
              \<equiv> t_set (seen dfs_aux_state_1) \<subseteq> t_set (seen dfs_aux_state_2)"

lemma state_rel_1_props[elim!]:
  "state_rel_1 dfs_aux_state_1 dfs_aux_state_2 \<Longrightarrow>
     (t_set (seen dfs_aux_state_1) \<subseteq> t_set (seen dfs_aux_state_2) \<Longrightarrow> P) \<Longrightarrow> P "
  by (auto simp: state_rel_1_def)

lemma state_rel_1_intro[state_rel_intros]:
  "\<lbrakk>t_set (seen dfs_aux_state_1) \<subseteq> t_set (seen dfs_aux_state_2)\<rbrakk> \<Longrightarrow>
    state_rel_1 dfs_aux_state_1 dfs_aux_state_2"
  by (auto simp: state_rel_1_def)

lemma state_rel_1_trans:
  "\<lbrakk>state_rel_1 dfs_aux_state_1 dfs_aux_state_2; state_rel_1 dfs_aux_state_2 dfs_aux_state_3\<rbrakk> \<Longrightarrow>
   state_rel_1 dfs_aux_state_1 dfs_aux_state_3"
  by (auto intro!: state_rel_intros)

lemma state_rel_1_holds_upd1[state_rel_holds_intros]:
  "\<lbrakk>DFS_Aux_call_1_conds dfs_aux_state; invar_1 dfs_aux_state\<rbrakk> \<Longrightarrow> state_rel_1 dfs_aux_state (DFS_Aux_upd1 dfs_aux_state)"
  by (auto simp: Let_def DFS_Aux_upd1_def elim!: invar_props_elims intro!: state_rel_intros)

lemma state_rel_1_holds_upd2[state_rel_holds_intros]:
  "\<lbrakk>DFS_Aux_call_2_conds dfs_aux_state; invar_1 dfs_aux_state\<rbrakk> \<Longrightarrow> state_rel_1 dfs_aux_state (DFS_Aux_upd2 dfs_aux_state)"
  by (auto simp: Let_def DFS_Aux_upd2_def elim!: invar_props_elims intro!: state_rel_intros)

lemma state_rel_1_holds_ret_1[state_rel_holds_intros]:
  "\<lbrakk>DFS_Aux_ret_1_conds dfs_aux_state\<rbrakk> \<Longrightarrow> state_rel_1 dfs_aux_state (DFS_Aux_ret1 dfs_aux_state)"
  by (auto simp: intro!: state_rel_intros simp: DFS_Aux_ret1_def)

lemma state_rel_1_holds_ret_2[state_rel_holds_intros]:
  "\<lbrakk>DFS_Aux_ret_2_conds dfs_aux_state\<rbrakk> \<Longrightarrow> state_rel_1 dfs_aux_state (DFS_Aux_ret2 dfs_aux_state)"
  by (auto simp: intro!: state_rel_intros simp: DFS_Aux_ret2_def)

lemma state_rel_1_holds[state_rel_holds_intros]:
   assumes "DFS_Aux_dom dfs_aux_state" "invar_1 dfs_aux_state"
   shows "state_rel_1 dfs_aux_state (DFS_Aux dfs_aux_state)" 
   using assms(2-)
proof(induction rule: DFS_Aux_induct[OF assms(1)])
  case IH: (1 dfs_aux_state)
  show ?case
    apply(rule DFS_Aux_cases[where dfs_aux_state = dfs_aux_state])
    by (auto intro: state_rel_1_trans invar_holds_intros state_rel_holds_intros intro!: IH(2-) simp: DFS_Aux_simps[OF IH(1)])
qed



lemma DFS_Aux_ret_1[ret_holds_intros]:
  "DFS_Aux_ret_1_conds (dfs_aux_state) \<Longrightarrow> DFS_Aux_ret_1_conds (DFS_Aux_ret1 dfs_aux_state)"
  by (auto simp: DFS_Aux_ret1_def elim!: call_cond_elims intro!: call_cond_intros )

(* TODO later: maybe simplify this proof (or at least make sure it conforms to linter) *)
lemma ret1_holds[ret_holds_intros]:
   assumes "DFS_Aux_dom dfs_aux_state" "cycle (DFS_Aux dfs_aux_state) = True" "cycle dfs_aux_state = False"
   shows "DFS_Aux_ret_1_conds (DFS_Aux dfs_aux_state)" 
   using assms(2-)
proof(induction  rule: DFS_Aux_induct[OF assms(1)])
  case IH: (1 dfs_aux_state)
  show ?case
    apply(rule DFS_Aux_cases[where dfs_aux_state = dfs_aux_state])
    subgoal
      using IH(4-5)                                                                
      apply (auto intro: ret_holds_intros intro!: IH(2-4) simp: DFS_Aux_simps[OF IH(1)] DFS_Aux_ret2_def)
      proof-
        assume "DFS_Aux_call_1_conds dfs_aux_state" "cycle (DFS_Aux (DFS_Aux_upd1 dfs_aux_state))"
          "\<not> cycle dfs_aux_state" "cycle (DFS_Aux_upd1 dfs_aux_state)"
        have "cycle (DFS_Aux_upd1 dfs_aux_state) = cycle (dfs_aux_state)"
          by (auto simp add: DFS_Aux_upd1_def Let_def)
        with \<open>\<not> cycle dfs_aux_state\<close> \<open>cycle (DFS_Aux_upd1 dfs_aux_state)\<close> show "False" by auto
      qed
    subgoal
      using IH(4-5)                                                                
      apply (auto intro: ret_holds_intros intro!: IH(2-4) simp: DFS_Aux_simps[OF IH(1)] DFS_Aux_ret2_def)
      proof-
        assume "DFS_Aux_call_2_conds dfs_aux_state" "cycle (DFS_Aux (DFS_Aux_upd2 dfs_aux_state))"
          "\<not> cycle dfs_aux_state" "cycle (DFS_Aux_upd2 dfs_aux_state)"
        have "cycle (DFS_Aux_upd2 dfs_aux_state) = cycle (dfs_aux_state)"
          by (auto simp add: DFS_Aux_upd2_def Let_def)
        with \<open>\<not> cycle dfs_aux_state\<close> \<open>cycle (DFS_Aux_upd2 dfs_aux_state)\<close> show "False" by auto
      qed
    subgoal
      using IH(4-5)                                                                
      by (auto intro: ret_holds_intros intro!: IH(2-4) simp: DFS_Aux_simps[OF IH(1)] DFS_Aux_ret2_def)
    subgoal
      using IH(4-5)                                                                
      by (auto intro: ret_holds_intros intro!: IH(2-4) simp: DFS_Aux_simps[OF IH(1)] DFS_Aux_ret2_def)
    done
qed


lemma DFS_Aux_correct_1_ret_1:
  "\<lbrakk>DFS_Aux_ret_1_conds dfs_aux_state; cycle dfs_aux_state; invar_cycle_true dfs_aux_state\<rbrakk> \<Longrightarrow>
    (\<exists>c. cycle' (Graph.digraph_abs G) c)"
  by (auto elim!: invar_props_elims)

lemma DFS_Aux_correct_4_ret_1:
  "\<lbrakk>DFS_Aux_ret_1_conds dfs_aux_state; invar_1 dfs_aux_state\<rbrakk> \<Longrightarrow>
    neighb_inv (seen dfs_aux_state)"
  by (auto elim!: invar_props_elims)


lemma DFS_Aux_ret_2[ret_holds_intros]:
  "DFS_Aux_ret_2_conds (dfs_aux_state) \<Longrightarrow> DFS_Aux_ret_2_conds (DFS_Aux_ret2 dfs_aux_state)"
  by (auto simp: DFS_Aux_ret2_def elim!: call_cond_elims intro!: call_cond_intros )

lemma ret2_holds[ret_holds_intros]:
   assumes "DFS_Aux_dom dfs_aux_state" "cycle (DFS_Aux dfs_aux_state) = False"
   shows "DFS_Aux_ret_2_conds (DFS_Aux dfs_aux_state)" 
   using assms(2-)
proof(induction  rule: DFS_Aux_induct[OF assms(1)])
  case IH: (1 dfs_aux_state)
  show ?case
    apply(rule DFS_Aux_cases[where dfs_aux_state = dfs_aux_state])
    using IH(4)                                                                
    by (auto intro: ret_holds_intros intro!: IH(2-) simp: DFS_Aux_simps[OF IH(1)] DFS_Aux_ret1_def)
qed

lemma DFS_Aux_correct_2_ret_2:
  "\<lbrakk>DFS_Aux_ret_2_conds dfs_aux_state; \<not>cycle dfs_aux_state; invar_seen_stack_finished dfs_aux_state;
    invar_cycle_false dfs_aux_state\<rbrakk> \<Longrightarrow>
    (\<nexists>c. cycle' ((Graph.digraph_abs G) \<downharpoonright> (t_set (seen dfs_aux_state))) c)"
proof-
  assume "DFS_Aux_ret_2_conds dfs_aux_state" "invar_seen_stack_finished dfs_aux_state"
    "\<not>cycle dfs_aux_state" "invar_cycle_false dfs_aux_state"
  then have "\<nexists>c. cycle' (dfs_tree dfs_aux_state) c"
    by (force elim!: invar_props_elims)

  have "dfs_tree dfs_aux_state = 
    {(x, y). (x, y) \<in> [G]\<^sub>g \<and> x \<in> t_set (finished dfs_aux_state) \<and> y \<in> t_set (finished dfs_aux_state)}"
    unfolding dfs_tree_def using \<open>DFS_Aux_ret_2_conds dfs_aux_state\<close>
    by (force elim!: call_cond_elims)
  moreover have "t_set (seen dfs_aux_state) = t_set (finished dfs_aux_state)"
    using \<open>DFS_Aux_ret_2_conds dfs_aux_state\<close> \<open>invar_seen_stack_finished dfs_aux_state\<close>
    by (force elim!: call_cond_elims invar_props_elims)
  ultimately have "dfs_tree dfs_aux_state = ((Graph.digraph_abs G) \<downharpoonright> (t_set (seen dfs_aux_state)))"
    unfolding induce_subgraph_def by blast
  with \<open>\<nexists>c. cycle' (dfs_tree dfs_aux_state) c\<close>
    show "(\<nexists>c. cycle' ((Graph.digraph_abs G) \<downharpoonright> (t_set (seen dfs_aux_state))) c)" by auto
qed

lemma DFS_Aux_correct_3_ret_2:
  "\<lbrakk>DFS_Aux_ret_2_conds dfs_aux_state; invar_visited_through_seen dfs_aux_state;
    v \<in> t_set (seen dfs_aux_state); w \<in> dVs (Graph.digraph_abs G) - t_set (seen dfs_aux_state)\<rbrakk> \<Longrightarrow>
      (\<nexists>p. awalk (Graph.digraph_abs G) v p w)"
proof-
  assume "DFS_Aux_ret_2_conds dfs_aux_state" "invar_visited_through_seen dfs_aux_state"
    "v \<in> t_set (seen dfs_aux_state)" "w \<in> dVs (Graph.digraph_abs G) - t_set (seen dfs_aux_state)"

  then have "\<forall>p. Vwalk.vwalk_bet (Graph.digraph_abs G) v p w \<and> distinct p \<longrightarrow> 
    (set p \<inter> set (stack dfs_aux_state) \<noteq> {})"
    by (auto elim!: call_cond_elims invar_props_elims)
  then have no_vwalks: "\<nexists>p. distinct p \<and> Vwalk.vwalk_bet (Graph.digraph_abs G) v p w"
    using \<open>DFS_Aux_ret_2_conds dfs_aux_state\<close>
    by (fastforce elim!: call_cond_elims)

  show "(\<nexists>p. awalk (Graph.digraph_abs G) v p w)"
  proof (rule ccontr, goal_cases)
    case 1
    then obtain p where "awalk (Graph.digraph_abs G) v p w" by blast
    from apath_awalk_to_apath[OF this]
      have "apath (Graph.digraph_abs G) v (awalk_to_apath (Graph.digraph_abs G) p) w" .
    with apath_def[of "(Graph.digraph_abs G)" "v" "(awalk_to_apath (Graph.digraph_abs G) p)" "w"]
      have "awalk (Graph.digraph_abs G) v (awalk_to_apath (Graph.digraph_abs G) p) w"
        "distinct (awalk_verts v (awalk_to_apath (Graph.digraph_abs G) p))"
      by auto
    moreover have
      "vwalk_bet (Graph.digraph_abs G) v (awalk_verts v (awalk_to_apath (Graph.digraph_abs G) p)) w"
      using awalk_imp_vwalk[OF \<open>awalk (Graph.digraph_abs G) v (awalk_to_apath (Graph.digraph_abs G) p) w\<close>]
      by simp
    ultimately show ?case using no_vwalks by blast
  qed
qed

lemma DFS_Aux_correct_4_ret_2:
  "\<lbrakk>DFS_Aux_ret_2_conds dfs_aux_state; invar_1 dfs_aux_state\<rbrakk> \<Longrightarrow>
    neighb_inv (seen dfs_aux_state)"
  by (auto elim!: invar_props_elims)

lemma DFS_Aux_correct_5_ret:
  "\<lbrakk>invar_seen_reachable dfs_aux_state; v \<in> t_set (seen dfs_aux_state)\<rbrakk> \<Longrightarrow>
    \<exists>p. awalk (Graph.digraph_abs G) s p v"
  by (auto elim!: invar_props_elims)


subsection \<open>Termination\<close>

named_theorems termination_intros

declare termination_intros

lemma in_prod_relI[intro!,termination_intros]:
  "\<lbrakk>f1 a = f1 a'; (a, a') \<in> f2 <*mlex*> r\<rbrakk> \<Longrightarrow> (a,a') \<in> (f1 <*mlex*> f2 <*mlex*> r)"
   by (simp add: mlex_iff)+

definition "less_rel \<equiv> {(x::nat, y::nat). x < y}"

lemma wf_less_rel[intro!]: "wf less_rel"
  by(auto simp: less_rel_def wf_less)


lemma call_1_measure_nonsym[simp]: "(call_1_measure dfs_aux_state, call_1_measure dfs_aux_state) \<notin> less_rel"
  by (auto simp: less_rel_def)

lemma call_1_terminates[termination_intros]:
  "\<lbrakk>DFS_Aux_call_1_conds dfs_aux_state; invar_1 dfs_aux_state; invar_seen_stack_finished dfs_aux_state\<rbrakk> \<Longrightarrow>
     (DFS_Aux_upd1 dfs_aux_state, dfs_aux_state) \<in> call_1_measure <*mlex*> r"
  by(fastforce elim!: invar_props_elims call_cond_elims
          simp add: DFS_Aux_upd1_def call_1_measure_def Let_def 
          intro!: mlex_less psubset_card_mono
          dest!: Graph.neighb.choose')

lemma call_2_measure_nonsym[simp]: "(call_2_measure dfs_aux_state, call_2_measure dfs_aux_state) \<notin> less_rel"
  by (auto simp: less_rel_def)

lemma call_2_measure_1[termination_intros]:
  "\<lbrakk>DFS_Aux_call_2_conds dfs_aux_state; invar_1 dfs_aux_state\<rbrakk> \<Longrightarrow>
    call_1_measure dfs_aux_state = call_1_measure (DFS_Aux_upd2 dfs_aux_state)"
  by(auto simp add: DFS_Aux_upd2_def call_1_measure_def Let_def
          intro!: psubset_card_mono)

lemma call_2_terminates[termination_intros]:
  "\<lbrakk>DFS_Aux_call_2_conds dfs_aux_state; invar_1 dfs_aux_state; invar_seen_stack_finished dfs_aux_state\<rbrakk> \<Longrightarrow>
     (DFS_Aux_upd2 dfs_aux_state, dfs_aux_state) \<in> call_2_measure <*mlex*> r"
  by(auto elim!: invar_props_elims elim!: call_cond_elims
          simp add: DFS_Aux_upd2_def call_2_measure_def
          intro!: mlex_less)

lemma wf_term_rel: "wf DFS_Aux_term_rel'"
  by(auto simp: wf_mlex DFS_Aux_term_rel'_def)

lemma in_DFS_Aux_term_rel'[termination_intros]:
  "\<lbrakk>DFS_Aux_call_1_conds dfs_aux_state; invar_1 dfs_aux_state; invar_seen_stack_finished dfs_aux_state\<rbrakk> \<Longrightarrow>
            (DFS_Aux_upd1 dfs_aux_state, dfs_aux_state) \<in> DFS_Aux_term_rel'" 
  "\<lbrakk>DFS_Aux_call_2_conds dfs_aux_state; invar_1 dfs_aux_state; invar_seen_stack_finished dfs_aux_state\<rbrakk> \<Longrightarrow>
            (DFS_Aux_upd2 dfs_aux_state, dfs_aux_state) \<in> DFS_Aux_term_rel'"
  by (simp add: DFS_Aux_term_rel'_def termination_intros)+

lemma DFS_Aux_terminates[termination_intros]:
  assumes "invar_1 dfs_aux_state" "invar_seen_stack_finished dfs_aux_state"
  shows "DFS_Aux_dom dfs_aux_state"
  using wf_term_rel assms
proof(induction rule: wf_induct_rule)
  case (less x)
  show ?case
    by (rule DFS_Aux_domintros) (auto intro!: invar_holds_intros less in_DFS_Aux_term_rel')
qed

lemma initial_state_props[invar_holds_intros, termination_intros]:
  "invar_1 (initial_state)" "invar_2 (initial_state)" "invar_seen_stack_finished (initial_state)"
  "invar_visited_through_seen (initial_state)" "invar_s_in_stack initial_state" 
  "invar_finished_neighbs (initial_state)" "invar_dfs_tree_seen_1 initial_state"
  "invar_dfs_tree_seen_2 initial_state" "invar_cycle_false (initial_state)"
  "invar_cycle_true (initial_state)" "invar_seen_reachable (initial_state)" "DFS_Aux_dom initial_state"
proof-
  show "invar_1 initial_state"
    by (auto simp: initial_state_def intro!: invar_props_intros)
  show "invar_2 initial_state"
    by (auto simp: initial_state_def intro!: invar_props_intros)
  show "invar_seen_stack_finished initial_state"
    by (auto simp: initial_state_def intro!: invar_props_intros)
  show "invar_visited_through_seen initial_state"
    by (auto simp: initial_state_def
                 hd_of_vwalk_bet''
           elim: vwalk_betE
           intro!: invar_props_intros)
  show "invar_s_in_stack initial_state"
    by (auto simp: initial_state_def intro!: invar_props_intros)
  show "invar_finished_neighbs initial_state"
    by (auto simp: initial_state_def intro!: invar_props_intros)
  show "invar_dfs_tree_seen_1 initial_state"
    by (auto simp: initial_state_def dfs_tree_def intro!: invar_props_intros)
  show "invar_dfs_tree_seen_2 initial_state"
    by (auto simp: initial_state_def dfs_tree_def intro!: invar_props_intros)
  show "invar_cycle_false initial_state"
  proof (intro invar_props_intros, goal_cases)
    case 1
    have "dfs_tree initial_state = {}"
      by (auto simp: dfs_tree_def initial_state_def)
    then show ?case
      using awalk_def
      by (metis cycle'_imp_awalk dVs_empty empty_iff)
  qed
  show "invar_cycle_true initial_state"
    by (auto simp: initial_state_def intro!: invar_props_intros)
  show "invar_seen_reachable (initial_state)"
  proof (intro invar_props_intros, goal_cases)
    case (1 v)
    then have "v = s"
      by (auto simp: initial_state_def)
    then show ?case
      unfolding awalk_def
      by (meson awalkE' awalk_Nil_iff s_in_G)
  qed
  show "DFS_Aux_dom initial_state"
    using \<open>invar_1 initial_state\<close> \<open>invar_seen_stack_finished initial_state\<close>
    by (auto intro!: termination_intros)
qed


lemma DFS_Aux_correct_1:
  assumes  "cycle (DFS_Aux initial_state)"
  shows "(\<exists>c. cycle' (Graph.digraph_abs G) c)"
  apply (intro DFS_Aux_correct_1_ret_1[where dfs_aux_state = "DFS_Aux (initial_state)"])
  subgoal
    using ret1_holds assms
    using initial_state_def initial_state_props(12) by force
  subgoal
    using assms by blast
  subgoal
    by (auto intro!: invar_holds_intros)
  done

lemma DFS_Aux_correct_2:
  assumes  "\<not>cycle (DFS_Aux initial_state)"
  shows "\<nexists>c. cycle' ((Graph.digraph_abs G) \<downharpoonright> (t_set (seen (DFS_Aux initial_state)))) c"
  apply (intro DFS_Aux_correct_2_ret_2[where dfs_aux_state = "DFS_Aux (initial_state)"])
  subgoal
    using assms by (auto intro: invar_holds_intros ret_holds_intros)
  subgoal
    using assms by blast
  subgoal
    by (auto intro!: invar_holds_intros)
  subgoal
    by (auto intro!: invar_holds_intros)
  done

lemma DFS_Aux_correct_3:
  assumes "\<not>cycle (DFS_Aux initial_state)" "v \<in> t_set (seen (DFS_Aux initial_state))"
    "w \<in> dVs (Graph.digraph_abs G) - t_set (seen (DFS_Aux initial_state))"
  shows "(\<nexists>p. awalk (Graph.digraph_abs G) v p w)"
  apply (intro DFS_Aux_correct_3_ret_2[where dfs_aux_state = "DFS_Aux (initial_state)"])
  using assms by (auto intro: invar_holds_intros ret_holds_intros)

lemma DFS_Aux_correct_4:
  "neighb_inv (seen (DFS_Aux initial_state))"
  using invar_1_holds
  by (auto intro!: invar_holds_intros elim!: invar_props_elims)


lemma DFS_Aux_correct_5:
  assumes "v \<in> t_set (seen (DFS_Aux initial_state))"
  shows "\<exists>p. awalk (Graph.digraph_abs G) s p v"
  apply (intro DFS_Aux_correct_5_ret[where dfs_aux_state = "(DFS_Aux initial_state)"])
  using assms by (auto intro!: invar_holds_intros elim!: invar_props_elims)

lemma DFS_Aux_correct_6:
  "s \<in> t_set (seen (DFS_Aux initial_state))"
proof-
  from state_rel_1_holds[where dfs_aux_state = "initial_state", OF initial_state_props(12)
    initial_state_props(1)]
    have "t_set (seen initial_state) \<subseteq> t_set (seen (DFS_Aux initial_state))"
    by auto
  then show "s \<in> t_set (seen (DFS_Aux initial_state))"
    unfolding initial_state_def by auto
qed


end


end

end