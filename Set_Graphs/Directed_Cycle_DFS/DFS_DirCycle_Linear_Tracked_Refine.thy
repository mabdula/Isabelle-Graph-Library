theory DFS_DirCycle_Linear_Tracked_Refine
  imports DFS_DirCycle_Linear_Tracked DFS_DirCycle_Linear_Tracked_Aux_Refine
begin

text \<open>Level 2 of the refinement chain at the \<^emph>\<open>outer\<close> (whole-graph) sweep --- the companion of
  \<^theory>\<open>Directed_Cycle_DFS.DFS_DirCycle_Linear_Tracked_Aux_Refine\<close>, which refines the inner
  (pre-seeded) DFS. The inner search of level 2 carries the adjacency map in its state and prunes
  it as it goes; this theory is what threads that map from one inner call to the next, so the
  pruning is done \<^emph>\<open>once\<close> over the whole run rather than once per root.

  \<^bold>\<open>Why level 1's sweep cannot simply be reused.\<close> \<^locale>\<open>DFS_DirCycle_Tracked\<close> fixes its inner
  search as \<open>dfs_aux :: 'v \<Rightarrow> 'vset \<Rightarrow> 'vset \<Rightarrow> 'state\<close> --- root, seed, unfinished set --- with no
  slot for an adjacency map. Instantiating it with the refined inner DFS would mean rebuilding the
  pruned map from \<open>G\<close> at every call, an \<open>O(E)\<close> pass per root, which is exactly the cost this
  level exists to remove: the refinement would be a net loss. So the sweep is rebuilt here with a
  four-argument inner search and one more state component.

  \<^bold>\<open>The state.\<close> \<open>DFS_DirCycle_Refine_state\<close> \<^emph>\<open>extends\<close> level 1's record with
  \<open>sweep_adj\<close>. That is deliberate: the projection that forgets the carried map is then the record
  package's own \<open>truncate\<close>, and the two sweeps are compared by a plain equation
  (\<open>refine_sweep_agrees_tracked\<close>) rather than by a bespoke agreement relation --- as in
  \<^theory>\<open>Directed_Cycle_DFS.DFS_DirCycle_Linear_Tracked_Aux_Refine\<close>. Level 1's state predicates
  (\<open>invar_1\<close>, \<open>invar_part\<close>, \<open>invar_seed\<close>, \<open>invar_cyc_true\<close>, \<open>call_measure\<close>, the call
  conditions) read only the shared fields and are polymorphic in the record extension, so they
  apply to level-2 states verbatim and are reused rather than duplicated.

  \<^bold>\<open>The contract.\<close> One new invariant, \<open>invar_adj\<close>: the carried map is \<open>G\<close> minus the in-edges
  of the finished region (\<open>adj_ok\<close>). The inner search must (a) agree with level 1's on the
  finished set, the unfinished set and the cycle flag, and (b) hand back a map satisfying
  \<open>adj_ok\<close> for the enlarged finished region. Those are precisely
  \<open>dircycle_refine_components\<close> and \<open>dircycle_refine_adj_abs_finished\<close> of
  \<^theory>\<open>Directed_Cycle_DFS.DFS_DirCycle_Linear_Tracked_Aux_Refine\<close>, and note that (a) is equality of the
  \<^emph>\<open>vsets\<close>, not merely of the sets they denote.

  \<^bold>\<open>No \<open>sel_cong\<close> here.\<close> Both levels of the inner DFS need the assumption that \<open>sel\<close> is
  determined by the element set, because they hand \<open>sel\<close> vsets built by different operations.
  The sweep does not: it picks its next root by \<open>sel (sweep_unfin st)\<close> from the very vset level 1
  picks from --- the two runs hold \<^emph>\<open>the same\<close> unfinished vset at every iteration, by (a). The
  assumption is discharged (or rather, passed on) inside the inner search; nothing of it reaches
  this level.

  \<^bold>\<open>What is proved.\<close> Only the equivalence: forgetting the carried map, the level-2 sweep is the
  level-1 sweep. Soundness and completeness are then \<^emph>\<open>transported\<close> from
  \<open>DFS_DirCycle_Tracked_sound\<close> / \<open>_complete\<close>, not re-proved.\<close>

record ('ver, 'vset, 'adjmap) DFS_DirCycle_Refine_state =
  "('ver, 'vset) DFS_DirCycle_Tracked_state" +
  sweep_adj :: "'adjmap"

locale DFS_DirCycle_Refine =
  DFS_DirCycle_Tracked where lookup = lookup
  for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option" +
  fixes rdfs_aux :: "'v \<Rightarrow> 'vset \<Rightarrow> 'vset \<Rightarrow> 'adjmap \<Rightarrow> 'rstate"
    and rfin_aux :: "'rstate \<Rightarrow> 'vset"
    and runfin_aux :: "'rstate \<Rightarrow> 'vset"
    and rcycle_aux :: "'rstate \<Rightarrow> bool"
    and radj_aux :: "'rstate \<Rightarrow> 'adjmap"
begin

subsection \<open>The contract on a carried adjacency map\<close>

text \<open>\<open>adj_ok fs M\<close>: \<open>M\<close> is a well-formed adjacency map holding \<open>G\<close> with every edge into the
  finished region \<open>fs\<close> deleted. It is both what the inner search assumes of the map it is handed
  (its \<open>A\<close>) and what it re-establishes for the enlarged region on a clean run, so threading it is
  all the sweep has to do.\<close>
definition "adj_ok fs M \<longleftrightarrow>
  Graph.graph_inv M \<and> Graph.digraph_abs M = Graph.digraph_abs G - (UNIV \<times> t_set fs)"

lemma adj_okI[intro]:
  assumes "Graph.graph_inv M"
      and "Graph.digraph_abs M = Graph.digraph_abs G - (UNIV \<times> t_set fs)"
  shows "adj_ok fs M"
  using assms by (simp add: adj_ok_def)

lemma adj_okE[elim]:
  assumes "adj_ok fs M"
  obtains "Graph.graph_inv M"
    and "Graph.digraph_abs M = Graph.digraph_abs G - (UNIV \<times> t_set fs)"
  using assms by (simp add: adj_ok_def)

lemma adj_ok_graph_invD[dest]: "adj_ok fs M \<Longrightarrow> Graph.graph_inv M"
  by (simp add: adj_ok_def)

lemma adj_ok_absD: "adj_ok fs M \<Longrightarrow> Graph.digraph_abs M = Graph.digraph_abs G - (UNIV \<times> t_set fs)"
  by (simp add: adj_ok_def)

text \<open>The two element-level consequences, so no caller has to unfold \<open>adj_ok\<close>: the carried map
  holds only \<open>G\<close>-edges, and none of them enters the finished region.\<close>

lemma adj_ok_edgeD:
  assumes "adj_ok fs M" and "(u, w) \<in> Graph.digraph_abs M"
  shows "(u, w) \<in> Graph.digraph_abs G"
  using assms by (auto simp: adj_ok_def)

lemma adj_ok_finD:
  assumes "adj_ok fs M" and "(u, w) \<in> Graph.digraph_abs M"
  shows "w \<notin> t_set fs"
  using assms by (auto simp: adj_ok_def)

subsection \<open>What the refined inner DFS must deliver\<close>

text \<open>Given a legitimate call --- the level-1 conditions on root, seed and unfinished set, plus a
  carried map satisfying \<open>adj_ok\<close> --- the refined search agrees with level 1's on all three
  components the sweep reads, and on a clean run its map is again \<open>adj_ok\<close>, now for the enlarged
  finished region. Nothing else is assumed of it: everything the sweep must know about the
  \<^emph>\<open>meaning\<close> of those components is already in \<open>dfs_aux_axioms\<close>.

  Both conjuncts are theorems of \<^locale>\<open>DFS_dircycle_refine_thms\<close>:
  \<open>dircycle_refine_components\<close> (3, 5, 6) and \<open>dircycle_refine_adj_abs_finished\<close> together with
  \<open>dircycle_refine_adj_graph_inv\<close>.\<close>
definition "rdfs_aux_axioms = (
  \<forall>s \<in> dVs (Graph.digraph_abs G). \<forall>fs us M.
    seed_ok fs \<longrightarrow> s \<notin> t_set fs \<longrightarrow> part_ok fs us \<longrightarrow> adj_ok fs M \<longrightarrow>
      (rfin_aux (rdfs_aux s fs us M) = fin_aux (dfs_aux s fs us)
       \<and> runfin_aux (rdfs_aux s fs us M) = unfin_aux (dfs_aux s fs us)
       \<and> rcycle_aux (rdfs_aux s fs us M) = cycle_aux (dfs_aux s fs us)
       \<and> (\<not> rcycle_aux (rdfs_aux s fs us M) \<longrightarrow>
            adj_ok (rfin_aux (rdfs_aux s fs us M)) (radj_aux (rdfs_aux s fs us M)))))"

subsection \<open>The sweep\<close>

text \<open>Level 1's loop with the carried map threaded through: the inner call reads \<open>sweep_adj st\<close>
  and the recursive call installs the map it hands back. Not one set operation is added.\<close>

function (domintros) DFS_DirCycle_Refine::
  "('v, 'vset, 'adjmap) DFS_DirCycle_Refine_state
     \<Rightarrow> ('v, 'vset, 'adjmap) DFS_DirCycle_Refine_state" where
  "DFS_DirCycle_Refine st =
    (if sweep_unfin st \<noteq> \<emptyset>\<^sub>N
     then
      (let
        s = sel (sweep_unfin st);
        aux = rdfs_aux s (sweep_fin st) (sweep_unfin st) (sweep_adj st)
      in
        (if rcycle_aux aux
         then st \<lparr>sweep_cyc := True\<rparr>
         else DFS_DirCycle_Refine
                (st \<lparr>sweep_fin := rfin_aux aux, sweep_unfin := runfin_aux aux,
                     sweep_adj := radj_aux aux\<rparr>)))
     else st)"
  by pat_completeness auto

partial_function (tailrec) DFS_DirCycle_Refine_impl::
  "('v, 'vset, 'adjmap) DFS_DirCycle_Refine_state
     \<Rightarrow> ('v, 'vset, 'adjmap) DFS_DirCycle_Refine_state" where
  "DFS_DirCycle_Refine_impl st =
    (if sweep_unfin st \<noteq> \<emptyset>\<^sub>N
     then
      (let
        s = sel (sweep_unfin st);
        aux = rdfs_aux s (sweep_fin st) (sweep_unfin st) (sweep_adj st)
      in
        (if rcycle_aux aux
         then st \<lparr>sweep_cyc := True\<rparr>
         else DFS_DirCycle_Refine_impl
                (st \<lparr>sweep_fin := rfin_aux aux, sweep_unfin := runfin_aux aux,
                     sweep_adj := radj_aux aux\<rparr>)))
     else st)"

lemmas [code] = DFS_DirCycle_Refine_impl.simps

lemma DFS_DirCycle_Refine_impl_same:
  assumes "DFS_DirCycle_Refine_dom st"
  shows "DFS_DirCycle_Refine_impl st = DFS_DirCycle_Refine st"
  by(induction rule: DFS_DirCycle_Refine.pinduct[OF assms])
    (subst DFS_DirCycle_Refine.psimps, simp, subst DFS_DirCycle_Refine_impl.simps,
     auto split: if_split simp add: Let_def)

subsection \<open>Call conditions\<close>

definition "DFS_DirCycle_Refine_call_1_conds st =
    (if sweep_unfin st \<noteq> \<emptyset>\<^sub>N
     then (if rcycle_aux (rdfs_aux (sel (sweep_unfin st)) (sweep_fin st) (sweep_unfin st)
                                   (sweep_adj st))
           then False else True)
     else False)"

lemma DFS_DirCycle_Refine_call_1_conds[call_cond_elims]:
  "DFS_DirCycle_Refine_call_1_conds st \<Longrightarrow>
   \<lbrakk>\<lbrakk>sweep_unfin st \<noteq> \<emptyset>\<^sub>N;
     \<not> rcycle_aux (rdfs_aux (sel (sweep_unfin st)) (sweep_fin st) (sweep_unfin st)
                            (sweep_adj st))\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp: DFS_DirCycle_Refine_call_1_conds_def split: if_splits)

definition "DFS_DirCycle_Refine_upd1 st =
    (let
      s = sel (sweep_unfin st);
      aux = rdfs_aux s (sweep_fin st) (sweep_unfin st) (sweep_adj st)
    in
      (st \<lparr>sweep_fin := rfin_aux aux, sweep_unfin := runfin_aux aux,
           sweep_adj := radj_aux aux\<rparr>))"

definition "DFS_DirCycle_Refine_ret_1_conds st =
    (if sweep_unfin st \<noteq> \<emptyset>\<^sub>N
     then (if rcycle_aux (rdfs_aux (sel (sweep_unfin st)) (sweep_fin st) (sweep_unfin st)
                                   (sweep_adj st))
           then True else False)
     else False)"

lemma DFS_DirCycle_Refine_ret_1_conds[call_cond_elims]:
  "DFS_DirCycle_Refine_ret_1_conds st \<Longrightarrow>
   \<lbrakk>\<lbrakk>sweep_unfin st \<noteq> \<emptyset>\<^sub>N;
     rcycle_aux (rdfs_aux (sel (sweep_unfin st)) (sweep_fin st) (sweep_unfin st)
                          (sweep_adj st))\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp: DFS_DirCycle_Refine_ret_1_conds_def split: if_splits)

lemma DFS_DirCycle_Refine_ret_1_condsI[call_cond_intros]:
  "\<lbrakk>sweep_unfin st \<noteq> \<emptyset>\<^sub>N;
    rcycle_aux (rdfs_aux (sel (sweep_unfin st)) (sweep_fin st) (sweep_unfin st)
                         (sweep_adj st))\<rbrakk> \<Longrightarrow>
    DFS_DirCycle_Refine_ret_1_conds st"
  by(auto simp: DFS_DirCycle_Refine_ret_1_conds_def split: if_splits)

definition "DFS_DirCycle_Refine_ret1 st = (st \<lparr>sweep_cyc := True\<rparr>)"

definition "DFS_DirCycle_Refine_ret_2_conds st =
    (if sweep_unfin st \<noteq> \<emptyset>\<^sub>N then False else True)"

lemma DFS_DirCycle_Refine_ret_2_conds[call_cond_elims]:
  "DFS_DirCycle_Refine_ret_2_conds st \<Longrightarrow> \<lbrakk>sweep_unfin st = \<emptyset>\<^sub>N \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp: DFS_DirCycle_Refine_ret_2_conds_def split: if_splits)

lemma DFS_DirCycle_Refine_ret_2_condsI[call_cond_intros]:
  "sweep_unfin st = \<emptyset>\<^sub>N \<Longrightarrow> DFS_DirCycle_Refine_ret_2_conds st"
  by(auto simp: DFS_DirCycle_Refine_ret_2_conds_def split: if_splits)

definition "DFS_DirCycle_Refine_ret2 st = st"

lemma DFS_DirCycle_Refine_cases:
  assumes "DFS_DirCycle_Refine_call_1_conds st \<Longrightarrow> P"
      "DFS_DirCycle_Refine_ret_1_conds st \<Longrightarrow> P"
      "DFS_DirCycle_Refine_ret_2_conds st \<Longrightarrow> P"
  shows "P"
proof-
  have "DFS_DirCycle_Refine_call_1_conds st \<or>
        DFS_DirCycle_Refine_ret_1_conds st \<or> DFS_DirCycle_Refine_ret_2_conds st"
    by (auto simp add: DFS_DirCycle_Refine_call_1_conds_def
                       DFS_DirCycle_Refine_ret_1_conds_def DFS_DirCycle_Refine_ret_2_conds_def
           split: list.split_asm option.split_asm if_splits)
  thus ?thesis using assms by auto
qed

lemma DFS_DirCycle_Refine_simps:
  assumes "DFS_DirCycle_Refine_dom st"
  shows "DFS_DirCycle_Refine_call_1_conds st \<Longrightarrow>
           DFS_DirCycle_Refine st = DFS_DirCycle_Refine (DFS_DirCycle_Refine_upd1 st)"
        "DFS_DirCycle_Refine_ret_1_conds st \<Longrightarrow>
           DFS_DirCycle_Refine st = DFS_DirCycle_Refine_ret1 st"
        "DFS_DirCycle_Refine_ret_2_conds st \<Longrightarrow>
           DFS_DirCycle_Refine st = DFS_DirCycle_Refine_ret2 st"
  by (auto simp add: DFS_DirCycle_Refine.psimps[OF assms] Let_def
                     DFS_DirCycle_Refine_call_1_conds_def DFS_DirCycle_Refine_upd1_def
                     DFS_DirCycle_Refine_ret_1_conds_def DFS_DirCycle_Refine_ret1_def
                     DFS_DirCycle_Refine_ret_2_conds_def DFS_DirCycle_Refine_ret2_def
            split: list.splits option.splits if_splits)

lemma DFS_DirCycle_Refine_induct:
  assumes "DFS_DirCycle_Refine_dom st"
  assumes "\<And>st. \<lbrakk>DFS_DirCycle_Refine_dom st;
     DFS_DirCycle_Refine_call_1_conds st \<Longrightarrow> P (DFS_DirCycle_Refine_upd1 st)\<rbrakk> \<Longrightarrow> P st"
  shows "P st"
  apply(rule DFS_DirCycle_Refine.pinduct[OF assms(1)])
  apply(rule assms(2)[simplified DFS_DirCycle_Refine_call_1_conds_def
                                 DFS_DirCycle_Refine_upd1_def])
  by (auto simp: Let_def split: list.splits option.splits if_splits)

lemma DFS_DirCycle_Refine_domintros:
  assumes "DFS_DirCycle_Refine_call_1_conds st \<Longrightarrow>
             DFS_DirCycle_Refine_dom (DFS_DirCycle_Refine_upd1 st)"
  shows "DFS_DirCycle_Refine_dom st"
proof(rule DFS_DirCycle_Refine.domintros, goal_cases)
  case 1
  thus ?case
    using assms(1)[simplified DFS_DirCycle_Refine_call_1_conds_def DFS_DirCycle_Refine_upd1_def]
    by (force simp: Let_def split: list.splits option.splits if_splits)
qed

text \<open>The measure is level 1's, \<open>call_measure\<close>, which reads only the shared \<open>sweep_unfin\<close>
  field and so applies to level-2 states unchanged.\<close>
definition "DFS_DirCycle_Refine_term_rel' = call_measure <*mlex*> {}"

text \<open>The initial state is level 1's plus the unpruned graph: nothing is finished yet, so the
  carried map is \<open>G\<close> itself, and this is the only place \<open>G\<close> is read as a map rather than
  through the state.\<close>
definition "refine_initial_state =
  \<lparr>sweep_fin = \<emptyset>\<^sub>N, sweep_unfin = V, sweep_cyc = False, sweep_adj = G\<rparr>"
lemmas [code] = refine_initial_state_def

subsection \<open>The one new invariant\<close>

definition "invar_adj st = adj_ok (sweep_fin st) (sweep_adj st)"

lemma invar_adj_props[invar_props_elims]:
  "invar_adj st \<Longrightarrow> (adj_ok (sweep_fin st) (sweep_adj st) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_adj_def)

lemma invar_adj_intro[invar_props_intros]:
  "adj_ok (sweep_fin st) (sweep_adj st) \<Longrightarrow> invar_adj st"
  by (auto simp: invar_adj_def)

end

text \<open>The reasoning layer. It merges level 1's \<^locale>\<open>DFS_DirCycle_Tracked_thms\<close> --- so the
  graph axioms and the \<^emph>\<open>abstract\<close> inner DFS's contract \<open>dfs_aux_axioms\<close> are in force --- with
  the single new assumption \<open>rdfs_aux_axioms\<close> relating the refined inner DFS to it. No assumption
  about \<open>sel\<close> is needed: see the header.\<close>

locale DFS_DirCycle_Refine_thms = DFS_DirCycle_Refine + DFS_DirCycle_Tracked_thms +
  assumes raux_axioms: rdfs_aux_axioms
begin

context
includes Graph.adjmap.automation and Graph.vset.set.automation
begin

subsection \<open>The projection that forgets the carried map\<close>

lemma truncate_sel[simp]:
  "sweep_fin (DFS_DirCycle_Tracked_state.truncate st) = sweep_fin st"
  "sweep_unfin (DFS_DirCycle_Tracked_state.truncate st) = sweep_unfin st"
  "sweep_cyc (DFS_DirCycle_Tracked_state.truncate st) = sweep_cyc st"
  by (simp_all add: DFS_DirCycle_Tracked_state.truncate_def)

text \<open>Level 1's invariants and measure read only the shared fields, so they are blind to the
  projection --- which is why a level-2 state can carry them as they stand.\<close>
lemma truncate_invars[simp]:
  "invar_1 (DFS_DirCycle_Tracked_state.truncate st) = invar_1 st"
  "invar_part (DFS_DirCycle_Tracked_state.truncate st) = invar_part st"
  "invar_seed (DFS_DirCycle_Tracked_state.truncate st) = invar_seed st"
  "invar_cyc_true (DFS_DirCycle_Tracked_state.truncate st) = invar_cyc_true st"
  "call_measure (DFS_DirCycle_Tracked_state.truncate st) = call_measure st"
  by (simp_all add: invar_1_def invar_part_def invar_seed_def invar_cyc_true_def call_measure_def)

lemma truncate_rets[simp]:
  "DFS_DirCycle_Tracked_state.truncate (DFS_DirCycle_Refine_ret1 st)
     = DFS_DirCycle_Tracked_ret1 (DFS_DirCycle_Tracked_state.truncate st)"
  "DFS_DirCycle_Tracked_state.truncate (DFS_DirCycle_Refine_ret2 st)
     = DFS_DirCycle_Tracked_ret2 (DFS_DirCycle_Tracked_state.truncate st)"
  by (simp_all add: DFS_DirCycle_Refine_ret1_def DFS_DirCycle_Tracked_ret1_def
                    DFS_DirCycle_Refine_ret2_def DFS_DirCycle_Tracked_ret2_def
                    DFS_DirCycle_Tracked_state.truncate_def)

subsection \<open>One inner call\<close>

text \<open>The assumption, unpacked. The premises are level 1's conditions on a legitimate call plus
  \<open>adj_ok\<close> on the map handed in.\<close>

lemma raux_spec:
  assumes "s \<in> dVs (Graph.digraph_abs G)"
      and "seed_ok fs"
      and "s \<notin> t_set fs"
      and "part_ok fs us"
      and "adj_ok fs M"
  shows "rfin_aux (rdfs_aux s fs us M) = fin_aux (dfs_aux s fs us)"
    and "runfin_aux (rdfs_aux s fs us M) = unfin_aux (dfs_aux s fs us)"
    and "rcycle_aux (rdfs_aux s fs us M) = cycle_aux (dfs_aux s fs us)"
  using raux_axioms[unfolded rdfs_aux_axioms_def, rule_format, OF assms]
  by auto

lemma raux_adj_spec:
  assumes "s \<in> dVs (Graph.digraph_abs G)"
      and "seed_ok fs"
      and "s \<notin> t_set fs"
      and "part_ok fs us"
      and "adj_ok fs M"
      and "\<not> rcycle_aux (rdfs_aux s fs us M)"
  shows "adj_ok (rfin_aux (rdfs_aux s fs us M)) (radj_aux (rdfs_aux s fs us M))"
  using raux_axioms[unfolded rdfs_aux_axioms_def, rule_format, OF assms(1-5)] assms(6)
  by auto

text \<open>The same at the state the sweep is looking at: the root it selects is a graph vertex outside
  the finished region (level 1's \<open>sel_root\<close>, which reads the partition), so the call is
  legitimate and the two inner searches return the same three components.\<close>

lemma raux_agree:
  assumes ne: "sweep_unfin st \<noteq> \<emptyset>\<^sub>N"
      and ip: "invar_part st"
      and isd: "invar_seed st"
      and ia: "invar_adj st"
  shows "rfin_aux (rdfs_aux (sel (sweep_unfin st)) (sweep_fin st) (sweep_unfin st) (sweep_adj st))
           = fin_aux (dfs_aux (sel (sweep_unfin st)) (sweep_fin st) (sweep_unfin st))"
    and "runfin_aux (rdfs_aux (sel (sweep_unfin st)) (sweep_fin st) (sweep_unfin st)
                              (sweep_adj st))
           = unfin_aux (dfs_aux (sel (sweep_unfin st)) (sweep_fin st) (sweep_unfin st))"
    and "rcycle_aux (rdfs_aux (sel (sweep_unfin st)) (sweep_fin st) (sweep_unfin st)
                              (sweep_adj st))
           = cycle_aux (dfs_aux (sel (sweep_unfin st)) (sweep_fin st) (sweep_unfin st))"
  using raux_spec[OF sel_root(1)[OF ne ip] isd[unfolded invar_seed_def] sel_root(2)[OF ne ip]
                     ip[unfolded invar_part_def] ia[unfolded invar_adj_def]]
  by auto

lemma raux_adj:
  assumes ne: "sweep_unfin st \<noteq> \<emptyset>\<^sub>N"
      and ip: "invar_part st"
      and isd: "invar_seed st"
      and ia: "invar_adj st"
      and ncyc: "\<not> rcycle_aux (rdfs_aux (sel (sweep_unfin st)) (sweep_fin st) (sweep_unfin st)
                                        (sweep_adj st))"
  shows "adj_ok (rfin_aux (rdfs_aux (sel (sweep_unfin st)) (sweep_fin st) (sweep_unfin st)
                                    (sweep_adj st)))
                (radj_aux (rdfs_aux (sel (sweep_unfin st)) (sweep_fin st) (sweep_unfin st)
                                    (sweep_adj st)))"
  by (rule raux_adj_spec[OF sel_root(1)[OF ne ip] isd[unfolded invar_seed_def]
                            sel_root(2)[OF ne ip] ip[unfolded invar_part_def]
                            ia[unfolded invar_adj_def] ncyc])

subsection \<open>The two sweeps take the same branch, and their steps commute with the projection\<close>

lemma conds_agree:
  assumes ip: "invar_part st"
      and isd: "invar_seed st"
      and ia: "invar_adj st"
  shows "DFS_DirCycle_Refine_call_1_conds st
           = DFS_DirCycle_Tracked_call_1_conds (DFS_DirCycle_Tracked_state.truncate st)"
    and "DFS_DirCycle_Refine_ret_1_conds st
           = DFS_DirCycle_Tracked_ret_1_conds (DFS_DirCycle_Tracked_state.truncate st)"
    and "DFS_DirCycle_Refine_ret_2_conds st
           = DFS_DirCycle_Tracked_ret_2_conds (DFS_DirCycle_Tracked_state.truncate st)"
proof -
  have eq: "rcycle_aux (rdfs_aux (sel (sweep_unfin st)) (sweep_fin st) (sweep_unfin st)
                                 (sweep_adj st))
              = cycle_aux (dfs_aux (sel (sweep_unfin st)) (sweep_fin st) (sweep_unfin st))"
    if "sweep_unfin st \<noteq> \<emptyset>\<^sub>N"
    by (rule raux_agree(3)[OF that ip isd ia])
  show "DFS_DirCycle_Refine_call_1_conds st
          = DFS_DirCycle_Tracked_call_1_conds (DFS_DirCycle_Tracked_state.truncate st)"
  proof (cases "sweep_unfin st = \<emptyset>\<^sub>N")
    case True
    thus ?thesis
      by (simp add: DFS_DirCycle_Refine_call_1_conds_def DFS_DirCycle_Tracked_call_1_conds_def)
  next
    case False
    thus ?thesis
      by (simp add: DFS_DirCycle_Refine_call_1_conds_def DFS_DirCycle_Tracked_call_1_conds_def eq)
  qed
  show "DFS_DirCycle_Refine_ret_1_conds st
          = DFS_DirCycle_Tracked_ret_1_conds (DFS_DirCycle_Tracked_state.truncate st)"
  proof (cases "sweep_unfin st = \<emptyset>\<^sub>N")
    case True
    thus ?thesis
      by (simp add: DFS_DirCycle_Refine_ret_1_conds_def DFS_DirCycle_Tracked_ret_1_conds_def)
  next
    case False
    thus ?thesis
      by (simp add: DFS_DirCycle_Refine_ret_1_conds_def DFS_DirCycle_Tracked_ret_1_conds_def eq)
  qed
  show "DFS_DirCycle_Refine_ret_2_conds st
          = DFS_DirCycle_Tracked_ret_2_conds (DFS_DirCycle_Tracked_state.truncate st)"
    by (simp add: DFS_DirCycle_Refine_ret_2_conds_def DFS_DirCycle_Tracked_ret_2_conds_def)
qed

text \<open>The step that matters: dropping the carried map, one level-2 iteration \<^emph>\<open>is\<close> one level-1
  iteration. Note this is equality of the two states, hence of the two \<open>sweep_unfin\<close> \<^emph>\<open>vsets\<close>
  --- so the next root, \<open>sel (sweep_unfin \<dots>)\<close>, is selected from the same vset on both sides and no
  \<open>sel_cong\<close> assumption is needed.\<close>
lemma truncate_upd1:
  assumes ne: "sweep_unfin st \<noteq> \<emptyset>\<^sub>N"
      and ip: "invar_part st"
      and isd: "invar_seed st"
      and ia: "invar_adj st"
  shows "DFS_DirCycle_Tracked_state.truncate (DFS_DirCycle_Refine_upd1 st)
           = DFS_DirCycle_Tracked_upd1 (DFS_DirCycle_Tracked_state.truncate st)"
  using raux_agree(1)[OF ne ip isd ia] raux_agree(2)[OF ne ip isd ia]
  by (simp add: DFS_DirCycle_Refine_upd1_def DFS_DirCycle_Tracked_upd1_def
                DFS_DirCycle_Tracked_state.truncate_def Let_def)

subsection \<open>Invariant preservation\<close>

text \<open>Level 1's three invariants are preserved because the step commutes with the projection and
  they are blind to it; the fourth, \<open>invar_adj\<close>, is exactly what the refined inner DFS
  re-establishes.\<close>

lemma invars_hold_upd1[invar_holds_intros]:
  assumes c: "DFS_DirCycle_Refine_call_1_conds st"
      and i1: "invar_1 st"
      and ip: "invar_part st"
      and isd: "invar_seed st"
      and ia: "invar_adj st"
  shows "invar_1 (DFS_DirCycle_Refine_upd1 st)"
    and "invar_part (DFS_DirCycle_Refine_upd1 st)"
    and "invar_seed (DFS_DirCycle_Refine_upd1 st)"
proof -
  have ne: "sweep_unfin st \<noteq> \<emptyset>\<^sub>N" using c by (auto elim!: call_cond_elims)
  have tc: "DFS_DirCycle_Tracked_call_1_conds (DFS_DirCycle_Tracked_state.truncate st)"
    using c conds_agree(1)[OF ip isd ia] by simp
  have i1': "invar_1 (DFS_DirCycle_Tracked_state.truncate st)" using i1 by simp
  have ip': "invar_part (DFS_DirCycle_Tracked_state.truncate st)" using ip by simp
  have isd': "invar_seed (DFS_DirCycle_Tracked_state.truncate st)" using isd by simp
  note tr = truncate_upd1[OF ne ip isd ia, symmetric]
  show "invar_1 (DFS_DirCycle_Refine_upd1 st)"
    using invar_1_holds_upd1[OF tc i1' ip' isd'] by (simp add: tr)
  show "invar_part (DFS_DirCycle_Refine_upd1 st)"
    using invar_part_holds_upd1[OF tc i1' ip' isd'] by (simp add: tr)
  show "invar_seed (DFS_DirCycle_Refine_upd1 st)"
    using invar_seed_holds_upd1[OF tc i1' ip' isd'] by (simp add: tr)
qed

lemma invar_adj_holds_upd1[invar_holds_intros]:
  assumes c: "DFS_DirCycle_Refine_call_1_conds st"
      and ip: "invar_part st"
      and isd: "invar_seed st"
      and ia: "invar_adj st"
  shows "invar_adj (DFS_DirCycle_Refine_upd1 st)"
proof -
  have ne: "sweep_unfin st \<noteq> \<emptyset>\<^sub>N" using c by (auto elim!: call_cond_elims)
  have ncyc: "\<not> rcycle_aux (rdfs_aux (sel (sweep_unfin st)) (sweep_fin st) (sweep_unfin st)
                                     (sweep_adj st))"
    using c by (auto elim!: call_cond_elims)
  show ?thesis
    using raux_adj[OF ne ip isd ia ncyc]
    by (simp add: invar_adj_def DFS_DirCycle_Refine_upd1_def Let_def)
qed

lemma invar_adj_holds_ret_1[invar_holds_intros]:
  "invar_adj st \<Longrightarrow> invar_adj (DFS_DirCycle_Refine_ret1 st)"
  by (simp add: invar_adj_def DFS_DirCycle_Refine_ret1_def)

lemma invar_adj_holds_ret_2[invar_holds_intros]:
  "invar_adj st \<Longrightarrow> invar_adj (DFS_DirCycle_Refine_ret2 st)"
  by (simp add: invar_adj_def DFS_DirCycle_Refine_ret2_def)

subsection \<open>Termination\<close>

text \<open>Nothing is re-argued: the level-2 step projects to the level-1 step, and level 1's measure
  is blind to the projection, so its decrease transfers verbatim.\<close>

lemma wf_refine_term_rel: "wf DFS_DirCycle_Refine_term_rel'"
  by (auto simp: wf_mlex DFS_DirCycle_Refine_term_rel'_def)

lemma refine_call_1_terminates:
  assumes c: "DFS_DirCycle_Refine_call_1_conds st"
      and i1: "invar_1 st"
      and ip: "invar_part st"
      and isd: "invar_seed st"
      and ia: "invar_adj st"
  shows "(DFS_DirCycle_Refine_upd1 st, st) \<in> call_measure <*mlex*> r"
proof -
  have ne: "sweep_unfin st \<noteq> \<emptyset>\<^sub>N" using c by (auto elim!: call_cond_elims)
  have tc: "DFS_DirCycle_Tracked_call_1_conds (DFS_DirCycle_Tracked_state.truncate st)"
    using c conds_agree(1)[OF ip isd ia] by simp
  have i1': "invar_1 (DFS_DirCycle_Tracked_state.truncate st)" using i1 by simp
  have ip': "invar_part (DFS_DirCycle_Tracked_state.truncate st)" using ip by simp
  have isd': "invar_seed (DFS_DirCycle_Tracked_state.truncate st)" using isd by simp
  have "(DFS_DirCycle_Tracked_upd1 (DFS_DirCycle_Tracked_state.truncate st),
         DFS_DirCycle_Tracked_state.truncate st) \<in> call_measure <*mlex*> {}"
    by (rule call_1_terminates[OF tc i1' ip' isd'])
  hence "call_measure (DFS_DirCycle_Tracked_upd1 (DFS_DirCycle_Tracked_state.truncate st))
           < call_measure (DFS_DirCycle_Tracked_state.truncate st)"
    by (simp add: mlex_iff)
  hence "call_measure (DFS_DirCycle_Refine_upd1 st) < call_measure st"
    by (simp add: truncate_upd1[OF ne ip isd ia, symmetric])
  thus ?thesis by (rule mlex_less)
qed

lemma in_refine_term_rel'[termination_intros]:
  "\<lbrakk>DFS_DirCycle_Refine_call_1_conds st; invar_1 st; invar_part st; invar_seed st;
    invar_adj st\<rbrakk> \<Longrightarrow>
     (DFS_DirCycle_Refine_upd1 st, st) \<in> DFS_DirCycle_Refine_term_rel'"
  by (simp add: DFS_DirCycle_Refine_term_rel'_def refine_call_1_terminates)

lemma DFS_DirCycle_Refine_terminates[termination_intros]:
  assumes "invar_1 st"
      and "invar_part st"
      and "invar_seed st"
      and "invar_adj st"
  shows "DFS_DirCycle_Refine_dom st"
  using wf_refine_term_rel assms
proof(induction rule: wf_induct_rule)
  case (less x)
  show ?case
    by (rule DFS_DirCycle_Refine_domintros)
       (auto intro!: invar_holds_intros less in_refine_term_rel')
qed

subsection \<open>The projection commutes with the whole sweep\<close>

text \<open>The capstone argument, and the only induction in this theory: at every iteration the two
  sweeps take the same branch (\<open>conds_agree\<close>) and their steps agree under the projection
  (\<open>truncate_upd1\<close>, \<open>truncate_rets\<close>), so the projection commutes with the entire run.\<close>

theorem refine_sweep_agree:
  assumes dom: "DFS_DirCycle_Refine_dom st"
      and "invar_1 st"
      and "invar_part st"
      and "invar_seed st"
      and "invar_adj st"
  shows "DFS_DirCycle_Tracked_state.truncate (DFS_DirCycle_Refine st)
           = DFS_DirCycle_Tracked (DFS_DirCycle_Tracked_state.truncate st)"
  using assms(2-)
proof (induction rule: DFS_DirCycle_Refine_induct[OF dom])
  case IH: (1 st)
  have i1': "invar_1 (DFS_DirCycle_Tracked_state.truncate st)" using IH(3) by simp
  have ip': "invar_part (DFS_DirCycle_Tracked_state.truncate st)" using IH(4) by simp
  have isd': "invar_seed (DFS_DirCycle_Tracked_state.truncate st)" using IH(5) by simp
  note simps = DFS_DirCycle_Refine_simps[OF IH(1)]
  note tsimps = DFS_DirCycle_Tracked_simps[OF DFS_DirCycle_Tracked_terminates[OF i1' ip' isd']]
  note conds = conds_agree[OF IH(4) IH(5) IH(6)]
  show ?case
  proof (rule DFS_DirCycle_Refine_cases[where st = st])
    assume c: "DFS_DirCycle_Refine_call_1_conds st"
    have tc: "DFS_DirCycle_Tracked_call_1_conds (DFS_DirCycle_Tracked_state.truncate st)"
      using c conds(1) by simp
    have ne: "sweep_unfin st \<noteq> \<emptyset>\<^sub>N" using c by (auto elim!: call_cond_elims)
    have "DFS_DirCycle_Tracked_state.truncate (DFS_DirCycle_Refine (DFS_DirCycle_Refine_upd1 st))
            = DFS_DirCycle_Tracked
                (DFS_DirCycle_Tracked_state.truncate (DFS_DirCycle_Refine_upd1 st))"
      by (rule IH(2)[OF c invars_hold_upd1(1)[OF c IH(3,4,5,6)]
                          invars_hold_upd1(2)[OF c IH(3,4,5,6)]
                          invars_hold_upd1(3)[OF c IH(3,4,5,6)]
                          invar_adj_holds_upd1[OF c IH(4,5,6)]])
    thus ?thesis
      by (simp add: simps(1)[OF c] tsimps(1)[OF tc] truncate_upd1[OF ne IH(4,5,6)])
  next
    assume c: "DFS_DirCycle_Refine_ret_1_conds st"
    have tc: "DFS_DirCycle_Tracked_ret_1_conds (DFS_DirCycle_Tracked_state.truncate st)"
      using c conds(2) by simp
    show ?thesis by (simp add: simps(2)[OF c] tsimps(2)[OF tc])
  next
    assume c: "DFS_DirCycle_Refine_ret_2_conds st"
    have tc: "DFS_DirCycle_Tracked_ret_2_conds (DFS_DirCycle_Tracked_state.truncate st)"
      using c conds(3) by simp
    show ?thesis by (simp add: simps(3)[OF c] tsimps(3)[OF tc])
  qed
qed

subsection \<open>The initial state\<close>

lemma truncate_initial:
  "DFS_DirCycle_Tracked_state.truncate refine_initial_state = initial_state"
  by (simp add: DFS_DirCycle_Tracked_state.truncate_def refine_initial_state_def
                initial_state_def)

text \<open>Level 1's four invariants come along the projection; the new one holds because nothing is
  finished at the start, so the unpruned \<open>G\<close> is the right map to carry.\<close>
lemma refine_initial_state_props:
  shows "invar_1 refine_initial_state"
    and "invar_part refine_initial_state"
    and "invar_seed refine_initial_state"
    and "invar_cyc_true refine_initial_state"
    and "invar_adj refine_initial_state"
    and "DFS_DirCycle_Refine_dom refine_initial_state"
proof -
  show i1: "invar_1 refine_initial_state"
    using initial_state_props(1) by (simp add: truncate_initial[symmetric])
  show ip: "invar_part refine_initial_state"
    using initial_state_props(2) by (simp add: truncate_initial[symmetric])
  show isd: "invar_seed refine_initial_state"
    using initial_state_props(3) by (simp add: truncate_initial[symmetric])
  show "invar_cyc_true refine_initial_state"
    using initial_state_props(4) by (simp add: truncate_initial[symmetric])
  show ia: "invar_adj refine_initial_state"
    by (simp add: invar_adj_def adj_ok_def refine_initial_state_def)
  show "DFS_DirCycle_Refine_dom refine_initial_state"
    by (rule DFS_DirCycle_Refine_terminates[OF i1 ip isd ia])
qed

section \<open>Level 2 against level 1\<close>

text \<open>Forgetting the carried adjacency map, the refined sweep \<^emph>\<open>is\<close> the tracked sweep of
  \<open>DFS_DirCycle_Tracked\<close> --- not merely a run with the same verdict, but the same state. Note in
  particular that the two \<open>sweep_fin\<close> \<^emph>\<open>vsets\<close> are equal, which the level-0/level-1 comparison
  of \<open>DFS_DirCycle_Tracked_Equiv\<close> (a sibling, not an ancestor) could not achieve for the
  sweeps: there the two loops select roots from differently built vsets, so only the verdict and
  the finished \<^emph>\<open>set\<close> agree.\<close>

theorem refine_sweep_agrees_tracked:
  "DFS_DirCycle_Tracked_state.truncate (DFS_DirCycle_Refine refine_initial_state)
     = DFS_DirCycle_Tracked initial_state"
  using refine_sweep_agree[OF refine_initial_state_props(6) refine_initial_state_props(1,2,3,5)]
  by (simp add: truncate_initial)

corollary refine_sweep_components:
  shows "sweep_fin (DFS_DirCycle_Refine refine_initial_state)
           = sweep_fin (DFS_DirCycle_Tracked initial_state)"
    and "sweep_unfin (DFS_DirCycle_Refine refine_initial_state)
           = sweep_unfin (DFS_DirCycle_Tracked initial_state)"
    and "sweep_cyc (DFS_DirCycle_Refine refine_initial_state)
           = sweep_cyc (DFS_DirCycle_Tracked initial_state)"
  using arg_cong[where f = sweep_fin, OF refine_sweep_agrees_tracked]
  using arg_cong[where f = sweep_unfin, OF refine_sweep_agrees_tracked]
  using arg_cong[where f = sweep_cyc, OF refine_sweep_agrees_tracked]
  by simp_all

corollary refine_sweep_impl_agrees_tracked:
  "DFS_DirCycle_Tracked_state.truncate (DFS_DirCycle_Refine_impl refine_initial_state)
     = DFS_DirCycle_Tracked initial_state"
  by (simp add: DFS_DirCycle_Refine_impl_same[OF refine_initial_state_props(6)]
                refine_sweep_agrees_tracked)

subsection \<open>What transports\<close>

text \<open>Soundness and completeness are \<^emph>\<open>not\<close> re-proved: the reported flag is level 1's flag.\<close>

theorem DFS_DirCycle_Refine_sound:
  assumes "sweep_cyc (DFS_DirCycle_Refine refine_initial_state)"
  shows "\<exists>c. Awalk_Defs.cycle (Graph.digraph_abs G) c"
proof -
  have "sweep_cyc (DFS_DirCycle_Tracked initial_state)"
    using assms refine_sweep_components(3) by simp
  thus ?thesis by (rule DFS_DirCycle_Tracked_sound)
qed

theorem DFS_DirCycle_Refine_complete:
  assumes "\<not> sweep_cyc (DFS_DirCycle_Refine refine_initial_state)"
  shows "\<nexists>c. Awalk_Defs.cycle (Graph.digraph_abs G) c"
proof -
  have "\<not> sweep_cyc (DFS_DirCycle_Tracked initial_state)"
    using assms refine_sweep_components(3) by simp
  thus ?thesis by (rule DFS_DirCycle_Tracked_complete)
qed

text \<open>And, for a caller that consumes the swept region rather than the verdict: on a clean sweep
  the finished vset holds the whole vertex set.\<close>

theorem DFS_DirCycle_Refine_fin_eq_dVs:
  assumes ncyc: "\<not> sweep_cyc (DFS_DirCycle_Refine refine_initial_state)"
  shows "t_set (sweep_fin (DFS_DirCycle_Refine refine_initial_state))
           = dVs (Graph.digraph_abs G)"
proof -
  note ini = initial_state_props
  have ncyc': "\<not> sweep_cyc (DFS_DirCycle_Tracked initial_state)"
    using ncyc refine_sweep_components(3) by simp
  have dom: "DFS_DirCycle_Tracked_dom initial_state" by (rule ini(5))
  have ip: "invar_part (DFS_DirCycle_Tracked initial_state)" by (intro invar_part_holds dom ini)
  have isd: "invar_seed (DFS_DirCycle_Tracked initial_state)" by (intro invar_seed_holds dom ini)
  have "DFS_DirCycle_Tracked_ret_2_conds (DFS_DirCycle_Tracked initial_state)"
    by (intro ret_2_holds dom ini ncyc')
  hence empty: "sweep_unfin (DFS_DirCycle_Tracked initial_state) = \<emptyset>\<^sub>N"
    by (auto elim!: call_cond_elims)
  have covers: "dVs (Graph.digraph_abs G)
                  \<subseteq> t_set (sweep_fin (DFS_DirCycle_Tracked initial_state))"
    using ip empty by (force elim!: invar_props_elims)
  have "t_set (sweep_fin (DFS_DirCycle_Tracked initial_state)) \<subseteq> dVs (Graph.digraph_abs G)"
    using isd by (auto simp: invar_seed_def seed_ok_def)
  hence "t_set (sweep_fin (DFS_DirCycle_Tracked initial_state)) = dVs (Graph.digraph_abs G)"
    using covers by blast
  thus ?thesis by (simp add: refine_sweep_components(1))
qed

end

end

end

