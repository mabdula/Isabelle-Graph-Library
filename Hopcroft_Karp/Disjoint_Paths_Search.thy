theory Disjoint_Paths_Search
  imports "Directed_Set_Graphs.Pair_Graph_Specs" "Data_Structures.Set2_Addons"
          Micali_Vazirani.Layered_Digraph
begin

provenance ai_human

section \<open>Searching for Vertex-Disjoint Paths\<close>

text \<open>From each root in turn, a search step looks for a path to a target vertex that avoids
  the vertices blocked by the paths found so far. The search step is a parameter of the
  locale, and its contract is an assumption of the locale.\<close>

lemma vwalk_bet_closed:
  "\<lbrakk>Vwalk.vwalk_bet E u q v; u \<in> S; \<And>a b. \<lbrakk>a \<in> S; (a, b) \<in> E\<rbrakk> \<Longrightarrow> b \<in> S\<rbrakk> \<Longrightarrow> v \<in> S"
  by (induction rule: induct_vwalk_bet) auto

lemma found_vwalk_bet:
  "\<lbrakk>Vwalk.vwalk E (rev p); p \<noteq> []\<rbrakk> \<Longrightarrow> Vwalk.vwalk_bet E (last p) (rev p) (hd p)"
  by (simp add: Vwalk.vwalk_bet_def hd_rev last_rev)

subsection \<open>The program state\<close>

record ('v, 'vset) Disjoint_Paths_Search_state =
  roots :: "'v list"
  avoided :: 'vset
  explored :: 'vset
  paths :: "'v list list"

subsection \<open>Setup for automation\<close>

named_theorems call_cond_elims
named_theorems call_cond_intros
named_theorems ret_holds_intros
named_theorems invar_props_intros
named_theorems invar_props_elims
named_theorems invar_holds_intros

subsection \<open>The loop\<close>

locale Disjoint_Paths_Search =
  Graph: Pair_Graph_Specs where lookup = lookup +
  set_ops: Set2 vset_empty vset_delete _ t_set vset_inv insert
  for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option" +
  fixes G :: 'adjmap
    and target :: "'v \<Rightarrow> bool"
    and blocked :: "'v list \<Rightarrow> 'vset"
    and initial_roots :: "'v list"
    and search_step :: "'vset \<Rightarrow> 'v \<Rightarrow> 'vset \<Rightarrow> 'v list option \<times> 'vset"
  assumes search_step:
    "\<And>lev avoid r vis res vis'.
       \<lbrakk>Graph.layered_graph_input G lev; vset_inv avoid; vset_inv vis;
        t_set avoid \<subseteq> dVs (Graph.digraph_abs G); t_set vis \<subseteq> dVs (Graph.digraph_abs G);
        r \<in> dVs (Graph.digraph_abs G); search_step avoid r vis = (res, vis')\<rbrakk>
       \<Longrightarrow> vset_inv vis'"
    "\<And>lev avoid r vis res vis'.
       \<lbrakk>Graph.layered_graph_input G lev; vset_inv avoid; vset_inv vis;
        t_set avoid \<subseteq> dVs (Graph.digraph_abs G); t_set vis \<subseteq> dVs (Graph.digraph_abs G);
        r \<in> dVs (Graph.digraph_abs G); search_step avoid r vis = (res, vis')\<rbrakk>
       \<Longrightarrow> t_set vis' \<subseteq> dVs (Graph.digraph_abs G)"
    "\<And>lev avoid r vis res vis'.
       \<lbrakk>Graph.layered_graph_input G lev; vset_inv avoid; vset_inv vis;
        t_set avoid \<subseteq> dVs (Graph.digraph_abs G); t_set vis \<subseteq> dVs (Graph.digraph_abs G);
        r \<in> dVs (Graph.digraph_abs G); search_step avoid r vis = (res, vis')\<rbrakk>
       \<Longrightarrow> t_set vis \<subseteq> t_set vis'"
    "\<And>lev avoid r vis vis'.
       \<lbrakk>Graph.layered_graph_input G lev; vset_inv avoid; vset_inv vis;
        t_set avoid \<subseteq> dVs (Graph.digraph_abs G); t_set vis \<subseteq> dVs (Graph.digraph_abs G);
        r \<in> dVs (Graph.digraph_abs G); search_step avoid r vis = (None, vis');
        r \<notin> t_set avoid\<rbrakk>
       \<Longrightarrow> r \<in> t_set vis'"
    "\<And>lev avoid r vis vis' v w.
       \<lbrakk>Graph.layered_graph_input G lev; vset_inv avoid; vset_inv vis;
        t_set avoid \<subseteq> dVs (Graph.digraph_abs G); t_set vis \<subseteq> dVs (Graph.digraph_abs G);
        r \<in> dVs (Graph.digraph_abs G); search_step avoid r vis = (None, vis');
        v \<in> t_set vis' - t_set vis; (v, w) \<in> Graph.digraph_abs G\<rbrakk>
       \<Longrightarrow> w \<in> t_set avoid \<union> t_set vis'"
    "\<And>lev avoid r vis res vis' v.
       \<lbrakk>Graph.layered_graph_input G lev; vset_inv avoid; vset_inv vis;
        t_set avoid \<subseteq> dVs (Graph.digraph_abs G); t_set vis \<subseteq> dVs (Graph.digraph_abs G);
        r \<in> dVs (Graph.digraph_abs G); search_step avoid r vis = (res, vis');
        v \<in> t_set vis' - t_set vis\<rbrakk>
       \<Longrightarrow> \<not> target v"
    "\<And>lev avoid r vis p vis'.
       \<lbrakk>Graph.layered_graph_input G lev; vset_inv avoid; vset_inv vis;
        t_set avoid \<subseteq> dVs (Graph.digraph_abs G); t_set vis \<subseteq> dVs (Graph.digraph_abs G);
        r \<in> dVs (Graph.digraph_abs G); search_step avoid r vis = (Some p, vis')\<rbrakk>
       \<Longrightarrow> Vwalk.vwalk (Graph.digraph_abs G) (rev p) \<and> p \<noteq> [] \<and> distinct p \<and> target (hd p) \<and>
           last p = r \<and> set p \<inter> (t_set avoid \<union> t_set vis') = {}"
begin

function (domintros) Disjoint_Paths_Search ::
  "('v, 'vset) Disjoint_Paths_Search_state \<Rightarrow> ('v, 'vset) Disjoint_Paths_Search_state" where
  "Disjoint_Paths_Search state =
     (case roots state of
        [] \<Rightarrow> state
      | r # rs \<Rightarrow>
          (case search_step (avoided state) r (explored state) of
             (Some p, explored') \<Rightarrow>
               Disjoint_Paths_Search
                 (state \<lparr>roots := rs, avoided := union (avoided state) (blocked p),
                         explored := explored', paths := p # paths state\<rparr>)
           | (None, explored') \<Rightarrow>
               Disjoint_Paths_Search (state \<lparr>roots := rs, explored := explored'\<rparr>)))"
  by pat_completeness auto

partial_function (tailrec) Disjoint_Paths_Search_impl ::
  "('v, 'vset) Disjoint_Paths_Search_state \<Rightarrow> ('v, 'vset) Disjoint_Paths_Search_state" where
  "Disjoint_Paths_Search_impl state =
     (case roots state of
        [] \<Rightarrow> state
      | r # rs \<Rightarrow>
          (case search_step (avoided state) r (explored state) of
             (Some p, explored') \<Rightarrow>
               Disjoint_Paths_Search_impl
                 (state \<lparr>roots := rs, avoided := union (avoided state) (blocked p),
                         explored := explored', paths := p # paths state\<rparr>)
           | (None, explored') \<Rightarrow>
               Disjoint_Paths_Search_impl (state \<lparr>roots := rs, explored := explored'\<rparr>)))"

lemma Disjoint_Paths_Search_impl_same:
  assumes "Disjoint_Paths_Search_dom state"
  shows "Disjoint_Paths_Search_impl state = Disjoint_Paths_Search state"
  by(induction rule: Disjoint_Paths_Search.pinduct[OF assms])
    (subst Disjoint_Paths_Search.psimps, assumption,
     subst Disjoint_Paths_Search_impl.simps,
     auto split: list.splits option.splits prod.splits)
definition "Disjoint_Paths_Search_axiom =
  ((\<exists>lev. Graph.layered_graph_input G lev) \<and>
   set initial_roots \<subseteq> dVs (Graph.digraph_abs G) \<and>
   (\<forall>p. vset_inv (blocked p) \<and> t_set (blocked p) \<subseteq> dVs (Graph.digraph_abs G)))"

definition "initial_state =
  \<lparr>roots = initial_roots, avoided = vset_empty, explored = vset_empty, paths = []\<rparr>"

definition "Disjoint_Paths_Search_run = Disjoint_Paths_Search initial_state"

definition "Disjoint_Paths_Search_run_impl = Disjoint_Paths_Search_impl initial_state"

lemmas [code] = Disjoint_Paths_Search_impl.simps initial_state_def Disjoint_Paths_Search_run_impl_def

definition "Disjoint_Paths_Search_call_1_conds state =
  (case roots state of
     [] \<Rightarrow> False
   | r # rs \<Rightarrow>
       (case search_step (avoided state) r (explored state) of
          (Some p, explored') \<Rightarrow> True
        | (None, explored') \<Rightarrow> False))"

definition "Disjoint_Paths_Search_upd1 state =
  (let (path, explored') = search_step (avoided state) (hd (roots state)) (explored state);
       p = the path
   in state \<lparr>roots := tl (roots state), avoided := union (avoided state) (blocked p),
             explored := explored', paths := p # paths state\<rparr>)"

definition "Disjoint_Paths_Search_call_2_conds state =
  (case roots state of
     [] \<Rightarrow> False
   | r # rs \<Rightarrow>
       (case search_step (avoided state) r (explored state) of
          (Some p, explored') \<Rightarrow> False
        | (None, explored') \<Rightarrow> True))"

definition "Disjoint_Paths_Search_upd2 state =
  state \<lparr>roots := tl (roots state),
         explored := snd (search_step (avoided state) (hd (roots state)) (explored state))\<rparr>"

definition "Disjoint_Paths_Search_ret_1_conds state = (roots state = [])"

abbreviation "Disjoint_Paths_Search_ret1 state \<equiv> state"

definition "call_1_measure state = length (roots state)"

definition "Disjoint_Paths_Search_term_rel' = call_1_measure <*mlex*> {}"

definition "invar_1 state = (vset_inv (avoided state) \<and> vset_inv (explored state))"

definition "invar_within_graph state =
  (t_set (avoided state) \<subseteq> dVs (Graph.digraph_abs G) \<and>
   t_set (explored state) \<subseteq> dVs (Graph.digraph_abs G) \<and>
   set (roots state) \<subseteq> dVs (Graph.digraph_abs G))"

definition "invar_roots state = (set (roots state) \<subseteq> set initial_roots)"

definition "invar_paths_sound state =
  (\<forall>p \<in> set (paths state).
     Vwalk.vwalk (Graph.digraph_abs G) (rev p) \<and> p \<noteq> [] \<and> distinct p \<and> target (hd p) \<and>
     last p \<in> set initial_roots)"

definition "invar_blocked_avoided state =
  (\<forall>p \<in> set (paths state). t_set (blocked p) \<subseteq> t_set (avoided state))"

definition "invar_paths_disjoint state =
  sorted_wrt (\<lambda>q p. set q \<inter> t_set (blocked p) = {}) (paths state)"

definition "invar_explored_closed state =
  (paths state = [] \<longrightarrow>
     t_set (avoided state) = {} \<and>
     set initial_roots \<subseteq> set (roots state) \<union> t_set (explored state) \<and>
     (\<forall>v \<in> t_set (explored state). \<not> target v) \<and>
     (\<forall>v w. v \<in> t_set (explored state) \<longrightarrow> (v, w) \<in> Graph.digraph_abs G \<longrightarrow>
            w \<in> t_set (explored state)))"

lemma Disjoint_Paths_Search_call_1_conds[call_cond_elims]:
  "Disjoint_Paths_Search_call_1_conds state \<Longrightarrow>
   (\<And>r rs p explored'. \<lbrakk>roots state = r # rs;
       search_step (avoided state) r (explored state) = (Some p, explored')\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: Disjoint_Paths_Search_call_1_conds_def split: list.splits option.splits prod.splits)

lemma Disjoint_Paths_Search_call_1_condsI[call_cond_intros]:
  "\<lbrakk>roots state = r # rs; search_step (avoided state) r (explored state) = (Some p, explored')\<rbrakk>
   \<Longrightarrow> Disjoint_Paths_Search_call_1_conds state"
  by (auto simp: Disjoint_Paths_Search_call_1_conds_def)

lemma Disjoint_Paths_Search_call_2_conds[call_cond_elims]:
  "Disjoint_Paths_Search_call_2_conds state \<Longrightarrow>
   (\<And>r rs explored'. \<lbrakk>roots state = r # rs;
       search_step (avoided state) r (explored state) = (None, explored')\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: Disjoint_Paths_Search_call_2_conds_def split: list.splits option.splits prod.splits)

lemma Disjoint_Paths_Search_call_2_condsI[call_cond_intros]:
  "\<lbrakk>roots state = r # rs; search_step (avoided state) r (explored state) = (None, explored')\<rbrakk>
   \<Longrightarrow> Disjoint_Paths_Search_call_2_conds state"
  by (auto simp: Disjoint_Paths_Search_call_2_conds_def)

lemma Disjoint_Paths_Search_ret_1_conds[call_cond_elims]:
  "Disjoint_Paths_Search_ret_1_conds state \<Longrightarrow> (roots state = [] \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: Disjoint_Paths_Search_ret_1_conds_def)

lemma Disjoint_Paths_Search_ret_1_condsI[call_cond_intros]:
  "roots state = [] \<Longrightarrow> Disjoint_Paths_Search_ret_1_conds state"
  by (auto simp: Disjoint_Paths_Search_ret_1_conds_def)

lemma Disjoint_Paths_Search_cases:
  assumes "Disjoint_Paths_Search_call_1_conds state \<Longrightarrow> P"
          "Disjoint_Paths_Search_call_2_conds state \<Longrightarrow> P"
          "Disjoint_Paths_Search_ret_1_conds state \<Longrightarrow> P"
  shows "P"
proof-
  have "Disjoint_Paths_Search_call_1_conds state \<or> Disjoint_Paths_Search_call_2_conds state \<or>
        Disjoint_Paths_Search_ret_1_conds state"
    by (auto simp: Disjoint_Paths_Search_call_1_conds_def Disjoint_Paths_Search_call_2_conds_def
                   Disjoint_Paths_Search_ret_1_conds_def
            split: list.splits option.splits prod.splits)
  then show ?thesis
    using assms
    by auto
qed

lemma Disjoint_Paths_Search_simps:
  assumes "Disjoint_Paths_Search_dom state"
  shows "Disjoint_Paths_Search_call_1_conds state \<Longrightarrow>
           Disjoint_Paths_Search state = Disjoint_Paths_Search (Disjoint_Paths_Search_upd1 state)"
        "Disjoint_Paths_Search_call_2_conds state \<Longrightarrow>
           Disjoint_Paths_Search state = Disjoint_Paths_Search (Disjoint_Paths_Search_upd2 state)"
        "Disjoint_Paths_Search_ret_1_conds state \<Longrightarrow>
           Disjoint_Paths_Search state = Disjoint_Paths_Search_ret1 state"
  by (auto simp add: Disjoint_Paths_Search.psimps[OF assms] Let_def
                     Disjoint_Paths_Search_call_1_conds_def Disjoint_Paths_Search_upd1_def
                     Disjoint_Paths_Search_call_2_conds_def Disjoint_Paths_Search_upd2_def
                     Disjoint_Paths_Search_ret_1_conds_def
           split: list.splits option.splits prod.splits)

lemma Disjoint_Paths_Search_induct:
  assumes "Disjoint_Paths_Search_dom state"
  assumes "\<And>state. \<lbrakk>Disjoint_Paths_Search_dom state;
                     Disjoint_Paths_Search_call_1_conds state \<Longrightarrow> P (Disjoint_Paths_Search_upd1 state);
                     Disjoint_Paths_Search_call_2_conds state \<Longrightarrow> P (Disjoint_Paths_Search_upd2 state)\<rbrakk>
                    \<Longrightarrow> P state"
  shows "P state"
  apply(rule Disjoint_Paths_Search.pinduct[OF assms(1)])
  apply(rule assms(2)[simplified Disjoint_Paths_Search_call_1_conds_def Disjoint_Paths_Search_upd1_def
                                 Disjoint_Paths_Search_call_2_conds_def Disjoint_Paths_Search_upd2_def])
  by (auto simp: Let_def split: list.splits option.splits prod.splits)

lemma Disjoint_Paths_Search_domintros:
  assumes "Disjoint_Paths_Search_call_1_conds state \<Longrightarrow>
             Disjoint_Paths_Search_dom (Disjoint_Paths_Search_upd1 state)"
  assumes "Disjoint_Paths_Search_call_2_conds state \<Longrightarrow>
             Disjoint_Paths_Search_dom (Disjoint_Paths_Search_upd2 state)"
  shows "Disjoint_Paths_Search_dom state"
proof(rule Disjoint_Paths_Search.domintros, goal_cases)
  case (1 r rs explored')
  then show ?case
    using assms(2)[OF Disjoint_Paths_Search_call_2_condsI[OF 1(1) 1(2)[symmetric]]]
    by (simp add: Disjoint_Paths_Search_upd2_def 1(1) 1(2)[symmetric])
next
  case (2 r rs explored' p)
  then show ?case
    using assms(1)[OF Disjoint_Paths_Search_call_1_condsI[OF 2(1) 2(2)[symmetric]]]
    by (simp add: Disjoint_Paths_Search_upd1_def 2(1) 2(2)[symmetric])
qed

end

subsection \<open>Locale for the proofs\<close>

locale Disjoint_Paths_Search_thms = Disjoint_Paths_Search +
  assumes Disjoint_Paths_Search_axiom: Disjoint_Paths_Search_axiom
begin

context
  includes set_ops.automation2 and Graph.adjmap.automation and Graph.vset.set.automation
begin

lemma Disjoint_Paths_Search_axiom_props[simp]:
  "Graph.layered_graph_input G (SOME lev. Graph.layered_graph_input G lev)"
  "set initial_roots \<subseteq> dVs (Graph.digraph_abs G)"
  "vset_inv (blocked p)"
  "t_set (blocked p) \<subseteq> dVs (Graph.digraph_abs G)"
  using Disjoint_Paths_Search_axiom
  by (auto simp: Disjoint_Paths_Search_axiom_def intro: someI[of "Graph.layered_graph_input G"])

lemmas search_step_props = search_step[OF Disjoint_Paths_Search_axiom_props(1)]

subsection \<open>Invariants\<close>

lemma invar_1_props[invar_props_elims]:
  "invar_1 state \<Longrightarrow>
     (\<lbrakk>vset_inv (avoided state); vset_inv (explored state)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_1_def)

lemma invar_1_intro[invar_props_intros]:
  "\<lbrakk>vset_inv (avoided state); vset_inv (explored state)\<rbrakk> \<Longrightarrow> invar_1 state"
  by (auto simp: invar_1_def)

lemma invar_within_graph_props[invar_props_elims]:
  "invar_within_graph state \<Longrightarrow>
     (\<lbrakk>t_set (avoided state) \<subseteq> dVs (Graph.digraph_abs G);
       t_set (explored state) \<subseteq> dVs (Graph.digraph_abs G);
       set (roots state) \<subseteq> dVs (Graph.digraph_abs G)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_within_graph_def)

lemma invar_within_graph_intro[invar_props_intros]:
  "\<lbrakk>t_set (avoided state) \<subseteq> dVs (Graph.digraph_abs G);
    t_set (explored state) \<subseteq> dVs (Graph.digraph_abs G);
    set (roots state) \<subseteq> dVs (Graph.digraph_abs G)\<rbrakk> \<Longrightarrow> invar_within_graph state"
  by (auto simp: invar_within_graph_def)

lemma invar_roots_props[invar_props_elims]:
  "invar_roots state \<Longrightarrow> (set (roots state) \<subseteq> set initial_roots \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_roots_def)

lemma invar_roots_intro[invar_props_intros]:
  "set (roots state) \<subseteq> set initial_roots \<Longrightarrow> invar_roots state"
  by (auto simp: invar_roots_def)

lemma invar_paths_sound_props[invar_props_elims]:
  "invar_paths_sound state \<Longrightarrow>
     ((\<And>p. p \<in> set (paths state) \<Longrightarrow>
         Vwalk.vwalk (Graph.digraph_abs G) (rev p) \<and> p \<noteq> [] \<and> distinct p \<and> target (hd p) \<and>
         last p \<in> set initial_roots) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_paths_sound_def)

lemma invar_paths_sound_intro[invar_props_intros]:
  "(\<And>p. p \<in> set (paths state) \<Longrightarrow>
      Vwalk.vwalk (Graph.digraph_abs G) (rev p) \<and> p \<noteq> [] \<and> distinct p \<and> target (hd p) \<and>
      last p \<in> set initial_roots) \<Longrightarrow> invar_paths_sound state"
  by (auto simp: invar_paths_sound_def)

lemma invar_blocked_avoided_props[invar_props_elims]:
  "invar_blocked_avoided state \<Longrightarrow>
     ((\<And>p. p \<in> set (paths state) \<Longrightarrow> t_set (blocked p) \<subseteq> t_set (avoided state)) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_blocked_avoided_def)

lemma invar_blocked_avoided_intro[invar_props_intros]:
  "(\<And>p. p \<in> set (paths state) \<Longrightarrow> t_set (blocked p) \<subseteq> t_set (avoided state))
   \<Longrightarrow> invar_blocked_avoided state"
  by (auto simp: invar_blocked_avoided_def)

lemma invar_paths_disjoint_props[invar_props_elims]:
  "invar_paths_disjoint state \<Longrightarrow>
     (sorted_wrt (\<lambda>q p. set q \<inter> t_set (blocked p) = {}) (paths state) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_paths_disjoint_def)

lemma invar_paths_disjoint_intro[invar_props_intros]:
  "sorted_wrt (\<lambda>q p. set q \<inter> t_set (blocked p) = {}) (paths state) \<Longrightarrow> invar_paths_disjoint state"
  by (auto simp: invar_paths_disjoint_def)

lemma invar_explored_closed_props[invar_props_elims]:
  "invar_explored_closed state \<Longrightarrow>
     (\<lbrakk>paths state = [] \<longrightarrow> t_set (avoided state) = {};
       paths state = [] \<longrightarrow> set initial_roots \<subseteq> set (roots state) \<union> t_set (explored state);
       paths state = [] \<longrightarrow> (\<forall>v \<in> t_set (explored state). \<not> target v);
       paths state = [] \<longrightarrow> (\<forall>v w. v \<in> t_set (explored state) \<longrightarrow> (v, w) \<in> Graph.digraph_abs G \<longrightarrow>
                                   w \<in> t_set (explored state))\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding invar_explored_closed_def
  by blast

lemma invar_explored_closed_intro[invar_props_intros]:
  "\<lbrakk>paths state = [] \<longrightarrow> t_set (avoided state) = {};
    paths state = [] \<longrightarrow> set initial_roots \<subseteq> set (roots state) \<union> t_set (explored state);
    paths state = [] \<longrightarrow> (\<forall>v \<in> t_set (explored state). \<not> target v);
    paths state = [] \<longrightarrow> (\<forall>v w. v \<in> t_set (explored state) \<longrightarrow> (v, w) \<in> Graph.digraph_abs G \<longrightarrow>
                                w \<in> t_set (explored state))\<rbrakk>
   \<Longrightarrow> invar_explored_closed state"
  by (auto simp: invar_explored_closed_def)

text \<open>Preservation of \<^term>\<open>invar_1\<close>.\<close>

lemma invar_1_holds_upd1[invar_holds_intros]:
  "\<lbrakk>Disjoint_Paths_Search_call_1_conds state; invar_within_graph state; invar_1 state\<rbrakk>
   \<Longrightarrow> invar_1 (Disjoint_Paths_Search_upd1 state)"
  by (auto elim!: call_cond_elims invar_props_elims intro!: invar_props_intros
            intro: search_step_props(1) simp: Disjoint_Paths_Search_upd1_def)

lemma invar_1_holds_upd2[invar_holds_intros]:
  "\<lbrakk>Disjoint_Paths_Search_call_2_conds state; invar_within_graph state; invar_1 state\<rbrakk>
   \<Longrightarrow> invar_1 (Disjoint_Paths_Search_upd2 state)"
  by (auto elim!: call_cond_elims invar_props_elims intro!: invar_props_intros
            intro: search_step_props(1) simp: Disjoint_Paths_Search_upd2_def)

lemma invar_1_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>Disjoint_Paths_Search_ret_1_conds state; invar_1 state\<rbrakk>
   \<Longrightarrow> invar_1 (Disjoint_Paths_Search_ret1 state)"
  by auto


text \<open>Preservation of \<^term>\<open>invar_within_graph\<close>.\<close>

lemma invar_within_graph_holds_upd1[invar_holds_intros]:
  "\<lbrakk>Disjoint_Paths_Search_call_1_conds state; invar_1 state; invar_within_graph state\<rbrakk>
   \<Longrightarrow> invar_within_graph (Disjoint_Paths_Search_upd1 state)"
  by (auto elim!: call_cond_elims invar_props_elims intro!: invar_props_intros
            intro: subsetD[OF Disjoint_Paths_Search_axiom_props(4)]
            simp: Disjoint_Paths_Search_upd1_def)
     (blast dest: search_step_props(2))

lemma invar_within_graph_holds_upd2[invar_holds_intros]:
  "\<lbrakk>Disjoint_Paths_Search_call_2_conds state; invar_1 state; invar_within_graph state\<rbrakk>
   \<Longrightarrow> invar_within_graph (Disjoint_Paths_Search_upd2 state)"
  by (auto elim!: call_cond_elims invar_props_elims intro!: invar_props_intros
            simp: Disjoint_Paths_Search_upd2_def)
     (blast dest: search_step_props(2))

lemma invar_within_graph_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>Disjoint_Paths_Search_ret_1_conds state; invar_within_graph state\<rbrakk>
   \<Longrightarrow> invar_within_graph (Disjoint_Paths_Search_ret1 state)"
  by auto

lemma invar_1_holds[invar_holds_intros]:
  assumes "Disjoint_Paths_Search_dom state" "invar_1 state" "invar_within_graph state"
  shows "invar_1 (Disjoint_Paths_Search state)"
  using assms(2-)
proof(induction rule: Disjoint_Paths_Search_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    apply(rule Disjoint_Paths_Search_cases[where state = state])
    by (auto intro: IH(2-) invar_holds_intros simp: Disjoint_Paths_Search_simps[OF IH(1)])
qed

lemma invar_within_graph_holds[invar_holds_intros]:
  assumes "Disjoint_Paths_Search_dom state" "invar_1 state" "invar_within_graph state"
  shows "invar_within_graph (Disjoint_Paths_Search state)"
  using assms(2-)
proof(induction rule: Disjoint_Paths_Search_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    apply(rule Disjoint_Paths_Search_cases[where state = state])
    by (auto intro: IH(2-) invar_holds_intros simp: Disjoint_Paths_Search_simps[OF IH(1)])
qed

text \<open>Preservation of \<^term>\<open>invar_roots\<close>.\<close>

lemma invar_roots_holds_upd1[invar_holds_intros]:
  "\<lbrakk>Disjoint_Paths_Search_call_1_conds state; invar_roots state\<rbrakk>
   \<Longrightarrow> invar_roots (Disjoint_Paths_Search_upd1 state)"
  by (auto elim!: call_cond_elims invar_props_elims intro!: invar_props_intros
            simp: Disjoint_Paths_Search_upd1_def)

lemma invar_roots_holds_upd2[invar_holds_intros]:
  "\<lbrakk>Disjoint_Paths_Search_call_2_conds state; invar_roots state\<rbrakk>
   \<Longrightarrow> invar_roots (Disjoint_Paths_Search_upd2 state)"
  by (auto elim!: call_cond_elims invar_props_elims intro!: invar_props_intros
            simp: Disjoint_Paths_Search_upd2_def)

lemma invar_roots_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>Disjoint_Paths_Search_ret_1_conds state; invar_roots state\<rbrakk>
   \<Longrightarrow> invar_roots (Disjoint_Paths_Search_ret1 state)"
  by auto

lemma invar_roots_holds[invar_holds_intros]:
  assumes "Disjoint_Paths_Search_dom state" "invar_roots state"
  shows "invar_roots (Disjoint_Paths_Search state)"
  using assms(2-)
proof(induction rule: Disjoint_Paths_Search_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    apply(rule Disjoint_Paths_Search_cases[where state = state])
    by (auto intro: IH(2-) invar_holds_intros simp: Disjoint_Paths_Search_simps[OF IH(1)])
qed

text \<open>Preservation of \<^term>\<open>invar_paths_sound\<close>.\<close>

lemma invar_paths_sound_holds_upd1[invar_holds_intros]:
  "\<lbrakk>Disjoint_Paths_Search_call_1_conds state; invar_1 state; invar_within_graph state;
    invar_roots state; invar_paths_sound state\<rbrakk>
   \<Longrightarrow> invar_paths_sound (Disjoint_Paths_Search_upd1 state)"
  by (auto elim!: call_cond_elims invar_props_elims intro!: invar_props_intros
                 dest: search_step_props(7) simp: Disjoint_Paths_Search_upd1_def)

lemma invar_paths_sound_holds_upd2[invar_holds_intros]:
  "\<lbrakk>Disjoint_Paths_Search_call_2_conds state; invar_paths_sound state\<rbrakk>
   \<Longrightarrow> invar_paths_sound (Disjoint_Paths_Search_upd2 state)"
  by (auto elim!: call_cond_elims invar_props_elims intro!: invar_props_intros
            simp: Disjoint_Paths_Search_upd2_def)

lemma invar_paths_sound_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>Disjoint_Paths_Search_ret_1_conds state; invar_paths_sound state\<rbrakk>
   \<Longrightarrow> invar_paths_sound (Disjoint_Paths_Search_ret1 state)"
  by auto

lemma invar_paths_sound_holds[invar_holds_intros]:
  assumes "Disjoint_Paths_Search_dom state" "invar_1 state" "invar_within_graph state"
          "invar_roots state" "invar_paths_sound state"
  shows "invar_paths_sound (Disjoint_Paths_Search state)"
  using assms(2-)
proof(induction rule: Disjoint_Paths_Search_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    apply(rule Disjoint_Paths_Search_cases[where state = state])
    by (auto intro: IH(2-) invar_holds_intros simp: Disjoint_Paths_Search_simps[OF IH(1)])
qed

text \<open>Preservation of \<^term>\<open>invar_blocked_avoided\<close>.\<close>

lemma invar_blocked_avoided_holds_upd1[invar_holds_intros]:
  "\<lbrakk>Disjoint_Paths_Search_call_1_conds state; invar_1 state; invar_blocked_avoided state\<rbrakk>
   \<Longrightarrow> invar_blocked_avoided (Disjoint_Paths_Search_upd1 state)"
  by (fastforce elim!: call_cond_elims invar_props_elims intro!: invar_props_intros
                 simp: Disjoint_Paths_Search_upd1_def)

lemma invar_blocked_avoided_holds_upd2[invar_holds_intros]:
  "\<lbrakk>Disjoint_Paths_Search_call_2_conds state; invar_blocked_avoided state\<rbrakk>
   \<Longrightarrow> invar_blocked_avoided (Disjoint_Paths_Search_upd2 state)"
  by (fastforce elim!: call_cond_elims invar_props_elims intro!: invar_props_intros
                 simp: Disjoint_Paths_Search_upd2_def)

lemma invar_blocked_avoided_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>Disjoint_Paths_Search_ret_1_conds state; invar_blocked_avoided state\<rbrakk>
   \<Longrightarrow> invar_blocked_avoided (Disjoint_Paths_Search_ret1 state)"
  by auto

lemma invar_blocked_avoided_holds[invar_holds_intros]:
  assumes "Disjoint_Paths_Search_dom state" "invar_1 state" "invar_within_graph state"
          "invar_blocked_avoided state"
  shows "invar_blocked_avoided (Disjoint_Paths_Search state)"
  using assms(2-)
proof(induction rule: Disjoint_Paths_Search_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    apply(rule Disjoint_Paths_Search_cases[where state = state])
    by (auto intro: IH(2-) invar_holds_intros simp: Disjoint_Paths_Search_simps[OF IH(1)])
qed

text \<open>Preservation of \<^term>\<open>invar_paths_disjoint\<close>: the new path misses the avoided set, which
  contains the blocked set of every earlier path.\<close>

lemma invar_paths_disjoint_holds_upd1[invar_holds_intros]:
  "\<lbrakk>Disjoint_Paths_Search_call_1_conds state; invar_1 state; invar_within_graph state;
    invar_blocked_avoided state; invar_paths_disjoint state\<rbrakk>
   \<Longrightarrow> invar_paths_disjoint (Disjoint_Paths_Search_upd1 state)"
  by (auto elim!: call_cond_elims invar_props_elims intro!: invar_props_intros
                 dest: search_step_props(7) simp: Disjoint_Paths_Search_upd1_def)
     (blast dest: search_step_props(7))

lemma invar_paths_disjoint_holds_upd2[invar_holds_intros]:
  "\<lbrakk>Disjoint_Paths_Search_call_2_conds state; invar_paths_disjoint state\<rbrakk>
   \<Longrightarrow> invar_paths_disjoint (Disjoint_Paths_Search_upd2 state)"
  by (auto elim!: call_cond_elims invar_props_elims intro!: invar_props_intros
            simp: Disjoint_Paths_Search_upd2_def)

lemma invar_paths_disjoint_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>Disjoint_Paths_Search_ret_1_conds state; invar_paths_disjoint state\<rbrakk>
   \<Longrightarrow> invar_paths_disjoint (Disjoint_Paths_Search_ret1 state)"
  by auto

lemma invar_paths_disjoint_holds[invar_holds_intros]:
  assumes "Disjoint_Paths_Search_dom state" "invar_1 state" "invar_within_graph state"
          "invar_blocked_avoided state" "invar_paths_disjoint state"
  shows "invar_paths_disjoint (Disjoint_Paths_Search state)"
  using assms(2-)
proof(induction rule: Disjoint_Paths_Search_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    apply(rule Disjoint_Paths_Search_cases[where state = state])
    by (auto intro: IH(2-) invar_holds_intros simp: Disjoint_Paths_Search_simps[OF IH(1)])
qed

text \<open>Preservation of \<^term>\<open>invar_explored_closed\<close>. After a successful search the invariant
  holds vacuously. After an unsuccessful one, with nothing avoided yet: the root is now
  explored, the newly explored vertices are not targets, and their successors are explored;
  the previously explored set was already closed.\<close>

lemma invar_explored_closed_holds_upd1[invar_holds_intros]:
  "\<lbrakk>Disjoint_Paths_Search_call_1_conds state; invar_explored_closed state\<rbrakk>
   \<Longrightarrow> invar_explored_closed (Disjoint_Paths_Search_upd1 state)"
  by (auto elim!: call_cond_elims intro!: invar_props_intros
            simp: Disjoint_Paths_Search_upd1_def)

lemma invar_explored_closed_holds_upd2[invar_holds_intros]:
  assumes "Disjoint_Paths_Search_call_2_conds state" "invar_1 state" "invar_within_graph state"
          "invar_explored_closed state"
  shows "invar_explored_closed (Disjoint_Paths_Search_upd2 state)"
proof-
  obtain r rs explored' where step: "roots state = r # rs"
      "search_step (avoided state) r (explored state) = (None, explored')"
    using assms(1)
    by (auto elim!: call_cond_elims)
  hence upd: "Disjoint_Paths_Search_upd2 state = state \<lparr>roots := rs, explored := explored'\<rparr>"
    by (simp add: Disjoint_Paths_Search_upd2_def)
  have pre: "vset_inv (avoided state)" "vset_inv (explored state)"
            "t_set (avoided state) \<subseteq> dVs (Graph.digraph_abs G)"
            "t_set (explored state) \<subseteq> dVs (Graph.digraph_abs G)" "r \<in> dVs (Graph.digraph_abs G)"
    using assms(2,3) step(1)
    by (auto elim!: invar_props_elims)
  note props = search_step_props(3-6)[OF pre step(2)]
  show ?thesis
  proof(cases "paths state = []")
    case True
    note H = assms(4)[unfolded invar_explored_closed_def, THEN mp, OF True]
    have av: "t_set (avoided state) = {}"
      using H
      by blast
    have r: "r \<in> t_set explored'"
      using props(2) av
      by simp
    have a: "set initial_roots \<subseteq> set rs \<union> t_set explored'"
      using H props(1) step(1) r
      by auto
    have b: "\<forall>v\<in>t_set explored'. \<not> target v"
      using H props(1,4)
      by blast
    have c: "\<forall>v w. v \<in> t_set explored' \<longrightarrow> (v, w) \<in> Graph.digraph_abs G \<longrightarrow> w \<in> t_set explored'"
      using H props(1,3) av
      by blast
    show ?thesis
      unfolding upd invar_explored_closed_def
      using True av a b c
      by simp
  next
    case False
    then show ?thesis
      unfolding upd invar_explored_closed_def
      by simp
  qed
qed

lemma invar_explored_closed_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>Disjoint_Paths_Search_ret_1_conds state; invar_explored_closed state\<rbrakk>
   \<Longrightarrow> invar_explored_closed (Disjoint_Paths_Search_ret1 state)"
  by auto

lemma invar_explored_closed_holds[invar_holds_intros]:
  assumes "Disjoint_Paths_Search_dom state" "invar_1 state" "invar_within_graph state"
          "invar_explored_closed state"
  shows "invar_explored_closed (Disjoint_Paths_Search state)"
  using assms(2-)
proof(induction rule: Disjoint_Paths_Search_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    apply(rule Disjoint_Paths_Search_cases[where state = state])
    by (auto intro: IH(2-) invar_holds_intros simp: Disjoint_Paths_Search_simps[OF IH(1)])
qed

subsection \<open>Termination\<close>

named_theorems termination_intros

lemma call_1_terminates[termination_intros]:
  "Disjoint_Paths_Search_call_1_conds state \<Longrightarrow>
     (Disjoint_Paths_Search_upd1 state, state) \<in> call_1_measure <*mlex*> r"
  by (auto elim!: call_cond_elims intro!: mlex_less
            simp: call_1_measure_def Disjoint_Paths_Search_upd1_def)

lemma call_2_terminates[termination_intros]:
  "Disjoint_Paths_Search_call_2_conds state \<Longrightarrow>
     (Disjoint_Paths_Search_upd2 state, state) \<in> call_1_measure <*mlex*> r"
  by (auto elim!: call_cond_elims intro!: mlex_less
            simp: call_1_measure_def Disjoint_Paths_Search_upd2_def)

lemma wf_term_rel: "wf Disjoint_Paths_Search_term_rel'"
  by (auto simp: wf_mlex Disjoint_Paths_Search_term_rel'_def)

lemma in_Disjoint_Paths_Search_term_rel'[termination_intros]:
  "Disjoint_Paths_Search_call_1_conds state \<Longrightarrow>
     (Disjoint_Paths_Search_upd1 state, state) \<in> Disjoint_Paths_Search_term_rel'"
  "Disjoint_Paths_Search_call_2_conds state \<Longrightarrow>
     (Disjoint_Paths_Search_upd2 state, state) \<in> Disjoint_Paths_Search_term_rel'"
  by (simp add: Disjoint_Paths_Search_term_rel'_def termination_intros)+

lemma Disjoint_Paths_Search_terminates[termination_intros]:
  "Disjoint_Paths_Search_dom state"
  using wf_term_rel
proof(induction rule: wf_induct_rule)
  case (less state)
  show ?case
    by (rule Disjoint_Paths_Search_domintros)
       (auto intro!: less in_Disjoint_Paths_Search_term_rel')
qed

subsection \<open>Correctness\<close>

lemma Disjoint_Paths_Search_correct_1_ret_1:
  "\<lbrakk>invar_paths_sound state; Disjoint_Paths_Search_ret_1_conds state; p \<in> set (paths state)\<rbrakk>
   \<Longrightarrow> Vwalk.vwalk (Graph.digraph_abs G) (rev p) \<and> p \<noteq> [] \<and> distinct p \<and> target (hd p) \<and>
       last p \<in> set initial_roots"
  by (auto elim!: invar_props_elims)

lemma Disjoint_Paths_Search_correct_2_ret_1:
  "\<lbrakk>invar_paths_disjoint state; Disjoint_Paths_Search_ret_1_conds state\<rbrakk>
   \<Longrightarrow> sorted_wrt (\<lambda>q p. set q \<inter> t_set (blocked p) = {}) (paths state)"
  by (auto elim!: invar_props_elims)

lemma Disjoint_Paths_Search_correct_3_ret_1:
  "\<lbrakk>invar_explored_closed state; Disjoint_Paths_Search_ret_1_conds state;
    r \<in> set initial_roots; Vwalk.vwalk_bet (Graph.digraph_abs G) r q z; target z\<rbrakk>
   \<Longrightarrow> paths state \<noteq> []"
  by (auto elim!: call_cond_elims invar_props_elims)
     (blast dest: vwalk_bet_closed[where S = "t_set (explored state)"])

lemma ret1_holds[ret_holds_intros]:
  assumes "Disjoint_Paths_Search_dom state"
  shows "Disjoint_Paths_Search_ret_1_conds (Disjoint_Paths_Search state)"
proof(induction rule: Disjoint_Paths_Search_induct[OF assms])
  case IH: (1 state)
  show ?case
    apply(rule Disjoint_Paths_Search_cases[where state = state])
    by (auto intro!: IH(2-) simp: Disjoint_Paths_Search_simps[OF IH(1)])
qed

subsection \<open>The initial state\<close>

lemma initial_state_props[invar_holds_intros, termination_intros]:
  "invar_1 initial_state" "invar_within_graph initial_state" "invar_roots initial_state"
  "invar_paths_sound initial_state" "invar_blocked_avoided initial_state"
  "invar_paths_disjoint initial_state" "invar_explored_closed initial_state"
  "Disjoint_Paths_Search_dom initial_state"
  by (auto intro!: invar_props_intros Disjoint_Paths_Search_terminates
            intro: subsetD[OF Disjoint_Paths_Search_axiom_props(2)] simp: initial_state_def)

lemma Disjoint_Paths_Search_impl_to_Disjoint_Paths_Search:
  "Disjoint_Paths_Search_impl initial_state = Disjoint_Paths_Search initial_state"
  by (auto intro!: Disjoint_Paths_Search_impl_same initial_state_props)

subsection \<open>Final correctness\<close>

lemma Disjoint_Paths_Search_correct_1:
  "p \<in> set (paths (Disjoint_Paths_Search initial_state)) \<Longrightarrow>
   Vwalk.vwalk (Graph.digraph_abs G) (rev p) \<and> p \<noteq> [] \<and> distinct p \<and> target (hd p) \<and>
   last p \<in> set initial_roots"
  apply(intro Disjoint_Paths_Search_correct_1_ret_1[where state = "Disjoint_Paths_Search initial_state"])
  by(auto intro: invar_holds_intros ret_holds_intros)

lemma Disjoint_Paths_Search_correct_2:
  "sorted_wrt (\<lambda>q p. set q \<inter> t_set (blocked p) = {}) (paths (Disjoint_Paths_Search initial_state))"
  apply(intro Disjoint_Paths_Search_correct_2_ret_1[where state = "Disjoint_Paths_Search initial_state"])
  by(auto intro: invar_holds_intros ret_holds_intros)

lemma Disjoint_Paths_Search_correct_3:
  "\<lbrakk>r \<in> set initial_roots; Vwalk.vwalk_bet (Graph.digraph_abs G) r q z; target z\<rbrakk>
   \<Longrightarrow> paths (Disjoint_Paths_Search initial_state) \<noteq> []"
  apply(intro Disjoint_Paths_Search_correct_3_ret_1[where state = "Disjoint_Paths_Search initial_state"])
  by(auto intro: invar_holds_intros ret_holds_intros)

end

end

end
