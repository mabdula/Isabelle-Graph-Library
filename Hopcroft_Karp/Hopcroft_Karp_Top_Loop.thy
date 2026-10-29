theory Hopcroft_Karp_Top_Loop
  imports "Basic_Matching.Berge" "Undirected_Set_Graphs.Bipartite"
          "Directed_Set_Graphs.Pair_Graph_Specs"
begin

section \<open>Top Loop of the Hopcroft-Karp Algorithm\<close>

subsection \<open>Augmenting along vertex-disjoint augmenting paths\<close>

lemma edges_of_path_disjoint:
  "\<lbrakk>e \<in> set (edges_of_path q); set p \<inter> set q = {}\<rbrakk> \<Longrightarrow> e \<notin> set (edges_of_path p)"
  using edges_of_path_Vs[of p] edges_of_path_Vs[of q]
  by (fastforce simp: Vs_def dest!: in_edges_of_path_split)

lemma augmenting_path_disjoint_preserved:
  assumes "matching M" "graph_augmenting_path G M p" "graph_augmenting_path G M q"
          "set p \<inter> set q = {}"
  shows "graph_augmenting_path G (M \<oplus> set (edges_of_path p)) q"
proof-
  let ?M' = "M \<oplus> set (edges_of_path p)"
  have same: "\<And>e. e \<in> set (edges_of_path q) \<Longrightarrow> e \<in> ?M' \<longleftrightarrow> e \<in> M"
    using assms(4)
    by (auto simp: in_symmetric_diff_iff dest: edges_of_path_disjoint)
  have "alt_list (\<lambda>e. e \<notin> ?M') (\<lambda>e. e \<in> M) (edges_of_path q)"
    by (rule alt_list_cong_2[of "\<lambda>e. e \<notin> M"])
       (use assms(3) same in \<open>auto simp: matching_augmenting_path_def\<close>)
  hence "alt_path ?M' q"
    by (rule alt_list_cong_1) (auto simp: same)
  moreover have "Vs ?M' = {hd p, last p} \<union> Vs M"
    using assms(1,2) aug_paths_are_even
    by (auto simp: rematch_atl_path_Vs_change matching_augmenting_path_def)
  moreover have "hd p \<in> set p" "last p \<in> set p" "hd q \<in> set q" "last q \<in> set q"
  proof-
    have "p \<noteq> []"
      using assms(2)
      by (intro notI) (simp add: matching_augmenting_path_def)
    moreover have "q \<noteq> []"
      using assms(3)
      by (intro notI) (simp add: matching_augmenting_path_def)
    ultimately show "hd p \<in> set p" "last p \<in> set p" "hd q \<in> set q" "last q \<in> set q"
      by simp_all
  qed
  ultimately show ?thesis
    using assms(3,4)
    by (auto simp: matching_augmenting_path_def disjoint_iff)
qed

subsection \<open>The program state\<close>

record 'matching Hopcroft_Karp_Loop_state =
  current_matching :: 'matching
  phases :: nat

subsection \<open>Setup for automation\<close>

named_theorems call_cond_elims
named_theorems call_cond_intros
named_theorems ret_holds_intros
named_theorems invar_props_intros
named_theorems invar_props_elims
named_theorems invar_holds_intros

subsection \<open>The input\<close>

locale Hopcroft_Karp_Input =
  Graph: Pair_Graph_Specs_Read_Only where lookup = lookup
  for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option" +
  fixes G :: 'adjmap and vertex_list :: "'v list"
begin

definition "ugraph_abs = {{u, v} | u v. (u, v) \<in> Graph.digraph_abs G}"

definition "Hopcroft_Karp_axiom =
  (Graph.graph_inv G \<and> Graph.finite_graph G \<and> Graph.finite_vsets G \<and>
   (\<forall>u v. (u, v) \<in> Graph.digraph_abs G \<longrightarrow> (v, u) \<in> Graph.digraph_abs G) \<and>
   (\<forall>u. (u, u) \<notin> Graph.digraph_abs G) \<and>
   set vertex_list = dVs (Graph.digraph_abs G) \<and>
   (\<exists>X Y. bipartite ugraph_abs X Y))"

end

subsection \<open>The loop\<close>

locale Hopcroft_Karp_Loop = Hopcroft_Karp_Input where lookup = lookup
  for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option" +
  fixes empty_matching :: 'matching
    and augment :: "'matching \<Rightarrow> 'v list \<Rightarrow> 'matching"
    and matching_invar :: "'matching \<Rightarrow> bool"
    and matching_abstract :: "'matching \<Rightarrow> 'v set set"
    and phase :: "'matching \<Rightarrow> 'v list list"
begin

function (domintros) Hopcroft_Karp_Loop ::
  "'matching Hopcroft_Karp_Loop_state \<Rightarrow> 'matching Hopcroft_Karp_Loop_state" where
  "Hopcroft_Karp_Loop state =
     (if phase (current_matching state) \<noteq> [] then
        let paths = phase (current_matching state) in
        Hopcroft_Karp_Loop
          (state \<lparr>current_matching := foldl augment (current_matching state) paths,
                  phases := Suc (phases state)\<rparr>)
      else state)"
  by pat_completeness auto

partial_function (tailrec) Hopcroft_Karp_Loop_impl ::
  "'matching Hopcroft_Karp_Loop_state \<Rightarrow> 'matching Hopcroft_Karp_Loop_state" where
  "Hopcroft_Karp_Loop_impl state =
     (if phase (current_matching state) \<noteq> [] then
        let paths = phase (current_matching state) in
        Hopcroft_Karp_Loop_impl
          (state \<lparr>current_matching := foldl augment (current_matching state) paths,
                  phases := Suc (phases state)\<rparr>)
      else state)"

lemma Hopcroft_Karp_Loop_impl_same:
  assumes "Hopcroft_Karp_Loop_dom state"
  shows "Hopcroft_Karp_Loop_impl state = Hopcroft_Karp_Loop state"
  by(induction rule: Hopcroft_Karp_Loop.pinduct[OF assms])
    (auto simp add: Hopcroft_Karp_Loop_impl.simps Hopcroft_Karp_Loop.psimps)

definition "initial_state = \<lparr>current_matching = empty_matching, phases = 0\<rparr>"

definition "Hopcroft_Karp_Loop_run = Hopcroft_Karp_Loop initial_state"

definition "Hopcroft_Karp_Loop_run_impl = Hopcroft_Karp_Loop_impl initial_state"

lemmas [code] = Hopcroft_Karp_Loop_impl.simps initial_state_def Hopcroft_Karp_Loop_run_impl_def

definition "Hopcroft_Karp_Loop_call_1_conds state = (phase (current_matching state) \<noteq> [])"

definition "Hopcroft_Karp_Loop_upd1 state =
  (let paths = phase (current_matching state) in
   state \<lparr>current_matching := foldl augment (current_matching state) paths,
          phases := Suc (phases state)\<rparr>)"

definition "Hopcroft_Karp_Loop_ret_1_conds state = (phase (current_matching state) = [])"

abbreviation "Hopcroft_Karp_Loop_ret1 state \<equiv> state"

definition "invar_matching state = matching_invar (current_matching state)"

definition "call_1_measure state = card ugraph_abs - card (matching_abstract (current_matching state))"

definition "Hopcroft_Karp_Loop_term_rel' = call_1_measure <*mlex*> {}"

lemma Hopcroft_Karp_Loop_call_1_conds[call_cond_elims]:
  "Hopcroft_Karp_Loop_call_1_conds state \<Longrightarrow> (phase (current_matching state) \<noteq> [] \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: Hopcroft_Karp_Loop_call_1_conds_def)

lemma Hopcroft_Karp_Loop_call_1_condsI[call_cond_intros]:
  "phase (current_matching state) \<noteq> [] \<Longrightarrow> Hopcroft_Karp_Loop_call_1_conds state"
  by (auto simp: Hopcroft_Karp_Loop_call_1_conds_def)

lemma Hopcroft_Karp_Loop_ret_1_conds[call_cond_elims]:
  "Hopcroft_Karp_Loop_ret_1_conds state \<Longrightarrow> (phase (current_matching state) = [] \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: Hopcroft_Karp_Loop_ret_1_conds_def)

lemma Hopcroft_Karp_Loop_ret_1_condsI[call_cond_intros]:
  "phase (current_matching state) = [] \<Longrightarrow> Hopcroft_Karp_Loop_ret_1_conds state"
  by (auto simp: Hopcroft_Karp_Loop_ret_1_conds_def)

lemma Hopcroft_Karp_Loop_cases:
  assumes "Hopcroft_Karp_Loop_call_1_conds state \<Longrightarrow> P"
          "Hopcroft_Karp_Loop_ret_1_conds state \<Longrightarrow> P"
  shows "P"
  using assms
  by (auto simp: Hopcroft_Karp_Loop_call_1_conds_def Hopcroft_Karp_Loop_ret_1_conds_def)

lemma Hopcroft_Karp_Loop_simps:
  assumes "Hopcroft_Karp_Loop_dom state"
  shows "Hopcroft_Karp_Loop_call_1_conds state \<Longrightarrow>
           Hopcroft_Karp_Loop state = Hopcroft_Karp_Loop (Hopcroft_Karp_Loop_upd1 state)"
        "Hopcroft_Karp_Loop_ret_1_conds state \<Longrightarrow>
           Hopcroft_Karp_Loop state = Hopcroft_Karp_Loop_ret1 state"
  by (auto simp: Hopcroft_Karp_Loop.psimps[OF assms] Let_def Hopcroft_Karp_Loop_upd1_def
                 Hopcroft_Karp_Loop_call_1_conds_def Hopcroft_Karp_Loop_ret_1_conds_def)

lemma Hopcroft_Karp_Loop_induct:
  assumes "Hopcroft_Karp_Loop_dom state"
  assumes "\<And>state. \<lbrakk>Hopcroft_Karp_Loop_dom state;
                     Hopcroft_Karp_Loop_call_1_conds state \<Longrightarrow> P (Hopcroft_Karp_Loop_upd1 state)\<rbrakk>
                    \<Longrightarrow> P state"
  shows "P state"
  apply(rule Hopcroft_Karp_Loop.pinduct[OF assms(1)])
  apply(rule assms(2)[simplified Hopcroft_Karp_Loop_call_1_conds_def Hopcroft_Karp_Loop_upd1_def])
  by (auto simp: Let_def)

lemma Hopcroft_Karp_Loop_domintros:
  assumes "Hopcroft_Karp_Loop_call_1_conds state \<Longrightarrow>
             Hopcroft_Karp_Loop_dom (Hopcroft_Karp_Loop_upd1 state)"
  shows "Hopcroft_Karp_Loop_dom state"
  using assms
  by (auto intro: Hopcroft_Karp_Loop.domintros
           simp: Hopcroft_Karp_Loop_call_1_conds_def Hopcroft_Karp_Loop_upd1_def Let_def)

end

subsection \<open>Locale for the proofs\<close>

locale Hopcroft_Karp_Loop_thms = Hopcroft_Karp_Loop +
  assumes matching:
      "\<And>M. matching_invar M \<Longrightarrow> graph_matching ugraph_abs (matching_abstract M)"
      "matching_invar empty_matching"
      "matching_abstract empty_matching = {}"
    and augment:
      "\<And>M p. \<lbrakk>matching_invar M; graph_augmenting_path ugraph_abs (matching_abstract M) p\<rbrakk>
         \<Longrightarrow> matching_invar (augment M p)"
      "\<And>M p. \<lbrakk>matching_invar M; graph_augmenting_path ugraph_abs (matching_abstract M) p\<rbrakk>
         \<Longrightarrow> matching_abstract (augment M p) = matching_abstract M \<oplus> set (edges_of_path p)"
    and phase:
      "\<And>M p. \<lbrakk>Hopcroft_Karp_axiom; matching_invar M; p \<in> set (phase M)\<rbrakk>
         \<Longrightarrow> graph_augmenting_path ugraph_abs (matching_abstract M) p"
      "\<And>M. \<lbrakk>Hopcroft_Karp_axiom; matching_invar M\<rbrakk>
         \<Longrightarrow> sorted_wrt (\<lambda>p q. set p \<inter> set q = {}) (phase M)"
      "\<And>M. \<lbrakk>Hopcroft_Karp_axiom; matching_invar M;
             \<exists>p. graph_augmenting_path ugraph_abs (matching_abstract M) p\<rbrakk>
         \<Longrightarrow> phase M \<noteq> []"
    and Hopcroft_Karp_axiom: Hopcroft_Karp_axiom
begin

lemma ugraph_abs_graph_invar[simp]: "graph_invar ugraph_abs"
proof(rule conjI)
  show "dblton_graph ugraph_abs"
    using Hopcroft_Karp_axiom
    by (fastforce simp: dblton_graph_def ugraph_abs_def Hopcroft_Karp_axiom_def)
  have "Vs ugraph_abs \<subseteq> dVs (Graph.digraph_abs G)"
    by (auto simp: ugraph_abs_def Vs_def)
  thus "finite (Vs ugraph_abs)"
    using Hopcroft_Karp_axiom Graph.finite_vertices
    by (auto simp: Hopcroft_Karp_axiom_def intro: finite_subset)
qed

lemma finite_ugraph_abs[simp]: "finite ugraph_abs"
  by (simp add: finite_Vs_then_finite)

lemmas phase_props[simp] = phase[OF Hopcroft_Karp_axiom]

lemma graph_matching_finite: "graph_matching ugraph_abs M \<Longrightarrow> finite M"
  by (auto intro: finite_subset)

lemma foldl_augment_props:
  "\<lbrakk>matching_invar M; \<forall>p \<in> set ps. graph_augmenting_path ugraph_abs (matching_abstract M) p;
    sorted_wrt (\<lambda>p q. set p \<inter> set q = {}) ps\<rbrakk>
   \<Longrightarrow> matching_invar (foldl augment M ps) \<and>
       card (matching_abstract (foldl augment M ps)) = card (matching_abstract M) + length ps"
proof(induction ps arbitrary: M)
  case (Cons p ps)
  have gm: "graph_matching ugraph_abs (matching_abstract M)"
    using Cons.prems(1)
    by (rule matching(1))
  have "matching (matching_abstract M)" "finite (matching_abstract M)"
    using gm
    by (auto intro: graph_matching_finite)
  moreover have "graph_augmenting_path ugraph_abs (matching_abstract M) p"
    using Cons.prems(2)
    by simp
  moreover have "\<forall>q \<in> set ps. graph_augmenting_path ugraph_abs (matching_abstract (augment M p)) q"
    using Cons.prems calculation augmenting_path_disjoint_preserved[of "matching_abstract M" ugraph_abs p]
    by (auto simp: augment(2))
  moreover have "matching_invar (augment M p)"
    using Cons.prems(1) calculation
    by (auto intro: augment(1))
  moreover have "card (matching_abstract (augment M p)) = card (matching_abstract M) + 1"
    using Cons.prems(1) calculation new_matching_plus_one[of "matching_abstract M" p]
    by (auto simp: augment(2))
  ultimately show ?case
    using Cons.IH[of "augment M p"] Cons.prems(3)
    by auto
qed simp

lemmas foldl_augment_invar = foldl_augment_props[THEN conjunct1]
lemmas foldl_augment_card = foldl_augment_props[THEN conjunct2]

subsection \<open>Invariant\<close>

lemma invar_matching_props[invar_props_elims]:
  "invar_matching state \<Longrightarrow> (matching_invar (current_matching state) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_matching_def)

lemma invar_matching_intro[invar_props_intros]:
  "matching_invar (current_matching state) \<Longrightarrow> invar_matching state"
  by (auto simp: invar_matching_def)

lemma invar_matching_holds_upd1[invar_holds_intros]:
  "\<lbrakk>Hopcroft_Karp_Loop_call_1_conds state; invar_matching state\<rbrakk>
   \<Longrightarrow> invar_matching (Hopcroft_Karp_Loop_upd1 state)"
  by (auto elim!: invar_props_elims
          intro!: invar_props_intros foldl_augment_invar
            simp: Hopcroft_Karp_Loop_upd1_def Let_def)

lemma invar_matching_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>Hopcroft_Karp_Loop_ret_1_conds state; invar_matching state\<rbrakk>
   \<Longrightarrow> invar_matching (Hopcroft_Karp_Loop_ret1 state)"
  by auto

lemma invar_matching_holds[invar_holds_intros]:
  assumes "Hopcroft_Karp_Loop_dom state" "invar_matching state"
  shows "invar_matching (Hopcroft_Karp_Loop state)"
  using assms(2)
proof(induction rule: Hopcroft_Karp_Loop_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    apply(rule Hopcroft_Karp_Loop_cases[where state = state])
    by (auto intro: IH(2-) invar_holds_intros simp: Hopcroft_Karp_Loop_simps[OF IH(1)])
qed

subsection \<open>Termination\<close>

named_theorems termination_intros

lemma call_1_terminates[termination_intros]:
  assumes "Hopcroft_Karp_Loop_call_1_conds state" "invar_matching state"
  shows "(Hopcroft_Karp_Loop_upd1 state, state) \<in> call_1_measure <*mlex*> r"
proof-
  let ?M = "current_matching state"
  have "matching_invar (foldl augment ?M (phase ?M))"
       "card (matching_abstract (foldl augment ?M (phase ?M))) =
          card (matching_abstract ?M) + length (phase ?M)"
    using assms
    by (auto elim!: call_cond_elims invar_props_elims intro!: foldl_augment_invar
              simp: foldl_augment_card)
  moreover have "phase ?M \<noteq> []"
    using assms(1)
    by (auto elim!: call_cond_elims)
  moreover have "card (matching_abstract (foldl augment ?M (phase ?M))) \<le> card ugraph_abs"
    using calculation(1)
    by (auto dest!: matching(1) intro!: card_mono)
  ultimately show ?thesis
    using length_greater_0_conv[of "phase ?M", THEN iffD2]
    by (intro mlex_less)
       (auto simp: call_1_measure_def Hopcroft_Karp_Loop_upd1_def Let_def
             simp del: length_greater_0_conv; presburger)
qed

lemma wf_term_rel: "wf Hopcroft_Karp_Loop_term_rel'"
  by (auto simp: wf_mlex Hopcroft_Karp_Loop_term_rel'_def)

lemma in_Hopcroft_Karp_Loop_term_rel'[termination_intros]:
  "\<lbrakk>Hopcroft_Karp_Loop_call_1_conds state; invar_matching state\<rbrakk> \<Longrightarrow>
     (Hopcroft_Karp_Loop_upd1 state, state) \<in> Hopcroft_Karp_Loop_term_rel'"
  by (simp add: Hopcroft_Karp_Loop_term_rel'_def termination_intros)

lemma Hopcroft_Karp_Loop_terminates[termination_intros]:
  assumes "invar_matching state"
  shows "Hopcroft_Karp_Loop_dom state"
  using wf_term_rel assms
proof(induction rule: wf_induct_rule)
  case (less x)
  show ?case
    by (rule Hopcroft_Karp_Loop_domintros)
       (auto intro: invar_holds_intros less in_Hopcroft_Karp_Loop_term_rel')
qed

subsection \<open>Correctness\<close>

lemma Hopcroft_Karp_Loop_correct_ret_1:
  "\<lbrakk>invar_matching state; Hopcroft_Karp_Loop_ret_1_conds state\<rbrakk>
   \<Longrightarrow> max_card_matching ugraph_abs (matching_abstract (current_matching state))"
proof(elim invar_props_elims call_cond_elims)
  assume "matching_invar (current_matching state)" "phase (current_matching state) = []"
  hence "\<nexists>p. graph_augmenting_path ugraph_abs (matching_abstract (current_matching state)) p"
    using phase_props(3)
    by blast
  thus ?thesis
    using matching(1)[OF \<open>matching_invar (current_matching state)\<close>]
          Berge[of "matching_abstract (current_matching state)" ugraph_abs] graph_matching_finite
    by (auto simp: max_card_matching_def not_le)
qed

lemma ret1_holds[ret_holds_intros]:
  assumes "Hopcroft_Karp_Loop_dom state"
  shows "Hopcroft_Karp_Loop_ret_1_conds (Hopcroft_Karp_Loop state)"
proof(induction rule: Hopcroft_Karp_Loop_induct[OF assms])
  case IH: (1 state)
  show ?case
    apply(rule Hopcroft_Karp_Loop_cases[where state = state])
    by (auto intro!: IH(2-) intro: call_cond_intros simp: Hopcroft_Karp_Loop_simps[OF IH(1)]
             elim!: call_cond_elims)
qed

subsection \<open>The initial state\<close>

lemma initial_state_props[invar_holds_intros, termination_intros]:
  "invar_matching initial_state" "Hopcroft_Karp_Loop_dom initial_state"
  by (auto intro!: invar_props_intros Hopcroft_Karp_Loop_terminates
            simp: initial_state_def matching(2))

lemma Hopcroft_Karp_Loop_impl_to_Hopcroft_Karp_Loop:
  "Hopcroft_Karp_Loop_impl initial_state = Hopcroft_Karp_Loop initial_state"
  by (auto intro!: Hopcroft_Karp_Loop_impl_same initial_state_props)

subsection \<open>Final correctness\<close>

lemma Hopcroft_Karp_Loop_correct_1:
  "max_card_matching ugraph_abs (matching_abstract (current_matching (Hopcroft_Karp_Loop initial_state)))"
  apply(intro Hopcroft_Karp_Loop_correct_ret_1[where state = "Hopcroft_Karp_Loop initial_state"])
  by(auto intro: invar_holds_intros ret_holds_intros)

lemma Hopcroft_Karp_Loop_correct_2:
  "matching_invar (current_matching (Hopcroft_Karp_Loop initial_state))"
  using invar_matching_holds[OF initial_state_props(2,1)]
  by (auto elim!: invar_props_elims)

end

end
