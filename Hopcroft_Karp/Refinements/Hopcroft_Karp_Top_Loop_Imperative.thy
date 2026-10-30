theory Hopcroft_Karp_Top_Loop_Imperative
  imports Hopcroft_Karp.Hopcroft_Karp_Top_Loop Separation_Logic_Imperative_HOL_Partial.Sep_Main
begin

section \<open>Imperative Refinement of the Top Loop\<close>

text \<open>The imperative top loop mirrors @{const Hopcroft_Karp_Loop.Hopcroft_Karp_Loop_impl}. As the
  functional loop, it is parametrised by the phase and by the augmentation along one path; the
  loop and the augmentation along all paths of a phase, i.e.\ the fold of @{term augment} over
  them, are implemented. The paths of a phase are held in an abstract store, from which the
  augmentation along one path removes the first path.\<close>

record 'mi Hopcroft_Karp_Loop_state_imp =
  i_matching :: 'mi
  i_phases :: nat

subsection \<open>The program\<close>

locale Hopcroft_Karp_Loop_Imperative_spec =
  fixes empty_matching_imp :: "'mi Heap"
    and phase_imp :: "'mi \<Rightarrow> 'ips Heap"
    and paths_is_empty_imp :: "'ips \<Rightarrow> bool Heap"
    and augment_first_imp :: "'mi \<Rightarrow> 'ips \<Rightarrow> ('mi \<times> 'ips) Heap"
begin

partial_function (heap) augment_all_imp :: "'mi \<Rightarrow> 'ips \<Rightarrow> 'mi Heap" where
  "augment_all_imp Mi Psi =
     do { e \<leftarrow> paths_is_empty_imp Psi;
          if e then return Mi
          else do { (Mi', Psi') \<leftarrow> augment_first_imp Mi Psi;
                    augment_all_imp Mi' Psi' } }"

partial_function (heap) Hopcroft_Karp_Loop_imp ::
  "'mi Hopcroft_Karp_Loop_state_imp \<Rightarrow> 'mi Hopcroft_Karp_Loop_state_imp Heap" where
  "Hopcroft_Karp_Loop_imp s =
     do { Psi \<leftarrow> phase_imp (i_matching s);
          e \<leftarrow> paths_is_empty_imp Psi;
          if e then return s
          else do { Mi' \<leftarrow> augment_all_imp (i_matching s) Psi;
                    Hopcroft_Karp_Loop_imp (s\<lparr>i_matching := Mi', i_phases := Suc (i_phases s)\<rparr>) } }"

definition "initial_state_imp Mi = \<lparr>i_matching = Mi, i_phases = 0\<rparr>"

definition "Hopcroft_Karp_Loop_run_imp =
  do { Mi \<leftarrow> empty_matching_imp;
       Hopcroft_Karp_Loop_imp (initial_state_imp Mi) }"

end

subsection \<open>Correctness\<close>

text \<open>The phase is specified for the input, described by @{term input_assn}, as the functional
  phase; the augmentation along the first path as the functional augmentation.\<close>

locale Hopcroft_Karp_Loop_Imperative =
  Hopcroft_Karp_Loop_thms where lookup = lookup and empty_matching = empty_matching +
  Hopcroft_Karp_Loop_Imperative_spec where phase_imp = phase_imp
    and augment_first_imp = augment_first_imp
  for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option"
  and empty_matching :: 'matching
  and phase_imp :: "'mi \<Rightarrow> 'ips Heap"
  and augment_first_imp :: "'mi \<Rightarrow> 'ips \<Rightarrow> ('mi \<times> 'ips) Heap" +
  fixes matching_assn :: "'matching \<Rightarrow> 'mi \<Rightarrow> assn"
    and paths_assn :: "'v list list \<Rightarrow> 'ips \<Rightarrow> assn"
    and input_assn :: assn
  assumes empty_matching_imp_rule: "<emp> empty_matching_imp <matching_assn empty_matching>"
    and phase_imp_rule:
      "\<And>M Mi. matching_invar M \<Longrightarrow>
       <input_assn * matching_assn M Mi> phase_imp Mi
       <\<lambda>Psi. input_assn * matching_assn M Mi * paths_assn (phase M) Psi>"
    and paths_is_empty_rule:
      "\<And>ps Psi. <paths_assn ps Psi> paths_is_empty_imp Psi <\<lambda>r. paths_assn ps Psi * \<up>(r \<longleftrightarrow> ps = [])>"
    and augment_first_rule:
      "\<And>M Mi p ps Psi. \<lbrakk>matching_invar M; graph_augmenting_path ugraph_abs (matching_abstract M) p\<rbrakk> \<Longrightarrow>
       <matching_assn M Mi * paths_assn (p # ps) Psi> augment_first_imp Mi Psi
       <\<lambda>(Mi', Psi'). matching_assn (augment M p) Mi' * paths_assn ps Psi'>"
begin

subsubsection \<open>The augmentation along all paths of a phase\<close>

lemma augment_all_imp_rule:
  assumes "matching_invar M" "\<forall>p \<in> set ps. graph_augmenting_path ugraph_abs (matching_abstract M) p"
          "sorted_wrt (\<lambda>p q. set p \<inter> set q = {}) ps"
  shows "<matching_assn M Mi * paths_assn ps Psi> augment_all_imp Mi Psi
         <\<lambda>Mi'. matching_assn (foldl augment M ps) Mi'>"
  using assms
proof(induction ps arbitrary: M Mi Psi)
  case Nil
  thus ?case
    by (subst augment_all_imp.simps) (sep_auto heap: paths_is_empty_rule)
next
  case (Cons p ps)
  have gm: "graph_matching ugraph_abs (matching_abstract M)"
    using Cons.prems(1)
    by (rule matching(1))
  hence mf: "matching (matching_abstract M)" "finite (matching_abstract M)"
    by (auto intro: graph_matching_finite)
  have p: "graph_augmenting_path ugraph_abs (matching_abstract M) p"
    using Cons.prems(2)
    by simp
  have aug: "\<forall>q \<in> set ps. graph_augmenting_path ugraph_abs (matching_abstract (augment M p)) q"
    using Cons.prems mf p augmenting_path_disjoint_preserved[of "matching_abstract M" ugraph_abs p]
    by (auto simp: augment(2))
  have inv: "matching_invar (augment M p)"
    using Cons.prems(1) p
    by (rule augment(1))
  have sorted: "sorted_wrt (\<lambda>p q. set p \<inter> set q = {}) ps"
    using Cons.prems(3)
    by simp
  note IH = Cons.IH[OF inv aug sorted]
  show ?case
    using Cons.prems(1) p
    by (subst augment_all_imp.simps) (sep_auto heap: paths_is_empty_rule augment_first_rule IH)
qed

subsubsection \<open>The loop\<close>

definition "state_assn s si =
  matching_assn (current_matching s) (i_matching si) * \<up>(phases s = i_phases si)"

lemma Hopcroft_Karp_Loop_imp_refine:
  assumes "Hopcroft_Karp_Loop_dom s" "invar_matching s"
  shows "<input_assn * state_assn s si> Hopcroft_Karp_Loop_imp si
         <\<lambda>si'. input_assn * state_assn (Hopcroft_Karp_Loop s) si'>"
  using assms(2)
proof(induction arbitrary: si rule: Hopcroft_Karp_Loop_induct[OF assms(1)])
  case IH: (1 s)
  have M: "matching_invar (current_matching s)"
    using IH(3)
    by (auto elim: invar_props_elims)
  show ?case
  proof(cases "phase (current_matching s) = []")
    case True
    hence ret: "Hopcroft_Karp_Loop s = s"
      by (intro Hopcroft_Karp_Loop_simps(2)[OF IH(1)])
         (simp add: Hopcroft_Karp_Loop_ret_1_conds_def)
    show ?thesis
      using M True
      unfolding ret state_assn_def
      by (subst Hopcroft_Karp_Loop_imp.simps) (sep_auto heap: phase_imp_rule paths_is_empty_rule)
  next
    case False
    hence call: "Hopcroft_Karp_Loop_call_1_conds s"
      by (simp add: Hopcroft_Karp_Loop_call_1_conds_def)
    have rec: "Hopcroft_Karp_Loop s = Hopcroft_Karp_Loop (Hopcroft_Karp_Loop_upd1 s)"
      using call
      by (simp add: Hopcroft_Karp_Loop_simps[OF IH(1)])
    note IH' = IH(2)[OF call invar_matching_holds_upd1[OF call IH(3)]]
    have aug: "\<forall>p \<in> set (phase (current_matching s)).
                 graph_augmenting_path ugraph_abs (matching_abstract (current_matching s)) p"
              "sorted_wrt (\<lambda>p q. set p \<inter> set q = {}) (phase (current_matching s))"
      using M
      by auto
    have IH'': "<input_assn * matching_assn (foldl augment (current_matching s) (phase (current_matching s))) Mi'>
                  Hopcroft_Karp_Loop_imp (si\<lparr>i_matching := Mi', i_phases := Suc (i_phases si)\<rparr>)
                <\<lambda>si'. input_assn * state_assn (Hopcroft_Karp_Loop s) si'>"
      if "phases s = i_phases si" for Mi'
      using IH'[of "si\<lparr>i_matching := Mi', i_phases := Suc (i_phases si)\<rparr>"] that
      unfolding rec
      by (simp add: state_assn_def Hopcroft_Karp_Loop_upd1_def Let_def)
    show ?thesis
      using M False
      by (subst Hopcroft_Karp_Loop_imp.simps)
         (sep_auto heap: phase_imp_rule paths_is_empty_rule augment_all_imp_rule[OF M aug] IH''
                   simp: state_assn_def[of s])
  qed
qed

subsubsection \<open>Final correctness\<close>

theorem Hopcroft_Karp_Loop_run_imp_rule:
  "<input_assn> Hopcroft_Karp_Loop_run_imp
   <\<lambda>si. input_assn * matching_assn (current_matching (Hopcroft_Karp_Loop initial_state)) (i_matching si) *
         \<up>(i_phases si = phases (Hopcroft_Karp_Loop initial_state))>"
proof-
  have init: "current_matching initial_state = empty_matching" "phases initial_state = 0"
    by (simp_all add: initial_state_def)
  have R: "<input_assn * matching_assn empty_matching Mi> Hopcroft_Karp_Loop_imp (initial_state_imp Mi)
           <\<lambda>si. input_assn * state_assn (Hopcroft_Karp_Loop initial_state) si>" for Mi
    using Hopcroft_Karp_Loop_imp_refine[OF initial_state_props(2,1), of "initial_state_imp Mi"]
    by (simp add: state_assn_def[of initial_state] init initial_state_imp_def)
  show ?thesis
    unfolding Hopcroft_Karp_Loop_run_imp_def
    by (sep_auto heap: empty_matching_imp_rule R simp: state_assn_def)
qed

text \<open>The imperative loop computes a maximum cardinality matching.\<close>

theorem Hopcroft_Karp_Loop_run_imp_correct:
  "<input_assn> Hopcroft_Karp_Loop_run_imp
   <\<lambda>si. \<exists>\<^sub>AM. input_assn * matching_assn M (i_matching si) *
              \<up>(matching_invar M \<and> max_card_matching ugraph_abs (matching_abstract M))>"
  using Hopcroft_Karp_Loop_correct_1 Hopcroft_Karp_Loop_correct_2
  by (sep_auto heap: Hopcroft_Karp_Loop_run_imp_rule)

end

end
