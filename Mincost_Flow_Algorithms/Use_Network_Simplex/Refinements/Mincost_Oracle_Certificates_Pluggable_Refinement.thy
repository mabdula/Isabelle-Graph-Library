theory Mincost_Oracle_Certificates_Pluggable_Refinement
  imports Mincost_Oracle_Certificates_Refinement 
          Use_Network_Simplex.Mincost_Oracle_Certificates_Pluggable
begin

section \<open>Imperative refinement of the pluggable checker\<close>

text \<open>\<open>Mincost_Oracle_Certificates_Pluggable\<close> abstracts the one call site of
      \<open>mcf_oracle_cleanup_spec.decide\<close> that decides an accepted certificate, turning the fixed
      \<open>screen\<close>/\<open>verdict_of\<close> pair into a locale parameter \<open>checker\<close>.  This theory does the same thing
      one layer down, to the imperative pipeline of \<open>Mincost_Oracle_Certificates_Refinement\<close>: \<open>decide_imp\<close>
      hard-wires \<open>check_answer_imp\<close> and \<open>flag_of\<close> exactly the way \<open>decide\<close> hard-wires \<open>screen\<close> and
      \<open>verdict_of\<close>, and that is the one call site abstracted here.

      The two pipelines are otherwise proved completely independently --- the imperative one never
      goes through \<open>decide\<close>/\<open>solve\<close> at all, so making it pluggable needs its own locale, its own
      assumed checker triple, and its own proof that today's checker discharges it.\<close>

subsection \<open>The pipeline, generic in the checker\<close>

text \<open>Same shape as \<open>mcf_oracle_heap_pipeline_spec\<close>, with one more parameter: \<open>checker_imp\<close> replaces
      the fixed \<open>check_answer_imp\<close>/\<open>flag_of\<close> pair.  A checker call and a cleanup call are the same
      shape a level up --- an instance in, a verdict (optionally) out --- so this is the only change
      \<open>decide_imp\<close>'s definition needs.  Everything else --- \<open>oracle_imp\<close>, \<open>cleanup_imp\<close>,
      \<open>rectify_imp\<close> --- is inherited unchanged from \<open>mcf_oracle_heap_pipeline_spec\<close>.\<close>

locale mcf_oracle_heap_pluggable_checker_spec =
  mcf_oracle_heap_pipeline_spec where capacity_list = capacity_list
  for capacity_list :: "('n :: {heap, linordered_idom}) list" +
  fixes checker_imp ::
      "checker_mode \<Rightarrow> nat \<Rightarrow>
       nat array \<Rightarrow> nat array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n answer_imp
       \<Rightarrow> verdict_flag option Heap"
begin

definition decide_imp' ::
  "checker_mode \<Rightarrow> nat \<Rightarrow>
   nat array \<Rightarrow> nat array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n answer_imp
   \<Rightarrow> verdict_flag Heap" where
  "decide_imp' cm M fa sa ca oa ba fla ai =
     do {
       co \<leftarrow> checker_imp cm M fa sa ca oa ba fla ai;
       case co of Some r \<Rightarrow> return r
                | None \<Rightarrow> do { _ \<leftarrow> rectify_imp ca fla 0 m; cleanup_imp fa sa ca oa ba fla } }"

definition solve_imp' ::
  "checker_mode \<Rightarrow> nat \<Rightarrow>
   nat array \<Rightarrow> nat array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> verdict_flag Heap" where
  "solve_imp' cm M fa sa ca oa ba fla =
     do { ai \<leftarrow> oracle_imp fa sa ca oa ba fla; decide_imp' cm M fa sa ca oa ba fla ai }"

end

text \<open>The proof layer adds one thing: the checker's triple.  An accepted verdict (\<open>Some r\<close>) has to
      be true of the instance; a deferral (\<open>None\<close>) says nothing, exactly as \<open>checker_correct\<close> says
      nothing about the functional \<open>checker\<close> on \<open>None\<close>.  \<open>oracle_imp_rule\<close> and \<open>cleanup_imp_rule\<close> are
      carried over unchanged from \<open>mcf_oracle_heap\<close>.\<close>

locale mcf_oracle_heap_pluggable_checker =
  mcf_oracle_heap_checks where capacity_list = capacity_list and h = h +
  mcf_oracle_heap_pluggable_checker_spec where capacity_list = capacity_list
  for capacity_list :: "('n :: {heap, linordered_idom}) list" and h +
  assumes oracle_imp_rule:
      "length fl = m \<Longrightarrow>
       <inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl>
         oracle_imp fa sa ca oa ba fla
       <\<lambda>ai. inst_assn fa sa ca oa ba * answer_assn fla orc_answer ai>"
    and cleanup_imp_rule:
      "\<lbrakk>length fl = m;
        \<And>e. e < m \<Longrightarrow> 0 \<le> fl ! e;
        \<And>e. \<lbrakk>e < m; capacity_list ! e \<noteq> - 1\<rbrakk> \<Longrightarrow> fl ! e \<le> capacity_list ! e\<rbrakk> \<Longrightarrow>
       <inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl>
         cleanup_imp fa sa ca oa ba fla
       <\<lambda>r. \<exists>\<^sub>A fl'. inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl'
                    * \<up>(length fl' = m \<and> verdict_ok (verdict_of_flag r fl'))>"
    and checker_imp_rule:
      "answer_wf a \<Longrightarrow> 0 < M \<Longrightarrow>
       <inst_assn fa sa ca oa ba * answer_assn fla a ai>
         checker_imp cm M fa sa ca oa ba fla ai
       <\<lambda>r. inst_assn fa sa ca oa ba * answer_assn fla a ai
            * \<up>(case r of Some r' \<Rightarrow> verdict_ok_dispatch cm M (verdict_of_flag r' (oa_flow a))
                        | None \<Rightarrow> True)>"
begin

text \<open>The rectification pass is proved exactly as in \<open>mcf_oracle_heap\<close>: it is not part of the
      specification, only of this proof, so it has no counterpart to inherit and is re-derived here
      from \<open>mcf_oracle_heap_checks\<close>'s \<open>capacity_format\<close> alone --- no dependence on either assumed
      triple above.\<close>

definition clamp1 :: "'n \<Rightarrow> 'n \<Rightarrow> 'n" where
  "clamp1 c f = (if f < 0 then 0 else if c \<noteq> - 1 \<and> c < f then c else f)"

fun rectify :: "'n list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'n list" where
  "rectify fl e 0 = fl"
| "rectify fl e (Suc k) = rectify (fl[e := clamp1 (capacity_list ! e) (fl ! e)]) (Suc e) k"

definition cap_ok :: "'n list \<Rightarrow> nat \<Rightarrow> bool" where
  "cap_ok fl i = (0 \<le> fl ! i \<and> (capacity_list ! i \<noteq> - 1 \<longrightarrow> fl ! i \<le> capacity_list ! i))"

lemma rectify_imp_rule:
  "\<lbrakk>e + k \<le> length fl; length capacity_list = m; e + k \<le> m\<rbrakk> \<Longrightarrow>
   <ca \<mapsto>\<^sub>a capacity_list * fla \<mapsto>\<^sub>a fl> rectify_imp ca fla e k
   <\<lambda>_. ca \<mapsto>\<^sub>a capacity_list * fla \<mapsto>\<^sub>a rectify fl e k>"
proof(induction k arbitrary: e fl)
  case 0
  thus ?case by(subst rectify_imp.simps) sep_auto
next
  case (Suc k)
  have ef: "e < length fl" and ec: "e < length capacity_list" using Suc.prems by simp_all
  have IH: "<ca \<mapsto>\<^sub>a capacity_list * fla \<mapsto>\<^sub>a (fl[e := clamp1 (capacity_list ! e) (fl ! e)])>
              rectify_imp ca fla (Suc e) k
            <\<lambda>_. ca \<mapsto>\<^sub>a capacity_list
                 * fla \<mapsto>\<^sub>a rectify (fl[e := clamp1 (capacity_list ! e) (fl ! e)]) (Suc e) k>"
    using Suc.IH[of "Suc e" "fl[e := clamp1 (capacity_list ! e) (fl ! e)]"] Suc.prems by simp
  show ?case
    by(subst rectify_imp.simps) (sep_auto simp: ef ec clamp1_def[symmetric] heap: IH)
qed

lemma rectify_length: "length (rectify fl e k) = length fl"
  by(induction k arbitrary: e fl) simp_all

lemma rectify_outside: "i < e \<or> e + k \<le> i \<Longrightarrow> rectify fl e k ! i = fl ! i"
  by(induction k arbitrary: e fl) (auto simp add: nth_list_update)

lemma cap_ok_clamp1:
  assumes "e < m" "e < length fl"
  shows "cap_ok (fl[e := clamp1 (capacity_list ! e) (fl ! e)]) e"
  using assms capacity_format[OF assms(1)] by(auto simp add: cap_ok_def clamp1_def)

lemma rectify_inside:
  "\<lbrakk>e + k \<le> m; e + k \<le> length fl; e \<le> i; i < e + k\<rbrakk> \<Longrightarrow> cap_ok (rectify fl e k) i"
proof(induction k arbitrary: e fl)
  case 0
  thus ?case by simp
next
  case (Suc k)
  show ?case
  proof(cases "i = e")
    case True
    have "rectify (fl[e := clamp1 (capacity_list ! e) (fl ! e)]) (Suc e) k ! e
            = fl[e := clamp1 (capacity_list ! e) (fl ! e)] ! e"
      by(rule rectify_outside) simp
    thus ?thesis
      using cap_ok_clamp1[of e fl] Suc.prems True by(simp add: cap_ok_def)
  next
    case False
    hence "Suc e \<le> i" using Suc.prems by simp
    thus ?thesis
      using Suc.IH[of "Suc e" "fl[e := clamp1 (capacity_list ! e) (fl ! e)]"] Suc.prems by simp
  qed
qed

lemma rectify_facts:
  assumes fl: "length fl = m"
  shows "length (rectify fl 0 m) = m"
    and "e < m \<Longrightarrow> 0 \<le> rectify fl 0 m ! e"
    and "\<lbrakk>e < m; capacity_list ! e \<noteq> - 1\<rbrakk> \<Longrightarrow> rectify fl 0 m ! e \<le> capacity_list ! e"
  using rectify_length[of fl 0 m] fl rectify_inside[of 0 m fl e]
  by(auto simp add: cap_ok_def)

subsection \<open>The pipeline is correct\<close>

text \<open>Deciding is correct.  If the checker accepts, its own triple makes the verdict true; if it
      defers, the flow is rectified into the capacities --- exactly what \<open>cleanup_imp_rule\<close> demands
      --- and the verdict is the cleanup's.  Structurally identical to \<open>decide_imp_correct\<close>, with the
      Boolean case split of \<open>check_answer_imp_rule\<close> replaced by the option case split of
      \<open>checker_imp_rule\<close>.\<close>

lemma decide_imp'_correct:
  assumes wf: "answer_wf a" and Mpos: "0 < M"
  shows "<inst_assn fa sa ca oa ba * answer_assn fla a ai>
           decide_imp' cm M fa sa ca oa ba fla ai
         <\<lambda>r. \<exists>\<^sub>A fl'. inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl'
              * \<up>(length fl' = m \<and> verdict_ok_dispatch cm M (verdict_of_flag r fl'))>"
proof -
  have flm: "length (oa_flow a) = m" using wf by(simp add: answer_wf_def)
  have rect: "<ca \<mapsto>\<^sub>a capacity_list * fla \<mapsto>\<^sub>a oa_flow a>
                rectify_imp ca fla 0 m
              <\<lambda>_. ca \<mapsto>\<^sub>a capacity_list * fla \<mapsto>\<^sub>a rectify (oa_flow a) 0 m>"
    by(rule rectify_imp_rule) (simp_all add: flm length_capacity)
  have clean: "<inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a rectify (oa_flow a) 0 m>
                 cleanup_imp fa sa ca oa ba fla
               <\<lambda>r. \<exists>\<^sub>A fl'. inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl'
                    * \<up>(length fl' = m \<and> verdict_ok (verdict_of_flag r fl'))>"
    by(rule cleanup_imp_rule) (auto simp add: rectify_facts[OF flm])
  have clean_dispatch: "<inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a rectify (oa_flow a) 0 m>
                 cleanup_imp fa sa ca oa ba fla
               <\<lambda>r. \<exists>\<^sub>A fl'. inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl'
                    * \<up>(length fl' = m \<and> verdict_ok_dispatch cm M (verdict_of_flag r fl'))>"
    using Mpos by(sep_auto heap: clean simp: verdict_ok_imp_dispatch)
  show ?thesis
    unfolding decide_imp'_def
    apply(sep_auto heap: checker_imp_rule[OF wf Mpos])
     apply(sep_auto simp: answer_assn_def inst_assn_def
                    heap: rect[unfolded inst_assn_def] clean_dispatch[unfolded inst_assn_def])
    apply(sep_auto simp: flm)
    done
qed

text \<open>And the pipeline: call the untrusted oracle, ask the checker, and if it defers fall back on
      the verified cleanup.  Same statement as \<open>mcf_oracle_heap.solve_imp_correct\<close> --- generic in
      \<open>checker_imp\<close> rather than fixed to \<open>check_answer_imp\<close>.\<close>

theorem solve_imp'_correct:
  assumes fl: "length fl = m" and wf: "answer_wf orc_answer" and Mpos: "0 < M"
  shows "<inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl>
           solve_imp' cm M fa sa ca oa ba fla
         <\<lambda>r. \<exists>\<^sub>A fl'. inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl'
              * \<up>(length fl' = m \<and> verdict_ok_dispatch cm M (verdict_of_flag r fl'))>"
  unfolding solve_imp'_def
  by(sep_auto heap: oracle_imp_rule[OF fl] decide_imp'_correct[OF wf Mpos])

end

subsection \<open>The current checker instantiates it for free\<close>

text \<open>\<open>check_answer_imp\<close> composed with \<open>flag_of\<close> is already exactly a function of \<open>checker_imp\<close>'s
      type.  The definition is given in \<open>mcf_oracle_heap_pipeline_spec\<close> itself --- assumption-free,
      like \<open>check_answer_imp\<close> and \<open>flag_of\<close> it is built from --- rather than in the proof locale
      below: a definition inside a locale that carries \<open>mcf_oracle\<close>'s real assumptions would export
      as a conditional code equation, and code generation cannot discharge that condition.\<close>

context mcf_oracle_heap_pipeline_spec
begin

definition current_checker_imp ::
  "checker_mode \<Rightarrow> nat \<Rightarrow>
   nat array \<Rightarrow> nat array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n answer_imp
   \<Rightarrow> verdict_flag option Heap" where
  "current_checker_imp cm M fa sa ca oa ba fla ai =
     do {
       ok \<leftarrow> check_answer_imp cm M fa sa ca oa ba fla ai;
       return (if ok then Some (flag_of ai) else None) }"

end

text \<open>Its correctness needs only \<open>mcf_oracle_heap_checks\<close> --- the four check refinements --- and
      none of \<open>mcf_oracle_heap\<close>'s two assumed triples, so it is proved in a locale that combines the
      checks with the pipeline's definitions and assumes nothing further.  (\<open>check_answer_imp_rule\<close>
      is reproved here rather than inherited: in \<open>Mincost_Oracle_Certificates_Refinement\<close> it lives in
      \<open>mcf_oracle_heap\<close> itself, bundled with the two assumed triples it does not actually need.)\<close>

locale mcf_oracle_heap_current_checker =
  mcf_oracle_heap_checks where capacity_list = capacity_list and h = h +
  mcf_oracle_heap_pipeline_spec where capacity_list = capacity_list
  for capacity_list :: "('n :: {heap, linordered_idom}) list" and h
begin

lemma check_answer_imp_rule:
  assumes wf: "answer_wf a" and Mpos: "0 < M"
  shows "<inst_assn fa sa ca oa ba * answer_assn fla a ai>
     check_answer_imp cm M fa sa ca oa ba fla ai
   <\<lambda>r. inst_assn fa sa ca oa ba * answer_assn fla a ai * \<up>(r = check_answer_dispatch cm a)>"
proof(cases a)
  case (OracleOptimum fl pot certm)
  have len: "length fl = m \<and> length pot = Suc n"
    using wf by(simp add: answer_wf_def OracleOptimum)
  show ?thesis
  proof(cases ai)
    case (OptimumI pota certm')
    show ?thesis
      unfolding OracleOptimum OptimumI check_answer_imp_def answer_assn_def
      by(sep_auto simp: check_answer_dispatch_def heap: check_optimum_dispatch_imp_rule[OF len])
  qed (simp_all add: OracleOptimum answer_assn_def)
next
  case (OracleInfeasible fl S)
  have len: "length S = Suc n"
    using wf by(simp add: answer_wf_def OracleInfeasible)
  show ?thesis
  proof(cases ai)
    case (InfeasibleI sca)
    show ?thesis
      unfolding OracleInfeasible InfeasibleI check_answer_imp_def answer_assn_def
      by(sep_auto simp: check_answer_dispatch_def heap: check_infeasible_imp_rule[OF len])
  qed (simp_all add: OracleInfeasible answer_assn_def)
next
  case (OracleUnbounded fl cyc)
  have rule: "<inst_assn fa sa ca oa ba * cyca \<mapsto>\<^sub>a (cyc @ rst)>
                check_unbounded_imp fa sa ca oa cyca (length cyc)
              <\<lambda>r. inst_assn fa sa ca oa ba * cyca \<mapsto>\<^sub>a (cyc @ rst)
                   * \<up>(r = check_unbounded cyc)>" for rst cyca
    using check_unbounded_imp_rule[OF length_fst_list length_snd_list length_capacity
                                      length_cost_list, of "length cyc" "cyc @ rst"]
    by simp
  show ?thesis
  proof(cases ai)
    case (UnboundedI cyca k)
    show ?thesis
      unfolding OracleUnbounded UnboundedI check_answer_imp_def answer_assn_def
      by(sep_auto simp: check_answer_dispatch_def heap: rule)
  qed (simp_all add: OracleUnbounded answer_assn_def)
qed

lemma verdict_of_flag_of:
  "answer_assn fla a ai = false \<or> verdict_of_flag (flag_of ai) (oa_flow a) = verdict_of a"
  by(cases a; cases ai) (auto simp add: answer_assn_def verdict_of_flag_def verdict_of_def)

lemma current_checker_imp_rule:
  assumes wf: "answer_wf a" and Mpos: "0 < M"
  shows "<inst_assn fa sa ca oa ba * answer_assn fla a ai>
           current_checker_imp cm M fa sa ca oa ba fla ai
         <\<lambda>r. inst_assn fa sa ca oa ba * answer_assn fla a ai
              * \<up>(case r of Some r' \<Rightarrow> verdict_ok_dispatch cm M (verdict_of_flag r' (oa_flow a))
                          | None \<Rightarrow> True)>"
proof(cases "answer_assn fla a ai = false")
  case True
  thus ?thesis by(simp add: current_checker_imp_def)
next
  case False
  hence vf: "verdict_of_flag (flag_of ai) (oa_flow a) = verdict_of a"
    using verdict_of_flag_of by blast
  show ?thesis
    unfolding current_checker_imp_def
    by(sep_auto simp: verdict_of_dispatch_sound vf Mpos heap: check_answer_imp_rule[OF wf Mpos])
qed

end

text \<open>And the punchline: plugging the current checker into the new, generic pipeline satisfies
      exactly the triple \<open>mcf_oracle_heap.solve_imp_correct\<close> already proves.  The restructuring
      changes nothing about what is computed today; it only gives the call site a second, as yet
      unused, way to be filled in --- the imperative counterpart of
      \<open>mcf_oracle_cleanup.decide'_current_checker_eq_decide\<close>.\<close>

context mcf_oracle_heap
begin

sublocale current: mcf_oracle_heap_current_checker
  where capacity_list = capacity_list and h = h and oracle_imp = oracle_imp
    and cleanup_imp = cleanup_imp
  by unfold_locales

sublocale pluggable: mcf_oracle_heap_pluggable_checker
  where capacity_list = capacity_list and h = h and oracle_imp = oracle_imp
    and cleanup_imp = cleanup_imp and checker_imp = current_checker_imp
  apply(unfold_locales)
     apply(rule oracle_imp_rule)
     apply assumption
    apply(rule cleanup_imp_rule)
      apply assumption
     apply assumption
    apply assumption
   apply(rule current.current_checker_imp_rule)
   apply assumption
  apply assumption
  done

end

end

