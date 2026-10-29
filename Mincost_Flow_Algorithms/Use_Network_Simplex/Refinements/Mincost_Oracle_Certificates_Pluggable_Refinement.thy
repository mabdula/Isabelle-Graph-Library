theory Mincost_Oracle_Certificates_Pluggable_Refinement
  imports Mincost_Oracle_Certificates_Refinement 
          Use_Network_Simplex.Mincost_Oracle_Certificates_Pluggable
begin

section \<open>Imperative refinement of the pluggable checker\<close>

text \<open>The imperative counterpart of \<open>Mincost_Oracle_Certificates_Pluggable\<close>: \<open>decide_imp\<close> calls
      \<open>check_answer_imp\<close> and \<open>flag_of\<close> at one call site, and that call becomes a parameter
      \<open>checker_imp\<close>. The imperative pipeline is proved independently of \<open>decide\<close>, so it needs its own
      locale and its own proof that the current checker fits.\<close>

subsection \<open>The pipeline, generic in the checker\<close>

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

text \<open>The checker's triple: an accepted verdict (\<open>Some r\<close>) is true of the instance; a deferral
      (\<open>None\<close>) says nothing. The oracle and cleanup triples are those of \<open>mcf_oracle_heap\<close>.\<close>

locale mcf_oracle_heap_pluggable_checker =
  mcf_oracle_heap_pipeline where capacity_list = capacity_list and h = h +
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

subsection \<open>The pipeline is correct\<close>

text \<open>As \<open>decide_imp_correct\<close>, with the option split of \<open>checker_imp_rule\<close> in place of the Boolean
      split of \<open>check_answer_imp_rule\<close>.\<close>

lemma decide_imp'_correct:
  assumes "answer_wf a" "0 < M"
  shows "<inst_assn fa sa ca oa ba * answer_assn fla a ai>
           decide_imp' cm M fa sa ca oa ba fla ai
         <\<lambda>r. \<exists>\<^sub>A fl'. inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl'
              * \<up>(length fl' = m \<and> verdict_ok_dispatch cm M (verdict_of_flag r fl'))>"
  unfolding decide_imp'_def
  apply (sep_auto heap: checker_imp_rule[OF assms])
   apply (sep_auto simp: answer_assn_def inst_assn_def assms[unfolded answer_wf_def]
                   heap: rectify_imp_rule cleanup_imp_rule[unfolded inst_assn_def])
     apply (sep_auto simp: rectify_facts assms[unfolded answer_wf_def] verdict_ok_imp_dispatch)+
  apply (sep_auto simp: answer_assn_def assms[unfolded answer_wf_def])
  done

lemma solve_imp'_correct:
  "\<lbrakk>length fl = m; answer_wf orc_answer; 0 < M\<rbrakk> \<Longrightarrow>
   <inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl>
     solve_imp' cm M fa sa ca oa ba fla
   <\<lambda>r. \<exists>\<^sub>A fl'. inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl'
              * \<up>(length fl' = m \<and> verdict_ok_dispatch cm M (verdict_of_flag r fl'))>"
  unfolding solve_imp'_def
  by (sep_auto heap: oracle_imp_rule decide_imp'_correct)

end

subsection \<open>The current checker instantiates it\<close>

text \<open>\<open>check_answer_imp\<close> composed with \<open>flag_of\<close>. It is defined in the assumption-free code locale,
      so that its code equation is unconditional.\<close>

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

context mcf_oracle_heap_pipeline
begin

lemma current_checker_imp_rule:
  "\<lbrakk>answer_wf a; 0 < M\<rbrakk> \<Longrightarrow>
   <inst_assn fa sa ca oa ba * answer_assn fla a ai>
     current_checker_imp cm M fa sa ca oa ba fla ai
   <\<lambda>r. inst_assn fa sa ca oa ba * answer_assn fla a ai
        * \<up>(case r of Some r' \<Rightarrow> verdict_ok_dispatch cm M (verdict_of_flag r' (oa_flow a))
                    | None \<Rightarrow> True)>"
  using verdict_of_flag_of[of fla a ai]
  unfolding current_checker_imp_def
  by (sep_auto simp: verdict_of_dispatch_sound heap: check_answer_imp_rule)

end

text \<open>Plugging the current checker into the generic pipeline satisfies the triple that
      \<open>mcf_oracle_heap.solve_imp_correct\<close> proves.\<close>

context mcf_oracle_heap
begin

sublocale pluggable: mcf_oracle_heap_pluggable_checker
  where capacity_list = capacity_list and h = h and oracle_imp = oracle_imp
    and cleanup_imp = cleanup_imp and checker_imp = current_checker_imp
  by unfold_locales (fact oracle_imp_rule cleanup_imp_rule current_checker_imp_rule)+

end

end
