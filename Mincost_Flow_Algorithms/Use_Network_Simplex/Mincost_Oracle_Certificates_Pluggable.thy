section \<open>A pluggable checker for the oracle/cleanup pipeline\<close>

text \<open>\<open>decide\<close> of \<open>mcf_oracle_cleanup\<close> calls one concrete checker, \<open>screen\<close> composed with
      \<open>verdict_of\<close>. Here that call becomes a locale parameter, assumed only to be sound. The current
      checker instantiates it and gives the same \<open>decide\<close>.\<close>

theory Mincost_Oracle_Certificates_Pluggable
  imports Mincost_Oracle_Certificates
begin

provenance ai


subsection \<open>The pipeline, generic in the checker\<close>

locale \<^marker>\<open>provenance ai_human\<close> mcf_oracle_pluggable_checker =
  mcf_oracle_cleanup_spec where capacity_list = capacity_list
  for capacity_list :: "('n :: linordered_idom) list" +
  fixes checker :: "'n oracle_answer \<Rightarrow> 'n solver_verdict option"
begin

definition decide' :: "'n oracle_answer \<Rightarrow> 'n solver_verdict" where
  "decide' a = (case checker a of Some b \<Rightarrow> b | None \<Rightarrow> cleanup orc_input (oa_flow a))"

definition solve' :: "'n solver_verdict" where
  "solve' = decide' orc_answer"

end

text \<open>An accepted verdict is true of the instance, the shape of \<open>checked_verdict_sound\<close>.\<close>

locale \<^marker>\<open>provenance ai_human\<close> mcf_oracle_pluggable_checker_proof =
  mcf_oracle + mcf_oracle_pluggable_checker +
  assumes cleanup_correct: "\<And>g. verdict_ok (cleanup orc_input g)"
      and checker_correct: "\<And>a r. checker a = Some r \<Longrightarrow> verdict_ok r"
begin

lemma solve'_correct: "verdict_ok solve'"
  using checker_correct cleanup_correct
  by (auto simp: solve'_def decide'_def split: option.splits)

end

subsection \<open>The current checker instantiates it\<close>

context mcf_oracle
begin

definition current_checker :: "'n oracle_answer \<Rightarrow> 'n solver_verdict option" where
  "current_checker a = map_option verdict_of (screen a)"

lemma current_checker_correct: "current_checker a = Some r \<Longrightarrow> verdict_ok r"
  using verdict_of_sound
  by (auto simp: current_checker_def screen_def split: if_splits)

end

text \<open>With the current checker, the generic pipeline computes \<open>decide\<close>.\<close>

context mcf_oracle_cleanup
begin

sublocale pluggable: mcf_oracle_pluggable_checker_proof
  where capacity_list = capacity_list and cleanup = cleanup and checker = current_checker
  by unfold_locales (auto simp: current_checker_correct cleanup_correct)

lemma decide'_current_checker_eq_decide: "pluggable.decide' a = decide a"
  unfolding pluggable.decide'_def decide_def current_checker_def
  by (cases "screen a") auto

end

end
