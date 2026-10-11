theory Hungarian_Code_Export
  imports
    Hungarian_CSR_Variants
    Imperative.Code_Target_Machine_Int
begin

section \<open>Code Export of the Weighted Bipartite Matching Programs\<close>

text \<open>The four variants on arrays of \<open>Hungarian_CSR_Variants.thy\<close>, with
  integer weights: minimum and maximum weight perfect matchings, minimum and maximum weight
  matchings, and minimum and maximum weight matchings among the matchings of maximum cardinality.
  As for matroid intersection, numbers are machine integers (see
  \<open>Code_Target_Machine_Int.thy\<close>), so a driver passes the input arrays
  directly and the code contains no arbitrary precision arithmetic.

  The SML and the Scala code are compiled here. There is no Go compiler in Isabelle's environment,
  so the Go code is only generated.\<close>

export_code hungarian_csr_run_int hungarian_csr_max_perfect_run_int
  hungarian_csr_mw_run_int hungarian_csr_mwmc_run_int
  checking SML_imp Scala_imp

text \<open>The code for each target is written to \<open>generated/<target>\<close> next to this theory.\<close>

ML \<open>
  fun write_hungarian_code target dir_name file_name =
    write_machine_code \<^context>
      [\<^const_name>\<open>hungarian_csr_run_int\<close>, \<^const_name>\<open>hungarian_csr_max_perfect_run_int\<close>,
       \<^const_name>\<open>hungarian_csr_mw_run_int\<close>, \<^const_name>\<open>hungarian_csr_mwmc_run_int\<close>]
      "Hungarian" target dir_name file_name;

  write_hungarian_code "SML_imp" "SML" "Hungarian.sml";
  write_hungarian_code "Scala_imp" "Scala" "Hungarian.scala";
  write_hungarian_code "Go" "Go" ""
\<close>

end
