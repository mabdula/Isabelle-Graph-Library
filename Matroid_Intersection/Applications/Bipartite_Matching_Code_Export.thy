theory Bipartite_Matching_Code_Export
  imports
    Weighted_Bipartite_Matching_Imp
    Weighted_Bipartite_B_Matching_Imp
    Imperative.Code_Target_Machine_Int
begin

section \<open>Code Export of the Four Matching Programs\<close>

text \<open>The maximum cardinality and the maximum weight variants, for matchings and for b-matchings.
  The weights are integers, so the two weighted programs are exported in their monomorphic
  copies. Numbers are machine integers (see @{theory Imperative.Code_Target_Machine_Int}),
  so a driver passes the input arrays directly and the code contains no arbitrary precision
  arithmetic.

  The SML and the Scala code are compiled here. There is no Go compiler in Isabelle's environment
  (\<open>ISABELLE_GOEXE\<close>), so the Go code is only generated.

  Two imported libraries attach SML preambles to every program, which none of the four programs
  uses and which compute on \<open>IntInf.int\<close>; they are removed. The Scala printer breaks long
  \<open>extends\<close> clauses after a trailing \<open>with\<close>, which Scala 3 reads as the start of a template
  body; a wide line avoids that.\<close>

code_printing code_module Uint32 \<rightharpoonup> (SML) and (Scala)
| code_module array_blit \<rightharpoonup> (SML)

declare [[default_code_width = 1000]]

export_code matching_imp b_matching_imp weighted_matching_int_imp weighted_b_matching_int_imp
  checking SML_imp Scala_imp

text \<open>The code for each target is written to \<open>Bipartite_Matching_code_exports/<target>\<close> next to this theory.\<close>

ML \<open>
  fun write_matching_code target dir_name file_name =
    write_machine_code \<^context>
      [\<^const_name>\<open>matching_imp\<close>, \<^const_name>\<open>b_matching_imp\<close>,
       \<^const_name>\<open>weighted_matching_int_imp\<close>, \<^const_name>\<open>weighted_b_matching_int_imp\<close>]
      "Bipartite_Matching" target dir_name file_name;

  write_matching_code "SML_imp" "SML" "Bipartite_Matching.sml";
  write_matching_code "Scala_imp" "Scala" "Bipartite_Matching.scala";
  write_matching_code "Go" "Go" ""
\<close>

end
