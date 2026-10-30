theory Kruskal_Code_Export
  imports
    Kruskal_Imperative_Min_Inst
    Imperative.Code_Target_Machine_Int
begin

provenance ai_human

section \<open>Code Export of the Imperative Kruskal's Algorithm\<close>

text \<open>The imperative Kruskal's algorithm for minimum-weight spanning forests
  (@{const kruskal_imp_min} of \<open>Kruskal_Imperative_Min_Inst.thy\<close>), together with
  @{const rat_of_int} for constructing the costs. Natural numbers and integers are machine integers
  (see \<open>Imperative/Code_Target_Machine_Int.thy\<close> and the printing of the conversions between
  @{typ nat} and @{typ int} in \<open>Kruskal_Imperative_Inst.thy\<close>).

  The SML and the Scala code are compiled here. There is no Go compiler in Isabelle's environment,
  so the Go code is only generated.\<close>

export_code kruskal_imp_min rat_of_int checking SML_imp Scala_imp

text \<open>The code for each target is written to \<open>Kruskal_code_exports/Kruskal_Imp_Min_<target>\<close>
  next to this theory.\<close>

ML \<open>
  val min_consts = [\<^const_name>\<open>kruskal_imp_min\<close>, \<^const_name>\<open>rat_of_int\<close>];

  write_machine_code \<^context> min_consts "Kruskal_Imp_Min" "SML_imp" "Kruskal_Imp_Min_SML"
    "Kruskal_Imp_Min.sml";
  write_machine_code \<^context> min_consts "Kruskal_Imp_Min" "Scala_imp" "Kruskal_Imp_Min_Scala"
    "Kruskal_Imp_Min.scala";
  write_machine_code \<^context> min_consts "Kruskal_Imp_Min" "Go" "Kruskal_Imp_Min_Go" ""
\<close>

end
