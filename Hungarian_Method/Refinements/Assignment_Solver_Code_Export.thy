theory Assignment_Solver_Code_Export
  imports
    Assignment_Solver
    Imperative.Code_Target_Machine_Int
begin

provenance ai


section \<open>Code Export of the Assignment Solver\<close>

text \<open>The program @{const asn_solve_int} of \<open>Assignment_Solver.thy\<close>, with integers and natural
      numbers as machine integers (see \<open>Imperative/Code_Target_Machine_Int.thy\<close>),
      together with the constructors of the oracle's answer, which the driver needs to wrap the
      external oracle.\<close>

export_code asn_solve_int Asn_opt Asn_infeas Asn_unknown checking SML_imp

text \<open>The code is written to \<open>Assignment_Solver_code_exports/Assignment_SML\<close> next to this theory, where the build of
      the solver (\<open>Use_Assignment_Solver/driver/Makefile\<close>) reads it.\<close>

ML \<open>
  write_machine_code \<^context>
    [\<^const_name>\<open>asn_solve_int\<close>, \<^const_name>\<open>Asn_opt\<close>, \<^const_name>\<open>Asn_infeas\<close>,
     \<^const_name>\<open>Asn_unknown\<close>]
    "Assignment_Solver" "SML_imp" "Assignment_SML" "Assignment_Solver.sml"
\<close>

end
