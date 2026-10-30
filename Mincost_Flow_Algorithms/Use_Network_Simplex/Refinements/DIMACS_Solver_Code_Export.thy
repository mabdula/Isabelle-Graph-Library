theory DIMACS_Solver_Code_Export
  imports DIMACS_Solver
begin

provenance ai


export_code dimacs_solve_prog reduce_imp orig_flow_imp ns_cleanup_imp isqrt
  integer_of_nat integer_of_int OptimumI InfeasibleI UnboundedI
  in SML module_name DIMACS_Solver_Code

text \<open>The same code, written into the \<open>DIMACS_Solver_code_exports\<close> directory -- the one the MLton build
      compiles from -- so that an external driver can compile it: the solver, the reduction and
      the back-transformation, plus the integer constructors a driver needs in order to build the
      six input arrays.

      It used to be written next to this theory and copied into \<open>DIMACS_Solver_code_exports\<close> by hand. The copy is
      what the driver builds, so a forgotten copy step meant building against code that was no
      longer what had been proved -- and nothing about that failure is visible from the outside:
      every test passes, against the wrong program. Writing it where the build reads it does not
      detect that, it makes it impossible. The path is still anchored at this theory's own
      directory, so generation stays unaware of how the surrounding project is organised.\<close>
ML \<open>
  val (files, _) =
    Code_Target.produce_code \<^context> false
      [\<^const_name>\<open>dimacs_solve_prog\<close>, \<^const_name>\<open>reduce_imp\<close>,
       \<^const_name>\<open>orig_flow_imp\<close>, \<^const_name>\<open>ns_cleanup_imp\<close>,
       \<^const_name>\<open>isqrt\<close>, \<^const_name>\<open>nat_of_integer\<close>,
       \<^const_name>\<open>int_of_integer\<close>, \<^const_name>\<open>integer_of_nat\<close>,
       \<^const_name>\<open>integer_of_int\<close>, \<^const_name>\<open>OptimumI\<close>,
       \<^const_name>\<open>InfeasibleI\<close>, \<^const_name>\<open>UnboundedI\<close>]
      "SML" "DIMACS_Solver_Code" NONE [];
  val code = String.concat (map (fn (_, b) => Bytes.content b) files);
  val dir =
    Isabelle_System.make_directory
      (Path.append (Resources.master_directory \<^theory>) (Path.basic "DIMACS_Solver_code_exports"));
  val path = Path.append dir (Path.basic "DIMACS_Solver_Code.sml");
  val () = File.write path code;
  writeln ("wrote " ^ Path.implode path ^ ": " ^ Int.toString (size code) ^ " chars")
\<close>

end
