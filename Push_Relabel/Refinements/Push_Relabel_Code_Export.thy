theory Push_Relabel_Code_Export
  imports
    Push_Relabel_Instantiation
    Imperative.Code_Target_Machine_Int
begin

section \<open>Code Export of the Push-Relabel Programs\<close>

text \<open>The three programs on integer capacities of \<open>Push_Relabel_Instantiation.thy\<close>: FIFO,
  relabel-to-front and highest label. As for matroid intersection, numbers are machine integers
  (see \<open>Code_Target_Machine_Int.thy\<close>), so a driver passes the input arrays directly and the code
  contains no arbitrary precision arithmetic.

  The SML and the Scala code are compiled here. There is no Go compiler in Isabelle's environment,
  so the Go code is only generated.\<close>

export_code push_relabel_fifo_run_int push_relabel_rtf_run_int push_relabel_hl_run_int
  checking SML_imp Scala_imp

text \<open>The code for each target is written to \<open>generated/<target>\<close> next to this theory.\<close>

ML \<open>
  fun write_push_relabel_code target dir_name file_name =
    write_machine_code \<^context>
      [\<^const_name>\<open>push_relabel_fifo_run_int\<close>, \<^const_name>\<open>push_relabel_rtf_run_int\<close>,
       \<^const_name>\<open>push_relabel_hl_run_int\<close>]
      "Push_Relabel" target dir_name file_name;

  write_push_relabel_code "SML_imp" "SML" "Push_Relabel.sml";
  write_push_relabel_code "Scala_imp" "Scala" "Push_Relabel.scala";
  write_push_relabel_code "Go" "Go" ""
\<close>

subsection \<open>A Small Test\<close>

text \<open>A network on the vertices \<open>0\<close> to \<open>3\<close> with source \<open>0\<close> and sink
  \<open>3\<close>. Its maximum flow has value \<open>5\<close>: the edges leaving the source are saturated,
  and so are the edges entering the sink. The program returns the flow by edge number.\<close>

definition pr_test :: "(nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> int array \<Rightarrow> int array Heap) \<Rightarrow>
  int list Heap" where
  "pr_test prog = do {
     Fa \<leftarrow> Array.of_list [0, 0, 1, 1, 2];
     Ta \<leftarrow> Array.of_list [1, 2, 2, 3, 3];
     Ca \<leftarrow> Array.of_list [3, 2, 1, 2, 3];
     Bw \<leftarrow> prog 4 0 3 Fa Ta Ca;
     Array.freeze Bw }"

definition "pr_test_fifo = pr_test push_relabel_fifo_run_int"
definition "pr_test_rtf = pr_test push_relabel_rtf_run_int"
definition "pr_test_hl = pr_test push_relabel_hl_run_int"

ML_val \<open>
  val results = [@{code pr_test_fifo} (), @{code pr_test_rtf} (), @{code pr_test_hl} ()];
  fun value flow = List.nth (flow, 3) + List.nth (flow, 4);
  val _ = map (fn flow => if value flow = 5 then () else error "wrong flow value") results;
  writeln (String.concatWith "\n" (map (String.concatWith " " o map Int.toString) results))
\<close>

end
