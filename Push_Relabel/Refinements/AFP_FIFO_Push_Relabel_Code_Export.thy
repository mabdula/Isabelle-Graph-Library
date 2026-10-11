theory AFP_FIFO_Push_Relabel_Code_Export
  imports
    Prpu_Maxflow.Fifo_Push_Relabel_Impl
    Imperative.Code_Target_Machine_Int
begin

section \<open>Code Export of the FIFO Push-Relabel Algorithm of the AFP\<close>

text \<open>For comparison with the programs of \<open>Push_Relabel_Code_Export.thy\<close>, the FIFO
  push-relabel implementation of the AFP entry \<open>Prpu_Maxflow\<close> (Lammich and Sefidgar), with the
  same serialisation of numbers: @{typ nat} and @{typ int} are machine integers (see
  \<open>Code_Target_Machine_Int.thy\<close>).

  The exported program is the AFP's @{const fifo_push_relabel_impl}: given the capacity function
  \<open>c\<close>, source \<open>s\<close>, sink \<open>t\<close>, the number \<open>N\<close> of vertices and an array of adjacency lists of
  length \<open>N\<close>, it returns a residual capacity matrix whose flow is maximum (theorem
  @{thm [source] Network_Impl.fifo_push_relabel_impl_correct}). Also exported are its two phases
  @{const fifo_push_relabel_init_impl} and @{const fifo_push_relabel_run_impl}, and
  @{const compute_flow_val_impl}, which computes the flow value from the residual matrix.

  The AFP's network checker \<open>prepareNet\<close>, which computes the capacity function and the
  adjacency lists from an edge list, is not exported: it uses hash maps on diff arrays with
  \<open>uint32\<close> hash codes, whose serialisation goes through @{typ integer} and does not exist for
  Go. The driver provides the capacity function and the adjacency lists instead.\<close>

text \<open>The code modules of diff arrays and of \<open>uint32\<close> are added to every program but not used by
  the one here. They are removed.\<close>

code_printing
  code_module Uint \<rightharpoonup> (SML) and (Scala)
| code_module Uint32 \<rightharpoonup> (SML) and (Scala)
| code_module STArray \<rightharpoonup> (SML)
| code_module FArray \<rightharpoonup> (SML)
| code_module DiffArray \<rightharpoonup> (Scala)
| code_module array_blit \<rightharpoonup> (SML)
| code_module AStatistics \<rightharpoonup> (SML)

export_code fifo_push_relabel_impl fifo_push_relabel_init_impl fifo_push_relabel_run_impl
  compute_flow_val_impl checking SML_imp Scala_imp

text \<open>The code for each target is written to \<open>generated/<target>\<close> next to this theory.\<close>

ML \<open>
  fun write_afp_fifo_code target dir_name file_name =
    write_machine_code \<^context>
      [\<^const_name>\<open>fifo_push_relabel_impl\<close>, \<^const_name>\<open>fifo_push_relabel_init_impl\<close>,
       \<^const_name>\<open>fifo_push_relabel_run_impl\<close>, \<^const_name>\<open>compute_flow_val_impl\<close>]
      "AFP_FIFO_Push_Relabel" target dir_name file_name;

  write_afp_fifo_code "SML_imp" "SML" "AFP_FIFO_Push_Relabel.sml";
  write_afp_fifo_code "Scala_imp" "Scala" "AFP_FIFO_Push_Relabel.scala";
  write_afp_fifo_code "Go" "Go" ""
\<close>

subsection \<open>A Small Test\<close>

text \<open>The test computes the capacity function and the adjacency lists from an edge list, as
  \<open>prepareNet\<close> would for a valid network, and returns the value of the maximum flow. The first
  network is the one of \<open>Push_Relabel_Code_Export.thy\<close>, with maximum flow value \<open>5\<close>, the second
  the one of the AFP's test, with maximum flow value \<open>42\<close>.\<close>

definition afp_fifo_test :: "(nat \<times> nat \<times> int) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int Heap" where
  "afp_fifo_test el N s t = do {
     let c = (\<lambda>e. case map_of (map (\<lambda>(u, v, w). ((u, v), w)) el) e of None \<Rightarrow> 0 | Some w \<Rightarrow> w);
     let am = (\<lambda>u. remdups ([v. (x, v, w) \<leftarrow> el, x = u] @ [v. (v, x, w) \<leftarrow> el, x = u]));
     ami \<leftarrow> Array.make N am;
     cf \<leftarrow> fifo_push_relabel_impl c s t N ami;
     compute_flow_val_impl s N ami cf }"

definition "afp_fifo_test_1 =
  afp_fifo_test [(0, 1, 3), (0, 2, 2), (1, 2, 1), (1, 3, 2), (2, 3, 3)] 4 0 3"

definition "afp_fifo_test_2 =
  afp_fifo_test [(0, 1, 22), (0, 2, 22), (1, 3, 20), (2, 3, 20), (1, 4, 1), (2, 4, 1), (4, 3, 2)]
    5 0 3"

ML_val \<open>
  val results = [@{code afp_fifo_test_1} (), @{code afp_fifo_test_2} ()];
  val _ = results = [5, 42] orelse error "wrong flow value";
  writeln (String.concatWith " " (map Int.toString results))
\<close>

end

