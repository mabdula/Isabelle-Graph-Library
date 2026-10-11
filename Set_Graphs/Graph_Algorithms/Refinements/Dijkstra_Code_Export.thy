theory Dijkstra_Code_Export
  imports
    Dijkstra_Instantiation
    Imperative.Code_Target_Machine_Int
begin

section \<open>Code Export of the Shortest-Path Programs\<close>

text \<open>The programs on integers of \<open>Dijkstra_Instantiation.thy\<close>: the search for a shortest path
  from the sources to the nearest target, and the search without early stopping together with the
  query for a shortest path to a vertex. Vertices, edge indices and weights are machine integers
  (see \<open>Imperative/Code_Target_Machine_Int.thy\<close>), so a driver passes the input
  arrays directly and the code contains no arbitrary precision arithmetic.

  The SML and the Scala code are compiled here. There is no Go compiler in Isabelle's environment,
  so the Go code is only generated.\<close>

export_code dijkstra_shortest_path_int dijkstra_sp_compute_int dijkstra_sp_query_int
  checking SML_imp Scala_imp

text \<open>The code for each target is written to \<open>generated/Dijkstra_<target>\<close> next to this
  theory.\<close>

ML \<open>
  fun write_dijkstra_code target dir_name file_name =
    write_machine_code \<^context>
      [\<^const_name>\<open>dijkstra_shortest_path_int\<close>, \<^const_name>\<open>dijkstra_sp_compute_int\<close>,
       \<^const_name>\<open>dijkstra_sp_query_int\<close>]
      "Dijkstra" target dir_name file_name;

  write_dijkstra_code "SML_imp" "Dijkstra_SML" "Dijkstra.sml";
  write_dijkstra_code "Scala_imp" "Dijkstra_Scala" "Dijkstra.scala";
  write_dijkstra_code "Go" "Dijkstra_Go" ""
\<close>

end
