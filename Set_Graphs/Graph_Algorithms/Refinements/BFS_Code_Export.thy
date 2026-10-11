theory BFS_Code_Export
  imports
    BFS_Instantiation
    Graph_Algorithms_Dev.BFS_Example
    Imperative.Code_Target_Machine_Int
begin

section \<open>Code Export of the Breadth-First Searches\<close>

text \<open>Two breadth-first searches, with vertices as machine integers (see
  \<open>Imperative/Code_Target_Machine_Int.thy\<close>), so the code contains no arbitrary
  precision arithmetic:

    \<^item> the imperative BFS on a CSR of \<open>BFS_Instantiation.thy\<close>: @{const bfs_csr_run} takes the
      number of vertices, the arrays of the tails and of the heads of the edges and the array of
      distinct sources and returns the visited, the distance and the parent array;
      @{const bfs_path} then writes a shortest path to a vertex, reversed, into a given array and
      returns its length;
    \<^item> the functional BFS on red-black trees of \<open>BFS_Example.thy\<close>: \<open>graph_rbt\<close> builds the
      adjacency map from an edge list, @{const build_rbt_sources} the source set from a list,
      @{const BFS_dag_rbt} returns the parent map and @{const BFS_check_reachable_rbt} tests
      whether a vertex is reachable. The parent map is queried with \<open>parent_rbt\<close>.

  The SML and the Scala code are compiled here. There is no Go compiler in Isabelle's environment,
  so the Go code is only generated.

  The imports bring code modules that the programs do not use and that compute on arbitrary
  precision integers: \<open>Uint32\<close> of the AFP entry \<open>Native_Word\<close> and \<open>array_blit\<close> of
  \<open>Array_Blit\<close>. Since a code module is printed into every program, they are removed.\<close>

code_printing code_module Uint32 \<rightharpoonup> (SML)
| code_module Uint32 \<rightharpoonup> (Scala)
| code_module array_blit \<rightharpoonup> (SML)

export_code bfs_csr_run bfs_path checking SML_imp Scala_imp

text \<open>The construction of the graph and the lookup in the parent map are generic in the vertex
  type. A program would take the dictionaries of @{typ nat} as arguments, which the SML signature
  does not export, so the entry points fix the type.\<close>

definition graph_rbt :: "(nat \<times> nat) list \<Rightarrow> ((nat \<times> (nat \<times> color) tree) \<times> color) tree" where
  "graph_rbt es = a_graph es"

definition parent_rbt :: "((nat \<times> nat) \<times> color) tree \<Rightarrow> nat \<Rightarrow> nat option" where
  "parent_rbt P v = lookup P v"

export_code graph_rbt build_rbt_sources BFS_dag_rbt BFS_check_reachable_rbt parent_rbt
  checking SML Scala

text \<open>The code for each target is written to \<open>generated/BFS_CSR_<target>\<close> and
  \<open>generated/BFS_RBT_<target>\<close> next to this theory.\<close>

ML \<open>
  val csr_consts = [\<^const_name>\<open>bfs_csr_run\<close>, \<^const_name>\<open>bfs_path\<close>];
  val rbt_consts =
    [\<^const_name>\<open>graph_rbt\<close>, \<^const_name>\<open>build_rbt_sources\<close>, \<^const_name>\<open>BFS_dag_rbt\<close>,
     \<^const_name>\<open>BFS_check_reachable_rbt\<close>, \<^const_name>\<open>parent_rbt\<close>];

  write_machine_code \<^context> csr_consts "BFS_CSR" "SML_imp" "BFS_CSR_SML" "BFS_CSR.sml";
  write_machine_code \<^context> csr_consts "BFS_CSR" "Scala_imp" "BFS_CSR_Scala" "BFS_CSR.scala";
  write_machine_code \<^context> csr_consts "BFS_CSR" "Go" "BFS_CSR_Go" "";
  write_machine_code \<^context> rbt_consts "BFS_RBT" "SML" "BFS_RBT_SML" "BFS_RBT.sml";
  write_machine_code \<^context> rbt_consts "BFS_RBT" "Scala" "BFS_RBT_Scala" "BFS_RBT.scala";
  write_machine_code \<^context> rbt_consts "BFS_RBT" "Go" "BFS_RBT_Go" ""
\<close>

end
