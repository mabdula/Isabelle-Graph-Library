theory DFS_Code_Export
  imports
    DFS_Example
    DFS_Imperative
    DFS_by_Iterator_Imperative
    Imperative.Code_Target_Machine_Int
begin

provenance ai


locale rbt_DFS_by_input_list =
  fixes n :: nat and fs ts :: "nat list" and s t :: nat
  assumes ts_length: "length ts = length fs"
    and fs_bound: "i < length fs \<Longrightarrow> fs ! i < n" and ts_bound: "i < length fs \<Longrightarrow> ts ! i < n"
    and edges_distinct: "distinct (zip fs ts)"
    and s_in_G: "s \<in> dVs (set (zip fs ts))"
begin

text \<open>Correctness of the functional DFS on red-black trees, on the graph built from the edge list.\<close>

interpretation dfs_thms: DFS_thms where insert = vset_insert and
 sel = sel and  vset_empty = vset_empty and  diff = vset_diff and
 lookup = lookup and empty = map_empty and delete=delete and isin = isin and t_set=t_set
and update=update and adjmap_inv = adj_inv and vset_delete= vset_delete
and vset_inv = vset_inv and union=vset_union and inter=vset_inter and G = "from_list (zip fs ts)"
and t = t and s = s
  by (intro DFS_thms.intro dfs.DFS_axioms DFS_thms_axioms.intro)
     (simp add: dfs.DFS_axioms_def dfs.Graph.from_list_correct(2,3) s_in_G)

theorem \<^marker>\<open>provenance ai_human\<close> rbt_dfs_correct:
  "let r = rbt_dfs_impl (rbt_from_list (zip fs ts)) t (rbt_dfs_initial_state s) in
   case DFS_state.return r of
     NotReachable \<Rightarrow> \<nexists>p. vwalk_bet (set (zip fs ts)) s p t
   | Reachable \<Rightarrow> vwalk_bet (set (zip fs ts)) s (rev (stack r)) t \<and> distinct (stack r)"
  using dfs_thms.DFS_correct_1_strong dfs_thms.DFS_correct_2
  by (simp add: rbt_dfs_impl_def rbt_from_list_def rbt_dfs_initial_state_def dfs_initial_state_def
                dfs_impl_def dfs_thms.DFS_impl_to_DFS split: return.splits)

end



section \<open>Code Export of the Depth-First Searches\<close>

text \<open>Three depth-first searches, with vertices as machine integers (see
  \<open>Imperative/Code_Target_Machine_Int.thy\<close>):

    \<^item> the functional DFS on red-black trees of \<open>DFS_Example.thy\<close>, through its instances at
      @{typ nat} from \<open>DFS_Imperative.thy\<close>: @{const rbt_from_list} builds the adjacency map from
      an edge list, @{const rbt_dfs_initial_state} the initial state at a source and
      @{const rbt_dfs_impl} runs the search for a target;
    \<^item> the imperative DFS of \<open>DFS_Imperative.thy\<close>: @{const dfs_input_arrays_run} takes the arrays
      of the first and of the second endpoints of the edges, a source and a target, builds the
      adjacency map to neighbourhood lists and returns the final state;
    \<^item> the imperative DFS by neighbourhood iterators of \<open>DFS_by_Iterator_Imperative.thy\<close>:
      @{const dfs_edges_run} additionally takes the number of vertices, builds a CSR and returns
      the result and the stack, which holds the path found.

  The SML and the Scala code are compiled here. There is no Go compiler in Isabelle's environment,
  so the Go code is only generated.\<close>

export_code rbt_from_list rbt_dfs_initial_state rbt_dfs_impl checking SML Scala

text \<open>The imperative map of \<open>DFS_Imperative.thy\<close> reads and writes its array through
  @{const nth_oo} and @{const upd_oo} and grows it by @{const blit}. Their code equations convert the
  indices to @{typ integer}, which is not printed for machine integers, so the defining equations
  are the code equations again. The code modules \<open>Uint32\<close> of the AFP entry \<open>Native_Word\<close> and
  \<open>array_blit\<close> of \<open>Array_Blit\<close> are then unused and compute on arbitrary precision integers,
  so they are removed.\<close>

declare nth_oo_def[code] upd_oo_def[code] blit.simps[code]

code_printing code_module Uint32 \<rightharpoonup> (SML)
| code_module Uint32 \<rightharpoonup> (Scala)
| code_module array_blit \<rightharpoonup> (SML)

export_code dfs_input_arrays_run dfs_edges_run checking SML_imp Scala_imp

text \<open>The code for each target is written to \<open>DFS_code_exports/DFS_<variant>_<target>\<close> next to this
  theory.\<close>

ML \<open>
  val rbt_consts =
    [\<^const_name>\<open>rbt_from_list\<close>, \<^const_name>\<open>rbt_dfs_initial_state\<close>,
     \<^const_name>\<open>rbt_dfs_impl\<close>];
  val lists_consts = [\<^const_name>\<open>dfs_input_arrays_run\<close>];
  val csr_consts = [\<^const_name>\<open>dfs_edges_run\<close>];

  write_machine_code \<^context> rbt_consts "DFS_RBT" "SML" "DFS_RBT_SML" "DFS_RBT.sml";
  write_machine_code \<^context> rbt_consts "DFS_RBT" "Scala" "DFS_RBT_Scala" "DFS_RBT.scala";
  write_machine_code \<^context> rbt_consts "DFS_RBT" "Go" "DFS_RBT_Go" "";
  write_machine_code \<^context> lists_consts "DFS_Lists" "SML_imp" "DFS_Lists_SML" "DFS_Lists.sml";
  write_machine_code \<^context> lists_consts "DFS_Lists" "Scala_imp" "DFS_Lists_Scala"
    "DFS_Lists.scala";
  write_machine_code \<^context> lists_consts "DFS_Lists" "Go" "DFS_Lists_Go" "";
  write_machine_code \<^context> csr_consts "DFS_CSR" "SML_imp" "DFS_CSR_SML" "DFS_CSR.sml";
  write_machine_code \<^context> csr_consts "DFS_CSR" "Scala_imp" "DFS_CSR_Scala" "DFS_CSR.scala";
  write_machine_code \<^context> csr_consts "DFS_CSR" "Go" "DFS_CSR_Go" ""
\<close>

end
