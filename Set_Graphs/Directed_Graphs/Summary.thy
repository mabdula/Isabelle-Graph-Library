theory Summary
  imports 
    Pair_Graph
    Vwalk
begin

text \<open>Summary of the graph formalization DDFS.\<close>
text \<open>A graph is a set of edges, where each edge is a pair. The vertices are defined implicitly.\<close>
thm dVs_def

text \<open>Walks are a list of vertices, they are defined via the inductive predicate \<^term>\<open>vwalk\<close>. There
      are also walks with a defined start end end (\<^term>\<open>vwalk_bet\<close>).\<close>

text \<open>Basic lemmas\<close>
thm vwalk_then_edge vwalk_then_in_dVs vwalk_cons
thm hd_of_vwalk_bet hd_of_vwalk_bet' last_of_vwalk_bet

text \<open>Induction principles\<close>
thm induct_pcpl induct_pcpl_2

text \<open>Appending vwalks\<close>
thm append_vwalk_pref
thm append_vwalk_suff
thm append_vwalk

text \<open>Splitting vwalks\<close>
thm split_vwalk

text \<open>Paths with start and end\<close>
thm vwalk_bet_cons
thm vwalk_bet_cons_2
thm vwalk_bet_snoc
thm vwalk_bet_vwalk

text \<open>Edges and vwalks\<close>
thm vwalk_snoc_edge vwalk_snoc_edge'
thm vwalk_snoc_edge_2
thm vwalk_append_edge

text \<open>Vwalks representing transitive relations\<close>
thm vwalk_transitive_rel
thm vwalk_transitive_rel'
end