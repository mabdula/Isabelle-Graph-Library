theory Edge_Iterators
  imports Directed_Set_Graphs.Multigraph Data_Structures.Iterable_Set_Specs
begin

section \<open>A Directed Multigraph via Two Indexed Edge-Iterators\<close>

text \<open>The multigraph is presented to the algorithm through two @{locale indexed_iterable_set}s
      over the vertices: one whose iterable set at a vertex \<open>v\<close> is the \emph{outgoing} edges
      \<open>\<delta>\<^sup>+ v\<close>, and one whose iterable set at \<open>v\<close> is the \emph{ingoing} edges
      \<open>\<delta>\<^sup>- v\<close>. These are the same edge objects indexed by tail resp.\ head; no reversal is
      applied. Each direction is a separate combination of @{locale indexed_iterable_set} with
      @{locale multigraph_spec}.\<close>

locale outgoing_edge_iterator =
  multigraph_spec where fst = fst +
  outg: indexed_iterable_set where
      idx_invar     = out_invar and
      idx_abstract  = out_abstract and
      idx_current   = out_current and
      idx_has       = out_has and
      idx_iterated  = out_iterated and
      idx_remaining = out_remaining and
      idx_move      = out_move and
      idx_reset     = out_reset and
      K = \<V>
  for fst :: "'e \<Rightarrow> 'v"
  and out_invar     :: "'g \<Rightarrow> bool"
  and out_abstract  :: "'g \<Rightarrow> 'v \<Rightarrow> 'e set"
  and out_current   :: "'g \<Rightarrow> 'v \<Rightarrow> 'e"
  and out_has       :: "'g \<Rightarrow> 'v \<Rightarrow> bool"
  and out_iterated  :: "'g \<Rightarrow> 'v \<Rightarrow> 'e set"
  and out_remaining :: "'g \<Rightarrow> 'v \<Rightarrow> 'e set"
  and out_move      :: "'g \<Rightarrow> 'v \<Rightarrow> 'g"
  and out_reset     :: "'g \<Rightarrow> 'v \<Rightarrow> 'g"
begin

text \<open>The collection @{term og} implements the outgoing adjacency iff it is well-formed and
      abstracts, at every vertex, to that vertex's outgoing edges.\<close>

definition "out_graph_inv og \<longleftrightarrow>
   out_invar og \<and> (\<forall>v \<in> \<V>. out_abstract og v = \<delta>\<^sup>+ v)"

end

locale ingoing_edge_iterator =
  multigraph_spec where fst = fst +
  ing: indexed_iterable_set where
      idx_invar     = in_invar and
      idx_abstract  = in_abstract and
      idx_current   = in_current and
      idx_has       = in_has and
      idx_iterated  = in_iterated and
      idx_remaining = in_remaining and
      idx_move      = in_move and
      idx_reset     = in_reset and
      K = \<V>
  for fst :: "'e \<Rightarrow> 'v"
  and in_invar     :: "'g \<Rightarrow> bool"
  and in_abstract  :: "'g \<Rightarrow> 'v \<Rightarrow> 'e set"
  and in_current   :: "'g \<Rightarrow> 'v \<Rightarrow> 'e"
  and in_has       :: "'g \<Rightarrow> 'v \<Rightarrow> bool"
  and in_iterated  :: "'g \<Rightarrow> 'v \<Rightarrow> 'e set"
  and in_remaining :: "'g \<Rightarrow> 'v \<Rightarrow> 'e set"
  and in_move      :: "'g \<Rightarrow> 'v \<Rightarrow> 'g"
  and in_reset     :: "'g \<Rightarrow> 'v \<Rightarrow> 'g"
begin

text \<open>The collection @{term ig} implements the ingoing adjacency iff it is well-formed and
      abstracts, at every vertex, to that vertex's ingoing edges.\<close>

definition "in_graph_inv ig \<longleftrightarrow>
   in_invar ig \<and> (\<forall>v \<in> \<V>. in_abstract ig v = \<delta>\<^sup>- v)"

end

text \<open>Both directions over the same multigraph. The two collections may have different types.\<close>

locale bidirectional_iterator =
  outgoing_edge_iterator where fst = fst +
  ingoing_edge_iterator where fst = fst
  for fst :: "'e \<Rightarrow> 'v"

end
