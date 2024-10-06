theory Kruskal_Greedy
  imports Matroids_Greedy.Best_In_Greedy Spanning_Trees
begin

context graph_abs
begin

(* Cycle matroid on undirected graphs (TODO maybe put this in Spanning_Trees file) *)
interpretation graph_matroid: matroid
  where carrier = "G" and indep = has_no_cycle
  apply standard
  using finite_E has_no_cycle_indep_subset_carrier has_no_cycle_indep_ex has_no_cycle_indep_subset 
    has_no_cycle_augment
  by blast+

(* TODO put stuff here in spanning tree file *)

(* For showing that basis wrt has_no_cycle is spanning tree: *)
thm "graph_matroid.basis_def"
(* Need to show that (\<forall>x\<in>G - ?X. \<not> has_no_cycle (insert x ?X)) is equivalent to the fact that
every pair of vertices is connected by a walk 
If {v, w} is in G v and w are obviously connected by a walk

We should have a theorem:
If X does not contain a cycle but (insert {v, w} X) contains a cycle, there is a walk between
v and w (this is one direction of thm, basis imp connected)
\<Rightarrow> should almost be given by decycle_edge_path, along with some reasoning in insert_edge_cycle_ex_walk_betw

Other direction of thm (connected imp basis):
need smth like
  "X \<subseteq> G \<Longrightarrow> \<exists>p. walk_betw X v p w \<Longrightarrow> {v, w} \<notin> X \<Longrightarrow> \<exists>u c. decycle (insert {v, w} X) u c"

\<Longrightarrow> Should be able to just use contrapositive of has_no_cycle_ex_unique_path

*)



end

(* Should connecting stuff go in separate file + locale? How to do this *)








end