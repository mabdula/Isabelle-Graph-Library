theory Multigraph_Potentials
  imports Multigraph_Weighted_Paths
begin

provenance ai


section \<open>Potentials on Weighted Multigraphs\<close>

text \<open>A real weight function on a finite directed multigraph is \<open>conservative\<close> when no closed
      walk has negative total weight. This is the classical hypothesis under which a potential function exists: a
      real-valued function on vertices making every edge's \<open>reduced cost\<close> \<open>w e + \<pi> (tail e) -
      \<pi> (head e)\<close> non-negative. The characterisation theorem below proves both directions, purely in
      terms of \<open>multigraph\<close>, \<open>weight\<close>, \<open>path_bet\<close> and
      \<open>distance_set\<close>, with no reference to flows, capacities or costs.\<close>

context multigraph
begin

subsection \<open>Conservative Weight Functions\<close>

definition conservative :: "('edge \<Rightarrow> real) \<Rightarrow> bool" where
  "conservative w \<longleftrightarrow>
     (\<forall> es v. es \<noteq> [] \<longrightarrow> path_bet es v v \<longrightarrow> weight w es \<ge> 0)"

lemma conservativeI:
  "(\<And> es v. \<lbrakk>es \<noteq> []; path_bet es v v\<rbrakk>
    \<Longrightarrow> weight w es \<ge> 0) \<Longrightarrow> conservative w"
  by (auto simp: conservative_def)

lemma conservativeD:
  "\<lbrakk>conservative w; es \<noteq> []; path_bet es v v\<rbrakk> \<Longrightarrow> weight w es \<ge> 0"
  by (auto simp: conservative_def)

subsection \<open>A Potential Forces Conservativity\<close>

lemma path_bet_telescope:
  fixes \<pi> :: "'a \<Rightarrow> real"
  assumes "path_bet es u v"
  shows "(\<Sum> e \<leftarrow> es. \<pi> (fst e) - \<pi> (snd e)) = \<pi> u - \<pi> v"
  using assms
  by (induction es arbitrary: u) (auto simp: path_bet_Cons)

lemma conservative_of_potential:
  assumes "\<forall> e \<in> \<E>. w e + \<pi> (fst e) - \<pi> (snd e) \<ge> 0"
  shows "conservative w"
proof(rule conservativeI)
  fix es v
  assume "path_bet es v v"
  thus "weight w es \<ge> 0"
    using assms path_bet_edges_subset[of es v v] path_bet_telescope[of es v v \<pi>]
      sum_list_nonneg[of "map (\<lambda>e. w e + (\<pi> (fst e) - \<pi> (snd e))) es"]
    by (fastforce simp: weight_def sum_list_addf)
qed

subsection \<open>Conservativity Yields a Potential, via Distance from the Vertex Set\<close>

lemma conservative_shortcut:
  assumes "conservative w"
  shows "path_bet es u v
    \<Longrightarrow> \<exists> es'. path_bet es' u v \<and> distinct es' \<and> weight w es' \<le> weight w es"
proof(induction "length es" arbitrary: es rule: less_induct)
  case less
  show ?case
  proof(cases "distinct es")
    case False
    obtain x p1 p2 p3 where "es = p1 @ x # p2 @ x # p3" "path_bet (p1 @ x # p3) u v"
      "path_bet (x # p2) (fst x) (fst x)"
      using less.prems(1) False
      by (blast elim: path_bet_not_distinct)
    thus ?thesis
      using assms less.hyps[of "p1 @ x # p3"] conservativeD[of w "x # p2" "fst x"]
      by fastforce
  qed (use less.prems in blast)
qed

lemma distance_neq_minf: "distance w a b \<noteq> - \<infinity>"
proof(cases "reachable a b")
  case True
  thus ?thesis
    by (rule reachable_dist_2[where w=w]) simp
qed (simp add: unreachable_dist)

lemma conservative_distance_set_finite:
  assumes "v \<in> \<V>"
  shows "distance_set w \<V> v \<noteq> \<infinity>" "distance_set w \<V> v \<noteq> - \<infinity>"
proof-
  show "distance_set w \<V> v \<noteq> \<infinity>"
    using assms dist_set_mem[of v \<V> w v] reachable_dist[of v v w] reachable_refl[of v]
    by auto
  show "distance_set w \<V> v \<noteq> - \<infinity>"
    by (rule distance_set_wit[of \<V> w v]) (use \<V>_finite V_non_empt distance_neq_minf in auto)
qed

lemma conservative_distance_set_triangle:
  assumes "conservative w" "e \<in> \<E>"
  shows "distance_set w \<V> (snd e) \<le> distance_set w \<V> (fst e) + ereal (w e)"
proof-
  have "distance_set w \<V> (fst e) < \<infinity>"
    using assms(2) conservative_distance_set_finite(1)[of "fst e" w] fst_E_V
    by simp
  then obtain es s where "s \<in> \<V>" "is_shortest_path w es s (fst e)"
    "distance w s (fst e) = distance_set w \<V> (fst e)"
    using \<V>_finite
    by (auto elim: dist_set_less_infty_get_path)
  moreover then obtain es' where "path_bet es' s (snd e)" "distinct es'"
    "weight w es' \<le> weight w (es @ [e])"
    using assms conservative_shortcut[of w "es @ [e]" s "snd e"] path_bet_snocI[of es s e]
    by (auto simp: is_shortest_path_def)
  ultimately show ?thesis
    using distance_set_le_path[of s \<V> es' "snd e" w]
    by (fastforce simp: is_shortest_path_def intro: order_trans)
qed

lemma potential_of_conservative:
  assumes "conservative w"
  shows "\<exists> \<pi>. \<forall> e \<in> \<E>. w e + \<pi> (fst e) - \<pi> (snd e) \<ge> 0"
proof(intro exI[of _ "\<lambda>v. real_of_ereal (distance_set w \<V> v)"] ballI)
  fix e
  assume "e \<in> \<E>"
  thus "w e + real_of_ereal (distance_set w \<V> (fst e)) - real_of_ereal (distance_set w \<V> (snd e)) \<ge> 0"
    using assms conservative_distance_set_triangle[of w e] fst_E_V[of e] snd_E_V[of e]
      conservative_distance_set_finite[of "fst e" w] conservative_distance_set_finite[of "snd e" w]
    by (cases "distance_set w \<V> (fst e)"; cases "distance_set w \<V> (snd e)") auto
qed

subsection \<open>No Negative Simple Cycle Already Suffices\<close>

text \<open>A checkable strengthening of \<open>conservative\<close>'s hypothesis side: it is enough to rule out
      negative-weight simple (distinct) closed walks, since any closed walk shortens, without
      increasing weight, to one that is simple --- the same decomposition used by
      \<open>conservative_shortcut\<close>, but run here as the base case of the bootstrap instead of relying on
      it.\<close>

lemma closed_walk_nonneg_of_simple:
  assumes "\<And> es v. \<lbrakk>es \<noteq> []; path_bet es v v; distinct es\<rbrakk>
    \<Longrightarrow> weight w es \<ge> 0"
  shows "\<lbrakk>path_bet es v v; es \<noteq> []\<rbrakk> \<Longrightarrow> weight w es \<ge> 0"
proof(induction "length es" arbitrary: es v rule: less_induct)
  case less
  show ?case
  proof(cases "distinct es")
    case False
    obtain x p1 p2 p3 where "es = p1 @ x # p2 @ x # p3" "path_bet (p1 @ x # p3) v v"
      "path_bet (x # p2) (fst x) (fst x)"
      using less.prems(1) False
      by (blast elim: path_bet_not_distinct)
    thus ?thesis
      using less.hyps[of "p1 @ x # p3" v] less.hyps[of "x # p2" "fst x"]
      by simp
  qed (use less.prems assms in blast)
qed

lemma conservative_of_simple:
  assumes "\<And> es v. \<lbrakk>es \<noteq> []; path_bet es v v; distinct es\<rbrakk>
    \<Longrightarrow> weight w es \<ge> 0"
  shows "conservative w"
  using assms closed_walk_nonneg_of_simple
  by (blast intro: conservativeI)

subsection \<open>The Characterisation Theorem\<close>

theorem ex_potential_iff_conservative:
  "(\<exists> \<pi>. \<forall> e \<in> \<E>. w e + \<pi> (fst e) - \<pi> (snd e) \<ge> 0)
    \<longleftrightarrow> conservative w"
  using conservative_of_potential potential_of_conservative
  by blast

end
end
