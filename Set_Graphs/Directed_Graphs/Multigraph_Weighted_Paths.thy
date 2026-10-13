theory Multigraph_Weighted_Paths
  imports Directed_Set_Graphs.Multigraph
begin

section \<open>Weighted Paths and Distances in a Multigraph\<close>

text \<open>This theory develops, for a directed multigraph presented \<^emph>\<open>via\<close> the @{locale multigraph}
      locale, the theory of \<^emph>\<open>real-weighted\<close> path lengths and the induced distances. It mirrors, for
      real edge weights, the development of unweighted vertex-walk distances in \<open>Dist.thy\<close>.
      Edge weights may be negative, so distances are taken over
      \<^emph>\<open>distinct\<close> (simple) edge paths and are valued in @{typ ereal} (finitely many simple paths in a
      finite graph, so an unreachable target has distance \<open>+\<infinity>\<close>).\<close>

text \<open>The concepts need no assumption on the graph and are defined in @{locale multigraph_spec}; the
      lemmas about them are proved in @{locale multigraph}.\<close>

context multigraph_spec
begin

subsection \<open>Concepts\<close>

text \<open>The length of an edge path under a real weight function @{term w} is the sum of the weights of
      its edges.\<close>

definition weight :: "('edge \<Rightarrow> real) \<Rightarrow> 'edge list \<Rightarrow> real" where
  "weight w es = (\<Sum>e\<leftarrow>es. w e)"

text \<open>A path between @{term u} and @{term v} is a list of graph edges forming a @{const
      multigraph_path} whose first tail is @{term u} and whose last head is @{term v}; the empty
      path connects a vertex to itself. This is the edge-list analogue of @{term vwalk_bet}.  The
      lemmas below give a self-contained calculus of such paths (introduction, elimination,
      composition, splitting) so that the underlying @{const awalk}/@{const make_pair} encoding need
      never be unfolded again.\<close>

definition path_bet :: "'edge list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "path_bet es u v \<longleftrightarrow> set es \<subseteq> \<E> \<and> multigraph_path es \<and>
     (if es = [] then u = v else fst (hd es) = u \<and> snd (last es) = v)"

text \<open>Because edge weights may be negative, a shortest walk need not exist over \<^emph>\<open>all\<close> paths (a
      negative cycle could be repeated). We therefore measure distance over \<^emph>\<open>distinct\<close>
      (simple) paths only. In a finite graph there are finitely many of these, so the infimum below
      is attained whenever the target is reachable, and equals @{term \<open>\<infinity>\<close>} otherwise. Distances
      live in @{typ ereal}.\<close>

definition spaths_bet :: "'a \<Rightarrow> 'a \<Rightarrow> 'edge list set" where
  "spaths_bet u v = {es. path_bet es u v \<and> distinct es}"

definition distance :: "('edge \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ereal" where
  "distance w u v = (INF es \<in> spaths_bet u v. ereal (weight w es))"

definition reachable :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "reachable u v \<longleftrightarrow> spaths_bet u v \<noteq> {}"

definition is_shortest_path :: "('edge \<Rightarrow> real) \<Rightarrow> 'edge list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_shortest_path w es u v \<longleftrightarrow>
      path_bet es u v \<and> distinct es \<and> distance w u v = ereal (weight w es)"

text \<open>The distance from a set of sources @{term U} to a target @{term v} is the least distance from
      any source. Attainment lemmas require @{term U} to be finite (as it is for the source set of a
      concrete algorithm); the ordering lemmas hold unconditionally.\<close>

definition distance_set :: "('edge \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> ereal" where
  "distance_set w U v = (INF u \<in> U. distance w u v)"

end


context multigraph
begin

subsection \<open>The Weight of a Path\<close>

lemma weight_Nil[simp]: "weight w [] = 0"
  and weight_Cons[simp]: "weight w (e#es) = w e + weight w es"
  by(auto simp: weight_def)

lemma weight_append[simp]: "weight w (es1 @ es2) = weight w es1 + weight w es2"
  by(auto simp: weight_def)

lemma weight_snoc: "weight w (es @ [e]) = weight w es + w e"
  and weight_single: "weight w [e] = w e"
  and weight_rev: "weight w (rev es) = weight w es"
  by(auto simp: weight_def rev_map[symmetric])


subsection \<open>Paths between two Vertices\<close>

lemma path_bet_Nil[simp]: "path_bet [] u v \<longleftrightarrow> u = v"
  by(auto simp: path_bet_def multigraph_path_intros)

lemma path_bet_Nil_iff: "path_bet [] u u"
  by simp

lemma path_bet_single: "e \<in> \<E> \<Longrightarrow> path_bet [e] (fst e) (snd e)"
  by(auto simp: path_bet_def multigraph_path_intros)

lemma path_bet_edges_subset: "path_bet es u v \<Longrightarrow> set es \<subseteq> \<E>"
  by(auto simp: path_bet_def)

lemma path_bet_hd: "path_bet es u v \<Longrightarrow> es \<noteq> [] \<Longrightarrow> fst (hd es) = u"
  by(auto simp: path_bet_def)

lemma path_bet_last: "path_bet es u v \<Longrightarrow> es \<noteq> [] \<Longrightarrow> snd (last es) = v"
  by(auto simp: path_bet_def)

lemma path_bet_multigraph_path: "path_bet es u v \<Longrightarrow> multigraph_path es"
  by(auto simp: path_bet_def)

text \<open>Composition of @{const multigraph_path}s and its consequences for @{const path_bet}.\<close>

lemma multigraph_path_tl: "multigraph_path (e # es) \<Longrightarrow> multigraph_path es"
  by(auto elim: flowpath_cases simp: multigraph_path_intros(1))

lemma multigraph_path_append:
  assumes "multigraph_path es1" "multigraph_path es2"
          "es1 = [] \<or> es2 = [] \<or> snd (last es1) = fst (hd es2)"
        shows "multigraph_path (es1 @ es2)"
  using assms
proof(induction es1)
  case Nil
  then show ?case by auto
next
  case (Cons e es1)
  show ?case
  proof(cases "es1 = []")
    case True
    show ?thesis
    proof(cases "es2 = []")
      case True
      then show ?thesis using Cons \<open>es1 = []\<close> by (auto simp: multigraph_path_intros)
    next
      case False
      then show ?thesis
        using Cons \<open>es1 = []\<close> by (auto simp: multigraph_path_intros(3))
    qed
  next
    case False
    have mp1: "multigraph_path es1" and conn: "snd e = fst (hd es1)"
      using Cons.prems(1) \<open>es1 \<noteq> []\<close> by (auto elim: flowpath_cases)
    have "multigraph_path (es1 @ es2)"
      using mp1 Cons.prems(2,3) \<open>es1 \<noteq> []\<close> by (auto intro!: Cons.IH)
    then show ?thesis
      using conn \<open>es1 \<noteq> []\<close> by (auto simp: multigraph_path_intros(3))
  qed
qed

lemma multigraph_path_pref: "multigraph_path (es1 @ es2) \<Longrightarrow> multigraph_path es1"
proof(induction es1)
  case (Cons e es1)
  show ?case
  proof(cases "es1 = []")
    case True
    then show ?thesis by (auto simp: multigraph_path_intros)
  next
    case False
    have "multigraph_path ((e # es1) @ es2)" using Cons.prems by simp
    then have "snd e = fst (hd (es1 @ es2))" "multigraph_path (es1 @ es2)"
      using \<open>es1 \<noteq> []\<close> by (auto elim: flowpath_cases)
    then show ?thesis
      using Cons.IH \<open>es1 \<noteq> []\<close> by (auto simp: multigraph_path_intros(3))
  qed
qed (auto simp: multigraph_path_intros)

lemma multigraph_path_suff: "multigraph_path (es1 @ es2) \<Longrightarrow> multigraph_path es2"
  by(induction es1) (auto dest: multigraph_path_tl)

lemma multigraph_path_append_conn:
  "multigraph_path (es1 @ es2) \<Longrightarrow> es1 \<noteq> [] \<Longrightarrow> es2 \<noteq> [] \<Longrightarrow> snd (last es1) = fst (hd es2)"
proof(induction es1)
  case (Cons e es1)
  show ?case
  proof(cases "es1 = []")
    case True
    then show ?thesis using Cons.prems by (auto elim: flowpath_cases)
  next
    case False
    have "multigraph_path (es1 @ es2)"
      using Cons.prems by (auto dest: multigraph_path_tl)
    then show ?thesis
      using Cons.IH \<open>es1 \<noteq> []\<close> Cons.prems(3) by simp
  qed
qed simp

lemma path_bet_append:
  assumes "path_bet es1 u v" "path_bet es2 v w"
  shows "path_bet (es1 @ es2) u w"
proof(cases "es1 = []")
  case True
  then show ?thesis using assms by (auto simp: path_bet_def)
next
  case False
  show ?thesis
  proof(cases "es2 = []")
    case True
    then show ?thesis using assms by (auto simp: path_bet_def)
  next
    case False
    have "snd (last es1) = fst (hd es2)"
      using assms \<open>es1 \<noteq> []\<close> \<open>es2 \<noteq> []\<close> by (auto simp: path_bet_def)
    then have "multigraph_path (es1 @ es2)"
      using assms by (auto intro!: multigraph_path_append simp: path_bet_def)
    then show ?thesis
      using assms \<open>es1 \<noteq> []\<close> \<open>es2 \<noteq> []\<close> by (auto simp: path_bet_def)
  qed
qed

lemma path_bet_pref:
  "path_bet (es1 @ es2) u w \<Longrightarrow> es1 \<noteq> [] \<Longrightarrow> es2 \<noteq> [] \<Longrightarrow> path_bet es1 u (fst (hd es2))"
  by(auto simp: path_bet_def multigraph_path_append_conn dest: multigraph_path_pref)

lemma path_bet_suff:
  "path_bet (es1 @ es2) u w \<Longrightarrow> es1 \<noteq> [] \<Longrightarrow> es2 \<noteq> [] \<Longrightarrow> path_bet es2 (snd (last es1)) w"
  by(auto simp: path_bet_def multigraph_path_append_conn dest: multigraph_path_suff)

lemma path_bet_fst_in_V:
  assumes "path_bet es u v" "es \<noteq> []" shows "u \<in> \<V>"
proof -
  have "hd es \<in> \<E>" "fst (hd es) = u"
    using assms hd_in_set by (auto simp: path_bet_def)
  then show ?thesis using fst_E_V by auto
qed

lemma path_bet_snd_in_V:
  assumes "path_bet es u v" "es \<noteq> []" shows "v \<in> \<V>"
proof -
  have "last es \<in> \<E>" "snd (last es) = v"
    using assms last_in_set by (auto simp: path_bet_def)
  then show ?thesis using snd_E_V by auto
qed

lemma path_bet_verts_in_V:
  assumes "path_bet es u v" "e \<in> set es" shows "fst e \<in> \<V>" "snd e \<in> \<V>"
proof -
  have "e \<in> \<E>" using assms by (auto simp: path_bet_def)
  then show "fst e \<in> \<V>" "snd e \<in> \<V>" using fst_E_V snd_E_V by auto
qed

lemma path_bet_ConsI: "e \<in> \<E> \<Longrightarrow> path_bet es (snd e) w \<Longrightarrow> path_bet (e # es) (fst e) w"
  using path_bet_append[OF path_bet_single] by simp

lemma path_bet_snocI: "path_bet es u (fst e) \<Longrightarrow> e \<in> \<E> \<Longrightarrow> path_bet (es @ [e]) u (snd e)"
  using path_bet_append path_bet_single by blast

lemma path_bet_ConsE:
  assumes "path_bet (e # es) u w"
  obtains "e \<in> \<E>" "fst e = u" "path_bet es (snd e) w"
proof -
  have eE: "e \<in> \<E>" and fu: "fst e = u" and mp: "multigraph_path (e # es)" and sub: "set es \<subseteq> \<E>"
    using assms by (auto simp: path_bet_def)
  have "path_bet es (snd e) w"
  proof(cases "es = []")
    case True
    then show ?thesis using assms by (auto simp: path_bet_def multigraph_path_intros(1))
  next
    case False
    have "snd e = fst (hd es)" using mp \<open>es \<noteq> []\<close> by (auto elim: flowpath_cases)
    moreover have "snd (last es) = w" using assms \<open>es \<noteq> []\<close> by (auto simp: path_bet_def)
    ultimately show ?thesis
      using sub multigraph_path_tl[OF mp] \<open>es \<noteq> []\<close> by (auto simp: path_bet_def)
  qed
  then show ?thesis using eE fu that by blast
qed

lemma path_bet_appendE:
  assumes "path_bet (es1 @ es2) u w"
  obtains x where "path_bet es1 u x" "path_bet es2 x w"
proof(cases "es1 = []")
  case True
  then show ?thesis using assms that[of u] by simp
next
  case False
  show ?thesis
  proof(cases "es2 = []")
    case True
    then show ?thesis using assms that[of w] by simp
  next
    case False
    show ?thesis
      using path_bet_pref[OF assms \<open>es1 \<noteq> []\<close> \<open>es2 \<noteq> []\<close>]
            path_bet_suff[OF assms \<open>es1 \<noteq> []\<close> \<open>es2 \<noteq> []\<close>]
            multigraph_path_append_conn assms \<open>es1 \<noteq> []\<close> \<open>es2 \<noteq> []\<close>
      by (auto simp: path_bet_def intro: that)
  qed
qed

lemma path_bet_edge_split:
  assumes "path_bet es u w" "e \<in> set es"
  obtains es1 es2 where "es = es1 @ e # es2" "path_bet es1 u (fst e)" "path_bet es2 (snd e) w"
proof -
  from split_list[OF assms(2)] obtain es1 es2 where dec: "es = es1 @ e # es2" by blast
  have "path_bet (es1 @ (e # es2)) u w" using assms(1) dec by simp
  then obtain x where p1: "path_bet es1 u x" and p2: "path_bet (e # es2) x w"
    by (auto elim: path_bet_appendE)
  from p2 have "fst e = x" "path_bet es2 (snd e) w" by (auto elim: path_bet_ConsE)
  then show ?thesis using p1 dec that by auto
qed


subsection \<open>Simple Paths, Distance and Reachability\<close>

lemma finite_spaths_bet: "finite (spaths_bet u v)"
proof -
  have "spaths_bet u v \<subseteq> {es. set es \<subseteq> \<E> \<and> distinct es}"
    by(auto simp: spaths_bet_def dest: path_bet_edges_subset)
  then show ?thesis
    using finite_subset_distinct[OF finite_E] by(auto elim: finite_subset)
qed

lemma spaths_betI: "path_bet es u v \<Longrightarrow> distinct es \<Longrightarrow> es \<in> spaths_bet u v"
  by(auto simp: spaths_bet_def)

lemma spaths_betD: "es \<in> spaths_bet u v \<Longrightarrow> path_bet es u v \<and> distinct es"
  by(auto simp: spaths_bet_def)


lemma spath_dist: "es \<in> spaths_bet u v \<Longrightarrow> distance w u v \<le> ereal (weight w es)"
  by(auto simp: distance_def intro: INF_lower)

lemma path_bet_dist: "path_bet es u v \<Longrightarrow> distinct es \<Longrightarrow> distance w u v \<le> ereal (weight w es)"
  by(auto simp: spath_dist spaths_betI)

lemma unreachable_dist: "\<not> reachable u v \<Longrightarrow> distance w u v = \<infinity>"
  by(auto simp: distance_def reachable_def top_ereal_def)

lemma reachable_dist: "reachable u v \<Longrightarrow> distance w u v < \<infinity>"
  by(auto simp: reachable_def dest!: spath_dist[of _ u v w] order_le_less_trans[rotated])

lemma dist_reachable: "distance w u v < \<infinity> \<Longrightarrow> reachable u v"
  using unreachable_dist by force

text \<open>In a finite graph the infimum is attained: a reachable target has an actual shortest simple
      path realising its distance.\<close>

lemma reachable_dist_2:
  assumes "reachable u v"
  obtains es where "path_bet es u v" "distinct es" "distance w u v = ereal (weight w es)"
proof -
  have "distance w u v \<in> (\<lambda>es. ereal (weight w es)) ` spaths_bet u v"
    unfolding distance_def
    using finite_spaths_bet assms[unfolded reachable_def]
    by (intro finite_INF_in)
  then obtain es where "es \<in> spaths_bet u v" "distance w u v = ereal (weight w es)"
    by auto
  then show ?thesis using that by (auto simp: spaths_bet_def)
qed

text \<open>Every path contains a simple path with the same endpoints; hence reachability is witnessed by
      simple paths and is transitive, even though shortest \<^emph>\<open>distinct\<close> paths need not concatenate to a
      distinct path.\<close>

lemma path_bet_imp_spath:
  "path_bet es u v \<Longrightarrow> \<exists>es'. path_bet es' u v \<and> distinct es' \<and> set es' \<subseteq> set es"
proof(induction "length es" arbitrary: es u v rule: less_induct)
  case less
  show ?case
  proof(cases "distinct es")
    case True
    then show ?thesis using less.prems by blast
  next
    case False
    from not_distinct_decomp[OF False] obtain p1 x p2 p3
      where dec0: "es = p1 @ [x] @ p2 @ [x] @ p3" by blast
    have dec: "es = p1 @ x # p2 @ x # p3" using dec0 by simp
    have "path_bet (p1 @ (x # p2 @ x # p3)) u v" using less.prems dec by simp
    then obtain m1 where p1p: "path_bet p1 u m1" and rest1: "path_bet (x # p2 @ x # p3) m1 v"
      by (auto elim: path_bet_appendE)
    from rest1 have xE: "x \<in> \<E>" and m1: "fst x = m1" and rest2: "path_bet (p2 @ x # p3) (snd x) v"
      by (auto elim: path_bet_ConsE)
    from rest2 obtain m2 where p2p: "path_bet p2 (snd x) m2" and rest3: "path_bet (x # p3) m2 v"
      by (auto elim: path_bet_appendE)
    from rest3 have m2: "fst x = m2" and p3p: "path_bet p3 (snd x) v"
      by (auto elim: path_bet_ConsE)
    have "path_bet (x # p3) (fst x) v" using xE p3p by (rule path_bet_ConsI)
    then have "path_bet (p1 @ x # p3) u v"
      using p1p m1 path_bet_append by fastforce
    moreover have "length (p1 @ x # p3) < length es" using dec by simp
    ultimately obtain es' where "path_bet es' u v" "distinct es'" "set es' \<subseteq> set (p1 @ x # p3)"
      using less.hyps by blast
    then show ?thesis using dec by auto
  qed
qed

lemma reachable_iff_path: "reachable u v \<longleftrightarrow> (\<exists>es. path_bet es u v)"
  by(auto simp: reachable_def spaths_bet_def dest: path_bet_imp_spath)

lemma reachableI: "path_bet es u v \<Longrightarrow> reachable u v"
  using reachable_iff_path by blast

lemma reachable_refl: "reachable u u"
  by(auto simp: reachable_iff_path intro!: exI[of _ "[]"])

lemma reachable_edge: "e \<in> \<E> \<Longrightarrow> reachable (fst e) (snd e)"
  using path_bet_single by(auto simp: reachable_iff_path)

lemma reachable_trans:
  assumes "reachable u v" "reachable v w" shows "reachable u w"
proof -
  obtain es1 where "path_bet es1 u v" using assms(1) reachable_iff_path by blast
  moreover obtain es2 where "path_bet es2 v w" using assms(2) reachable_iff_path by blast
  ultimately have "path_bet (es1 @ es2) u w" using path_bet_append by blast
  then show ?thesis by (rule reachableI)
qed

lemma distance_self_le0: "distance w u u \<le> 0"
  using path_bet_dist[of "[]" u u w] by (simp add: zero_ereal_def)


subsection \<open>Shortest Paths\<close>

lemma is_shortest_pathI:
  "path_bet es u v \<Longrightarrow> distinct es \<Longrightarrow> distance w u v = ereal (weight w es) \<Longrightarrow>
     is_shortest_path w es u v"
  by(auto simp: is_shortest_path_def)

lemma is_shortest_path_path_bet: "is_shortest_path w es u v \<Longrightarrow> path_bet es u v"
  and is_shortest_path_distinct: "is_shortest_path w es u v \<Longrightarrow> distinct es"
  and is_shortest_path_dist: "is_shortest_path w es u v \<Longrightarrow> distance w u v = ereal (weight w es)"
  by(auto simp: is_shortest_path_def)

lemma is_shortest_path_exists:
  assumes "reachable u v"
  obtains es where "is_shortest_path w es u v"
  using reachable_dist_2[OF assms] by(auto simp: is_shortest_path_def)

lemma is_shortest_path_exists_2:
  assumes "distance w u v < \<infinity>"
  obtains es where "is_shortest_path w es u v"
  using dist_reachable[OF assms] by(auto elim: is_shortest_path_exists)

text \<open>The triangle inequality holds along any two paths that together form a \<^emph>\<open>distinct\<close> (simple)
      path; unlike the unweighted case, distinctness of the concatenation is essential, since a
      negative cycle could otherwise be inserted.\<close>

lemma triangle_ineq_path:
  assumes "path_bet es1 u v" "path_bet es2 v w" "distinct (es1 @ es2)"
  shows "distance wt u w \<le> ereal (weight wt es1) + ereal (weight wt es2)"
proof -
  have "path_bet (es1 @ es2) u w" using assms(1,2) by (rule path_bet_append)
  then have "distance wt u w \<le> ereal (weight wt (es1 @ es2))"
    using assms(3) by (rule path_bet_dist)
  then show ?thesis by simp
qed

lemma triangle_ineq_distinct:
  assumes "is_shortest_path wt es1 u v" "is_shortest_path wt es2 v w" "distinct (es1 @ es2)"
  shows "distance wt u w \<le> distance wt u v + distance wt v w"
  using triangle_ineq_path[OF is_shortest_path_path_bet[OF assms(1)]
          is_shortest_path_path_bet[OF assms(2)] assms(3)]
        is_shortest_path_dist[OF assms(1)] is_shortest_path_dist[OF assms(2)]
  by simp


subsection \<open>Distance from a Set of Vertices\<close>

lemma dist_set_mem: "u \<in> U \<Longrightarrow> distance_set w U v \<le> distance w u v"
  by(auto simp: distance_set_def intro: INF_lower)

lemma distance_set_union: "distance_set w (U \<union> V) v \<le> distance_set w U v"
  by(auto simp: distance_set_def intro: INF_superset_mono)

lemma distance_set_mono: "U \<subseteq> V \<Longrightarrow> distance_set w V v \<le> distance_set w U v"
  by(auto simp: distance_set_def intro: INF_superset_mono)

lemma distance_set_single_source: "distance_set w {s} v = distance w s v"
  by(auto simp: distance_set_def)

lemma distance_set_empty: "distance_set w {} v = \<infinity>"
  by(auto simp: distance_set_def top_ereal_def)

lemma distance_set_le_path:
  "u \<in> U \<Longrightarrow> path_bet es u v \<Longrightarrow> distinct es \<Longrightarrow> distance_set w U v \<le> ereal (weight w es)"
  using dist_set_mem[of u U w v] path_bet_dist[of es u v w] by simp

lemma distance_set_infty_iff:
  "distance_set w U v = \<infinity> \<longleftrightarrow> (\<forall>u\<in>U. \<not> reachable u v)"
proof
  assume *: "distance_set w U v = \<infinity>"
  show "\<forall>u\<in>U. \<not> reachable u v"
  proof(intro ballI notI)
    fix u assume "u \<in> U" "reachable u v"
    then have "distance w u v < \<infinity>" using reachable_dist by auto
    moreover have "distance_set w U v \<le> distance w u v" using \<open>u \<in> U\<close> dist_set_mem by auto
    ultimately show False using * by auto
  qed
next
  assume "\<forall>u\<in>U. \<not> reachable u v"
  then have "distance w u v = \<infinity>" if "u \<in> U" for u
    using that unreachable_dist by auto
  then show "distance_set w U v = \<infinity>"
    by(cases "U = {}") (auto simp: distance_set_def top_ereal_def)
qed

text \<open>For a finite source set the infimum is attained by an actual source and shortest simple path.\<close>

lemma distance_set_wit:
  assumes "finite U" "U \<noteq> {}"
  obtains u where "u \<in> U" "distance_set w U v = distance w u v"
proof -
  have "distance_set w U v \<in> (\<lambda>u. distance w u v) ` U"
    unfolding distance_set_def using assms by (intro finite_INF_in)
  then show ?thesis using that by auto
qed

lemma distance_set_reachable:
  assumes "finite U" "distance_set w U v < \<infinity>"
  obtains u where "u \<in> U" "reachable u v" "distance w u v = distance_set w U v"
proof -
  have "U \<noteq> {}" using assms(2) distance_set_empty by auto
  then obtain u where u: "u \<in> U" "distance_set w U v = distance w u v"
    using distance_set_wit[OF assms(1)] by blast
  then have "reachable u v" using assms(2) dist_reachable by auto
  then show ?thesis using u that by auto
qed

lemma dist_set_less_infty_get_path:
  assumes "finite U" "distance_set w U v < \<infinity>"
  obtains es u where "u \<in> U" "is_shortest_path w es u v" "distance w u v = distance_set w U v"
proof -
  obtain u where u: "u \<in> U" "reachable u v" "distance w u v = distance_set w U v"
    using distance_set_reachable[OF assms] by blast
  then obtain es where "is_shortest_path w es u v" by (auto elim: is_shortest_path_exists)
  then show ?thesis using u that by auto
qed

subsection \<open>Subgraphs\<close>

context
  fixes E' assumes sub: "E' \<subseteq> \<E>"
begin

interpretation sub: multigraph_spec E' fst snd create_edge .

lemma sub_path_bet: "sub.path_bet es u v \<longleftrightarrow> path_bet es u v \<and> set es \<subseteq> E'"
  using sub by (auto simp: sub.path_bet_def path_bet_def)

lemma sub_path_bet_ConsE:
  assumes "sub.path_bet (e # es) u w"
  obtains "e \<in> E'" "fst e = u" "sub.path_bet es (snd e) w"
  using assms by (auto simp: sub_path_bet elim: path_bet_ConsE)

lemma sub_path_bet_snocI: "\<lbrakk>sub.path_bet es u (fst e); e \<in> E'\<rbrakk> \<Longrightarrow> sub.path_bet (es @ [e]) u (snd e)"
  using sub by (auto simp: sub_path_bet intro: path_bet_snocI)

lemma sub_path_bet_edge_split:
  assumes "sub.path_bet es u w" "e \<in> set es"
  obtains es1 es2 where "es = es1 @ e # es2" "sub.path_bet es1 u (fst e)" "sub.path_bet es2 (snd e) w"
proof -
  have p: "path_bet es u w" and s: "set es \<subseteq> E'" using assms(1) by (simp_all add: sub_path_bet)
  obtain es1 es2 where "es = es1 @ e # es2" "path_bet es1 u (fst e)" "path_bet es2 (snd e) w"
    by (rule path_bet_edge_split[OF p assms(2)])
  with s show ?thesis by (intro that[of es1 es2]) (auto simp: sub_path_bet)
qed

lemma sub_reachable_iff_path: "sub.reachable u v \<longleftrightarrow> (\<exists>es. sub.path_bet es u v)"
proof
  assume "\<exists>es. sub.path_bet es u v"
  then obtain es where "path_bet es u v" "set es \<subseteq> E'" by (auto simp: sub_path_bet)
  then obtain es' where "path_bet es' u v" "distinct es'" "set es' \<subseteq> E'"
    using path_bet_imp_spath[of es u v] by blast
  then show "sub.reachable u v" by (auto simp: sub.reachable_def sub.spaths_bet_def sub_path_bet)
qed (auto simp: sub.reachable_def sub.spaths_bet_def)

lemma sub_distance_set_le_path:
  "\<lbrakk>u \<in> U; sub.path_bet es u v; distinct es\<rbrakk> \<Longrightarrow> sub.distance_set w U v \<le> ereal (weight w es)"
  unfolding sub.distance_set_def sub.distance_def sub.spaths_bet_def
  by (rule INF_lower2[of u]) (auto intro: INF_lower)

lemma sub_distance_set_infty_iff: "sub.distance_set w U v = \<infinity> \<longleftrightarrow> (\<forall>u\<in>U. \<not> sub.reachable u v)"
  unfolding sub.distance_set_def sub.distance_def sub.reachable_def top_ereal_def[symmetric] INF_top_conv
  by (auto simp: top_ereal_def)

lemma sub_dist_set_less_infty_get_path:
  assumes "finite U" "sub.distance_set w U v < \<infinity>"
  obtains es u where "u \<in> U" "sub.is_shortest_path w es u v" "sub.distance w u v = sub.distance_set w U v"
proof -
  have "U \<noteq> {}" using assms(2) by (auto simp: sub.distance_set_def top_ereal_def)
  then have "sub.distance_set w U v \<in> (\<lambda>u. sub.distance w u v) ` U"
    unfolding sub.distance_set_def by (rule finite_INF_in[OF assms(1)])
  then obtain u where u: "u \<in> U" "sub.distance w u v = sub.distance_set w U v" by auto
  have "finite (sub.spaths_bet u v)"
    by (rule finite_subset[OF _ finite_spaths_bet[of u v]]) (auto simp: sub.spaths_bet_def spaths_bet_def sub_path_bet)
  moreover have "sub.spaths_bet u v \<noteq> {}" using u(2) assms(2) by (auto simp: sub.distance_def top_ereal_def)
  ultimately have "sub.distance w u v \<in> (\<lambda>es. ereal (weight w es)) ` sub.spaths_bet u v"
    unfolding sub.distance_def by (rule finite_INF_in)
  then obtain es where "es \<in> sub.spaths_bet u v" "sub.distance w u v = ereal (weight w es)" by auto
  then show ?thesis using u that by (auto simp: sub.is_shortest_path_def sub.spaths_bet_def)
qed

text \<open>A simple path from a source \<open>s \<in> U\<close> whose weight is the distance from \<open>U\<close> is a shortest
      path from \<open>s\<close>. A path no heavier than the distance from \<open>U\<close> to every vertex of \<open>T\<close> is no
      heavier than any simple path from \<open>U\<close> to \<open>T\<close>.\<close>

lemma sub_distance_set_path_shortest:
  assumes "s \<in> U" "sub.path_bet p s v" "distinct p" "ereal (weight w p) = sub.distance_set w U v"
  shows "ereal (weight w p) = sub.distance w s v"
proof (rule order_antisym)
  show "ereal (weight w p) \<le> sub.distance w s v"
    unfolding assms(4) sub.distance_set_def by (rule INF_lower[OF assms(1)])
  show "sub.distance w s v \<le> ereal (weight w p)"
    using assms(2,3) unfolding sub.distance_def sub.spaths_bet_def by (auto intro: INF_lower)
qed

lemma sub_distance_set_path_le_targets:
  assumes "\<forall>x \<in> T. ereal (weight w p) \<le> sub.distance_set w U x"
    "s \<in> U" "x \<in> T" "sub.path_bet q s x" "distinct q"
  shows "weight w p \<le> weight w q"
  using order_trans[OF bspec[OF assms(1,3)] sub_distance_set_le_path[OF assms(2,4,5)]] by simp

end

end

end