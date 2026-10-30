theory Multigraph_Weighted_Paths
  imports Directed_Set_Graphs.Multigraph
begin

provenance ai


section \<open>Weighted Paths and Distances in a Multigraph\<close>

text \<open>This theory develops, for a directed multigraph presented \<^emph>\<open>via\<close> the @{locale
      multigraph} locale, the theory of \<^emph>\<open>real-weighted\<close> path lengths and the induced distances.
      It mirrors, for real edge weights, the development of unweighted vertex-walk distances in
      \<open>Dist.thy\<close>. Edge weights may be negative, so distances are taken over
      \<^emph>\<open>distinct\<close> (simple) edge paths and are valued in @{typ ereal} (finitely many simple paths
      in a finite graph, so an unreachable target has distance \<open>+\<infinity>\<close>).\<close>

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

text \<open>Because edge weights may be negative, a shortest walk need not exist over \<^emph>\<open>all\<close>
      paths (a negative cycle could be repeated). We therefore measure distance over \<^emph>\<open>distinct\<close>
      (simple) paths only. In a finite graph there are finitely many of these, so the infimum below is attained
      whenever the target is reachable, and equals @{term \<open>\<infinity>\<close>} otherwise. Distances live in
      @{typ ereal}.\<close>

definition spaths_bet :: "'a \<Rightarrow> 'a \<Rightarrow> 'edge list set" where
  "spaths_bet u v = {es. path_bet es u v \<and> distinct es}"

definition distance :: "('edge \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ereal" where
  "distance w u v = (INF es \<in> spaths_bet u v. ereal (weight w es))"

definition reachable :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "reachable u v \<longleftrightarrow> spaths_bet u v \<noteq> {}"

definition is_shortest_path ::
  "('edge \<Rightarrow> real) \<Rightarrow> 'edge list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
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
  by (auto simp: weight_def)

lemma weight_append[simp]: "weight w (es1 @ es2) = weight w es1 + weight w es2"
  by (auto simp: weight_def)

lemma weight_snoc: "weight w (es @ [e]) = weight w es + w e"
  and weight_single: "weight w [e] = w e"
  and weight_rev: "weight w (rev es) = weight w es"
  by (auto simp: weight_def rev_map[symmetric])


subsection \<open>Paths between two Vertices\<close>

lemma path_bet_Nil[simp]: "path_bet [] u v \<longleftrightarrow> u = v"
  by (auto simp: path_bet_def multigraph_path_intros)

lemma path_bet_Nil_iff: "path_bet [] u u"
  by simp

lemma path_bet_single: "e \<in> \<E> \<Longrightarrow> path_bet [e] (fst e) (snd e)"
  by (auto simp: path_bet_def multigraph_path_intros)

lemma path_bet_edges_subset: "path_bet es u v \<Longrightarrow> set es \<subseteq> \<E>"
  by (auto simp: path_bet_def)

lemma path_bet_hd: "\<lbrakk>path_bet es u v; es \<noteq> []\<rbrakk> \<Longrightarrow> fst (hd es) = u"
  by (auto simp: path_bet_def)

lemma path_bet_last: "\<lbrakk>path_bet es u v; es \<noteq> []\<rbrakk> \<Longrightarrow> snd (last es) = v"
  by (auto simp: path_bet_def)

lemma path_bet_multigraph_path: "path_bet es u v \<Longrightarrow> multigraph_path es"
  by (auto simp: path_bet_def)

text \<open>Composition of @{const multigraph_path}s and its consequences for @{const path_bet}.\<close>

lemma multigraph_path_Cons:
  "multigraph_path (e # es) \<longleftrightarrow> es = [] \<or> snd e = fst (hd es) \<and> multigraph_path es"
  by (auto simp: multigraph_path_intros elim: flowpath_cases)

lemma multigraph_path_tl: "multigraph_path (e # es) \<Longrightarrow> multigraph_path es"
  by (auto simp: multigraph_path_Cons multigraph_path_intros(1))

lemma multigraph_path_append:
  assumes "multigraph_path es1" "multigraph_path es2"
    "es1 = [] \<or> es2 = [] \<or> snd (last es1) = fst (hd es2)"
  shows "multigraph_path (es1 @ es2)"
  using assms
  by (induction es1) (auto simp: multigraph_path_Cons hd_append split: if_splits)

lemma multigraph_path_pref: "multigraph_path (es1 @ es2) \<Longrightarrow> multigraph_path es1"
  by (induction es1) (auto simp: multigraph_path_Cons multigraph_path_intros(1))

lemma multigraph_path_suff: "multigraph_path (es1 @ es2) \<Longrightarrow> multigraph_path es2"
  by (induction es1) (auto dest: multigraph_path_tl)

lemma multigraph_path_append_conn:
  "\<lbrakk>multigraph_path (es1 @ es2); es1 \<noteq> []; es2 \<noteq> []\<rbrakk>
    \<Longrightarrow> snd (last es1) = fst (hd es2)"
  by (induction es1) (auto simp: multigraph_path_Cons)

lemma path_bet_Cons:
  "path_bet (e # es) u w \<longleftrightarrow> e \<in> \<E> \<and> fst e = u \<and> path_bet es (snd e) w"
  by (cases es) (auto simp: path_bet_def multigraph_path_Cons multigraph_path_intros)

lemma path_bet_append_iff:
  "path_bet (es1 @ es2) u w \<longleftrightarrow> (\<exists>x. path_bet es1 u x \<and> path_bet es2 x w)"
  by (induction es1 arbitrary: u) (auto simp: path_bet_Cons)

lemma path_bet_append:
  assumes "path_bet es1 u v" "path_bet es2 v w"
  shows "path_bet (es1 @ es2) u w"
  using assms
  by (auto simp: path_bet_append_iff)

lemma path_bet_pref:
  "\<lbrakk>path_bet (es1 @ es2) u w; es1 \<noteq> []; es2 \<noteq> []\<rbrakk>
    \<Longrightarrow> path_bet es1 u (fst (hd es2))"
  by (auto simp: path_bet_append_iff dest: path_bet_hd)

lemma path_bet_suff:
  "\<lbrakk>path_bet (es1 @ es2) u w; es1 \<noteq> []; es2 \<noteq> []\<rbrakk>
    \<Longrightarrow> path_bet es2 (snd (last es1)) w"
  by (auto simp: path_bet_append_iff dest: path_bet_last)

lemma path_bet_fst_in_V: "\<lbrakk>path_bet es u v; es \<noteq> []\<rbrakk> \<Longrightarrow> u \<in> \<V>"
  by (cases es) (auto simp: path_bet_Cons intro: fst_E_V)

lemma path_bet_snd_in_V: "\<lbrakk>path_bet es u v; es \<noteq> []\<rbrakk> \<Longrightarrow> v \<in> \<V>"
  using last_in_set[of es]
  by (auto simp: path_bet_def intro!: snd_E_V)

lemma path_bet_verts_in_V:
  assumes "path_bet es u v" "e \<in> set es"
  shows "fst e \<in> \<V>" "snd e \<in> \<V>"
  using assms fst_E_V snd_E_V
  by (auto simp: path_bet_def)

lemma path_bet_ConsI:
  "\<lbrakk>e \<in> \<E>; path_bet es (snd e) w\<rbrakk> \<Longrightarrow> path_bet (e # es) (fst e) w"
  by (simp add: path_bet_Cons)

lemma path_bet_snocI:
  "\<lbrakk>path_bet es u (fst e); e \<in> \<E>\<rbrakk> \<Longrightarrow> path_bet (es @ [e]) u (snd e)"
  by (auto simp: path_bet_append_iff path_bet_Cons)

lemma path_bet_ConsE:
  assumes "path_bet (e # es) u w"
  obtains "e \<in> \<E>" "fst e = u" "path_bet es (snd e) w"
  using assms that
  by (simp add: path_bet_Cons)

lemma path_bet_appendE:
  assumes "path_bet (es1 @ es2) u w"
  obtains x where "path_bet es1 u x" "path_bet es2 x w"
  using assms that
  by (auto simp: path_bet_append_iff)

lemma path_bet_edge_split:
  assumes "path_bet es u w" "e \<in> set es"
  obtains es1 es2 where "es = es1 @ e # es2" "path_bet es1 u (fst e)" "path_bet es2 (snd e) w"
  using assms split_list[of e es] that
  by (fastforce simp: path_bet_append_iff path_bet_Cons)

text \<open>A path that repeats an edge \<open>x\<close> splits into a shorter path with the same endpoints and a
      closed path starting with \<open>x\<close>.\<close>

lemma path_bet_not_distinct:
  assumes "path_bet es u v" "\<not> distinct es"
  obtains x p1 p2 p3 where "es = p1 @ x # p2 @ x # p3" "path_bet (p1 @ x # p3) u v"
    "path_bet (x # p2) (fst x) (fst x)"
proof-
  obtain p1 x p2 p3 where "es = p1 @ x # p2 @ x # p3"
    using assms(2) not_distinct_decomp[of es]
    by auto
  thus ?thesis
    using assms(1) that
    by (auto simp: path_bet_append_iff path_bet_Cons)
qed


subsection \<open>Simple Paths, Distance and Reachability\<close>

lemma finite_spaths_bet: "finite (spaths_bet u v)"
  using finite_subset_distinct[of \<E>] finite_E
  by (auto simp: spaths_bet_def path_bet_def intro: rev_finite_subset)

lemma spaths_betI: "\<lbrakk>path_bet es u v; distinct es\<rbrakk> \<Longrightarrow> es \<in> spaths_bet u v"
  by (auto simp: spaths_bet_def)

lemma spaths_betD: "es \<in> spaths_bet u v \<Longrightarrow> path_bet es u v \<and> distinct es"
  by (auto simp: spaths_bet_def)


lemma spath_dist: "es \<in> spaths_bet u v \<Longrightarrow> distance w u v \<le> ereal (weight w es)"
  by (auto simp: distance_def intro: INF_lower)

lemma path_bet_dist:
  "\<lbrakk>path_bet es u v; distinct es\<rbrakk> \<Longrightarrow> distance w u v \<le> ereal (weight w es)"
  by (auto simp: spath_dist spaths_betI)

lemma unreachable_dist: "\<not> reachable u v \<Longrightarrow> distance w u v = \<infinity>"
  by (auto simp: distance_def reachable_def top_ereal_def)

lemma reachable_dist: "reachable u v \<Longrightarrow> distance w u v < \<infinity>"
  by (auto simp: reachable_def dest!: spath_dist[of _ u v w] order_le_less_trans[rotated])

lemma dist_reachable: "distance w u v < \<infinity> \<Longrightarrow> reachable u v"
  using unreachable_dist
  by force

text \<open>In a finite graph the infimum is attained: a reachable target has an actual shortest simple
      path realising its distance.\<close>

lemma reachable_dist_2:
  assumes "reachable u v"
  obtains es where "path_bet es u v" "distinct es" "distance w u v = ereal (weight w es)"
  using assms finite_INF_in[of "spaths_bet u v" "\<lambda>es. ereal (weight w es)"] finite_spaths_bet that
  by (auto simp: distance_def reachable_def spaths_bet_def)

text \<open>Every path contains a simple path with the same endpoints; hence reachability is witnessed by simple
      paths and is transitive, even though shortest \<^emph>\<open>distinct\<close> paths need not concatenate to a
      distinct path.\<close>

lemma path_bet_imp_spath:
  "path_bet es u v
    \<Longrightarrow> \<exists>es'. path_bet es' u v \<and> distinct es' \<and> set es' \<subseteq> set es"
proof(induction "length es" arbitrary: es rule: less_induct)
  case less
  show ?case
  proof(cases "distinct es")
    case False
    obtain x p1 p2 p3 where "es = p1 @ x # p2 @ x # p3" "path_bet (p1 @ x # p3) u v"
      "path_bet (x # p2) (fst x) (fst x)"
      using less.prems False
      by (blast elim: path_bet_not_distinct)
    thus ?thesis
      using less.hyps[of "p1 @ x # p3"]
      by fastforce
  qed (use less.prems in blast)
qed

lemma reachable_iff_path: "reachable u v \<longleftrightarrow> (\<exists>es. path_bet es u v)"
  by (auto simp: reachable_def spaths_bet_def dest: path_bet_imp_spath)

lemma reachableI: "path_bet es u v \<Longrightarrow> reachable u v"
  using reachable_iff_path
  by blast

lemma reachable_refl: "reachable u u"
  by (auto simp: reachable_iff_path intro!: exI[of _ "[]"])

lemma reachable_edge: "e \<in> \<E> \<Longrightarrow> reachable (fst e) (snd e)"
  using path_bet_single
  by (auto simp: reachable_iff_path)

lemma reachable_trans: "\<lbrakk>reachable u v; reachable v w\<rbrakk> \<Longrightarrow> reachable u w"
  unfolding reachable_iff_path
  by (blast intro: path_bet_append)

lemma distance_self_le0: "distance w u u \<le> 0"
  using path_bet_dist[of "[]" u u w]
  by (simp add: zero_ereal_def)


subsection \<open>Shortest Paths\<close>

lemma is_shortest_pathI:
  "\<lbrakk>path_bet es u v; distinct es; distance w u v = ereal (weight w es)\<rbrakk>
    \<Longrightarrow> is_shortest_path w es u v"
  by (auto simp: is_shortest_path_def)

lemma is_shortest_path_path_bet: "is_shortest_path w es u v \<Longrightarrow> path_bet es u v"
  and is_shortest_path_distinct: "is_shortest_path w es u v \<Longrightarrow> distinct es"
  and is_shortest_path_dist: "is_shortest_path w es u v \<Longrightarrow> distance w u v = ereal (weight w es)"
  by (auto simp: is_shortest_path_def)

lemma is_shortest_path_exists:
  assumes "reachable u v"
  obtains es where "is_shortest_path w es u v"
  using reachable_dist_2[OF assms]
  by (auto simp: is_shortest_path_def)

lemma is_shortest_path_exists_2:
  assumes "distance w u v < \<infinity>"
  obtains es where "is_shortest_path w es u v"
  using dist_reachable[OF assms]
  by (auto elim: is_shortest_path_exists)

text \<open>The triangle inequality holds along any two paths that together form a \<^emph>\<open>distinct\<close>
      (simple) path; unlike the unweighted case, distinctness of the concatenation is essential, since a negative
      cycle could otherwise be inserted.\<close>

lemma triangle_ineq_path:
  assumes "path_bet es1 u v" "path_bet es2 v w" "distinct (es1 @ es2)"
  shows "distance wt u w \<le> ereal (weight wt es1) + ereal (weight wt es2)"
  using assms path_bet_append[of es1 u v es2 w] path_bet_dist[of "es1 @ es2" u w wt]
  by simp

lemma triangle_ineq_distinct:
  assumes "is_shortest_path wt es1 u v" "is_shortest_path wt es2 v w" "distinct (es1 @ es2)"
  shows "distance wt u w \<le> distance wt u v + distance wt v w"
  using assms triangle_ineq_path[of es1 u v es2 w wt]
  by (simp add: is_shortest_path_def)


subsection \<open>Distance from a Set of Vertices\<close>

lemma dist_set_mem: "u \<in> U \<Longrightarrow> distance_set w U v \<le> distance w u v"
  by (auto simp: distance_set_def intro: INF_lower)

lemma distance_set_union: "distance_set w (U \<union> V) v \<le> distance_set w U v"
  by (auto simp: distance_set_def intro: INF_superset_mono)

lemma distance_set_mono: "U \<subseteq> V \<Longrightarrow> distance_set w V v \<le> distance_set w U v"
  by (auto simp: distance_set_def intro: INF_superset_mono)

lemma distance_set_single_source: "distance_set w {s} v = distance w s v"
  by (auto simp: distance_set_def)

lemma distance_set_empty: "distance_set w {} v = \<infinity>"
  by (auto simp: distance_set_def top_ereal_def)

lemma distance_set_le_path:
  "\<lbrakk>u \<in> U; path_bet es u v; distinct es\<rbrakk>
    \<Longrightarrow> distance_set w U v \<le> ereal (weight w es)"
  using dist_set_mem[of u U w v] path_bet_dist[of es u v w]
  by simp

lemma distance_set_infty_iff:
  "distance_set w U v = \<infinity> \<longleftrightarrow> (\<forall>u\<in>U. \<not> reachable u v)"
  unfolding distance_set_def distance_def reachable_def top_ereal_def[symmetric] INF_top_conv
  by (auto simp: top_ereal_def)

text \<open>For a finite source set the infimum is attained by an actual source and shortest simple path.\<close>

lemma distance_set_wit:
  assumes "finite U" "U \<noteq> {}"
  obtains u where "u \<in> U" "distance_set w U v = distance w u v"
  using assms finite_INF_in[of U "\<lambda>u. distance w u v"] that
  by (auto simp: distance_set_def)

lemma distance_set_reachable:
  assumes "finite U" "distance_set w U v < \<infinity>"
  obtains u where "u \<in> U" "reachable u v" "distance w u v = distance_set w U v"
proof-
  obtain u where "u \<in> U" "distance_set w U v = distance w u v"
    using assms distance_set_empty[of w v]
    by (cases "U = {}") (auto elim: distance_set_wit)
  thus ?thesis
    using assms(2) dist_reachable that
    by auto
qed

lemma dist_set_less_infty_get_path:
  assumes "finite U" "distance_set w U v < \<infinity>"
  obtains es u where "u \<in> U" "is_shortest_path w es u v" "distance w u v = distance_set w U v"
  using assms that
  by (auto elim: distance_set_reachable is_shortest_path_exists)

subsection \<open>Subgraphs\<close>

context
  fixes E' assumes sub: "E' \<subseteq> \<E>"
begin

interpretation sub: multigraph_spec E' fst snd create_edge .

lemma sub_path_bet: "sub.path_bet es u v \<longleftrightarrow> path_bet es u v \<and> set es \<subseteq> E'"
  using sub
  by (auto simp: sub.path_bet_def path_bet_def)

lemma sub_path_bet_ConsE:
  assumes "sub.path_bet (e # es) u w"
  obtains "e \<in> E'" "fst e = u" "sub.path_bet es (snd e) w"
  using assms
  by (auto simp: sub_path_bet elim: path_bet_ConsE)

lemma sub_path_bet_snocI:
  "\<lbrakk>sub.path_bet es u (fst e); e \<in> E'\<rbrakk> \<Longrightarrow> sub.path_bet (es @ [e]) u (snd e)"
  using sub
  by (auto simp: sub_path_bet intro: path_bet_snocI)

lemma sub_path_bet_edge_split:
  assumes "sub.path_bet es u w" "e \<in> set es"
  obtains es1 es2 where "es = es1 @ e # es2" "sub.path_bet es1 u (fst e)" "sub.path_bet es2 (snd e) w"
  by (rule path_bet_edge_split[of es u w e]) (use assms that in \<open>auto simp: sub_path_bet\<close>)+

lemma sub_reachable_iff_path: "sub.reachable u v \<longleftrightarrow> (\<exists>es. sub.path_bet es u v)"
proof
  assume "\<exists>es. sub.path_bet es u v"
  then obtain es where "path_bet es u v" "set es \<subseteq> E'"
    by (auto simp: sub_path_bet)
  thus "sub.reachable u v"
    using path_bet_imp_spath[of es u v]
    by (auto simp: sub.reachable_def sub.spaths_bet_def sub_path_bet)
qed (auto simp: sub.reachable_def sub.spaths_bet_def)

lemma sub_distance_set_le_path:
  "\<lbrakk>u \<in> U; sub.path_bet es u v; distinct es\<rbrakk>
    \<Longrightarrow> sub.distance_set w U v \<le> ereal (weight w es)"
  unfolding sub.distance_set_def sub.distance_def sub.spaths_bet_def
  by (rule INF_lower2[of u]) (auto intro: INF_lower)

lemma sub_distance_set_infty_iff:
  "sub.distance_set w U v = \<infinity> \<longleftrightarrow> (\<forall>u\<in>U. \<not> sub.reachable u v)"
  unfolding sub.distance_set_def sub.distance_def sub.reachable_def top_ereal_def[symmetric] INF_top_conv
  by (auto simp: top_ereal_def)

lemma sub_dist_set_less_infty_get_path:
  assumes "finite U" "sub.distance_set w U v < \<infinity>"
  obtains es u where "u \<in> U" "sub.is_shortest_path w es u v" "sub.distance w u v = sub.distance_set w U v"
proof-
  have "U \<noteq> {}"
    using assms(2)
    by (auto simp: sub.distance_set_def top_ereal_def)
  then have "sub.distance_set w U v \<in> (\<lambda>u. sub.distance w u v) ` U"
    unfolding sub.distance_set_def
    by (rule finite_INF_in[OF assms(1)])
  then obtain u where u: "u \<in> U" "sub.distance w u v = sub.distance_set w U v"
    by auto
  have "finite (sub.spaths_bet u v)"
    by (rule finite_subset[OF _ finite_spaths_bet[of u v]]) (auto simp: sub.spaths_bet_def spaths_bet_def sub_path_bet)
  moreover have "sub.spaths_bet u v \<noteq> {}"
    using u(2) assms(2)
    by (auto simp: sub.distance_def top_ereal_def)
  ultimately have "sub.distance w u v \<in> (\<lambda>es. ereal (weight w es)) ` sub.spaths_bet u v"
    unfolding sub.distance_def
    by (rule finite_INF_in)
  then obtain es where "es \<in> sub.spaths_bet u v" "sub.distance w u v = ereal (weight w es)"
    by auto
  then show ?thesis
    using u that
    by (auto simp: sub.is_shortest_path_def sub.spaths_bet_def)
qed

text \<open>A simple path from a source \<open>s \<in> U\<close> whose weight is the distance from \<open>U\<close>
      is a shortest path from \<open>s\<close>. A path no heavier than the distance from \<open>U\<close> to every
      vertex of \<open>T\<close> is no heavier than any simple path from \<open>U\<close> to
      \<open>T\<close>.\<close>

lemma sub_distance_set_path_shortest:
  assumes "s \<in> U" "sub.path_bet p s v" "distinct p" "ereal (weight w p) = sub.distance_set w U v"
  shows "ereal (weight w p) = sub.distance w s v"
proof(rule order_antisym)
  show "ereal (weight w p) \<le> sub.distance w s v"
    unfolding assms(4) sub.distance_set_def
    using assms(1)
    by (auto intro: INF_lower)
  show "sub.distance w s v \<le> ereal (weight w p)"
    using assms(2,3)
    unfolding sub.distance_def sub.spaths_bet_def
    by (auto intro: INF_lower)
qed

lemma sub_distance_set_path_le_targets:
  assumes "\<forall>x \<in> T. ereal (weight w p) \<le> sub.distance_set w U x"
    "s \<in> U" "x \<in> T" "sub.path_bet q s x" "distinct q"
  shows "weight w p \<le> weight w q"
  using assms sub_distance_set_le_path[of s U q x w]
  by (fastforce dest: order_trans)

end

end

end