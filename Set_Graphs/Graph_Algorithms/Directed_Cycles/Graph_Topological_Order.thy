theory Graph_Topological_Order
  imports Directed_Set_Graphs.Awalk
begin

section \<open>Topological numbering of a directed graph\<close>

text \<open>A directed graph in the Isabelle-Graph-Library is a set of arcs
  \<^typ>\<open>'a dgraph\<close> \<open>= ('a \<times> 'a) set\<close>; an edge \<open>(u, v)\<close> reads \<open>u \<rightarrow> v\<close>.
  A \<^emph>\<open>topological numbering\<close> assigns each vertex a natural number that strictly
  increases along every edge. The main result: for a finite graph a topological
  numbering exists iff the graph has no \<^const>\<open>cycle\<close> (equivalently, iff it is
  \<^const>\<open>acyclic\<close>). Beyond its intrinsic interest this is the usual way to \<^emph>\<open>certify\<close>
  acyclicity: a numbering supplied by an untrusted source is checked in one pass over the
  arcs, so a checker never has to search for cycles itself.\<close>

definition top_num :: "'a dgraph \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> bool" where
  "top_num E \<tau> \<longleftrightarrow> (\<forall>(u, v) \<in> E. \<tau> u < \<tau> v)"

definition has_top_num :: "'a dgraph \<Rightarrow> bool" where
  "has_top_num E \<longleftrightarrow> (\<exists>\<tau>. top_num E \<tau>)"

lemma top_numI:
  assumes "\<And>u v. (u, v) \<in> E \<Longrightarrow> \<tau> u < \<tau> v"
  shows "top_num E \<tau>"
  using assms by (auto simp: top_num_def)

lemma top_numD:
  assumes "top_num E \<tau>" and "(u, v) \<in> E"
  shows "\<tau> u < \<tau> v"
  using assms by (auto simp: top_num_def)

subsection \<open>A topological numbering implies acyclicity\<close>

lemma top_num_trancl:
  assumes "top_num E \<tau>" and "(u, v) \<in> E\<^sup>+"
  shows "\<tau> u < \<tau> v"
  using assms(2) by (induction rule: trancl_induct) (auto dest: top_numD[OF assms(1)])

lemma top_num_imp_acyclic:
  assumes "top_num E \<tau>"
  shows "acyclic E"
  unfolding acyclic_def
proof (intro allI notI)
  fix x assume "(x, x) \<in> E\<^sup>+"
  from top_num_trancl[OF assms this] show False by simp
qed

subsection \<open>A finite acyclic graph has a topological numbering\<close>

text \<open>Witness: rank each vertex by the number of its strict predecessors in \<open>E\<^sup>+\<close>.
  Along an edge \<open>(u, v)\<close> the predecessor set strictly grows (it gains \<open>u\<close>, which
  acyclicity keeps out of \<open>u\<close>'s own predecessors), so the cardinality strictly
  increases.\<close>

lemma trancl_src_in_dVs:
  assumes "(u, v) \<in> E\<^sup>+"
  shows "u \<in> dVs E"
  using assms by (metis dVsI(1) tranclD)

lemma finite_preds:
  assumes "finite E"
  shows "finite {u. (u, x) \<in> E\<^sup>+}"
proof -
  have "{u. (u, x) \<in> E\<^sup>+} \<subseteq> dVs E"
    by (auto intro: trancl_src_in_dVs)
  thus ?thesis
    using assms finite_vertices_iff finite_subset by blast
qed

lemma finite_acyclic_imp_has_top_num:
  assumes "finite E" and "acyclic E"
  shows "has_top_num E"
proof -
  define \<tau> :: "'a \<Rightarrow> nat" where "\<tau> x = card {u. (u, x) \<in> E\<^sup>+}" for x
  have "\<tau> u < \<tau> v" if e: "(u, v) \<in> E" for u v
  proof -
    have uv: "(u, v) \<in> E\<^sup>+" using e by (rule r_into_trancl)
    have sub: "{w. (w, u) \<in> E\<^sup>+} \<subseteq> {w. (w, v) \<in> E\<^sup>+}"
    proof (rule subsetI)
      fix w assume "w \<in> {w. (w, u) \<in> E\<^sup>+}"
      hence "(w, u) \<in> E\<^sup>+" by simp
      hence "(w, v) \<in> E\<^sup>+" using uv by (rule trancl_trans)
      thus "w \<in> {w. (w, v) \<in> E\<^sup>+}" by simp
    qed
    have "u \<in> {w. (w, v) \<in> E\<^sup>+}" using uv by simp
    moreover have "u \<notin> {w. (w, u) \<in> E\<^sup>+}"
      using \<open>acyclic E\<close> by (auto simp: acyclic_def)
    ultimately have psub: "{w. (w, u) \<in> E\<^sup>+} \<subset> {w. (w, v) \<in> E\<^sup>+}"
      using sub by blast
    have "card {w. (w, u) \<in> E\<^sup>+} < card {w. (w, v) \<in> E\<^sup>+}"
      using psubset_card_mono[OF finite_preds[OF \<open>finite E\<close>] psub] .
    thus ?thesis unfolding \<tau>_def .
  qed
  hence "top_num E \<tau>" by (rule top_numI)
  thus ?thesis unfolding has_top_num_def by blast
qed

subsection \<open>Relation to the library \<^const>\<open>cycle\<close> predicate\<close>

text \<open>We use the genuine directed \<^const>\<open>cycle\<close> (a non-empty closed \<^const>\<open>awalk\<close> with
  distinct interior vertices), \<^emph>\<open>not\<close> \<^const>\<open>cycle'\<close> (which adds \<open>length > 2\<close> for the
  undirected reading). A cycle witnesses a non-trivial closed walk, hence \<open>x \<rightarrow>\<^sup>+ x\<close>.\<close>

lemma cycle_imp_trancl_loop:
  assumes "cycle E p"
  shows "\<exists>x. (x, x) \<in> E\<^sup>+"
proof -
  from assms obtain u where "awalk E u p u" and "p \<noteq> []"
    by (auto simp: cycle_def)
  have ex: "\<exists>q. awalk E u q u \<and> q \<noteq> []"
    using \<open>awalk E u p u\<close> \<open>p \<noteq> []\<close> by blast
  have "(u, u) \<in> E\<^sup>+"
    using reachable1_awalk[THEN iffD2, OF ex] .
  thus ?thesis by auto
qed

lemma cycle_imp_not_acyclic:
  assumes "cycle E p"
  shows "\<not> acyclic E"
  using cycle_imp_trancl_loop[OF assms] by (auto simp: acyclic_def)

text \<open>The converse: a graph with a non-trivial closed walk has a proper cycle. Proof by strong
  induction on the walk length --- if the closed walk's interior vertices are already distinct it is
  itself a cycle; otherwise peel the first arc to get a strictly shorter \<^emph>\<open>open\<close> walk that still has
  a repeated vertex, extract a closed sub-walk from it (\<open>awalk_not_distinct_decomp\<close>), and
  recurse.\<close>

lemma closed_walk_imp_cycle:
  assumes "awalk E u p u" and "p \<noteq> []"
  shows "\<exists>c. cycle E c"
  using assms
proof (induction "length p" arbitrary: u p rule: less_induct)
  case less
  show ?case
  proof (cases "distinct (tl (awalk_verts u p))")
    case True
    have "cycle E p" using less.prems True unfolding cycle_def by blast
    thus ?thesis by blast
  next
    case False
    obtain u1 p' where p_eq: "p = (u, u1) # p'"
      using less.prems by (cases p) (auto simp: awalk_Cons_iff)
    have aw': "awalk E u1 p' u"
      using less.prems(1) unfolding p_eq by (simp add: awalk_Cons_iff)
    have "awalk_verts u p = u # awalk_verts u1 p'" unfolding p_eq by simp
    hence nd': "\<not> distinct (awalk_verts u1 p')" using False by simp
    obtain q r s w
      where dec: "p' = q @ r @ s"
        and "distinct (awalk_verts u1 q)"
        and lr: "0 < length r"
        and "awalk E u1 q w"
        and aw_r: "awalk E w r w"
        and "awalk E w s u"
      by (rule awalk_not_distinct_decomp[OF aw' nd'])
    have rne: "r \<noteq> []" using lr by auto
    have "length r < length p" using dec p_eq by simp
    thus ?thesis using less.hyps aw_r rne by blast
  qed
qed

lemma not_acyclic_imp_cycle:
  assumes "\<not> acyclic E"
  shows "\<exists>p. cycle E p"
proof -
  obtain x where "(x, x) \<in> E\<^sup>+" using assms by (auto simp: acyclic_def)
  hence "\<exists>q. awalk E x q x \<and> q \<noteq> []" by (meson reachable1_awalk)
  then obtain q where q: "awalk E x q x" and qne: "q \<noteq> []" by blast
  show ?thesis using closed_walk_imp_cycle[OF q qne] .
qed

lemma no_cycle_iff_acyclic:
  "(\<nexists>p. cycle E p) \<longleftrightarrow> acyclic E"
proof
  assume "\<nexists>p. cycle E p"
  thus "acyclic E" using not_acyclic_imp_cycle by blast
next
  assume "acyclic E"
  show "\<nexists>p. cycle E p"
    using cycle_imp_not_acyclic \<open>acyclic E\<close> by blast
qed

subsection \<open>Main equivalence\<close>

theorem acyclic_iff_has_top_num:
  assumes "finite E"
  shows "acyclic E \<longleftrightarrow> has_top_num E"
proof
  assume "acyclic E"
  thus "has_top_num E" using finite_acyclic_imp_has_top_num[OF assms] by blast
next
  assume "has_top_num E"
  thus "acyclic E" using top_num_imp_acyclic by (auto simp: has_top_num_def)
qed

corollary no_cycle_iff_has_top_num:
  assumes "finite E"
  shows "(\<nexists>p. cycle E p) \<longleftrightarrow> has_top_num E"
  using acyclic_iff_has_top_num[OF assms] no_cycle_iff_acyclic by blast

end
