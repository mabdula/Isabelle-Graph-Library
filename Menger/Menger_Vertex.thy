theory Menger_Vertex
  imports
    Menger_Edge
begin

section \<open>Linkages and Menger's Theorem\<close>

text \<open>Let \<open>G\<close> be a directed graph and \<open>S\<close> a set of source vertices. A set of vertices \<open>T\<close> is
linked from \<open>S\<close> if there is a family of pairwise vertex-disjoint paths, one for every \<open>t \<in> T\<close>,
each starting in \<open>S\<close> and ending in \<open>t\<close>. As in the rest of the library, there are no isolated
vertices: the vertices of \<open>G\<close> are \<open>dVs G\<close>, and the trivial path \<open>[t]\<close> is a path iff
\<open>t \<in> dVs G\<close>.\<close>

definition linkage :: "'a dgraph \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a list) \<Rightarrow> bool" where
  "linkage G S T p =
    ((\<forall>t \<in> T. hd (p t) \<in> S \<and> distinct_vwalk_bet G (hd (p t)) (p t) t) \<and>
     (\<forall>t1 \<in> T. \<forall>t2 \<in> T. t1 \<noteq> t2 \<longrightarrow> set (p t1) \<inter> set (p t2) = {}))"

lemma linkageE:
  "linkage G S T p \<Longrightarrow>
    (\<lbrakk>\<And>t. t \<in> T \<Longrightarrow> hd (p t) \<in> S;
      \<And>t. t \<in> T \<Longrightarrow> distinct_vwalk_bet G (hd (p t)) (p t) t;
      \<And>t1 t2. \<lbrakk>t1 \<in> T; t2 \<in> T; t1 \<noteq> t2\<rbrakk> \<Longrightarrow> set (p t1) \<inter> set (p t2) = {}\<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
    P"
and linkageI:
  "\<lbrakk>\<And>t. t \<in> T \<Longrightarrow> hd (p t) \<in> S;
    \<And>t. t \<in> T \<Longrightarrow> distinct_vwalk_bet G (hd (p t)) (p t) t;
    \<And>t1 t2. \<lbrakk>t1 \<in> T; t2 \<in> T; t1 \<noteq> t2\<rbrakk> \<Longrightarrow> set (p t1) \<inter> set (p t2) = {}\<rbrakk> \<Longrightarrow>
    linkage G S T p"
and linkageD:
  "\<lbrakk>linkage G S T p; t \<in> T\<rbrakk> \<Longrightarrow> hd (p t) \<in> S"
  "\<lbrakk>linkage G S T p; t \<in> T\<rbrakk> \<Longrightarrow> distinct_vwalk_bet G (hd (p t)) (p t) t"
  "\<lbrakk>linkage G S T p; t1 \<in> T; t2 \<in> T; t1 \<noteq> t2\<rbrakk> \<Longrightarrow> set (p t1) \<inter> set (p t2) = {}"
  by (auto simp: linkage_def)

definition linked :: "'a dgraph \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "linked G S T = (\<exists>p. linkage G S T p)"

lemma linkedE:
  "linked G S T \<Longrightarrow> (\<And>p. linkage G S T p \<Longrightarrow> P) \<Longrightarrow> P"
and linkedI:
  "linkage G S T p \<Longrightarrow> linked G S T"
  by (auto simp: linked_def)

lemma linkage_empty: "linkage G S {} p"
  by (auto intro: linkageI)

lemma linkage_subset: "\<lbrakk>linkage G S T p; T' \<subseteq> T\<rbrakk> \<Longrightarrow> linkage G S T' p"
  by (rule linkageI) (auto dest: linkageD)

lemma linkage_in_dVs: "linkage G S T p \<Longrightarrow> T \<subseteq> dVs G"
proof
  fix t
  assume "linkage G S T p" "t \<in> T"
  then have "vwalk_bet G (hd (p t)) (p t) t"
    by (auto elim: distinct_vwalk_betE dest: linkageD(2))
  then show "t \<in> dVs G"
    by (rule vwalk_bet_endpoints(2))
qed

lemma linked_empty: "linked G S {}"
  using linkage_empty by (rule linkedI)

lemma linked_subset: "\<lbrakk>linked G S T; T' \<subseteq> T\<rbrakk> \<Longrightarrow> linked G S T'"
  by (auto elim!: linkedE intro: linkedI dest: linkage_subset)

lemma linked_in_dVs: "linked G S T \<Longrightarrow> T \<subseteq> dVs G"
  by (auto elim!: linkedE dest: linkage_in_dVs)

text \<open>A set of vertices \<open>X\<close> separates \<open>A\<close> from \<open>B\<close> if every path from \<open>A\<close> to \<open>B\<close> meets \<open>X\<close>.
This includes the trivial paths, i.e.\ \<open>A \<inter> B \<inter> dVs G \<subseteq> X\<close>.\<close>

definition separator :: "'a dgraph \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "separator G A B X = (\<forall>u p v. u \<in> A \<longrightarrow> v \<in> B \<longrightarrow> vwalk_bet G u p v \<longrightarrow> set p \<inter> X \<noteq> {})"

lemma separatorE:
  "separator G A B X \<Longrightarrow>
    ((\<And>u p v. \<lbrakk>u \<in> A; v \<in> B; vwalk_bet G u p v\<rbrakk> \<Longrightarrow> set p \<inter> X \<noteq> {}) \<Longrightarrow> P) \<Longrightarrow> P"
and separatorI:
  "(\<And>u p v. \<lbrakk>u \<in> A; v \<in> B; vwalk_bet G u p v\<rbrakk> \<Longrightarrow> set p \<inter> X \<noteq> {}) \<Longrightarrow> separator G A B X"
and separatorD:
  "\<lbrakk>separator G A B X; u \<in> A; v \<in> B; vwalk_bet G u p v\<rbrakk> \<Longrightarrow> set p \<inter> X \<noteq> {}"
  by (auto simp: separator_def)

text \<open>The easy direction of Menger's Theorem: no linkage is larger than a separator.\<close>

lemma linkage_card_le_separator:
  assumes link: "linkage G A T p" and sep: "separator G A B X" and TB: "T \<subseteq> B" and fin: "finite X"
  shows "card T \<le> card X"
proof -
  have "\<forall>t \<in> T. \<exists>x. x \<in> set (p t) \<inter> X"
  proof
    fix t
    assume t: "t \<in> T"
    have "vwalk_bet G (hd (p t)) (p t) t"
      using linkageD(2)[OF link t] by (rule distinct_vwalk_betD(1))
    then have "set (p t) \<inter> X \<noteq> {}"
      by (rule separatorD[OF sep linkageD(1)[OF link t] subsetD[OF TB t]])
    then show "\<exists>x. x \<in> set (p t) \<inter> X"
      by blast
  qed
  from bchoice[OF this] obtain g where g: "\<forall>t \<in> T. g t \<in> set (p t) \<inter> X" ..
  have "inj_on g T"
  proof (rule inj_onI, rule ccontr)
    fix t1 t2
    assume t: "t1 \<in> T" "t2 \<in> T" "g t1 = g t2" "t1 \<noteq> t2"
    then have "g t1 \<in> set (p t1) \<inter> set (p t2)"
      using g by auto
    then show False
      using linkageD(3)[OF link t(1,2,4)] by blast
  qed
  then show ?thesis
    by (rule card_inj_on_le) (use g fin in auto)
qed

text \<open>A family of pairwise vertex-disjoint paths gives a linkage onto the set of their end
vertices, which has as many elements as there are paths.\<close>

lemma linkage_of_paths:
  assumes paths: "\<And>q. q \<in> Q \<Longrightarrow> hd q \<in> A \<and> distinct_vwalk_bet G (hd q) q (last q)"
    and disj: "\<And>q1 q2. \<lbrakk>q1 \<in> Q; q2 \<in> Q; q1 \<noteq> q2\<rbrakk> \<Longrightarrow> set q1 \<inter> set q2 = {}"
  shows "linkage G A (last ` Q) (\<lambda>t. SOME q. q \<in> Q \<and> last q = t)"
    and "inj_on last Q"
proof -
  let ?p = "\<lambda>t. SOME q. q \<in> Q \<and> last q = t"
  have p: "?p t \<in> Q \<and> last (?p t) = t" if "t \<in> last ` Q" for t
    by (rule someI_ex) (use that in blast)
  have pA: "hd (?p t) \<in> A \<and> distinct_vwalk_bet G (hd (?p t)) (?p t) t" if "t \<in> last ` Q" for t
  proof -
    from p[OF that] have q: "?p t \<in> Q" and l: "last (?p t) = t"
      by auto
    from paths[OF q] show ?thesis
      unfolding l .
  qed
  show "linkage G A (last ` Q) ?p"
  proof (rule linkageI)
    fix t
    assume "t \<in> last ` Q"
    with pA show "hd (?p t) \<in> A"
      by blast
  next
    fix t
    assume "t \<in> last ` Q"
    with pA show "distinct_vwalk_bet G (hd (?p t)) (?p t) t"
      by blast
  next
    fix t1 t2
    assume t: "t1 \<in> last ` Q" "t2 \<in> last ` Q" "t1 \<noteq> t2"
    then have "?p t1 \<noteq> ?p t2"
      using p[OF t(1)] p[OF t(2)] by auto
    then show "set (?p t1) \<inter> set (?p t2) = {}"
      using p[OF t(1)] p[OF t(2)] disj by blast
  qed
  show "inj_on last Q"
  proof (rule inj_onI, rule ccontr)
    fix q1 q2
    assume q: "q1 \<in> Q" "q2 \<in> Q" "last q1 = last q2" "q1 \<noteq> q2"
    have "q1 \<noteq> []" "q2 \<noteq> []"
      using paths[OF q(1)] paths[OF q(2)] by (auto simp: distinct_vwalk_bet_def vwalk_bet_def)
    then have "last q1 \<in> set q1 \<inter> set q2"
      using last_in_set[of q1] last_in_set[of q2] q(3) by simp
    then show False
      using disj[OF q(1,2,4)] by simp
  qed
qed

subsection \<open>Splitting Vertices\<close>

text \<open>Every vertex \<open>v\<close> is split into an entry \<open>Vin v\<close> and an exit \<open>Vout v\<close>, connected by an edge.
An edge \<open>(u, v)\<close> becomes an edge from \<open>Vout u\<close> to \<open>Vin v\<close>. Edge-disjoint paths in the split graph
are vertex-disjoint in the original one.\<close>

datatype 'a snode = Vin 'a | Vout 'a

fun unsplit_node :: "'a snode \<Rightarrow> 'a" where
  "unsplit_node (Vin v) = v"
| "unsplit_node (Vout v) = v"

definition split_graph :: "'a dgraph \<Rightarrow> 'a snode dgraph" where
  "split_graph G = (\<lambda>v. (Vin v, Vout v)) ` dVs G \<union> (\<lambda>e. (Vout (fst e), Vin (snd e))) ` G"

fun split_walk :: "'a list \<Rightarrow> 'a snode list" where
  "split_walk [] = []"
| "split_walk (v # p) = Vin v # Vout v # split_walk p"

fun unsplit_walk :: "'a snode list \<Rightarrow> 'a list" where
  "unsplit_walk [] = []"
| "unsplit_walk (Vin v # p) = v # unsplit_walk p"
| "unsplit_walk (Vout v # p) = unsplit_walk p"

lemma split_graph_edge_iff:
  "(Vin u, x) \<in> split_graph G \<longleftrightarrow> x = Vout u \<and> u \<in> dVs G"
  "(Vout u, x) \<in> split_graph G \<longleftrightarrow> (\<exists>v. x = Vin v \<and> (u, v) \<in> G)"
  by (force simp: split_graph_def)+

lemma split_graph_fst: "e \<in> split_graph G \<Longrightarrow> unsplit_node (fst e) \<in> dVs G"
  by (auto simp: split_graph_def intro: dVsI')

lemma finite_split_graph: "finite G \<Longrightarrow> finite (split_graph G)"
  by (simp add: split_graph_def finite_vertices_iff)

lemma unsplit_split_walk[simp]: "unsplit_walk (split_walk p) = p"
  by (induction p) auto

lemma split_walk_Nil[simp]: "split_walk p = [] \<longleftrightarrow> p = []"
  by (cases p) auto

lemma hd_split_walk: "p \<noteq> [] \<Longrightarrow> hd (split_walk p) = Vin (hd p)"
  by (cases p) auto

lemma last_split_walk: "p \<noteq> [] \<Longrightarrow> last (split_walk p) = Vout (last p)"
  by (induction p) auto

lemma set_split_walk: "set (split_walk p) = Vin ` set p \<union> Vout ` set p"
  by (induction p) auto

lemma split_walk_distinct: "distinct (split_walk p) \<Longrightarrow> distinct p"
  by (induction p) (auto simp: set_split_walk)

lemma split_walk_edges: "v \<in> set p \<Longrightarrow> (Vin v, Vout v) \<in> set (edges_of_vwalk (split_walk p))"
proof (induction p)
  case (Cons x p)
  then show ?case
    by (cases p) auto
qed simp

lemma split_walk_edge_fst:
  "e \<in> set (edges_of_vwalk (split_walk p)) \<Longrightarrow> unsplit_node (fst e) \<in> set p"
proof -
  assume "e \<in> set (edges_of_vwalk (split_walk p))"
  then have "fst e \<in> set (split_walk p)"
    by (rule subsetD[OF edges_of_vwalk_dVs dVsI'(1)])
  then show ?thesis
    by (auto simp: set_split_walk)
qed

lemma vwalk_split_walk: "Vwalk.vwalk G p \<Longrightarrow> Vwalk.vwalk (split_graph G) (split_walk p)"
proof (induction p rule: Vwalk.vwalk.induct)
  case (vwalk1 v)
  then have "(Vin v, Vout v) \<in> split_graph G"
    by (simp add: split_graph_edge_iff)
  then show ?case
    by auto
next
  case (vwalk2 v v' vs)
  then show ?case
    by (auto simp: split_graph_edge_iff)
qed simp

lemma vwalk_bet_split_walk:
  "vwalk_bet G u p v \<Longrightarrow> vwalk_bet (split_graph G) (Vin u) (split_walk p) (Vout v)"
  by (auto simp: vwalk_bet_def hd_split_walk last_split_walk intro: vwalk_split_walk)

lemma vwalk_unsplit:
  "\<lbrakk>Vwalk.vwalk (split_graph G) (Vin a # p); last (Vin a # p) = Vout b\<rbrakk> \<Longrightarrow>
    split_walk (unsplit_walk (Vin a # p)) = Vin a # p \<and> vwalk_bet G a (unsplit_walk (Vin a # p)) b"
proof (induction "length p" arbitrary: a p rule: less_induct)
  case less
  then obtain p' where p: "p = Vout a # p'" "a \<in> dVs G"
    by (cases p) (auto simp: split_graph_edge_iff)
  show ?case
  proof (cases p')
    case Nil
    then show ?thesis
      using less.prems p by (auto simp: vwalk_bet_def)
  next
    case (Cons y p'')
    then obtain c where y: "y = Vin c" "(a, c) \<in> G"
      using less.prems(1) p by (auto simp: split_graph_edge_iff)
    have "split_walk (unsplit_walk (Vin c # p'')) = Vin c # p'' \<and>
        vwalk_bet G c (unsplit_walk (Vin c # p'')) b"
      by (rule less.hyps) (use less.prems p Cons y in auto)
    then show ?thesis
      using p Cons y by (auto simp: vwalk_bet_def)
  qed
qed

subsection \<open>From the Split Graph back to the Original Graph\<close>

text \<open>Edge-disjoint paths from entries of \<open>A\<close> to exits of \<open>B\<close> in the split graph give a linkage
in the original graph onto as many vertices of \<open>B\<close>.\<close>

lemma split_edge_linkage_linked:
  assumes link: "edge_linkage (split_graph G) (Vin ` A) (Vout ` B) P"
  shows "\<exists>T. T \<subseteq> B \<and> card T = card P \<and> linked G A T"
proof -
  let ?H = "split_graph G"
  have path: "split_walk (unsplit_walk p) = p \<and> hd (unsplit_walk p) \<in> A \<and> last (unsplit_walk p) \<in> B \<and>
      distinct_vwalk_bet G (hd (unsplit_walk p)) (unsplit_walk p) (last (unsplit_walk p))"
    if p: "p \<in> P" for p
  proof -
    obtain a where a: "a \<in> A" "hd p = Vin a"
      using edge_linkageD(1)[OF link p] by blast
    obtain b where b: "b \<in> B" "last p = Vout b"
      using edge_linkageD(2)[OF link p] by blast
    have dw: "distinct_vwalk_bet ?H (hd p) p (last p)"
      by (rule edge_linkageD(3)[OF link p])
    then obtain p' where p': "p = Vin a # p'"
      using a(2) by (cases p) (auto simp: distinct_vwalk_bet_def vwalk_bet_def)
    have "split_walk (unsplit_walk p) = p \<and> vwalk_bet G a (unsplit_walk p) b"
      unfolding p' by (rule vwalk_unsplit) (use dw p' b(2) in \<open>auto simp: distinct_vwalk_bet_def vwalk_bet_def\<close>)
    then show ?thesis
      using a(1) b(1) dw split_walk_distinct[of "unsplit_walk p"]
      by (auto simp: distinct_vwalk_bet_def vwalk_bet_def)
  qed
  define Q where "Q = unsplit_walk ` P"
  have Q_paths: "hd q \<in> A \<and> distinct_vwalk_bet G (hd q) q (last q)" if "q \<in> Q" for q
    using that path unfolding Q_def by blast
  have Q_disj: "set q1 \<inter> set q2 = {}" if q: "q1 \<in> Q" "q2 \<in> Q" "q1 \<noteq> q2" for q1 q2
  proof -
    obtain p1 p2 where p: "p1 \<in> P" "p2 \<in> P" "q1 = unsplit_walk p1" "q2 = unsplit_walk p2"
      using q(1,2) unfolding Q_def by blast
    have sw: "split_walk q1 = p1" "split_walk q2 = p2"
      using path[OF p(1)] path[OF p(2)] p(3,4) by auto
    have "p1 \<noteq> p2"
      using q(3) p(3,4) by blast
    then have edisj: "set (edges_of_vwalk p1) \<inter> set (edges_of_vwalk p2) = {}"
      by (rule edge_linkageD(4)[OF link p(1,2)])
    show ?thesis
    proof (rule ccontr)
      assume "set q1 \<inter> set q2 \<noteq> {}"
      then obtain v where "v \<in> set q1" "v \<in> set q2"
        by blast
      then have "(Vin v, Vout v) \<in> set (edges_of_vwalk p1) \<inter> set (edges_of_vwalk p2)"
        using split_walk_edges[of v q1] split_walk_edges[of v q2] unfolding sw by blast
      with edisj show False
        by blast
    qed
  qed
  define T where "T = last ` Q"
  have link_G: "linkage G A T (\<lambda>t. SOME q. q \<in> Q \<and> last q = t)"
    unfolding T_def using Q_paths Q_disj by (rule linkage_of_paths(1))
  have inj_last: "inj_on last Q"
    using Q_paths Q_disj by (rule linkage_of_paths(2))
  have inj_P: "inj_on unsplit_walk P"
    by (rule inj_on_inverseI[where g = split_walk]) (use path in blast)
  have TB: "T \<subseteq> B"
    using path unfolding T_def Q_def by blast
  have card_T: "card T = card P"
    unfolding T_def Q_def using card_image[OF inj_last] card_image[OF inj_P] Q_def by simp
  show ?thesis
    using TB card_T link_G by (auto intro: linkedI)
qed

text \<open>An edge separator in the split graph gives a vertex separator with at most as many
vertices.\<close>

lemma split_edge_separator_separator:
  assumes fin: "finite G" and sep: "edge_separator (split_graph G) (Vin ` A) (Vout ` B) F"
  shows "\<exists>X. separator G A B X \<and> X \<subseteq> dVs G \<and> finite X \<and> card X \<le> card F"
proof -
  let ?H = "split_graph G"
  define X where "X = (\<lambda>e. unsplit_node (fst e)) ` F"
  have sep_G: "separator G A B X"
  proof (rule separatorI)
    fix u p v
    assume u: "u \<in> A" and v: "v \<in> B" and p: "vwalk_bet G u p v"
    have "vwalk_bet ?H (Vin u) (split_walk p) (Vout v)"
      by (rule vwalk_bet_split_walk[OF p])
    then obtain e where e: "e \<in> set (edges_of_vwalk (split_walk p))" "e \<in> F"
      using edge_separatorD(2)[OF sep imageI[OF u] imageI[OF v]] by blast
    then have "unsplit_node (fst e) \<in> set p \<inter> X"
      unfolding X_def by (auto intro: split_walk_edge_fst)
    then show "set p \<inter> X \<noteq> {}"
      by blast
  qed
  have F_H: "F \<subseteq> ?H"
    by (rule edge_separatorD(1)[OF sep])
  have X_V: "X \<subseteq> dVs G"
    using F_H unfolding X_def by (auto intro: split_graph_fst)
  have fin_F: "finite F"
    by (rule finite_subset[OF F_H finite_split_graph[OF fin]])
  have "finite X"
    unfolding X_def using fin_F by (rule finite_imageI)
  moreover have "card X \<le> card F"
    unfolding X_def using fin_F by (rule card_image_le)
  ultimately show ?thesis
    using sep_G X_V by blast
qed

text \<open>Menger's Theorem (set version): there are as many vertex-disjoint paths from \<open>A\<close> to \<open>B\<close>
as a smallest set separating \<open>A\<close> from \<open>B\<close> has vertices. The other inequality, i.e.\ that no
linkage is larger than any separator, is the easy direction.\<close>

theorem menger:
  assumes "finite G"
  shows "\<exists>T X. T \<subseteq> B \<and> linked G A T \<and> separator G A B X \<and> X \<subseteq> dVs G \<and> card X = card T"
proof -
  have AB: "Vin ` A \<inter> Vout ` B = {}"
    by auto
  obtain P F where link: "edge_linkage (split_graph G) (Vin ` A) (Vout ` B) P"
    and sep: "edge_separator (split_graph G) (Vin ` A) (Vout ` B) F" and card_FP: "card F = card P"
    using menger_edge[OF finite_split_graph[OF assms] AB] by blast
  obtain T where T: "T \<subseteq> B" "card T = card P" "linked G A T"
    using split_edge_linkage_linked[OF link] by blast
  obtain X where X: "separator G A B X" "X \<subseteq> dVs G" "finite X" "card X \<le> card F"
    using split_edge_separator_separator[OF assms sep] by blast
  from T(3) obtain p where p: "linkage G A T p"
    by (rule linkedE)
  have "card T \<le> card X"
    using p X(1) T(1) X(3) by (rule linkage_card_le_separator)
  then have "card X = card T"
    using X(4) card_FP T(2) by simp
  then show ?thesis
    using T(1,3) X(1,2) by blast
qed

end
