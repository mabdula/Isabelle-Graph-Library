theory Menger
  imports
    Directed_Set_Graphs.Vwalk
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

text \<open>Menger's Theorem (set version): there are as many vertex-disjoint paths from \<open>A\<close> to \<open>B\<close>
as a smallest set separating \<open>A\<close> from \<open>B\<close> has vertices. The other inequality, i.e.\ that no
linkage is larger than any separator, is the easy direction.\<close>

theorem menger:
  assumes "finite G"
  shows "\<exists>T X. T \<subseteq> B \<and> linked G A T \<and> separator G A B X \<and> X \<subseteq> dVs G \<and> card X = card T"
  sorry

end
