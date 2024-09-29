theory Component_Defs
  imports
    Pair_Graph
begin

definition subgraph :: "'a dgraph \<Rightarrow> 'a dgraph \<Rightarrow> bool" where
  "subgraph H G \<equiv> H \<subseteq> G"

definition induce_subgraph :: "'a dgraph \<Rightarrow> 'a set \<Rightarrow> 'a dgraph" (infix "\<downharpoonright>" 67) where
  "G \<downharpoonright> vs \<equiv> {(u,v) \<in> G. u \<in> vs \<and> v \<in> vs}"

definition induced_subgraph :: "'a dgraph \<Rightarrow> 'a dgraph \<Rightarrow> bool" where
  "induced_subgraph H G \<equiv> H = G \<downharpoonright> dVs H"

definition spanning :: "'a dgraph \<Rightarrow> 'a dgraph \<Rightarrow> bool" where
  "spanning H G \<equiv> subgraph H G \<and> dVs G = dVs H"

definition strongly_connected :: "'a dgraph \<Rightarrow> bool" where
  "strongly_connected G \<equiv> G \<noteq> {} \<and> (\<forall>u \<in> dVs G. \<forall>v \<in> dVs G. u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v)"

definition mk_symmetric :: "'a dgraph \<Rightarrow> 'a dgraph" where
  "mk_symmetric G \<equiv> G \<union> {(v,u). (u,v) \<in> G}"

definition connected :: "'a dgraph \<Rightarrow> bool" where
  "connected G \<equiv> strongly_connected (mk_symmetric G)"

definition max_subgraph :: "'a dgraph \<Rightarrow> ('a dgraph \<Rightarrow> bool) \<Rightarrow> 'a dgraph \<Rightarrow> bool" where
  "max_subgraph G P H \<equiv> subgraph H G \<and> P H \<and> 
    (\<forall>H'. H' \<noteq> H \<and> subgraph H H' \<longrightarrow> \<not>(subgraph H' G \<and> P H'))"

definition sccs :: "'a dgraph \<Rightarrow> 'a dgraph set" where
  "sccs G \<equiv> 
     {H. induced_subgraph H G \<and> strongly_connected H \<and>
         \<not>(\<exists>H'. induced_subgraph H' G \<and> strongly_connected H' \<and>  H \<subset> H')}"

definition sccs_dVs :: "'a dgraph \<Rightarrow> 'a set set" where
  "sccs_dVs G \<equiv> {S. S \<noteq> {} \<and> (\<forall>u \<in> S. \<forall>v \<in> S. u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v) \<and> (\<forall>u \<in> S. \<forall>v. v \<notin> S \<longrightarrow> \<not>u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<or> \<not>v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u)}"

definition scc_of :: "'a dgraph \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "scc_of G u \<equiv> {v. u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<and> v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u}"


subsection \<open>Intro, destruction and elim rules\<close>
lemma subgraphI[intro]:
  "H \<subseteq> G \<Longrightarrow> subgraph H G" by (simp add: subgraph_def)

lemma subgraphD:
  "subgraph H G \<Longrightarrow> H \<subseteq> G" by (simp add: subgraph_def)

lemma dVs_subset:
  assumes "E \<subseteq> E'"
  shows "dVs E \<subseteq> dVs E'"
  using assms
  unfolding dVs_def
  by blast

lemma subgraph_dVs: "subgraph H G \<Longrightarrow> dVs H \<subseteq> dVs G"
  by (auto simp: subgraph_def dVs_subset)

lemma subgraph_dVs': "subgraph H G \<Longrightarrow> u \<in> dVs H \<Longrightarrow> u \<in> dVs G"
  by (auto dest: subgraph_dVs)

lemma subgraphE[elim]:
  assumes "subgraph H G"
  obtains "H \<subseteq> G" "dVs H \<subseteq> dVs G"
  using assms
  by (auto dest: subgraphD subgraph_dVs)

lemma in_induce_subgraphI[intro]:
  assumes "(u,v) \<in> G" "u \<in> vs" "v \<in> vs"
  shows "(u,v) \<in> G \<downharpoonright> vs"
  using assms
  unfolding induce_subgraph_def
  by simp

lemma in_induce_subgraphD:
  assumes "(u,v) \<in> G \<downharpoonright> vs"
  shows "(u,v) \<in> G" "u \<in> vs" "v \<in> vs"
  using assms unfolding induce_subgraph_def
  by auto

lemma in_induce_subgraphE[elim?]:
  assumes "(u,v) \<in> G \<downharpoonright> vs"
  obtains "(u,v) \<in> G" "u \<in> vs" "v \<in> vs"
  using assms
  by (auto dest: in_induce_subgraphD)

lemma subgraph_induce_subgraph:
  "subgraph (G \<downharpoonright> vs) G"
  by (auto dest: in_induce_subgraphD)

lemma subgraph_induce_subgraph':
  "H = (G \<downharpoonright> vs) \<Longrightarrow> subgraph H G"
  by (simp add: subgraph_induce_subgraph)

lemma induced_subgraphI[intro]:
  assumes "subgraph H G"
  assumes "\<And>u v. \<lbrakk>(u,v) \<in> G; u \<in> dVs H; v \<in> dVs H\<rbrakk> \<Longrightarrow> (u,v) \<in> H"
    shows "induced_subgraph H G"
  using assms unfolding induced_subgraph_def induce_subgraph_def
  by (auto simp: dVsI)

lemma induced_subgraphD:
  assumes "induced_subgraph H G"
  shows "subgraph H G"
  and "\<And>u v. \<lbrakk>(u,v) \<in> G; u \<in> dVs H; v \<in> dVs H\<rbrakk> \<Longrightarrow> (u,v) \<in> H"
  using assms unfolding induced_subgraph_def
  by (auto dest: subgraph_induce_subgraph')

lemma induced_subgraphE[elim?]:
  assumes "induced_subgraph H G"
  obtains "subgraph H G"
  and "\<And>u v. \<lbrakk>(u,v) \<in> G; u \<in> dVs H; v \<in> dVs H\<rbrakk> \<Longrightarrow> (u,v) \<in> H"
  using assms
  by (auto dest: induced_subgraphD)

lemma spanningI[intro]:
  assumes "subgraph H G"
  assumes "dVs G = dVs H"
  shows "spanning H G"
  using assms unfolding spanning_def
  by simp

lemma spanningD:
  assumes "spanning H G"
  shows "subgraph H G" "dVs G = dVs H"
  using assms unfolding spanning_def
  by simp_all

lemma spanningE[elim?]:
  assumes "spanning H G"
  obtains "subgraph H G" "dVs G = dVs H"
  using assms
  by (auto dest: spanningD)

lemma strongly_connectedI[intro]:
  assumes "G \<noteq> {}"
  assumes "\<And>u v. \<lbrakk>u \<in> dVs G; v \<in> dVs G\<rbrakk> \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  shows "strongly_connected G"
  using assms unfolding strongly_connected_def
  by auto

lemma strongly_connectedD:
  assumes "strongly_connected G"
  shows "G \<noteq> {}" "\<And>u v. \<lbrakk>u \<in> dVs G; v \<in> dVs G\<rbrakk> \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  using assms unfolding strongly_connected_def
  by auto

lemma in_mk_symmetricI[intro]:
  assumes "(u,v) \<in> G \<or> (v,u) \<in> G"
  shows "(u,v) \<in> mk_symmetric G"
  using assms
  unfolding mk_symmetric_def by simp

lemma in_mk_symmetricD:
  assumes "(u,v) \<in> mk_symmetric G"
  shows "(u,v) \<in> G \<or> (v,u) \<in> G"
  using assms
  unfolding mk_symmetric_def by simp

lemma in_mk_symmetricE[elim?]:
  assumes "(u,v) \<in> mk_symmetric G"
  obtains "(u,v) \<in> G \<or> (v,u) \<in> G"
  using assms
  by (auto dest: in_mk_symmetricD)

lemma sym_mk_symmetric:
  "sym (mk_symmetric G)"
  unfolding mk_symmetric_def by (auto intro: symI)

lemma dVs_sym: "dVs {(v,u). (u,v) \<in> G} = dVs G"
  unfolding dVs_def by blast

lemma dVs_mk_symmetric: "dVs (mk_symmetric G) = dVs G"
  unfolding mk_symmetric_def by (simp add: dVs_union_distr dVs_sym)

lemma mk_symmetric_conv: "mk_symmetric G = (\<Union>(u,v)\<in>G. {(u,v), (v,u)})"
  by (auto simp: mk_symmetric_def)

lemma connectedI[intro]:
  assumes "strongly_connected (mk_symmetric G)"
  shows "connected G"
  using assms unfolding connected_def
  by simp

lemma connectedD:
  assumes "connected G"
  shows "strongly_connected (mk_symmetric G)"
  using assms unfolding connected_def
  by simp

lemma connectedE[elim?]:
  assumes "connected G"
  obtains "strongly_connected (mk_symmetric G)"
  using assms
  by (auto dest: connectedD)

lemma max_subgraphI[intro]:
  assumes "subgraph H G"
  assumes "P H"
  assumes "\<And>H'. \<lbrakk>H'\<noteq>H; subgraph H H'; subgraph H' G\<rbrakk> \<Longrightarrow> \<not>P H"
  shows "max_subgraph G P H"
  using assms unfolding max_subgraph_def
  by auto

lemma max_subgraphD:
  assumes "max_subgraph G P H"
  shows "subgraph H G" "P H"
  and "\<And>H'. \<lbrakk>H'\<noteq>H; subgraph H H'; subgraph H' G\<rbrakk> \<Longrightarrow> \<not>P H'"
  using assms unfolding max_subgraph_def
  by auto

lemma max_subgraphE[elim?]:
  assumes "max_subgraph G P H"
  obtains "subgraph H G" "P H"
  and "\<And>H'. \<lbrakk>H'\<noteq>H; subgraph H H'; subgraph H' G\<rbrakk> \<Longrightarrow> \<not>P H'"
  using assms
  by (auto dest: max_subgraphD)

lemma in_sccsI[intro]:
  assumes "induced_subgraph H G"
  assumes "strongly_connected H"
  assumes "\<And>H'. \<lbrakk>induced_subgraph H' G; strongly_connected H'; H \<subset> H'\<rbrakk> \<Longrightarrow> False"
  shows "H \<in> sccs G"
  using assms unfolding sccs_def
  by auto

lemma in_sccsD:
  assumes "H \<in> sccs G"
  shows "induced_subgraph H G" "strongly_connected H"
  and "\<And>H'. \<lbrakk>induced_subgraph H' G; strongly_connected H'; H \<subset> H'\<rbrakk> \<Longrightarrow> False"
  using assms
  by (auto simp: sccs_def)

lemma in_sccsE[elim?]:
  assumes "H \<in> sccs G"
  obtains "induced_subgraph H G" "strongly_connected H"
  and "\<And>H'. \<lbrakk>induced_subgraph H' G; strongly_connected H'; H \<subset> H'\<rbrakk> \<Longrightarrow> False"
  using assms
  by (auto dest: in_sccsD)

text \<open>
  This lemma is merely here to prove that we can replace \<^term>\<open>dVs H \<subset> dVs H'\<close> by \<^term>\<open>H \<subset> H'\<close>
  in the definition \<^term>\<open>sccs\<close>.
\<close>
lemma induced_subgraph_dVs_subset_iff:
  "induced_subgraph H G \<Longrightarrow> induced_subgraph H' G \<Longrightarrow> dVs H \<subset> dVs H' \<longleftrightarrow> H \<subset> H'"
  unfolding induced_subgraph_def induce_subgraph_def subset_eq
  apply (auto dest!: dVs_subset)
  by (smt (verit, best) case_prodD case_prodI mem_Collect_eq subsetD) 

lemma in_sccs_dVsI[intro]:
  fixes G :: "'a dgraph"
  assumes "S \<noteq> {}"
  assumes "\<And>u v. \<lbrakk>u \<in> S; v \<in> S\<rbrakk> \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  assumes "\<And>u v. \<lbrakk>u \<in> S; v \<notin> S\<rbrakk> \<Longrightarrow> \<not> u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<or> \<not> v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u"
  shows "S \<in> sccs_dVs G"
  using assms unfolding sccs_dVs_def
  by auto

lemma in_sccs_dVsD:
  fixes G :: "'a dgraph"
  assumes "S \<in> sccs_dVs G"
  shows "S \<noteq> {}"
  and "\<And>u v. \<lbrakk>u \<in> S; v \<in> S\<rbrakk> \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  and "\<And>u v. \<lbrakk>u \<in> S; v \<notin> S\<rbrakk> \<Longrightarrow> \<not> u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<or> \<not> v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u"
  using assms unfolding sccs_dVs_def
  by auto

lemma in_sccs_dVsE[elim?]:
  fixes G :: "'a dgraph"
  assumes "S \<in> sccs_dVs G"
  obtains "S \<noteq> {}"
  and "\<And>u v. \<lbrakk>u \<in> S; v \<in> S\<rbrakk> \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  and "\<And>u v. \<lbrakk>u \<in> S; v \<notin> S\<rbrakk> \<Longrightarrow> \<not> u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<or> \<not> v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u"
  using assms
  by (auto dest: in_sccs_dVsD)

lemma in_scc_ofI[intro]:
  fixes G :: "'a dgraph"
  assumes "v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u" "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  shows "v \<in> scc_of G u"
  using assms unfolding scc_of_def
  by simp

lemma in_scc_ofD:
  fixes G :: "'a dgraph"
  assumes "v \<in> scc_of G u"
  shows "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v" "v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u"
  using assms unfolding scc_of_def
  by simp_all

lemma in_scc_ofE[elim?]:
  fixes G :: "'a dgraph"
  assumes "v \<in> scc_of G u"
  obtains "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v" "v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u"
  using assms
  by (auto dest: in_scc_ofD)


end