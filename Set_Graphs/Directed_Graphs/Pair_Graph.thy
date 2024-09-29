theory Pair_Graph
  imports 
    Main
    Graph_Theory.Rtrancl_On
begin

text \<open>Graphs are a fundamental structure in computer science and mathematics.\<close>

type_synonym 'a dgraph = "('a \<times> 'a) set"

definition "dVs G \<equiv> \<Union> {{v1,v2} | v1 v2. (v1, v2) \<in> G}"

(*<*)

lemma induct_pcpl:
  "\<lbrakk>P []; \<And>x. P [x]; \<And>x y zs. P zs \<Longrightarrow> P (x # y # zs)\<rbrakk> \<Longrightarrow> P xs"
  by induction_schema (pat_completeness, lexicographic_order)

lemma induct_pcpl_2:
  "\<lbrakk>P []; \<And>x. P [x]; \<And>x y. P [x,y]; \<And>x y z. P [x,y,z]; \<And>w x y z zs. P zs \<Longrightarrow> P (w # x # y # z # zs)\<rbrakk> \<Longrightarrow> P xs"
  by induction_schema (pat_completeness, lexicographic_order)

lemma dVs_empty[simp]: "dVs {} = {}"
  by (simp add: dVs_def)

lemma dVs_empty_iff[simp]: "dVs E = {} \<longleftrightarrow> E = {}"
  unfolding dVs_def by auto

lemma dVsI[intro]:
  assumes "(a, v) \<in> dG" shows "a \<in> dVs dG" and "v \<in> dVs dG"
  using assms unfolding dVs_def by auto

lemma dVsI':
  assumes "e \<in> dG" shows "fst e \<in> dVs dG" and "snd e \<in> dVs dG"
  using assms
  by (auto intro: dVsI[of "fst e" "snd e"])

lemma dVs_union_distr[simp]: "dVs (G \<union> H) = dVs G \<union> dVs H"
  unfolding dVs_def by blast

lemma dVs_union_big_distr: "dVs (\<Union>G) = \<Union>(dVs ` G)"
  apply (induction G rule: infinite_finite_induct)
    apply (auto simp: dVs_union_distr)
   apply (smt dVs_def mem_Collect_eq mem_simps(9))
  by (metis Sup_insert UnCI dVs_union_distr mk_disjoint_insert)

lemma dVs_eq: "dVs E = fst ` E \<union> snd ` E"
  by (induction E rule: infinite_finite_induct)
     (auto simp: dVs_def intro!: image_eqI, blast+)

lemma finite_vertices_iff: "finite (dVs E) \<longleftrightarrow> finite E" (is "?L \<longleftrightarrow> ?R")
proof
  show "?R \<Longrightarrow> ?L"
    by (induction E rule: finite_induct)
       (auto simp: dVs_eq)
  show "?L \<Longrightarrow> ?R"
  proof (rule ccontr)
    show "?L \<Longrightarrow> \<not>?R \<Longrightarrow> False"
      unfolding dVs_eq
      using finite_subset subset_fst_snd by fastforce
  qed
qed

abbreviation reachable1 :: "('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<rightarrow>\<^sup>+\<index> _" [100,100] 40) where
  "reachable1 E u v \<equiv> (u,v) \<in> E\<^sup>+"

definition reachable :: "('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<rightarrow>\<^sup>*\<index> _" [100,100] 40) where
  "reachable E u v \<equiv> (u,v) \<in> rtrancl_on (dVs E) E"

lemma reachableE[elim?]:
  assumes "(u,v) \<in> E"
  obtains e where "e \<in> E" "e = (u, v)"
  using assms by auto

lemma reachable_refl[intro!, Pure.intro!, simp]: "v \<in> dVs E \<Longrightarrow> v \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v"
  unfolding reachable_def by auto



lemma reachable_trans[trans,intro]:
  assumes "u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v" "v \<rightarrow>\<^sup>*\<^bsub>E\<^esub> w" shows "u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> w"
  using assms unfolding reachable_def by (rule rtrancl_on_trans)

lemma reachable_edge[dest,intro]: "(u,v) \<in> E \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v"
  unfolding reachable_def
  by (auto intro!: rtrancl_consistent_rtrancl_on)

lemma reachable_induct[consumes 1, case_names base step]:
  assumes major: "u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v"
    and cases: "\<lbrakk>u \<in> dVs E\<rbrakk> \<Longrightarrow> P u"
      "\<And>x y. \<lbrakk>u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> x; (x,y) \<in> E; P x\<rbrakk> \<Longrightarrow> P y"
  shows "P v"
  using assms unfolding reachable_def by (rule rtrancl_on_induct)

lemma converse_reachable_induct[consumes 1, case_names base step, induct pred: reachable]:
  assumes major: "u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v"
    and cases: "v \<in> dVs E \<Longrightarrow> P v"
      "\<And>x y. \<lbrakk>(x,y) \<in> E; y \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v; P y\<rbrakk> \<Longrightarrow> P x"
    shows "P u"
  using assms unfolding reachable_def by (rule converse_rtrancl_on_induct)

lemma reachable_in_dVs:
  assumes "u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v"
  shows "u \<in> dVs E" "v \<in> dVs E"
  using assms by (induct) (simp_all add: dVsI)

lemma reachable1_in_dVs:
  assumes "u \<rightarrow>\<^sup>+\<^bsub>E\<^esub> v"
  shows "u \<in> dVs E" "v \<in> dVs E"
  using assms by (induct) (simp_all add: dVsI)


lemma reachable1_reachable[intro]:
  "v \<rightarrow>\<^sup>+\<^bsub>E\<^esub> w \<Longrightarrow> v \<rightarrow>\<^sup>*\<^bsub>E\<^esub> w"
  unfolding reachable_def
  by (auto intro: rtrancl_consistent_rtrancl_on simp: dVsI reachable1_in_dVs)

lemmas reachable1_reachableE[elim] = reachable1_reachable[elim_format]

lemma reachable_neq_reachable1[intro]:
  assumes reach: "v \<rightarrow>\<^sup>*\<^bsub>E\<^esub> w"
    and neq: "v \<noteq> w"
  shows "v \<rightarrow>\<^sup>+\<^bsub>E\<^esub> w" 
  using assms
  unfolding reachable_def
  by (auto dest: rtrancl_on_rtranclI rtranclD)

lemmas reachable_neq_reachable1E[elim] = reachable_neq_reachable1[elim_format]

lemma arc_implies_dominates: "e \<in> E \<Longrightarrow> (fst e, snd e) \<in> E" by auto
(*>*)

definition "neighbourhood G u = {v. (u,v) \<in> G}"

lemma 
  neighbourhoodI[intro]: "v \<in> (neighbourhood G u) \<Longrightarrow> (u,v) \<in> G" and
  neighbourhoodD[dest]: "(u,v) \<in> G \<Longrightarrow> v \<in> (neighbourhood G u)"
  by (auto simp: neighbourhood_def)


definition "sources G = {u | u v . (u,v) \<in> G}"

definition "sinks G = {v | u v . (u,v) \<in> G}"

lemma dVs_subset: "G \<subseteq> G' \<Longrightarrow> dVs G \<subseteq> dVs G'"
  by (auto simp: dVs_def)

lemma dVs_insert[elim]:
  "v\<in> dVs (insert (x,y) G) \<Longrightarrow> \<lbrakk>v = x \<Longrightarrow> P; v = y \<Longrightarrow> P; v \<in> dVs G \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: dVs_def)

lemma in_neighbourhood_dVs[simp, intro]:
  "v \<in> neighbourhood G u \<Longrightarrow> v \<in> dVs G"
  by auto

lemma subset_neighbourhood_dVs[simp, intro]:
  "neighbourhood G u \<subseteq> dVs G"
  by auto

lemma in_dVsE: "v \<in> dVs G \<Longrightarrow> \<lbrakk>(\<And>u. (u, v) \<in> G \<Longrightarrow> P); (\<And>u. (v, u) \<in> G \<Longrightarrow> P)\<rbrakk> \<Longrightarrow> P"
               "v \<notin> dVs G \<Longrightarrow> (\<lbrakk>(\<And>u. (u, v) \<notin> G); (\<And>u. (v, u) \<notin> G)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: dVs_def)

lemma neighoubrhood_union[simp]: "neighbourhood (G \<union> G') u = neighbourhood G u \<union> neighbourhood G' u"
  by (auto simp: neighbourhood_def)

end
