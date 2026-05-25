(*authors: Mohammad Abdulaziz, Thomas Ammer, Christoph Madlener*)
section \<open>Basic Theory on Matchings\<close>

theory Matching
  imports Alternating_Lists.Alternating_Lists
          Directed_Set_Graphs.More_Lists
          Undirected_Set_Graphs.Bipartite
begin

subsection \<open>Misc\<close>

subsection \<open>Symmetric Difference\<close>

definition symmetric_diff (infixl "\<oplus>" 65) where
  "symmetric_diff s t = (s - t) \<union> (t - s)"

lemma in_symmetric_diff_iff:
  "x \<in> X \<oplus> Y \<longleftrightarrow> x \<in> X \<and> x \<notin> Y \<or> x \<in> Y \<and> x \<notin> X"
  by(auto simp add: symmetric_diff_def)

lemma sym_diff_subset:
  "s \<oplus> s' \<subseteq> s \<union> s'"
  by (auto simp: symmetric_diff_def)

lemma card_Int_Diff:
  assumes "finite s" "finite t" 
  shows "card (s - t) + card (s \<inter> t) = card s"
  using assms
  by (metis add.commute Int_Diff_Un Int_Diff_disjoint card_Un_disjoint finite_Diff finite_Int)

lemma card_symm_diff:
  assumes "finite s" "finite t" "card (t - s) = card (s \<inter> t)"
  shows "card (s \<oplus> t) = card s"
  using assms 
  by(auto simp: symmetric_diff_def disjnt_Diff1 card_Un_disjnt card_Int_Diff)

lemma in_symm_diff_eq_1:
  assumes "e \<in> G'"
  shows "e \<in> G \<longleftrightarrow> e \<notin> (G \<oplus> G')"
  using assms
  unfolding symmetric_diff_def
  by auto

lemma in_symm_diff_eq_2:
  assumes "e \<notin> G'"
  shows "e \<in> G \<longleftrightarrow> e \<in> (G \<oplus> G')"
  using assms
  unfolding symmetric_diff_def
  by auto

lemma symmetric_diff_id:
  shows "(s \<oplus> t) \<oplus> t = s"
  unfolding symmetric_diff_def
  by auto

lemma finite_symm_diff:
  "\<lbrakk>finite s; finite t\<rbrakk> \<Longrightarrow> finite (s \<oplus> t)"
  by (auto simp: symmetric_diff_def)

lemma symm_diff_mutex:
  "\<lbrakk>x \<in> (s \<oplus> t); x \<in> s\<rbrakk> \<Longrightarrow> x \<notin> t"
  by (auto simp: symmetric_diff_def)

lemma smaller_matching_less_members:
  assumes "finite G" "card G < card G'"
  shows "card ((G \<oplus> G') \<inter> G) < card ((G \<oplus> G') \<inter> G')"
proof-
  have "card ((G \<oplus> G') \<inter> G) = card (G - G')"
    by (auto intro: HOL.arg_cong[where f = card] simp: symmetric_diff_def)
  moreover have "card ((G \<oplus> G') \<inter> G') = card (G' - G)"
    by (auto intro: HOL.arg_cong[where f = card] simp: symmetric_diff_def)
  moreover have "card (G - G') < card (G' - G)"
    using assms card.infinite
    by (fastforce intro!: card_less_sym_Diff)
  ultimately show "card ((G \<oplus> G') \<inter> G) < card ((G \<oplus> G') \<inter> G')"
    by simp
qed

lemma symm_diff_empty[simp]:
  "G = G' \<Longrightarrow> G \<oplus> G' = {}"
  unfolding symmetric_diff_def
  by simp

lemma symm_diff_with_empty[simp]:
  "G \<oplus> {} = G"
  unfolding symmetric_diff_def
  by simp

lemma sym_diff_sym:
  "s \<oplus> s' = s' \<oplus> s"
  unfolding symmetric_diff_def
  by blast

subsection \<open>Matchings\<close>

definition matching where
  "matching M \<longleftrightarrow> 
     (\<forall>e1 \<in> M. \<forall>e2 \<in> M. e1 \<noteq> e2 \<longrightarrow> e1 \<inter> e2 = {})"

abbreviation "graph_matching G M \<equiv> matching M \<and> M \<subseteq> G"

lemma matchingE:
  "matching M \<Longrightarrow> 
    ((\<And>e1 e2. \<lbrakk>e1 \<in> M; e2 \<in> M; e1 \<noteq> e2\<rbrakk> \<Longrightarrow> e1 \<inter> e2 = {}) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: matching_def)

lemma matchingI:
  "(\<And>e1 e2. \<lbrakk>e1 \<in> M; e2 \<in> M; e1 \<noteq> e2\<rbrakk> \<Longrightarrow> e1 \<inter> e2 = {}) \<Longrightarrow> matching M"
  by (auto simp: matching_def)

lemma matching_def2:
  "matching M \<longleftrightarrow> (\<forall>v \<in> Vs M. \<exists>!e\<in>M. v \<in> e)"
  unfolding matching_def Vs_def by blast

lemma matching_unique_match:
  "\<lbrakk>matching M; v \<in> e; v \<in> f; e \<in> M; f \<in> M\<rbrakk> \<Longrightarrow> e = f"
  by (auto simp: matching_def)

lemma doubleton_in_matching:
  assumes "matching M"
  shows "{v1 ,v2} \<in> M \<Longrightarrow> {v1, v3} \<in> M \<Longrightarrow> v2 = v3"
        "{v2 ,v1} \<in> M \<Longrightarrow> {v3, v1} \<in> M \<Longrightarrow> v2 = v3"
  using assms
  by (fastforce simp: doubleton_eq_iff matching_def2 Vs_def)+

lemma degree_matching_in_M:
  assumes "matching M" "v \<in> Vs M"
  shows "degree M v = 1"
proof-
  obtain e where edef: "v \<in> e" "e \<in> M"
    using assms
    by (fastforce simp: matching_def2)
  hence "{e} = {e. v \<in> e} \<inter> M"
    using assms edef
    by (auto simp: matching_def2)
  moreover have "card' {e} = 1" 
    by (simp add: card'_def one_eSuc enat_0)
  ultimately show ?thesis
    by (simp add: degree_def)
qed

lemma degree_matching:
  assumes "matching M"
  shows "degree M v \<le> 1"
proof(cases "v \<in> Vs M")
  case True thus ?thesis
    by (simp add: assms degree_matching_in_M)
next
  case False thus ?thesis
    by (simp add: degree_not_Vs)
qed

lemma degree_matching_union:
  assumes "matching M" "matching M'"
  shows "degree (M \<union> M') v \<le> 2"
proof-
   have "degree (M \<union> M') v \<le> degree M v + degree M' v"
    by (simp add: Int_Un_distrib card'_def card_Un_le degree_def)
  also have "... \<le> degree M v + 1"
    using degree_matching[OF \<open>matching M'\<close>]
    by auto
  also have "... \<le> 2"
    using degree_matching[OF \<open>matching M\<close>]
    by (subst one_add_one[symmetric]) (fastforce intro!:  add_right_mono)
  finally show ?thesis .
qed

lemma degree_symm_diff:
  assumes "matching M" "matching M'"
  shows "degree (M \<oplus> M') v \<le> 2"
  using degree_matching_union[OF assms, of v] 
        subset_edges_less_degree[OF sym_diff_subset, of M M' v] 
  by simp

lemma matching_delete:
  assumes "matching M"
  shows "matching (M - N)"
  using assms
  unfolding matching_def by blast

lemma matching_insert:
  assumes "e \<inter> (Vs M) = {}" "matching M"
  shows "matching (insert e M)"
  using assms
  unfolding Vs_def matching_def by blast

lemma matching_empty[simp]: "matching {}"
  unfolding matching_def by simp

lemma matching_subgraph: "matching M \<Longrightarrow> M' \<subseteq> M \<Longrightarrow> matching M'"
  unfolding matching_def
  by auto

lemma matching_graph_mono: "\<lbrakk>graph_matching G M; G \<subseteq> G'\<rbrakk> \<Longrightarrow> graph_matching G' M"
  by(auto simp add: matching_def)

lemma the_match: "matching M \<Longrightarrow> {u,v} \<in> M \<Longrightarrow> (THE u. {u,v} \<in> M) = u"
  by (auto intro!: the_equality)
     (metis doubleton_eq_iff insertI1 matching_unique_match)

lemma the_match': "matching M \<Longrightarrow> {u,v} \<in> M \<Longrightarrow> (THE v. {u,v} \<in> M) = v"
  by (auto dest: the_match edge_commute)

lemma the_match'': "matching M \<Longrightarrow> {u,v} \<in> M \<Longrightarrow> (THE u. {v,u} \<in> M) = u"
  by (auto dest: the_match edge_commute)

lemma the_match''': "matching M \<Longrightarrow> {u,v} \<in> M \<Longrightarrow> (THE v. {v,u} \<in> M) = v"
  by (auto dest: the_match' edge_commute)

lemma the_edge:
  assumes "matching M"
  assumes "e \<in> M"
  assumes "v \<in> e"
  shows "(THE e. e \<in> M \<and> v \<in> e) = e"
  using assms
  by (auto intro!: the_equality dest: matching_unique_match)

lemma (in graph_abs) matching_card_vs:
  assumes "matching G"
  shows "2 * card G = card (Vs G)"
  using assms graph
  by (auto simp: Vs_def card_2_iff card_partition finite_E dblton_graph_def matching_def)

lemma matching_vertex_disj_union:
  assumes "matching M" "matching M'" "Vs M \<inter> Vs M' = {}"
  shows   "matching (M \<union> M')" 
proof(rule matchingI, goal_cases)
  case (1 e1 e2)
  have "\<lbrakk>e1 \<in> M; e2 \<in> M'\<rbrakk> \<Longrightarrow> e1 \<inter> e2 = {}" for e1 e2
    using assms(3) by auto
  moreover have "\<lbrakk>e1 \<in> M; e2 \<in> M; e1\<noteq>e2\<rbrakk> \<Longrightarrow> e1 \<inter> e2 = {}" for e1 e2
    using assms(1) by (auto elim!: matchingE) 
  moreover have "\<lbrakk>e1 \<in> M'; e2 \<in> M'; e1\<noteq>e2\<rbrakk> \<Longrightarrow> e1 \<inter> e2 = {}" for e1 e2
    using assms(2) by (auto elim!: matchingE) 
  ultimately show ?case 
    using 1 by fast
qed

lemma matching_overlapping_union:
  assumes "matching M" "matching M'" "Vs M \<inter> Vs M' = Vs (M \<inter> M')"
  shows   "matching (M \<union> M')" 
proof(rule matchingI, goal_cases)
  case (1 e1 e2)
  have "\<lbrakk>e1 \<in> M; e2 \<in> M'; e1 \<notin> M'\<rbrakk> \<Longrightarrow> e1 \<inter> e2 = {}" for e1 e2
  proof(rule ccontr, goal_cases)
    case 1
    then obtain x where x: "x \<in> e1" "x \<in> e2" by auto
    hence "x \<in>  Vs (M \<inter> M')"
      using 1 assms by blast
    then obtain e3 where "e3 \<in> M \<inter> M'" "x \<in> e3" 
      by(auto elim!: vs_member_elim)
    hence "e3 = e1" "e3 = e2"
      using  x 1  matching_unique_match[OF assms(1), of x e1 e3]
             matching_unique_match[OF assms(2), of x e2 e3] by blast+
    thus ?case
      using 1 by auto
  qed
  moreover have "\<lbrakk>e1 \<in> M; e2 \<in> M; e1\<noteq>e2\<rbrakk> \<Longrightarrow> e1 \<inter> e2 = {}" for e1 e2
    using assms(1) by (auto elim!: matchingE) 
  moreover have "\<lbrakk>e1 \<in> M'; e2 \<in> M'; e1\<noteq>e2\<rbrakk> \<Longrightarrow> e1 \<inter> e2 = {}" for e1 e2
    using assms(2) by (auto elim!: matchingE) 
  ultimately show ?case 
    using 1 by fast
qed

lemma matching_image:
  assumes "matching M" "inj_on f (Vs M)"
  shows   "matching ((image f) ` M)"
proof(rule matchingI, rule ccontr, goal_cases)
  case (1 e1 e2)
  obtain e1' where e1': "e1 = f ` e1'" "e1' \<in> M" 
    using 1 by auto
  obtain e2' where e2': "e2 = f ` e2'" "e2' \<in> M" 
    using 1 by auto
  have e1'_not_e2':"e1' \<noteq> e2'"
    using "1"(3) e1'(1) e2'(1) by blast
  hence e1'_inter_e2'_empty:"e1' \<inter> e2' = {}"
    using assms(1) e1'(2) e2'(2)
    by(auto elim: matchingE)
  obtain x where x: "x \<in> e1 \<inter> e2"
    using 1 by auto
  obtain x1 where x1: "x1 \<in> e1'" "f x1 = x"
    using e1'(1) x by auto
  obtain x2 where x2: "x2 \<in> e2'" "f x2 = x"
    using e2'(1) x by auto
  have "x1 = x2" 
    using  e1'(2) e2'(2) inj_on_contraD[OF assms(2)] x1(1,2) x2(1,2) 
    by force
  then show ?case
    using e1'_inter_e2'_empty x1(1) x2(1) by blast
qed

lemma matching_remove_vertices:
  "matching M \<Longrightarrow> matching (M \<setminus> X)"
  using remove_vertices_subgraph
  by (auto intro: matching_subgraph)

lemma remove_edge_matching: "matching M \<Longrightarrow> {u,v} \<in> M \<Longrightarrow> M \<setminus> {u,v} = M - {{u,v}}"
  unfolding remove_vertices_graph_def
  by auto (metis empty_iff insert_iff matching_unique_match)+

lemma remove_vertex_matching: "matching M \<Longrightarrow> {u,v} \<in> M \<Longrightarrow> M \<setminus> {u} = M - {{u,v}}"
  unfolding remove_vertices_graph_def
  by auto (metis empty_iff insert_iff matching_unique_match)+

lemma remove_vertex_matching': "matching M \<Longrightarrow> {u,v} \<in> M \<Longrightarrow> M \<setminus> {v} = M - {{u,v}}"
  unfolding remove_vertices_graph_def
  by auto (metis empty_iff insert_iff matching_unique_match)+

lemma remove_edge_matching_vs: "matching M \<Longrightarrow> {u,v} \<in> M \<Longrightarrow> Vs (M \<setminus> {u,v}) = Vs M - {u,v}"
  by (auto simp add: remove_edge_matching Vs_def) (metis empty_iff insert_iff matching_unique_match)+

lemma remove_vertex_matching_vs: "matching M \<Longrightarrow> {u,v} \<in> M \<Longrightarrow> Vs (M \<setminus> {u}) = Vs M - {u,v}"
  by (metis remove_edge_matching remove_edge_matching_vs remove_vertex_matching)

lemma remove_vertex_matching_vs': "matching M \<Longrightarrow> {u,v} \<in> M \<Longrightarrow> Vs (M \<setminus> {v}) = Vs M - {u,v}"
  by (metis remove_edge_matching remove_edge_matching_vs remove_vertex_matching')

definition one_sided_matching :: "'a graph \<Rightarrow> 'a graph \<Rightarrow> 'a set \<Rightarrow> bool" where
  "one_sided_matching G M A = ( M \<subseteq> G \<and> (\<forall>a\<in>A. card {e\<in>M. a \<in> e} \<le> 1))"

lemma one_sided_matchingI:
  assumes "M \<subseteq> G"
  assumes "\<And>a. a \<in> A \<Longrightarrow> card {e\<in>M. a \<in> e} \<le> 1"
    shows "one_sided_matching G M A"
  using assms
  by(auto simp add: one_sided_matching_def)

lemma one_sided_matchingE:
  assumes "one_sided_matching G M A" 
          "\<lbrakk>M \<subseteq> G; \<And>a. a \<in> A \<Longrightarrow> card {e\<in>M. a \<in> e} \<le> 1\<rbrakk> \<Longrightarrow> P"
    shows P
  using assms
  by(auto simp add: one_sided_matching_def)

lemma one_sided_matching_empty[intro,simp]:
  "one_sided_matching G {} R"
  by (auto intro: one_sided_matchingI)

lemma one_sided_matching_subgraphD: "one_sided_matching G M A \<Longrightarrow> M \<subseteq> G"
  unfolding one_sided_matching_def by blast

lemma one_sided_matching_subgraphD': "one_sided_matching G M A \<Longrightarrow> e \<in> M \<Longrightarrow> e \<in> G"
  by (auto dest: one_sided_matching_subgraphD)

lemma one_sided_matching_insertI:
  assumes "{i,j} \<in> G"
  assumes "j \<notin> Vs M"
  assumes "i \<notin> A"
  assumes "one_sided_matching G M A"
  shows "one_sided_matching G (insert {i,j} M) A"
proof (intro one_sided_matchingI)
  from assms show "insert {i,j} M \<subseteq> G"
    by (auto dest: one_sided_matching_subgraphD)
next
  fix a assume "a \<in> A"

  then show "card {e \<in> insert {i,j} M. a \<in> e} \<le> 1"
  proof (cases "a = j")
    case True
    with \<open>j \<notin> Vs M\<close> have "{e \<in> insert {i, j} M. a \<in> e} = {{i,j}}"
      by (auto simp: vs_member_intro)

    then show ?thesis
      by simp
  next
    case False
    with \<open>a \<in> A\<close> \<open>i \<notin> A\<close> have *: "{e \<in> insert {i,j} M. a \<in> e} = {e \<in> M. a \<in> e}"
      by auto

    with \<open>a \<in> A\<close> \<open>one_sided_matching G M A\<close> show ?thesis
      unfolding one_sided_matching_def
      by simp
  qed
qed

lemmas matching_partner_eqI = doubleton_in_matching(2)

lemma empty_is_graph_matching: "graph_matching G {}"
  using matching_empty by blast

lemma (in graph_abs) matching_card_vs':
  assumes "matching G"
  shows "card G = card (Vs G) / 2"
  using assms by(simp add: matching_card_vs[symmetric])

lemma neighbours_of_Vs_in_matching_singl:
  assumes "x \<in> Vs M"
  assumes "matching M"
  assumes" M \<subseteq> G"
  assumes "graph_invar G"
  shows "\<exists> v. (neighbours_of_Vs M {x}) = {v}"
proof -
  have "\<exists>!e. e \<in> M \<and> x \<in> e"  using matching_def2 assms(2) assms(1)  by metis
  then obtain e where e: " e \<in> M \<and> x \<in> e" by auto
  then have x_one_edge:"\<forall> e' \<in> M. e' \<noteq> e \<longrightarrow> x \<notin> e'" 
    using \<open>\<exists>!e. e \<in> M \<and> x \<in> e\<close> by blast
  have "\<exists>v. (\<exists> e\<in>M. x \<in> e \<and> v\<in>e \<and> x \<noteq> v)"
    by (metis assms(3) assms(4) dblton_graphE dblton_graph_subset e insertCI)
  then obtain v where "(\<exists> e\<in>M. x\<in> e \<and> v \<in> e \<and> x \<noteq> v)" by auto
  have "\<forall>v'. (\<exists> e\<in>M. x\<in> e \<and> v'\<in>e \<and> x \<noteq> v') \<longrightarrow> v = v'"
    by (metis \<open>\<exists>e\<in>M. x \<in> e \<and> v \<in> e \<and> x \<noteq> v\<close> assms(3) assms(4) dblton_graphE dblton_graph_subset
              insertE singletonD x_one_edge) 
  then have "\<exists>!v. \<exists>e\<in>M. x \<in> e \<and> v \<in> e \<and> x \<noteq> v" 
    using \<open>\<exists>e\<in>M. x \<in> e \<and> v \<in> e \<and> x \<noteq> v\<close> by blast
  then show ?thesis unfolding neighbours_of_Vs_def 
    by auto
qed

lemma vertex_not_in_source_then_not_neighbours_of_Vs:
  assumes "matching M"
  assumes "{x, y} \<in> M"
  assumes "x \<notin> X"
  shows "y \<notin> neighbours_of_Vs M X"
proof(rule ccontr)
  assume "\<not> y \<notin> neighbours_of_Vs M X"
  then show False 
    unfolding neighbours_of_Vs_def 
    by (smt (verit) assms insert_iff matching_unique_match mem_Collect_eq singleton_iff)
qed

lemma card_ther_vertex:
  assumes "graph_invar G"
  assumes "matching M"
  assumes" M \<subseteq> G"
  assumes "X \<subseteq> Vs M"
  shows" card X = card (neighbours_of_Vs M X)" 
proof -
  have "finite X" using assms(1)
    by (meson Vs_subset assms(3) assms(4) finite_subset)
  show ?thesis
    using \<open>finite X\<close> \<open>X \<subseteq> Vs M\<close>
  proof (induct X)
    case empty
    then show ?case 
      by (simp add: neighbours_of_Vs_def)
  next
    case (insert x F)  
    then have "\<exists>v. neighbours_of_Vs M {x} = {v}"
      using neighbours_of_Vs_in_matching_singl assms(1-3) by fastforce
    then obtain v where v:"neighbours_of_Vs M {x} = {v}" by auto
    then obtain e where e: "e \<in> M \<and> x \<in> e \<and> v \<in> e \<and> x \<noteq> v" 
      unfolding neighbours_of_Vs_def by auto
    then have "e = {x, v}" 
      using assms(1) assms(3) by fastforce
    then have "v \<notin> neighbours_of_Vs M F" 
      by (metis assms(2) e insert.hyps(2) vertex_not_in_source_then_not_neighbours_of_Vs)
    then have  "neighbours_of_Vs M {x} \<inter> neighbours_of_Vs M F = {}" 
      by (simp add: v)
    then have card_sum_u: "card (neighbours_of_Vs M {x}) + card( neighbours_of_Vs M F) = 
                  card (neighbours_of_Vs M {x} \<union> neighbours_of_Vs M F)"
      by (metis finite_neighbours_of_Vs assms(1) assms(3) card_Un_disjoint)
    have " neighbours_of_Vs M (insert x F) = neighbours_of_Vs M F \<union> neighbours_of_Vs M {x}"
      by (meson neighbours_of_Vs_insert)
    then have 3: "card (neighbours_of_Vs M (insert x F)) = card (neighbours_of_Vs M F) + 1"
      using v card_sum_u  by simp
    have "card (insert x F) = card F + 1"
      by (simp add: insert.hyps(1) insert.hyps(2)) 
    then show  "card (insert x F) = card (neighbours_of_Vs M (insert x F))" using 3
      by (metis insert.hyps(3) insert.prems insert_subset)
  qed
qed

subsection \<open>Augmenting and Alternating Paths\<close>

definition matching_augmenting_path where
  "matching_augmenting_path M p = ( 
    (length p \<ge> 2) \<and>
     alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path p) \<and> 
     hd p \<notin> Vs M \<and> last p \<notin> Vs M)"

abbreviation "graph_augmenting_path G M p \<equiv>
  path G p \<and> distinct p \<and> matching_augmenting_path M p"

lemma matching_augmenting_pathI:
 "\<lbrakk>length p \<ge> 2; alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path p); hd p \<notin> Vs M; last p \<notin> Vs M\<rbrakk>
  \<Longrightarrow> matching_augmenting_path M p"
  by(auto simp add: matching_augmenting_path_def)

lemma matching_augmenting_path_feats:
  assumes "matching_augmenting_path M p"
  shows "(length p \<ge> 2)" "alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path p)"
         "hd p \<notin> Vs M" "last p \<notin> Vs M"
  using assms
  by (auto simp: matching_augmenting_path_def)

lemma graph_augmenting_path_feats:
  assumes "graph_augmenting_path G M p"
  shows "matching_augmenting_path M p" "distinct p" "path G p"
  using assms
  by auto

lemma matching_augmenting_pathE:
  "\<lbrakk>matching_augmenting_path M p; 
      \<lbrakk>(length p \<ge> 2); alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path p);
       hd p \<notin> Vs M; last p \<notin> Vs M\<rbrakk> \<Longrightarrow> P\<rbrakk> 
   \<Longrightarrow> P"
  by (auto simp: matching_augmenting_path_def)

lemma matching_augmenting_path_last_edge_nin:
  assumes "matching_augmenting_path M p"
  shows "last (edges_of_path p) \<notin> M"
proof- 
  have "last p \<in> last (edges_of_path p)"
    using assms
    by (simp add: matching_augmenting_path_def last_v_in_last_e)
  then show ?thesis
    using matching_augmenting_path_feats(4)[OF assms]
    by (fastforce simp: Vs_def)
qed

lemma matching_augmenting_path_odd_length:
  assumes "matching_augmenting_path M p"
  shows "odd (length (edges_of_path p))"
  using matching_augmenting_path_last_edge_nin[OF assms] assms
  by (fastforce simp add: eval_nat_numeral Suc_le_length_iff edges_of_path_length'[where p = p]
                          matching_augmenting_path_last_edge_nin
                   dest!: alternating_list_even_last
                   elim!: matching_augmenting_pathE)

lemma symmetric_difference_assoc: "A \<oplus> (B \<oplus> C) = (A \<oplus> B) \<oplus> C"
  unfolding symmetric_diff_def by blast

lemma symm_diff_is_matching:
  assumes 
    "alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path p)"
    "matching M"
    "hd p \<notin> Vs M"
    "length p \<ge> 2 \<and> even (length p) \<Longrightarrow> last p \<notin> Vs M"
    "distinct p"
  shows "matching (M \<oplus> set (edges_of_path p))"
  using assms
proof(induction p arbitrary: M rule: induct_list0123)
  case nil
  then show ?case by (simp add: symmetric_diff_def)
next
  case list1
  then show ?case by (simp add: symmetric_diff_def)
next
  case (list2 x y)
  have "\<nexists>e. e \<in> M \<and> x \<in> e"
    using Vs_def list2.prems(3)
    by fastforce
  moreover have "\<nexists>e. e \<in> M \<and> y \<in> e"
    using Vs_def list2.prems(4)
    by fastforce
  moreover have "z \<in> Vs (insert {x, y} M) \<Longrightarrow> z = x \<or> z = y \<or> z \<in> Vs M"
    for z
    by(auto simp: Vs_def)
  ultimately have "matching (insert {x, y} M)"
    using list2.prems(2)
    by (simp add: matching_def)
  moreover have "{x, y} \<notin> M" using \<open>\<nexists>e. e \<in> M \<and> x \<in> e\<close>
    by blast
  ultimately show ?case 
    by (simp add: symmetric_diff_def)
next
  case (list3 x y z ps)
  from list3.prems(1)
  have "{x, y} \<notin> M" "{y, z} \<in> M"
    by (simp_all add: alt_list_step)

  define M' where "M' = insert {x, y} (M - {{y, z}})"
  have M'symmdiff: "M' = M \<oplus> {{x, y}, {y, z}}" unfolding symmetric_diff_def M'_def
    using \<open>{x, y} \<notin> M\<close> \<open>{y, z} \<in> M\<close>
    by fastforce

  have xysymmdiff: "set (edges_of_path (x#y#z#ps)) = {{x, y}, {y, z}} \<oplus> set (edges_of_path (z # ps))"
    using list3.prems(5) v_in_edge_in_path
    by (fastforce simp: symmetric_diff_def)

  have "alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path (z # ps))"
    using list3.prems(1)
    by (simp add: alt_list_step)

  hence altlistM': "alt_list (\<lambda>e. e \<notin> M') (\<lambda>e. e \<in> M') (edges_of_path (z # ps))"
    apply (rule alt_list_cong)
    using list3.prems(5) v_in_edge_in_path
    by (force simp: M'_def)+

  have "x \<notin> Vs (M - {{y, z}})"
    using \<open>{y, z} \<in> M\<close> list3.prems(3)
    by (simp add: Vs_def)
  moreover have "y \<notin> Vs (M - {{y, z}})"
    using \<open>{y, z} \<in> M\<close> list3.prems(2)
    by (force simp: Vs_def matching_def)
  ultimately have "matching M'"
    by (simp add: matching_delete matching_insert list3.prems(2) M'_def)

  have "z \<notin> Vs M'"
  proof(rule ccontr, subst (asm) not_not)
    assume "z \<in> Vs M'"
    hence "z \<in> Vs (M - {{y, z}})"
      using list3.prems(5)
      by (fastforce simp: M'_def Vs_def)
    then obtain e where "z \<in> e" "e \<in> M" "e \<noteq> {y, z}"
      by (auto simp: Vs_def)
    thus False
      using \<open>{y, z} \<in> M\<close> list3.prems(2)
      by (force simp: matching_def)
  qed
  moreover have "last (z # ps) \<notin> Vs M'"
    if "2 \<le> length (z # ps)" "even (length (z # ps))"
  proof(rule ccontr, subst (asm) not_not)
    assume "last (z # ps) \<in> Vs M'"
    hence "last (z # ps) \<in> Vs M \<or> last (z # ps) \<in> {x, y}"
      by (force simp: M'_def Vs_def)
    then have "last (z # ps) \<in> {x, y}"
      using list3.prems(4) that
      by force
    thus False
      using list3.prems(5) last_in_set
      by (auto simp: distinct_length_2_or_more split: if_splits)
  qed
  moreover note \<open>matching M'\<close> altlistM' list3.prems(5)
  ultimately have "matching (M' \<oplus> set (edges_of_path (z # ps)))"
    using list3.IH(2)
    by fastforce
  then show ?case
    by(simp only: M'symmdiff xysymmdiff symmetric_difference_assoc)
qed

lemma condition_for_greatness:
  assumes "card (s \<inter> t) < card (s - t)" "finite t"
  shows "card t < card (t \<oplus> s)"
proof-
  have tsstinter: "(t - s) \<inter> (s - t) = {}" by blast

  have "card t = card ((t - s) \<union> (t \<inter> s))"
    by (simp add: Un_Diff_Int)
  also have "... = card (t - s) + card (t \<inter> s)"
    using assms(2)
    by (auto intro!: card_Un_disjoint)
  also have "... < card (t - s) + card (s - t)"
    by (simp add: assms(1) inf.commute)
  also have "... = card ((t - s) \<union> (s - t))"
    using assms order_less_trans
    by (fastforce intro!: card_Un_disjoint[symmetric])
  also have "... = card (t \<oplus> s)"
    by (simp add: symmetric_diff_def)
  finally show ?thesis .
qed

lemma condition_for_same_card:
  assumes "card (s \<inter> t) = card (s - t)" "finite t" "finite s"
  shows "card t = card (t \<oplus> s)"
proof-
  have tsstinter: "(t - s) \<inter> (s - t) = {}" by blast

  have "card t = card ((t - s) \<union> (t \<inter> s))"
    by (simp add: Un_Diff_Int)
  also have "... = card (t - s) + card (t \<inter> s)"
    using assms(2)
    by (auto intro!: card_Un_disjoint)
  also have "... = card (t - s) + card (s - t)"
    by (simp add: assms(1) inf.commute)
  also have "... = card ((t - s) \<union> (s - t))"
    using assms
    by(subst card_Un_disjoint[symmetric]) auto
  also have "... = card (t \<oplus> s)"
    by (simp add: symmetric_diff_def)
  finally show ?thesis .
qed

text\<open>An augmenting path can be used to construct a larger matching.\<close>

lemma distinct_length_filter_neg: 
  assumes "distinct xs"
 shows "card (set xs - M) = length (filter (\<lambda>e. e \<notin> M) xs)" (is "?lhs = ?rhs")
proof-
  have "?lhs = card (set (filter  (\<lambda>e. e \<notin> M) xs))"
    by (auto intro!: arg_cong[where f = card])
  also have "... = length (remdups (filter (\<lambda>e. e \<notin> M) xs))"
    by (auto simp: length_remdups_card_conv)
  also have "... = ?rhs"
    using \<open>distinct xs\<close>
    by auto
  finally show ?thesis
    by simp
qed

lemma 
  assumes "matching_augmenting_path M p"
  assumes "distinct p"
  assumes "finite M"
  shows new_matching_bigger: "card M < card (M \<oplus> set (edges_of_path p))"
  and new_matching_plus_one: "card M +1 = card (M \<oplus> set (edges_of_path p))"
proof-
  have dist: "distinct (edges_of_path p)"
    using assms(2)
    by (simp add: distinct_edges_of_vpath)
  have "length (filter (\<lambda>e. e \<notin> M) (edges_of_path p)) = length (filter (\<lambda>e. e \<in> M) (edges_of_path p)) + 1"
    using alternating_eq_iff_odd assms(1) matching_augmenting_path_feats(2) matching_augmenting_path_odd_length
    by blast
  then have "card (set (edges_of_path p) - M) = card (set (edges_of_path p) \<inter> M) + 1"
    using distinct_length_filter_neg[OF dist] distinct_length_filter[OF dist]
    by (simp add: inf_commute)
  then show "card M < card (M \<oplus> set (edges_of_path p))"
            "card M +1 = card (M \<oplus> set (edges_of_path p))"
    using condition_for_greatness[OF _ assms(3)] 
    by (auto simp add: card_Int_Diff assms(3) card_Un_disjoint disjoint_iff inf_sup_aci(1)
                       symmetric_diff_def)
qed

abbreviation "alt_path M p \<equiv> alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path p)"
abbreviation "rev_alt_path M p \<equiv> alt_list (\<lambda>e. e \<in> M) (\<lambda>e. e \<notin> M) (edges_of_path p)"

lemma matching_augmenting_path_rev:
  assumes "matching_augmenting_path M p"
  shows "matching_augmenting_path M (rev p)"
  using assms
proof-
  have "hd p = last (rev p)" "last p = hd (rev p)"
    using matching_augmenting_path_feats[OF assms]
    by (auto simp: Suc_le_length_iff hd_rev last_rev numeral_2_eq_2 split: if_splits)
  moreover have "alt_path M (rev p)"
    using alt_list_rev[OF matching_augmenting_path_feats(2)[OF assms] matching_augmenting_path_odd_length[OF assms]]
    by (auto simp: edges_of_path_rev[symmetric])
  ultimately show ?thesis
    using length_rev matching_augmenting_path_feats[OF assms] 
    by(auto simp: matching_augmenting_path_def split: if_splits)
qed

lemma aug_paths_are_even:
  assumes "matching_augmenting_path M p"
  shows "even (length p)"
  using assms
  unfolding matching_augmenting_path_def
  by (metis assms edges_of_path_length' even_add length_greater_0_conv
            matching_augmenting_path_odd_length odd_one odd_pos)

lemma odd_alt_path_rev:
  assumes odd_lens: "odd (length p1)" "length p1 \<ge> 2" and alt_paths: "alt_path (-M) p1"
  shows "alt_path M (rev p1)"
    unfolding edges_of_path_rev[symmetric]
    apply (intro alt_list_rev_even)
    subgoal using alt_paths by simp
    subgoal using odd_lens
      by (simp add: edges_of_path_length)
    done

lemma even_alt_path_rev:
  assumes even_lens: "even (length p1)" "length p1 \<ge> 2" and alt_paths: "alt_path M p1"
  shows "alt_path M (rev p1)"
  using  assms
    unfolding edges_of_path_rev[symmetric]
    apply (intro alt_list_rev)
    subgoal using alt_paths by simp
    subgoal using even_lens
      by (auto simp add: edges_of_path_length)
    done

lemma alt_path_cons_odd:
  assumes "odd (length p)" "alt_path M (v # p)"
  shows "alt_path (-M) p" "{v, hd p} \<notin> M"
  using assms
  by(cases p; auto simp add: alt_list_step alt_list_empty)+

lemma nin_M_alt_path:
  "{v, hd vs} \<notin> M \<Longrightarrow> alt_path (-M) vs \<Longrightarrow> alt_path M (v # vs)"
  by(cases vs; simp add: alt_list_step alt_list_empty)

lemma alt_path_sym_diff_rev_alt_path:
  assumes "M \<oplus> M' = set (edges_of_path p)"
  assumes "alt_path M p"
  shows "rev_alt_path M' p"
  using assms
  by (auto intro: alt_list_cong simp: symmetric_diff_def)

lemma rev_alt_path_sym_diff_alt_path:
  assumes "M \<oplus> M' = set (edges_of_path p)"
  assumes "rev_alt_path M p"
  shows "alt_path M' p"
  using assms
  by (auto intro: alt_list_cong simp: symmetric_diff_def)

lemma union_of_matchings_alt_list:
  assumes "matching M" "matching M'" "epath (M \<union> M') x p y" "hd p \<notin> M" "distinct p"
  shows "alt_list (\<lambda> e. e \<in> M' \<and> e \<notin> M) (\<lambda> e. e \<in> M \<and> e \<notin> M') p"
  using assms
proof(induction p arbitrary: M M' x )
  case (Cons e p)
  note IH = this
  obtain z where z: "e = {x, z}" "z \<noteq> x"
    using Cons.prems(3) by auto
  show ?case 
  proof(cases p)
    case Nil
    then show ?thesis 
      using IH(4,5) by (auto intro!: alt_list_singleton)
  next
    case (Cons e' pp)
     hence "e \<in> M'" 
      using IH(4,5) by auto
    moreover have epath_z: "epath (M' \<union> M) z p y" 
      using  IH(4)  z(1) by(auto simp add: doubleton_eq_iff  sup_commute)
    moreover have "hd p \<notin> M'"
    proof-
      have "hd p \<in> M \<or> hd p \<in> M'" 
        using IH(4) local.Cons by auto
      moreover have "hd p \<in> M' \<Longrightarrow> False"
      proof(goal_cases)
        case 1
        have "e \<noteq> e'" 
          using IH(6) local.Cons by force
        moreover have "z \<in> e \<inter> e'" 
          using epath_z local.Cons z(1) by fastforce
        ultimately show False 
          using "1" IH(3) \<open>e \<in> M'\<close> Cons by(auto elim!: matchingE)
      qed
      ultimately show ?thesis 
        by auto
    qed
    ultimately show ?thesis 
      using IH(5,6)
      by(auto intro!: alt_list.intros(2) IH(1)[of _ _ z] IH(2,3))
  qed
qed (auto intro: alt_list.intros(1))

lemma
  assumes "matching M" "matching M'" "path (M \<union> M') p" "length p \<ge> 2" "hd p \<notin> Vs M"
          "dblton_graph M" "dblton_graph M'" "distinct p"
  shows  union_of_matchings_alt_path: "alt_path M p" (is ?thesis1)
  and union_of_matchings_alt_list_M'_M: "alt_list (\<lambda>e. e \<in> M' \<and> e \<notin> M) (\<lambda>e. e \<in> M \<and> e \<notin> M') (edges_of_path p)"
       (is ?thesis2)
proof-
  show alt_list_M'_M:"alt_list (\<lambda>e. e \<in> M' \<and> e \<notin> M) (\<lambda>e. e \<in> M \<and> e \<notin> M') (edges_of_path p)"
    using assms(4,5)  hd_edge_in_hd_vert_in
    by(auto intro!: union_of_matchings_alt_list[OF assms(1,2), of "hd p" _ "last p"]
                       walk_betw_imp_epath nonempty_path_walk_between 
          simp add: assms(3,6,7,8) dblton_graph_union  distinct_edges_of_vpath)
  show ?thesis1
proof(rule alt_list_from_indices, goal_cases)
  case (2 i)
  show ?case
    using "2"(1,2) alt_list_M'_M alternating_list_odd_index by blast
next
  case (1 i)
  show ?case
  proof(cases i)
    case 0
    then show ?thesis 
      using "1"(1) assms(4,5) alt_list_M'_M hd_edge_in_hd_vert_in[OF assms(4), of M]
      by (auto simp add: hd_conv_nth)
  next
    case (Suc nat)
    hence "(edges_of_path p ! nat) \<in> M"
      using "1"(1,2) Suc_lessD alt_list_M'_M alternating_list_odd_index even_Suc by blast
    moreover have "(edges_of_path p ! nat) \<noteq> (edges_of_path p ! i)" 
      using "1"(1) Suc distinct_edges_of_vpath[OF assms(8)] nth_eq_iff_index_eq
      by force
    moreover have "p ! i \<in> (edges_of_path p ! nat) \<inter> (edges_of_path p ! i)" 
      using "1"(1) Suc
      by(auto simp add: edges_of_path_length edges_of_path_index)
    ultimately show ?thesis
      using assms(1) by(auto elim!: matchingE)
  qed 
qed
qed

lemma rematch_odd_alt_path_same_card:
  assumes "matching M" "alt_path M p" "odd (length p)" "distinct p"
  shows   "card (M \<oplus> set (edges_of_path p)) = card M"
proof(cases "finite M")
  case False
  show ?thesis
    by (simp add: False symmetric_diff_def)
next
  case True
  have dist: "distinct (edges_of_path p)"
    using assms(4)
    by (simp add: distinct_edges_of_vpath)
  have "length (filter (\<lambda>e. e \<notin> M) (edges_of_path p))
       = length (filter (\<lambda>e. e \<in> M) (edges_of_path p))"
    using assms(2) 
    by (auto simp add: alternating_eq_iff_even assms(3) edges_of_path_length)
  then have "card (set (edges_of_path p) - M) = card (set (edges_of_path p) \<inter> M)"
    using distinct_length_filter_neg[OF dist] distinct_length_filter[OF dist]
    by (simp add: inf_commute)
  thus ?thesis
    using True
    by(auto intro!: condition_for_same_card[symmetric])
qed

lemma rematch_atl_path_matching_change:
  assumes "matching M" "alt_path M p" "distinct p"
  shows "M \<oplus> set (edges_of_path p) = 
         M - {(edges_of_path p)! i | i . odd i \<and> i < length p - 1} 
         \<union> {(edges_of_path p)! i | i . even i \<and> i < length p - 1}" (is "?M' = M - ?rev \<union> ?add")
proof(rule set_eqI, goal_cases)
  case (1 e)
  show ?case 
  proof(cases "e \<in> set (edges_of_path p)")
    case False
    moreover have "e \<notin> ?rev" "e \<notin> ?add"
      using False 
      by (auto simp add: edges_of_path_length)
    ultimately show ?thesis
      by (auto simp add: symmetric_diff_def)
  next
    case True
    then obtain i where i: "e = (edges_of_path p) ! i" "i < length p -1"
      using edges_of_path_length[of p] by(auto simp add: in_set_conv_nth)
    have rev_add_disjoint:"?rev \<inter> ?add = {}" 
      by (auto simp add: assms(3) distinct_edges_of_vpath edges_of_path_length nth_eq_iff_index_eq)
    show ?thesis
    proof(cases i rule: parity_cases)
      case even
      have "e \<in> ?add"
        using even(1) i(1,2) by blast
      moreover hence "e \<notin> ?rev"
        using rev_add_disjoint by auto
      moreover have "e \<notin> M" 
        using assms(2) edges_of_path_length[of p] even(1) i(1,2)
        by(intro alternating_list_even_index[of "\<lambda>e. e \<notin> M" "\<lambda>e. e \<in> M" "edges_of_path p" i, 
                           simplified i(1)[symmetric]])
           auto
      ultimately show ?thesis 
        using True
        by(auto simp add: symmetric_diff_def i(1))
    next
      case odd
      have "e \<in> ?rev"
        using odd(1) i(1,2) by blast
      moreover hence "e \<notin> ?add"
        using rev_add_disjoint by auto
      moreover have "e \<in> M" 
        using assms(2) edges_of_path_length[of p] odd(1) i(1,2)
        by(intro alternating_list_odd_index[of "\<lambda>e. e \<notin> M" "\<lambda>e. e \<in> M" "edges_of_path p" i, 
                           simplified i(1)[symmetric]])
           auto
      ultimately show ?thesis 
        using True
        by(auto simp add: symmetric_diff_def i(1))
    qed
  qed 
qed

lemma rematch_atl_path_verts_matched:
  assumes "matching M" "alt_path M p" "distinct p"
  shows   "(if even (length p) then set p else set (butlast p)) 
            \<subseteq> Vs (M \<oplus> set (edges_of_path p))"
proof-
  have "p = [] \<Longrightarrow> ?thesis" by simp
  moreover have "p = [x] \<Longrightarrow> ?thesis" for x by simp
  moreover have "p = x#y#q \<Longrightarrow> ?thesis" for x y q
  proof(rule, goal_cases)
    case (1 z)
    note one = this
    show ?case
    proof(cases "x = z")
      case True
      then show ?thesis 
        using  "1"(1) assms(2)  
        by(auto intro!: edges_are_Vs[of z y] simp add:  alt_list_step symmetric_diff_def)
    next
      case False
      note false = this
      obtain i where i_prop: "p!i = z" "i < length p"
        using "1"(2) by (cases " even (length p)") (auto simp add: in_set_conv_nth nth_butlast)
      have i_gtr_0:"i > 0"
        using "1"(1) \<open>p ! i = z\<close> false nth_Cons_0 by fastforce
      have edge_i_minus_1:"edges_of_path p ! (i-1) = {p!(i-1), p! i}"
          using edges_of_path_index[of "i-1" p]  Suc_pred' i_gtr_0 i_prop(2) by presburger
      show ?thesis
      proof(cases "even i")
        case True
        have "i + 1 < length p"
        proof(rule ccontr, goal_cases)
          case 1
          hence "i + 1 = length p" 
            using i_prop(2) by (auto dest!: linorder_class.leI)
          hence "z = last p"
            using  i_gtr_0 i_prop(1,2) by (auto simp add: last_conv_nth one(1))
          moreover have "odd (length p)" 
            using True \<open>i + 1 = length p\<close> by presburger
          moreover hence "z \<in> set (butlast p)" 
            using one(2) by fastforce
          ultimately show ?case 
            using  assms(3) one(1) false append_butlast_last_id[of p] 
                assms(3) distinct_append[of "butlast p" "[last p]"]   
            by auto
        qed
        have edge_i: "edges_of_path p ! i = {p!(Suc i), p! i}"
          using \<open>i + 1 < length p\<close> edges_of_path_index by auto
        moreover have "edges_of_path p ! i \<notin> M"
          using assms(2) True  \<open>i + 1 < length p\<close> edges_of_path_length[of p]
          by(intro alternating_list_even_index[of "(\<lambda>e. e \<notin> M)" "(\<lambda>e. e \<in> M)" "(edges_of_path p)" i])
            auto
        moreover have "edges_of_path p ! i \<in> set (edges_of_path p)"
          using \<open>i + 1 < length p\<close> edges_of_path_length[of p]
          by simp
        ultimately have "edges_of_path p ! i \<in> M \<oplus> set (edges_of_path p)"
          by(auto simp add: symmetric_diff_def)
        thus ?thesis 
          using edge_i i_prop(1) by blast
      next
        case False
        hence "edges_of_path p ! (i-1) \<notin> M"
          using "1"(1)  assms(2) i_gtr_0 i_prop(2)
          by(intro alternating_list_even_index[of "(\<lambda>e. e \<notin> M)"
                             "(\<lambda>e. e \<in> M)" "(edges_of_path p)" "i - 1"])
            (auto simp add: edges_of_path_length)
        moreover have "edges_of_path p ! (i-1) \<in> set (edges_of_path p)"
          using  i_gtr_0 i_prop(2)
          by(auto simp add: in_set_conv_nth edges_of_path_length intro!: exI[of _ "i-1"])
        ultimately have "edges_of_path p ! (i-1) \<in> M \<oplus> set (edges_of_path p)"
          by(auto simp add: symmetric_diff_def)
        thus ?thesis 
          using edge_i_minus_1 i_prop(1) by blast
      qed
    qed
  qed
  ultimately show ?thesis
    by(cases p rule: list_cases3) auto
qed

lemma verts_of_even_eges:
      "Vs {edges_of_path p ! i | i. i < length p - 1 \<and> even i} = 
       (if even (length p) then set p else set (butlast p))" (is ?ths1)
  and verts_of_odd_edges:
      "Vs {edges_of_path p ! i | i. i < length p - 1 \<and> odd i} = 
       (if even (length p) then set (butlast (tl p)) else set (tl p))" (is ?ths2)
proof-
  have "?ths1 \<and> ?ths2"
  proof(induction p rule: edges_of_path.induct)
    case 1
    then show ?case by auto
  next
    case (2 v)
    then show ?case by auto
  next
    case (3 v v' l)
    note IH = conjunct1[OF this] conjunct2[OF this]
    show ?case
    proof(rule, goal_cases)
      case 1
      have edges_are: "{edges_of_path (v # v' # l) ! i |i. i < length (v # v' # l) - 1 \<and> even i} = 
            insert {v, v'} {edges_of_path  (v' # l) ! i |i. i < length (v'#l) - 1 \<and> odd i}"
      proof(rule, all \<open>rule\<close>, goal_cases)
        case (1 e)
        then obtain i where i: "i < length (v # v' # l) - 1" "even i" 
                            "e = edges_of_path (v # v' # l) ! i" by auto
        show ?case 
        proof(cases "i = 0")
          case False
          thus ?thesis
            using False i(1)
            by(auto intro!: exI[of _ "i - 1"] simp add: i(3,2))
        qed (simp add: i(3))
      next
        case (2 e)
        show ?case
        proof(cases "e = {v, v'}")
          case True
          then show ?thesis 
            by (auto intro!: exI[of _ 0])
        next
          case False
          then obtain i where "e = edges_of_path (v' # l) ! i" "i < length (v' # l) - 1" "odd i"
            using 2 by auto
          then show ?thesis 
            by(auto intro!: exI[of _ "Suc i"])
        qed
      qed
      show ?case 
        unfolding edges_are vs_insert IH(2)
        by (auto dest: in_set_butlastD)
    next
      case 2
      have edges_are: "{edges_of_path (v # v' # l) ! i |i. i < length (v # v' # l) - 1 \<and> odd i} = 
                       {edges_of_path  (v' # l) ! i |i. i < length (v'#l) - 1 \<and> even i}"
      proof(rule, all \<open>rule\<close>, goal_cases)
        case (1 e)
        then obtain i where i: "i < length (v # v' # l) - 1" "odd i" 
                            "e = edges_of_path (v # v' # l) ! i" by auto
        show ?case 
        proof(cases "i = 0")
          case False
          thus ?thesis
            using False i(1)
            by(auto intro!: exI[of _ "i - 1"] simp add: i(3,2))
        next
          case True
          thus ?thesis
            using i(2) by blast
        qed
      next
        case (2 e)
          then obtain i where "e = edges_of_path (v' # l) ! i" "i < length (v' # l) - 1" "even i"
            using 2 by auto
          then show ?case
            by(auto intro!: exI[of _ "Suc i"])
        qed
      show ?case 
        unfolding edges_are vs_insert  IH(1)
        by (auto dest: in_set_butlastD)
    qed
  qed
  thus ?ths1 ?ths2
    by auto
qed

lemma rematch_atl_path_Vs_change:
  assumes "matching M" "alt_path M p" "distinct p" "length p \<ge> 2"
  shows "Vs (M \<oplus> set (edges_of_path p)) = 
         (if even (length p) then {hd p, last p} \<union> (Vs M) else insert (hd p) (Vs M) - {last p})"
         (is "Vs ?left = ?right")
proof-
  note left_simp = rematch_atl_path_matching_change[OF assms(1-3)]
  show ?thesis
proof(rule, all \<open>rule\<close>, goal_cases)
  case (1 x)
  then obtain e where e: "e \<in> ?left" "x \<in> e" 
    using vs_member[of x] by auto
  show ?case
  proof(cases rule: UnE[OF e(1)[simplified left_simp]])
    case 1
    note one = this
    show ?thesis 
    proof(cases "even (length p)")
      case True
      then show ?thesis 
        using "1" e(2) by auto
    next
      case False
      have "x = last p \<Longrightarrow> False"
      proof(goal_cases)
        case 1
        have "length p - 2 < length (edges_of_path p)" 
          using assms(4) edges_of_path_length[of p] 
          by simp
        hence a1: "edges_of_path p ! (length p - 2) = {p ! (length p-2) , p ! (length p -1)}"
          using assms(4)
          by(subst edges_of_path_index[of "length p-2" p])
            (auto dest!: Suc_diff_le)
        have last_edge_is: "edges_of_path p ! (length p - 2) = {last p, last (butlast p)}" 
          using assms(4)
        proof(subst a1, subst last_conv_nth, force, subst last_conv_nth, goal_cases)
          case 1
          thus ?case
            by(cases p) auto
        next
          case 2
          have "length (butlast p) - 1 = length p - 2" 
            by fastforce
          moreover hence "butlast p ! (length p - 2) = p ! (length p - 2)"
            using edges_of_path_length[of p]  assms(4)
            by (auto simp add: nth_butlast)
          ultimately show ?case
            by auto
        qed
        moreover have "edges_of_path p ! (length p - 2) \<in> M" 
          using assms False \<open>length p - 2 < length (edges_of_path p)\<close>
          by(intro alternating_list_odd_index[of "\<lambda>e. e \<notin> M" "\<lambda>e. e \<in> M" "edges_of_path p"])
            auto
        ultimately have "{last p, last (butlast p)} \<in> M" 
          by simp
        moreover have "e \<noteq> {last p, last (butlast p)}" 
          using  \<open>length p - 2 < length (edges_of_path p)\<close> calculation e(1) last_edge_is nth_mem
              symm_diff_mutex[of e M "set (edges_of_path p)"]
          by force
        ultimately show ?case
          using  "1" assms(1) e(2) one
          by(auto elim!: matchingE)
      qed
      from False this show ?thesis 
        using "1" e(2) by auto
    qed
  next
    case 2
    then obtain i where i: "e = edges_of_path p ! i" "even i" "i < length p - 1"
      by auto
    have e_is: "e = {p!i, p! Suc i}" 
      using edges_of_path_index i(1,3) less_diff_conv by auto
    have if_i_0:"i = 0 \<Longrightarrow> x = hd p \<or> x = hd (tl p)"
      using i e(2) assms(4) by(cases p rule: list_cases3)(auto simp add: e_is)
    show ?thesis
    proof(cases "x = p!i")
      case True
      note true = this
      then show ?thesis 
      proof(cases "i = 0")
        case True
        hence "x = hd p" 
          using  assms(4) true
          by(cases p rule: list_cases3) auto
        then show ?thesis 
          using assms(4,3)
          by(cases p rule: list_cases3) auto
      next
        case False
        hence "edges_of_path p ! (i-1) = {p! (i-1), p!i}" 
          using edges_of_path_index[of "i-1" p] i(3) 
          by auto
        moreover have "edges_of_path p ! (i-1) \<in> M"
          using assms False i(2,3)
          by(intro alternating_list_odd_index[of "\<lambda>e. e \<notin> M" "\<lambda>e. e \<in> M" "edges_of_path p" "i-1"])
            (auto simp add: edges_of_path_length)
        ultimately have "x \<in> Vs M"
          using true by blast
        moreover have "odd (length p) \<Longrightarrow> x \<noteq> last p"
          using true  assms(3,4) i(3)
          by(cases p rule: rev_cases)
           (auto simp add: in_set_conv_nth nth_append)
        ultimately show ?thesis  
          by auto
      qed
    next
      case False
      hence Fls: "x = p ! Suc i" 
        using e(2) e_is by blast
       have "Suc i < length p -1 \<Longrightarrow> edges_of_path p ! Suc i \<in> M"
          using assms Fls i(2,3)
          by(intro alternating_list_odd_index[of "\<lambda>e. e \<notin> M" "\<lambda>e. e \<in> M" "edges_of_path p" "Suc i"])
            (auto simp add: edges_of_path_length)
        moreover have "Suc i < length p -1 \<Longrightarrow> edges_of_path p ! Suc i = {p!Suc i, p ! Suc (Suc i)}"
          by(intro edges_of_path_index[of "Suc i" p]) simp
        ultimately have "Suc i < length p -1 \<Longrightarrow> x \<in> Vs M" 
          using Fls by blast
        moreover have "odd (length p) \<Longrightarrow> x \<noteq> last p" 
          using assms(3,4) i(2,3) by(cases p rule: rev_cases) (force simp add: Fls  nth_append)+
        moreover have "odd (length p) \<Longrightarrow> Suc i < length p -1" 
          using  i(2,3) odd_Suc_minus_one[of "length p"]
          by presburger
        moreover have "(Suc i < length p - Suc 0 \<Longrightarrow> False) \<Longrightarrow> x = last p"
          using Fls  Suc_lessI assms(4) i(3) last_conv_nth[of p] 
          by fastforce
        ultimately show ?thesis 
          using False i(3) Fls assms(4) by auto
      qed
    qed
  next
    case (2 x)
    thus ?case 
    proof(cases "x \<in> set p")
      case True
      have "x = hd p \<Longrightarrow> x \<in> Vs (M \<oplus> set (edges_of_path p))"
      proof(goal_cases)
        case 1 
        hence "x \<in> edges_of_path p ! 0"
          using assms(4) edges_of_path_index[of 0 p]
          by(cases p rule: list_cases3) auto
        moreover have "edges_of_path p ! 0 \<in>  set (edges_of_path p)"
          by (simp add: assms(4) edges_of_path_nempty)
        moreover have "edges_of_path p ! 0 \<notin> M" 
          using alternating_list_even_index assms(2,4) edges_of_path_nempty by blast 
        ultimately show ?thesis
          by (simp add: in_symmetric_diff_iff vs_member_intro)
      qed
      moreover have 
       "\<lbrakk>even (length p); x = last p\<rbrakk> \<Longrightarrow> x \<in> Vs (M \<oplus> set (edges_of_path p))"
      proof(goal_cases)
        case 1 
        hence "x \<in> edges_of_path p ! (length p - 2)"
          using assms(4) edges_of_path_index[of "length p - 2" p]
          by(cases p rule: list_cases3) (auto simp add: last_conv_nth)
        moreover have "edges_of_path p ! (length p - 2) \<in>  set (edges_of_path p)"
          using  assms(4) edges_of_path_length[of p]
          by simp
        moreover have "edges_of_path p ! (length p - 2) \<notin> M" 
          using assms(2,4) edges_of_path_nempty 1
          by(intro  alternating_list_even_index[of
                     "\<lambda>e. e \<notin> M" "\<lambda>e. e \<in> M" "edges_of_path p" "length p - 2"])
           (auto simp add: edges_of_path_length)
        ultimately show ?thesis
          by (simp add: in_symmetric_diff_iff vs_member_intro)
      qed
      moreover have 
        "\<lbrakk>x \<noteq> hd p; x \<noteq> last p \<or> odd (length p)\<rbrakk> \<Longrightarrow> x \<in> Vs (M \<oplus> set (edges_of_path p))"
      proof(goal_cases)
        case 1
        obtain i where "x \<in> edges_of_path p ! i" "even i" "i < length p - 1"
          using 1 non_last_vertex_or_even_list_in_even_edge[OF assms(3,4), of x] True 2
          by force
        thus ?case 
          unfolding rematch_atl_path_matching_change[OF assms(1-3)] 
          by auto
      qed
      ultimately show ?thesis
        using 2 by auto
    next
      case False
      hence "x \<in> Vs M"
        using assms(3,4) 2 
        by(cases "even (length p)", all \<open>cases p rule: list_cases3\<close>) auto
      then obtain e where e: "e \<in> M" "x \<in> e"
        using vs_member[of x] by auto
      moreover hence "e \<notin> set (edges_of_path p)"
        using False v_in_edge_in_path_gen by fastforce
      ultimately have "e\<in> M \<oplus> set (edges_of_path p)"
        by (simp add: symmetric_diff_def)
      thus ?thesis
        using e vs_member[of x] by auto
    qed
  qed
qed

subsection \<open>Matchings and Optimisation\<close>

subsubsection \<open>Cardinality Matching\<close>

definition maximal_matching :: "'a graph \<Rightarrow> 'a graph \<Rightarrow> bool" where
  "maximal_matching G M \<longleftrightarrow> matching M \<and> (\<forall>u v. {u,v} \<in> G \<longrightarrow> u \<in> Vs M \<or> v \<in> Vs M)"

definition max_card_matching :: "'a graph \<Rightarrow> 'a graph \<Rightarrow> bool" where
  "max_card_matching G M \<longleftrightarrow> M \<subseteq> G \<and> matching M \<and> (\<forall>M'. M' \<subseteq> G \<and> matching M' \<longrightarrow> card M' \<le> card M)"

definition perfect_matching :: "'a graph \<Rightarrow> 'a graph \<Rightarrow> bool" where
  "perfect_matching G M \<longleftrightarrow> M \<subseteq> G \<and> matching M \<and> Vs G = Vs M"

lemma maximal_matchingI:
  assumes "matching M"
  assumes "\<And>u v. {u,v} \<in> G \<Longrightarrow> u \<in> Vs M \<or> v \<in> Vs M"
  shows "maximal_matching G M"
  using assms
  unfolding maximal_matching_def
  by auto

lemma maximal_matching_edgeE:
  assumes "maximal_matching G M"
  assumes "{u,v} \<in> G"
  obtains e where "e \<in> M" "u \<in> e \<or> v \<in> e"
  using assms
  unfolding maximal_matching_def
  by (auto simp: vs_member)

lemma maximal_matchingD:
  assumes "maximal_matching G M"
  shows "matching M"
  using assms
  unfolding maximal_matching_def
  by auto

lemma maximal_matching_edgeD:
  assumes "maximal_matching G M"
  assumes "{u,v} \<in> G"
  shows "u \<in> Vs M \<or> v \<in> Vs M"
  using assms
  by (auto elim: maximal_matching_edgeE)

lemma not_maximal_matchingE:
  assumes "matching M"
  assumes "\<not>maximal_matching G M"
  obtains u v where "{u,v} \<in> G" "u \<notin> Vs M" "v \<notin> Vs M"
  using assms
  unfolding maximal_matching_def graph_abs_def
  by auto

lemma max_card_matchingI:
  assumes "M \<subseteq> G" "matching M"
  assumes "\<And>M'. M' \<subseteq> G \<Longrightarrow> matching M' \<Longrightarrow> card M' \<le> card M"
  shows "max_card_matching G M"
  using assms
  unfolding max_card_matching_def
  by blast

lemma max_card_matchingI':
  assumes "graph_matching G M"
  assumes "\<And>M'. graph_matching G M' \<Longrightarrow> card M' \<le> card M"
  shows "max_card_matching G M"
  using assms
  by(auto intro: max_card_matchingI)

lemma max_card_matchingD:
  assumes "max_card_matching G M"
  shows "M \<subseteq> G \<and> matching M \<and> (\<forall>M'. M' \<subseteq> G \<and> matching M' \<longrightarrow> card M' \<le> card M)"
  using assms
  unfolding max_card_matching_def
  by blast

lemma max_card_matchingE:
  assumes "max_card_matching G M"
          "\<lbrakk> M \<subseteq> G; matching M; \<And> M'. \<lbrakk>M' \<subseteq> G; matching M'\<rbrakk> \<Longrightarrow> card M' \<le> card M\<rbrakk> \<Longrightarrow> P"
        shows P
  using assms
  by(auto simp add: max_card_matching_def)

lemmas max_card_matchingDs = conjunct1[OF max_card_matchingD]
                             conjunct1[OF conjunct2[OF max_card_matchingD]]
                             mp[OF spec[OF conjunct2[OF conjunct2[OF max_card_matchingD]]]]

lemma max_matching_if_same_card:
  "\<lbrakk>max_card_matching G M; graph_matching G M'; card M = card M'\<rbrakk> \<Longrightarrow> max_card_matching G M'"
  by(auto intro!: max_card_matchingI elim!: max_card_matchingE)

lemma max_card_matching_subgraphD:
  assumes "max_card_matching G M"
  shows "\<And>e. e \<in> M \<Longrightarrow> e \<in> G"
  using assms
  by (auto dest: max_card_matchingD)


lemma max_card_matching_ex:
  assumes "finite G"
  shows "\<exists>M. max_card_matching G M"
proof (rule ccontr)
  assume no_max_card: "\<nexists>M. max_card_matching G M"

  obtain M where "M \<subseteq> G" "matching M"
    using matching_empty by blast

  then show False
  proof (induction "card G - card M" arbitrary: M rule: less_induct)
    case less
    with no_max_card obtain M' where "M' \<subseteq> G" "matching M'" "card M < card M'"
      unfolding max_card_matching_def
      by auto

    with assms show ?case
      by (intro less)
         (auto simp add: card_mono le_diff_iff' less.prems less_le_not_le)
  qed
qed

lemma max_card_matchings_same_size:
  assumes "max_card_matching G M"
  assumes "max_card_matching G M'"
  shows "card M = card M'"
  using assms
  unfolding max_card_matching_def
  by (simp add: dual_order.eq_iff)

lemma max_card_matching_cardI:
  assumes "max_card_matching G M"
  assumes "card M = card M'"
  assumes "M' \<subseteq> G" "matching M'"
  shows "max_card_matching G M'"
  using assms
  unfolding max_card_matching_def
  by simp

lemma max_card_matching_non_empty:
  assumes "max_card_matching G M"
  assumes "G \<noteq> {}"
  shows "M \<noteq> {}"
proof (rule ccontr, simp)
  assume "M = {}"

  from assms obtain e where "e \<in> G"
    by blast

  then have "matching {e}" "{e} \<subseteq> G"
    unfolding matching_def
    by blast+

  with assms \<open>M = {}\<close> show False
    unfolding max_card_matching_def
    by auto
qed

lemma perfect_matchingI:
  assumes "M \<subseteq> G" "matching M" "Vs G = Vs M"
  shows "perfect_matching G M"
  using assms
  unfolding perfect_matching_def
  by blast

lemma perfect_matchingE:
  "\<lbrakk>perfect_matching G M ; \<lbrakk>M \<subseteq> G; matching M; Vs G = Vs M\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp add: perfect_matching_def)

lemma perfect_matching_max_card_matchingI:
  assumes "max_card_matching G M"
  assumes "Vs G = Vs M"
  shows "perfect_matching G M"
  using assms
  unfolding max_card_matching_def
  by (auto intro: perfect_matchingI)

lemma perfect_matchingD:
  assumes "perfect_matching G M"
  shows "M \<subseteq> G" "matching M" "Vs G = Vs M"
  using assms
  unfolding perfect_matching_def
  by blast+

lemma perfect_matching_subgraphD:
  assumes "perfect_matching G M"
  shows "\<And>e. e \<in> M \<Longrightarrow> e \<in> G"
  using assms
  by (auto dest: perfect_matchingD)

lemma perfect_matching_edgeE:
  assumes "perfect_matching G M"
  assumes "v \<in> Vs G"
  obtains e where "e \<in> M" "v \<in> e"
  using assms
  by (auto dest: perfect_matchingD elim!: vs_member_elim)

lemma perfect_matching_member[iff?]: 
  "perfect_matching G M \<longleftrightarrow> matching M \<and> M \<subseteq> G \<and> Vs M = Vs G"
  unfolding perfect_matching_def by auto

lemma (in graph_abs) perfect_matching_is_max_card_matching: 
  assumes perfect: "perfect_matching G M"
  shows "max_card_matching G M"
proof (rule ccontr)
  assume not_max_card: "\<not>max_card_matching G M"

  interpret M_graph: graph_abs M
    apply unfold_locales
    using graph graph_invar_subset assms
    by (auto dest!: perfect_matchingD(1))

  from perfect have "M \<subseteq> G" "matching M" "Vs G = Vs M"
    by (auto dest: perfect_matchingD)

  with not_max_card obtain M' where bigger_matching: "M' \<subseteq> G" "matching M'" "card M < card M'"
    unfolding max_card_matching_def perfect_matching_def
    by auto

  then interpret M'_graph: graph_abs M'
    apply unfold_locales
    using graph graph_invar_subset 
    by (auto dest!: perfect_matchingD(1))

  from bigger_matching have *: "2 * card M < 2 * card M'"
    by linarith

  with * \<open>matching M\<close> \<open>matching M'\<close> have "card (Vs M) < card (Vs M')"
    by (auto simp: M_graph.matching_card_vs M'_graph.matching_card_vs)

  with \<open>Vs G = Vs M\<close>[symmetric] \<open>M' \<subseteq> G\<close> M_graph.graph show False
    by (auto simp: Vs_def Union_mono card_mono leD dest: )
qed

lemma maximal_matching_remove_edges:
  assumes "M \<subseteq> G"
  assumes "E \<subseteq> M"
  assumes "X = Vs E"
  assumes "maximal_matching G M"
  shows "maximal_matching (G \<setminus> X) (M \<setminus> X)"
  unfolding maximal_matching_def
proof (intro conjI allI impI)
  show "matching (M \<setminus> X)" using assms
    by (auto simp: maximal_matching_def intro: matching_remove_vertices)
next
  fix u v
  assume "{u,v} \<in> G \<setminus> X"

  then have "{u,v} \<in> G" "u \<notin> X" "v \<notin> X"
    using remove_vertices_subgraph'
    by(auto dest: edges_are_Vs edges_are_Vs_2 remove_vertices_not_vs) 

  with \<open>maximal_matching G M\<close> consider "u \<in> Vs M" | "v \<in> Vs M"
    by (auto dest: maximal_matching_edgeD)

  then show "u \<in> Vs (M \<setminus> X) \<or> v \<in> Vs (M \<setminus> X)"
  proof cases
    case 1
    then obtain e where "e \<in> M" "u \<in> e"
      by (auto simp: vs_member)

    with assms \<open>u \<notin> X\<close> have "e \<in> M \<setminus> X"
    proof (intro in_remove_verticesI, goal_cases)
      case 2
      then show ?case
        by (auto simp: vs_member)
           (metis matching_unique_match maximal_matchingD subsetD)
    qed blast

    with \<open>u \<in> e\<close> show ?thesis
      by blast
  next
    case 2
    then obtain e where "e \<in> M" "v \<in> e"
      by (auto simp: vs_member)

    with assms \<open>v \<notin> X\<close> have "e \<in> M \<setminus> X"
    proof (intro in_remove_verticesI, goal_cases)
      case 2
      then show ?case
        by (auto simp: vs_member)
           (metis matching_unique_match maximal_matchingD subsetD)
    qed blast

    with \<open>v \<in> e\<close> show ?thesis
      by blast
  qed
qed

lemma max_card_matching_remove_vertices:
  assumes "max_card_matching G M"
  assumes "X \<subseteq> Vs G - Vs M"
  shows "max_card_matching (G \<setminus> X) M"
proof (rule ccontr)
  assume contr: "\<not>max_card_matching (G \<setminus> X) M"

  from assms have "M \<subseteq> G \<setminus> X"
    by (auto dest: max_card_matchingD intro: in_remove_verticesI)

  with assms contr obtain M' where M': "M' \<subseteq> G \<setminus> X" "matching M'" "card M' > card M"
    by (auto simp: max_card_matching_def)

  then have "M' \<subseteq> G"
    by (auto intro: remove_vertices_subgraph')

  with M' assms show False
    by (simp add: leD max_card_matchingD)
qed

text \<open>
  As mentioned above we can reduce the analysis of the competitive ratio to inputs where a perfect
  matching exists. In order to reason about all inputs, we need to remove vertices from the graph
  which are not in a maximum matching.
\<close>

text \<open>
  This function takes two graphs \<^term>\<open>G::'a graph\<close>, \<^term>\<open>M::'a graph\<close> and removes all vertices
  (and edges incident to them) from \<^term>\<open>G::'a graph\<close> which are not in \<^term>\<open>M::'a graph\<close>.
  Under the assumptions \<^term>\<open>matching M\<close> and \<^term>\<open>(M::'a graph) \<subseteq> G\<close>, this returns a graph where
  \<^term>\<open>M::'a graph\<close> is a perfect matching. We explicitly state the function this way, as it
  yields an induction scheme that allows to reason about removing single vertices as compared to
  removing sets of vertices.
\<close>
function make_perfect_matching :: "'a graph \<Rightarrow> 'a graph \<Rightarrow> 'a graph" where
  "make_perfect_matching G M = (
    if (\<exists>x. x \<in> Vs G \<and> x \<notin> Vs M)
    then make_perfect_matching (G \<setminus> {SOME x. x \<in> Vs G \<and> x \<notin> Vs M}) M
    else G
  )
  " if "finite G"
| "make_perfect_matching G M = G" if "infinite G"
  by auto

termination
  by (relation "measure (card \<circ> fst)")
     (auto intro: remove_vertex_card_less dest!: someI_ex)

lemma max_card_matching_make_perfect_matching:
  assumes "matching M" "M \<subseteq> G" "graph_invar G"
  shows "max_card_matching (make_perfect_matching G M) M"
  using assms
proof (induction G M rule: make_perfect_matching.induct)
  case (2 G M)
  then show ?case
    using dblton_graph_finite_Vs
    by blast
next
  case (1 G M)
  then interpret graph_abs1: graph_abs G
      apply unfold_locales
      by auto

  show ?case
  proof (cases "\<exists>x. x \<in> Vs G \<and> x \<notin> Vs M")
    case True

    interpret graph_abs2: graph_abs "G \<setminus> {SOME x. x \<in> Vs G \<and> x \<notin> Vs M}"
      apply unfold_locales 
      by (simp add: graph_abs1.graph  graph_invar_remove_vertices)

    from True \<open>M \<subseteq> G\<close> have "M \<subseteq> G \<setminus> {SOME x. x \<in> Vs G \<and> x \<notin> Vs M}"
      by (intro subgraph_remove_some_ex)


    from "1.IH"[OF True \<open>matching M\<close> this graph_abs2.graph] True \<open>finite G\<close>
    show ?thesis
      by simp
  next
    case False

    from False 1 have "perfect_matching G M"
      by (auto intro!: perfect_matchingI subgraph_vs_subset_eq)
    
    with 1 False show ?thesis
      using graph_abs1.perfect_matching_is_max_card_matching
      by auto
  qed
qed

lemma vs_make_perfect_matching:
  assumes "M \<subseteq> G"
  assumes "finite G"
  shows "Vs (make_perfect_matching G M) = Vs M"
  using assms
proof (induction G M rule: make_perfect_matching.induct)
  case (1 G M)
  show ?case
  proof (cases "\<exists>x. x \<in> Vs G \<and> x \<notin> Vs M")
    case True

    from \<open>finite G\<close> True 1 show ?thesis
      by simp (intro "1.IH" finite_remove_vertices subgraph_remove_some_ex)
  next
    case False
    with 1 show ?thesis
      by (auto dest: Vs_subset)
  qed
qed blast

lemma perfect_matching_make_perfect_matching:
  assumes "finite G" "graph_invar G"
  assumes "matching M" "M \<subseteq> G"
  shows "perfect_matching (make_perfect_matching G M) M"
  using assms
  by (auto simp del: make_perfect_matching.simps
           intro!: perfect_matching_max_card_matchingI
                   vs_make_perfect_matching max_card_matching_make_perfect_matching
           dest: max_card_matchingD)

lemma subgraph_make_perfect_matching:
  shows "make_perfect_matching G M \<subseteq> G"
  by (induction G M rule: make_perfect_matching.induct)
     (auto dest: remove_vertices_subgraph')

lemma same_matching_card:
  assumes "graph_abs G" "graph_matching G M" "graph_matching G M'"
  shows  "(card (Vs G - Vs M) = card (Vs G - Vs M')) \<longleftrightarrow> card M = card M'"
proof-
  have "card (Vs G - Vs M) = card (Vs G) - card (Vs M)" 
    using assms(1,2) card_Vs_diff graph_abs.finite_Vs graph_abs_mono by blast
  moreover have "card (Vs G) \<ge> card (Vs M)" 
    by (simp add: Vs_subset assms(1,2) card_mono graph_abs.finite_Vs)
  moreover have "card (Vs M) = 2*card M" 
    using  assms(1,2)  graph_abs_mono
    by(auto intro!: graph_abs.matching_card_vs[symmetric])
  moreover have "card (Vs G - Vs M') = card (Vs G) - card (Vs M')" 
    using assms(1,3) card_Vs_diff graph_abs.finite_Vs graph_abs_mono by blast
  moreover have "card (Vs G) \<ge> card (Vs M')" 
    by (simp add: Vs_subset assms(1,3) card_mono graph_abs.finite_Vs)
  moreover have "card (Vs M') = 2*card M'" 
    using  assms(1,3)  graph_abs_mono
    by(auto intro!: graph_abs.matching_card_vs[symmetric])
  ultimately show ?thesis
    by linarith
qed

lemma 
  assumes "finite G"
  shows finite_number_of_matchings: "finite (Collect (graph_matching G))"
    and finite_number_of_perfect_matchings: "finite (Collect (perfect_matching G))"
    and finite_number_of_max_card_matchings: "finite (Collect (max_card_matching G))"
  using assms
  by(auto intro!: finite_subset[of _ "Pow G"] simp add: perfect_matching_def max_card_matching_def)

lemma max_card_matchings_same_number_unmatched:
 "\<lbrakk> max_card_matching G M; max_card_matching G M'; graph_abs G\<rbrakk> 
  \<Longrightarrow> card (Vs G-  Vs M) = card (Vs G - Vs M')"
  by(subst same_matching_card)
    (auto elim: max_card_matchingE
         intro: max_card_matchings_same_size)

(*TODO MOVE*)

lemma maximiser_of_function_nempty_finite:
  assumes "finite X" "X \<noteq> {}"
  obtains x where "x \<in> X" "\<And> y. y \<in> X \<Longrightarrow> ((f x)::'a::linorder) \<ge> f y"
proof(goal_cases)
  case 1
  define MX where "MX = {f x | x. x \<in> X}"
  have "Max MX \<in> MX"
    using assms
    by(intro linorder_class.Max_in) (auto simp add: MX_def)
  then obtain x where x: "f x = Max MX" "x \<in> X"
    by(auto simp add: MX_def)
  hence "\<And> y. y \<in> X \<Longrightarrow> ((f x)::'a::linorder) \<ge> f y"
    using assms
    by(auto intro!:  linorder_class.Max.coboundedI 
        simp add: MX_def)
  thus thesis
    using 1 x by auto
qed

lemma max_card_matching_exists:
  assumes "finite G"
  obtains M' where "max_card_matching G M'"
  apply(rule  maximiser_of_function_nempty_finite[of "Collect (graph_matching G)" card])
  using finite_number_of_matchings[OF assms(1)] 
  by(auto intro!: exI[of _ "{}"] simp add: max_card_matching_def)

definition "\<nu> G = Max {card M | M. graph_matching G M}"

lemmas ny_def = \<nu>_def

lemma max_matching_is_\<nu>: "\<lbrakk>finite G;max_card_matching G M\<rbrakk> \<Longrightarrow> card M = \<nu> G"
  unfolding ny_def
  using matching_empty
  by(subst linorder_class.eq_Max_iff)
    (auto simp add: image_Collect[symmetric] max_card_matchingDs(1,2)
            intro!: finite_imageI finite_number_of_matchings exI[of _ "{}"]
              dest: max_card_matchingD)

lemma obtain_max_card_matching_\<nu>:
  assumes "finite G"
  obtains M where "graph_matching G M" "card M = \<nu> G" "max_card_matching G M"
  using max_card_matchingDs(1,2)[of G] max_card_matching_exists[OF assms] 
        max_matching_is_\<nu>[OF assms]
  by force

lemma perfect_matching_card:
  assumes "perfect_matching G M" "graph_abs G"
  shows "2* card M = card (Vs G)" 
  using assms
  by(subst graph_abs.matching_card_vs)
    (auto intro: graph_abs_mono 
      simp add: perfect_matching_def)

lemma perfect_matchings_same_card:
  "\<lbrakk>perfect_matching G M; perfect_matching G M'; graph_abs G\<rbrakk> \<Longrightarrow> card M = card M'"
  by(auto intro!: max_card_matchings_same_size graph_abs.perfect_matching_is_max_card_matching)

lemma perfect_matching_card':  
  assumes "perfect_matching G M" "graph_abs G"
  shows "card M = card (Vs G) div 2"
  using  perfect_matching_card assms by fastforce

lemma perfect_matching_if_projected_to_matched_verts:
  assumes "graph_matching G M"
  shows "perfect_matching (graph_inter_Vs G (Vs M)) M"
  using assms 
  by(fastforce intro!: perfect_matchingI simp add: graph_inter_Vs_def Vs_def)

subsubsection \<open>Weighted Matchings\<close>

definition "max_weight_matching E w M =
  (graph_matching E M \<and> (\<forall> M'. graph_matching E M' \<longrightarrow> (sum w M'::real) \<le> sum w M))"

lemma max_weight_matchingI:
  "\<lbrakk>graph_matching E M; \<And> M'. graph_matching E M' \<Longrightarrow> sum w M' \<le> sum w M\<rbrakk>
   \<Longrightarrow> max_weight_matching E w M"
and max_weight_matchingE:
  "\<lbrakk>max_weight_matching E w M; 
     \<lbrakk>graph_matching E M; \<And> M'. graph_matching E M' \<Longrightarrow> sum w M' \<le> sum w M\<rbrakk> \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
and max_weight_matchingD:
  "max_weight_matching E w M \<Longrightarrow> graph_matching E M"
  "\<lbrakk>max_weight_matching E w M; graph_matching E M'\<rbrakk> \<Longrightarrow> sum w M' \<le> sum w M"
  by(auto simp add: max_weight_matching_def)

definition "min_weight_perfect_matching E w M =
  (perfect_matching E M \<and> (\<forall> M'. perfect_matching E M' \<longrightarrow> (sum w M'::real) \<ge> sum w M))"

lemma min_weight_perfect_matchingI:
  "\<lbrakk>perfect_matching E M; \<And> M'. perfect_matching E M' \<Longrightarrow> sum w M' \<ge> sum w M\<rbrakk>
   \<Longrightarrow> min_weight_perfect_matching E w M"
and min_weight_perfect_matchingE:
  "\<lbrakk>min_weight_perfect_matching E w M;
    \<lbrakk>perfect_matching E M; \<And> M'. perfect_matching E M' \<Longrightarrow> sum w M' \<ge> sum w M\<rbrakk> \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
and min_weight_perfect_matchingD:
  "min_weight_perfect_matching E w M \<Longrightarrow> perfect_matching E M"
  "\<lbrakk>min_weight_perfect_matching E w M; perfect_matching E M'\<rbrakk> \<Longrightarrow> sum w M' \<ge> sum w M"
  by(auto simp add: min_weight_perfect_matching_def)

definition "min_weight_matching E w M =
  (graph_matching E M \<and> (\<forall> M'. graph_matching E M' \<longrightarrow> ((sum w M')::real) \<ge> sum w M))"

lemma min_weight_matchingI:
  "\<lbrakk>graph_matching E M; \<And> M'. graph_matching E M' \<Longrightarrow> sum w M' \<ge> sum w M\<rbrakk>
   \<Longrightarrow> min_weight_matching E w M"
and min_weight_matchingE:
  "\<lbrakk>min_weight_matching E w M;
    \<lbrakk>graph_matching E M; \<And> M'. graph_matching E M' \<Longrightarrow> sum w M' \<ge> sum w M\<rbrakk> \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
and min_weight_matchingD:
  "min_weight_matching E w M \<Longrightarrow> graph_matching E M"
  "\<lbrakk>min_weight_matching E w M; graph_matching E M'\<rbrakk> \<Longrightarrow> sum w M' \<ge> sum w M"
  by(auto simp add: min_weight_matching_def)

lemma min_weight_matching_only_negs:
  "\<lbrakk>min_weight_matching G w M; finite M;e \<in> M\<rbrakk> \<Longrightarrow> w e \<le> 0"
proof(rule ccontr, goal_cases)
  case 1
  have "graph_matching G (M - {e})"
    using "1"(1) min_weight_matchingD(1)
    by(auto intro!:  matching_delete)
  moreover have "sum w (M - {e}) < sum w M"
    using 1(3,4)
    by(auto simp add: sum_diff1[OF 1(2)])
  ultimately show False
    using 1(1)
    by(auto elim!: min_weight_matchingE)
qed

definition "max_weight_perfect_matching E w M =
  (perfect_matching E M \<and> (\<forall> M'. perfect_matching E M' \<longrightarrow> (sum w M'::real) \<le> sum w M))"

lemma max_weight_perfect_matchingI:
  "\<lbrakk>perfect_matching E M; \<And> M'. perfect_matching E M' \<Longrightarrow> sum w M' \<le> sum w M\<rbrakk>
  \<Longrightarrow> max_weight_perfect_matching E w M"
  and max_weight_perfect_matchingE:
  "\<lbrakk>max_weight_perfect_matching E w M;
     \<lbrakk>perfect_matching E M; \<And> M'. perfect_matching E M' \<Longrightarrow> sum w M' \<le> sum w M\<rbrakk> \<Longrightarrow> P\<rbrakk>
  \<Longrightarrow> P"
  and max_weight_perfect_matchingD:
  "max_weight_perfect_matching E w M \<Longrightarrow> perfect_matching E M"
  "\<lbrakk>max_weight_perfect_matching E w M; perfect_matching E M'\<rbrakk> \<Longrightarrow> sum w M' \<le> sum w M"
  by(auto simp add: max_weight_perfect_matching_def)

lemma max_weight_matching_only_pos:
  "\<lbrakk>max_weight_matching G w M; finite M;e \<in> M\<rbrakk> \<Longrightarrow> w e \<ge> 0"
proof(rule ccontr, goal_cases)
  case 1
  have "graph_matching G (M - {e})"
    using "1"(1) max_weight_matchingD(1)
    by(auto intro!:  matching_delete)
  moreover have "sum w (M - {e}) > sum w M"
    using 1(3,4)
    by(auto simp add: sum_diff1[OF 1(2)])
  ultimately show False
    using 1(1)
    by(auto elim!: max_weight_matchingE)
qed

definition "max_weight_max_card_matching E w M =
  (max_card_matching E M \<and> (\<forall> M'. max_card_matching E M' \<longrightarrow> (sum w M'::real) \<le> sum w M))"

lemma max_weight_max_card_matchingI:
  "\<lbrakk>max_card_matching E M; \<And> M'. max_card_matching E M' \<Longrightarrow> sum w M' \<le> sum w M\<rbrakk>
   \<Longrightarrow> max_weight_max_card_matching E w M"
  and max_weight_max_card_matchingE:
  "\<lbrakk>max_weight_max_card_matching E w M;
    \<lbrakk>max_card_matching E M; \<And> M'. max_card_matching E M' \<Longrightarrow> sum w M' \<le> sum w M\<rbrakk> \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  and max_weight_max_card_matchingD:
  "max_weight_max_card_matching E w M \<Longrightarrow> max_card_matching E M"
  "\<lbrakk>max_weight_max_card_matching E w M; max_card_matching E M'\<rbrakk> \<Longrightarrow> sum w M' \<le> sum w M"
  by(auto simp add: max_weight_max_card_matching_def)

definition "min_weight_max_card_matching E w M =
  (max_card_matching E M \<and> (\<forall> M'. max_card_matching E M' \<longrightarrow> (sum w M'::real) \<ge> sum w M))"

lemma min_weight_max_card_matchingI:
  "\<lbrakk>max_card_matching E M; \<And> M'. max_card_matching E M' \<Longrightarrow> sum w M' \<ge> sum w M\<rbrakk>
   \<Longrightarrow> min_weight_max_card_matching E w M"
  and min_weight_max_card_matchingE:
  "\<lbrakk>min_weight_max_card_matching E w M;
    \<lbrakk>max_card_matching E M; \<And> M'. max_card_matching E M' \<Longrightarrow> sum w M' \<ge> sum w M\<rbrakk> \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  and min_weight_max_card_matchingD:
  "min_weight_max_card_matching E w M \<Longrightarrow> max_card_matching E M"
  "\<lbrakk>min_weight_max_card_matching E w M; max_card_matching E M'\<rbrakk> \<Longrightarrow> sum w M' \<ge> sum w M"
  by(auto simp add: min_weight_max_card_matching_def)

lemma weighted_matchings_over_coinciding_weights:
  assumes "\<And> e. e \<in> G \<Longrightarrow> w' e = w e"
  shows  "max_weight_matching G w M \<longleftrightarrow> max_weight_matching G w' M"
         "min_weight_matching G w M \<longleftrightarrow> min_weight_matching G w' M"
         "max_weight_perfect_matching G w M \<longleftrightarrow> max_weight_perfect_matching G w' M"
         "min_weight_perfect_matching G w M \<longleftrightarrow> min_weight_perfect_matching G w' M"
         "max_weight_max_card_matching G w M \<longleftrightarrow> max_weight_max_card_matching G w' M"
         "min_weight_max_card_matching G w M \<longleftrightarrow> min_weight_max_card_matching G w' M" 
  using assms
  by(auto elim!: max_weight_matchingE min_weight_matchingE
                 max_weight_perfect_matchingE min_weight_perfect_matchingE
                 max_weight_max_card_matchingE min_weight_max_card_matchingE
         intro!: max_weight_matchingI min_weight_matchingI
                 max_weight_perfect_matchingI min_weight_perfect_matchingI
                 max_weight_max_card_matchingI min_weight_max_card_matchingI
      simp add: comm_monoid_add_class.sum.cong[OF refl, of _ w' w] subsetD
                perfect_matching_subgraphD max_card_matching_subgraphD)

(*TODO MOVE*)
lemma minimiser_of_function_nempty_finite:
  assumes "finite X" "X \<noteq> {}"
  obtains x where "x \<in> X" "\<And> y. y \<in> X \<Longrightarrow> ((f x)::'a::linorder) \<le> f y"
proof(goal_cases)
  case 1
  define MX where "MX = {f x | x. x \<in> X}"
  have "Min MX \<in> MX"
    using assms
    by(intro linorder_class.Min_in) (auto simp add: MX_def)
  then obtain x where x: "f x = Min MX" "x \<in> X"
    by(auto simp add: MX_def)
  hence "\<And> y. y \<in> X \<Longrightarrow> ((f x)::'a::linorder) \<le> f y"
    using assms
    by(auto intro!: linorder_class.Min.coboundedI 
        simp add: MX_def)
  thus thesis
    using 1 x by auto
qed

lemma min_matching_exists:
  assumes "finite G"
  obtains M' where "min_weight_matching G w M'"
  apply(rule  minimiser_of_function_nempty_finite[of "Collect (graph_matching G)" "sum w"])
  using finite_number_of_matchings[OF assms(1)] 
  by(auto intro!: exI[of _ "{}"] simp add: min_weight_matching_def)

lemma min_perfect_matching_exists:
  assumes "finite G" "perfect_matching G M"
  obtains M' where "min_weight_perfect_matching G w M'"
  apply(rule  minimiser_of_function_nempty_finite[of "Collect (perfect_matching G)" "sum w"])
  using finite_number_of_perfect_matchings[OF assms(1)] assms(2)
  by(auto simp add: min_weight_perfect_matching_def)

lemma min_weight_max_card_matching_exists:
  assumes "finite G"
  obtains M' where "min_weight_max_card_matching G w M'"
  apply(rule  minimiser_of_function_nempty_finite[of "Collect (max_card_matching G)" "sum w"])
  using finite_number_of_max_card_matchings[OF assms(1)]
  by(auto simp add: min_weight_max_card_matching_def 
      intro: max_card_matching_exists[OF assms(1)])

lemma max_matching_exists:
  assumes "finite G"
  obtains M' where "max_weight_matching G w M'"
  apply(rule  maximiser_of_function_nempty_finite[of "Collect (graph_matching G)" "sum w"])
  using finite_number_of_matchings[OF assms(1)]
  by(auto simp add: max_weight_matching_def 
      intro: exI[of _ "{}"])

lemma max_perfect_matching_exists:
  assumes "finite G" "perfect_matching G M"
  obtains M' where "max_weight_perfect_matching G w M'"
  apply(rule  maximiser_of_function_nempty_finite[of "Collect (perfect_matching G)" "sum w"])
  using finite_number_of_perfect_matchings[OF assms(1)] assms(2)
  by(auto simp add: max_weight_perfect_matching_def)

lemma max_weight_max_card_matching_exists:
  assumes "finite G"
  obtains M' where "max_weight_max_card_matching G w M'"
  apply(rule  maximiser_of_function_nempty_finite[of "Collect (max_card_matching G)" "sum w"])
  using finite_number_of_max_card_matchings[OF assms(1)]
  by(auto simp add: max_weight_max_card_matching_def
      intro: max_card_matching_exists[OF assms(1)])

lemma max_weight_matching_unused_edges:
  assumes "max_weight_matching G w M" "e \<in> G" "e \<inter> Vs M = {}" "e \<noteq> {}" "finite M"
  shows "w e \<le> 0"
proof(rule ccontr, goal_cases)
  case 1
  hence "sum w (insert e M) > sum w M"
    using assms
    by(subst comm_monoid_add_class.sum.insert) auto
  moreover have "graph_matching G (insert e M)"
    using assms 
    by(auto elim!: max_weight_matchingE intro: matchingI
        dest: matching_unique_match)
  ultimately show False
    using assms(1)
    by(auto elim!:  max_weight_matchingE)
qed

lemma min_weight_matching_unused_edges:
  assumes "min_weight_matching G w M" "e \<in> G" "e \<inter> Vs M = {}" "e \<noteq> {}" "finite M"
  shows "w e \<ge> 0"
proof(rule ccontr, goal_cases)
  case 1
  hence "sum w (insert e M) < sum w M"
    using assms
    by(subst comm_monoid_add_class.sum.insert) auto
  moreover have "graph_matching G (insert e M)"
    using assms 
    by(auto elim!: min_weight_matchingE intro: matchingI
        dest: matching_unique_match)
  ultimately show False
    using assms(1)
    by(auto elim!: min_weight_matchingE)
qed

subsubsection \<open>Matching Specific Vertices\<close>

definition cover_matching where
  "cover_matching G M A = (matching M \<and> M \<subseteq> G \<and> A \<subseteq> Vs M)"

lemma cover_matchingI:
  "\<lbrakk>matching M; M \<subseteq> G; A \<subseteq> Vs M\<rbrakk> \<Longrightarrow> cover_matching G M A"
and cover_matchingE:
  "\<lbrakk>cover_matching G M A; \<lbrakk>matching M; M \<subseteq> G; A \<subseteq> Vs M\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
and cover_matchingD:
  "cover_matching G M A \<Longrightarrow> matching M"
  "cover_matching G M A \<Longrightarrow> M \<subseteq> G"
  "cover_matching G M A \<Longrightarrow> A \<subseteq> Vs M"
  by(auto simp add: cover_matching_def)

lemma cover_matching_bigger_graph:
   "\<lbrakk>cover_matching G M A; G \<subseteq> G'\<rbrakk> \<Longrightarrow> cover_matching G' M A"
  by(auto elim!: cover_matchingE intro!: cover_matchingI)

lemma cover_matching_neighbours_of_Vs_card:
  fixes G :: "'a set set"
  assumes "cover_matching G M A" "graph_invar G"
  shows "\<forall> X \<subseteq> A. card (neighbours_of_Vs M X) = card X"
  using assms card_ther_vertex 
  unfolding cover_matching_def 
  by fastforce

lemma finite_number_of_cover_matchings:
  assumes "finite G"
  shows "finite (Collect (\<lambda> M. cover_matching G M X))"
  using assms
  by(auto intro!: finite_subset[of _ "Pow G"] simp add: cover_matching_def)

lemma max_card_cover_matching_exists:
  assumes "finite G" "cover_matching G M X"
  obtains M' where "cover_matching G M' X" 
                   "\<And> M. cover_matching G M X \<Longrightarrow> card M \<le> card M'"
  apply(rule maximiser_of_function_nempty_finite[of "Collect (\<lambda> M. cover_matching G M X)" card])
  using finite_number_of_cover_matchings[OF assms(1)] assms(2)
  by auto

lemma cover_matching_is_graph_matching:
  "cover_matching G M X \<Longrightarrow> graph_matching G M"
  by(auto elim!: cover_matchingE)

lemma cover_matching_subset:
  "\<lbrakk>cover_matching G M X; Y \<subseteq> X\<rbrakk> \<Longrightarrow> cover_matching G M Y"
  by(auto elim!: cover_matchingE intro!: cover_matchingI)

lemma obtain_covering_edge:
  assumes "cover_matching G M X" "x \<in> X"
  obtains e where "e \<in> M" "x \<in> e"
  using assms
  by(auto elim!: cover_matchingE 
      simp add: vs_member 
      dest!: subsetD[of X "Vs M" x])

subsection \<open>Bipartite Matching\<close>

lemma perfect_matching_bipartite_card_eq:
  assumes "perfect_matching G M"
  assumes "bipartite G U V"
  assumes "Vs G = U \<union> V"
  shows "card M = card V"
proof (intro bij_betw_same_card[where f = "\<lambda>e. (THE v. v \<in> e \<and> v \<in> V)"]
    bij_betwI[where g = "\<lambda>v. (THE e. v \<in> e \<and> e \<in> M)"] funcsetI)
  fix e
  assume "e \<in> M"
  with assms obtain u v where uv: "e = {u,v}" "u \<in> U" "v \<in> V"
    by (auto dest!: perfect_matching_subgraphD elim: bipartite_edgeE)
  with assms have the_v: "(THE v. v \<in> e \<and> v \<in> V) = v"
    by (auto dest: bipartite_disjointD)
  with \<open>v \<in> V\<close> show "(THE v. v \<in> e \<and> v \<in> V) \<in> V"
    by blast
  from uv have "v \<in> e"
    by blast
  with assms \<open>e \<in> M\<close> show "(THE e'. (THE v. v \<in> e \<and> v \<in> V) \<in> e' \<and> e' \<in> M) = e"
    by (simp only: the_v, intro the_equality matching_unique_match)
       (auto dest: perfect_matchingD)
next
  fix v
  assume "v \<in> V"
  with assms have "v \<in> Vs M"
    by (auto simp: perfect_matchingD)
  then obtain e where e: "v \<in> e" "e \<in> M"
    by (auto elim: vs_member_elim)
  with assms have the_e: "(THE e. v \<in> e \<and> e \<in> M) = e"
    by (intro the_equality matching_unique_match)
       (auto dest: perfect_matchingD)
  with e show "(THE e. v \<in> e \<and> e \<in> M) \<in> M"
    by blast
  from assms e \<open>v \<in> V\<close> obtain u where "e = {u,v}" "u \<in> U"
    using   bipartite_edgeE[OF _ assms(2), of e]
    by(force dest: perfect_matching_subgraphD bipartite_disjointD
         simp add: disjoint_iff_not_equal) 
  with assms e \<open>v \<in> V\<close> show "(THE v'. v' \<in> (THE e. v \<in> e \<and> e \<in> M) \<and> v' \<in> V) = v"
    by (simp only: the_e, intro the_equality)
       (auto dest: bipartite_disjointD)
qed

lemma bipartite_edge_In_Ex1:
  assumes "bipartite M U V"
  assumes "matching M"
  assumes "e \<in> M"
  shows "\<exists>!e'. e' \<in> M \<and> V \<inter> e \<subseteq> e'"
proof
  from assms show "e \<in> M \<and> V \<inter> e \<subseteq> e"
    by blast
next
  fix e'
  assume e': "e' \<in> M \<and> V \<inter> e \<subseteq> e'"
  from assms obtain u v where e: "e = {u,v}" "v \<in> V" "u \<in> U"
    by (auto elim: bipartite_edgeE)
  from assms have "U \<inter> V = {}"
    by (auto dest: bipartite_disjointD)
  with e' e have "v \<in> e'" by blast
  with assms e' e show "e' = e"
    by (intro matching_unique_match) auto
qed

lemma the_bipartite_edge_In:
  assumes "bipartite M U V"
  assumes "matching M"
  assumes "e \<in> M"
  shows "(THE e'. e' \<in> M \<and> V \<inter> e \<subseteq> e') = e"
  using assms
  by (intro the1_equality bipartite_edge_In_Ex1) auto

lemma card_bipartite_matching_In:
  assumes "bipartite M U V"
  assumes "matching M"
  shows "card M = card (((\<inter>) V) ` M)"
  using assms
  by (auto intro!: bij_betw_same_card[of "(\<inter>) V"] 
            intro: bij_betwI[where g = "\<lambda>v. (THE e. e \<in> M \<and> v \<subseteq> e)"]
             simp: the_bipartite_edge_In)

lemma bipartite_same_matcheds_on_both_sides:
  assumes "bipartite G L R" "graph_matching G M"
  shows   "card (Vs M \<inter> L) = card (Vs M \<inter> R)"
proof-
  define f where "f = (\<lambda> l. SOME r. \<exists> e \<in> M. {l, r} = e)"
  have "inj_on f (Vs M \<inter> L)"
  proof(rule inj_onI, goal_cases)
    case (1 l l')
     have "{l, f l} \<in> M"
      using 1(1) assms(1,2) 
      by(auto simp add: Vs_def  insert_commute  f_def
                   elim!: bipartite_edgeE[of _ G L R] 
                   dest!: set_mp[of M G] dest: someI)
    moreover have "{l', f l'} \<in> M"
      using 1(2) assms(1,2) 
      by(auto simp add: Vs_def  insert_commute  f_def
                   elim!: bipartite_edgeE[of _ G L R] 
                   dest!: set_mp[of M G] dest: someI)
    ultimately show ?case
      using 1(3)  assms(2) 
      by(auto intro!: doubleton_in_matching(2))
  qed
  moreover have "f ` (Vs M \<inter> L) = Vs M \<inter> R"
  proof(rule, all \<open>rule\<close>, goal_cases)
    case (1 r)
    then obtain l e where le: "l \<in> L" "l \<in> e" "e \<in> M" "r = f l"
      by(auto simp add: Vs_def)
    moreover hence lflM:"{l, f l} \<in> M"
      using assms(1,2) 
      by(auto simp add: insert_commute  f_def
                   elim!: bipartite_edgeE[of _ G L R] 
                   dest!: set_mp[of M G] dest: someI)
    ultimately have "e = {l, f l}" "f l = r" "r \<in> R"
      using assms(1,2) matching_unique_match[of M l e "{l, f l}"] 
      by(auto  elim!: bipartite_edgeE[of _ G L R] dest!: set_mp[of M G] 
            simp add: doubleton_eq_iff  bipartite_def disjoint_iff)
    thus ?case 
      using edges_are_Vs_2[OF lflM] 
      by auto
  next
    case (2 r)
    then obtain l where l: "{l ,r} \<in> M" 
      using 2(1) assms(1,2) 
      by(auto simp add: Vs_def  insert_commute 
                   elim!: bipartite_edgeE[of _ G L R] 
                   dest!: set_mp[of M G] )
    have "f l = r" "l \<in> L"
      using assms(1,2) l 2 someI[of "\<lambda> r. \<exists> e \<in> M. {l, r} = e", OF bexI, OF refl l]
       by(auto  elim!: bipartite_edgeE[of _ G L R] dest!: set_mp[of M G]
                intro: doubleton_in_matching(1)
             simp add: f_def doubleton_eq_iff bipartite_def disjoint_iff)
     thus ?case
       using edges_are_Vs[of l "f l"] l  
       by auto
   qed
  ultimately have "bij_betw f (Vs M \<inter> L) (Vs M \<inter> R)"
    by(auto simp add: bij_betw_def)
  thus ?thesis
    by(rule bij_betw_same_card)
qed

lemma all_left_matched_perfect:
  assumes "bipartite G L R"
          "L \<subseteq> Vs M" "card L = card R"
          "graph_matching G M" "finite R"
    shows "perfect_matching G M"
proof(rule perfect_matchingI, goal_cases)
  case 1
  then show ?case 
    using assms(4) by simp 
next
  case 2
  then show ?case 
   using assms(4) by simp
next
  case 3
  have "Vs M \<inter> L = L"
    using assms(1,2,4)
    by blast
  hence "card L = card (Vs M \<inter> R)"
    using bipartite_same_matcheds_on_both_sides[OF assms(1,4)] by simp
  hence "card (Vs M \<inter> R) = card R"
    using assms(3) by simp
  hence "Vs M \<inter> R = R"
    using assms(5) 
    by(intro card_subset_eq) auto
  hence "R \<subseteq> Vs M" 
    by auto
  hence "Vs G \<subseteq> Vs M"
    using assms(2) bipartite_vs_subset[OF assms(1)] by auto
  then show ?case 
    by (simp add: assms(4) subgraph_vs_subset_eq)  
qed

lemma all_right_matched_perfect:
  assumes "bipartite G L R"
          "R \<subseteq> Vs M" "card L = card R"
          "graph_matching G M" "finite L"
    shows "perfect_matching G M"
proof(rule perfect_matchingI, goal_cases)
  case 1
  then show ?case 
    using assms(4) by simp 
next
  case 2
  then show ?case 
   using assms(4) by simp
next
  case 3
  have "Vs M \<inter> R = R"
    using assms(1,2,4)
    by blast
  hence "card R = card (Vs M \<inter> L)"
    using bipartite_same_matcheds_on_both_sides[OF assms(1,4)] by simp
  hence "card (Vs M \<inter> L) = card L"
    using assms(3) by simp
  hence "Vs M \<inter> L = L"
    using assms(5) 
    by(intro card_subset_eq) auto
  hence "L \<subseteq> Vs M" 
    by auto
  hence "Vs G \<subseteq> Vs M"
    using assms(2) bipartite_vs_subset[OF assms(1)] by auto
  then show ?case 
    by (simp add: assms(4) subgraph_vs_subset_eq)  
qed

lemma no_perfect_matching_one_side_bigger:
  assumes "bipartite G L R" "L \<union> R \<subseteq> Vs G" 
          "card L \<noteq> card R"
    shows "\<nexists> M. perfect_matching G M"
proof(rule ccontr, goal_cases)
  case 1
  then obtain M where M: "perfect_matching G M" by auto
  hence "card (Vs M \<inter> L) = card (Vs M \<inter> R)" 
    using assms(1) bipartite_same_matcheds_on_both_sides perfect_matchingD(1,2) by blast
  moreover have "card (Vs M \<inter> L) = card L"  "card (Vs M \<inter> R) = card R"
    using M assms(2) perfect_matchingD(3)
    by(fastforce intro!: arg_cong[of _ _ card ])+
  ultimately have "card L = card R" 
    by simp
  thus False
    using assms(3) by simp
qed

lemma bipartite_L_R_matched_perfect:
  assumes "bipartite G L R" "finite G" "finite L" "finite R"
          "graph_matching G M" "2*card M = card L + card R"
    shows "perfect_matching G M"
proof(rule ccontr, goal_cases)
  case 1
  then obtain u where u: "u \<in> Vs G" "u \<notin> Vs M" 
    using assms(5) 
    by(auto simp add: perfect_matching_def dest: Vs_subset)
  have Vs_M_L_R:"Vs M = Vs M \<inter> L \<union> Vs M \<inter> R"
    using assms(5)  bipartite_vs_subset[OF assms(1)] assms(1)
    by (auto dest!: bipartite_vertex(4)[OF _ bipartite_subgraph])
  have "2*card M = card (Vs M)"
    using assms(1,2,5)
    by(auto intro!: graph_abs.matching_card_vs graph_abs_mono[OF bipartite_to_graph_abs, of G L R M])
  also have "... = card (Vs M \<inter> L) + card (Vs M \<inter> R)"
    apply(subst card_Un_disjoint[symmetric])
    using assms(1,2,5) graph_abs.finite_Vs[OF graph_abs_mono[of G M] ]
      bipartite_to_graph_abs[OF assms(1)] bipartite_disjointD Vs_M_L_R 
    by auto
  also have "... < card L + card R"
  proof(cases "u \<in> L")
    case True
    have "card (Vs M \<inter> L) + card (Vs M \<inter> R) \<le>card (Vs M \<inter> L) + card R"
      by (auto intro!: card_mono assms(4))
    moreover have "... < card L + card R"
      using True u(2)
      by (auto intro!: psubset_card_mono assms(3))
    ultimately show ?thesis 
      by simp
  next
    case False
    hence False: "u \<in> R" 
      using assms(1)  u(1)
      by(auto intro: bipartite_vertex(3))
    have "card (Vs M \<inter> L) + card (Vs M \<inter> R) \<le> card (Vs M \<inter> R) + card L"
      by (auto intro!: card_mono assms(3))
    moreover have "... < card L + card R"
      using False u(2)
      by (auto intro!: psubset_card_mono assms(4))
    ultimately show ?thesis 
      by simp
  qed
  finally have "2*card M < card L + card R"
    by simp
  thus False
    using assms(6) by simp
qed

lemma extend_to_perfect_matching_in_balanced_complete_bipartite:
  assumes "balanced_complete_bipartite G L R" "graph_matching G M" "finite G"
    shows "\<exists> M'. perfect_matching G M' \<and> M' \<supseteq> M"
proof-
  define unmatched where "unmatched = card G - card M"
  note G_props = complete_bipartiteD[OF balanced_complete_bipartiteD(1)[OF assms(1)]]
    balanced_complete_bipartiteD(2)[OF assms(1)]
  show ?thesis
    using assms(2) unmatched_def
  proof(induction unmatched arbitrary: M rule: less_induct)
    case (less unmatched)
    note IH = this
    show ?case 
    proof(cases "perfect_matching G M")
      case True
      then show ?thesis by auto
    next
      case False
      then obtain a where a: "a \<notin> Vs M" "a \<in> Vs G" 
        using less.prems(1)  subgraph_vs_subset_eq [of G M]
        by(auto simp add: perfect_matching_def dest: Vs_subset) 
      obtain u where u: "u \<in> L" "u \<notin> Vs M" 
      proof(rule ccontr, goal_cases)
        case 1
        hence "L \<subseteq> Vs M" by blast
        moreover hence "L \<noteq> {} \<Longrightarrow> card L > 0" 
          using a  G_props(1) assms(3) less.prems(1)
            graph_invar_subset[OF finite_bipartite_graph_invar[OF assms(3) G_props(1)], of M]       
          by (auto simp add: finite_subset card_gt_0_iff)
        moreover hence "finite R"
          using G_props(1, 3) a(2) bipartite_empty_part_iff_empty[of G R] by force
        ultimately have "perfect_matching G M" 
          using G_props IH(2)
          by(auto intro!: all_left_matched_perfect[of G L R M])
        thus False
          using False by simp
      qed
      obtain v where v: "v \<in> R" "v \<notin> Vs M" 
      proof(rule ccontr, goal_cases)
        case 1
        hence "R \<subseteq> Vs M" by blast
        moreover hence "L \<noteq> {} \<Longrightarrow> card L > 0" 
          using a  bipartite_commute[OF G_props(1)] assms(3) less.prems(1) G_props(3) 
            graph_invar_subset[OF finite_bipartite_graph_invar[OF assms(3) G_props(1)], of M]       
          by (auto simp add: finite_subset card_gt_0_iff vs_member elim!: bipartite_edgeE)
        moreover hence "finite L"
          using G_props(1, 3) a(2) bipartite_empty_part_iff_empty[of G R] by force
        ultimately have "perfect_matching G M" 
          using G_props IH(2)
          by(auto intro!: all_right_matched_perfect[of G L R M])    
        thus False
          using False by simp
      qed
      have uv: "{u, v} \<notin> M" "{u, v} \<in> G"
        using edges_are_Vs[of u v] u(2) G_props(2) u(1) v(1) by auto
      hence uvG:"{u, v} \<in> G"
        using G_props(2) by blast 
      have finiteM: "finite M"
        using assms(3) less.prems(1) rev_finite_subset by blast
      have "card (insert {u, v} M) \<le> card G"
        by (simp add: assms(3) card_mono less.prems(1) uvG)
      hence "card G - card (insert {u, v} M) < unmatched"
        using finiteM uv(1) by(auto simp add: IH(3))
      moreover have "graph_matching G ({{u, v}} \<union> M)"
        using uv IH(2) u(2) v(2) 
        by (auto intro!: matching_insert)
      ultimately obtain M' where "perfect_matching G M'" "insert {u, v} M \<subseteq> M'"
        using IH(1)[OF _ _ refl] by force
      thus ?thesis 
        by auto
    qed
  qed
qed

corollary perfect_matching_in_balanced_complete_bipartite:
  assumes "balanced_complete_bipartite G L R" "finite G"
  shows "\<exists> M. perfect_matching G M"
  using extend_to_perfect_matching_in_balanced_complete_bipartite[where M = empty] assms
  by auto

lemma part_bipart_of_cover_matching:
  fixes G :: "'a set set"
  fixes M
  assumes "partitioned_bipartite G A"
  assumes "cover_matching G M A"
  assumes "graph_invar G"
  shows "partitioned_bipartite M A"
proof -
  have M_subs:"M \<subseteq> G" 
    using assms(2) unfolding cover_matching_def by auto
  have "graph_invar G"
    using assms(1,3) partitioned_bipartite_def
    by auto
  then have "graph_invar M"
    using M_subs graph_invar_subset
    by auto
  have "A \<subseteq> Vs M" 
    using assms(2) unfolding cover_matching_def by auto
  have "\<forall> e \<in> G. \<exists> u v. e = {u, v} \<and> (u \<in> A \<and> v \<in> Vs G - A)"
    using assms(1) unfolding partitioned_bipartite_def by auto
  then have "\<forall>e \<in> M. \<exists> u v. e = {u, v} \<and> (u \<in> A \<and> v \<in> Vs M - A)" 
    by (metis M_subs Diff_iff edges_are_Vs insert_commute subsetD)
  then show ?thesis 
    unfolding partitioned_bipartite_def
    using \<open>A \<subseteq> Vs M\<close> \<open>graph_invar M\<close>  by auto
qed
end