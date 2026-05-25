(*Authors: Mohammad Abdulaziz, Thomas Ammer, Christoph Madlener*)
theory Bipartite
  imports Undirected_Set_Graphs Paths
begin

subsection \<open>Bipartite Graphs\<close>
text \<open>
  We are considering the online \<^emph>\<open>bipartite\<close> matching problem, hence, a definition of
  bipartiteness.
\<close>

subsubsection \<open>Definition and Basics\<close>

definition bipartite :: "'a graph \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "bipartite G X Y  = ( X \<inter> Y = {} \<and> (\<forall>e \<in> G. \<exists>u v. e = {u,v} \<and> u \<in> X \<and> v \<in> Y))"

lemma bipartiteI:
  assumes "X \<inter> Y = {}"
  assumes "\<And>e. e \<in> G \<Longrightarrow> \<exists>u v. e = {u,v} \<and> u \<in> X \<and> v \<in> Y"
  shows "bipartite G X Y"
  using assms
  unfolding bipartite_def
  by auto

lemma bipartiteE:
 "\<lbrakk>bipartite G L R;
   \<lbrakk>L \<inter> R = {}; \<And> e. e \<in> G \<Longrightarrow> \<exists>u v. e = {u,v} \<and> u \<in> L \<and> v \<in> R\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp add: bipartite_def)

lemma bipartite_disjointD:
  assumes "bipartite G X Y"
  shows "X \<inter> Y = {}"
  using assms
  unfolding bipartite_def
  by blast

lemma bipartite_edgeE:
  assumes "e \<in> G"
  assumes "bipartite G X Y"
  obtains x y where "x \<in> X" "y \<in> Y" "e = {x,y}" "x \<noteq> y"
  using assms
  unfolding bipartite_def
  by fast

lemma bipartite_vertex:
  assumes "x \<in> Vs G"
  assumes "bipartite G U V"
  shows "x \<in> U \<Longrightarrow> x \<notin> V"
    and "x \<in> V \<Longrightarrow> x \<notin> U"
    and "x \<notin> U \<Longrightarrow> x \<in> V"
    and "x \<notin> V \<Longrightarrow> x \<in> U"
  using assms
  unfolding bipartite_def Vs_def
  by auto

lemma bipartite_edgeD:
  assumes "{u,v} \<in> G"
  assumes "bipartite G X Y"
  shows
    "u \<in> X \<Longrightarrow> v \<in> Y - X"
    "u \<in> Y \<Longrightarrow> v \<in> X - Y"
    "v \<in> X \<Longrightarrow> u \<in> Y - X"
    "v \<in> Y \<Longrightarrow> u \<in> X - Y"
  using assms
  unfolding bipartite_def
  by fast+

lemma bipartite_empty[simp]: "X \<inter> Y = {} \<Longrightarrow> bipartite {} X Y"
  unfolding bipartite_def by blast

lemma bipartite_empty_part_iff_empty: "bipartite G {} Y \<longleftrightarrow> G = {}"
  unfolding bipartite_def by blast

lemma bipartite_commute:
  "bipartite G X Y \<Longrightarrow> bipartite G Y X"
  unfolding bipartite_def
  by fast

lemma bipartite_subgraph:
  "\<lbrakk>bipartite G X Y; G' \<subseteq> G\<rbrakk> \<Longrightarrow> bipartite G' X Y"
  unfolding bipartite_def
  by blast

lemma bipartite_vs_subset: "bipartite G X Y \<Longrightarrow> Vs G \<subseteq> X \<union> Y"
  unfolding bipartite_def Vs_def
  by auto

lemma finite_parts_bipartite_graph_invar:
  "\<lbrakk>finite X; finite Y; bipartite G X Y\<rbrakk> \<Longrightarrow> graph_invar G"
  by (auto simp: dblton_graph_def dest: bipartite_vs_subset intro: finite_subset elim!: bipartite_edgeE)

lemma bipartite_to_graph_abs:
  "\<lbrakk>bipartite G L R; finite G\<rbrakk> \<Longrightarrow> graph_abs G"
  by(fastforce simp add: bipartite_def graph_abs_def dblton_graph_def disjoint_iff
      intro!: finite_dbl_finite_verts) 

lemma finite_bipartite_graph_invar:
  "\<lbrakk>finite G; bipartite G X Y\<rbrakk> \<Longrightarrow> graph_invar G"
  by (auto simp: dblton_graph_def elim!: bipartite_edgeE simp: Vs_def)

lemma bipartite_insertI:
  assumes "bipartite G X Y"
  assumes "u \<in> X" "v \<in> Y"
  shows "bipartite (insert {u,v} G) X Y"
  using assms
  unfolding bipartite_def
  by auto

lemma bipartite_unionI:
  assumes "bipartite G X Y"
  assumes "bipartite H X Y"
  shows "bipartite (G \<union> H) X Y"
  using assms
  unfolding bipartite_def
  by auto

lemma bipartite_reduced_to_vs:
  "bipartite G X Y \<Longrightarrow> bipartite G (X \<inter> Vs G) (Y \<inter> Vs G)"
  unfolding bipartite_def
  by auto (metis edges_are_Vs insert_commute)

lemma bipartite_In_singletons:
  assumes "bipartite G U V"
  assumes "X \<in> ((\<inter>) V) ` G"
  shows "\<exists>x. X = {x}"
  using assms
  by (auto elim!: bipartite_edgeE dest: bipartite_disjointD)

lemma bipartite_eqI:
  assumes "bipartite M U V"
  assumes "e \<in> M"
  assumes "x \<in> e" "x \<in> V" "y \<in> e" "y \<in> V"
  shows "x = y"
  using assms
proof -
  from assms obtain u v where e: "e = {u,v}" "u \<in> U" "v \<in> V"
    by (auto elim: bipartite_edgeE)

  from assms have "U \<inter> V = {}"
    by (auto dest: bipartite_disjointD)

  with assms e show "x = y"
    by blast
qed

lemma bipartite_remove_vertices:
  "bipartite G U V \<Longrightarrow> bipartite (G \<setminus> X) U V"
  using remove_vertices_subgraph
  by (auto intro: bipartite_subgraph)

lemma Vs_of_edges_connecting_two_sets:
  "\<lbrakk> X \<noteq> {}; Y \<noteq> {}\<rbrakk> \<Longrightarrow> Vs ({{u, v} | u v. u\<in> X \<and> v \<in> Y}) = X \<union> Y"
  by(auto simp add: Vs_def)

lemma Vs_of_edges_connecting_two_sets_subs:
  "Vs ({{u, v} | u v. u\<in> X \<and> v \<in> Y}) \<subseteq> X \<union> Y"
  by(auto simp add: Vs_def)

lemma bipartite_even_and_odd_walk:
  assumes "bipartite G X Y" "x \<in> X"
          "walk_betw G x p y"
    shows "odd (length p) \<Longrightarrow> y \<in> X"
          "even (length p) \<Longrightarrow> y \<in> Y"
proof-
  have "(odd (length p) \<longrightarrow> y \<in> X) \<and> (even (length p) \<longrightarrow> y \<in> Y)"
    using assms(3)
  proof(induction p arbitrary: y rule: rev_induct)
    case Nil
    then show ?case by(simp add: walk_betw_def)
  next
    case (snoc x' xs)
    note IH = this
    show ?case 
    proof(cases "even (length (xs@[x]))")
      case True
      hence odd: "odd (length xs)" by simp
      have "\<exists> y'. walk_betw G x xs y' \<and> {y', y} \<in> G"
        using odd snoc(2) path_2[of G y] path_suff[of G _ "[_, y]"] snoc.prems[simplified walk_betw_def] 
        by(cases xs rule: rev_cases)
          (auto intro!: exI[of _ "last xs"] walk_reflexive_cong simp add: walk_pref)
      then obtain y' where y':"walk_betw G x xs y'" "{y', y} \<in> G"
        by auto
      moreover hence "y' \<in> X" 
        using snoc(1) odd by simp
      ultimately have "y \<in> Y"
        using assms(1) bipartite_edgeD(1) by fastforce
      thus ?thesis
        using True by fastforce
    next
      case False
      show ?thesis
      proof(cases xs rule: rev_cases)
        case Nil
        hence "y = x" 
          using IH(2) snoc.prems[simplified walk_betw_def]  
          by auto
        then show ?thesis 
          by (simp add: assms(2) local.Nil)
      next
        case (snoc list a)
      hence even: "even (length xs)"using False  by simp
      have "\<exists> y'. (walk_betw G x xs y' \<and> {y', y} \<in> G)"
        using IH(2)  path_suff[of G _ "[_, y]"] 
             snoc.prems[simplified walk_betw_def] 
        by(auto intro!: exI[of _ a] simp add: snoc walk_pref)
      then obtain y' where y':"walk_betw G x xs y'" "{y', y} \<in> G"
        by auto
      moreover hence "y' \<in> Y" 
        using IH(1) even by simp
      ultimately have "y \<in> X"
        using assms(1) bipartite_edgeD(2) by fastforce
      thus ?thesis
        using False by fastforce
    qed
  qed
qed
  thus  "odd (length p) \<Longrightarrow> y \<in> X" "even (length p) \<Longrightarrow> y \<in> Y" 
    by auto
qed

definition partitioned_bipartite where
  "partitioned_bipartite G X = (X \<subseteq> Vs G \<and> 
              (\<forall> e \<in> G. \<exists> u v. e = {u, v} \<and> (u \<in> X \<and> v \<in> Vs G - X)))"

lemma partitioned_bipartiteI:
 "\<lbrakk>X \<subseteq> Vs G; \<And> e. e \<in> G \<Longrightarrow> \<exists> u v. e = {u, v} \<and> (u \<in> X \<and> v \<in> Vs G - X)\<rbrakk>
   \<Longrightarrow> partitioned_bipartite G X"
and partitioned_bipartiteE:
 "\<lbrakk>partitioned_bipartite G X;
  \<lbrakk>X \<subseteq> Vs G; \<And> e. e \<in> G \<Longrightarrow> \<exists> u v. e = {u, v} \<and> (u \<in> X \<and> v \<in> Vs G - X)\<rbrakk> \<Longrightarrow> P\<rbrakk>
  \<Longrightarrow> P"
  by(auto simp add: partitioned_bipartite_def)

definition is_bipartite where 
  "is_bipartite E = (\<exists> X \<subseteq> Vs E. \<forall> e \<in> E. \<exists> u v. 
                                   e = {u, v} \<and> (u \<in> X \<and> v \<in> Vs E - X))"

lemma part_biparite_is_bipartite: "partitioned_bipartite G X \<longrightarrow> is_bipartite G "
  unfolding  partitioned_bipartite_def is_bipartite_def by auto

lemma neighbours_of_Vs_bipartite:
  assumes "partitioned_bipartite G A"
  shows "neighbours_of_Vs G A = Vs G - A" 
proof -
  have partition:"\<forall> e \<in> G. \<exists> u v. e = {u, v} \<and> (u \<in> A \<and> v \<in> Vs G - A)"
    using assms unfolding partitioned_bipartite_def by auto
  show ?thesis
  proof
    show "neighbours_of_Vs G A \<subseteq> Vs G - A"
      unfolding neighbours_of_Vs_def using partition insert_absorb insert_commute by fastforce
    show "Vs G - A \<subseteq> neighbours_of_Vs G A"
    proof
      fix x
      assume "x \<in> Vs G - A"
      then obtain e where "e \<in> G \<and> x \<in> e" 
        using DiffD1 vs_member_elim  by metis
      then obtain u  where 2:"e = {u, x} \<and> (u \<in> A \<and> x \<in> Vs G - A) \<and> u \<noteq> x" 
        using partition \<open>x \<in> Vs G - A\<close> by fastforce
      then have "u \<in> e" 
        by blast
      then show "x \<in> neighbours_of_Vs G A" 
        unfolding neighbours_of_Vs_def 
        by (smt (verit) "2" \<open>e \<in> G \<and> x \<in> e\<close> mem_Collect_eq)
    qed
  qed
qed

lemma partitioned_bipartite_swap:
  assumes "partitioned_bipartite G A"
  shows "partitioned_bipartite G (Vs G - A)" 
  using assms unfolding partitioned_bipartite_def  by fastforce 

lemma neighbours_of_Vs_intersection_is_empty:
  assumes "partitioned_bipartite G A"
  shows" \<forall>X \<subseteq> A. neighbours_of_Vs G X \<inter> X = {}" 
proof safe
  fix X x
  assume "X \<subseteq> A" "x \<in> neighbours_of_Vs G X" "x \<in> X"
  then show "x \<in> {}" 
    by (metis Diff_iff assms in_mono neighbours_of_Vs_subset neighbours_of_Vs_bipartite)
qed

lemma part_bipartite_diff:
  assumes "partitioned_bipartite G A" "graph_invar G"
  shows "partitioned_bipartite (G - X) (A \<inter> Vs (G - X))"
proof -
  let ?A' = "(A \<inter> Vs (G - X))" 
  have 2: "graph_invar (G - X)" 
    by (metis Diff_subset assms graph_invar_subset partitioned_bipartite_def)
  have  "A \<subseteq> Vs G" 
    by (metis assms partitioned_bipartite_def)
  have 3: "?A' \<subseteq> Vs (G - X)" by blast 
  have "( \<forall> e \<in> G - X. \<exists> u v.  e = {u, v} \<and> (u \<in> ?A' \<and> v \<in> Vs (G - X) - ?A'))"
  proof 
    fix e
    assume "e \<in> G - X"
    then obtain u v where u'_v': "e = {u, v} \<and> u \<noteq> v \<and> (u \<in> A \<and> v \<in> Vs G - A)"
      using `partitioned_bipartite G A` unfolding partitioned_bipartite_def 
      by (metis (no_types, lifting) Diff_iff \<open>e \<in> G - X\<close>)

    then have "u \<in> ?A'" 
      using UnionI u'_v' \<open>e \<in> G - X\<close> by auto

    then have "v \<in> Vs (G - X) - ?A'"
      using IntE u'_v' \<open>e \<in> G - X\<close> by auto
    then show "\<exists> ua va. e = {ua, va} \<and> (ua \<in> ?A' \<and> va \<in> Vs (G - X) - ?A')"
      using \<open>u \<in> ?A'\<close> u'_v' by blast
  qed
  then show ?thesis 
    using "2" 3 
    by (simp add: partitioned_bipartite_def)
qed

lemma partitioned_bipartite_project_to_verts:
  "partitioned_bipartite G A \<Longrightarrow> partitioned_bipartite (deltas G (A \<inter> X)) (A \<inter> X)"
proof(rule partitioned_bipartiteI, goal_cases)
  case 1
  then show ?case 
    by(auto simp add: deltas_def 
        elim!: partitioned_bipartiteE vs_member_elim[OF subsetD, of A G ] )
next
  case (2 e)
  then show ?case 
    by(auto  simp add: deltas_def 
        elim!: partitioned_bipartiteE 
        dest!: spec 
        intro!: exI[of  "\<lambda> u. \<exists> va. {ua, v} = {u, va} \<and> _ u va v" for v ua]
        exI[of  "\<lambda> va. {ua, v} = {u, va} \<and> _ u va v" for v ua u]) 
qed

lemma partioned_bipartite_project:
  "partitioned_bipartite G A 
  \<Longrightarrow> partitioned_bipartite (graph_inter_Vs G X) (A \<inter> (Vs (graph_inter_Vs G X)))"
proof(rule partitioned_bipartiteI, rule, goal_cases)
  case (1 x)
  then obtain e where e: "x \<in> e" "e \<in> (graph_inter_Vs G X)"
    using vs_member[of x "graph_inter_Vs G X"]
    by(auto elim!: partitioned_bipartiteE) 
  thus ?case 
    by auto
next
  case (2 e)
  hence e_in_G_X: "e \<in> G" "e \<subseteq> X"
    by(auto simp add: graph_inter_Vs_def)
  then obtain u v where uv: "e = {u, v}" "u \<in> A" "v \<in> Vs G - A"
    using 2(1) by(auto elim!: partitioned_bipartiteE)
  show ?case
    using uv 2(2) 
    by (auto intro!: exI[of "\<lambda> ua. \<exists> va. {u, v} = {ua, va} \<and> _  ua va" u]
        exI[of  "\<lambda> va. {u, v} = {u, va} \<and> _ va"])
qed

subsubsection \<open>Neighbourhoods in Bipartite Graphs\<close>

lemma Neighbourhood_bipartite:
  assumes"bipartite G X Y" "V \<subseteq> X \<or> V \<subseteq> Y"
  shows  "Neighbourhood G V = \<Union> (neighbourhood G ` V)"
proof(rule, all \<open>rule\<close>, goal_cases)
  case (1 u)
  then obtain v where uv:"{v, u} \<in> G" "v \<in> V"
    by(auto simp add: Neighbourhood_def)
  hence "u \<in> neighbourhood G v"
    by(auto simp add: neighbourhood_def edge_commute) 
  then show ?case 
    using uv(2) by auto
next
  case (2 u)
  then obtain v where v: "u \<in> neighbourhood G v" "v \<in> V" by auto
  hence uv:"{u, v} \<in> G"
    by(auto simp add: neighbourhood_def)
  hence "u \<notin> V"
    using v(2) assms by(fastforce simp add: bipartite_def)
  then show ?case 
    using edge_commute[OF uv] v(2)
    by(auto simp add: Neighbourhood_def) 
qed

lemma Neighbourhood_bipartite_left:
  assumes "bipartite G X Y" "V \<subseteq> X"
  shows   "Neighbourhood G V \<subseteq> Y"
  using assms
  by(auto simp add: doubleton_eq_iff bipartite_def Neighbourhood_def 
              dest: bipartite_edgeD(1))

lemma Neighbourhood_bipartite_mono:
  assumes "bipartite G X Y" "G' \<subseteq> G"
  shows   "Neighbourhood G' X \<subseteq> Neighbourhood G X"
  using assms
  by (auto simp add: doubleton_eq_iff bipartite_def Neighbourhood_def)

lemma Neighbourhood_bipartite_right:
  assumes "bipartite G X Y" "V \<subseteq> Y"
  shows   "Neighbourhood G V \<subseteq> X"
  using assms
  by (auto simp add: doubleton_eq_iff bipartite_def Neighbourhood_def 
               dest: bipartite_edgeD(2))


lemma bipartite_neighbours_of_Vs_Neighbourhood:
  assumes "partitioned_bipartite G A" "X \<subseteq> A"
  shows "neighbours_of_Vs G X = Neighbourhood G X"
  using assms
  by(auto simp add: neighbours_of_Vs_def Neighbourhood_def partitioned_bipartite_def
            intro!: bexI[of "\<lambda> u. x \<noteq> u \<and> (\<exists>e\<in>G. u \<in> e \<and> x \<in> e)"_ X for x]
                    exI[of "\<lambda>u. {u, x} \<in> G \<and> u \<in> X \<and> x \<notin> X" for x])

subsubsection \<open>Complete Bipartite Graphs\<close>

definition "complete_bipartite G L R = 
   (bipartite G L R \<and> (\<forall> u \<in> L. \<forall> v \<in> R. {u, v} \<in> G))"

lemma complete_bipartiteE:
  "complete_bipartite G L R \<Longrightarrow>
  (\<lbrakk>bipartite G L R; \<And> u v. \<lbrakk>u \<in> L; v \<in> R\<rbrakk> \<Longrightarrow> {u, v} \<in> G\<rbrakk> \<Longrightarrow> P)
  \<Longrightarrow> P"
  and complete_bipartiteI:
  "\<lbrakk>bipartite G L R; \<And> u v. \<lbrakk>u \<in> L; v \<in> R\<rbrakk> \<Longrightarrow> {u, v} \<in> G\<rbrakk> \<Longrightarrow> complete_bipartite G L R"
  and complete_bipartiteD:
  "complete_bipartite G L R \<Longrightarrow> bipartite G L R"
  "\<lbrakk>complete_bipartite G L R; u \<in> L; v \<in> R\<rbrakk> \<Longrightarrow> {u, v} \<in> G"
  by(auto simp add: complete_bipartite_def)

lemma complete_bipartite_Vs:
  assumes "complete_bipartite G L R" "dblton_graph G" "L = {} \<longleftrightarrow> R = {}"
  shows "Vs G = L \<union> R"
  using assms
  by(auto elim!: complete_bipartiteE bipartite_edgeE 
      intro: bipartite_vertex(3) 
      dest!: edges_are_Vs) blast

definition "balanced_complete_bipartite G L R = (complete_bipartite G L R \<and> card L = card R)"

lemma balanced_complete_bipartiteE:
  "\<lbrakk>balanced_complete_bipartite G L R; \<lbrakk>complete_bipartite G L R; card L = card R\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  and balanced_complete_bipartiteI:
  "\<lbrakk>complete_bipartite G L R; card L = card R\<rbrakk> \<Longrightarrow> balanced_complete_bipartite G L R"
  and balanced_complete_bipartiteD:
  "balanced_complete_bipartite G L R \<Longrightarrow> complete_bipartite G L R"
  "balanced_complete_bipartite G L R \<Longrightarrow> card L = card R"
  by(auto simp add: balanced_complete_bipartite_def)
end