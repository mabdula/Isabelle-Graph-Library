(*
  Author: Christoph Madlener
*)

theory Ranking_Order
  imports
    Matching_LPs.Bipartite_Matching_LP
    Order_Relations
begin

sledgehammer_params [provers = cvc4 vampire verit e spass z3 zipperposition]

definition step :: "('a \<times> 'a) set \<Rightarrow> 'a graph \<Rightarrow> 'a graph \<Rightarrow> 'a \<Rightarrow> 'a graph" where
  "step r G M j = (
    let ns = {i. i \<notin> Vs M \<and> {i, j} \<in> G} in
      if ns \<noteq> {} \<and> j \<notin> Vs M
      then let i = min_on_rel ns r in insert {i, j} M
      else M
  )"

definition "ranking' r G M = foldl (step r G) M"
abbreviation "ranking r G \<equiv> ranking' r G {}"

lemma step_cases'[case_names no_neighbor j_matched new_match]:
  assumes "{i. i \<notin> Vs M \<and> {i,j} \<in> G} = {} \<Longrightarrow> P"
  assumes "j \<in> Vs M \<Longrightarrow> P"
  assumes "{i. i \<notin> Vs M \<and> {i,j} \<in> G} \<noteq> {} \<Longrightarrow> j \<notin> Vs M \<Longrightarrow> P"
  shows "P"
  using assms
  by blast

lemma finite_unmatched_neighbors[intro]:
  "finite (Vs G) \<Longrightarrow> finite {i. i \<notin> Vs M \<and> {i,j} \<in> G}"
  by (rule finite_subset[of _ "Vs G"]) (auto intro: vs_member_intro)

lemma step_cases[consumes 2, case_names no_neighbor j_matched new_match]:
  fixes G M j
  defines "ns \<equiv> {i. i \<notin> Vs M \<and> {i, j} \<in> G}"
  assumes "preorder_on' {i. {i,j} \<in> G} r" and "finite (Vs G)"
  assumes "{i. i \<notin> Vs M \<and> {i, j} \<in> G} = {} \<Longrightarrow> P"
  assumes "j \<in> Vs M \<Longrightarrow> P"
  assumes 
    "\<lbrakk>ns \<noteq> {}; j \<notin> Vs M; min_on_rel ns r \<in> ns; 
      \<not>(\<exists>i' \<in> ns. (i', min_on_rel ns r) \<in> r \<and> (min_on_rel ns r, i') \<notin> r)\<rbrakk> \<Longrightarrow> P"
  shows "P"
proof (cases M j G rule: step_cases')
  case new_match

  have "min_on_rel ns r \<in> ns"
  proof (intro min_if_finite, goal_cases)
    case 1
    from \<open>preorder_on' {i. {i,j} \<in> G} r\<close> show ?case
      unfolding ns_def
      by (auto intro: preorder_on'_subset)
  next
    case 2
    from \<open>finite (Vs G)\<close> show ?case
      unfolding ns_def
      by blast
  next
    case 3
    from new_match show ?case
      unfolding ns_def
      by blast
  qed

  have "\<not>(\<exists>i'\<in>ns. (i', min_on_rel ns r) \<in> r \<and> (min_on_rel ns r, i') \<notin> r)"
  proof (intro min_if_finite, goal_cases)
    case 1
    from \<open>preorder_on' {i. {i,j} \<in> G} r\<close> show ?case
      unfolding ns_def
      by (auto intro: preorder_on'_subset)
  next
    case 2
    from \<open>finite (Vs G)\<close> show ?case
      unfolding ns_def
      by blast
  next
    case 3
    from new_match show ?case
      unfolding ns_def
      by blast
  qed

  with new_match \<open>min_on_rel ns r \<in> ns\<close> assms show ?thesis
    by blast
qed (use assms in \<open>blast+\<close>)

lemma ranking_Nil[simp]: "ranking' r G M [] = M"
  unfolding ranking'_def by simp

lemma ranking_Cons: "ranking' r G M (j#js) = ranking' r G (step r G M j) js"
  unfolding ranking'_def
  by simp

lemma ranking_append: "ranking' r G M (js@js') = ranking' r G (ranking' r G M js) js'"
  unfolding ranking'_def
  by simp

lemma step_insertI:
  assumes "{i. i \<notin> Vs M \<and> {i,j} \<in> G} \<noteq> {}" "j \<notin> Vs M"
  assumes "i = min_on_rel {i. i \<notin> Vs M \<and> {i,j} \<in> G} r"
  shows "step r G M j = insert {i,j} M"
  using assms
  by (simp add: step_def)

lemma step_online:
  "step r G M j = step r {e \<in> G. j \<in> e} M j"
  unfolding step_def
  by simp

lemma step_subgraph:
  assumes fin: "finite (Vs G)"
  assumes preorder: "preorder_on' {i. {i,j} \<in> G} r"
  assumes "M \<subseteq> G" 
  shows "step r G M j \<subseteq> G"
  using preorder fin
  by (cases rule: step_cases[where M = M]) (use assms in \<open>simp_all add: step_def\<close>)

lemma ranking_subgraph:
  assumes "finite (Vs G)"
  assumes "\<forall>j\<in>set js. preorder_on' {i. {i,j} \<in> G} r"
  assumes "M \<subseteq> G"
  shows "ranking' r G M js \<subseteq> G"
  using assms
  by (induction js arbitrary: M)
     (auto simp: ranking_Cons dest: step_subgraph)

lemma matching_step:
  assumes fin: "finite (Vs G)"
  assumes preorder: "preorder_on' {i. {i,j} \<in> G} r"
  assumes "matching M"
  shows "matching (step r G M j)"
  using preorder fin
  by (cases rule: step_cases[where M = M])
     (use assms in \<open>auto simp: step_def intro: matching_insert\<close>)

lemma matching_ranking:
  assumes "finite (Vs G)"
  assumes "\<forall>j\<in>set js. preorder_on' {i. {i,j} \<in> G} r"
  assumes "matching M"
  shows "matching (ranking' r G M js)"
  using assms
  by (induction js arbitrary: M)
     (auto simp: ranking_Cons dest: matching_step)

lemma step_mono:
  assumes "e \<in> M"
  shows "e \<in> step r G M j"
  using assms
  by (cases M j G rule: step_cases')
     (auto simp: step_def)

lemma ranking_mono:
  assumes "e \<in> M"
  shows "e \<in> ranking' r G M js"
  using assms
  by (induction js arbitrary: M)
     (auto simp: ranking_Cons dest: step_mono)

lemma ranking_mono_vs:
  assumes "v \<in> Vs M"
  shows "v \<in> Vs (ranking' r G M js)"
  using assms
  by (auto simp: vs_member dest: ranking_mono)

lemma edge_in_step:
  assumes "e \<in> step r G M j"
  shows "e \<in> M \<or> j \<in> e"
  using assms
  by (auto simp: step_def split: if_splits)

lemma edge_in_ranking:
  assumes "e \<in> ranking' r G M js"
  shows "e \<in> M \<or> (\<exists>j \<in> set js. j \<in> e)"
  using assms
  by (induction js arbitrary: M)
     (auto dest: edge_in_step simp: ranking_Cons)

lemma edge_in_rankingE:
  assumes "e \<in> ranking' r G M js"
  obtains "e \<in> M" | j where "j \<in> set js" "j \<in> e"
  using assms
  by (auto dest: edge_in_ranking)

lemma step_matches_if_possible:
  assumes "j \<notin> Vs M"
  assumes "{i,j} \<in> G"
  assumes "i \<notin> Vs M"
  shows "j \<in> Vs (step r G M j)"
  using assms
  by (cases M j G rule: step_cases')
     (auto simp: step_def vs_insert)

context bipartite_matching_lp
begin

lemma finite_vs_subgraph[simp]: "H \<subseteq> G \<Longrightarrow> finite (Vs H)"
  using finite_vs
  by (auto intro: finite_subset dest: Vs_subset)

lemma finite_subsets: "finite {M. M \<subseteq> G}"
  using finite_graph by blast

lemma neighbors_right_subset_left: "H \<subseteq> G \<Longrightarrow> j \<in> R \<Longrightarrow> {i. {i,j} \<in> H} \<subseteq> L"
  using bipartite_graph
  by (auto dest: bipartite_edgeD)

lemma neighbors_right_subset_left_remove_vertices: "j \<in> R \<Longrightarrow> {i. {i,j} \<in> G \<setminus> X} \<subseteq> L - X"
  by (auto dest: neighbors_right_subset_left[OF remove_vertices_subgraph] edges_are_Vs intro: remove_vertices_not_vs')

lemma preorder_on_neighborsI[intro]:
  assumes "H \<subseteq> G"
  assumes "preorder_on L r"
  assumes "j \<in> R"
  shows "preorder_on' {i. {i,j} \<in> H} r"
  using assms
  by (auto dest: preorder_on_imp_preorder_on' neighbors_right_subset_left intro: preorder_on'_subset)

lemma preorder_on_neighborsI_remove_vertices[intro]:
  assumes "preorder_on (L - X) r"
  assumes "j \<in> R"
  shows "preorder_on' {i. {i,j} \<in> G \<setminus> X} r"
  using assms
  by (auto dest: preorder_on_imp_preorder_on' neighbors_right_subset_left_remove_vertices intro: preorder_on'_subset)

lemma linorder_on_neighborsI[intro]:
  assumes "H \<subseteq> G"
  assumes "linorder_on L r"
  assumes "j \<in> R"
  shows "linorder_on' {i. {i,j} \<in> H} r"
  using assms
  by (auto dest: linorder_on_imp_linorder_on' neighbors_right_subset_left intro: linorder_on'_subset)

lemma linorder_on_neighborsI_remove_vertices[intro]:
  assumes "linorder_on (L - X) r"
  assumes "j \<in> R"
  shows "linorder_on' {i. {i,j} \<in> G \<setminus> X} r"
  using assms
  by (auto dest: linorder_on_imp_linorder_on' neighbors_right_subset_left_remove_vertices intro: linorder_on'_subset)

lemma finite_neighbors:
  "H \<subseteq> G \<Longrightarrow> finite {i. {i,j} \<in> H}"
  by (rule finite_subset[of _ "Vs G"])
     (auto simp: graph intro: vs_member_intro)

lemma finite_unmatched_neighbors:
  "H \<subseteq> G \<Longrightarrow> finite {i. i \<notin> Vs M \<and> {i,j} \<in> H}"
  by (rule finite_subset[of _ "Vs G"])
     (auto simp: graph intro: vs_member_intro)

lemma unmatched_neighbors_L:
  assumes "H \<subseteq> G"
  assumes "j \<in> R"
  shows "{i. i \<notin> Vs M \<and> {i,j} \<in> H} \<subseteq> L"
  using assms bipartite_graph
  by (auto dest: bipartite_edgeD)

lemma min_in_L:
  assumes "H \<subseteq> G"
  assumes "preorder_on' {i. {i,j} \<in> H} r"
  assumes "j \<in> R"
  assumes "i \<notin> Vs M" "{i,j} \<in> H"
  shows "min_on_rel {i. i \<notin> Vs M \<and> {i, j} \<in> H} r \<in> L" (is "min_on_rel ?S r \<in> L")
proof -
  from assms have "min_on_rel ?S r \<in> ?S"
    by (intro min_if_finite finite_unmatched_neighbors)
       (auto intro: preorder_on'_subset)

  with \<open>H \<subseteq> G\<close> \<open>j \<in> R\<close> bipartite_graph show ?thesis
    by (auto dest: bipartite_edgeD bipartite_subgraph)
qed

lemma unmatched_R_in_step_if:
  assumes "H \<subseteq> G"
  assumes preorder: "preorder_on' {i. {i,j'} \<in> H} r"
  assumes "j' \<in> R" "j' \<noteq> j"
  assumes "j \<notin> L" "j \<notin> Vs M"
  shows "j \<notin> Vs (step r H M j')"
  using assms
  by (cases M j' H rule: step_cases')
     (auto simp: step_def vs_insert dest: min_in_L)

lemma unmatched_R_in_ranking_if:
  assumes "H \<subseteq> G"
  assumes "\<forall>j \<in> set js. preorder_on' {i. {i,j} \<in> H} r"
  assumes "set js \<subseteq> R"
  assumes "j \<notin> L" "j \<notin> set js"
  assumes "j \<notin> Vs M"
  shows "j \<notin> Vs (ranking' r H M js)"
  using assms
proof (induction js arbitrary: M)
  case (Cons j' js)

  then have "j \<notin> Vs (step r H M j')"
    by (intro unmatched_R_in_step_if) auto

  with Cons show ?case
    by (simp add: ranking_Cons)
qed simp

lemma bipartite_step:
  assumes subgraph: "H \<subseteq> G"
  assumes preorder: "preorder_on' {i. {i,j} \<in> H} r"
  assumes "bipartite M L R"
  assumes "j \<in> R"
  shows "bipartite (step r H M j) L R"
  using preorder finite_vs_subgraph[OF subgraph]
  by (cases rule: step_cases[where M = M])
     (use assms in \<open>auto simp: step_def intro!: bipartite_insertI dest: neighbors_right_subset_left\<close>)

lemma bipartite_ranking:
  assumes "H \<subseteq> G"
  assumes "\<forall>j\<in>set js. preorder_on' {i. {i,j} \<in> H} r"
  assumes "set js \<subseteq> R"
  assumes "bipartite M L R"
  shows "bipartite (ranking' r H M js) L R"
  using assms
  by (induction js arbitrary: M)
     (auto simp: ranking_Cons dest: bipartite_step)

lemma ranking_subgraph:
  assumes "H \<subseteq> G"
  assumes "preorder_on L r"
  assumes "set js \<subseteq> R"
  shows "ranking r H js \<subseteq> H"
  using assms graph
  by (intro ranking_subgraph)
     (auto intro: ranking_subgraph finite_vs_subgraph)

lemma ranking_subgraph':
  assumes "H \<subseteq> G"
  assumes "preorder_on L r"
  assumes "set js \<subseteq> R"
  shows "e \<in> ranking r H js \<Longrightarrow> e \<in> H"
  using assms
  by (auto dest: ranking_subgraph)

lemma the_ranking_match_left:
  assumes "H \<subseteq> G"
  assumes "\<forall>j\<in>set js. preorder_on' {i. {i,j} \<in> H} r"
  assumes "matching M"
  assumes "bipartite M L R"
  assumes j_matched: "j \<in> Vs (ranking' r H M js)"
  assumes "j \<in> R"
  assumes "set js \<subseteq> R"
  shows "{THE i. {i,j} \<in> ranking' r H M js, j} \<in> ranking' r H M js"
    "(THE i. {i,j} \<in> ranking' r H M js) \<in> L"
proof -
  from j_matched obtain e where e: "e \<in> ranking' r H M js" "j \<in> e"
    by (auto elim: vs_member_elim)

  from assms have bipartite: "bipartite (ranking' r H M js) L R"
    by (auto intro: bipartite_ranking)

  with e obtain u v where uv: "e = {u,v}" "u \<noteq> v" "u \<in> L" "v \<in> R"
    by (auto elim: bipartite_edgeE)

  with bipartite \<open>j \<in> R\<close> e have "v = j"
    by (auto intro: bipartite_eqI)

  with e uv assms have "(THE i. {i,j} \<in> ranking' r H M js) = u"
    by (intro the_match matching_ranking finite_subset[OF Vs_subset finite_vs])
        auto  

  with e uv \<open>v = j\<close> show "{THE i. {i, j} \<in> ranking' r H M js, j} \<in> ranking' r H M js"
    "(THE i. {i, j} \<in> ranking' r H M js) \<in> L"
    by auto
qed

lemma step_remove_unmatched_eq:
  assumes linorder: "linorder_on L r" \<comment> \<open>required because of \<^term>\<open>Eps\<close> in \<^term>\<open>min_on_rel\<close>\<close>

  assumes "i \<in> L" "j \<in> R"
  assumes "i \<notin> Vs (step r G M j)"
  shows "step r (G \<setminus> {i}) M j = step r G M j"
proof -
  from linorder \<open>j \<in> R\<close> have "preorder_on' {i. {i,j} \<in> G} r"
    by (auto dest: linorder_on_imp_preorder_on)

  from this finite_vs
  show ?thesis
  proof (cases rule: step_cases[where M = M])
    case new_match
    let ?ns = "{i'. i' \<notin> Vs M \<and> {i',j} \<in> G}"
    and ?ns' = "{i'. i' \<notin> Vs M \<and> {i',j} \<in> G \<setminus> {i}}"

    let ?min = "min_on_rel ?ns r"
    and ?min' = "min_on_rel ?ns' r"

    from \<open>j \<in> R\<close> have "?ns \<subseteq> L" "?ns' \<subseteq> ?ns"
      by (auto dest: remove_vertices_subgraph' neighbors_right_subset_left[OF subset_refl])

    then have "?ns' \<subseteq> L"
      by blast

    from new_match have step_eq: "step r G M j = insert {?min, j} M"
      by (simp add: step_def)

    with \<open>i \<notin> Vs (step r G M j)\<close> have "?min \<noteq> i" "j \<noteq> i"
      by (auto simp: vs_insert)

    with \<open>?min \<in> ?ns\<close> have "?ns' \<noteq> {}"
      by (auto intro: in_remove_verticesI)

    have "?min' = ?min"
    proof (intro min_on_rel_linorder_eq, goal_cases)
      case 1
      from linorder \<open>?ns' \<subseteq> L\<close> show ?case
        by (auto dest: linorder_on_imp_linorder_on' intro: linorder_on'_subset)
    next
      case 2
      from \<open>?min \<in> ?ns\<close> \<open>?min \<noteq> i\<close> \<open>j \<noteq> i\<close> show ?case
        by (auto intro: in_remove_verticesI)
    next
      case 3
      from \<open>?ns' \<subseteq> ?ns\<close> \<open>preorder_on' {i. {i,j} \<in> G} r\<close> show ?case
      proof (intro ballI min_on_rel_least, goal_cases)
        case 1
        from linorder \<open>?ns \<subseteq> L\<close> show ?case
          by (auto dest: linorder_on_imp_linorder_on' intro: linorder_on'_subset)
      next
        case 2
        show ?case
          by (auto intro: finite_subset)
      next
        case 3
        from new_match show ?case by blast
      next
        case (4 y)
        with \<open>?ns' \<subseteq> ?ns\<close> show ?case
          by blast
      qed
    qed

    with \<open>j \<notin> Vs M\<close> \<open>?ns' \<noteq> {}\<close> show ?thesis
      by (subst step_eq) (simp add: step_def)
  qed (use assms in \<open>auto simp: step_def dest: remove_vertices_subgraph'\<close>)
qed

lemma ranking_remove_unmatched_eq:
  assumes linorder: "linorder_on L r"

  assumes "i \<in> L" and "set js \<subseteq> R"
  assumes "i \<notin> Vs (ranking' r G M js)"
  shows "ranking' r (G \<setminus> {i}) M js = ranking' r G M js"
  using assms
proof (induction js arbitrary: M)
  case (Cons j js)

  from Cons.prems have "step r (G \<setminus> {i}) M j = step r G M j"
    by (intro step_remove_unmatched_eq)
       (auto simp: ranking_Cons dest: ranking_mono_vs)

  with Cons show ?case
    by (simp add: ranking_Cons)
qed simp

lemma dominance_order_matched:
  assumes linorder: "linorder_on L r"

  assumes "i \<in> L" "j \<in> R"
  assumes "set js = R"
  assumes "{i,j} \<in> G"

  assumes "{i',j} \<in> ranking r (G \<setminus> {i}) js"
  assumes less: "(i,i') \<in> r" "(i',i) \<notin> r"
  shows "i \<in> Vs (ranking r G js)"
proof -
  from \<open>set js = R\<close> \<open>j \<in> R\<close> obtain pre suff where js_split: "js = pre @ j # suff" "j \<notin> set pre"
    by (auto dest: split_list_first)

  with linorder \<open>set js = R\<close> \<open>j \<in> R\<close>
  have j_unmatched_pre: "j \<notin> Vs (ranking r (G \<setminus> {i}) pre) \<and> j \<notin> Vs (ranking r G pre)"
    by (intro unmatched_R_in_ranking_if conjI)
       (auto dest: remove_vertices_subgraph' linorder_on_imp_preorder_on)

  from linorder \<open>set js = R\<close> have preorder_neighbors:
    "j' \<in> set js \<Longrightarrow> preorder_on' {i'. {i', j'} \<in> G \<setminus> {i}} r" for j'
    by (auto dest: linorder_on_imp_preorder_on remove_vertices_subgraph')

  with \<open>set js = R\<close> linorder have bipartite_js: "bipartite (ranking r (G \<setminus> {i}) js) L R"
    by (intro bipartite_ranking)
       (auto dest: remove_vertices_subgraph')

  with \<open>{i',j} \<in> ranking r (G \<setminus> {i}) js\<close> \<open>j \<in> R\<close> have \<open>i' \<in> L\<close>
    by (auto dest: bipartite_edgeD)

  from preorder_neighbors have "matching (ranking r (G \<setminus> {i}) js)"
    by (auto intro!: matching_ranking simp add: graph graph_invar_remove_vertices)

  from \<open>i \<in> L\<close> \<open>i' \<in> L\<close> \<open>j \<in> R\<close> have "i \<noteq> j" "i' \<noteq> j"
    by auto

  from less have "i \<noteq> i'"
    by auto

  from linorder \<open>set js = R\<close> have "{i',j} \<in> G \<setminus> {i}"
    by (auto dest: linorder_on_imp_preorder_on remove_vertices_subgraph' 
             intro!: ranking_subgraph'[OF _ _ _ \<open>{i',j} \<in> ranking r (G \<setminus> {i}) js\<close>])

  show ?thesis
  proof (cases "i \<in> Vs (ranking r G pre)")
    case True
    with js_split show ?thesis
      by (auto simp: ranking_append dest: ranking_mono_vs)
  next
    case False

    have i'_unmatched_pre: "i' \<notin> Vs (ranking r (G \<setminus> {i}) pre)"
    proof (rule ccontr, simp only: not_not)
      assume "i' \<in> Vs (ranking r (G \<setminus> {i}) pre)"
      then obtain e where e: "e \<in> ranking r (G \<setminus> {i}) pre" "i' \<in> e"
        by (auto elim: vs_member_elim)

      from e js_split have "e \<in> ranking r (G \<setminus> {i}) js"
        by (auto simp: ranking_append intro: ranking_mono)

      from e obtain j' where "j' \<in> e" "j' \<in> set pre"
        by (auto elim: edge_in_rankingE)

      with js_split \<open>set js = R\<close> have "j' \<in> R" "j' \<noteq> j"
        by auto

      with \<open>i' \<in> L\<close> \<open>j \<in> R\<close> \<open>i' \<in> e\<close> \<open>j' \<in> e\<close> have "e \<noteq> {i',j}" "e \<inter> {i',j} \<noteq> {}"
        by auto

      with \<open>{i',j} \<in> ranking r (G \<setminus> {i}) js\<close> \<open>e \<in> ranking r (G \<setminus> {i}) js\<close>
      have "\<not>matching (ranking r (G \<setminus> {i}) js)"
        unfolding matching_def
        by force

      with \<open>matching (ranking r (G \<setminus> {i}) js)\<close> show False
        by blast
    qed

    from assms False js_split have ranking_pre_eq: "ranking r (G \<setminus> {i}) pre = ranking r G pre"
      by (intro ranking_remove_unmatched_eq) auto

    let ?ns = "{i. i \<notin> Vs (ranking r G pre) \<and> {i,j} \<in> G}"
    and ?ns' = "{i'. i' \<notin> Vs (ranking r (G \<setminus> {i}) pre) \<and> {i',j} \<in> G \<setminus> {i}}" 

    from False \<open>i \<noteq> j\<close> \<open>{i,j} \<in> G\<close> have *: "?ns = insert i ?ns'"
      by (auto intro: in_remove_vertices_vsI in_remove_verticesI 
               dest: edges_are_Vs remove_vertices_subgraph'
               simp: ranking_pre_eq)

    from i'_unmatched_pre \<open>{i',j} \<in> G \<setminus> {i}\<close> have "i' \<in> ?ns'"
      by auto

    have **: "min_on_rel ?ns' r = i'"
    proof (rule ccontr)
      assume "min_on_rel ?ns' r \<noteq> i'"
      then obtain i'' where i'': "i'' = min_on_rel ?ns' r" "i'' \<noteq> i'"
        by blast   

      with \<open>i' \<in> ?ns'\<close> j_unmatched_pre have "step r (G \<setminus> {i}) (ranking r (G \<setminus> {i}) pre) j = insert {i'',j} (ranking r (G \<setminus> {i}) pre)"
        by (auto simp: step_def)

      with js_split have "{i'',j} \<in> ranking r (G \<setminus> {i}) js"
        by (auto simp: ranking_append ranking_Cons intro: ranking_mono)

      with \<open>{i',j} \<in> ranking r (G \<setminus> {i}) js\<close> \<open>i'' \<noteq> i'\<close> \<open>i' \<noteq> j\<close> have "\<not>matching (ranking r (G \<setminus> {i}) js)"
        unfolding matching_def
        by fast

      with \<open>matching (ranking r (G \<setminus> {i}) js)\<close> show False
        by blast
    qed

    have "min_on_rel ?ns r = i"
    proof (intro min_on_rel_linorder_eq ballI, goal_cases)
      case 1
      from linorder \<open>j \<in> R\<close> show ?case
        by (auto intro: linorder_on'_subset[OF _ unmatched_neighbors_L] unmatched_neighbors_L
                 dest: linorder_on_imp_linorder_on')
    next
      case 2
      from * show ?case
        by blast
    next
      case (3 y)
      have "\<lbrakk>i'' \<notin> Vs (ranking r (G \<setminus> {i}) pre); {i'',j} \<in> G \<setminus> {i}\<rbrakk> \<Longrightarrow> (i',i'') \<in> r" for i''
      proof (subst **[symmetric], intro min_on_rel_least, goal_cases)
        case 1
        from linorder \<open>j \<in> R\<close> show ?case
          by (auto intro: linorder_on'_subset[OF _ unmatched_neighbors_L]
                   dest: linorder_on_imp_linorder_on' remove_vertices_subgraph')
      next
        case 2
        then show ?case
          by (auto intro: finite_unmatched_neighbors dest: remove_vertices_subgraph')
      qed blast+

      with 3 linorder \<open>(i,i') \<in> r\<close> \<open>i \<in> L\<close> show ?case
        unfolding *
        by (auto dest: linorder_on_imp_linorder_on' linorder_on'_transD transD linorder_on'_refl_on'D refl_on'D)
    qed

    with False \<open>{i,j} \<in> G\<close> \<open>i' \<in> ?ns'\<close> j_unmatched_pre have "step r G (ranking r G pre) j = insert {i,j} (ranking r G pre)"
      by (auto simp: step_def)

    with js_split show ?thesis
      by (auto simp: ranking_append ranking_Cons vs_insert intro: ranking_mono_vs)
  qed
qed

lemma dominance_order_unmatched:
  assumes linorder: "linorder_on L r"

  assumes "i \<in> L"
  assumes "j \<in> set js"
  assumes "set js \<subseteq> R"

  assumes "{i,j} \<in> G"
  assumes "j \<notin> Vs (ranking r (G \<setminus> {i}) js)"
  shows "i \<in> Vs (ranking r G js)"
proof -
  from \<open>j \<in> set js\<close> obtain pre suff where js_split: "js = pre @ j # suff"
    by (auto dest: split_list)

  from \<open>j \<in> set js\<close> \<open>set js \<subseteq> R\<close> have "j \<in> R"
    by blast

  with \<open>i \<in> L\<close> have "i \<noteq> j"
    by auto

  from js_split \<open>j \<notin> Vs (ranking r (G \<setminus> {i}) js)\<close> have j_not_pre:  "j \<notin> Vs (ranking r (G \<setminus> {i}) pre)"
    by (auto simp: ranking_append dest: ranking_mono_vs)

  show ?thesis
  proof (cases "i \<in> Vs (ranking r G pre)")
    case True
    with js_split show ?thesis
      by (auto simp: ranking_append dest: ranking_mono_vs)
  next
    case False

    with assms js_split have pre_eq: "ranking r (G \<setminus> {i}) pre = ranking r G pre"
      by (intro ranking_remove_unmatched_eq) auto

    have "step r G (ranking r G pre) j = insert {i,j} (ranking r G pre)"
    proof (intro step_insertI, goal_cases)
      case 1
      from False \<open>{i,j} \<in> G\<close> show ?case
        by blast
    next
      case 2
      from j_not_pre show ?case
        by (simp add: pre_eq)
    next
      case 3
      have "{i'. i' \<notin> Vs (ranking r (G \<setminus> {i}) pre) \<and> {i',j} \<in> G \<setminus> {i}} = {}"
      proof (rule ccontr)
        let ?ns' = "{i'. i' \<notin> Vs (ranking r (G \<setminus> {i}) pre) \<and> {i',j} \<in> G \<setminus> {i}}"
        assume "?ns' \<noteq> {}"

        with j_not_pre have "step r (G \<setminus> {i}) (ranking r (G \<setminus> {i}) pre) j =
          insert {min_on_rel ?ns' r, j} (ranking r (G \<setminus> {i}) pre)"
          by (auto simp: step_def)


        with js_split have "j \<in> Vs (ranking r (G \<setminus> {i}) js)"
          by (auto simp: ranking_append ranking_Cons vs_insert intro: ranking_mono_vs)

        with \<open>j \<notin> Vs (ranking r (G \<setminus> {i}) js)\<close> show False
          by blast
      qed

      with False \<open>{i,j} \<in> G\<close> \<open>i \<noteq> j\<close> have "{i. i \<notin> Vs (ranking r G pre) \<and> {i,j} \<in> G} = {i}"
        by (auto simp: pre_eq intro: in_remove_verticesI)


      then show ?case
        by (simp flip: min_on_rel_singleton)
    qed

    with js_split show ?thesis
      by (auto simp: ranking_append ranking_Cons vs_insert intro: ranking_mono_vs)
  qed
qed

lemma dominance_order:
  assumes linorder: "linorder_on L r"

  assumes "i \<in> L" and "j \<in> R"
  assumes "set js = R"
  assumes "{i, j} \<in> G"

  defines "i' \<equiv> (THE i'. {i', j} \<in> ranking r (G \<setminus> {i}) js)"
  assumes "j \<in> Vs (ranking r (G \<setminus> {i}) js) \<Longrightarrow>  (i, i') \<in> r \<and> (i', i) \<notin> r"
  shows "i \<in> Vs (ranking r G js)"
proof (cases "j \<in> Vs (ranking r (G \<setminus> {i}) js)")
  case True
  then obtain e where e: "e \<in> ranking r (G \<setminus> {i}) js" "j \<in> e"
    by (auto elim: vs_member_elim)

  interpret G': graph_abs "G \<setminus> {i}"
    apply unfold_locales
    using graph
    by (rule graph_invar_subgraph[of G])
       (auto simp: dest: remove_vertices_subgraph')

  have "e \<in> G \<setminus> {i}"
    by (rule ranking_subgraph')
       (use linorder e \<open>set js = R\<close>
          in \<open>auto dest: remove_vertices_subgraph' 
                         linorder_on_imp_preorder_on preorder_on_imp_preorder_on'\<close>)
  
  with \<open>j \<in> e\<close> G'.graph obtain i' where "e = {i',j}"
    by fast

  from G'.graph linorder \<open>j \<in> R\<close> \<open>set js = R\<close> have "matching (ranking r (G \<setminus> {i}) js)"
    by (auto intro!: matching_ranking intro: preorder_on'_subset[OF _ neighbors_right_subset_left]
             dest: linorder_on_imp_preorder_on preorder_on_imp_preorder_on' remove_vertices_subgraph')

  with e \<open>e = {i',j}\<close> have the_i': "(THE i'. {i',j} \<in> ranking r (G \<setminus> {i}) js) = i'"
    by (auto dest: the_match)

  from assms True e \<open>e = {i',j}\<close> show ?thesis
    by (intro dominance_order_matched) (auto simp: the_i')
next
  case False
  with assms show ?thesis
    by (auto intro: dominance_order_unmatched)
qed

lemma monotonicity_order_step:
  assumes "i \<in> L" "j \<in> R"

  assumes "j \<notin> Vs M" "j \<notin> Vs M'"

  assumes linorder: "linorder_on' {i. {i, j} \<in> G} r"
  assumes subset_before: "L - {i} - Vs M' \<subseteq> L - Vs M"
  shows "L - {i} - Vs (step r (G \<setminus> {i}) M' j) \<subseteq> L - Vs (step r G M j)"
  using linorder_on'_imp_preorder_on'[OF linorder] finite_vs
proof (cases rule: step_cases[where M = M])
  case no_neighbor
  with bipartite_graph subset_before \<open>i \<in> L\<close> \<open>j \<in> R\<close> have "{i'. i' \<notin> Vs M' \<and> {i',j} \<in> G \<setminus> {i}} = {}"
    apply auto
    by (smt (verit, best) Diff_iff bipartite_edgeD(4) edges_are_Vs(1) remove_vertices_not_vs remove_vertices_subgraph' subset_iff)

  with no_neighbor subset_before show ?thesis
    by (simp add: step_def)
next
  case new_match
  note new_match_orig = this

  let ?min = "min_on_rel {i. i \<notin> Vs M \<and> {i,j} \<in> G} r"

  from new_match \<open>i \<in> L\<close> \<open>j \<in> R\<close> have min_available_if: "?min \<notin> Vs M' \<Longrightarrow> ?min \<noteq> i \<Longrightarrow> ?min \<in> {i'. i' \<notin> Vs M' \<and> {i',j} \<in> G \<setminus> {i}}"
    by (auto intro: in_remove_verticesI)

  from linorder have "preorder_on' {i'. {i', j} \<in> G \<setminus> {i}} r" "finite (Vs (G \<setminus> {i}))"
    by (auto intro: preorder_on'_subset 
                dest: remove_vertices_subgraph' linorder_on'_imp_preorder_on'
                simp: graph graph_invar_remove_vertices)

  then show ?thesis
  proof (cases rule: step_cases[where M = M'])
    case no_neighbor

    with min_available_if subset_before new_match \<open>j \<in> R\<close> show ?thesis
      by (auto simp: step_def vs_insert)
  next
    case j_matched
    with \<open>j \<notin> Vs M'\<close> show ?thesis
      by blast
  next
    case new_match

    let ?min' = "min_on_rel {i'. i' \<notin> Vs M' \<and> {i',j} \<in> G \<setminus> {i}} r"

    from new_match have "?min' \<in> {i. i \<notin> Vs M \<and> {i,j} \<in> G}"
      using remove_vertices_subgraph'
      by (smt (verit, ccfv_threshold) Diff_iff assms(2) bipartite_edgeD(4) bipartite_graph
              edges_are_Vs mem_Collect_eq remove_vertices_not_vs' subset_before subset_eq)

    have "?min \<in> {i'. i' \<notin> Vs M' \<and> {i',j} \<in> G \<setminus> {i}} \<Longrightarrow> ?min = ?min'"
    proof -
      assume "?min \<in> {i'. i' \<notin> Vs M' \<and> {i',j} \<in> G \<setminus> {i}}"

      with linorder have "(?min', ?min) \<in> r"
        by (intro min_on_rel_least linorder_on'_subset[where S = "{i. {i,j} \<in> G}" and T = "{i'. i' \<notin> Vs M' \<and> {i', j} \<in> G \<setminus> {i}}"])
           (auto dest: remove_vertices_subgraph' intro: finite_vs_subgraph)

      from linorder \<open>?min' \<in> {i. i \<notin> Vs M \<and> {i,j} \<in> G}\<close> have "(?min, ?min') \<in> r"
        by (intro min_on_rel_least linorder_on'_subset[where S = "{i. {i,j} \<in> G}" and T = "{i. i \<notin> Vs M \<and> {i,j} \<in> G}"])
           (auto intro: finite_vs_subgraph)

      with linorder \<open>(?min', ?min) \<in> r\<close> show "?min = ?min'"
        unfolding linorder_on'_def antisym_def
        by blast
    qed

    with new_match new_match_orig subset_before min_available_if show ?thesis
      by (auto simp: step_def vs_insert)
  qed
qed (use \<open>j \<notin> Vs M\<close> in blast)

lemma monotonicity_order_ranking:
  assumes "i \<in> L"
  assumes "set js \<subseteq> R" "distinct js"
  assumes "set js \<inter> Vs M = {}" "set js \<inter> Vs M' = {}"
  assumes "\<forall>j \<in> set js. linorder_on' {i. {i,j} \<in> G} r"

  assumes "L - {i} - Vs M' \<subseteq> L - Vs M"
  shows "L - {i} - (Vs (ranking' r (G \<setminus> {i}) M' js)) \<subseteq> L - (Vs (ranking' r G M js))"
  using assms
proof (induction js arbitrary: M' M)
  case (Cons j js)

  from Cons.prems have mono_step: "L - {i} - Vs (step r (G \<setminus> {i}) M' j) \<subseteq> L - Vs (step r G M j)"
    by (intro monotonicity_order_step) auto

  from Cons.prems have j'_not_in_step: "j' \<in> set js \<Longrightarrow> j' \<notin> Vs (step r G M j)" for j'
    by (intro unmatched_R_in_step_if)
       (auto intro: linorder_on'_imp_preorder_on')

  from Cons.prems have "j' \<in> set js \<Longrightarrow> j' \<notin> Vs (step r (G \<setminus> {i}) M' j)" for j'
    by (intro unmatched_R_in_step_if)
       (auto intro: linorder_on'_imp_preorder_on' preorder_on'_subset dest: remove_vertices_subgraph')

  with Cons.prems mono_step j'_not_in_step show ?case
    by (simp only: ranking_Cons, intro Cons.IH unmatched_R_in_step_if)
       auto
qed simp



lemma monotonicity_order_matched_matched:
  assumes linorder: "linorder_on L r"
  assumes "{i,j} \<in> G"
  assumes "i \<in> L" "j \<in> set js"
  assumes "set js \<subseteq> R" "distinct js"
  assumes "set js \<inter> Vs M = {}" "set js \<inter> Vs M' = {}"
  
  assumes "j \<notin> Vs M" "j \<notin> Vs M'"
  assumes "L - {i} - Vs M' \<subseteq> L - Vs M"

  assumes "matching M" "matching M'"

  assumes i'j: "{i',j} \<in> ranking' r G M js"
  assumes i''j: "{i'',j} \<in> (ranking' r (G \<setminus> {i}) M' js)"
  shows "(i', i'') \<in> r"
  using assms
proof -
  from \<open>j \<in> set js\<close> \<open>distinct js\<close> obtain pre suff where js_decomp: "js = pre @ j # suff"
    by (auto dest: split_list)

  from \<open>j \<in> set js\<close> \<open>set js \<subseteq> R\<close> have "j \<in> R"
    by blast

  let ?ranking_pre = "ranking' r G M pre"
  and ?ranking_pre' = "ranking' r (G \<setminus> {i}) M' pre"

  from js_decomp assms have "L - {i} - Vs ?ranking_pre' \<subseteq> L - Vs ?ranking_pre"
    by (intro monotonicity_order_ranking) auto

  from linorder js_decomp \<open>distinct js\<close> \<open>set js \<subseteq> R\<close> \<open>j \<notin> Vs M\<close> have j_unmatched_pre: "j \<notin> Vs ?ranking_pre"
    by (intro unmatched_R_in_ranking_if)
       (auto dest: linorder_on_imp_preorder_on)

  let ?ns = "{i. i \<notin> Vs ?ranking_pre \<and> {i,j} \<in> G}"
  let ?min = "min_on_rel ?ns r"

  have "?ns \<noteq> {}"
  proof (rule ccontr, simp only: not_not)
    assume "?ns = {}"
    then have "step r G ?ranking_pre j = ?ranking_pre"
      by (simp add: step_def)

    with linorder j_unmatched_pre js_decomp \<open>distinct js\<close> \<open>set js \<subseteq> R\<close> have "j \<notin> Vs (ranking' r G M js)"
      by (simp only: ranking_append ranking_Cons)
         (rule unmatched_R_in_ranking_if, auto dest: linorder_on_imp_preorder_on)

    with i'j show False
      by (auto dest: edges_are_Vs)
  qed

  with linorder \<open>j \<in> R\<close> have "?min \<in> ?ns"
    by (intro min_if_finite)
       (auto dest: linorder_on_imp_preorder_on preorder_on_imp_preorder_on' intro: preorder_on'_subset)
    
  with j_unmatched_pre have "step r G ?ranking_pre j = insert {?min, j} ?ranking_pre"
    by (auto simp: step_def)
  
  with js_decomp have "{?min, j} \<in> ranking' r G M js"
    by (auto simp: ranking_append ranking_Cons intro: ranking_mono)

  with i'j linorder \<open>set js \<subseteq> R\<close> \<open>matching M\<close> have "i' = ?min"
    by (auto intro: matching_partner_eqI matching_ranking dest: linorder_on_imp_preorder_on)


  from linorder js_decomp \<open>distinct js\<close> \<open>set js \<subseteq> R\<close> \<open>j \<notin> Vs M'\<close> have j_unmatched_pre': "j \<notin> Vs ?ranking_pre'"
    by (intro unmatched_R_in_ranking_if)
       (auto dest: remove_vertices_subgraph' linorder_on_imp_preorder_on)

  let ?ns' = "{i'. i' \<notin> Vs ?ranking_pre' \<and> {i',j} \<in> G \<setminus> {i}}"
  let ?min' = "min_on_rel ?ns' r"

  have "?ns' \<noteq> {}"
  proof (rule ccontr, simp only: not_not)
    assume "?ns' = {}"
    then have "step r (G \<setminus> {i}) ?ranking_pre' j = ?ranking_pre'"
      by (simp add: step_def)

    with linorder j_unmatched_pre' js_decomp \<open>distinct js\<close> \<open>set js \<subseteq> R\<close> have "j \<notin> Vs (ranking' r (G \<setminus> {i}) M' js)"
      by (simp only: ranking_append ranking_Cons)
         (rule unmatched_R_in_ranking_if, auto dest: linorder_on_imp_preorder_on remove_vertices_subgraph')

    with i''j show False
      by (auto dest: edges_are_Vs)
  qed

  with linorder \<open>j \<in> R\<close> have "?min' \<in> ?ns'"
    by(intro min_if_finite)
      (auto dest: linorder_on_imp_preorder_on preorder_on_imp_preorder_on' remove_vertices_subgraph' 
                intro: preorder_on'_subset
                simp add: local.finite_unmatched_neighbors remove_vertices_subgraph)


  with j_unmatched_pre' have "step r (G \<setminus> {i}) ?ranking_pre' j = insert {?min', j} ?ranking_pre'"
    by (auto simp: step_def)

  with js_decomp have "{?min', j} \<in> ranking' r (G \<setminus> {i}) M' js"
    by (auto simp: ranking_append ranking_Cons intro: ranking_mono)

  with linorder \<open>set js \<subseteq> R\<close> \<open>matching M'\<close> have "i'' = ?min'"

    by (auto intro!: matching_partner_eqI[OF _ i''j] matching_ranking
             dest!: linorder_on_imp_preorder_on remove_vertices_subgraph'
             simp: graph graph_invar_remove_vertices)
  (*have "Vs (ranking' r G M pre) \<subseteq> Vs (ranking' r (G \<setminus> {i}) M' pre)"
    sorry*)
  have "?ns' \<subseteq> ?ns"
  proof-
    have "G \<setminus> {i} \<subseteq> G"
      by (simp add: remove_vertices_subgraph)
    moreover have "x \<in> Vs (ranking' r (G \<setminus> {i}) M' pre)" if
      "{x, j} \<in> G \<setminus> {i}"
      "x \<in> Vs (ranking' r G M pre)" for x
    proof-
      have "x \<in> L"
        using \<open>G \<setminus> {i} \<subseteq> G\<close> that \<open>j \<in> R\<close> neighbors_right_subset_left
        by fastforce
      moreover have "x \<noteq> i"
        using \<open>{x, j} \<in> G \<setminus> {i}\<close> edges_are_Vs remove_vertices_not_vs
        by (metis insertI1) 
      ultimately show ?thesis
        using \<open>x \<in> Vs (ranking' r G M pre)\<close>
              \<open>L - {i} - Vs (ranking' r (G \<setminus> {i}) M' pre) \<subseteq> L - Vs (ranking' r G M pre)\<close>
        by auto
    qed
    ultimately show ?thesis
      by auto
  qed

  with \<open>?min' \<in> ?ns'\<close> have "?min' \<in> ?ns"
    by auto

  with linorder \<open>?min \<in> ?ns\<close> \<open>j \<in> R\<close> have "(?min, ?min') \<in> r"
    by (intro min_on_rel_least)
       (auto dest: linorder_on_imp_linorder_on' intro: linorder_on'_subset)

  with \<open>i' = ?min\<close> \<open>i'' = ?min'\<close> show "(i',i'') \<in> r"
    by simp
qed

lemma online_matched_mono:
  assumes linorder: "linorder_on L r"
  assumes perm: "\<pi> \<in> permutations_of_set R"
  assumes "i \<in> L" "j \<in> R"
  assumes "j \<in> Vs (ranking r (G \<setminus> {i}) \<pi>)"
  shows "j \<in> Vs (ranking r G \<pi>)"
proof -
  let ?M' = "ranking r (G \<setminus> {i}) \<pi>"

  from perm \<open>j \<in> R\<close> obtain pre suff where \<pi>_decomp: "\<pi> = pre @ j # suff"
    by (metis permutations_of_setD(1) split_list)

  let ?ranking_pre = "ranking r G pre"
  let ?ranking_pre' = "ranking r (G \<setminus> {i}) pre"

  from \<pi>_decomp perm linorder \<open>j \<in> R\<close> have j_unmatched_pre: "j \<notin> Vs ?ranking_pre"
    by (intro unmatched_R_in_ranking_if ballI preorder_on_neighborsI)
       (auto dest: permutations_of_setD linorder_on_imp_preorder_on)

  from \<pi>_decomp perm linorder \<open>j \<in> R\<close> have j_unmatched_pre': "j \<notin> Vs ?ranking_pre'"
    by (intro unmatched_R_in_ranking_if ballI preorder_on_neighborsI)
       (auto dest: permutations_of_setD remove_vertices_subgraph' linorder_on_imp_preorder_on)

  let ?ns = "{i. i \<notin> Vs ?ranking_pre \<and> {i,j} \<in> G}"
  and ?ns' = "{i'. i' \<notin> Vs ?ranking_pre' \<and> {i',j} \<in> G \<setminus> {i}}"

  from \<open>j \<in> R\<close> have "?ns \<subseteq> L"
    by (intro unmatched_neighbors_L subset_refl)

  from \<open>j \<in> R\<close> have "?ns' \<subseteq> L - {i}"
    by (auto dest: neighbors_right_subset_left[OF remove_vertices_subgraph] edges_are_Vs intro: remove_vertices_not_vs')

  have "?ns' \<noteq> {}"
  proof (rule ccontr, simp only: not_not)
    assume "?ns' = {}"

    then have step_eq: "step r (G \<setminus> {i}) ?ranking_pre' j = ?ranking_pre'"
      by (simp add: step_def)

    from j_unmatched_pre' \<pi>_decomp perm linorder \<open>j \<in> R\<close> have "j \<notin> Vs ?M'"
      by (simp only: \<pi>_decomp ranking_append ranking_Cons step_eq,
          intro unmatched_R_in_ranking_if[where M = ?ranking_pre'] ballI preorder_on_neighborsI)
         (auto dest: remove_vertices_subgraph' permutations_of_setD linorder_on_imp_preorder_on)

    with \<open>j \<in> Vs ?M'\<close> show False
      by blast
  qed

  from linorder perm \<pi>_decomp \<open>i \<in> L\<close> have "L - {i} - Vs ?ranking_pre' \<subseteq> L - Vs ?ranking_pre"
    by (intro monotonicity_order_ranking ballI linorder_on_neighborsI)
       (auto dest: permutations_of_setD)
    
  with \<open>?ns \<subseteq> L\<close> \<open>?ns' \<subseteq> L - {i}\<close> have "?ns' \<subseteq> ?ns"
    by (auto dest: remove_vertices_subgraph')

  with \<open>?ns' \<noteq> {}\<close> obtain i' where "i' \<in> ?ns"
    by blast

  then have "{i',j} \<in> G" "i' \<notin> Vs ?ranking_pre"
    by auto

  with j_unmatched_pre have "j \<in> Vs (step r G ?ranking_pre j)"
    by (intro step_matches_if_possible[OF j_unmatched_pre \<open>{i',j} \<in> G\<close>])
       auto

  with \<pi>_decomp show "j \<in> Vs (ranking r G \<pi>)"
    by (auto simp: ranking_append ranking_Cons intro: ranking_mono_vs)
qed

lemma step_Restr_to_vertices:
  assumes "j \<in> R"
  shows "step (Restr r (L - X)) (G \<setminus> X) M j = step r (G \<setminus> X) M j"
proof (cases M j "G \<setminus> X" rule: step_cases')
  case new_match
  from bipartite_graph \<open>j \<in> R\<close> have "{i. i \<notin> Vs M \<and> {i, j} \<in> G \<setminus> X} \<subseteq> L - X"
    by (auto dest: remove_vertices_subgraph' bipartite_edgeD edges_are_Vs intro: remove_vertices_not_vs')

  then have "Restr (Restr r (L - X)) {i. i \<notin> Vs M \<and> {i, j} \<in> G \<setminus> X} = Restr r {i. i \<notin> Vs M \<and> {i,j} \<in> G \<setminus> X}"
    by blast
  with new_match show ?thesis
    by (simp add: step_def min_on_rel_def)
qed (simp_all add: step_def)

lemma ranking_Restr_to_vertices:
  assumes "set js \<subseteq> R"
  shows "ranking' (Restr r (L - X)) (G \<setminus> X) M js = ranking' r (G \<setminus> X) M js"
  using assms
  by (induction js arbitrary: M) (simp_all add: ranking_Cons step_Restr_to_vertices)

end
end
