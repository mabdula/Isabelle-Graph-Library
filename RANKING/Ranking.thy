section \<open>RANKING (in a deterministic setting)\label{sec:ranking}\<close>
theory Ranking
  imports
    More_Graph
    More_List
begin
text \<open>
  We start off by formulating the algorithm in a deterministic fashion. Both the arrival order
  of the online vertices and the ranking of the offline vertices are modelled as lists. In this
  and the following sections, \<^term>\<open>V::'a set\<close> usually refers to the set of offline vertices,
  \<^term>\<open>v::'a\<close> is a single offline vertex, and \<^term>\<open>\<sigma>::'a list\<close> represents an ordering
  (permutation\<^footnote>\<open>In this section it is usually not necessary that the lists actually represent
  permutations. This becomes relevant in~\autoref{sec:prob}.\<close>) of \<^term>\<open>V::'a set\<close>. The respective
  identifiers for the online side are \<^term>\<open>U::'a set\<close>, \<^term>\<open>u::'a\<close>, and \<^term>\<open>\<pi>::'a list\<close>.
  
  We will see at a later point that the online and offline side are interchangeable, which also
  plays an important part in our proof of Lemma 2 of the Birnbaum, and Mathieu
  paper~\cite{birnbaum2008}. The first proper proof of that \<^emph>\<open>simple structural observation\<close>, as the
  "proof" was phrased there, is actually the most involved part of this formalization and makes
  up the majority of this section. Lemma 2 is the key to arguing that we can consider instances
  where a perfect matching exists in \<^term>\<open>G::'a graph\<close> to determine the competitive ratio,
  enabling the simpler reasoning in the randomized setting.
\<close>

subsection \<open>Definitions\label{sec:ranking-defs}\<close>
text \<open>
  The definition of RANKING is relatively straightforward. The \<^term>\<open>step\<close> function handles
  the arrival of a single vertex \<^term>\<open>u \<in> U\<close>. RANKING can then be seen as folding \<^term>\<open>step\<close>
  over the arrival order \<^term>\<open>\<pi>::'a list\<close> with an initially empty matching.
\<close>
fun step :: "'a graph \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a graph \<Rightarrow> 'a graph" where
  "step _ _ [] M = M"
| "step G u (v#vs) M = (
      if v \<notin> Vs M \<and> u \<notin> Vs M \<and> {u,v} \<in> G
      then insert {u,v} M
      else step G u vs M
    )"

fun online_match' :: "'a graph \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a graph \<Rightarrow> 'a graph" where
  "online_match' _ [] _ M = M"
| "online_match' G (u#us) \<sigma> M = online_match' G us \<sigma> (step G u \<sigma> M)"

lemma online_match_foldl: "online_match' G \<pi> \<sigma> M = foldl (\<lambda>M u. step G u \<sigma> M) M \<pi>"
  by (induction G \<pi> \<sigma> M rule: online_match'.induct) auto

abbreviation "online_match G \<pi> \<sigma> \<equiv> online_match' G \<pi> \<sigma> {}"

lemma online_match'_append: "online_match' G (us@us') \<sigma> M = online_match' G us' \<sigma> (online_match' G us \<sigma> M)"
  by (simp add: online_match_foldl)

lemma online_match_append: "online_match G (us@us') \<sigma> = online_match' G us' \<sigma> (online_match G us \<sigma>)"
  by (simp add: online_match'_append)

text \<open>
  The following predicate fully specifies a matching \<^term>\<open>M::'a graph\<close> resulting from RANKING
  on graph \<^term>\<open>G::'a graph\<close> with arrival order \<^term>\<open>\<pi>::'a list\<close> and ranking \<^term>\<open>\<sigma>::'a list\<close>.
  It also includes a wellformedness condition for \<^term>\<open>G::'a graph\<close> wrt.\ the inputs \<^term>\<open>\<pi>::'a list\<close>
  and \<^term>\<open>\<sigma>::'a list\<close>.
  The predicate is useful as many of the proofs where we are arguing about removing vertices don't
  follow the induction scheme provided by \<^term>\<open>online_match'\<close>.
\<close>
definition ranking_matching :: "'a graph \<Rightarrow> 'a graph \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "ranking_matching G M \<pi> \<sigma> = ( graph_matching G M \<and>
    bipartite G (set \<pi>) (set \<sigma>) \<and> maximal_matching G M \<and>
    \<comment> \<open>an \<^emph>\<open>online\<close> vertex \<^term>\<open>u\<in>set \<pi>\<close> is matched to the (available) offline vertex with the lowest rank\<close>
    (\<forall>u v v'. ({u,v}\<in>M \<and> {u,v'}\<in>G \<and> index \<sigma> v' < index \<sigma> v) \<longrightarrow> (\<exists>u'. {u',v'}\<in>M \<and> index \<pi> u' < index \<pi> u)) \<and>
    \<comment> \<open>an \<^emph>\<open>offline\<close> vertex \<^term>\<open>v\<in>set \<sigma>\<close> is matched to the earliest online vertex that makes an offer\<close>
    (\<forall>u v u'. ({u,v}\<in>M \<and> {u',v}\<in>G \<and> index \<pi> u' < index \<pi> u) \<longrightarrow> (\<exists>v'. {u',v'}\<in>M \<and> index \<sigma> v' < index \<sigma> v))
    )"

lemma ranking_matchingE:
  "ranking_matching G M \<pi> \<sigma> \<Longrightarrow> 
    \<lbrakk>\<lbrakk>graph_invar G; graph_matching G M; bipartite G (set \<pi>) (set \<sigma>); maximal_matching G M;
     bipartite M (set \<pi>) (set \<sigma>) ; graph_invar M\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P
   "
  using finite_parts_bipartite_graph_invar
  unfolding ranking_matching_def
  by (auto intro: bipartite_subgraph graph_invar_subgraph finite_parts_bipartite_graph_invar)
                                                                          
text \<open>
  This lemma shows that for the given specification \<^term>\<open>ranking_matching\<close>, the online and offline
  side are interchangeable.
\<close>
lemma\<^marker>\<open>tag important\<close> ranking_matching_commute:
  assumes "ranking_matching G M \<pi> \<sigma>"
  shows "ranking_matching G M \<sigma> \<pi>"
  using assms
  unfolding ranking_matching_def
  by (auto simp: insert_commute bipartite_commute)
     (meson edge_commute)

lemma ranking_matching_bipartite_edges:
  assumes "ranking_matching G M \<pi> \<sigma>"
  assumes "{u,v} \<in> M"
  assumes "u \<in> set \<pi>"
  shows "v \<in> set \<sigma>"
  using assms
  by (auto dest: bipartite_edgeD elim: ranking_matchingE)

lemma ranking_matching_bipartite_edges':
  assumes "ranking_matching G M \<pi> \<sigma>"
  assumes "{u,v} \<in> M"
  assumes "v \<in> set \<sigma>"
  shows "u \<in> set \<pi>"
  using assms
  by (auto intro: ranking_matching_bipartite_edges dest: ranking_matching_commute edge_commute)

lemma ranking_matching_maximalE:
  assumes "ranking_matching G M \<pi> \<sigma>"
  assumes "{u,v} \<in> G"
  obtains e where "e \<in> M" "u \<in> e \<or> v \<in> e"
  using assms
  by (auto dest: elim!: ranking_matchingE maximal_matching_edgeE)

text \<open>
  The following two elimination rules are useful to obtain the required vertices for the
  induction hypothesis of
\<close>

lemma ranking_matching_earlier_match_onlineE:
  assumes "ranking_matching G M \<pi> \<sigma>"
  assumes "{u,v} \<in> M"
  assumes "{u,v'} \<in> G"
  assumes "index \<sigma> v' < index \<sigma> v"
  obtains u' where "{u',v'} \<in> M" "index \<pi> u' < index \<pi> u"
  using assms
  unfolding ranking_matching_def
  by blast

lemma ranking_matching_earlier_match_offlineE:
  assumes "ranking_matching G M \<pi> \<sigma>"
  assumes "{u,v} \<in> M"
  assumes "{u',v} \<in> G"
  assumes "index \<pi> u' < index \<pi> u"
  obtains v' where "{u',v'} \<in> M" "index \<sigma> v' < index \<sigma> v"
  using assms
  unfolding ranking_matching_def
  by blast

lemma ranking_matching_unique_match:
  assumes rm_M: "ranking_matching G M \<pi> \<sigma>"
  assumes rm_M': "ranking_matching G M' \<pi> \<sigma>"
  assumes v_M: "{u,v} \<in> M"
  assumes v'_M': "{u,v'} \<in> M'"
  assumes before: "index \<sigma> v' < index \<sigma> v"
  shows False
  using v_M v'_M' before
proof (induction u \<pi> arbitrary: v v' rule: index_less_induct)
  case (index_less u)
  with rm_M rm_M' obtain u' where u': "{u',v'} \<in> M" "index \<pi> u' < index \<pi> u"
    by (meson ranking_matchingE ranking_matching_earlier_match_onlineE subsetD)

  with rm_M rm_M' \<open>{u,v'} \<in> M'\<close> obtain v'' where "{u',v''} \<in> M'" "index \<sigma> v'' < index \<sigma> v'"
    by (meson ranking_matchingE ranking_matching_earlier_match_offlineE subsetD)

  with index_less u' show ?case
    by blast
qed

lemma ranking_matching_unique_match':
  assumes rm_M: "ranking_matching G M \<pi> \<sigma>"
  assumes rm_M': "ranking_matching G M' \<pi> \<sigma>"
  assumes u_M: "{u,v} \<in> M"
  assumes u'_M': "{u',v} \<in> M'"
  assumes before: "index \<pi> u' < index \<pi> u"
  shows False
  using assms
  by (auto intro!: ranking_matching_unique_match[OF ranking_matching_commute ranking_matching_commute]
      dest: edge_commute)

lemma ranking_matching_unique':
  assumes rm_M: "ranking_matching G M \<pi> \<sigma>"
  assumes rm_M': "ranking_matching G M' \<pi> \<sigma>"
  assumes "u \<in> set \<pi>" "v \<in> set \<sigma>"
  assumes "{u,v} \<in> M"
  shows "{u,v} \<in>  M'"
proof (rule ccontr)
  assume "{u,v} \<notin> M'"
  with rm_M' rm_M \<open>{u,v} \<in> M\<close> consider (u_matched) "u \<in> Vs M'" | (v_matched) "v \<in> Vs M'"
    by (auto dest!: elim!: ranking_matchingE maximal_matching_edgeE)

  then show False
  proof cases
    case u_matched
    with rm_M' obtain v' where "{u,v'} \<in> M'"
      by (meson graph_invar_vertex_edgeE ranking_matchingE)

    with assms \<open>{u,v} \<notin> M'\<close> show False
      by (metis index_eq_index_conv nat_neq_iff ranking_matching_unique_match)    
  next
    case v_matched
    with rm_M' obtain u' where "{u',v} \<in> M'"
      by (meson graph_invar_vertex_edgeE' ranking_matchingE)

    with assms \<open>{u,v} \<notin> M'\<close> show ?thesis
      by (metis index_eq_index_conv nat_neq_iff ranking_matching_unique_match')    
  qed
qed

lemma ranking_matching_unique'':
  assumes rm_M: "ranking_matching G M \<pi> \<sigma>"
  assumes "ranking_matching G M' \<pi> \<sigma>"
  assumes "e \<in> M"
  shows "e \<in> M'"
  using assms
proof -
  from rm_M \<open>e \<in> M\<close> obtain u v where "e = {u,v}" "u \<in> set \<pi>" "v \<in> set \<sigma>"
    by (auto elim: ranking_matchingE elim: bipartite_edgeE)

  with assms show ?thesis
    by (auto intro: ranking_matching_unique')
qed

text \<open>
  There is only one matching \<^term>\<open>M::'a graph\<close> that satisfies \<^term>\<open>ranking_matching G M \<pi> \<sigma>\<close> for
  a given graph \<^term>\<open>G::'a graph\<close>, arrival order \<^term>\<open>\<pi>::'a list\<close> and ranking \<^term>\<open>\<sigma>::'a list\<close>.
\<close>
lemma\<^marker>\<open>tag important\<close> ranking_matching_unique:
  assumes "ranking_matching G M \<pi> \<sigma>"
  assumes "ranking_matching G M' \<pi> \<sigma>"
  shows "M = M'"
  using assms
  by (auto intro: ranking_matching_unique'')

lemma remove_edge_ranking_matching:
  "{u,v} \<in> M \<Longrightarrow> ranking_matching G M \<pi> \<sigma> \<Longrightarrow> ranking_matching (G \<setminus> {u,v}) (M \<setminus> {u,v}) \<pi> \<sigma>"
  unfolding ranking_matching_def
proof (intro conjI impI allI, goal_cases)
  case 1
  then show ?case
    by (auto intro: matching_remove_vertices)
next
  case 2
  then show ?case
    by (auto intro: remove_vertices_mono)
next
  case 3
  then show ?case
    by (auto intro: bipartite_remove_vertices)
next
  case 4
  then show ?case
    by (auto intro!: maximal_matching_remove_edges[where G = G and M = M and X = "{u,v}" and E = "{{u,v}}"] simp: Vs_def)
next
  case (5 u v v')
  then show ?case
    by (smt (verit, ccfv_threshold) DiffI edges_are_Vs empty_iff insert_commute insert_iff
            remove_edge_matching remove_vertices_not_vs remove_vertices_subgraph')
next
  case (6 u v u')
  then show ?case
    by (metis edges_are_Vs insert_Diff insert_iff remove_edge_matching remove_vertices_not_vs remove_vertices_subgraph')
qed

lemma step_already_matched:
  "u \<in> Vs M \<Longrightarrow> step G u \<sigma> M = M"
  by (induction \<sigma>) auto

lemma step_mono:
  "e \<in> M \<Longrightarrow> e \<in> step G u \<sigma> M"
  by (induction \<sigma>) auto

lemma step_mono_vs:
  "v \<in> Vs M \<Longrightarrow> v \<in> Vs (step G u \<sigma> M)"
  by (induction \<sigma>) (auto simp: Vs_def)

lemma step_Vs_subset: "x \<in> Vs (step G u \<sigma> M) \<Longrightarrow> x = u \<or> x \<in> set \<sigma> \<or> x \<in> Vs M"
  by (induction G u \<sigma> M rule: step.induct)
     (auto split: if_splits simp: Vs_def)

lemma step_ConsI:
  assumes "v \<notin> Vs M \<Longrightarrow> u \<notin> Vs M \<Longrightarrow> {u,v} \<in> G \<Longrightarrow> P (insert {u,v} M)"
  assumes "v \<in> Vs M \<or> u \<in> Vs M \<or> {u,v} \<notin> G \<Longrightarrow> P (step G u vs M)"
  shows "P (step G u (v#vs) M)"
  using assms by simp

lemma edge_in_step:
  assumes "e \<in> step G u \<sigma> M"
  shows "e \<in> M \<or> (\<exists>v. e = {u,v} \<and> v \<in> set \<sigma> - Vs M \<and> {u,v} \<in> G \<and> 
                      (\<forall>v'\<in> set \<sigma> \<inter> {v''. {u,v''} \<in> G} - Vs M - {v}. index \<sigma> v < index \<sigma> v'))"
  using assms
proof (induction G u \<sigma> M rule: step.induct)
  case (2 G u v vs M)
  consider (match) "v \<notin> Vs M" "{u,v} \<in> G" "u \<notin> Vs M" | (ind) "v \<in> Vs M \<or> {u,v} \<notin> G \<or> u \<in> Vs M" by blast
  then show ?case 
  proof cases
    case match
    with 2 show ?thesis
      by auto
  next
    case ind
    with 2 consider "e \<in> M" | "(\<exists>v. e = {u, v} \<and> v \<in> set vs - Vs M \<and> {u, v} \<in> G \<and> (\<forall>v'\<in>set vs \<inter> {v''. {u,v''} \<in> G} - Vs M - {v}. index vs v < index vs v'))"
      by fastforce
    then show ?thesis
    proof cases
      case 2
      then obtain w where w: "e = {u,w}" "w \<in> set vs - Vs M" "{u,w} \<in> G"
        "\<forall>v'\<in> set vs \<inter> {v''. {u,v''} \<in> G} - Vs M - {w}. index vs w < index vs v'" by blast
      have "v \<noteq> w"
        by (metis "2.prems" DiffD2 \<open>e = {u, w}\<close> \<open>w \<in> set vs - Vs M\<close> \<open>{u, w} \<in> G\<close> ind insert_subset step_already_matched subsetI vs_member_intro)

      with w have "\<forall>v'\<in> set (v#vs) \<inter> {v''. {u,v''} \<in> G} - Vs M - {w}. index (v#vs) w < index (v#vs) v'"
        apply simp
        by (smt (z3) "2.prems" Diff_iff IntE Int_commute Int_insert_right_if0 Int_insert_right_if1 edges_are_Vs ind insert_commute insert_iff mem_Collect_eq step_already_matched)
      then show ?thesis
        by (metis Diff_iff Diff_insert \<open>e = {u, w}\<close> \<open>w \<in> set vs - Vs M\<close> \<open>{u, w} \<in> G\<close> list.simps(15))
    qed simp
  qed
qed simp

lemma edge_matched_in_stepE:
  assumes "e \<in> step G u \<sigma> M"
  assumes "e \<notin> M"
  obtains v where "e = {u,v}" "v \<in> set \<sigma> \<inter> {v'. {u,v'} \<in> G} - Vs M"
    "\<forall>v'\<in> set \<sigma> \<inter> {v''. {u,v''} \<in> G} - Vs M - {v}. index \<sigma> v < index \<sigma> v'"
  using assms edge_in_step
  by force

lemma step_no_match_id:
  assumes "u \<in> Vs M \<or> \<not>(\<exists>v \<in> set \<sigma>. v \<notin> Vs M \<and> {u,v} \<in> G)"
  shows "step G u \<sigma> M = M"
  using assms
  by (induction G u \<sigma> M rule: step.induct) auto

lemma step_matches_if_possible:
  assumes "u \<notin> Vs M"
  assumes "v \<in> set \<sigma>" "v \<notin> Vs M"
  assumes "{u,v} \<in> G"
  shows "\<exists>v. {u,v} \<in> step G u \<sigma> M"
  using assms
proof (induction G u \<sigma> M rule: step.induct)
  case (2 G u v' vs M)
  then show ?case
  proof (cases "v = v'")
    case True
    with 2 show ?thesis
      by auto
  next
    case False
    then consider (match) "v' \<notin> Vs M \<and> {u,v'} \<in> G" | (prev_match) "v' \<in> Vs M" | (not_connected) "{u,v'} \<notin> G" by blast

    then show ?thesis
      by cases (use 2 in auto)
  qed
qed simp

lemma graph_invar_step:
  assumes "graph_invar G"
  assumes "graph_invar M"
  shows "graph_invar (step G u \<sigma> M)"
  using assms
  by (induction \<sigma>) (auto dest: graph_invar_edgeD)

lemma matching_step:
  assumes "matching M"
  assumes "u \<notin> set \<sigma>"
  shows "matching (step G u \<sigma> M)"
  using assms
  by (induction \<sigma>) (auto simp: matching_def)

lemma step_matches_graph_edge:
  assumes "M \<subseteq> G"
  shows "step G u \<sigma> M \<subseteq> G"
  using assms
  by (induction \<sigma>) auto

lemma online_match_mono: "e \<in> M \<Longrightarrow> e \<in> online_match' G \<pi> \<sigma> M"
  by (induction G \<pi> \<sigma> M rule: online_match'.induct)
     (auto simp: step_mono)

lemma online_match_mono_vs: "x \<in> Vs M \<Longrightarrow> x \<in> Vs (online_match' G \<pi> \<sigma> M)"
  by (meson online_match_mono vs_member)

lemma online_match'_Vs_subset: "x \<in> Vs (online_match' G \<pi> \<sigma> M) \<Longrightarrow> x \<in> Vs M \<or> x \<in> set \<pi> \<or> x \<in> set \<sigma>"
  by (induction G \<pi> \<sigma> M rule: online_match'.induct)
     (auto dest: step_Vs_subset)

lemma online_match_Vs_subset: "x \<in> Vs (online_match G \<pi> \<sigma>) \<Longrightarrow> x \<in> set \<pi> \<or> x \<in> set \<sigma>"
  by (auto dest: online_match'_Vs_subset)

lemma bipartite_step:
  assumes "bipartite G (set \<pi>) (set \<sigma>)"
  assumes "M \<subseteq> G"
  shows "bipartite (step G u \<sigma> M) (set \<pi>) (set \<sigma>)"
  using assms
  by (auto dest: step_matches_graph_edge intro: bipartite_subgraph)

lemma graph_invar_online_match':
  assumes "graph_invar G"
  assumes "graph_invar M"
  shows "graph_invar (online_match' G \<pi> \<sigma> M)"
  using assms
  by (induction \<pi> arbitrary: M) (auto simp: graph_invar_step)

lemma graph_abs_online_match:
  assumes "graph_invar G"
  shows "graph_invar (online_match G \<pi> \<sigma>)"
  using assms
  by (auto simp: graph_invar_online_match')

lemma matching_online_match':
  assumes "matching M"
  assumes "set \<pi> \<inter> set \<sigma> = {}"
  shows "matching (online_match' G \<pi> \<sigma> M)"
  using assms
  by (induction \<pi> arbitrary: M) (auto dest: matching_step)

lemma matching_online_match: "set \<pi> \<inter> set \<sigma> = {} \<Longrightarrow> matching (online_match G \<pi> \<sigma>)"
  by (auto intro: matching_online_match')

lemma subgraph_online_match':
  assumes "M \<subseteq> G"
  shows "e \<in> online_match' G \<pi> \<sigma> M \<Longrightarrow> e \<in> G"
  using assms
  by (induction \<pi> arbitrary: M) (auto simp: step_matches_graph_edge)

lemma subgraph_online_match: "e \<in> online_match G \<pi> \<sigma> \<Longrightarrow> e \<in> G"
  by (auto intro: subgraph_online_match')

lemma bipartite_online_match':
  assumes "bipartite G (set \<pi>) (set \<sigma>)"
  assumes "M \<subseteq> G"
  shows "bipartite (online_match' G \<pi> \<sigma> M) (set \<pi>) (set \<sigma>)"
  using assms
  by (auto intro: bipartite_subgraph dest: subgraph_online_match')

lemma bipartite_online_match:
  assumes "bipartite G (set \<pi>) (set \<sigma>)"
  shows "bipartite (online_match G \<pi> \<sigma>) (set \<pi>) (set \<sigma>)"
  using assms
  by (auto intro: bipartite_online_match')

lemma not_matched_in_prefix:
  assumes "x \<notin> Vs (online_match G \<pi> \<sigma>)"
  assumes "\<pi> = us @ us'"
  shows "x \<notin> Vs (online_match G us \<sigma>)"
  using assms
  by (auto simp: online_match_append dest: online_match_mono_vs)

lemma maximal_online_match_aux:
  assumes "{u,v} \<in> G"
  assumes "u \<in> set \<pi>" "v \<in> set \<sigma>"
  assumes "set \<pi> \<inter> set \<sigma> = {}"
  assumes "u \<notin> Vs (online_match G \<pi> \<sigma>)" "v \<notin> Vs (online_match G \<pi> \<sigma>)"
  shows False
proof -
  from \<open>u \<in> set \<pi>\<close> obtain us us' where split_pi: "\<pi> = us @ u # us'"
    by (auto dest: split_list)

  with \<open>u \<notin> Vs (online_match G \<pi> \<sigma>)\<close> \<open>v \<notin> Vs (online_match G \<pi> \<sigma>)\<close> have "u \<notin> Vs (online_match G us \<sigma>)" "v \<notin> Vs (online_match G us \<sigma>)"
    by (auto dest: not_matched_in_prefix)

  with \<open>{u,v} \<in> G\<close> \<open>u \<in> set \<pi>\<close> \<open>v \<in> set \<sigma>\<close> obtain v' where "{u,v'} \<in> step G u \<sigma> (online_match G us \<sigma>)"
    by (auto dest: step_matches_if_possible)

  with split_pi have "{u,v'} \<in> online_match G \<pi> \<sigma>"
    by (simp add: online_match_append online_match_mono)

  with \<open>u \<notin> Vs (online_match G \<pi> \<sigma>)\<close> show False by auto
qed

lemma maximal_online_match:
  assumes bipartite: "bipartite G (set \<pi>) (set \<sigma>)"
  shows "maximal_matching G (online_match G \<pi> \<sigma>)"
proof (rule ccontr)
  assume "\<not>maximal_matching G (online_match G \<pi> \<sigma>)"

  with bipartite_disjointD[OF assms] matching_online_match[of \<pi> \<sigma> G]
  obtain u v where unmatched: "{u,v} \<in> G" "u \<notin> Vs (online_match G \<pi> \<sigma>)" "v \<notin> Vs (online_match G \<pi> \<sigma>)"
    by (auto elim: not_maximal_matchingE)

  with bipartite consider "u \<in> set \<pi>" "v \<in> set \<sigma>" | "u \<in> set \<sigma>" "v \<in> set \<pi>"
    by (metis bipartite_edgeE doubleton_eq_iff)

  then show False
    by cases 
       (use unmatched \<open>set \<pi> \<inter> set \<sigma> = {}\<close> in \<open>auto intro: maximal_online_match_aux dest: edge_commute\<close>)
qed

lemma online_match_matched_together:
  assumes bipartite: "bipartite G (set \<pi>) (set \<sigma>)"
  assumes "{u,v} \<in> online_match G \<pi> \<sigma>"
  assumes "u \<in> set \<pi>" "u \<notin> set us" "\<pi> = us @ us'"
  shows "v \<notin> Vs (online_match G us \<sigma>)"
proof
  assume "v \<in> Vs (online_match G us \<sigma>)"

  from bipartite have "graph_invar G"
    using finite_parts_bipartite_graph_invar
    by auto


  with \<open>v \<in> Vs (online_match G us \<sigma>)\<close> obtain u' where u': "{u',v} \<in> online_match G us \<sigma>"
    by (meson graph_abs_online_match graph_invar_vertex_edgeE')
    

  with \<open>\<pi> = us @ us'\<close> have "{u',v} \<in> online_match G \<pi> \<sigma>"
    by (simp add: online_match_append online_match_mono)

  from bipartite \<open>u \<notin> set us\<close> \<open>u \<in> set \<pi>\<close> have "u \<notin> Vs (online_match G us \<sigma>)"
    by (auto dest: online_match_Vs_subset bipartite_disjointD)

  with u' have "u \<noteq> u'" by auto

  with bipartite \<open>{u,v} \<in> online_match G \<pi> \<sigma>\<close> \<open>{u',v} \<in> online_match G \<pi> \<sigma>\<close> show False
    by (auto dest!: bipartite_disjointD dest: matching_online_match the_match)
qed

lemma online_match_lowest_free_rank_match:
  assumes bipartite: "bipartite G (set \<pi>) (set \<sigma>)"
  assumes "{u,v} \<in> online_match G \<pi> \<sigma>"
  assumes "{u,v'} \<in> G"
  assumes v'_before_v: "index \<sigma> v' < index \<sigma> v"
  shows "\<exists>u'. {u',v'} \<in> online_match G \<pi> \<sigma> \<and> index \<pi> u' < index \<pi> u"
proof (rule ccontr)
  assume contr: "\<nexists>u'. {u', v'} \<in> online_match G \<pi> \<sigma> \<and> index \<pi> u' < index \<pi> u"

  from \<open>{u,v} \<in> online_match G \<pi> \<sigma>\<close> have "{u,v} \<in> G"
    by (auto intro: subgraph_online_match)

  from v'_before_v have "v' \<in> set \<sigma>"
    by (auto dest: index_less_in_set)

  with bipartite \<open>{u,v'} \<in> G\<close> have "u \<in> set \<pi>"
    by (auto dest: bipartite_edgeD edge_commute)

  with bipartite \<open>{u,v} \<in> online_match G \<pi> \<sigma>\<close> have "v \<in> set \<sigma>"
    by (auto dest: bipartite_edgeD bipartite_online_match)

  from \<open>u \<in> set \<pi>\<close> obtain us us' where split_pi: "\<pi> = us @ u # us' \<and> u \<notin> set us"
    by (auto dest: split_list_first)

  with bipartite \<open>u \<in> set \<pi>\<close> \<open>{u,v} \<in> G\<close> have "u \<notin> Vs (online_match G us \<sigma>)"
    by (auto dest: online_match_Vs_subset bipartite_edgeD)

  then have no_v': "\<And>v'. {u,v'} \<notin> online_match G us \<sigma>"
    by (auto dest: edges_are_Vs)

  from bipartite \<open>{u,v} \<in> online_match G \<pi> \<sigma>\<close> \<open>u \<in> set \<pi>\<close> split_pi have "v \<notin> Vs (online_match G us \<sigma>)"
    by (intro online_match_matched_together) auto

  with \<open>u \<notin> Vs (online_match G us \<sigma>)\<close> \<open>v \<in> set \<sigma>\<close> \<open>{u,v} \<in> G\<close>
  obtain v'' where v'': "{u,v''} \<in> step G u \<sigma> (online_match G us \<sigma>)"
    by (auto dest: step_matches_if_possible)

  show False
  proof (cases "v = v''")
    case True

    from v'' no_v' have v_lowest_rank: "\<forall>v'\<in>set \<sigma> \<inter> {v''. {u, v''} \<in> G} - Vs (online_match G us \<sigma>) - {v''}. index \<sigma> v'' < index \<sigma> v'"
      by (auto elim!: edge_matched_in_stepE simp: doubleton_eq_iff)

    from v'_before_v have "v \<noteq> v'" by blast

    have "v' \<notin> Vs (online_match G us \<sigma>)"
    proof
      assume "v' \<in> Vs (online_match G us \<sigma>)"
      then obtain e where "e \<in> online_match G us \<sigma>" "v' \<in> e"
        by (auto elim: vs_member_elim)

      with \<open>v' \<in> set \<sigma>\<close> bipartite obtain u' where "e = {u',v'}" "u' \<in> set us"
        by (auto elim!: bipartite_edgeE dest!: subgraph_online_match dest: bipartite_disjointD)
           (metis \<open>e \<in> online_match G us \<sigma>\<close> bipartite_vertex(2) edges_are_Vs(1) online_match_Vs_subset subgraph_online_match)

      with split_pi have "index \<pi> u' < index \<pi> u"
        by (auto simp: index_append)

      with contr split_pi \<open>e \<in> online_match G us \<sigma>\<close> \<open>e = {u',v'}\<close> show False
        using online_match_append online_match_mono by blast
    qed

    with True \<open>v' \<in> set \<sigma>\<close> \<open>{u,v'} \<in> G\<close> \<open>v \<noteq> v'\<close> have "v'\<in>set \<sigma> \<inter> {v''. {u, v''} \<in> G} - Vs (online_match G us \<sigma>) - {v''}"
      by blast

    with True v_lowest_rank v'_before_v show ?thesis
      by (meson not_less_iff_gr_or_eq)
  next
    case False

    from split_pi have "online_match G \<pi> \<sigma> = online_match' G us' \<sigma> (step G u \<sigma> (online_match G us \<sigma>))"
      by (simp add: online_match_foldl)

    with \<open>{u,v''} \<in> step G u \<sigma> (online_match G us \<sigma>)\<close> have "{u,v''} \<in> online_match G \<pi> \<sigma>"
      by (auto intro: online_match_mono)

    with bipartite False \<open>{u,v} \<in> online_match G \<pi> \<sigma>\<close> the_match' show ?thesis
      by (metis bipartite_disjointD matching_online_match)
  qed
qed

lemma online_match_earliest_match:
  assumes bipartite: "bipartite G (set \<pi>) (set \<sigma>)"
  assumes "{u,v} \<in> online_match G \<pi> \<sigma>"
  assumes "{u',v} \<in> G"
  assumes u'_before_u: "index \<pi> u' < index \<pi> u"
  shows "\<exists>v'. {u',v'} \<in> online_match G \<pi> \<sigma> \<and> index \<sigma> v' < index \<sigma> v"
proof (rule ccontr)
  assume contr: "\<nexists>v'. {u',v'} \<in> online_match G \<pi> \<sigma> \<and> index \<sigma> v' < index \<sigma> v"

  from u'_before_u have "u' \<in> set \<pi>"
    by (auto intro: index_less_in_set)

  with bipartite \<open>{u',v} \<in> G\<close> have "v \<in> set \<sigma>"
    by (auto dest: bipartite_edgeD)

  with bipartite \<open>{u,v} \<in> online_match G \<pi> \<sigma>\<close> have "u \<in> set \<pi>"
    by (auto dest: bipartite_online_match bipartite_edgeD)

  from \<open>u' \<in> set \<pi>\<close> obtain us us' where split_pi: "\<pi> = us @ u' # us' \<and> u' \<notin> set us"
    by (auto dest: split_list_first)

  with u'_before_u have "u \<notin> set us"
    by (auto simp: index_append index_le_size leD)

  with bipartite \<open>u \<in> set \<pi>\<close> have  "u \<notin> Vs (online_match G us \<sigma>)"
    by (auto dest: bipartite_disjointD online_match_Vs_subset)

  with bipartite \<open>{u,v} \<in> online_match G \<pi> \<sigma>\<close> \<open>u \<in> set \<pi>\<close> \<open>u \<notin> set us\<close> split_pi have "v \<notin> Vs (online_match G us \<sigma>)"
    by (meson online_match_matched_together)

  from bipartite \<open>u' \<in> set \<pi>\<close> split_pi have "u' \<notin> Vs (online_match G us \<sigma>)"
    by (auto dest: bipartite_disjointD online_match_Vs_subset)

  with \<open>v \<notin> Vs (online_match G us \<sigma>)\<close> \<open>v \<in> set \<sigma>\<close> \<open>{u',v} \<in> G\<close>
  obtain v' where v': "{u',v'} \<in> step G u' \<sigma> (online_match G us \<sigma>)"
    by (auto dest: step_matches_if_possible)

  show False
  proof (cases "v' = v")
    case True
    from u'_before_u have "u \<noteq> u'" by blast

    from v' split_pi have "{u',v'} \<in> online_match G \<pi> \<sigma>"
      by (auto simp: online_match_append dest: online_match_mono)

    with True bipartite \<open>{u,v} \<in> online_match G \<pi> \<sigma>\<close> \<open>u \<noteq> u'\<close> show ?thesis
      by (metis bipartite_disjointD matching_online_match the_match)
  next
    case False

    from \<open>u' \<notin> Vs (online_match G us \<sigma>)\<close> have "{u',v'} \<notin> online_match G us \<sigma>"
      by (auto dest: edges_are_Vs)

    with v' have v'_lowest_rank: "\<forall>v\<in>set \<sigma> \<inter> {v''. {u', v''} \<in> G} - Vs (online_match G us \<sigma>) - {v'}. index \<sigma> v' < index \<sigma> v"
      by (auto elim!: edge_matched_in_stepE simp: doubleton_eq_iff)

    from False \<open>v \<in> set \<sigma>\<close> \<open>{u',v} \<in> G\<close> \<open>v \<notin> Vs (online_match G us \<sigma>)\<close>
    have "v \<in> set \<sigma> \<inter> {v''. {u',v''} \<in> G} - Vs (online_match G us \<sigma>) - {v'}" by blast

    with v'_lowest_rank have "index \<sigma> v' < index \<sigma> v" by blast

    with contr split_pi \<open>{u',v'} \<in> step G u' \<sigma> (online_match G us \<sigma>)\<close> show ?thesis
      by (auto simp: online_match_append dest: online_match_mono)
  qed
qed

text \<open>
  The algorithm produces a matching which satisfies \<^term>\<open>ranking_matching\<close>.
\<close>
lemma\<^marker>\<open>tag important\<close> ranking_matching_online_match:
  "bipartite G (set \<pi>) (set \<sigma>) \<Longrightarrow> ranking_matching G (online_match G \<pi> \<sigma>) \<pi> \<sigma>"
  unfolding ranking_matching_def
  by (auto dest: bipartite_disjointD online_match_lowest_free_rank_match online_match_earliest_match
           intro: matching_online_match subgraph_online_match maximal_online_match)

text \<open>
  From this fact and the uniqueness of \<^term>\<open>ranking_matching\<close> we can easily prove the
  interchangeability of the online and offline vertices also for the algorithm.
\<close>
lemma online_match_commute:
  assumes "bipartite G (set \<pi>) (set \<sigma>)"
  shows "online_match G \<pi> \<sigma> = online_match G \<sigma> \<pi>"
  using assms
  by (auto intro!: ranking_matching_unique intro: ranking_matching_commute dest: ranking_matching_online_match bipartite_commute)

lemma bipartite_ranking_matchingE:
  assumes "bipartite G (set \<pi>) (set \<sigma>)"
  obtains M where "ranking_matching G M \<pi> \<sigma>"
  using assms
  by (auto dest: ranking_matching_online_match)

subsection \<open>Removing a Vertex (Lemma 2)\label{sec:ranking-zigzag}\<close>
text \<open>
  Lemma 2 from~\cite{birnbaum2008} describes what happens when we remove a vertex \<^term>\<open>x::'a\<close> from
  a graph \<^term>\<open>G::'a graph\<close>, resulting in \<^term>\<open>G'::'a graph\<close>, and run RANKING on them with
  the same arrival order \<^term>\<open>\<pi>::'a set\<close>, and ranking \<^term>\<open>\<sigma>::'a set\<close> (removing \<^term>\<open>x::'a\<close> from
  them as well for the run on \<^term>\<open>G'\<close>\<^footnote>\<open>For the given definition of \<^term>\<open>online_match\<close> removing a vertex
  from any of the inputs (i.e.\ graph, arrival order, or ranking) is equivalent to removing it
  from all of them.\<close>). It states that the run
  on \<^term>\<open>G::'a graph\<close> and \<^term>\<open>G'::'a graph\<close> differ by at most one \<^emph>\<open>alternating\<close> (not
  necessarily augmenting) path starting at \<^term>\<open>x::'a\<close>. Hence, the produced matching on \<^term>\<open>G::'a graph\<close>
  is always at least as big as the one produced on \<^term>\<open>G'::'a graph\<close>. By repeatedly applying this
  to vertices which are not in a maximum matching, we can reduce the analysis of the competitive
  ratio to instances with a perfect matching.

  In~\cite{birnbaum2008} only a brief explanation and an illustration was provided as proof of this
  statement. The following formal proof is the first proper proof of this statement. It required
  much more rigor and a complete specification of the alternating path that results when removing a vertex.
\<close>

text \<open>
  Under the assumption \<^term>\<open>ranking_matching G M \<pi> \<sigma>\<close>, the following predicate specifies that
  \<^term>\<open>u \<in> set \<pi>\<close> would be matched to \<^term>\<open>v' \<in> set \<sigma>\<close>, when removing \<^term>\<open>v \<in> set \<sigma>\<close>
  (where \<^term>\<open>v\<close> is supposed to be the vertex \<^emph>\<open>originally\<close> matched to \<^term>\<open>u\<close>).
\<close>
definition "shifts_to G M u v v' \<pi> \<sigma> = (
  \<comment> \<open>\<^term>\<open>v'::'a\<close> comes after \<^term>\<open>v::'a\<close> and there's an edge to \<^term>\<open>u::'a\<close>\<close>
  u \<in> set \<pi> \<and> v' \<in> set \<sigma> \<and> index \<sigma> v < index \<sigma> v' \<and> {u,v'} \<in> G \<and>
  \<comment> \<open>but \<^term>\<open>v'::'a\<close> is not matched to some \<^term>\<open>u'::'a\<close> before \<^term>\<open>u::'a\<close>\<close>
    (\<nexists>u'. index \<pi> u' < index \<pi> u \<and> {u',v'} \<in> M) \<and>
  \<comment> \<open>every other vertex between \<^term>\<open>v::'a\<close> and \<^term>\<open>v'::'a\<close> is not connected to \<^term>\<open>u::'a\<close> or
    matched to some \<^term>\<open>u'::'a\<close> before \<^term>\<open>u::'a\<close>\<close>
    (\<forall>v''. (index \<sigma> v < index \<sigma> v'' \<and> index \<sigma> v'' < index \<sigma> v') \<longrightarrow>
      ({u,v''} \<notin> G \<or> (\<exists>u'. index \<pi> u' < index \<pi> u \<and> {u',v''} \<in> M)))
     )"

text \<open>
  The following mutually recursive functions describe the alternating path that
  results when removing a vertex. In particular \<^term>\<open>zig G M v \<pi> \<sigma>\<close> gives the path when
  removing \<^term>\<open>v \<in> set \<sigma>\<close> from \<^term>\<open>G::'a graph\<close> (where again generally assume
  \<^term>\<open>ranking_matching G M \<pi> \<sigma>\<close>). \<^term>\<open>zig\<close> simply selects the vertex \<^term>\<open>u\<close> that is matched to
  \<^term>\<open>v\<close> if possible. Since the removal makes \<^term>\<open>v\<close> unavailable to \<^term>\<open>u\<close>, \<^term>\<open>zag\<close> then
  checks -- employing \<^term>\<open>shifts_to\<close> -- if \<^term>\<open>u\<close> would be matched to some other vertex \<^term>\<open>v'\<close>.
  If that is the case, \<^term>\<open>v'\<close> of course is not available to vertices following \<^term>\<open>u\<close>, which
  is equivalent to removing \<^term>\<open>v'\<close> for them -- hence we complete the zig-zag by another call
  to \<^term>\<open>zig\<close> with \<^term>\<open>v'\<close>.

  This cascading of choosing a matching partner and shifting those matching partners to the next
  available partner fully describes the resulting path when removing a vertex. Note, that due to
  the interchangeability of the online and offline vertices, this also works for removing a vertex
  \<^term>\<open>u \<in> set \<pi>\<close> via \<^term>\<open>zig G M u \<sigma> \<pi>\<close> (observe the swap of \<^term>\<open>\<pi>::'a list\<close> and
  \<^term>\<open>\<sigma>::'a list\<close>).

  The induction scheme these mutually recursive functions yield is key in proving properties
  required for showing that the difference between the two matchings in question is this
  alternating path.
\<close>
function zig :: "'a graph \<Rightarrow> 'a graph \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
and zag :: "'a graph \<Rightarrow> 'a graph \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  proper_zig: "zig G M v \<pi> \<sigma> = v # (
                    if \<exists>u. {u,v} \<in> M 
                    then zag G M (THE u. {u,v} \<in> M) \<pi> \<sigma>
                    else [])" if "matching M"
| no_matching_zig: "zig _ M v _ _ = [v]" if "\<not>matching M"

| proper_zag: "zag G M u \<pi> \<sigma> =  u # (if \<exists>v. {u,v} \<in> M
                      then 
                      (let v = THE v. {u,v} \<in> M in (
                        if \<exists>v'. shifts_to G M u v v' \<pi> \<sigma>
                        then zig G M (THE v'. shifts_to G M u v v' \<pi> \<sigma>) \<pi> \<sigma>
                        else [])
                      )
                      else []
                    )" if "matching M"
| no_matching_zag: "zag _ M v _ _ = [v]" if "\<not>matching M"
  by auto (metis prod_cases5 sumE)

definition zig_zag_relation where
  "zig_zag_relation =
    {(Inr (G, M, u, \<pi>, \<sigma>), Inl (G, M, v, \<pi>, \<sigma>)) | (G :: 'a graph) M u v \<pi> \<sigma>. matching M \<and> {u,v} \<in> M \<and> ((\<exists>v'. shifts_to G M u v v' \<pi> \<sigma>) \<longrightarrow> index \<sigma> v < index \<sigma> (THE v'. shifts_to G M u v v' \<pi> \<sigma>))} \<union>
    {(Inl (G, M, v', \<pi>, \<sigma>), Inr (G, M, u, \<pi>, \<sigma>)) | (G :: 'a graph) M u v' \<pi> \<sigma>. matching M \<and> (\<exists>v. {u,v} \<in> M \<and> shifts_to G M u (THE v. {u,v} \<in> M) v' \<pi> \<sigma>) \<and> index \<sigma> (THE v. {u,v} \<in> M) < index \<sigma> v'}"

lemma shifts_to_only_from_input:
  assumes "shifts_to G M u v v' \<pi> \<sigma>"
  shows "v \<in> set \<sigma>" "v' \<in> set \<sigma>"
  using assms
  unfolding shifts_to_def
  by (auto intro: index_less_in_set)

lemma shifts_to_inj:
  assumes "shifts_to G M u v v' \<pi> \<sigma>"
  assumes "shifts_to G M u v v'' \<pi> \<sigma>"
  shows "v' = v''"
  using assms
  unfolding shifts_to_def
  by (metis index_eq_index_conv not_less_iff_gr_or_eq)

lemma shifts_to_graph_edge:
  assumes "shifts_to G M u v v' \<pi> \<sigma>"
  shows "{u,v'} \<in> G"
  using assms
  unfolding shifts_to_def
  by blast

lemma the_shifts_to:
  assumes "shifts_to G M u v v' \<pi> \<sigma>"
  shows "(THE v'. shifts_to G M u v v' \<pi> \<sigma>) = v'"
  using assms
  by (auto dest: shifts_to_inj)

lemma zig_zag_relation_unique:
  "(y,x) \<in> zig_zag_relation \<Longrightarrow> (y',x) \<in> zig_zag_relation \<Longrightarrow> y = y'"
  unfolding zig_zag_relation_def
  by (auto dest: the_match shifts_to_inj)

lemma zig_zag_relation_increasing_rank:
  assumes "(Inr (G, M, u, \<pi>, \<sigma>), Inl (G, M, v, \<pi>, \<sigma>)) \<in> zig_zag_relation"
  assumes "(Inl (G, M, v', \<pi>, \<sigma>), Inr (G, M, u, \<pi>, \<sigma>)) \<in> zig_zag_relation"
  shows "index \<sigma> v < index \<sigma> v'"
proof -
  from \<open>(Inr (G, M, u, \<pi>, \<sigma>), Inl (G, M, v, \<pi>, \<sigma>)) \<in> zig_zag_relation\<close> have "matching M"
    "{u,v} \<in> M"
    unfolding zig_zag_relation_def
    by auto

  then have "(THE v. {u,v} \<in> M) = v" by (auto intro: the_match')

  with \<open>(Inl (G, M, v', \<pi>, \<sigma>), Inr (G, M, u, \<pi>, \<sigma>)) \<in> zig_zag_relation\<close> show ?thesis
    unfolding zig_zag_relation_def
    by simp
qed

lemma wf_zig_zag_relation_Inl_aux:
  assumes "\<forall>x. (\<forall>y. (y,x) \<in> zig_zag_relation \<longrightarrow> P y) \<longrightarrow> P x"
  shows "P (Inl a)"
proof (cases a)
  case (fields G M v \<pi> \<sigma>)
  have PI: "\<And>x. (\<And>y. (y,x) \<in> zig_zag_relation \<Longrightarrow> P y) \<Longrightarrow> P x" using assms by blast

  have "P (Inl (G, M, v, \<pi>, \<sigma>))"
  proof (induction v \<sigma> rule: index_gt_induct)
    case (index_gt v)
    then show ?case
    proof (cases "\<exists>y. (y, Inl (G, M, v, \<pi>, \<sigma>)) \<in> zig_zag_relation")
      case True
      then obtain u where "(Inr (G, M, u, \<pi>, \<sigma>), Inl (G, M, v, \<pi>, \<sigma>)) \<in> zig_zag_relation"
        unfolding zig_zag_relation_def by auto

      then have "\<And>y. (y, Inl (G, M, v, \<pi>, \<sigma>)) \<in> zig_zag_relation \<Longrightarrow> y = Inr (G, M, u, \<pi>, \<sigma>)"
        by (simp add: zig_zag_relation_unique)

      show ?thesis
      proof (cases "\<exists>x'. (x', Inr (G, M, u, \<pi>, \<sigma>)) \<in> zig_zag_relation")
        case True
        then obtain v' where "(Inl (G, M, v', \<pi>, \<sigma>), Inr (G, M, u, \<pi>, \<sigma>)) \<in> zig_zag_relation"
          unfolding zig_zag_relation_def by auto

        then have "\<And>x'. (x', Inr (G, M, u, \<pi>, \<sigma>)) \<in> zig_zag_relation \<Longrightarrow> x' = Inl (G, M, v', \<pi>, \<sigma>)"
          by (simp add: zig_zag_relation_unique)

        have "P (Inl (G, M, v', \<pi>, \<sigma>))"
          using \<open>(Inr (G, M, u, \<pi>, \<sigma>), Inl (G, M, v, \<pi>, \<sigma>)) \<in> zig_zag_relation\<close>
            \<open>(Inl (G, M, v', \<pi>, \<sigma>), Inr (G, M, u, \<pi>, \<sigma>)) \<in> zig_zag_relation\<close>
          by (auto intro: index_gt zig_zag_relation_increasing_rank)

        then have "P (Inr (G, M, u, \<pi>, \<sigma>))"
          using PI \<open>\<And>x'. (x', Inr (G, M, u, \<pi>, \<sigma>)) \<in> zig_zag_relation \<Longrightarrow> x' = Inl (G, M, v', \<pi>, \<sigma>)\<close> by blast

        then show ?thesis
          using PI \<open>\<And>y. (y, Inl (G, M, v, \<pi>, \<sigma>)) \<in> zig_zag_relation \<Longrightarrow> y = Inr (G, M, u, \<pi>, \<sigma>)\<close> by blast
      next
        case False
        then show ?thesis
          using PI \<open>(Inr (G, M, u, \<pi>, \<sigma>), Inl (G, M, v, \<pi>, \<sigma>)) \<in> zig_zag_relation\<close> zig_zag_relation_unique by blast
      qed
    next
      case False
      then show ?thesis
        using \<open>\<forall>x. (\<forall>y. (y, x) \<in> zig_zag_relation \<longrightarrow> P y) \<longrightarrow> P x\<close> by blast
    qed
  qed
  with fields show ?thesis by simp
qed

lemma wf_zig_zag_relation_aux:
  assumes "\<forall>x. (\<forall>y. (y,x) \<in> zig_zag_relation \<longrightarrow> P y) \<longrightarrow> P x"
  shows "P x"
proof -
  have PI: "\<And>x. (\<And>y. (y,x) \<in> zig_zag_relation \<Longrightarrow> P y) \<Longrightarrow> P x" using assms by blast
  show "P x"
  proof (cases x)
    case Inl
    with assms wf_zig_zag_relation_Inl_aux show ?thesis by blast
  next
    case (Inr b)
    then show ?thesis
    proof (cases "\<exists>y. (y, Inr b) \<in> zig_zag_relation")
      case True
      then obtain a where "(Inl a, Inr b) \<in> zig_zag_relation" 
        unfolding zig_zag_relation_def by blast

      then have "\<And>y. (y, Inr b) \<in> zig_zag_relation \<Longrightarrow> y = Inl a"
        by (simp add: zig_zag_relation_unique)

      have "P (Inl a)" using assms wf_zig_zag_relation_Inl_aux by blast

      then show ?thesis
        using Inr PI \<open>\<And>y. (y, Inr b) \<in> zig_zag_relation \<Longrightarrow> y = Inl a\<close> by blast
    next
      case False
      then show ?thesis
        using Inr PI by blast
    qed
  qed
qed

lemma wf_zig_zag_relation: "wf zig_zag_relation"
  using wf_def wf_zig_zag_relation_aux by auto

termination zig
proof (relation zig_zag_relation, goal_cases)
  case 1
  then show ?case
    by (rule wf_zig_zag_relation)
next
  case (2 M G v \<pi> \<sigma>)

  then show ?case
    unfolding zig_zag_relation_def
  proof (intro UnI1 CollectI exI conjI, goal_cases)
    case 1
    then show "(Inr (G, M, THE u. {u, v} \<in> M, \<pi>, \<sigma>), Inl (G, M, v, \<pi>, \<sigma>)) = (Inr (G, M, THE u. {u, v} \<in> M, \<pi>, \<sigma>), Inl (G, M, v, \<pi>, \<sigma>))"
      by simp
  next
    case 2
    then show "matching M" by blast
  next
    case 3
    then show "{THE u. {u, v} \<in> M, v} \<in> M"
      by (auto simp: the_match)
  next
    case 4
    then show "(\<exists>v'. shifts_to G M (THE u. {u, v} \<in> M) v v' \<pi> \<sigma>) \<longrightarrow> index \<sigma> v < index \<sigma> (THE v'. shifts_to G M (THE u. {u, v} \<in> M) v v' \<pi> \<sigma>)"
    proof (intro impI)
      assume "matching M" "\<exists>u. {u,v} \<in> M" and shift: "\<exists>v'. shifts_to G M (THE u. {u, v} \<in> M) v v' \<pi> \<sigma>"
      then obtain u where the_u: "(THE u. {u,v} \<in> M) = u"
        by (auto simp: the_match)

      with shift obtain v' where "shifts_to G M u v v' \<pi> \<sigma>" "(THE v'. shifts_to G M u v v' \<pi> \<sigma>) = v'"
        by (auto simp: the_shifts_to)

      with the_u show "index \<sigma> v < index \<sigma> (THE v'. shifts_to G M (THE u. {u, v} \<in> M) v v' \<pi> \<sigma>)"
        by (auto simp: shifts_to_def)
    qed
  qed
next
  case (3 M G u \<pi> \<sigma> x)
  then show ?case
    unfolding zig_zag_relation_def
  proof (intro UnI2 CollectI exI conjI, goal_cases)
    case 1
    show "(Inl (G, M, THE v'. shifts_to G M u x v' \<pi> \<sigma>, \<pi>, \<sigma>), Inr (G, M, u, \<pi>, \<sigma>)) = (Inl (G, M, THE v'. shifts_to G M u x v' \<pi> \<sigma>, \<pi>, \<sigma>), Inr (G, M, u, \<pi>, \<sigma>))"
      by blast
  next
    case 2
    then show "matching M" by blast
  next
    case 3
    then show "{u, x} \<in> M"
      by (smt (verit, del_insts) theI' the_match''')
  next
    case 4
    then obtain v' where v': "shifts_to G M u x v' \<pi> \<sigma>" "(THE v'. shifts_to G M u x v' \<pi> \<sigma>) = v'"
      by (auto simp: the_shifts_to)

    then show "shifts_to G M u (THE v. {u, v} \<in> M) (THE v'. shifts_to G M u x v' \<pi> \<sigma>) \<pi> \<sigma>"
      by (simp flip: \<open>x = (THE v. {u,v} \<in> M)\<close>)

    case 5
    from v' show "index \<sigma> (THE v. {u, v} \<in> M) < index \<sigma> (THE v'. shifts_to G M u x v' \<pi> \<sigma>)"
      by (simp flip: \<open>x = (THE v. {u,v} \<in> M)\<close> add: shifts_to_def)
  qed
qed

text \<open>
  Restating the induction scheme of \<^term>\<open>zig\<close>-\<^term>\<open>zag\<close> and explicitly stating a case distinction
  makes dealing with the definite description easier.
\<close>
lemma zig_zag_induct[case_names zig_matched zig_unmatched zig_no_matching zag zag_no_matching]:
  assumes "\<And>G M v \<pi> \<sigma>. matching M \<Longrightarrow> (\<And>u. {u,v} \<in> M \<Longrightarrow> (THE u. {u,v} \<in> M) = u \<Longrightarrow> Q G M u \<pi> \<sigma> \<Longrightarrow> P G M v \<pi> \<sigma>)"
  assumes "\<And>G M v \<pi> \<sigma>. matching M \<Longrightarrow> \<nexists>u. {u,v} \<in> M \<Longrightarrow> P G M v \<pi> \<sigma>"
  assumes "\<And>G M v \<pi> \<sigma>. \<not>matching M \<Longrightarrow> P G M v \<pi> \<sigma>"
  assumes "\<And>G M u \<pi> \<sigma>. matching M \<Longrightarrow> (\<And>v v'. {u, v} \<in> M \<Longrightarrow> shifts_to G M u v v' \<pi> \<sigma> \<Longrightarrow> P G M v' \<pi> \<sigma>) \<Longrightarrow> Q G M u \<pi> \<sigma>"
  assumes "\<And>G M u \<pi> \<sigma>. \<not>matching M \<Longrightarrow> Q G M u \<pi> \<sigma>"
  shows "P G M v \<pi> \<sigma>" and "Q G M u \<pi> \<sigma>"
proof (induction G M v \<pi> \<sigma> and G M u \<pi> \<sigma> rule: zig_zag.induct)
  case (1 M G v \<pi> \<sigma>)
  then show ?case
  proof (cases "\<exists>u. {u,v} \<in> M")
    case True
    then obtain u where "{u,v} \<in> M" by blast
    with \<open>matching M\<close> have "(THE u. {u,v} \<in> M) = u"
      by (simp add: the_match)
    with True assms 1 \<open>{u,v} \<in> M\<close> show ?thesis
      by blast
  next
    case False
    with assms 1 show ?thesis
      by blast
  qed
next
  case (3 M G u \<pi> \<sigma>)
  then show ?case
  proof (cases "\<exists>v. {u,v} \<in> M")
    case True
    then obtain v where "{u,v} \<in> M" by blast
    with \<open>matching M\<close> have the_v: "(THE v. {u,v} \<in> M) = v"
      by (simp add: the_match')

    then show ?thesis
    proof (cases "\<exists>v'. shifts_to G M u v v' \<pi> \<sigma>")
      case True
      then obtain v' where shifts_to: "shifts_to G M u v v' \<pi> \<sigma>" by blast
      then have "(THE v'. shifts_to G M u v v' \<pi> \<sigma>) = v'"
        by (simp add: the_shifts_to)

      with "3.IH"[OF \<open>\<exists>v. {u,v} \<in> M\<close> the_v[symmetric] True, simplified this]
      assms(4)[OF \<open>matching M\<close>] show ?thesis
        by (metis "3.hyps" \<open>{u, v} \<in> M\<close> the_match' the_shifts_to)
    next
      case False
      with assms \<open>{u,v} \<in> M\<close> show ?thesis
        by (metis the_match')
    qed
  next
    case False
    with assms show ?thesis
      by metis
  qed
qed (use assms in auto)

lemma zag_casesE[case_names has_shifts_to has_no_shifts_to unmatched]:
  obtains "\<exists>v. {u,v} \<in> M \<and> (\<exists>v'. shifts_to G M u v v' \<pi> \<sigma>)" | "\<exists>v. {u,v} \<in> M \<and> (\<nexists>v'. shifts_to G M u v v' \<pi> \<sigma>)" | "\<nexists>v. {u,v} \<in> M"
  by blast

declare zig.simps[simp del] zag.simps[simp del]

fun_cases zig_ConsE: "zig G M v \<pi> \<sigma> = v' # uvs"
fun_cases zig_SingleE: "zig G M v \<pi> \<sigma> = [v']"
fun_cases zig_NilE: "zig G M v \<pi> \<sigma> = []"
thm zig_ConsE zig_SingleE zig_NilE

lemmas zig_symE = zig_ConsE[OF sym] zig_SingleE[OF sym] zig_NilE[OF sym]

fun_cases zag_ConsE: "zag G M u \<pi> \<sigma> = u' # uvs"
fun_cases zag_SingleE: "zag G M u \<pi> \<sigma> = [u']"
fun_cases zag_NilE: "zag G M u \<pi> \<sigma> = []"
thm zag_ConsE zag_SingleE zag_NilE

lemmas zag_symE = zag_ConsE[OF sym] zag_SingleE[OF sym] zag_NilE[OF sym]

lemma hd_zig: "hd (zig G M x \<pi> \<sigma>) = x"
  by (cases "matching M")
     (auto simp: zig.simps)

lemma zig_hdE:
  obtains uvs where "zig G M v \<pi> \<sigma> = v # uvs"
  by (cases "matching M")
     (auto simp: zig.simps)

lemma hd_zag: "hd (zag G M x \<pi> \<sigma>) = x"
  by (cases "matching M")
     (auto simp: zag.simps)

lemma zag_hdE:
  obtains vus where "zag G M u \<pi> \<sigma> = u # vus"
  by (cases "matching M")
     (auto simp: zag.simps)

lemma zig_Cons_zagE:
  assumes "zig G M v \<pi> \<sigma> = v' # zag G M u \<pi> \<sigma>"
  obtains "v = v'" "{u,v} \<in> M" "matching M"
  using assms
  by (auto elim: zig_ConsE zag_NilE zag_hdE split: if_splits simp: the_match zag.simps)
  
lemma zag_Cons_zigE:
  assumes "zag G M u \<pi> \<sigma> = u' # zig G M v' \<pi> \<sigma>"
  obtains v where "u = u'" "{u,v} \<in> M" "shifts_to G M u v v' \<pi> \<sigma>" "matching M"
  using assms
  by (auto elim!: zag_ConsE zig_NilE zig_hdE split: if_splits 
      simp: the_match' zig.simps the_shifts_to)

lemma zag_no_shifts_to:
  "{u,v} \<in> M \<Longrightarrow> \<nexists>v'. shifts_to G M u v v' \<pi> \<sigma> \<Longrightarrow> zag G M u \<pi> \<sigma> = [u]"
  by (cases "matching M")
     (auto simp: zag.simps the_match')

lemma zig_then_zag:
  assumes "zig G M v \<pi> \<sigma> = v' # u # vus"
  shows "zag G M u \<pi> \<sigma> = u # vus"
  using assms
  by (auto elim!: zig_ConsE zag_symE split: if_splits simp: the_match)

lemmas zig_then_zagE = zig_then_zag[elim_format]

lemma zag_then_zig:
  assumes "zag G M u \<pi> \<sigma> = u' # v # uvs"
  shows "zig G M v \<pi> \<sigma> = v # uvs"
  using assms
  by (auto elim!: zag_ConsE zig_symE split: if_splits simp: the_match' the_shifts_to)

lemmas zag_then_zigE = zag_then_zig[elim_format]

lemma zig_matching_edge: "zig G M v \<pi> \<sigma> = v' # u # uvs \<Longrightarrow> {u,v} \<in> M"
  by (auto elim!: zig_ConsE split: if_splits simp: the_match zag.simps)

lemma zag_shift_edge:
  assumes "{u,v} \<in> M"
  assumes "zag G M u \<pi> \<sigma> = u # v' # uvs"
  shows "shifts_to G M u v v' \<pi> \<sigma>"
  using assms
  by (auto elim!: zag_ConsE zig_symE split: if_splits simp: the_match' the_shifts_to)

lemma zig_increasing_ranks:
  assumes "zig G M v \<pi> \<sigma> = v # u # zig G M v' \<pi> \<sigma>"
  shows "index \<sigma> v < index \<sigma> v'"
proof -
  have "{u,v} \<in> M" using assms zig_matching_edge by fast
  then have "(THE u. {u,v} \<in> M) = u" using assms the_match zig_ConsE by fast
  with \<open>{u,v} \<in> M\<close> assms have "zig G M v \<pi> \<sigma> = v # zag G M u \<pi> \<sigma>"
    by (auto elim!: zig_ConsE intro: the_match)

  with assms \<open>{u,v} \<in> M\<close> have "shifts_to G M u v v' \<pi> \<sigma>"
    by (metis zag_shift_edge zig_hdE zig_then_zag)

  then show ?thesis unfolding shifts_to_def by blast
qed

lemma zag_increasing_arrival:
  assumes "zag G M u \<pi> \<sigma> = u # v' # zag G M u' \<pi> \<sigma>"
  shows "index \<pi> u < index \<pi> u'"
proof -
  have "matching M" using assms by (auto elim: zag_ConsE)

  obtain v where "{u,v} \<in> M" using assms
    by (auto elim: zag_ConsE split: if_splits)

  with \<open>{u,v} \<in> M\<close> \<open>matching M\<close> have zig_zag: "zig G M v \<pi> \<sigma> = v # zag G M u \<pi> \<sigma>"
    by (auto simp: zig.simps the_match)

  with assms \<open>{u,v} \<in> M\<close> have shifts_to: "shifts_to G M u v v' \<pi> \<sigma>"
    by (auto dest: zag_shift_edge)

  with \<open>{u,v} \<in> M\<close> \<open>matching M\<close> have "zag G M u \<pi> \<sigma> = u # zig G M v' \<pi> \<sigma>"
    by (fastforce simp: zag.simps the_shifts_to the_match')

  with zig_zag assms have "{u',v'} \<in> M"
    by (meson zag_then_zig zig_Cons_zagE)
    
  with shifts_to show ?thesis
    unfolding shifts_to_def
    by (metis \<open>matching M\<close> \<open>{u, v} \<in> M\<close> index_eq_index_conv linorder_neqE the_match')
qed

text \<open>
  \<^term>\<open>zig\<close>-\<^term>\<open>zag\<close> produces a list of vertices which alternate between \<^term>\<open>set \<sigma>\<close> and
  \<^term>\<open>set \<pi>\<close>.
\<close>
lemma
  assumes "bipartite M (set \<pi>) (set \<sigma>)"
  shows
    alt_list_zig: "v \<in> set \<sigma> \<Longrightarrow> alt_list (\<lambda>x. x \<in> set \<sigma>) (\<lambda>x. x \<in> set \<pi>) (zig G M v \<pi> \<sigma>)" and
    alt_list_zag: "u \<in> set \<pi> \<Longrightarrow> alt_list (\<lambda>x. x \<in> set \<pi>) (\<lambda>x. x \<in> set \<sigma>) (zag G M u \<pi> \<sigma>)"
  using assms
proof (induction G M v \<pi> \<sigma> and G M u \<pi> \<sigma> rule: zig_zag_induct)
  case (zig_matched G M v \<pi> \<sigma> u)
  then have "u \<in> set \<pi>"
    by (auto dest: bipartite_edgeD)

  with zig_matched show ?case
    by (auto simp: zig.simps intro: alt_list.intros)
next
  case (zag G M u \<pi> \<sigma>)
  from zag_casesE[of u M G \<pi> \<sigma>] show ?case
  proof cases
    case has_shifts_to
    then obtain v v' where vv': "{u,v} \<in> M" "shifts_to G M u v v' \<pi> \<sigma>" by blast
    then have "v' \<in> set \<sigma>"
      by (simp add: shifts_to_only_from_input)

    from vv' \<open>matching M\<close> have "(THE v. {u,v} \<in> M) = v" "(THE v'. shifts_to G M u v v' \<pi> \<sigma>) = v'"
      by (auto dest: the_match' the_shifts_to)

    with has_shifts_to zag vv' \<open>v' \<in> set \<sigma>\<close> show ?thesis
      by (auto simp: zag.simps intro: alt_list.intros)
  next
    case has_no_shifts_to
    then obtain v where "{u,v} \<in> M" by blast

    with has_no_shifts_to zag show ?thesis
      by (auto simp: zag_no_shifts_to intro!: alt_list.intros)      
  next
    case unmatched
    with \<open>matching M\<close> \<open>u \<in> set \<pi>\<close> show ?thesis
      by (auto simp: zag.simps intro: alt_list.intros)
  qed
qed (auto simp: zig.simps zag.simps alt_list_step alt_list_empty)

lemma rev_alt_path_zig_edges: "rev_alt_path M (zig G M v \<pi> \<sigma>)"
proof (induction "zig G M v \<pi> \<sigma>" arbitrary: v rule: induct_list012)
  case (single x)
  from this[symmetric] show ?case
    by (simp add: alt_list_empty)
next
  case (sucsuc v' u vus)
  then have zig_v: "zig G M v \<pi> \<sigma> = v' # u # vus"
    by simp

  then have "{u,v} \<in> M" "v' = v" "matching M"
    by (auto dest: zig_matching_edge elim: zig_ConsE)

  show ?case
  proof (cases vus)
    case Nil
    with zig_v \<open>v' = v\<close> \<open>{u,v} \<in> M\<close> show ?thesis
      by (auto simp: alt_list_step alt_list_empty dest: edge_commute)
  next
    case (Cons v'' uvs)
    with zig_v \<open>v' = v\<close> have "v'' \<noteq> v"
      by (metis "sucsuc.hyps"(1) \<open>{u, v} \<in> M\<close> alt_list_step edges_of_path.simps(3) zag_then_zig zig_then_zag)

    with zig_v Cons have "vus = zig G M v'' \<pi> \<sigma>"
      by (auto elim!: zig_then_zagE zag_then_zigE)

    with sucsuc Cons \<open>v'' \<noteq> v\<close> \<open>v' = v\<close> \<open>{u,v} \<in> M\<close> \<open>matching M\<close> show ?thesis
      by (metis (mono_tags, lifting) alt_list.intros(2) edge_commute edges_of_path.simps(3) the_match)
  qed
qed (simp add: alt_list_empty)

lemma zig_not_augmenting:
  "matching_augmenting_path M (zig G M x \<pi> \<sigma>) \<Longrightarrow> False"
proof (cases "2 \<le> length (zig G M x \<pi> \<sigma>)")
  case True
  assume aug: "matching_augmenting_path M (zig G M x \<pi> \<sigma>)"

  from True obtain v u vus where "zig G M x \<pi> \<sigma> = v # u # vus"
    using length_at_least_two_Cons_Cons by blast

  with aug hd_zig show ?thesis
    unfolding matching_augmenting_path_def
    by (metis edge_commute insertI1 vs_member zig_matching_edge)

next
  case False
  assume "matching_augmenting_path M (zig G M x \<pi> \<sigma>)"
  with False show ?thesis
    unfolding matching_augmenting_path_def by blast
qed

lemma zig_start_wrong_side:
  assumes "u \<notin> set \<sigma>"
  assumes "bipartite M (set \<pi>) (set \<sigma>)"
  obtains v where "zig G M u \<pi> \<sigma> = [u,v]" "{u,v} \<in> M" "v \<in> set \<sigma>" | "zig G M u \<pi> \<sigma> = [u]"
proof (cases "matching M")
  case True
  assume assm: "zig G M u \<pi> \<sigma> = [u] \<Longrightarrow> thesis"
    "(\<And>v. zig G M u \<pi> \<sigma> = [u, v] \<Longrightarrow> {u, v} \<in> M \<Longrightarrow> v \<in> set \<sigma> \<Longrightarrow> thesis)"
  
  show ?thesis
  proof (cases "\<exists>v. {u,v} \<in> M")
    case True
    then obtain v where "{u,v} \<in> M" by blast

    with assms have "v \<in> set \<sigma>"
      by (auto elim: bipartite_edgeE)

    from \<open>u \<notin> set \<sigma>\<close> have "\<nexists>u'. shifts_to G M v u u' \<pi> \<sigma>"
      by (auto dest: shifts_to_only_from_input)

    with \<open>matching M\<close> \<open>{u,v} \<in> M\<close> have "zag G M v \<pi> \<sigma> = [v]"
      by (auto simp: zag.simps dest: the_match'')

    with \<open>matching M\<close> \<open>{u,v} \<in> M\<close> have "zig G M u \<pi> \<sigma> = [u,v]"
      by (auto simp: zig.simps dest: edge_commute the_match''')

    with assm \<open>{u,v} \<in> M\<close> \<open>v \<in> set \<sigma>\<close> show ?thesis
      by blast
  next
    case False
    from False \<open>matching M\<close> have "zig G M u \<pi> \<sigma> = [u]"
      by (auto simp: zig.simps dest: edge_commute)

    with assm show ?thesis
      by blast
  qed
next
  case False
  assume assm: "zig G M u \<pi> \<sigma> = [u] \<Longrightarrow> thesis"

  from \<open>\<not>matching M\<close> have "zig G M u \<pi> \<sigma> = [u]"
    by (simp add: zig.simps)

  with assm show ?thesis
    by blast
qed

lemma sorted_wrt_rank_zig:
  assumes "bipartite M (set \<pi>) (set \<sigma>)"
  shows "sorted_wrt (\<lambda>a b. index \<sigma> a < index \<sigma> b) [x <- zig G M v \<pi> \<sigma>. x \<in> set \<sigma>]"
  using assms
proof (cases "v \<in> set \<sigma>")
  case True
  with assms show ?thesis
  proof (induction "zig G M v \<pi> \<sigma>" arbitrary: v rule: induct_list012)
    case (single x)
    from this(1)[symmetric] show ?case
      by simp
  next
    case (sucsuc v u vus v')
    then have "{u,v} \<in> M" "v' = v"
      by (metis zig_ConsE zig_matching_edge)+
  
    with sucsuc have "u \<notin> set \<sigma>"
      by (auto dest: bipartite_edgeD)
  
    show ?case
    proof (cases vus)
      case Nil
      with \<open>v # u # vus = zig G M v' \<pi> \<sigma>\<close>[symmetric] \<open>u \<notin> set \<sigma>\<close> show ?thesis
        by simp
    next
      case (Cons v'' uvs)
      with sucsuc have vus_zig: "vus = zig G M v'' \<pi> \<sigma>"
        by (metis zag_then_zig zig_then_zag)
  
      with sucsuc have "v'' \<in> set \<sigma>"
        by (metis shifts_to_only_from_input(2) zag_Cons_zigE zig_then_zag)
  
      from \<open>v # u # vus = zig G M v' \<pi> \<sigma>\<close>[symmetric] vus_zig \<open>v' = v\<close> \<open>u \<notin> set \<sigma>\<close> \<open>v' \<in> set \<sigma>\<close>
      have "[x <- zig G M v' \<pi> \<sigma>. x \<in> set \<sigma>] = v # [x <- zig G M v'' \<pi> \<sigma>. x \<in> set \<sigma>]"
        by auto
  
      with sucsuc vus_zig \<open>v' = v\<close> \<open>v'' \<in> set \<sigma>\<close> show ?thesis
        by (simp flip: successively_conv_sorted_wrt[OF transp_index_less])
           (metis (mono_tags, lifting) filter.simps(2) list.sel(1) local.Cons successively_Cons zig_increasing_ranks)
    qed
  qed simp
next
  case False
  with assms show ?thesis
    by (auto elim!: zig_start_wrong_side[where G = G] dest: bipartite_edgeD)
qed

lemma zag_start_wrong_side:
  assumes "v \<notin> set \<pi>"
  assumes "bipartite M (set \<pi>) (set \<sigma>)"
  shows "zag G M v \<pi> \<sigma> = [v]"
  using assms
  by (cases "matching M")
     (auto simp: zag.simps shifts_to_def)

lemma sorted_wrt_arrival_zag:
  assumes "bipartite M (set \<pi>) (set \<sigma>)"
  shows "sorted_wrt (\<lambda>a b. index \<pi> a < index \<pi> b) [x <- zag G M u \<pi> \<sigma>. x \<in> set \<pi>]"
proof (cases "u \<in> set \<pi>")
  case True
  then show ?thesis
  proof (induction "zag G M u \<pi> \<sigma>" arbitrary: u rule: induct_list012)
    case (single x)
    from this(1)[symmetric] show ?case
      by simp
  next
    case (sucsuc u' v uvs)
    then show ?case
    proof (cases uvs)
      case Nil
      with sucsuc show ?thesis
        by (metis alt_list_step alt_list_zag assms bipartite_disjointD disjoint_iff filter.simps(1) filter.simps(2) sorted_wrt1)
    next
      case (Cons u'' vus)
      with sucsuc have uvs_zag: "uvs = zag G M u'' \<pi> \<sigma>"
        by (metis zag_then_zig zig_then_zag)

      with sucsuc assms have "u'' \<in> set \<pi>"
        by (metis alt_list_step alt_list_zag zag_hdE)

      with sucsuc assms have "v \<notin> set \<pi>"
        by (metis DiffE bipartite_edgeD(1) local.Cons zag_then_zig zig_matching_edge)

      from sucsuc have "u' \<in> set \<pi>"
        by (auto elim: zag_symE)

      with \<open>u' # v # uvs = zag G M u \<pi> \<sigma>\<close>[symmetric] uvs_zag \<open>v \<notin> set \<pi>\<close> have "[x <- zag G M u \<pi> \<sigma>. x \<in> set \<pi>] = u' # [x <- zag G M u'' \<pi> \<sigma>. x \<in> set \<pi>]"
        by simp

      with sucsuc uvs_zag \<open>u'' \<in> set \<pi>\<close> show ?thesis
        by (simp flip: successively_conv_sorted_wrt[OF transp_index_less])
           (metis (no_types, lifting) filter.simps(2) local.Cons successively.simps(3) zag_ConsE zag_increasing_arrival)
    qed
  qed simp
next
  case False
  with assms show ?thesis
    by (simp add: zag_start_wrong_side)
qed

lemma sorted_wrt_arrival_zig:
  assumes "bipartite M (set \<pi>) (set \<sigma>)"
  shows "sorted_wrt (\<lambda>a b. index \<pi> a < index \<pi> b) [x <- zig G M v \<pi> \<sigma>. x \<in> set \<pi>]"
proof (cases "v \<in> set \<sigma>")
  case True
  with assms have "v \<notin> set \<pi>"
    by (auto dest: bipartite_disjointD)

  show ?thesis
  proof (cases "zig G M v \<pi> \<sigma>")
    case (Cons v' uvs)
    then show ?thesis
    proof (cases uvs)
      case (Cons u vus)
      with \<open>zig G M v \<pi> \<sigma> = v' # uvs\<close> have "zig G M v \<pi> \<sigma> = v # zag G M u \<pi> \<sigma>" "{u,v} \<in> M"
        by (metis zig_Cons_zagE zig_then_zag)+

      with \<open>v \<notin> set \<pi>\<close> assms
      show ?thesis
        by (simp add: sorted_wrt_arrival_zag)
    qed simp
  qed simp
next
  case False
  with assms show ?thesis
    by (auto elim!: zig_start_wrong_side[where G = G] dest: bipartite_edgeD)
qed

lemma distinct_zig:
  assumes "bipartite M (set \<pi>) (set \<sigma>)"
  shows "distinct (zig G M v \<pi> \<sigma>)"
proof (cases "v \<in> set \<sigma>")
  case True
  with assms show ?thesis
    by (auto intro!: alt_list_distinct[OF alt_list_zig] intro: sorted_wrt_index_less_distinct sorted_wrt_rank_zig sorted_wrt_arrival_zig dest: bipartite_disjointD)
next
  case False
  with assms show ?thesis
    by (auto elim!: zig_start_wrong_side[where G = G] bipartite_edgeE simp: distinct_length_2_or_more)
qed

lemma
  assumes "M \<subseteq> G"
  shows path_zig: "v \<in> Vs G \<Longrightarrow> path G (zig G M v \<pi> \<sigma>)"
    and path_zag: "u \<in> Vs G \<Longrightarrow> path G (zag G M u \<pi> \<sigma>)"
  using assms
proof (induction G M v \<pi> \<sigma> and G M u \<pi> \<sigma> rule: zig_zag_induct)
  case (zig_matched G M v \<pi> \<sigma> u)
  then have "u \<in> Vs G"
    by (auto dest: edges_are_Vs)
  with zig_matched show ?case
    by (auto simp: zig.simps hd_zag intro!: path_Cons_hd dest: edge_commute)
next
  case (zag G M u \<pi> \<sigma>)
  from zag_casesE[of u M G \<pi> \<sigma>] show ?case
  proof cases
    case has_shifts_to
    then obtain v v' where vs: "{u,v} \<in> M" "shifts_to G M u v v' \<pi> \<sigma>" by blast
    then have "{u,v'} \<in> G" "v' \<in> Vs G"
      unfolding shifts_to_def
      by auto
    with zag vs show ?thesis
      by (auto simp: zag.simps the_match' the_shifts_to hd_zig intro!: path_Cons_hd)
  qed (auto simp: zag.simps the_match' zag)
qed (auto simp: zig.simps zag.simps)

text \<open>
  All but the last vertex of \<^term>\<open>zig\<close> (and \<^term>\<open>zag\<close>) are in the original matching. This
  fact is crucial in proving that there can never be an augmenting path for \<^term>\<open>M::'a graph\<close>.
\<close>
lemma
  shows zig_butlast_subset_M: "v \<in> Vs M \<Longrightarrow> set (butlast (zig G M v \<pi> \<sigma>)) \<subseteq> Vs M"
    and zag_butlast_subset_M: "u \<in> Vs M \<Longrightarrow> set (butlast (zag G M u \<pi> \<sigma>)) \<subseteq> Vs M"
proof (induction G M v \<pi> \<sigma> and G M u \<pi> \<sigma> rule: zig_zag_induct)
  case (zag G M u \<pi> \<sigma>)
  from zag_casesE[of u M G \<pi> \<sigma>]
  show ?case
  proof cases
    case has_shifts_to
    then obtain v v' where shift: "{u,v} \<in> M" "shifts_to G M u v v' \<pi> \<sigma>" by blast
    with zag show ?thesis
      proof (cases "v' \<in> Vs M")
        case True
        from zag.IH[OF shift True] zag.hyps zag.prems shift show ?thesis
          by (simp add: zag.simps the_match' the_shifts_to)
      next
        case False
        with zag.hyps have "zig G M v' \<pi> \<sigma> = [v']"
          by (auto simp: zig.simps)

        with shift zag.hyps zag.prems show ?thesis
          by (simp add: zag.simps the_match' the_shifts_to)
      qed
  next
    case has_no_shifts_to
    then obtain v where "{u,v} \<in> M" "\<nexists>v'. shifts_to G M u v v' \<pi> \<sigma>" by blast
    then show ?thesis
      by (auto simp: zag_no_shifts_to)
  next
    case unmatched
    with zag show ?thesis
      by (simp add: zag.simps)
  qed
next
  case zag_no_matching
  then show ?case
    by (simp add: zag.simps)
qed (auto simp: zig.simps)

text \<open>
  There are several simple equalities regarding removing vertices from the different input parameters
  we need.
\<close>
lemma step_u_not_in_graph:
  "u \<notin> Vs G \<Longrightarrow> step G u \<sigma> M = M"
  by (induction G u \<sigma> M rule: step.induct)
     (auto dest: edges_are_Vs)

lemma online_match'_remove_vertices_graph_remove_vertices_arrival:
  "online_match' (G \<setminus> X) [u <- \<pi>. u \<notin> X] \<sigma> M = online_match' (G \<setminus> X) \<pi> \<sigma> M"
  by (induction "G \<setminus> X" \<pi> \<sigma> M rule: online_match'.induct)
     (auto simp: remove_vertices_not_vs step_u_not_in_graph)

lemma online_match_remove_vertices_graph_remove_vertices_arrival:
  "online_match (G \<setminus> X) [u <- \<pi>. u \<notin> X] \<sigma> = online_match (G \<setminus> X) \<pi> \<sigma>"
  using online_match'_remove_vertices_graph_remove_vertices_arrival
  by blast

lemma online_match'_remove_vertices_not_in_graph_arrival:
  assumes "\<And>x. x \<in> X \<Longrightarrow> x \<notin> Vs G"
  shows "online_match' G [u <- \<pi>. u \<notin> X] \<sigma> M = online_match' G \<pi> \<sigma> M"
  using assms
  by (induction G \<pi> \<sigma> M rule: online_match'.induct)
     (auto simp: step_u_not_in_graph)

lemma online_match_remove_vertices_not_in_graph_arrival:
  assumes "\<And>x. x \<in> X \<Longrightarrow> x \<notin> Vs G"
  shows "online_match G [u <- \<pi>. u \<notin> X] \<sigma> = online_match G \<pi> \<sigma>"
  using assms
  by (auto intro!: online_match'_remove_vertices_not_in_graph_arrival)

lemma step_remove_vertices_not_in_graph:
  assumes "\<And>x. x \<in> X \<Longrightarrow> x \<notin> Vs G"
  shows "step G u [v <- \<sigma>. v \<notin> X] M = step G u \<sigma> M"
  using assms 
  by (induction G u \<sigma> M rule: step.induct) (auto dest: edges_are_Vs_2)

lemma online_match'_remove_vertices_not_in_graph_online_match:
  assumes "\<And>x. x \<in> X \<Longrightarrow> x \<notin> Vs G"
  shows "online_match' G \<pi> [v <- \<sigma>. v \<notin> X] M = online_match' G \<pi> \<sigma> M"
  using assms
  by (induction G \<pi> \<sigma> M rule: online_match'.induct)
     (simp_all add: step_remove_vertices_not_in_graph)

lemma online_match_remove_vertices_not_in_graph_online_match:
  assumes "\<And>x. x \<in> X \<Longrightarrow> x \<notin> Vs G"
  shows "online_match G \<pi> [v <- \<sigma>. v \<notin> X] = online_match G \<pi> \<sigma>"
  using assms
  by (rule online_match'_remove_vertices_not_in_graph_online_match)

lemma step_filter_vertices_in_graph:
  assumes "\<And>x. x \<in> Vs G \<inter> set \<sigma> \<Longrightarrow> P x"
  shows "step G u [v <- \<sigma>. P v] M = step G u \<sigma> M"
  using assms
  by (induction G u \<sigma> M rule: step.induct)
     (auto dest: edges_are_Vs_2)

lemma online_match'_filter_vertices_in_graph_online_match':
  assumes "\<And>x. x \<in> Vs G \<inter> set \<sigma> \<Longrightarrow> P x"
  shows "online_match' G \<pi> [v <- \<sigma>. P v] M = online_match' G \<pi> \<sigma> M"
  using assms
proof (induction G \<pi> \<sigma> M rule: online_match'.induct)
  case (2 G u us \<sigma> M)
  then have "step G u (filter P \<sigma>) M = step G u \<sigma> M"
    by (auto intro!: step_filter_vertices_in_graph)

  with 2 show ?case
    by auto
qed simp

lemma online_match_filter_vertices_in_graph_online_match:
  assumes "\<And>x. x \<in> Vs G \<inter> set \<sigma> \<Longrightarrow> P x"
  shows "online_match G \<pi> [v <- \<sigma>. P v] = online_match G \<pi> \<sigma>"
  using assms
  by (rule online_match'_filter_vertices_in_graph_online_match')

lemma step_remove_vertices_graph_remove_vertices_rank:
  "step (G \<setminus> X) u [v <- \<sigma>. v \<notin> X] M = step (G \<setminus> X) u \<sigma> M"
  by (induction "G \<setminus> X" u \<sigma> M rule: step.induct)
     (simp_all add: remove_vertices_graph_def)

lemma online_match'_remove_vertices_graph_remove_vertices_rank:
  "online_match' (G \<setminus> X) \<pi> [v <- \<sigma>. v \<notin> X] M = online_match' (G \<setminus> X) \<pi> \<sigma> M"
  by (induction "G \<setminus> X" \<pi> \<sigma> M rule: online_match'.induct)
     (simp_all add: step_remove_vertices_graph_remove_vertices_rank)

lemma online_match_remove_vertices_graph_remove_vertices_rank:
  "online_match (G \<setminus> X) \<pi> [v <- \<sigma>. v \<notin> X] = online_match (G \<setminus> X) \<pi> \<sigma>"
  using online_match'_remove_vertices_graph_remove_vertices_rank
  by blast

lemma step_remove_unmatched_vertex_same:
  assumes "x \<notin> Vs (step G u \<sigma> M)"
  shows "step (G \<setminus> {x}) u \<sigma> M = step G u \<sigma> M"
  using assms
proof (induction G u \<sigma> M rule: step.induct)
  case (2 G u v vs M)
  show ?case
  proof (cases "(v \<notin> Vs M \<and> u \<notin> Vs M \<and> {u, v} \<in> G)")
    case True
    with \<open>x \<notin> Vs (step G u (v # vs) M)\<close> show ?thesis
      using in_remove_verticesI vs_member by fastforce
  next
    case False
    with 2 show ?thesis
      using remove_vertices_subgraph'
      by (metis step.simps(2))
  qed
qed simp

text \<open>
  Removing an unmatched vertex does not change the result of \<^term>\<open>online_match\<close>.
\<close>
lemma online_match_remove_unmatched_vertex_same:
  assumes "x \<notin> Vs (online_match' G \<pi> \<sigma> M)"
  shows "online_match' G \<pi> \<sigma> M = online_match' (G \<setminus> {x}) \<pi> \<sigma> M"
  using assms
proof (induction G \<pi> \<sigma> M rule: online_match'.induct)
  case (2 G u us \<sigma> M)
  then have IH_assm: "x \<notin> Vs (online_match' G us \<sigma> (step G u \<sigma> M))" by simp
  then have "x \<notin> Vs (step G u \<sigma> M)"
    by (auto dest: online_match_mono_vs)

  with 2 IH_assm show ?case
    by (simp add: step_remove_unmatched_vertex_same)
qed simp

lemma online_match_filter_vs: "online_match' G [u <- \<pi>. u \<in> Vs G] \<sigma> M = online_match' G \<pi> \<sigma> M"
  by (induction G \<pi> \<sigma> M rule: online_match'.induct)
     (auto simp: step_u_not_in_graph)

lemma shifts_to_mono: 
  assumes "G' \<subseteq> G"
  assumes "shifts_to G' M u v v' \<pi> \<sigma>"
  shows "\<exists>v'. shifts_to G M u v v' \<pi> \<sigma>"
proof -
  consider (same) "shifts_to G M u v v' \<pi> \<sigma>" | (earlier) "\<not>shifts_to G M u v v' \<pi> \<sigma>" by blast
  then show ?thesis
  proof (cases)
    case earlier
    with assms have "\<exists>v''. index \<sigma> v < index \<sigma> v'' \<and> index \<sigma> v'' < index \<sigma> v' \<and> {u,v''} \<in> G \<and> (\<nexists>u'. index \<pi> u' < index \<pi> u \<and> {u',v''} \<in> M)"
      unfolding shifts_to_def by blast

    then obtain v'' where "index \<sigma> v < index \<sigma> v'' \<and> index \<sigma> v'' < index \<sigma> v' \<and> {u,v''} \<in> G \<and> (\<nexists>u'. index \<pi> u' < index \<pi> u \<and> {u',v''} \<in> M)"
      by blast

    then show ?thesis
    proof (induction v'' \<sigma> rule: index_less_induct)
      case (index_less v'')
      then show ?case
      proof (cases "shifts_to G M u v v'' \<pi> \<sigma>")
        case False
        have "v'' \<in> set \<sigma>" 
          using index_less
          by (auto intro: index_less_in_set)

        with False index_less assms(2)
        have "\<exists>v'''. index \<sigma> v < index \<sigma> v''' \<and> index \<sigma> v''' < index \<sigma> v'' \<and> {u,v'''} \<in> G \<and> (\<nexists>u'. index \<pi> u' < index \<pi> u \<and> {u',v'''} \<in> M)"
          unfolding shifts_to_def
          by blast
        
        with index_less show ?thesis by auto
      qed blast
    qed
  qed blast
qed

lemma remove_offline_vertices_before_shifts_to_mono:
  assumes "set \<pi> \<inter> set \<sigma> = {}"
  assumes "X \<subseteq> set \<sigma>"
  assumes "\<forall>x \<in> X. index \<sigma> x < index \<sigma> v"
  assumes "shifts_to (G \<setminus> X) (M \<setminus> X) u v v' \<pi> \<sigma>"
  shows "\<exists>v'. shifts_to G M u v v' \<pi> \<sigma>"
proof -
  consider (same) "shifts_to G M u v v' \<pi> \<sigma>" | (earlier) "\<not>shifts_to G M u v v' \<pi> \<sigma>" by blast
  then show ?thesis
  proof cases
    case earlier
    with assms have "\<exists>v''. index \<sigma> v < index \<sigma> v'' \<and> index \<sigma> v'' < index \<sigma> v' \<and> {u,v''} \<in> G \<and> (\<nexists>u'. index \<pi> u' < index \<pi> u \<and> {u',v''} \<in> M)"
      unfolding shifts_to_def
      by (smt (verit, best) Diff_disjoint Diff_insert_absorb Int_insert_left_if0 disjoint_iff in_remove_verticesI index_less_in_set less_asym' remove_vertices_subgraph')

    then obtain v'' where "index \<sigma> v < index \<sigma> v''" "index \<sigma> v'' < index \<sigma> v'" "{u,v''} \<in> G" "\<nexists>u'. index \<pi> u' < index \<pi> u \<and> {u',v''} \<in> M"
      by blast

    then show ?thesis
    proof (induction v'' \<sigma> rule: index_less_induct)
      case (index_less v'')
      then show ?case
      proof (cases "shifts_to G M u v v'' \<pi> \<sigma>")
        case False
        from \<open>index \<sigma> v'' < index \<sigma> v'\<close> have "v'' \<in> set \<sigma>"
          by (auto intro: index_less_in_set)

        with False index_less assms have "\<exists>v'''. index \<sigma> v < index \<sigma> v''' \<and> index \<sigma> v''' < index \<sigma> v'' \<and> {u,v'''} \<in> G \<and> (\<nexists>u'. index \<pi> u' < index \<pi> u \<and> {u',v'''} \<in> M)"
          unfolding shifts_to_def
          by blast

        with index_less show ?thesis by auto
      qed blast
    qed
  qed blast
qed

lemma remove_online_vertices_before_shifts_to_mono:
  assumes "set \<pi> \<inter> set \<sigma> = {}"
  assumes "X \<subseteq> set \<pi>"
  assumes "matching M"
  assumes "(\<forall>x \<in> X. ((\<exists>v. {x,v} \<in> M) \<longrightarrow> index \<sigma> (THE v. {x,v} \<in> M) < index \<sigma> v))"
  assumes "shifts_to (G \<setminus> X) (M \<setminus> X) u v v' \<pi> \<sigma>"
  shows "\<exists>v'. shifts_to G M u v v' \<pi> \<sigma>"
proof -
  {
    fix u'
    assume "{u',v'} \<in> M"

    with assms have "u' \<notin> X"
      by (auto simp: shifts_to_def the_match')

    with \<open>{u',v'} \<in> M\<close> assms have "{u',v'} \<in> M \<setminus> X"
      by (auto intro!: in_remove_verticesI dest: shifts_to_only_from_input)
  }

  note v'_match_reduced = this

  consider (same) "shifts_to G M u v v' \<pi> \<sigma>" | (earlier) "\<not>shifts_to G M u v v' \<pi> \<sigma>" by blast

  then show ?thesis
  proof cases
    case earlier
    with assms have "\<exists>v''. index \<sigma> v < index \<sigma> v'' \<and> index \<sigma> v'' < index \<sigma> v' \<and> {u,v''} \<in> G \<and> (\<nexists>u'. index \<pi> u' < index \<pi> u \<and> {u',v''} \<in> M)"
      unfolding shifts_to_def
      by (auto dest: v'_match_reduced remove_vertices_subgraph')

    then obtain v'' where "index \<sigma> v < index \<sigma> v''" "index \<sigma> v'' < index \<sigma> v'" "{u,v''} \<in> G" "(\<nexists>u'. index \<pi> u' < index \<pi> u \<and> {u',v''} \<in> M)"
      by blast

    then show ?thesis
    proof (induction v'' \<sigma> rule: index_less_induct)
      case (index_less v'')
      then show ?case
      proof (cases "shifts_to G M u v v'' \<pi> \<sigma>")
        case False
        from \<open>index \<sigma> v'' < index \<sigma> v'\<close> have "v'' \<in> set \<sigma>"
          by (auto intro: index_less_in_set)

        with False index_less assms have "\<exists>v'''. index \<sigma> v < index \<sigma> v''' \<and> index \<sigma> v''' < index \<sigma> v'' \<and> {u,v'''} \<in> G \<and> (\<nexists>u'. index \<pi> u' < index \<pi> u \<and> {u',v'''} \<in> M)"
          unfolding shifts_to_def
          by blast

        with index_less show ?thesis by auto
      qed blast
    qed
  qed blast
qed

lemma no_shifts_to_mono:
  "G' \<subseteq> G \<Longrightarrow> \<nexists>v'. shifts_to G M u v v' \<pi> \<sigma> \<Longrightarrow> \<nexists>v'. shifts_to G' M u v v' \<pi> \<sigma>"
  by (auto dest: shifts_to_mono)
                                    
lemma remove_vertices_no_shifts_to_mono:
  "xs \<subseteq> xs' \<Longrightarrow> \<nexists>v'. shifts_to (G \<setminus> xs) M u v v' \<pi> \<sigma> \<Longrightarrow> \<nexists>u'. shifts_to (G \<setminus> xs') M u v v' \<pi> \<sigma>"
  by (auto dest: remove_vertices_inv_mono'[of xs xs' G] no_shifts_to_mono)

lemma shifts_to_matched_vertex_later_match:
  assumes "shifts_to G M u v v' \<pi> \<sigma>"
  assumes "{u,v} \<in> M"
  assumes "{u',v'} \<in> M"
  assumes "matching M"
  assumes  "u \<in> set \<pi>"
  shows "index \<pi> u < index \<pi> u'"
  using assms
  unfolding shifts_to_def
  by auto (metis doubleton_eq_iff index_eq_index_conv insertI1 linorder_neqE_nat matching_unique_match)

lemma remove_online_vertices_before_shifts_to_same:
  assumes subset_pi: "xs' \<subseteq> set \<pi>"
  assumes subset: "xs \<subseteq> xs'"
  assumes disjoint: "set \<sigma> \<inter> set \<pi> = {}"
  assumes before: "\<forall>x \<in> xs' - xs. index \<pi> x < index \<pi> u"
  assumes shift: "shifts_to (G \<setminus> xs) M u v v' \<pi> \<sigma>"
  shows "shifts_to (G \<setminus> xs') M u v v' \<pi> \<sigma>"
  unfolding shifts_to_def
proof (intro conjI allI impI, goal_cases)
  case 1
  from shift show ?case
    by (simp add: shifts_to_def)

  case 2
  from shift show ?case
    by (simp add: shifts_to_def)


  case 4
  from assms have "{u,v'} \<in> G \<setminus> xs"
    by (simp add: shifts_to_def)

  then have "u \<notin> xs"
    by (auto dest: remove_vertices_not_vs edges_are_Vs)

  with subset_pi disjoint before \<open>v' \<in> set \<sigma>\<close> \<open>{u,v'} \<in> G \<setminus> xs\<close> show ?case
    by (auto dest: remove_vertices_subgraph' intro!: in_remove_verticesI)
next
  case 3
  from shift show ?case
    by (simp add: shifts_to_def)
next
  case 5
  from shift show ?case
    by (simp add: shifts_to_def)
next
  case (6 v'')
  with shift subset show ?case
    unfolding shifts_to_def
    by (auto dest: remove_vertices_inv_mono)
qed

lemma remove_online_vertices_shifts_to_same:
  assumes subset_pi: "X \<subseteq> set \<pi>"
  assumes u_not_X: "u \<notin> X"
  assumes disjoint: "set \<pi> \<inter> set \<sigma> = {}"
  assumes matching: "matching M"
  assumes before: "(\<forall>x \<in> X. ((\<exists>v. {x,v} \<in> M) \<longrightarrow> index \<sigma> (THE v. {x,v} \<in> M) < index \<sigma> v))"
  assumes shift: "shifts_to G M u v v' \<pi> \<sigma>"
  shows "shifts_to (G \<setminus> X) (M \<setminus> X) u v v' \<pi> \<sigma>"
  unfolding shifts_to_def
proof (intro conjI allI impI, goal_cases)
  case 1
  from shift show ?case
    by (simp add: shifts_to_def)
next
  case 2
  from shift show ?case
    by (simp add: shifts_to_def)

  case 4
  from shift have "{u,v'} \<in> G"
    by (simp add: shifts_to_def)

  with u_not_X disjoint subset_pi \<open>v' \<in> set \<sigma>\<close> show ?case
    by (auto intro: in_remove_verticesI)
next
  case 3
  from shift show ?case
    by (simp add: shifts_to_def)
next
  case 5
  from shift show ?case
    by (auto simp: shifts_to_def dest: remove_vertices_subgraph')
next
  case (6 v'')
  with shift consider "{u,v''} \<notin> G" | "(\<exists>u'. index \<pi> u' < index \<pi> u \<and> {u', v''} \<in> M)"
    by (auto simp: shifts_to_def)

  then show ?case
  proof cases
    case 1
    then show ?thesis
      by (auto dest: remove_vertices_subgraph')
  next
    case 2
    then obtain u' where u': "index \<pi> u' < index \<pi> u" "{u',v''} \<in> M" by blast

    with matching have "(THE v. {u',v} \<in> M) = v''"
      by (simp add: the_match')

    with \<open>{u',v''} \<in> M\<close> before 6 have "u' \<notin> X"
      by auto

    with \<open>{u',v''} \<in> M\<close> subset_pi disjoint 6 have "{u',v''} \<in> M \<setminus> X"
      by (auto intro!: in_remove_verticesI dest: index_less_in_set)

    with u' show ?thesis
      by blast
  qed
qed

lemma remove_offline_vertices_before_shifts_to_same:
  assumes subset_sigma: "xs' \<subseteq> set \<sigma>"
  assumes subset: "xs \<subseteq> xs'"
  assumes disjoint: "set \<sigma> \<inter> set \<pi> = {}"
  assumes before: "\<forall>x \<in> xs' - xs. index \<sigma> x < index \<sigma> v"
  assumes shift: "shifts_to (G \<setminus> xs) M u v v' \<pi> \<sigma>"
  shows "shifts_to (G \<setminus> xs') M u v v' \<pi> \<sigma>"
  unfolding shifts_to_def
proof (intro conjI allI impI, goal_cases)
  case 1
  from shift show ?case
    by (simp add: shifts_to_def)

  case 2
  from shift show ?case
    by (simp add: shifts_to_def)

  case 4
  from shift have "{u,v'} \<in> G \<setminus> xs" and v'_after_v: "index \<sigma> v < index \<sigma> v'"
    by (auto simp: shifts_to_def)

  then have "v' \<notin> xs"
    by (auto dest: remove_vertices_not_vs edges_are_Vs_2)

  with before subset subset_sigma disjoint shift v'_after_v \<open>u \<in> set \<pi>\<close> \<open>{u,v'} \<in> G \<setminus> xs\<close> show ?case
    by (auto intro!: in_remove_verticesI dest: remove_vertices_subgraph' order.asym)
next
  case 3
  from shift show ?case
    by (simp add: shifts_to_def)
next
  case 5
  from shift show ?case
    by (simp add: shifts_to_def)
next
  case (6 v'')
  with shift consider "{u,v''} \<notin> G \<setminus> xs" | "\<exists>u'. index \<pi> u' < index \<pi> u \<and> {u',v''} \<in> M"
    by (auto simp: shifts_to_def)

  then show ?case
  proof cases
    case 1
    with subset show ?thesis
      by (auto dest: remove_vertices_inv_mono)
  next
    case 2
    then show ?thesis
      by blast
  qed
qed

lemma remove_offline_vertices_before_shifts_to_same':
  assumes subset_sigma: "X \<subseteq> set \<sigma>"
  assumes disjoint: "set \<pi> \<inter> set \<sigma> = {}"
  assumes before: "\<forall>x \<in> X. index \<sigma> x < index \<sigma> v"
  assumes shift: "shifts_to G M u v v' \<pi> \<sigma>"
  shows "shifts_to (G \<setminus> X) (M \<setminus> X) u v v' \<pi> \<sigma>"
  unfolding shifts_to_def
proof (intro conjI allI impI, goal_cases)
  case 1
  from shift show ?case
    by (simp add: shifts_to_def)

  case 2
  from shift show ?case
    by (simp add: shifts_to_def)

  case 4
  from before shift have "v' \<notin> X"
    by (auto simp: shifts_to_def)

  with shift subset_sigma disjoint \<open>u \<in> set \<pi>\<close> show ?case
    by (auto intro!: in_remove_verticesI simp: shifts_to_def)
next
  case 3
  from shift show ?case
    by (simp add: shifts_to_def)
next
  case 5
  from shift show ?case
    by (auto simp: shifts_to_def dest: remove_vertices_subgraph')
next
  case (6 v'')
  with shift consider "{u,v''} \<notin> G" | "\<exists>u'. index \<pi> u' < index \<pi> u \<and> {u',v''} \<in> M"
    by (auto simp: shifts_to_def)

  then show ?case
  proof cases
    case 1
    then show ?thesis
      by (auto dest: remove_vertices_subgraph')
  next
    case 2
    then obtain u' where u': "{u',v''} \<in> M" "index \<pi> u' < index \<pi> u"
      by blast

    with disjoint subset_sigma before 6 have "{u',v''} \<in> M \<setminus> X"
      by (auto intro!: in_remove_verticesI dest: index_less_in_set)

    with u' show ?thesis
      by blast
  qed
qed

text \<open>
  Removing online vertices (and all their incident edges) which are matched to vertices
  earlier than the starting vertex does not change the alternating path.
\<close>
lemma
  assumes "X \<subseteq> set \<pi>"
  assumes "bipartite M (set \<pi>) (set \<sigma>)"
  assumes "matching M"
  shows 
   remove_online_vertices_zig_zig_eq: 
     "v \<in> set \<sigma> \<Longrightarrow> 
        \<forall>x \<in> X. ((\<exists>v'. {x,v'} \<in> M) \<longrightarrow> index \<sigma> (THE v'. {x,v'} \<in> M) < index \<sigma> v) \<Longrightarrow> 
                  zig (G \<setminus> X) (M \<setminus> X) v \<pi> \<sigma> = zig G M v \<pi> \<sigma>" and
   remove_online_vertices_zag_zag_eq:
     "u \<in> set \<pi> \<Longrightarrow>
     ((\<exists>v. {u,v} \<in> M \<Longrightarrow> 
           \<forall>x \<in> X. ((\<exists>v. {x,v} \<in> M) \<longrightarrow> 
                  index \<sigma> (THE v. {x,v} \<in> M) < index \<sigma> (THE v. {u,v} \<in> M)))) \<Longrightarrow>
         zag (G \<setminus> X) (M \<setminus> X) u \<pi> \<sigma> = zag G M u \<pi> \<sigma>"
  using assms
proof (induction G M v \<pi> \<sigma> and G M u \<pi> \<sigma> rule: zig_zag_induct)
  case (zig_matched G M v \<pi> \<sigma> u)
  then have "u \<in> set \<pi>"
    by (auto dest: bipartite_edgeD)

  from \<open>matching M\<close> have "matching (M \<setminus> X)"
    by (auto intro: matching_remove_vertices)

  from zig_matched.prems \<open>{u,v} \<in> M\<close> \<open>matching M\<close> have "u \<notin> X"
    by (auto simp: the_match')

  from zig_matched.prems have "v \<notin> X"
    by (auto dest!: bipartite_disjointD)

  with \<open>{u,v} \<in> M\<close> \<open>u \<notin> X\<close> have "{u,v} \<in> M \<setminus> X"
    by (auto intro: in_remove_verticesI)

  with zig_matched \<open>matching (M \<setminus> X)\<close> \<open>u \<in> set \<pi>\<close> show ?case
    by (auto simp: zig.simps the_match' the_match)
next
  case (zig_unmatched G M v \<pi> \<sigma>)
  then have "matching (M \<setminus> X)" "\<nexists>u. {u,v} \<in> M \<setminus> X"
    by (auto dest: matching_remove_vertices remove_vertices_subgraph')

  with zig_unmatched show ?case
    by (auto simp: zig.simps)
next
  case (zag G M u \<pi> \<sigma>)

  have uv: "\<And>v. {u,v} \<in> M \<Longrightarrow> {u,v} \<in> M \<setminus> X"
  proof (intro in_remove_verticesI, simp)
    fix v
    assume "{u,v} \<in> M"

    with zag.prems have "u \<notin> X"
      by (auto simp: the_match)

    from zag \<open>{u,v} \<in> M\<close> have "v \<notin> X"
      by (auto dest: bipartite_edgeD)

    with \<open>u \<notin> X\<close> show "{u,v} \<inter> X = {}"
      by blast
  qed

  from \<open>matching M\<close> have "matching (M \<setminus> X)"
    by (auto intro: matching_remove_vertices)

  from zag_casesE[of u M G \<pi> \<sigma>]
  show ?case
  proof cases
    case has_shifts_to
    then obtain v v' where vv': "{u,v} \<in> M" "shifts_to G M u v v' \<pi> \<sigma>" by blast

    then have "{u,v} \<in> M \<setminus> X"
      by (auto intro: uv)

    from vv' have v': "v' \<in> set \<sigma>" "index \<sigma> v < index \<sigma> v'"
      by (auto simp add: shifts_to_def)

    from zag.prems vv' have "u \<notin> X"
      by (auto simp: the_match)

    from zag.prems vv' \<open>u \<notin> X\<close> have "shifts_to (G \<setminus> X) (M \<setminus> X) u v v' \<pi> \<sigma>"
      by (auto intro!: remove_online_vertices_shifts_to_same dest: bipartite_disjointD simp: the_match')

    with zag vv' v' \<open>matching (M \<setminus> X)\<close> \<open>{u,v} \<in> M \<setminus> X\<close> show ?thesis
      by (auto simp: zag.simps the_match the_match' the_shifts_to)
         (meson order.strict_trans)
  next
    case has_no_shifts_to
    then obtain v where v: "{u,v} \<in> M" "\<nexists>v'. shifts_to G M u v v' \<pi> \<sigma>" by blast

    then have "\<nexists>v'. shifts_to (G \<setminus> X) (M \<setminus> X) u v v' \<pi> \<sigma>"
      using has_no_shifts_to remove_online_vertices_before_shifts_to_mono[OF bipartite_disjointD[OF \<open>bipartite M (set \<pi>) (set \<sigma>)\<close>]
          \<open>X \<subseteq> set \<pi>\<close> \<open>matching M\<close> zag(4) _] \<open>matching M\<close>
      by (auto simp: the_match') blast

    with v uv[OF v(1)] \<open>matching M\<close> \<open>matching (M \<setminus> X)\<close> show ?thesis
      by (auto simp: zag.simps the_match' the_shifts_to)
  next
    case unmatched
    with \<open>matching M\<close> \<open>matching (M \<setminus> X)\<close> show ?thesis
      by (auto simp: zag.simps dest: remove_vertices_subgraph')
  qed
qed blast+

text \<open>
  An analogous statement holds for the offline side.
\<close>
lemma
  assumes "X \<subseteq> set \<sigma>"
  assumes "matching M"
  assumes "bipartite M (set \<pi>) (set \<sigma>)"
  shows
    remove_offline_vertices_zig_zig_eq: "v \<in> set \<sigma> \<Longrightarrow> (\<forall>x \<in> X. index \<sigma> x < index \<sigma> v) \<Longrightarrow> zig (G \<setminus> X) (M \<setminus> X) v \<pi> \<sigma> = zig G M v \<pi> \<sigma>" and
    remove_offline_vertices_zag_zag_eq: "u \<in> set \<pi> \<Longrightarrow> (\<exists>v. {u,v} \<in> M \<Longrightarrow> \<forall>x \<in> X. index \<sigma> x < index \<sigma> (THE v. {u,v} \<in> M)) \<Longrightarrow> zag (G \<setminus> X) (M \<setminus> X) u \<pi> \<sigma> = zag G M u \<pi> \<sigma>"
  using assms
proof (induction G M v \<pi> \<sigma> and G M u \<pi> \<sigma> rule: zig_zag_induct)
  case (zig_matched G M v \<pi> \<sigma> u)

  then have "matching (M \<setminus> X)"
    by (simp add: matching_remove_vertices)

  from \<open>v \<in> set \<sigma>\<close> \<open>\<forall>x\<in>X. index \<sigma> x < index \<sigma> v\<close> have "v \<notin> X" by blast

  from \<open>v \<in> set \<sigma>\<close> \<open>{u,v} \<in> M\<close> \<open>bipartite M (set \<pi>) (set \<sigma>)\<close> have "u \<in> set \<pi>"
    unfolding bipartite_def
    by fast

  with \<open>X \<subseteq> set \<sigma>\<close> \<open>bipartite M (set \<pi>) (set \<sigma>)\<close> have "u \<notin> X"
    by (auto dest: bipartite_disjointD)

  with \<open>{u,v} \<in> M\<close> \<open>v \<notin> X\<close> have "{u,v} \<in> M \<setminus> X"
    by (auto intro: in_remove_verticesI)

  with zig_matched \<open>matching (M \<setminus> X)\<close> \<open>{u,v} \<in> M \<setminus> X\<close> \<open>u \<in> set \<pi>\<close> show ?case
    by (auto simp: zig.simps simp: the_match' the_match)
next
  case (zig_unmatched G M v \<pi> \<sigma>)
    then have "\<nexists>u. {u,v} \<in> M \<setminus> X"
      using remove_vertices_subgraph by blast

    with zig_unmatched \<open>matching M\<close> matching_remove_vertices[OF \<open>matching M\<close>] show ?case
      by (auto simp: zig.simps)
next
  case (zag G M u \<pi> \<sigma>)

  then have "u \<notin> X"
    by (auto dest!: bipartite_disjointD)

  have uv: "\<And>v. {u,v} \<in> M \<Longrightarrow> {u,v} \<in> M \<setminus> X"
  proof (rule in_remove_verticesI, simp)
    fix v
    assume "{u,v} \<in> M"

    with zag.prems have "v \<notin> X"
      by (auto simp: the_match')

    with \<open>u \<notin> X\<close> show "{u,v} \<inter> X = {}"
      by blast
  qed

  from \<open>matching M\<close> have "matching (M \<setminus> X)"
    by (simp add: matching_remove_vertices)

  from zag_casesE[of u M G \<pi> \<sigma>]
  show ?case 
  proof cases
    case has_shifts_to
    then obtain v v' where vv': "{u,v} \<in> M" "shifts_to G M u v v' \<pi> \<sigma>" by blast

    then have v': "v' \<in> set \<sigma>" "index \<sigma> v < index \<sigma> v'"
      by (auto simp: shifts_to_def)

    from vv' have "{u,v} \<in> M \<setminus> X"
      by (auto intro: uv)

    from zag.prems vv' have "shifts_to (G \<setminus> X) (M \<setminus> X) u v v' \<pi> \<sigma>"
      by (auto intro!: remove_offline_vertices_before_shifts_to_same' dest: bipartite_disjointD simp: the_match')

    with zag vv' v' \<open>matching (M \<setminus> X)\<close> \<open>{u,v} \<in> M \<setminus> X\<close> \<open>v' \<in> set \<sigma>\<close> show ?thesis
      by (auto simp: zag.simps simp: the_match the_match' the_shifts_to)
         (meson order.strict_trans)
  next
    case has_no_shifts_to
    then obtain v where v: "{u,v} \<in> M" "\<nexists>v'. shifts_to G M u v v' \<pi> \<sigma>" by blast

    with zag.prems have "\<nexists>v'. shifts_to (G \<setminus> X) (M \<setminus> X) u v v' \<pi> \<sigma>"
      using remove_offline_vertices_before_shifts_to_mono[OF bipartite_disjointD[OF \<open>bipartite M (set \<pi>) (set \<sigma>)\<close>]
          \<open>X \<subseteq> set \<sigma>\<close>]
      by (auto simp: the_match') blast
      
    with v uv[OF v(1)] \<open>matching M\<close> \<open>matching (M \<setminus> X)\<close> show ?thesis
      by (auto simp: zag.simps the_match')
  next
    case unmatched
    with \<open>matching M\<close> \<open>matching (M \<setminus> X)\<close> show ?thesis
      by (auto simp: zag.simps dest: remove_vertices_subgraph')
  qed
qed blast+

lemma ranking_matching_shifts_to_reduced_edges:
  assumes rm_M: "ranking_matching G M \<pi> \<sigma>"
  assumes "ranking_matching (G \<setminus> {x}) M' \<sigma> \<pi>"
  assumes "x \<in> set \<sigma>"
  assumes "{u,x} \<in> M"
  assumes "{u,x'} \<in> M'"
  shows "shifts_to G M u x x' \<pi> \<sigma>"
proof -
  have disjoint: "set \<pi> \<inter> set \<sigma> = {}" using rm_M
    by (auto dest: bipartite_disjointD elim!: ranking_matchingE)

  have "u \<in> set \<pi>" using \<open>x \<in> set \<sigma>\<close> \<open>{u,x} \<in> M\<close> rm_M
    by (auto intro: ranking_matching_bipartite_edges')

  have "x \<notin> Vs M'" using \<open>ranking_matching (G \<setminus> {x}) M' \<sigma> \<pi>\<close>
    by (auto dest!: Vs_subset simp: remove_vertices_not_vs elim!: ranking_matchingE)

  then have "x \<noteq> x'"
    using assms(5) insert_commute by auto

  have rm_M': "ranking_matching (G \<setminus> {x}) M' \<pi> \<sigma>"
    using \<open>ranking_matching (G \<setminus> {x}) M' \<sigma> \<pi>\<close> ranking_matching_commute
    by blast

  have "{u,x'} \<in> G"
    using \<open>{u,x'} \<in> M'\<close> rm_M' remove_vertices_subgraph
    by(force elim!: ranking_matchingE)

  have no_u'_for_x': "\<nexists>u'. index \<pi> u' < index \<pi> u \<and> {u',x'} \<in> M"
  proof (rule ccontr, simp)
    assume "\<exists>u'. index \<pi> u' < index \<pi> u \<and> {u',x'} \<in> M"
    then obtain u' where earlier_match: "index \<pi> u' < index \<pi> u" "{u',x'} \<in> M" by blast

    with rm_M rm_M' \<open>{u,x'} \<in> M'\<close> \<open>x \<noteq> x'\<close>
    show False
    proof (induction u' \<pi> arbitrary: u x' rule: index_less_induct)
      case (index_less u')
      then have "{u',x'} \<in> G"
        by (auto elim: ranking_matchingE)

      with disjoint \<open>x \<noteq> x'\<close> \<open>x \<in> set \<sigma>\<close> \<open>index \<pi> u' < index \<pi> u\<close> have "{u',x'} \<in> G \<setminus> {x}"
        by (auto intro!: in_remove_verticesI dest: index_less_in_set)

      with index_less.prems obtain x'' where earlier_match: "{u',x''} \<in> M'" "index \<sigma> x'' < index \<sigma> x'"
        by (auto elim: ranking_matching_earlier_match_offlineE)

      with index_less.prems have "{u',x''} \<in> G"
        using remove_vertices_subgraph'
        by(force elim: ranking_matchingE)


      with earlier_match index_less.prems obtain u'' where u'': "{u'',x''} \<in> M" "index \<pi> u'' < index \<pi> u'"
        by (auto elim: ranking_matching_earlier_match_onlineE)

      then have "x \<noteq> x''"
        using \<open>x \<notin> Vs M'\<close> earlier_match insert_commute by blast

      with u'' index_less.prems \<open>{u',x''} \<in> M'\<close> show ?case
        by (auto intro: index_less.IH)
    qed
  qed

  show ?thesis
    unfolding shifts_to_def
  proof (intro conjI)
    show \<open>u \<in> set \<pi>\<close> using \<open>u \<in> set \<pi>\<close> by blast
  next
    show "x' \<in> set \<sigma>" using \<open>u \<in> set \<pi>\<close> \<open>{u,x'} \<in> G\<close> rm_M disjoint
      by (auto elim: ranking_matchingE elim!: bipartite_edgeE)
  next
    show "index \<sigma> x < index \<sigma> x'"
    proof (rule ccontr)
      assume "\<not> index \<sigma> x < index \<sigma> x'"
      with \<open>x \<noteq> x'\<close> \<open>x \<in> set \<sigma>\<close> index_eq_index_conv have "index \<sigma> x' < index \<sigma> x"
        by fastforce

      with rm_M \<open>{u,x} \<in> M\<close> \<open>{u,x'} \<in> G\<close> have "\<exists>u'. {u',x'} \<in> M \<and> index \<pi> u' < index \<pi> u"
        unfolding ranking_matching_def
        by blast

      with no_u'_for_x' show False by blast
    qed
  next
    show "{u,x'} \<in> G" using \<open>{u,x'} \<in> G\<close> by blast
  next
    show "\<nexists>u'. index \<pi> u' < index \<pi> u \<and> {u',x'} \<in> M" using no_u'_for_x' by blast
  next
    show "\<forall>x''. index \<sigma> x < index \<sigma> x'' \<and> index \<sigma> x'' < index \<sigma> x' \<longrightarrow>
      {u,x''} \<notin> G \<or> (\<exists>u'. index \<pi> u' < index \<pi> u \<and> {u',x''} \<in> M)"
    proof (rule ccontr, simp)
      assume "\<exists>x''. index \<sigma> x < index \<sigma> x'' \<and> index \<sigma> x'' < index \<sigma> x' \<and> {u,x''} \<in> G \<and> (\<forall>u'. index \<pi> u' < index \<pi> u \<longrightarrow> {u',x''} \<notin> M)"
      then obtain x'' where x'': "index \<sigma> x < index \<sigma> x''" "index \<sigma> x'' < index \<sigma> x'" "{u,x''} \<in> G"
        and no_earlier_u_for_x'': "\<forall>u'. index \<pi> u' < index \<pi> u \<longrightarrow> {u',x''} \<notin> M"
        by blast

      then have "{u,x''} \<in> G \<setminus> {x}"
        by (metis \<open>u \<in> set \<pi>\<close> assms(3) disjoint disjoint_iff_not_equal empty_iff in_remove_verticesI insertE neq_iff)

      from \<open>index \<sigma> x < index \<sigma> x''\<close> have "x \<noteq> x''"
        by blast

      with rm_M' \<open>{u,x'} \<in> M'\<close> \<open>{u,x''} \<in> G \<setminus> {x}\<close> \<open>index \<sigma> x'' < index \<sigma> x'\<close>
      obtain u' where "{u',x''} \<in> M'" "index \<pi> u' < index \<pi> u"
        by (auto elim: ranking_matching_earlier_match_onlineE)

      with rm_M' have "{u',x''} \<in> G"
        by (auto elim: ranking_matchingE dest: remove_vertices_subgraph')

      have "u \<noteq> u'"
        using \<open>index \<pi> u' < index \<pi> u\<close> by blast

      from \<open>index \<pi> u' < index \<pi> u\<close> have "u' \<in> set \<pi>"
        using index_less_in_set by fast

      show False
      proof (cases "\<exists>u''. {u'',x''} \<in> M")
        case True
        then obtain u'' where "{u'',x''} \<in> M" by blast
        with x'' \<open>{u,x} \<in> M\<close> \<open>x \<noteq> x''\<close> rm_M have "u'' \<noteq> u"
          by (auto dest: ranking_matching_unique_match)
                                      
        with no_earlier_u_for_x'' \<open>{u'',x''} \<in> M\<close> have "index \<pi> u < index \<pi> u''"
          by (meson \<open>u \<in> set \<pi>\<close> index_eq_index_conv less_linear)

        with \<open>index \<pi> u' < index \<pi> u\<close> have "index \<pi> u' < index \<pi> u''" by linarith

        with \<open>{u'',x''} \<in> M\<close> \<open>{u',x''} \<in> G\<close> rm_M
        obtain x3 where x3: "{u',x3} \<in> M" "index \<sigma> x3 < index \<sigma> x''"
          by (auto elim: ranking_matching_earlier_match_offlineE)

        then have "x3 \<in> set \<sigma>"
          by (auto dest: index_less_in_set)

        with x3 \<open>u' \<in> set \<pi>\<close> \<open>{u',x''} \<in> M'\<close> \<open>index \<pi> u' < index \<pi> u\<close>
        show ?thesis
        proof (induction x3 \<sigma> arbitrary: u' x'' rule: index_less_induct)
          case (index_less s p)

          have "p \<noteq> u" using \<open>index \<pi> p < index \<pi> u\<close> by blast

          have "p \<noteq> x"
            using \<open>x \<in> set \<sigma>\<close> disjoint \<open>p \<in> set \<pi>\<close> by blast

          with \<open>p \<noteq> u\<close> \<open>{u,x} \<in> M\<close> \<open>{p,s} \<in> M\<close> \<open>index \<pi> p < index \<pi> u\<close> rm_M have "s \<noteq> x"
            by (auto dest: ranking_matching_unique_match')

          with index_less \<open>p \<noteq> x\<close> \<open>x \<notin> Vs M'\<close> rm_M have "{p,s} \<in> G \<setminus> {x}"
            by (auto intro!: in_remove_verticesI elim: ranking_matchingE)

          with index_less rm_M' obtain p' where p': "{p',s} \<in> M'" "index \<pi> p' < index \<pi> p"
            by (auto elim: ranking_matching_earlier_match_onlineE)

          with \<open>index \<pi> p < index \<pi> u\<close> have \<open>index \<pi> p' < index \<pi> u\<close> by linarith

          with index_less_in_set have "p' \<in> set \<pi>" by fast

          from p' rm_M' have "{p',s} \<in> G"
            by (auto elim: ranking_matchingE dest: remove_vertices_subgraph')

          with \<open>{p,s} \<in> M\<close> \<open>index \<pi> p' < index \<pi> p\<close> rm_M
          obtain s' where "{p',s'} \<in> M" "index \<sigma> s' < index \<sigma> s"
            by (auto elim: ranking_matching_earlier_match_offlineE)

          with index_less_in_set have "s' \<in> set \<sigma>" by fast

          with index_less \<open>index \<sigma> s' < index \<sigma> s\<close> \<open>{p',s'} \<in> M\<close> \<open>p' \<in> set \<pi>\<close>
            \<open>{p',s} \<in> M'\<close> \<open>index \<pi> p' < index \<pi> u\<close> \<open>s' \<in> set \<sigma>\<close>
          show ?case
            by auto
        qed
      next
        case False
        then show ?thesis
        proof (cases "\<exists>x3. {u',x3} \<in> M")
          case True
          then obtain x3 where x3: "{u',x3} \<in> M" by blast

          with \<open>index \<pi> u' < index \<pi> u\<close> \<open>u \<noteq> u'\<close> rm_M \<open>{u,x} \<in> M\<close> have "x \<noteq> x3"
            by (auto dest: ranking_matching_unique_match')

          consider (before_x'') "index \<sigma> x3 < index \<sigma> x''" | (x'') "index \<sigma> x3 = index \<sigma> x''" | (after_x'') "index \<sigma> x'' < index \<sigma> x3"
            by linarith

          then show ?thesis
          proof cases
            case before_x''
            with x3 \<open>{u',x''} \<in> M'\<close> \<open>x \<noteq> x3\<close> \<open>u' \<in> set \<pi>\<close> \<open>index \<pi> u' < index \<pi> u\<close> show ?thesis
            proof (induction x3 \<sigma> arbitrary: u' x'' rule: index_less_induct)
              case (index_less s p)
              with rm_M \<open>x \<in> set \<sigma>\<close> disjoint have "{p,s} \<in> G \<setminus> {x}"
                by (auto intro: in_remove_verticesI elim: ranking_matchingE)

              with index_less rm_M'
              obtain p' where p': "{p',s} \<in> M'" "index \<pi> p' < index \<pi> p"
                by (auto elim: ranking_matching_earlier_match_onlineE)

              then have "p' \<in> set \<pi>" by (auto intro: index_less_in_set)

              from p' \<open>index \<pi> p < index \<pi> u\<close> have "index \<pi> p' < index \<pi> u" by linarith

              from p' rm_M' have "{p',s} \<in> G"
                by (auto elim: ranking_matchingE dest: remove_vertices_subgraph')

              with rm_M \<open>{p,s} \<in> M\<close> \<open>index \<pi> p' < index \<pi> p\<close>
              obtain s' where "{p',s'} \<in> M" "index \<sigma> s' < index \<sigma> s"
                by (auto elim: ranking_matching_earlier_match_offlineE)

              have "u \<noteq> p'"
                using \<open>index \<pi> p' < index \<pi> p\<close> \<open>index \<pi> p < index \<pi> u\<close> less_asym' by blast

              with rm_M \<open>index \<pi> p' < index \<pi> u\<close> \<open>{u,x} \<in> M\<close> \<open>{p',s'} \<in> M\<close> have "x \<noteq> s'"
                by (auto dest:  ranking_matching_unique_match')

              with index_less \<open>index \<sigma> s' < index \<sigma> s\<close> \<open>{p',s'} \<in> M\<close> \<open>{p',s} \<in> M'\<close> \<open>x \<noteq> s'\<close> \<open>p' \<in> set \<pi>\<close>
                \<open>index \<pi> p' < index \<pi> u\<close>
              show ?case
                by auto
            qed
          next
            case x''
            with False \<open>index \<sigma> x'' < index \<sigma> x'\<close> \<open>{u', x3} \<in> M\<close> show ?thesis
              by (auto dest: index_less_in_set)
          next
            case after_x''
            with \<open>index \<pi> u' < index \<pi> u\<close> \<open>{u', x''} \<in> G\<close> \<open>{u', x3} \<in> M\<close> rm_M no_earlier_u_for_x''
            show ?thesis
              by (auto elim: ranking_matching_earlier_match_onlineE)
          qed
        next
          case False
          with \<open>\<nexists>u''. {u'', x''} \<in> M\<close> rm_M have "u' \<notin> Vs M" "x'' \<notin> Vs M"
            by (auto elim: ranking_matchingE simp: graph_invar_no_edge_no_vertex insert_commute)

          with \<open>{u',x''} \<in> G\<close> rm_M show ?thesis
            by (auto elim: ranking_matchingE dest: maximal_matching_edgeD)
        qed
      qed
    qed
  qed
qed

lemma ranking_matching_shifts_to_original_edges:
  assumes rm_G: "ranking_matching G M \<pi> \<sigma>"
  assumes "ranking_matching (G \<setminus> {x}) M' \<sigma> \<pi>"
  assumes "x \<in> set \<sigma>"
  assumes "{u,x} \<in> M"
  assumes "{u,x'} \<in> M'"
  assumes "{u',x'} \<in> M"
  assumes u_before_u': "index \<pi> u < index \<pi> u'"
  shows "shifts_to (G \<setminus> {x}) M' x' u u' \<sigma> \<pi>"
  using assms
proof -
  have rm_G': "ranking_matching (G \<setminus> {x}) M' \<pi> \<sigma>" using \<open>ranking_matching (G \<setminus> {x}) M' \<sigma> \<pi>\<close>
    by (auto dest: ranking_matching_commute)

  have disjoint: "set \<pi> \<inter> set \<sigma> = {}" using \<open>ranking_matching G M \<pi> \<sigma>\<close>
    by (auto dest: ranking_matchingE bipartite_disjointD)

  have "u \<in> set \<pi>" using u_before_u' by (auto intro: index_less_in_set)
  have "x' \<in> set \<sigma>"
    using assms
    by (auto dest: ranking_matching_shifts_to_reduced_edges shifts_to_only_from_input)

  with rm_G \<open>{u',x'} \<in> M\<close> have "u' \<in> set \<pi>"
    by (auto intro: ranking_matching_bipartite_edges')

  with disjoint \<open>x \<in> set \<sigma>\<close> have "x \<noteq> u'" by blast

  from assms have "x \<noteq> x'"
    by (auto dest: ranking_matching_unique_match')

  have "u' \<noteq> u"
    using u_before_u' by blast

  have "{u',x'} \<in> G"
    using assms
    by (auto dest: ranking_matchingE)

  show ?thesis
    unfolding shifts_to_def
  proof (intro conjI)
    show "x' \<in> set \<sigma>" using \<open>x' \<in> set \<sigma>\<close> by blast
  next
    show "u' \<in> set \<pi>" using \<open>u' \<in> set \<pi>\<close> by blast
  next
    show "index \<pi> u < index \<pi> u'" using assms by blast
  next
    from \<open>x \<noteq> x'\<close> \<open>x \<noteq> u'\<close> \<open>{u',x'} \<in> G\<close> show "{x',u'} \<in> G \<setminus> {x}" 
      by (auto intro!: in_remove_verticesI simp: insert_commute)
  next
    show "\<nexists>x''. index \<sigma> x'' < index \<sigma> x' \<and> {x'',u'} \<in> M'"
    proof (rule ccontr, simp)
      assume "\<exists>x''. index \<sigma> x'' < index \<sigma> x' \<and> {x'',u'} \<in> M'"
      then obtain x'' where "index \<sigma> x'' < index \<sigma> x'" "{u',x''} \<in> M'"
        by (auto simp: insert_commute)

      with \<open>{u',x'} \<in> M\<close> show False
      proof (induction x'' \<sigma> arbitrary: u' x' rule: index_less_induct)
        case (index_less x'')
        with rm_G' have "{u',x''} \<in> G"
          by (auto dest: ranking_matchingE remove_vertices_subgraph')

        with index_less rm_G \<open>{u',x'} \<in> M\<close>
        obtain u'' where u'': "index \<pi> u'' < index \<pi> u'" "{u'',x''} \<in> M"
          by (auto elim: ranking_matching_earlier_match_onlineE)

        with \<open>x \<in> set \<sigma>\<close> disjoint have "u'' \<noteq> x"
          by (auto dest!: index_less_in_set)

        from rm_G' \<open>{u', x''} \<in> M'\<close> have "x \<noteq> x''"
          by (metis in_mono insertI1 insert_commute ranking_matchingE remove_vertices_not_vs vs_member_intro)

        with \<open>{u'',x''} \<in> M\<close> \<open>u'' \<noteq> x\<close> rm_G have "{u'',x''} \<in> G \<setminus> {x}" 
          by (auto intro: in_remove_verticesI dest: ranking_matchingE)

        with index_less u'' rm_G'
        obtain x3 where "index \<sigma> x3 < index \<sigma> x''" "{u'',x3} \<in> M'"                          
          by (auto elim: ranking_matching_earlier_match_offlineE)

        with index_less \<open>{u'',x''} \<in> M\<close> show ?case
          by auto
      qed
    qed
  next
    show "\<forall>u''. index \<pi> u < index \<pi> u'' \<and> index \<pi> u'' < index \<pi> u' \<longrightarrow> 
      {x',u''} \<notin> G \<setminus> {x} \<or> (\<exists>x''. index \<sigma> x'' < index \<sigma> x' \<and> {x'',u''} \<in> M')"
    proof (rule ccontr, simp)
      assume "\<exists>u''. index \<pi> u < index \<pi> u'' \<and> index \<pi> u'' < index \<pi> u' \<and> {x', u''} \<in> G \<setminus> {x} \<and> 
        (\<forall>x''. index \<sigma> x'' < index \<sigma> x' \<longrightarrow> {x'', u''} \<notin> M')"

      then obtain u'' where u'': "index \<pi> u < index \<pi> u''" "index \<pi> u'' < index \<pi> u'" "{u'',x'} \<in> G \<setminus> {x}"
        and no_x''_before_x'_for_u'': "\<nexists>x''. index \<sigma> x'' < index \<sigma> x' \<and> {u'',x''} \<in> M'"
        by (auto simp: insert_commute)

      then have "u \<noteq> u''"
        by blast

      with u'' rm_G \<open>{u',x'} \<in> M\<close>
      obtain x'' where x'': "{u'',x''} \<in> M" "index \<sigma> x'' < index \<sigma> x'"
        by (auto elim: ranking_matching_earlier_match_offlineE dest: remove_vertices_subgraph')

      from rm_G u'' x'' \<open>{u,x} \<in> M\<close> have "x \<noteq> x''"
        by (auto dest: ranking_matching_unique_match')

      from x'' no_x''_before_x'_for_u'' have "{u'',x''} \<notin> M'" by blast

      with x'' \<open>u \<noteq> u''\<close> \<open>x \<noteq> x''\<close> show False
      proof (induction x'' \<sigma> arbitrary: u'' rule: index_less_induct)
        case (index_less x'')
        
        from rm_G disjoint \<open>{u'',x''} \<in> M\<close> \<open>x \<noteq> x''\<close> \<open>index \<sigma> x'' < index \<sigma> x'\<close> \<open>x \<in> set \<sigma>\<close>
        have "{u'',x''} \<in> G \<setminus> {x}"
          by (auto intro!: in_remove_verticesI dest: ranking_matchingE ranking_matching_bipartite_edges' index_less_in_set)

        then show ?case
        proof (cases "\<exists>x3. {u'',x3} \<in> M'")
          case True
          then obtain x3 where "{u'',x3} \<in> M'" by blast
          with \<open>{u'',x''} \<notin> M'\<close> consider (before_x'') "index \<sigma> x3 < index \<sigma> x''" | (after_x'') "index \<sigma> x'' < index \<sigma> x3"
            by (metis index_eq_index_conv index_less_in_set index_less.prems(2) linorder_neqE_nat)

          then show ?thesis
          proof cases
            case before_x''
            from \<open>{u'',x3} \<in> M'\<close> rm_G' have "{u'',x3} \<in> G"
              by (auto dest: ranking_matchingE remove_vertices_subgraph')

            with before_x'' rm_G \<open>{u'',x''} \<in> M\<close> obtain u3 where "{u3,x3} \<in> M" "index \<pi> u3 < index \<pi> u''"
              by (auto elim: ranking_matching_earlier_match_onlineE)

            have "x \<noteq> x3"
              by (metis \<open>{u'', x3} \<in> M'\<close> edges_are_Vs insert_commute ranking_matchingE remove_vertices_not_vs rm_G' singletonI subset_iff)

            with rm_G \<open>{u3,x3} \<in> M\<close> \<open>{u,x} \<in> M\<close> have "u \<noteq> u3"
              by (metis ranking_matching_def the_match')

            from rm_G' \<open>{u'',x3} \<in> M'\<close> \<open>index \<pi> u3 < index \<pi> u''\<close> have "{u3,x3} \<notin> M'"
              by (auto dest: ranking_matching_unique_match')


            with index_less before_x'' \<open>{u3,x3} \<in> M\<close> \<open>u \<noteq> u3\<close> \<open>x \<noteq> x3\<close> show ?thesis 
              by auto
          next
            case after_x''

            with rm_G' \<open>{u'',x3} \<in> M'\<close> \<open>{u'',x''} \<in> G \<setminus> {x}\<close> obtain u3 where "{u3,x''} \<in> M'" "index \<pi> u3 < index \<pi> u''"
              by (auto elim: ranking_matching_earlier_match_onlineE)

            with rm_G' have "{u3,x''} \<in> G" 
              by (auto dest: ranking_matchingE remove_vertices_subgraph')

            with rm_G \<open>{u'',x''} \<in> M\<close> \<open>index \<pi> u3 < index \<pi> u''\<close> obtain x4 where "{u3,x4} \<in> M" "index \<sigma> x4 < index \<sigma> x''"
              by (auto elim: ranking_matching_earlier_match_offlineE)

            with rm_G rm_G' \<open>{u3,x''} \<in> M'\<close> \<open>{u, x} \<in> M\<close> \<open>{u, x'} \<in> M'\<close> \<open>index \<sigma> x'' < index \<sigma> x'\<close> have "x \<noteq> x4"
              by (metis nat_neq_iff ranking_matchingE the_match the_match')

            with rm_G' \<open>{u3,x''} \<in> M'\<close> \<open>{u,x'} \<in> M'\<close> \<open>index \<sigma> x'' < index \<sigma> x'\<close> have "u \<noteq> u3"
              by (auto dest: ranking_matching_unique_match)

            from rm_G' \<open>{u3,x''} \<in> M'\<close> \<open>index \<sigma> x4 < index \<sigma> x''\<close> have "{u3,x4} \<notin> M'"
              by (auto dest: ranking_matching_unique_match)

            with index_less \<open>index \<sigma> x4 < index \<sigma> x''\<close> \<open>{u3,x4} \<in> M\<close> \<open>u \<noteq> u3\<close> \<open>x \<noteq> x4\<close> show ?thesis
              by auto
          qed
        next
          case False
          with rm_G' have "u'' \<notin> Vs M'"
            by (intro graph_invar_no_edge_no_vertex) (auto dest: ranking_matchingE graph_invar_subgraph)

          with rm_G' \<open>{u'',x''} \<in> G \<setminus> {x}\<close> obtain u3 where "{u3,x''} \<in> M'"
            unfolding ranking_matching_def
            by (metis graph_invar_no_edge_no_vertex insert_commute maximal_matching_def ranking_matchingE rm_G')

          with rm_G' \<open>u'' \<notin> Vs M'\<close> \<open>{u'', x''} \<in> G \<setminus> {x}\<close> \<open>index \<sigma> x'' < index \<sigma> x'\<close> have "index \<pi> u3 < index \<pi> u''"
            by (smt (verit, best) edges_are_Vs(1) index_eq_index_conv index_less_in_set linorder_neqE_nat ranking_matching_bipartite_edges' ranking_matching_earlier_match_offlineE)

          from rm_G' \<open>{u3,x''} \<in> M'\<close> have "{u3,x''} \<in> G" 
            by (auto dest: ranking_matchingE remove_vertices_subgraph')

          with rm_G \<open>{u'',x''} \<in> M\<close> \<open>index \<pi> u3 < index \<pi> u''\<close> obtain x3 where x3: "{u3,x3} \<in> M" "index \<sigma> x3 < index \<sigma> x''"
            by (auto elim: ranking_matching_earlier_match_offlineE)

          from rm_G' \<open>{u,x'} \<in> M'\<close> \<open>index \<sigma> x'' < index \<sigma> x'\<close> \<open>{u3, x''} \<in> M'\<close> have "u \<noteq> u3"
            by (auto dest: ranking_matching_unique_match)

          with \<open>{u, x} \<in> M\<close> \<open>{u3,x3} \<in> M\<close> rm_G have "x \<noteq> x3"
            by (auto elim!: ranking_matchingE dest: the_match simp: doubleton_in_matching)

          from rm_G' x3 \<open>{u3,x''} \<in> M'\<close> have "{u3,x3} \<notin> M'"            
            by (auto dest: ranking_matching_unique_match)

          with index_less x3 \<open>u \<noteq> u3\<close> \<open>x \<noteq> x3\<close> show ?thesis
            by auto
        qed
      qed
    qed
  qed
qed

lemma shifts_to_implies_reduced_edge:
  assumes rm_G: "ranking_matching G M \<pi> \<sigma>"
  assumes "ranking_matching (G \<setminus> {x}) M' \<sigma> \<pi>"
  assumes "x \<in> set \<sigma>"
  assumes "{u,x} \<in> M"

  assumes x_to_x': "shifts_to G M u x x' \<pi> \<sigma>"
  shows "{u,x'} \<in> M'"
proof (rule ccontr)
  assume "{u,x'} \<notin> M'"

  from \<open>ranking_matching (G \<setminus> {x}) M' \<sigma> \<pi>\<close> have rm_G': "ranking_matching (G \<setminus> {x}) M' \<pi> \<sigma>" by (auto dest: ranking_matching_commute)

  from x_to_x' rm_G \<open>x \<in> set \<sigma>\<close> have "{u,x'} \<in> G \<setminus> {x}"
    by (auto intro!: in_remove_verticesI simp: shifts_to_def dest: ranking_matchingE bipartite_disjointD)

  with \<open>{u,x'} \<notin> M'\<close> rm_G' consider (u_matched) "\<exists>x''. {u,x''} \<in> M'" | (u_unmatched) "\<exists>u'. {u',x'} \<in> M'"
    by (metis graph_invar_no_edge_no_vertex insert_commute maximal_matching_def ranking_matchingE)

  then show False
  proof cases
    case u_matched
    then obtain x'' where "{u,x''} \<in> M'" by blast
    with rm_G assms \<open>{u,x'} \<notin> M'\<close> x_to_x' show False
      by (auto dest: ranking_matching_shifts_to_reduced_edges shifts_to_inj)
  next
    case u_unmatched
    then obtain u' where "{u',x'} \<in> M'" by blast

    with rm_G' have "{u',x'} \<in> G"
      by (auto dest: ranking_matchingE remove_vertices_subgraph')

    from \<open>{u',x'} \<in> M'\<close> \<open>{u,x'} \<notin> M'\<close> assms rm_G consider (before_u) "index \<pi> u' < index \<pi> u" | (after_u) "index \<pi> u < index \<pi> u'"
      by (metis index_eq_index_conv less_linear ranking_matching_bipartite_edges')
    then show ?thesis
    proof cases
      case before_u
      have "{u',x'} \<in> M"
      proof (rule ccontr)
        assume \<open>{u',x'} \<notin> M\<close>

        with rm_G \<open>{u',x'} \<in> G\<close> consider (u'_matched) "\<exists>x''. {u',x''} \<in> M" | (u'_unmatched) "\<exists>u''. {u'',x'} \<in> M"
          by (metis graph_invar_no_edge_no_vertex insert_commute maximal_matching_def ranking_matchingE)

        then show False
        proof cases
          case u'_matched
          then obtain x'' where "{u',x''} \<in> M" by blast

          with \<open>{u',x'} \<notin> M\<close> x_to_x' consider (before_x') "index \<sigma> x'' < index \<sigma> x'" | (after_x') "index \<sigma> x' < index \<sigma> x''"
            by (metis index_eq_index_conv nat_neq_iff shifts_to_only_from_input(2))

          then show ?thesis
          proof cases
            case before_x'
            with before_u \<open>{u',x''} \<in> M\<close> \<open>{u',x'} \<in> M'\<close> show ?thesis
            proof (induction u' \<pi> arbitrary: x'' x' rule: index_less_induct)
              case (index_less u')

              with rm_G \<open>x \<in> set \<sigma>\<close> have "x \<noteq> u'"
                by (auto elim!: ranking_matchingE dest!: bipartite_disjointD dest: index_less_in_set)

              have "u \<noteq> u'"
                using \<open>index \<pi> u' < index \<pi> u\<close> by blast

              with rm_G \<open>{u,x} \<in> M\<close> \<open>{u',x''} \<in> M\<close> \<open>index \<pi> u' < index \<pi> u\<close> have "x \<noteq> x''"
                by (auto dest: ranking_matching_unique_match')

              with rm_G \<open>{u',x''} \<in> M\<close> \<open>x \<noteq> u'\<close> have "{u',x''} \<in> G \<setminus> {x}"
                by (auto intro: in_remove_verticesI dest: ranking_matchingE)

              with rm_G' \<open>{u',x'} \<in> M'\<close> \<open>index \<sigma> x'' < index \<sigma> x'\<close> obtain u'' where u'': "{u'',x''} \<in> M'" "index \<pi> u'' < index \<pi> u'"
                by (auto elim!: ranking_matching_earlier_match_onlineE)

              with rm_G' have "{u'',x''} \<in> G"
                by (auto dest: ranking_matchingE remove_vertices_subgraph')

              with rm_G \<open>{u',x''} \<in> M\<close> \<open>index \<pi> u'' < index \<pi> u'\<close> obtain x3 where "{u'',x3} \<in> M" "index \<sigma> x3 < index \<sigma> x''"
                by (auto elim: ranking_matching_earlier_match_offlineE)

              with index_less u''
              show ?case 
                by auto
            qed
          next
            case after_x'
            with rm_G before_u x_to_x' \<open>{u',x''} \<in> M\<close> \<open>{u',x'} \<in> G\<close> show ?thesis
              by (auto elim!: ranking_matching_earlier_match_onlineE simp: shifts_to_def)
          qed
        next
          case u'_unmatched
          then obtain u'' where "{u'',x'} \<in> M" by blast

          with \<open>{u',x'} \<notin> M\<close> before_u consider (before_u') "index \<pi> u'' < index \<pi> u'" | (after_u') "index \<pi> u' < index \<pi> u''"
            by (metis index_eq_index_conv index_less_in_set neqE)

          then show ?thesis
          proof cases
            case before_u'
            with \<open>{u'',x'} \<in> M\<close> x_to_x' before_u show ?thesis
              unfolding shifts_to_def
              by auto
          next
            case after_u'
            with \<open>{u'',x'} \<in> M\<close> \<open>{u',x'} \<in> M'\<close> before_u show ?thesis
            proof (induction u'' \<pi> arbitrary: x' u' rule: index_less_induct)
              case (index_less u'')
              with rm_G' have "{u',x'} \<in> G" by (auto dest: ranking_matchingE remove_vertices_subgraph')

              with rm_G index_less  obtain x'' where "{u',x''} \<in> M" "index \<sigma> x'' < index \<sigma> x'"
                by (auto elim: ranking_matching_earlier_match_offlineE)

              from rm_G \<open>index \<pi> u' < index \<pi> u\<close> \<open>x \<in> set \<sigma>\<close>
              have "x \<noteq> u'"
                by (auto dest: ranking_matchingE bipartite_disjointD dest!: index_less_in_set)

              have "u \<noteq> u'"
                using \<open>index \<pi> u' < index \<pi> u\<close> by blast

              with rm_G \<open>{u,x} \<in> M\<close> \<open>index \<pi> u' < index \<pi> u\<close> \<open>{u',x''} \<in> M\<close> have "x \<noteq> x''"
                by (auto dest: ranking_matching_unique_match')

              with rm_G \<open>{u',x''} \<in> M\<close> \<open>x \<noteq> u'\<close> have "{u',x''} \<in> G \<setminus> {x}"
                by (auto intro: in_remove_verticesI dest: ranking_matchingE)

              with rm_G' \<open>{u',x'} \<in> M'\<close> \<open>index \<sigma> x'' < index \<sigma> x'\<close> obtain u3 where "{u3,x''} \<in> M'" "index \<pi> u3 < index \<pi> u'"
                by (auto elim: ranking_matching_earlier_match_onlineE)

              with index_less \<open>{u',x''} \<in> M\<close>
              show ?case
                by fastforce
            qed
          qed
        qed
      qed

      with x_to_x' before_u show ?thesis unfolding shifts_to_def by blast
    next
      case after_u

      with rm_G' \<open>{u,x'} \<in> G \<setminus> {x}\<close> \<open>{u',x'} \<in> M'\<close> obtain x'' where "{u,x''} \<in> M'" "index \<sigma> x'' < index \<sigma> x'"
        by (auto elim: ranking_matching_earlier_match_offlineE)

      with assms rm_G x_to_x' show ?thesis
        by (metis nat_neq_iff ranking_matching_shifts_to_reduced_edges shifts_to_inj)
    qed
  qed
qed

lemma shifts_to_implies_original_edge:
  assumes rm_G: "ranking_matching G M \<pi> \<sigma>"
  assumes "ranking_matching (G \<setminus> {x}) M' \<sigma> \<pi>"
  assumes "x \<in> set \<sigma>"
  assumes "{u,x} \<in> M"
  assumes "{u,x'} \<in> M'"

  assumes u_to_u': "shifts_to (G \<setminus> {x}) M' x' u u' \<sigma> \<pi>"
  shows "{u',x'} \<in> M"
proof (rule ccontr)
  assume "{u',x'} \<notin> M"

  from \<open>ranking_matching (G \<setminus> {x}) M' \<sigma> \<pi>\<close> have rm_G': "ranking_matching (G \<setminus> {x}) M' \<pi> \<sigma>" by (auto dest: ranking_matching_commute)

  from u_to_u' have "{u',x'} \<in> G" "{u',x'} \<in> G \<setminus> {x}"
    unfolding shifts_to_def
    by (auto simp: insert_commute dest: remove_vertices_subgraph')

  from u_to_u' have \<open>index \<pi> u < index \<pi> u'\<close> unfolding shifts_to_def by blast

  with \<open>{u',x'} \<notin> M\<close> \<open>{u', x'} \<in> G\<close> rm_G consider (u'_matched) "\<exists>x''. {u',x''} \<in> M" | (u'_unmatched) "\<exists>u''. {u'',x'} \<in> M"
    by (metis graph_invar_no_edge_no_vertex insert_commute maximal_matching_def ranking_matchingE)

  then show False
  proof cases
    case u'_matched
    then obtain x'' where "{u',x''} \<in> M" by blast

    from u_to_u' have "x \<noteq> u'"
      by (metis edges_are_Vs_2 insertI1 remove_vertices_not_vs shifts_to_def)

    from rm_G \<open>{u,x} \<in> M\<close> \<open>{u',x''} \<in> M\<close> \<open>index \<pi> u < index \<pi> u'\<close> have "x \<noteq> x''"
      by (auto dest: ranking_matching_unique_match')

    with rm_G \<open>{u',x''} \<in> M\<close> \<open>x \<noteq> u'\<close> have "{u',x''} \<in> G \<setminus> {x}"
      by (auto intro: in_remove_verticesI dest: ranking_matchingE)

    from \<open>{u',x''} \<in> M\<close> rm_G u_to_u' \<open>{u',x'} \<notin> M\<close> consider (before_x') "index \<sigma> x'' < index \<sigma> x'" | (after_x') "index \<sigma> x' < index \<sigma> x''"
      by (metis index_eq_index_conv neqE ranking_matching_bipartite_edges shifts_to_only_from_input(2))
    then show ?thesis
    proof cases
      case before_x'

      have "{u',x''} \<in> M'"
      proof (rule ccontr)
        assume "{u',x''} \<notin> M'"
        with rm_G' \<open>{u',x''} \<in> G \<setminus> {x}\<close> consider (u'_matched') "\<exists>x3. {u',x3} \<in> M'" | (u'_unmatched') "\<exists>u''. {u'',x''} \<in> M'"
          by (metis graph_invar_no_edge_no_vertex insert_commute maximal_matching_def ranking_matchingE)

        then show False
        proof cases
          case u'_matched'
          then obtain x3 where "{u',x3} \<in> M'" by blast
          with rm_G u_to_u' \<open>{u', x''} \<in> M\<close> \<open>{u', x''} \<notin> M'\<close> consider (before_x'') "index \<sigma> x3 < index \<sigma> x''" | (after_x'') "index \<sigma> x'' < index \<sigma> x3"
            by (metis index_eq_index_conv less_linear ranking_matching_bipartite_edges shifts_to_only_from_input(2))

          then show ?thesis
          proof cases
            case before_x''
            with \<open>{u', x3} \<in> M'\<close> u_to_u' before_x' show ?thesis
              by (metis (no_types, lifting) insert_commute order.strict_trans shifts_to_def)
          next
            case after_x''
            with \<open>{u',x3} \<in> M'\<close> \<open>{u',x''} \<in> G \<setminus> {x}\<close> \<open>{u',x''} \<in> M\<close> before_x' show ?thesis
            proof (induction u' \<pi> arbitrary: x3 x'' rule: index_less_induct)
              case (index_less u')
              with rm_G' obtain u'' where "{u'',x''} \<in> M'" "index \<pi> u'' < index \<pi> u'"
                by (auto elim: ranking_matching_earlier_match_onlineE)

              with rm_G' have "{u'',x''} \<in> G" by (auto dest: ranking_matchingE remove_vertices_subgraph')

              with rm_G \<open>{u',x''} \<in> M\<close> \<open>index \<pi> u'' < index \<pi> u'\<close> obtain x4 where "{u'',x4} \<in> M" "index \<sigma> x4 < index \<sigma> x''"
                by (auto elim: ranking_matching_earlier_match_offlineE)

              from rm_G \<open>index \<pi> u'' < index \<pi> u'\<close> \<open>x \<in> set \<sigma>\<close> have "x \<noteq> u''"
                by (auto dest: ranking_matchingE bipartite_disjointD dest!: index_less_in_set)

              from rm_G' \<open>{u,x'} \<in> M'\<close> \<open>{u'',x''} \<in> M'\<close> \<open>index \<sigma> x'' < index \<sigma> x'\<close> have "u \<noteq> u''"
                by (auto dest: ranking_matching_unique_match)

              with rm_G \<open>{u'',x4} \<in> M\<close> \<open>{u,x} \<in> M\<close> have "x \<noteq> x4"
                by (auto elim!: ranking_matchingE dest: the_match simp: doubleton_in_matching)

              with rm_G \<open>{u'',x4} \<in> M\<close> \<open>x \<noteq> u''\<close> have "{u'',x4} \<in> G \<setminus> {x}"
                by (auto intro: in_remove_verticesI dest: ranking_matchingE)

              with index_less \<open>index \<pi> u'' < index \<pi> u'\<close> \<open>{u'',x''} \<in> M'\<close> \<open>{u'',x4} \<in> M\<close> \<open>index \<sigma> x4 < index \<sigma> x''\<close>
              show ?case
                by fastforce
            qed
          qed
        next
          case u'_unmatched'
          then obtain u'' where "{u'',x''} \<in> M'" by blast

          with \<open>{u', x''} \<notin> M'\<close> u_to_u' consider (before_u') "index \<pi> u'' < index \<pi> u'" | (after_u') "index \<pi> u' < index \<pi> u''"
            by (metis index_eq_index_conv nat_neq_iff shifts_to_only_from_input(2))

          then show ?thesis
          proof cases
            case before_u'
            with \<open>{u'',x''} \<in> M'\<close> \<open>{u',x''} \<in> M\<close> before_x' show ?thesis
            proof (induction x'' \<sigma> arbitrary: u' u'' rule: index_less_induct)
              case (index_less x'')
              with rm_G' have "{u'',x''} \<in> G" by (auto dest: ranking_matchingE remove_vertices_subgraph')

              with index_less rm_G obtain x3 where x3: "{u'',x3} \<in> M" "index \<sigma> x3 < index \<sigma> x''"
                by (auto elim: ranking_matching_earlier_match_offlineE)

              from rm_G u_to_u' \<open>{u,x} \<in> M\<close> \<open>index \<pi> u'' < index \<pi> u'\<close> \<open>x \<in> set \<sigma>\<close> have "x \<noteq> u''"
                by (auto dest!: shifts_to_only_from_input index_less_in_set  bipartite_disjointD
                         elim: ranking_matchingE)
 
              from rm_G' \<open>{u, x'} \<in> M'\<close> \<open>{u'', x''} \<in> M'\<close> \<open>index \<sigma> x'' < index \<sigma> x'\<close> have "u \<noteq> u''"
                by (auto dest: ranking_matching_unique_match)

              with rm_G \<open>{u, x} \<in> M\<close> \<open>{u'',x3} \<in> M\<close> have "x \<noteq> x3"
                by (auto elim!: ranking_matchingE dest: the_match simp: doubleton_in_matching)

              with rm_G \<open>{u'',x3} \<in> M\<close> \<open>x \<noteq> u''\<close> have "{u'',x3} \<in> G \<setminus> {x}"
                by (auto intro: in_remove_verticesI dest: ranking_matchingE)

              with rm_G' \<open>{u'',x''} \<in> M'\<close> \<open>index \<sigma> x3 < index \<sigma> x''\<close> obtain u3 where "{u3,x3} \<in> M'" "index \<pi> u3 < index \<pi> u''"
                by (auto elim: ranking_matching_earlier_match_onlineE)

              with index_less x3
              show ?case
                by auto
            qed
          next
            case after_u'
            with rm_G' u_to_u' before_x' \<open>{u'', x''} \<in> M'\<close> \<open>{u', x''} \<in> G \<setminus> {x}\<close> show ?thesis
              by (meson dual_order.strict_trans edge_commute ranking_matching_earlier_match_offlineE shifts_to_def)
          qed
        qed
      qed

      with before_x' u_to_u' show ?thesis
        unfolding shifts_to_def
        by (auto simp: insert_commute)
    next
      case after_x'
      with rm_G \<open>{u',x''} \<in> M\<close> \<open>{u',x'} \<in> G\<close> obtain u'' where "{u'',x'} \<in> M" "index \<pi> u'' < index \<pi> u'"
        by (auto elim: ranking_matching_earlier_match_onlineE)

      with rm_G \<open>{u', x'} \<in> G \<setminus> {x}\<close> \<open>{u,x} \<in> M\<close> have "u \<noteq> u''"
        by (metis edges_are_Vs_2 insertI1 ranking_matchingE remove_vertices_not_vs the_match')

      with \<open>index \<pi> u'' < index \<pi> u'\<close> consider (before_u) "index \<pi> u'' < index \<pi> u" | (after_u) "index \<pi> u < index \<pi> u''"
        by (force dest: index_less_in_set)

      then show ?thesis
      proof cases
        case before_u
        with assms \<open>index \<pi> u < index \<pi> u'\<close> \<open>{u'',x'} \<in> M\<close> show ?thesis
          by (meson index_less_in_set not_less_iff_gr_or_eq ranking_matchingE ranking_matching_shifts_to_reduced_edges shifts_to_matched_vertex_later_match)
      next
        case after_u
        with assms \<open>index \<pi> u'' < index \<pi> u'\<close> \<open>{u'', x'} \<in> M\<close> show ?thesis
          by (metis nat_neq_iff ranking_matching_shifts_to_original_edges shifts_to_inj)
      qed
    qed
  next
    case u'_unmatched
    then obtain u'' where "{u'',x'} \<in> M" by blast
    with assms \<open>index \<pi> u < index \<pi> u'\<close> \<open>{u', x'} \<notin> M\<close> show ?thesis
      by (metis index_less_in_set ranking_matchingE ranking_matching_shifts_to_original_edges ranking_matching_shifts_to_reduced_edges shifts_to_inj shifts_to_matched_vertex_later_match)
  qed
qed

text \<open>
  A key lemma for employing the induction hypothesis in the eventual proof of Lemma 2. It shows
  the relationship of the two steps in the cascading (\<^term>\<open>zig\<close> and \<^term>\<open>zag\<close>) on a graph
  \<^term>\<open>G::'a graph\<close> and on \<^term>\<open>G \<setminus> {x}\<close> (the graph where we removed \<^term>\<open>x\<close>).
\<close>
lemma\<^marker>\<open>tag important\<close> ranking_matching_zig_zag_eq:
  assumes "{u,x} \<in> M"
  assumes "x \<in> set \<sigma>"
  assumes "ranking_matching G M \<pi> \<sigma>"
  assumes "ranking_matching (G \<setminus> {x}) M' \<sigma> \<pi>"
  shows "zig (G \<setminus> {x}) M' u \<sigma> \<pi> = zag G M u \<pi> \<sigma>"
  using assms
proof (induction u \<pi> arbitrary: x G M M' rule: index_gt_induct)
  case (index_gt u)
  let ?lhs = "zig (G \<setminus> {x}) M' u \<sigma> \<pi>"
  and ?rhs = "zag G M u \<pi> \<sigma>"

  have matching_M: "matching M" and matching_M': "matching M'" using index_gt
    by (auto dest: ranking_matchingE maximal_matchingD)

  with \<open>{u,x} \<in> M\<close> have x_unique_match: "(THE x. {u,x} \<in> M) = x"
    by (auto simp: insert_commute intro: the_match)

  show ?case
  proof (cases "\<exists>x'. {x',u} \<in> M'")
    case True
    then obtain x' where x'u_in_M': "{x',u} \<in> M'" by blast

    with matching_M' have unique_u_M'_match: "(THE x'. {x',u} \<in> M') = x'"
      by (auto intro: the_match)
 

    with \<open>{x',u} \<in> M'\<close> matching_M' have lhs_Cons: "?lhs = u # zag (G \<setminus> {x}) M' x' \<sigma> \<pi>"
      by (auto simp: zig.simps)
      

    from \<open>{x',u} \<in> M'\<close> matching_M' have unique_x'_M'_match: "(THE u. {x',u} \<in> M') = u"
      by (auto simp: insert_commute intro: the_match)
   

    from \<open>ranking_matching G M \<pi> \<sigma>\<close> \<open>ranking_matching (G \<setminus> {x}) M' \<sigma> \<pi>\<close> \<open>x \<in> set \<sigma>\<close> \<open>{u,x} \<in> M\<close>
      \<open>{x',u} \<in> M'\<close>
    have x_to_x': "shifts_to G M u x x' \<pi> \<sigma>"
      by (auto intro!: ranking_matching_shifts_to_reduced_edges simp: insert_commute)

    then have the_x_to_x': "(THE x'. shifts_to G M u x x' \<pi> \<sigma>) = x'"
      by (simp add: the_shifts_to)

    from x_to_x' have "x \<in> set \<sigma>" "x' \<in> set \<sigma>"
      by (meson shifts_to_only_from_input)+

    from x_to_x' the_x_to_x' x_unique_match \<open>{u,x} \<in> M\<close> matching_M have rhs_Cons: "?rhs = u # zig G M x' \<pi> \<sigma>"
      by (auto simp: zag.simps)


    show ?thesis
    proof (cases "\<exists>u'. {u',x'} \<in> M")
      case True
      then obtain u' where "{u',x'} \<in> M" by blast

      with matching_M have "(THE u'. {u',x'} \<in> M) = u'"
        by (auto intro: the_match)

      with \<open>{u',x'} \<in> M\<close> matching_M have rhs: "zig G M x' \<pi> \<sigma> = x' # zag G M u' \<pi> \<sigma>"
        by (auto simp: zig.simps)

      from \<open>{u,x} \<in> M\<close> \<open>{u',x'} \<in> M\<close> \<open>matching M\<close> x_to_x' have "index \<pi> u < index \<pi> u'"
        by (auto intro!: shifts_to_matched_vertex_later_match simp: shifts_to_def)

      with \<open>ranking_matching G M \<pi> \<sigma>\<close> \<open>ranking_matching (G \<setminus> {x}) M' \<sigma> \<pi>\<close> \<open>x \<in> set \<sigma>\<close> \<open>{u,x} \<in> M\<close>
        \<open>{x',u} \<in> M'\<close> \<open>{u',x'} \<in> M\<close>
      have u_to_u': "shifts_to (G \<setminus> {x}) M' x' u u' \<sigma> \<pi>"
        by (auto intro!: ranking_matching_shifts_to_original_edges simp: insert_commute)

      then have the_u_to_u': "(THE u'. shifts_to (G \<setminus> {x}) M' x' u u' \<sigma> \<pi>) = u'"
        by (simp add: the_shifts_to)

      with u_to_u' \<open>{x',u} \<in> M'\<close> unique_x'_M'_match matching_M' have lhs: "zag (G \<setminus> {x}) M' x' \<sigma> \<pi> = x' # zig (G \<setminus> {x}) M' u' \<sigma> \<pi>"
        by (auto simp: zag.simps)

      from u_to_u' have index_gt_prem: "index \<pi> u < index \<pi> u'"
        unfolding shifts_to_def
        by blast


      from \<open>ranking_matching G M \<pi> \<sigma>\<close> \<open>{u,x} \<in> M\<close> have ranking_matching_reduced: "ranking_matching (G \<setminus> {u,x}) (M \<setminus> {u,x}) \<pi> \<sigma>"
        by (simp add: remove_edge_ranking_matching)

      from x'u_in_M' \<open>{u,x} \<in> M\<close> \<open>ranking_matching (G \<setminus> {x}) M' \<sigma> \<pi>\<close> \<open>{u',x'} \<in> M\<close> \<open>matching M\<close> \<open>index \<pi> u < index \<pi> u'\<close> 
      have "{u', x'} \<in> M \<setminus> {u, x}"
        by (fastforce simp add: remove_edge_matching doubleton_eq_iff elim: ranking_matchingE dest: graph_invar_edgeD)

      have "G \<setminus> {u,x} \<setminus> {x'} = G \<setminus> {x} \<setminus> {u,x'}"
        by (simp add: remove_remove_union insert_commute)

      with \<open>ranking_matching (G \<setminus> {x}) M' \<sigma> \<pi>\<close> \<open>{x',u} \<in> M'\<close> have ranking_matching_reduced': "ranking_matching (G \<setminus> {u,x} \<setminus> {x'}) (M' \<setminus> {u,x'}) \<sigma> \<pi>"
        by (auto dest!: remove_edge_ranking_matching simp: insert_commute)


      from \<open>ranking_matching (G \<setminus> {x}) M' \<sigma> \<pi>\<close> have "x \<notin> Vs M'"
        by (auto elim!: ranking_matchingE dest!: Vs_subset dest: subsetD intro: remove_vertices_not_vs')

      then have "M' \<setminus> {x} = M'"
        by (subst remove_vertices_only_vs)
           (simp add: remove_vertices_empty)

      have "x' \<in> Vs M'"
        by (meson edges_are_Vs(1) x'u_in_M')

      with \<open>x \<notin> Vs M'\<close> have "M' \<setminus> {x,x'} = M' \<setminus> {x'}"
        by (subst remove_vertices_only_vs) simp

      then have "zig (G \<setminus> {u, x} \<setminus> {x'}) (M' \<setminus> {u, x'}) u' \<sigma> \<pi> = zig (G \<setminus> {x} \<setminus> {x'} \<setminus> {u}) (M' \<setminus> {x} \<setminus> {x'} \<setminus> {u}) u' \<sigma> \<pi>"
        by (simp add: insert_commute remove_remove_union)

      also have "\<dots> = zig (G \<setminus> {x} \<setminus> {x'}) (M' \<setminus> {x} \<setminus> {x'}) u' \<sigma> \<pi>"
      proof (rule remove_offline_vertices_zig_zig_eq, goal_cases)
        case 1
        from u_to_u' show ?case
          by (auto dest: shifts_to_only_from_input)
      next
        case 2
        from matching_M' show ?case
          by (auto intro: matching_remove_vertices)
      next
        case 3
        from \<open>ranking_matching (G \<setminus> {x}) M' \<sigma> \<pi>\<close> show ?case
          by (auto dest: ranking_matchingE intro: bipartite_remove_vertices)
      next
        case 4
        from u_to_u' show ?case
          by (auto dest: shifts_to_only_from_input)
      next
        case 5
        from \<open>index \<pi> u < index \<pi> u'\<close> show ?case by blast
      qed

      also have "\<dots> = zig (G \<setminus> {x}) (M' \<setminus> {x}) u' \<sigma> \<pi>"
      proof (rule remove_online_vertices_zig_zig_eq, goal_cases)
        case 1
        from \<open>x' \<in> set \<sigma>\<close> show ?case by blast
      next
        case 2
        from \<open>ranking_matching (G \<setminus> {x}) M' \<sigma> \<pi>\<close> show ?case
          by (auto intro: bipartite_remove_vertices dest: ranking_matchingE)
      next
        case 3
        from matching_M' show ?case
          by (auto dest: ranking_matchingE intro: matching_remove_vertices)
      next
        case 4
        from u_to_u' show ?case
          by (auto dest: shifts_to_only_from_input)
      next
        case 5
        from matching_M' unique_x'_M'_match \<open>index \<pi> u < index \<pi> u'\<close> show ?case
          by (simp add: \<open>M' \<setminus> {x} = M'\<close>)
      qed

      also have "\<dots> = zig (G \<setminus> {x}) M' u' \<sigma> \<pi>"
        by (simp add: \<open>M' \<setminus> {x} = M'\<close>)

      finally have zig_zig_eq: "zig (G \<setminus> {u, x} \<setminus> {x'}) (M' \<setminus> {u, x'}) u' \<sigma> \<pi> = zig (G \<setminus> {x}) M' u' \<sigma> \<pi>" .

      from x_to_x' have "index \<sigma> x < index \<sigma> x'"
        by (simp add: shifts_to_def)

      have "zag (G \<setminus> {u, x}) (M \<setminus> {u, x}) u' \<pi> \<sigma> = zag (G \<setminus> {x} \<setminus> {u}) (M \<setminus> {x} \<setminus> {u}) u' \<pi> \<sigma>"
        by (simp add: remove_remove_union)

      also have "\<dots> = zag (G \<setminus> {x}) (M \<setminus> {x}) u' \<pi> \<sigma>"
      proof (rule remove_online_vertices_zag_zag_eq, goal_cases)
        case 1
        from u_to_u' show ?case
          by (auto dest: shifts_to_only_from_input)
      next
        case 2
        from \<open>ranking_matching G M \<pi> \<sigma>\<close> show ?case
          by (auto dest: ranking_matchingE intro: bipartite_remove_vertices)
      next
        case 3
        from matching_M show ?case
          by (auto intro: matching_remove_vertices)
      next
        case 4
        from u_to_u' show ?case
          by (auto dest: shifts_to_only_from_input)
      next
        case 5
        from matching_M  \<open>{u,x} \<in> M\<close> show ?case
          by (auto simp: remove_vertex_matching' dest: the_match')
      qed
      
      also have  "\<dots> = zag G M u' \<pi> \<sigma>"
      proof (rule remove_offline_vertices_zag_zag_eq, goal_cases)
        case 1
        from \<open>x \<in> set \<sigma>\<close> show ?case by simp
      next
        case 2
        from matching_M show ?case by blast
      next
        case 3
        from \<open>ranking_matching G M \<pi> \<sigma>\<close> show ?case
          by (auto dest: ranking_matchingE)
      next
        case 4
        from u_to_u' show ?case
          by (auto dest: shifts_to_only_from_input)
      next
        case 5
        from matching_M \<open>index \<sigma> x < index \<sigma> x'\<close> \<open>{u', x'} \<in> M\<close> show ?case
          by (auto simp: the_match')
      qed

      finally have zag_zag_eq: "zag (G \<setminus> {u, x}) (M \<setminus> {u, x}) u' \<pi> \<sigma> = zag G M u' \<pi> \<sigma>" .
      
      with zig_zig_eq zag_zag_eq \<open>M' \<setminus> {x} = M'\<close>
        index_gt.IH[OF index_gt_prem \<open>{u',x'} \<in> M \<setminus> {u,x}\<close> \<open>x' \<in> set \<sigma>\<close> ranking_matching_reduced ranking_matching_reduced']
      show ?thesis
        unfolding lhs_Cons rhs_Cons lhs rhs
        by auto
    next
      case False

      with matching_M have rhs: "zig G M x' \<pi> \<sigma> = [x']"
        by (simp add: zig.simps)


      with False x_to_x' \<open>ranking_matching G M \<pi> \<sigma>\<close> \<open>ranking_matching (G \<setminus> {x}) M' \<sigma> \<pi>\<close> \<open>{u,x} \<in> M\<close> \<open>{x',u} \<in> M'\<close> \<open>x \<in> set \<sigma>\<close>
      have "\<nexists>u'. shifts_to (G \<setminus> {x}) M' x' u u' \<sigma> \<pi>"
        by (meson shifts_to_implies_original_edge shifts_to_implies_reduced_edge)

      with \<open>{x',u} \<in> M'\<close> unique_x'_M'_match matching_M' have lhs: "zag (G \<setminus> {x}) M' x' \<sigma> \<pi> = [x']"
        by (auto simp: zag.simps)

      with lhs_Cons rhs_Cons rhs show ?thesis by simp
    qed
  next
    case False
    with matching_M' have lhs: "zig (G \<setminus> {x}) M' u \<sigma> \<pi> = [u]"
      by (simp add: zig.simps)

    with \<open>ranking_matching G M \<pi> \<sigma>\<close> \<open>ranking_matching (G \<setminus> {x}) M' \<sigma> \<pi>\<close> \<open>x \<in> set \<sigma>\<close> \<open>{u,x} \<in> M\<close> False
    have "\<nexists>x'. shifts_to G M u x x' \<pi> \<sigma>"
      by (metis (full_types) insert_commute shifts_to_implies_reduced_edge)

    with x_unique_match \<open>{u,x} \<in> M\<close> matching_M have rhs: "zag G M u \<pi> \<sigma> = [u]"
      by (auto simp: zag.simps)

    show ?thesis
      unfolding lhs rhs by (rule refl)
  qed
qed

text \<open>
  This is the main proof of Lemma 2. It puts most of the material of this section together.
  The lemmas after this just deal with using the interchangeability of the online and offline side
  to obtain the lemma for removing arbitrary (and not just offline) vertices.
\<close>
lemma\<^marker>\<open>tag important\<close> remove_offline_vertex_diff_is_zig:
  assumes "ranking_matching G M \<pi> \<sigma>"
  assumes "ranking_matching (G \<setminus> {x}) M' \<pi> \<sigma>"
  assumes "x \<in> set \<sigma>"
  shows "M \<oplus> M' = set (edges_of_path (zig G M x \<pi> \<sigma>))"
  using assms
proof (induction "card G" arbitrary: G M M' \<pi> \<sigma> x rule: less_induct)
  case less

  then have "matching M" by (auto dest: ranking_matchingE maximal_matchingD)

  consider (matched) "x \<in> Vs M" | (unmatched) "x \<notin> Vs M" by blast
  then show ?case
  proof cases
    case matched
    with \<open>ranking_matching G M \<pi> \<sigma>\<close> obtain u where "{u,x} \<in> M"
      apply(elim ranking_matchingE)
      apply(elim graph_invar_vertex_edgeE') 
      by auto

    with \<open>x \<in> set \<sigma>\<close> \<open>ranking_matching G M \<pi> \<sigma>\<close> have "u \<in> set \<pi>"
      by (auto dest: ranking_matching_bipartite_edges')

    have "{u,x} \<notin> G \<setminus> {x}"
      by (auto dest: edges_are_Vs_2 intro: remove_vertices_not_vs')

    from \<open>{u,x} \<in> M\<close> \<open>ranking_matching G M \<pi> \<sigma>\<close> have rm_Gxu: "ranking_matching (G \<setminus> {x} \<setminus> {u}) (M \<setminus> {u,x}) \<sigma> \<pi>"
      by (auto simp: remove_remove_union intro: remove_edge_ranking_matching ranking_matching_commute)

    interpret graph_abs G
      apply unfold_locales
      using \<open>ranking_matching G M \<pi> \<sigma>\<close> 
      by (auto elim: ranking_matchingE)

    from \<open>{u,x} \<in> M\<close> \<open>{u,x} \<notin> G \<setminus> {x}\<close> \<open>ranking_matching G M \<pi> \<sigma>\<close> finite_E have "card (G \<setminus> {x}) < card G"
      by (auto intro!: psubset_card_mono dest: remove_vertices_subgraph' elim!: ranking_matchingE )


    from \<open>{u,x} \<in> M\<close> \<open>{u,x} \<notin> G \<setminus> {x}\<close> \<open>matching M\<close> \<open>ranking_matching (G \<setminus> {x}) M' \<pi> \<sigma>\<close> have "M \<oplus> M' = insert {u,x} (M' \<oplus> (M \<setminus> {u,x}))"
      by (auto simp: remove_edge_matching symmetric_diff_def dest: ranking_matchingE)
 
    also have "\<dots> = insert {u,x} (set (edges_of_path (zig (G \<setminus> {x}) M' u \<sigma> \<pi>)))"
      using less.hyps[OF \<open>card (G \<setminus> {x}) < card G\<close> ranking_matching_commute[OF less.prems(2)] rm_Gxu \<open>u \<in> set \<pi>\<close>]
      by simp

    also have "\<dots> = insert {u,x} (set (edges_of_path (zag G M u \<pi> \<sigma>)))"
      using ranking_matching_zig_zag_eq[OF \<open>{u,x} \<in> M\<close> \<open>x \<in> set \<sigma>\<close> \<open>ranking_matching G M \<pi> \<sigma>\<close> ranking_matching_commute[OF\<open>ranking_matching (G \<setminus> {x}) M' \<pi> \<sigma>\<close>]]
      by simp

    also from \<open>matching M\<close> have "\<dots> = set (edges_of_path (x # zag G M u \<pi> \<sigma>))"
      by (smt (verit, ccfv_SIG) edges_of_path.elims hd_zag insert_commute list.inject list.sel(1) list.simps(15) list.simps(3) zag_NilE)

    also have "\<dots> = set (edges_of_path (zig G M x \<pi> \<sigma>))"
      using \<open>matching M\<close> \<open>{u,x} \<in> M\<close>
      by (auto simp: zig.simps dest: the_match)

    finally show ?thesis .
  next
    case unmatched
    then have "\<nexists>u. {u,x} \<in> M"
      by (auto dest: edges_are_Vs)

    from unmatched less.prems have "M = M'"
      by (metis ranking_matchingE ranking_matching_online_match ranking_matching_unique online_match_remove_unmatched_vertex_same)

    with less.prems \<open>\<nexists>u. {u,x} \<in> M\<close> \<open>matching M\<close> show ?thesis
      by (auto simp: zig.simps)
  qed
qed

lemma remove_online_vertex_diff_is_zig:
  assumes "ranking_matching G M \<pi> \<sigma>"
  assumes "ranking_matching (G \<setminus> {x}) M' \<pi> \<sigma>"
  assumes "x \<in> set \<pi>"
  shows "M \<oplus> M' = set (edges_of_path (zig G M x \<sigma> \<pi>))"
  using assms
  by (meson ranking_matching_commute remove_offline_vertex_diff_is_zig)

text \<open>
  Depending on if we remove an online or offline vertex, we need to adapt the parameter order
  for \<^term>\<open>zig\<close>.
\<close>
definition remove_vertex_path :: "'a graph \<Rightarrow> 'a graph \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "remove_vertex_path G M x \<pi> \<sigma> = ( if x \<in> set \<sigma> then zig G M x \<pi> \<sigma> else zig G M x \<sigma> \<pi> )"

lemma remove_vertex_path_offline_zig:
  "x \<in> set \<sigma> \<Longrightarrow> remove_vertex_path G M x \<pi> \<sigma> = zig G M x \<pi> \<sigma>"
  unfolding remove_vertex_path_def
  by simp

lemma remove_vertex_path_not_offline_zig:
  "x \<notin> set \<sigma> \<Longrightarrow> remove_vertex_path G M x \<pi> \<sigma> = zig G M x \<sigma> \<pi>"
  unfolding remove_vertex_path_def
  by simp

lemma rev_alt_path_remove_vertex_path: "rev_alt_path M (remove_vertex_path G M x \<pi> \<sigma>)"
  unfolding remove_vertex_path_def
  by (auto intro: rev_alt_path_zig_edges)

text \<open>
  Finally, we state Lemma 2 in multiple steps:
  \<^item> The difference between the matchings is precisely \<^term>\<open>remove_vertex_path G M \<pi> \<sigma>\<close>
\<close>
lemma\<^marker>\<open>tag important\<close> remove_vertex_diff_is_zig:
  assumes "ranking_matching G M \<pi> \<sigma>"
  assumes "ranking_matching (G \<setminus> {x}) M' \<pi> \<sigma>"
  shows "M \<oplus> M' = set (edges_of_path (remove_vertex_path G M x \<pi> \<sigma>))"
  using assms
proof -
  from \<open>ranking_matching G M \<pi> \<sigma>\<close> consider (offline) "x \<in> set \<sigma>" | (online) "x \<in> set \<pi>" | (no_vertex) "x \<notin> Vs G"
    by (auto dest: ranking_matchingE elim: bipartite_edgeE simp: vs_member)

  then show ?thesis
  proof cases
    case offline
    with assms show ?thesis
      by (auto dest: remove_offline_vertex_diff_is_zig simp: remove_vertex_path_offline_zig)
  next
    case online
    with assms have "x \<notin> set \<sigma>"
      by (auto elim!: ranking_matchingE simp: bipartite_def)

    with assms online show ?thesis
      by (auto dest: remove_online_vertex_diff_is_zig simp: remove_vertex_path_not_offline_zig)
  next
    case no_vertex
    with \<open>ranking_matching G M \<pi> \<sigma>\<close> have rm_path: "remove_vertex_path G M x \<pi> \<sigma> = [x]"      
      by (smt (verit, ccfv_SIG) edges_are_Vs_2 ranking_matchingE remove_vertex_path_def subsetD zig.simps(1))

    from no_vertex assms have "M \<oplus> M' = {}"
      by (intro symm_diff_empty ranking_matching_unique)
         (simp_all add: remove_vertex_not_in_graph)

    with rm_path show ?thesis
      by simp
  qed
qed

lemma remove_vertex_diff_is_zigE:
  assumes "ranking_matching G M \<pi> \<sigma>"
  assumes "ranking_matching (G \<setminus> {x}) M' \<pi> \<sigma>"
  obtains "M \<oplus> M' = set (edges_of_path (remove_vertex_path G M x \<pi> \<sigma>))"
  using assms
  by (auto dest: remove_vertex_diff_is_zig)

text \<open>
  \<^item> which is an alternating path
\<close>
lemma remove_vertex_alt_path:
  assumes "ranking_matching G M \<pi> \<sigma>"
  assumes "ranking_matching (G \<setminus> {x}) M' \<pi> \<sigma>"
  shows "alt_path M' (remove_vertex_path G M x \<pi> \<sigma>)"
  using assms
  by (auto intro: rev_alt_path_sym_diff_alt_path[OF remove_vertex_diff_is_zig]
                  rev_alt_path_remove_vertex_path
           dest: ranking_matchingE)

text \<open>
  \<^item> starting at \<^term>\<open>x\<close>
\<close>
lemma remove_vertex_path_hd:
  shows "hd (remove_vertex_path G M x \<pi> \<sigma>) = x"
  unfolding remove_vertex_path_def
  by (auto simp: hd_zig)

text \<open>
  The consequence being that it can never augment the matching on \<^term>\<open>G::'a graph\<close>.
\<close>
lemma remove_vertex_path_not_augmenting:
  shows "matching_augmenting_path M (remove_vertex_path G M x \<pi> \<sigma>) \<Longrightarrow> False"
  unfolding remove_vertex_path_def
  by (auto split: if_splits dest: zig_not_augmenting)

lemma distinct_remove_vertex_path:
  assumes "bipartite M (set \<pi>) (set \<sigma>)"
  shows "distinct (remove_vertex_path G M x \<pi> \<sigma>)"
  using assms
  unfolding remove_vertex_path_def
  by (auto intro: distinct_zig dest: bipartite_commute)

lemma path_remove_vertex_path:
  assumes "M \<subseteq> G"
  assumes "x \<in> Vs G"
  shows "path G (remove_vertex_path G M x \<pi> \<sigma>)"
  using assms
  unfolding remove_vertex_path_def
  by (auto intro: path_zig)

lemma remove_vertex_path_butlast_subset_M:
  assumes "x \<in> Vs M"
  shows "set (butlast (remove_vertex_path G M x \<pi> \<sigma>)) \<subseteq> Vs M"
  using assms
  unfolding remove_vertex_path_def
  by (auto intro!: zig_butlast_subset_M)

text \<open>
  Hence, the matching on \<^term>\<open>G::'a graph\<close> is always at least as big as the one on \<^term>\<open>G \<setminus> {x}\<close>.
  This proof crucially depends on Berge's Lemma, formalized by Abdulaziz~\cite{abdulaziz2019}.
\<close>
lemma remove_vertex_matching_card_leq:
  assumes rm_M: "ranking_matching G M \<pi> \<sigma>"
  assumes rm_M': "ranking_matching (G \<setminus> {x}) M' \<pi> \<sigma>"
  shows "card M' \<le> card M"
proof (cases "x \<in> Vs M")
  case True
  show ?thesis
  proof (rule ccontr)
    assume "\<not> card M' \<le> card M"
    then have lt_matching: "card M < card M'"
      by linarith

    interpret graph_M: graph_abs M'
      apply unfold_locales
      using ranking_matchingE rm_M' by blast

    interpret graph_M': graph_abs M
      apply unfold_locales
      using ranking_matchingE rm_M by blast

    from rm_M rm_M' graph_M.finite_E graph_M'.finite_E  have matchings: "finite M" "finite M'" "matching M" "matching M'"
      by (auto elim!: ranking_matchingE )

    let ?symm_diff = "set (edges_of_path (remove_vertex_path G M x \<pi> \<sigma>))"
    from assms have symm_diff_eq: "M \<oplus> M' = ?symm_diff"
      by (auto intro!: remove_vertex_diff_is_zig)

    with rm_M graph_M.graph graph_M'.graph
    have doubleton_neq_edges: "\<forall>e\<in>(M \<oplus> M'). \<exists>u v. e = {u,v} \<and> u \<noteq> v" "\<forall>e\<in>M. \<exists>u v. e = {u,v} \<and> u \<noteq> v"
      using graph_abs_edges_of_distinct_path[OF distinct_remove_vertex_path]
      by (smt (verit, ccfv_threshold) dblton_graphE ranking_matchingE)+

    with Berge_1[OF matchings lt_matching]
    obtain p where aug_path: "matching_augmenting_path M p" "path (?symm_diff) p" "distinct p"
      by (auto simp: symm_diff_eq)

    then have hd_last_p: "hd p \<noteq> last p" "hd p \<in> set p" "last p \<in> set p"
      by (induction p)
         (auto simp: matching_augmenting_path_def)

    have p_subset_symm_diff: "set p \<subseteq> set (remove_vertex_path G M x \<pi> \<sigma>)"
      by (meson \<open>path (set (edges_of_path (remove_vertex_path G M x \<pi> \<sigma>))) p\<close> edges_of_path_Vs mem_path_Vs subset_iff)

    with hd_last_p aug_path have "last p \<in> Vs M"
      by (auto intro!: subset_butlast_only_one[OF remove_vertex_path_butlast_subset_M[OF True]]
               dest: matching_augmenting_path_feats)

    with aug_path show False
      by (auto dest: matching_augmenting_path_feats)
  qed
next
  case False
  with assms have "M = M'"
    by (metis ranking_matchingE ranking_matching_online_match ranking_matching_unique
              online_match_remove_unmatched_vertex_same)
  then show ?thesis
    by blast
qed

lemma ranking_matching_card_leq_on_perfect_matching_graph:
  assumes "ranking_matching G M \<pi> \<sigma>" "ranking_matching (make_perfect_matching G N) M' \<pi> \<sigma>"
  shows "card M' \<le> card M"
  using assms
proof (induction G N arbitrary: M M' rule: make_perfect_matching.induct)
  case (2 G M)
  then show ?case
    by (meson finite_Vs_then_finite ranking_matchingE)
next
  case (1 G N)
  then show ?case
  proof (cases "\<exists>x. x \<in> Vs G \<and> x \<notin> Vs N")
    case True
    with 1 obtain M'' where M'': "ranking_matching (G \<setminus> {SOME x. x \<in> Vs G \<and> x \<notin> Vs N}) M'' \<pi> \<sigma>"
      by (meson bipartite_remove_vertices ranking_matchingE bipartite_ranking_matchingE)

    with 1 True have *: "card M' \<le> card M''"
      by (auto dest: bipartite_remove_vertices)

    from 1 M'' have "card M'' \<le> card M"
      by (auto intro: remove_vertex_matching_card_leq)

    with * show ?thesis
      by linarith
  qed (use 1 in \<open>auto dest: ranking_matching_unique\<close>)
qed 

text \<open>
  Thus, by repeatedly applying this we finally obtain that the competitive ratio is lower bounded
  by instances where a perfect matching exists.
\<close>
lemma\<^marker>\<open>tag important\<close> ranking_matching_comp_ratio_perfect_matching_lower_bound:
  assumes "ranking_matching G M \<pi> \<sigma>" "ranking_matching (make_perfect_matching G N) M' \<pi> \<sigma>"
  assumes "max_card_matching G N" "max_card_matching (make_perfect_matching G N) N'"
  shows "(real (card M)) / card N \<ge> card M' / card N'"
proof -
  from assms have max_cards_eq: "card N = card N'"
    by (metis make_perfect_matching.simps(2) max_card_matching_def max_card_matching_make_perfect_matching max_card_matchings_same_size ranking_matchingE)

  from assms have "card M' \<le> card M"
    by (auto intro: ranking_matching_card_leq_on_perfect_matching_graph)

  with max_cards_eq show ?thesis
    by (auto simp: divide_right_mono)
qed

subsection \<open>Moving Unmatched Vertices (Lemma 4)\label{sec:ranking-move-to}\<close>
text \<open>
  Lemma 4 from~\cite{birnbaum2008} is required to ensure the independence of probabilistic events
  in the analysis of the randomized version of RANKING. In comparison to Lemma 2, the proof
  is relatively straightforward and follows immediately from the specification
  \<^term>\<open>ranking_matching\<close>.
\<close>
lemma v_unmatched_edge_matched_earlier:
  assumes "u \<in> set \<pi>" 
  assumes "v \<in> set \<sigma>"
  assumes "{u,v} \<in> G"
  assumes "v \<notin> Vs M"
  assumes rm_M: "ranking_matching G M \<pi> \<sigma>"
  assumes rm_M': "ranking_matching G M' \<pi> \<sigma>[v \<mapsto> i]"
  shows "\<exists>v'. {u,v'} \<in> M' \<and> index \<sigma>[v \<mapsto> i] v' \<le> index \<sigma> v"
proof -
  let ?\<sigma>i = "\<sigma>[v \<mapsto> i]"

  from assms obtain w where"{u,w} \<in> M"
    by (meson graph_invar_no_edge_no_vertex ranking_matchingE ranking_matching_maximalE vs_member_intro)

  with assms have "index \<sigma> w < index \<sigma> v"
    by (metis edges_are_Vs_2 index_eq_index_conv linorder_less_linear ranking_matching_earlier_match_onlineE)

  then have "index ?\<sigma>i w \<le> index \<sigma> v"
    by (auto intro: index_less_index_leq_move_to)

  from rm_M \<open>{u,w} \<in> M\<close> have "{u,w} \<in> G"
    by (auto dest: ranking_matchingE)

  have "u \<in> Vs M'"
  proof (rule ccontr)
    assume "u \<notin> Vs M'"
    with rm_M' \<open>{u,w} \<in> G\<close> have "w \<in> Vs M'"
      by (auto elim: ranking_matching_maximalE)

    with rm_M' obtain u' where "{u',w} \<in> M'"
      by (meson edge_commute graph_invar_no_edge_no_vertex ranking_matchingE)

    with rm_M' \<open>{u,w} \<in> G\<close> \<open>u \<in> set \<pi>\<close> \<open>u \<notin> Vs M'\<close> have "index \<pi> u' < index \<pi> u"
      by (metis edges_are_Vs(1) index_eq_index_conv linorder_neqE ranking_matching_earlier_match_offlineE)

    with \<open>{u,w} \<in> M\<close> \<open>{u',w} \<in> M'\<close> show False
    proof (induction u' \<pi> arbitrary: w u rule: index_less_induct)
      case (index_less u')

      with rm_M ranking_matchingE[OF rm_M'] obtain w' where "{u',w'} \<in> M" "index \<sigma> w' < index \<sigma> w"
        by (auto elim: ranking_matching_earlier_match_offlineE)

      with \<open>{u,w} \<in> M\<close> \<open>v \<notin> Vs M\<close> have "index ?\<sigma>i w' < index ?\<sigma>i w"
        by (metis edges_are_Vs_2 move_to_others_less)

      with ranking_matchingE[OF rm_M] rm_M' \<open>{u',w'} \<in> M\<close> \<open>{u',w} \<in> M'\<close>
      obtain u'' where "{u'',w'} \<in> M'" "index \<pi> u'' < index \<pi> u'"
        by (auto elim: ranking_matching_earlier_match_onlineE)

      with index_less \<open>{u',w'} \<in> M\<close> show ?case
        by blast
    qed
  qed

  with rm_M' obtain w' where "{u,w'} \<in> M'"
    apply(elim ranking_matchingE)
    apply(elim graph_invar_vertex_edgeE[of M'])
    by auto

  have "index ?\<sigma>i w' \<le> index ?\<sigma>i w"
  proof (rule ccontr)
    assume "\<not> index ?\<sigma>i w' \<le> index ?\<sigma>i w"
    then have "index ?\<sigma>i w < index ?\<sigma>i w'"
      by linarith

    with ranking_matchingE[OF rm_M] rm_M' \<open>{u,w} \<in> M\<close> \<open>{u,w'} \<in> M'\<close>
    obtain u' where "{u',w} \<in> M'" "index \<pi> u' < index \<pi> u"
      by (auto elim: ranking_matching_earlier_match_onlineE)

    with \<open>{u,w} \<in> M\<close> show False
    \<comment> \<open>can't get @{thm index_less_induct} to work here\<close>
    proof (induction "index ?\<sigma>i w" arbitrary: u w u' rule: less_induct)
      case less
      with rm_M ranking_matchingE[OF rm_M']
      obtain w'' where "{u',w''} \<in> M" "index \<sigma> w'' < index \<sigma> w"
        by (auto elim: ranking_matching_earlier_match_offlineE)

      with \<open>{u,w} \<in> M\<close> \<open>v \<notin> Vs M\<close> have "index ?\<sigma>i w'' < index ?\<sigma>i w"
        by (metis edges_are_Vs_2 move_to_others_less)

      with ranking_matchingE[OF rm_M] rm_M' \<open>{u',w''} \<in> M\<close> \<open>{u',w} \<in> M'\<close>
      obtain u'' where "{u'',w''} \<in> M'" "index \<pi> u'' < index \<pi> u'"
        by (auto elim: ranking_matching_earlier_match_onlineE)

      with less \<open>{u',w''} \<in> M\<close> \<open>index ?\<sigma>i w'' < index ?\<sigma>i w\<close> show ?case
        by blast
    qed
  qed

  with \<open>{u,w'} \<in> M'\<close> \<open>index ?\<sigma>i w \<le> index \<sigma> v\<close> have "{u,w'} \<in> M' \<and> index ?\<sigma>i w' \<le> index \<sigma> v"
    by auto

  then show ?thesis
    by blast
qed

lemma first_rank_always_matched:
  assumes "ranking_matching G M \<pi> \<sigma>"
  assumes "\<sigma> \<noteq> []"
  assumes "\<sigma> ! 0 \<in> Vs G"
  shows "\<sigma> ! 0 \<in> Vs M"
proof -
  let ?v = "\<sigma> ! 0"

  from assms obtain u where uv: "{u,?v} \<in> G"
    apply(elim ranking_matchingE)
    apply(elim graph_invar_vertex_edgeE'[of G])    
    by auto

  with assms have "u \<in> set \<pi>"
    by (auto elim: ranking_matchingE dest: bipartite_edgeD)

  from \<open>\<sigma> \<noteq> []\<close> have index_gt: "\<And>v'. ?v \<noteq> v' \<Longrightarrow> index \<sigma> ?v < index \<sigma> v'"
    by (metis gr0I index_conv_size_if_notin index_first length_greater_0_conv nth_index)

  consider (matched) "?v \<in> Vs M" | (unmatched) "?v \<notin> Vs M" by blast
  then show ?thesis
  proof cases
    case unmatched
    with uv \<open>ranking_matching G M \<pi> \<sigma>\<close> obtain v' where uv': "{u,v'} \<in> M"
      apply(elim ranking_matchingE)
      apply(elim graph_invar_vertex_edgeE[of M])
      by (auto elim!: dest: maximal_matching_edgeD elim!: )

    with unmatched have "index \<sigma> ?v < index \<sigma> v'"
      by (auto intro!: index_gt)

    with uv uv' \<open>ranking_matching G M \<pi> \<sigma>\<close> obtain u' where "{u',?v} \<in> M"
      by (auto elim: ranking_matching_earlier_match_onlineE)

    with unmatched show ?thesis
      by blast
  qed blast
qed

end
