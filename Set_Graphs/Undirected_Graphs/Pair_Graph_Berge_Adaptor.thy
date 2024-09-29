(*Author: Christoph Madlener *)
theory Pair_Graph_Berge_Adaptor
  imports 
    Directed_Set_Graphs.Pair_Graph
    Directed_Set_Graphs.Vwalk
    Directed_Set_Graphs.Component
    Undirected_Set_Graphs.Undirected_Set_Graphs
begin

subsection \<open>Directed-Undirected Graph Adaptor\<close>
text \<open>Here we have adaptors between directed and undirected graphs. These are for the concepts of 
      paths.

      We have used the adaptor to derive some lemmas on undirected graphs from the corresponding 
      lemmas on directed graphs.\<close>
context graph_abs
begin

definition "D \<equiv> {(u,v) | u v. {u, v} \<in> G}"

lemma edge_iff_edge_1:
  "{u, v} \<in> G \<longleftrightarrow> (u, v) \<in> D"
  unfolding D_def by simp

lemma edge_iff_edge_2:
  "{u, v} \<in> G \<longleftrightarrow> (v, u) \<in> D"
  unfolding D_def
  by (auto simp: insert_commute)

lemma edge_iff_edges:
  "{u, v} \<in> G \<longleftrightarrow> (u, v) \<in> D \<and> (v, u) \<in> D"
  using edge_iff_edge_1 edge_iff_edge_2 by blast

lemma symmetric:
  "(u, v) \<in> D \<Longrightarrow> (v, u) \<in> D"
  using edge_iff_edge_2 edge_iff_edges by blast

lemma vwalk_rev_vwalk:
  "Vwalk.vwalk D p \<Longrightarrow> Vwalk.vwalk D (rev p)"
  by (induction rule: vwalk.induct)
     (auto simp add: vwalk_snoc_edge symmetric)

lemma dVs_member:
  "u \<in> dVs D \<longleftrightarrow> (\<exists>v. (u, v) \<in> D)"
  unfolding dVs_def
  by (auto dest: symmetric)

lemma dVs_member':
  "u \<in> dVs D \<longleftrightarrow> (\<exists>v. (v, u) \<in> D)"
  unfolding dVs_def
  by (auto dest: symmetric)

lemma vs_member': "v \<in> Vs G \<longleftrightarrow> (\<exists>u. {u, v} \<in> G)"
  unfolding Vs_def
  using graph
  apply (auto simp: dblton_graph_def)
  by (metis edge_iff_edge_2 emptyE insertE insert_commute) 
                                  
lemma in_Vs_iff_in_dVs:
  "u \<in> Vs G \<longleftrightarrow> u \<in> dVs D"
  by (auto simp: vs_member' edge_iff_edge_1 dVsI dVs_member')

lemma Vs_eq_dVs:
  "Vs G = dVs D"
  using in_Vs_iff_in_dVs by blast

lemma path_iff_vwalk:
  "path G p \<longleftrightarrow> Vwalk.vwalk D p"
  by (induction p rule: edges_of_path.induct)
     (auto simp: in_Vs_iff_in_dVs edge_iff_edges symmetric)

lemma walk_betw_iff_vwalk_bet:
  "walk_betw G u p v \<longleftrightarrow> vwalk_bet D u p v"
  unfolding walk_betw_def vwalk_bet_def
  by (auto simp: path_iff_vwalk)


subsection \<open>Lemmas about relation of \<^term>\<open>edges_of_path\<close> and \<^term>\<open>edges_of_vwalk\<close>\<close>
text \<open>
  \<^term>\<open>edges_of_path\<close> gives a list of doubleton sets, whereas \<^term>\<open>edges_of_vwalk\<close> gives
  a list of pairs. Dealing with the interaction between these doubleton sets and pairs
  is the greatest challenge in this adaptor.
\<close>
fun undirected :: "'a \<times> 'a \<Rightarrow> 'a set" where
  "undirected (u, v) = {u, v}"

lemma undirected_iff:
  "undirected e = {u, v} \<longleftrightarrow> e = (u, v) \<or> e = (v, u)"
  by (fastforce simp add: doubleton_eq_iff elim!: undirected.elims)

lemma
  shows fst_in_undirected: "fst e \<in> undirected e"
  and snd_in_undirected: "snd e \<in> undirected e"
  by (auto intro: prod_cases)

lemma edges_of_path_eq:
  "edges_of_path p = map undirected (edges_of_vwalk p)"
  by (induction p rule: edges_of_path.induct) auto

lemma set_edges_of_path_eq:
  "set (edges_of_path p) = undirected ` set (edges_of_vwalk p)"
  by (simp add: edges_of_path_eq)

lemma edges_of_pathE:
  assumes "{u, v} \<in> set (edges_of_path (p::'a list))"
  obtains "(u, v) \<in> set (edges_of_vwalk p) \<or> (v, u) \<in> set (edges_of_vwalk p)"
  using assms set_edges_of_path_eq undirected_iff 
  by auto

lemma Vs_edges_of_path:
  "Vs (set (edges_of_path (p::'a list))) = dVs (set (edges_of_vwalk p))"
  unfolding Vs_def dVs_def
  by (induction p rule: edges_of_vwalk.induct, auto) blast+

lemma Suc_le_length_le_length_edges_of_vwalk: "Suc i < length p \<Longrightarrow> i < length (edges_of_vwalk p)"
  by (simp add: edges_of_vwalk_length)

lemma edges_of_path_nth:
  \<comment> \<open>Use length of p because of assumptions in following lemmas\<close>
  \<comment> \<open>explicit type needed???\<close>
  "Suc i < length (p::'a list) \<Longrightarrow> edges_of_vwalk p ! i = (u, v) \<Longrightarrow> edges_of_path p ! i = {u, v}"
  by (auto dest: Suc_le_length_le_length_edges_of_vwalk simp: edges_of_path_eq)

lemma edges_of_path_nth_sym:
  "edges_of_vwalk p ! i = (u, v) \<Longrightarrow> Suc i < length (p::'a list) \<Longrightarrow>  edges_of_path p ! i = {u, v}"
  by (auto intro!: edges_of_path_nth)

lemma not_in_edges_of_path_not_in_edges_of_vwalk:
  assumes "{u, v} \<notin> set (edges_of_path (p::'a list))"
  shows "(v, u) \<notin> set (edges_of_vwalk p)"
  using assms
  by (auto simp: set_edges_of_path_eq image_def)

lemma edges_of_vwalk_nonempty_if: "Suc 0 < length p \<Longrightarrow> edges_of_vwalk p \<noteq> []"
  by (induction p rule: edges_of_vwalk.induct) auto

lemma hd_edges_of_path_eq:
  "edges_of_vwalk p \<noteq> [] \<Longrightarrow> hd (edges_of_path p) = undirected (hd (edges_of_vwalk p))"
  by (simp add: edges_of_path_eq hd_map)

lemma last_edges_of_path_eq:
  "edges_of_vwalk p \<noteq> [] \<Longrightarrow> last (edges_of_path p) = undirected (last (edges_of_vwalk p))"
  by (simp add: edges_of_path_eq last_map)


subsection \<open>Obtaining undirected graph lemmas\<close>

thm path_ball_edges
lemma path_ball_edges': "path G p \<Longrightarrow> b \<in> set (edges_of_path p) \<Longrightarrow> b \<in> G"
  by (auto simp: path_iff_vwalk edges_of_path_eq edge_iff_edge_1 dest!: vwalk_ball_edges)

thm edges_of_path_index
lemma edges_of_path_index':
  \<comment> \<open>explicit type required??\<close>
  "Suc i < length (p::'a list) \<Longrightarrow> edges_of_path p ! i = {p ! i, p ! Suc i}"
  by (frule edges_of_vwalk_index)
     (auto simp: edges_of_path_nth)

lemma edges_of_vwalk_for_inner'':
  assumes "i \<noteq> 0" "p ! i = v" "i < length p"
  obtains u where "edges_of_vwalk p ! (i - 1) = (u, v)"
  using assms by (simp add: edges_of_vwalk_index)

thm 
edges_of_path_nth_sym edges_of_path_index'

edges_of_vwalk_for_inner''

\<comment> \<open>TODO\<close>
thm edges_of_path_for_inner
(*lemma "f l = x \<Longrightarrow> P"
  apply safe_step*)
lemma edges_of_path_for_inner':
  assumes "p ! i = v" "Suc i < length (p::'a list)"
  obtains u w where "edges_of_path p ! (i - 1) = {u, v}" "edges_of_path p ! i = {v, w}"
  using assms
  by (cases i) (fastforce simp: edges_of_path_index')+

lemma last_Cons_nonempty: "p \<noteq> [] \<Longrightarrow> Suc 0 < length (last p # p)"
  by simp

thm hd_edges_neq_last
lemma hd_edges_neq_last':
  notes length_greater_0_conv[iff del]
  shows "\<lbrakk>{hd (p::'a list), last p} \<notin> set (edges_of_path p); hd p \<noteq> last p; p \<noteq> []\<rbrakk> \<Longrightarrow> 
         hd (edges_of_path (last p # p)) \<noteq> last (edges_of_path (last p # p))"
  by (induction p) (auto elim: edges_of_path.elims simp: insert_commute)

\<comment> \<open>TODO\<close>
thm distinct_edges_of_vpath
text \<open>This does not hold for directed graphs\<close>
lemma distinct_edges_of_vpath':
  "distinct (p::'a list) \<Longrightarrow> distinct (edges_of_path p)"
  using v_in_edge_in_path
  by (induction p rule: edges_of_path.induct) fastforce+

lemma distinct_edges_of_paths_cons':
  assumes "distinct (edges_of_path (v # p))"
  shows "distinct (edges_of_path (p::'a list))"
  using assms
  by (cases p) (auto)

thm tl_path_is_path
lemma "path G p \<Longrightarrow> path G (tl p)"
  by (simp add: path_iff_vwalk tl_vwalk_is_vwalk)

thm path_concat
lemma path_concat':
  assumes "path G p" "path G q" "q \<noteq> []" "p \<noteq> [] \<Longrightarrow> last p = hd q"
  shows "path G (p @ tl q)"
  using assms
  by (simp add: path_iff_vwalk vwalk_concat)

thm path_append
lemma path_append':
  assumes "path G p1" "path G p2" "p1 \<noteq> [] \<Longrightarrow> p2 \<noteq> [] \<Longrightarrow> {last p1, hd p2} \<in> G"
  shows "path G (p1 @ p2)"
  using assms
  by (simp add: path_iff_vwalk edge_iff_edge_1 append_vwalk)

\<comment> \<open>TODO\<close>
thm edges_of_path_append
lemma edges_of_path_append': "\<exists>ep. edges_of_path ((p::'a list) @ p') = ep @ edges_of_path p'"
  by(auto simp add: edges_of_path_eq intro: exE[OF edges_of_vwalk_append, of p p'])

thm edges_of_path_append_2
lemma edges_of_path_append_2':
  assumes "(p'::'a list) \<noteq> []"
  shows "edges_of_path (p @ p') = edges_of_path (p @ [hd p']) @ edges_of_path p'"
  by (simp add: edges_of_path_eq edges_of_vwalk_append_2[OF assms])

thm edges_of_path_append_3
lemma edges_of_path_append_3:
  "(p::'a list) \<noteq> [] \<Longrightarrow> edges_of_path (p @ p') = edges_of_path p @ edges_of_path (last p # p')"
  by (simp add: edges_of_path_eq edges_of_vwalk_append_3)

thm path_suff
lemma path_suff': "path G (p1 @ p2) \<Longrightarrow> path G p2"
  by (simp add: path_iff_vwalk append_vwalk_suff)

thm path_pref
lemma path_pref': "path G (p1 @ p2) \<Longrightarrow> path G p1"
  by (simp add: path_iff_vwalk append_vwalk_pref)

fun rev_pair :: "('a \<times> 'b) \<Rightarrow> ('b \<times> 'a)" where
  "rev_pair (a, b) = (b, a)"

lemma rev_pair_set: "undirected (u, v) = undirected (rev_pair (u, v))"
  by auto

lemma edges_of_vwalk_append: "edges_of_vwalk (p @ [u, v]) = edges_of_vwalk (p @ [u]) @ [(u, v)]"
  by (induction p rule: edges_of_vwalk.induct) auto

lemma edges_of_vwalk_rev:
  "rev (edges_of_vwalk p) = map rev_pair (edges_of_vwalk (rev p))"
  by (induction p rule: edges_of_vwalk.induct)
     (auto simp: edges_of_vwalk_append)

thm edges_of_path_rev
lemma "rev (edges_of_path (p::'a list)) = edges_of_path (rev p)"
  by (auto simp add: edges_of_path_eq edges_of_vwalk_rev rev_map rev_pair_set)

thm rev_path_is_path
lemma path_rev_path:
  "path G p \<Longrightarrow> path G (rev p)"
  by (simp add: path_iff_vwalk vwalk_rev_vwalk)

thm path_vertex_has_edge
lemma path_vertex_has_edge:
  assumes "length (p::'a list) \<ge> 2" "v \<in> set p"
  obtains e u where "e \<in> set (edges_of_path p)" "v \<in> e"
  using assms
  by (fastforce elim!: vwalk_vertex_has_edge simp: edges_of_path_eq)


thm v_in_edge_in_path
lemma v_in_edge_in_path':
  assumes "{u, v} \<in> set (edges_of_path (p::'a list))"
  shows "u \<in> set p"
  using assms
  by (auto elim!: edges_of_pathE dest: v_in_edge_in_vwalk)

thm v_in_edge_in_path_inj
lemma v_in_edge_in_path_inj':
  assumes "e \<in> set (edges_of_path (p::'a list))"
  obtains u v where "e = {u, v}"
  using assms
  by (auto simp: edges_of_path_eq)

thm v_in_edge_in_path_gen
lemma v_in_edge_in_path_gen':
  assumes "e \<in> set (edges_of_path (p::'a list))" "u \<in> e"
  shows "u \<in> set p"
  using assms
  by (auto simp: edges_of_path_eq dest: v_in_edge_in_vwalk)

thm mem_path_Vs
lemma mem_path_Vs': 
  assumes "path G p" "a\<in>set p" 
  shows "a \<in> Vs G"
  using assms
  by (simp add: path_iff_vwalk in_Vs_iff_in_dVs vwalk_then_in_dVs)


lemma edges_of_vwalk_nonempty_if': "length p \<ge> 2 \<Longrightarrow> edges_of_vwalk p \<noteq> []"
  by (simp add: edges_of_vwalk_nonempty_if)

thm last_v_in_last_e
lemma last_v_in_last_e': 
  assumes "length (p::'a list) \<ge> 2"
  shows "last p \<in> last (edges_of_path p)"
  using assms
  by (auto dest!: edges_of_vwalk_nonempty_if' simp: last_v_snd_last_e[OF assms] edges_of_path_eq last_map snd_in_undirected)

thm hd_v_in_hd_e
lemma hd_v_fst_hd_e':
  assumes "length (p::'a list) \<ge> 2"
  shows "hd p \<in> hd (edges_of_path p)"
  using assms
  by (auto dest!: edges_of_vwalk_nonempty_if' simp: hd_v_fst_hd_e[OF assms] edges_of_path_eq hd_map fst_in_undirected)

thm last_in_edge
lemma last_in_edge':
  assumes "(p::'a list) \<noteq> []"
  shows "\<exists>u. {u, last p} \<in> set (edges_of_path (v # p)) \<and> u \<in> set (v # p)"
  using assms
  by (auto dest!: Vwalk.last_in_edge simp: edges_of_path_eq intro!: rev_image_eqI)


thm edges_of_path_append_subset
lemma edges_of_path_append_subset':
  shows  "set (edges_of_path (p'::'a list)) \<subseteq> set (edges_of_path (p @ p'))"
  unfolding set_edges_of_path_eq
  by (intro image_mono) (simp add: edges_of_vwalk_append_subset)

subsection \<open>Start and end vertices\<close>
thm nonempty_path_walk_between
\<comment> \<open>intro? del? proof by simp though\<close>
declare nonempty_path_walk_between[rule del]
lemma nonempty_path_walk_between'[intro?]:
  assumes "path G p" "p \<noteq> []" "hd p = u" "last p = v"
  shows "walk_betw G u p v"
  using assms
  by (simp add: path_iff_vwalk walk_betw_iff_vwalk_bet nonempty_vwalk_vwalk_bet)

thm walk_nonempty
declare walk_nonempty[simp del]
lemma walk_nonempty':
  assumes "walk_betw G u p v"
  shows [simp]: "p \<noteq> []"
  using assms
  by (simp add: walk_betw_iff_vwalk_bet)



lemma walk_between_nonempty_path'[elim]:
  assumes "walk_betw G u p v"
  shows "path G p" "p \<noteq> []" "hd p = u" "last p = v"
  using assms
  by (simp_all add: walk_betw_iff_vwalk_bet path_iff_vwalk vwalk_bet_nonempty_vwalk)

thm walk_reflexive
lemma walk_reflexive':
  assumes "w \<in> Vs G"
  shows "walk_betw G w [w] w"
  using assms
  by (simp add: in_Vs_iff_in_dVs walk_betw_iff_vwalk_bet vwalk_bet_reflexive)

thm walk_symmetric
lemma walk_symmetric':
  assumes "walk_betw G u p v"
  shows "walk_betw G v (rev p) u"
  using assms
  unfolding walk_betw_iff_vwalk_bet vwalk_bet_def
  by (auto simp: vwalk_rev_vwalk hd_rev last_rev)

thm walk_transitive
lemma walk_transitive':
  assumes "walk_betw G u p v" "walk_betw G v q w"
  shows "walk_betw G u (p @ tl q) w"
  using assms 
  unfolding walk_betw_iff_vwalk_bet
  by (simp add: vwalk_bet_transitive)
end

locale subset_graph =
  graph_abs +
  fixes G' :: "'a set set"
  assumes subgraph: "G' \<subseteq> G"
begin

sublocale subgraph: graph_abs G'
  apply standard
  using graph subgraph
  by (auto simp: Vs_def Union_mono rev_finite_subset)

lemma D_subset: "subgraph.D \<subseteq> D"
  unfolding subgraph.D_def D_def
  using subgraph by fastforce

thm Vs_subset
lemma Vs_subset':
  shows "Vs G' \<subseteq> Vs G"
  using D_subset
  by (simp add: Vs_eq_dVs subgraph.Vs_eq_dVs dVs_subset)

thm path_subset
lemma path_subset':
  assumes "path G' p"
  shows "path G p"
  using assms D_subset
  by (auto simp add: path_iff_vwalk subgraph.path_iff_vwalk intro: vwalk_subgraph)

end

locale path_graph = graph_abs +
  fixes p :: "'a list"
  assumes p_path: "path G p"
begin

definition "edge_set \<equiv> set (edges_of_path p)"

text \<open>this also proves @{thm path_edges_subset}\<close>
sublocale path_induced: subset_graph G edge_set
  apply standard
  unfolding edge_set_def
  using p_path
  by (auto simp: path_ball_edges')

lemma in_edges_of_vwalk_in_D: "(u, v) \<in> set (edges_of_vwalk p) \<Longrightarrow> (u, v) \<in> path_induced.subgraph.D"
  by (simp flip: path_induced.subgraph.edge_iff_edge_1)
     (force simp add: edge_set_def edges_of_path_eq image_iff)

lemma set_edges_of_vwalk_subset_D: "set (edges_of_vwalk p) \<subseteq> path_induced.subgraph.D"
  using in_edges_of_vwalk_in_D by auto

thm path_edges_of_path_refl
lemma path_edges_of_path_refl':
  "length p \<ge> 2 \<Longrightarrow> path edge_set p"
  by (auto dest!: vwalk_edges_of_vwalk_refl 
           intro: vwalk_subgraph[simplified subgraph_def, OF _ set_edges_of_vwalk_subset_D] 
           simp: path_induced.subgraph.path_iff_vwalk )

thm edges_of_path_Vs
lemma edges_of_path_Vs': "Vs edge_set \<subseteq> set p"
  unfolding edge_set_def
  by (simp add: path_induced.subgraph.Vs_edges_of_path edges_of_vwalk_dVs)
end


end