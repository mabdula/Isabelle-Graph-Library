(*Author: Christoph Madlener *)
theory Pair_Graph_Berge_Adaptor
  imports 
    Directed_Set_Graphs.Pair_Graph
    Directed_Set_Graphs.Vwalk
    Directed_Set_Graphs.Component
    Undirected_Set_Graphs.Undirected_Set_Graphs
    Paths Cycles
begin

subsection \<open>Directed-Undirected Graph Adaptor\<close>
text \<open>Here we have adaptors between directed and undirected graphs. These are for the concepts of 
      paths.

      We have used the adaptor to derive some lemmas on undirected graphs from the corresponding 
      lemmas on directed graphs.\<close>
context graph_abs
begin

definition "D = {(u,v) | u v. {u, v} \<in> G}"

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

text \<open>We also show equivalence between (existence of) cycles in undirected and directed graphs\<close>

(* Note: for correctness of this function, need to assume that u is really the "head" of the path *)
(* TODO later: should this function go somewhere else? *)
fun epath_to_awalk :: "'a \<Rightarrow> 'a set list \<Rightarrow> ('a \<times> 'a) list" where
  "epath_to_awalk u [] = []" |
  "epath_to_awalk u (e # p) = 
    (let v' = (THE v. v \<in> e - {u}) in (u, v') # epath_to_awalk v' p)"

lemma no_self_loops_1:
  "(x, x) \<notin> D"
  unfolding D_def using graph by fastforce

lemma no_self_loops_2:
  "(x, y) \<in> D \<Longrightarrow> x \<noteq> y"
  unfolding D_def using graph by fastforce


lemma awalk_imp_epath:
  "awalk D u p v \<Longrightarrow> epath G u (map undirected p) v"
  apply (induction p arbitrary: u v)
  apply fastforce
  by (metis (no_types, lifting) awalk_Cons_iff edge_iff_edge_1 epath.simps(2) list.simps(9) no_self_loops_1 prod.collapse undirected.simps)

lemma awalk_distinct_imp_epath_distinct:
  "awalk D u p v \<Longrightarrow> distinct (tl (awalk_verts u p)) \<Longrightarrow> distinct (butlast (awalk_verts u p)) \<Longrightarrow>
     length p > 2 \<Longrightarrow> distinct (map undirected p)"
proof (induction p arbitrary: u v)
  case Nil
  then show ?case by fastforce
next
  case (Cons e p)
  then consider (a) "length (e # p) = 3" | (b) "length (e # p) > 3" by force
  then show ?case
  proof (cases)
    case a
    then have "length p = 2" by simp
    then have "p = [(fst (p ! 0), snd (p ! 0)), (fst (p ! 1), snd (p ! 1))]"
      by (metis (mono_tags, lifting) One_nat_def Suc_eq_plus1 less_2_cases_iff list.size(3) list.size(4)
        nat_1_add_1 nth_Cons_0 nth_Cons_Suc nth_equalityI prod.collapse)
    then have "e # p = [(fst e, snd e), (fst (p ! 0), snd (p ! 0)), (fst (p ! 1), snd (p ! 1))]"
      by simp

    from \<open>e # p = [(fst e, snd e), (fst (p ! 0), snd (p ! 0)), (fst (p ! 1), snd (p ! 1))]\<close>
      have "e # p = [(u, snd e), (snd e, snd (p ! 0)), (snd (p ! 0), v)]"
      by (metis (no_types, lifting) Cons.prems(1) awalk_Cons_iff awalk_ends prod.collapse)
    then have "awalk_verts u (e # p) = [u, snd e, snd (p ! 0), v]"
      by (metis awalk_verts.simps(1) awalk_verts.simps(2))
    with \<open>distinct (tl (awalk_verts u (e # p)))\<close>
      have "distinct [snd e, snd (p ! 0), v]" by simp

    from \<open>e # p = [(u, snd e), (snd e, snd (p ! 0)), (snd (p ! 0), v)]\<close>
      have "map undirected (e # p) = [{u, snd e}, {snd e, snd (p ! 0)}, {snd (p ! 0), v}]"
      by (metis (no_types, lifting) list.simps(8) list.simps(9) undirected.simps)
    with \<open>distinct [snd e, snd (p ! 0), v]\<close>
      show ?thesis 
      using Cons.prems(3) \<open>awalk_verts u (e # p) = [u, snd e, snd (p ! 0), v]\<close> butlast.simps(2)
      distinct_length_2_or_more by auto
  next
    case b
    then have "length p > 2" by auto

    obtain x y where e: "e = (x, y)" by fastforce
    from \<open>awalk D u (e # p) v\<close>
      have "awalk D y p v"
      by (simp add: \<open>e = (x, y)\<close> awalk_Cons_iff)
  
    from awalk_verts_cons \<open>awalk D u (e # p) v\<close> e 
      have "tl (awalk_verts u ([(x, y)] @ p)) = [y] @ tl (awalk_verts u p)" by force
    with \<open>distinct (tl (awalk_verts u (e # p)))\<close> e
      have "distinct (tl (awalk_verts y p))" by auto
    with \<open>distinct (butlast (awalk_verts u (e # p)))\<close> e
      have "distinct (butlast (awalk_verts y p))" by auto
  
    have "tl (awalk_verts u ([(x, y)] @ p)) = awalk_verts y p" by auto

  
    from \<open>awalk D u (e # p) v\<close> have "cas u (e # p) v" unfolding awalk_def by blast
  
    have "(x, y) \<notin> set p"
    proof (rule ccontr, goal_cases)
      case 1
      then obtain p1 p2 where "p = p1 @ [(x, y)] @ p2"
        by (metis append_Cons append_Nil in_set_conv_decomp_first)
  
      with e awalk_verts_conv'[of "u" "e # p", OF \<open>cas u (e # p) v\<close>]
        have "tl (awalk_verts u (e # p)) = map snd ([(x, y)] @ p1 @ [(x, y)] @ p2)"
        by auto
      then have 
        "tl (awalk_verts u (e # p)) = [y] @ (map snd p1) @ [y] @ (map snd p2)" by simp
      with \<open>distinct (tl (awalk_verts u (e # p)))\<close>
        show ?case by simp
    qed
    have "(y, x) \<notin> set p"
    proof (rule ccontr, goal_cases)
      case 1
      then obtain p1 p2 where "p = p1 @ [(y, x)] @ p2"
        by (metis append_Cons append_Nil in_set_conv_decomp_first)
    
      from \<open>awalk D u (e # p) v\<close> have "cas u (e # p) v" unfolding awalk_def by blast
  
      from \<open>length p > 2\<close> \<open>p = p1 @ [(y, x)] @ p2\<close>
        consider (1) "p1 \<noteq> []" | (2) "p2 \<noteq> []" (* (1) "\<exists>e1 p1'. p1 = [e1] @ p1'" | (2) "\<exists>e2 p2'. p2 = [e2] @ p2'" *)
        by fastforce
      then show ?case
      proof (cases)
        case 1
        then have "\<exists>e1 p1'. p1 = [e1] @ p1'"
          by (simp add: neq_Nil_conv)
        then obtain e1 p1' where "p1 = [e1] @ p1'" by blast
        with e \<open>p = p1 @ [(y, x)] @ p2\<close> have "e # p = [(x, y), e1] @ p1' @ [(y, x)] @ p2" by auto
        with \<open>cas u (e # p) v\<close> have "y = fst e1"
          by (simp add: cas_simp)
        with \<open>e # p = [(x, y), e1] @ p1' @ [(y, x)] @ p2\<close>
          have "e # p = [(x, y), (y, snd e1)] @ p1' @ [(y, x)] @ p2" by simp
        with awalk_verts_conv[of "u" "(e # p)"] have
          "tl (awalk_verts u (e # p)) = [y] @ map fst p1' @ [y] @ map fst p2 @ [snd (last (e # p))]"
          by simp
        with \<open>distinct (tl (awalk_verts u (e # p)))\<close> show ?thesis by auto
      next
        case 2
        then have "\<exists>e2 p2'. p2 = [e2] @ p2'"
          by (simp add: neq_Nil_conv)
        then obtain e2 p2' where "p2 = [e2] @ p2'" by blast
        with e \<open>p = p1 @ [(y, x)] @ p2\<close> have "e # p = [(x, y)] @ p1 @ [(y, x)] @ [e2] @ p2'" by auto
        with \<open>cas u (e # p) v\<close> have "x = fst e2"
          by (simp add: cas_simp)
        with \<open>e # p = [(x, y)] @ p1 @ [(y, x)] @ [e2] @ p2'\<close>
          have "e # p = [(x, y)] @ p1 @ [(y, x)] @ [(x, snd e2)] @ p2'" by simp
        with awalk_verts_conv'[of "u" "(e # p)", OF \<open>cas u (e # p) v\<close>] have
          "(awalk_verts u (e # p)) = [x, y] @ map snd p1 @ [x] @ [snd e2] @ map snd p2'"
          by simp
        then have 
          "\<exists>p'. butlast (awalk_verts u (e # p)) = [x, y] @ map snd p1 @ [x] @ p'"
          by (simp add: butlast_append)
        with \<open>distinct (butlast (awalk_verts u (e # p)))\<close> show ?thesis by auto
      qed
    qed
  
    from \<open>(x, y) \<notin> set p\<close> \<open>(y, x) \<notin> set p\<close> e
      have "(undirected e) \<notin> set (map undirected p)"
      by (metis (no_types, lifting) imageE list.set_map undirected_iff)
    moreover have "map undirected (e # p) = undirected e # (map undirected p)" by simp
    ultimately show ?thesis 
      using Cons.IH[OF \<open>awalk D y p v\<close> \<open>distinct (tl (awalk_verts y p))\<close>
      \<open>distinct (butlast (awalk_verts y p))\<close> \<open>length p > 2\<close>] by simp
  qed
qed

lemma cycle'_imp_decycle:
  "cycle' D p \<Longrightarrow> \<exists>u. decycle G u (map undirected p)"
  using cycle'_def cycle_def decycle_def
   awalk_imp_epath awalk_distinct_imp_epath_distinct cycle'_imp_awalk_verts_distinct
  by (metis length_map)


lemma map_undirected_epath_to_awalk:
  "epath E u p v \<Longrightarrow> map undirected (epath_to_awalk u p) = p"
proof (induction p arbitrary: u v)
  case Nil
  then show ?case by simp
next
  case (Cons e p)
  then have "(\<exists>w. u \<noteq> w \<and> {u, w} = e \<and> epath E w p v) \<and> e \<in> E" by simp
  then obtain w where "u \<noteq> w" "{u, w} = e" "epath E w p v" "e \<in> E" by blast
  then have v_unique: "(\<exists>!v. v \<in> e - {u})" by blast
  with \<open>{u, w} = e\<close> have "(THE v. v \<in> e - {u}) = w" by auto

  with \<open>{u, w} = e\<close>
    have undirected_e: "undirected (let v' = (THE v. v \<in> e - {u}) in (u, v')) = e"
    by fastforce

  from undirected_e Cons.IH[OF \<open>epath E w p v\<close>] \<open>(THE v. v \<in> e - {u}) = w\<close>
    show ?case by simp
qed


lemma epath_imp_awalk:
  "epath G u p v \<Longrightarrow> u \<in> Vs G \<Longrightarrow> awalk D u (epath_to_awalk u p) v"
proof (induction p arbitrary: u v)
  case Nil
  then show ?case using in_Vs_iff_in_dVs unfolding awalk_def by simp
next
  case (Cons e p)
  have "epath_to_awalk u (e # p) = (let v' = (THE v. v \<in> e - {u}) in (u, v') # epath_to_awalk v' p)" by auto
  from \<open>epath G u (e # p) v\<close>
    have "(\<exists>w. u \<noteq> w \<and> {u, w} = e \<and> epath G w p v) \<and> e \<in> G" by simp
  then obtain w where "u \<noteq> w" "{u, w} = e" "epath G w p v" "e \<in> G" by blast
  then have v_unique: "(\<exists>!v. v \<in> e - {u})" by blast
  with \<open>{u, w} = e\<close> have "(THE v. v \<in> e - {u}) = w" by auto
  from \<open>{u, w} = e\<close> \<open>e \<in> G\<close> have "w \<in> Vs G" by auto

  have "(let v' = (THE v. v \<in> e - {u}) in (u, v')) \<in> D"
    using \<open>e \<in> G\<close> \<open>{u, w} = e\<close> \<open>u \<noteq> w\<close> D_def
    by force
  from awalk_Cons_iff \<open>(let v' = (THE v. v \<in> e - {u}) in (u, v')) \<in> D\<close>
    Cons.IH[OF \<open>epath G w p v\<close> \<open>w \<in> Vs G\<close>] show ?case 
    by (metis \<open>(THE v. v \<in> e - {u}) = w\<close>
    \<open>epath_to_awalk u (e # p) = (let v' = THE v. v \<in> e - {u} in (u, v') # epath_to_awalk v' p)\<close>
    fst_conv snd_conv)
qed


lemma decycle_imp_cycle':
  "decycle G u p \<Longrightarrow> \<exists>c. cycle' D c"
proof-
  assume "decycle G u p"
  then have "epath G u p u" "length p > 2" "distinct p"
    unfolding decycle_def by auto
  then have "p \<noteq> []" by auto

  let ?p_tl = "tl p"
  from \<open>length p > 2\<close> have "length ?p_tl > 1" by auto
  from \<open>epath G u p u\<close> \<open>length p > 2\<close>
    have "\<exists>x. u \<noteq> x \<and> p = {u, x} # ?p_tl \<and> epath G x ?p_tl u \<and> {u, x} \<in> G"
    by (metis epath.simps(2) \<open>p \<noteq> []\<close> list.collapse)
  then obtain x where "u \<noteq> x" "p = {u, x} # ?p_tl" "epath G x ?p_tl u" "{u, x} \<in> G" by blast

  from \<open>{u, x} \<in> G\<close> have "x \<in> Vs G" by blast
  from epath_imp_awalk[OF \<open>epath G x ?p_tl u\<close> this]
    have "awalk D x (epath_to_awalk x ?p_tl) u" by blast
  from apath_awalk_to_apath[OF this]
    have apath: "apath D x (awalk_to_apath D (epath_to_awalk x (tl p))) u" by blast

  let ?c' = "(u, x) # (awalk_to_apath D (epath_to_awalk x (tl p)))"

  from apath have "awalk D x (awalk_to_apath D (epath_to_awalk x (tl p))) u" unfolding apath_def by simp
  moreover have "(u, x) \<in> D" using D_def \<open>{u, x} \<in> G\<close> by auto
  ultimately have "awalk D u ?c' u"
    using awalk_Cons_iff
    by (metis fst_conv snd_conv)

  from apath have distinct_verts: "distinct (awalk_verts x (awalk_to_apath D (epath_to_awalk x (tl p))))"
    unfolding apath_def by auto

  have "awalk_verts u ?c' = u # awalk_verts x (awalk_to_apath D (epath_to_awalk x (tl p)))"
    by simp
  then have "tl (awalk_verts u ?c') = awalk_verts x (awalk_to_apath D (epath_to_awalk x (tl p)))"
    by simp
  with distinct_verts
    have "distinct (tl (awalk_verts u ?c'))" by simp

  have list_decomp_1: "\<And>l. length l = 1 \<Longrightarrow> \<exists>a. l = [a]"
    by (metis One_nat_def length_0_conv length_Cons nat.inject neq_Nil_conv)

  have "length ?c' > 2"
  proof (rule ccontr, goal_cases)
    case 1
    then have "length ?c' \<le> 2" by simp
    with \<open>awalk D u ?c' u\<close> \<open>u \<noteq> x\<close> have "length ?c' = 2"
      by (metis Suc_1 \<open>awalk D x (awalk_to_apath D (epath_to_awalk x (tl p))) u\<close> awalk_ends diff_is_0_eq'
      le_antisym length_greater_0_conv length_tl list.sel(3) list.size(3) not_less_eq_eq)
    then have "length (awalk_to_apath D (epath_to_awalk x (tl p))) = 1" by auto 
    with \<open>awalk D x (awalk_to_apath D (epath_to_awalk x (tl p))) u\<close>
      have "[(x, u)] = (awalk_to_apath D (epath_to_awalk x (tl p)))"
      using list_decomp_1 by fastforce
    with awalk_to_apath_subset[OF \<open>awalk D x (epath_to_awalk x (tl p)) u\<close>]
      have "(x, u) \<in> set (epath_to_awalk x (tl p))"
      by (metis in_mono list.set_intros(1))
    then have "undirected (x, u) \<in> set (map undirected (epath_to_awalk x (tl p)))"
      by (metis (no_types, opaque_lifting) image_insert insert_absorb insert_subset list.set_map subset_refl)
    with map_undirected_epath_to_awalk[OF \<open>epath G x (tl p) u\<close>]
      have "{x, u} \<in> set (tl p)" by simp
    with \<open>p = {u, x} # ?p_tl\<close> \<open>distinct p\<close>
      show ?case 
      by (metis distinct.simps(2) insert_commute)
  qed
  
  with \<open>awalk D u ?c' u\<close> \<open>distinct (tl (awalk_verts u ?c'))\<close>
    have "cycle' D ?c'" unfolding cycle'_def cycle_def by blast
  then show ?thesis by blast
qed

lemma cycle'_iff_decycle:
  "(\<exists>c. cycle' D c) = (\<exists>u c. decycle G u c)"
  using cycle'_imp_decycle decycle_imp_cycle' by blast




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

definition "edge_set = set (edges_of_path p)"

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

lemma vwalk_arcs_to_edges_of_path: 
  "e \<in> set (vwalk_arcs Q) \<Longrightarrow> {fst e, snd e} \<in> set (edges_of_path Q)" for e Q
 apply(induction Q, simp)
  subgoal for a Q
   by(cases Q, auto)
 done

end
