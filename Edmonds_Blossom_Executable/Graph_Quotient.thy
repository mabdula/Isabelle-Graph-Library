(*
  Author: Mohammad Abdulaziz
*)

theory Graph_Quotient
imports Undirected_Set_Graphs.Pair_Graph_Berge_Adaptor Undirected_Set_Graphs.Undirected_Set_Graphs
        "Basic_Matching.Berge"
         
begin

provenance human

subsection \<open>List Auxiliary Lemmas\<close>

lemma neq_Nil_conv_2:
  "l \<noteq> [] \<longleftrightarrow> (\<exists>l' x. l = l' @ [x])"
  by (auto intro: rev_exhaust)

lemma tl_distinct_rev:
  assumes "hd l = last l" "distinct (tl l)"
  shows "distinct (tl (rev l))"
proof-
  have "l \<noteq> [] \<Longrightarrow> rev (butlast l) = tl (rev l)"
    by (induction l; auto)
  then have "(butlast (tl (rev l))) = rev (butlast (tl l))"
    proof(induction l)
      case \<^marker>\<open>provenance ai\<close> (Cons a l)
      then \<^marker>\<open>provenance ai\<close> show \<^marker>\<open>provenance ai\<close> ?case
        by \<^marker>\<open>provenance human\<close> (cases "l = []"; auto)
    qed \<^marker>\<open>provenance ai\<close> auto
  then have set_butlast_tl: "set (butlast (tl (rev l))) = set (butlast (tl l))"
    by simp
  have [simp]: "distinct l \<longleftrightarrow> card (set l) = length l" for l
    using distinct_card card_distinct
    by auto
  have a[simp]: "l \<noteq> [] \<Longrightarrow> insert (last l) (set (butlast l)) = set l" for l
    by (induction l; auto)
  have [simp]: "tl l \<noteq> [] \<Longrightarrow> set (tl (rev l)) = insert (hd l) (set (butlast (tl (rev l))))"
    by (induction l; auto)
  have [simp]: "tl l = [] \<Longrightarrow> tl (rev l) = []"
    by(induction l; auto)
  have [simp]: "tl l \<noteq> [] \<Longrightarrow> last l = last (tl l)"
    by(induction l; auto)
  show ?thesis
    using assms
    by (cases "tl l = []"; auto simp: set_butlast_tl)
qed

lemma distinct_tl_then_butlast:
  assumes "distinct (tl l)" "hd l = last l" "l \<noteq> []"
  shows "distinct (butlast l)"
  using assms
proof(induction l)
  case Nil
  then show ?case
    by auto
next
  case (Cons a l)
  then show ?case
    by (cases l rule: rev_cases; auto)
qed

lemma two_mem_list_split:
  assumes "v1 \<in> set p" "v2 \<in> set p" "Q v1" "Q v2" "v1 \<noteq> v2"
  shows "\<exists>w x p1 p2 p3. p = p1 @ w # p2 @ x # p3 \<and> Q w \<and> Q x"
  using extract_first_and_last[of v1 p v2 Q, OF assms]
  by fastforce

lemma two_mem_list_split':
  assumes "v1 \<in> set p" "v2 \<in> set p" "Q v1" "Q v2" "v1 \<noteq> v2"
  shows "\<exists>w x p1 p2 p3. p = p1 @ w # p2 @ x # p3 \<and> Q w \<and> Q x \<and> (\<forall>x\<in>set p1. \<not> Q x)"
proof \<^marker>\<open>provenance ai\<close>-
  obtain a b as bs cs where "p = as @ a # bs @ b # cs" "Q a" "Q b" "\<forall>z\<in>set as. \<not> Q z"
    using \<^marker>\<open>provenance human\<close> extract_first_and_last[of v1 p v2 Q, OF assms]
    by \<^marker>\<open>provenance human\<close> auto
  then \<^marker>\<open>provenance human\<close> show \<^marker>\<open>provenance human\<close> ?thesis
    by \<^marker>\<open>provenance ai\<close> (intro exI[of _ a] exI[of _ b] exI[of _ as] exI[of _ bs] exI[of _ cs]) simp
qed \<^marker>\<open>provenance human\<close>

lemma one_mem_pure_suff:
  assumes "v \<in> set p" "Q v"
  shows "\<exists>w p1 p2 . p = p1 @ w # p2 \<and> Q w \<and> (\<forall>x\<in>set p2. \<not> Q x)"
  using \<^marker>\<open>provenance ai\<close> split_list_last_prop[OF bexI[of Q v "set p", OF assms(2,1)]]
  by \<^marker>\<open>provenance ai\<close> auto

lemma one_mem_pure_pref:
  assumes "v \<in> set p" "Q v"
  shows "\<exists>w p1 p2 . p = p1 @ w # p2 \<and> Q w \<and> (\<forall>x\<in>set p1. \<not> Q x)"
  using \<^marker>\<open>provenance ai\<close> split_list_first_prop[OF bexI[of Q v "set p", OF assms(2,1)]]
  by \<^marker>\<open>provenance ai\<close> auto

lemma two_mem_list_split'':
  assumes "v1 \<in> set p" "v2 \<in> set p" "Q v1" "Q v2" "v1 \<noteq> v2" "distinct p"
  shows "\<exists>p1 p2 p3 w x. p = p1 @ w # p2 @ x # p3 \<and> Q w \<and> Q x \<and> w \<noteq> x \<and> (\<forall>x\<in>set p1. \<not> Q x) \<and> (\<forall>x\<in>set p3. \<not> Q x)"
proof \<^marker>\<open>provenance ai\<close>-
  obtain a b as bs cs where p: "p = as @ a # bs @ b # cs" and Q: "Q a" "Q b" and pre: "\<forall>z\<in>set as. \<not> Q z" and suf: "\<forall>z\<in>set cs. \<not> Q z"
    using \<^marker>\<open>provenance human\<close> extract_first_and_last[of v1 p v2 Q, OF assms(1-5)]
    by auto
  have ab: "a \<noteq> b"
    using assms(6) p
    by \<^marker>\<open>provenance human\<close> (simp add: distinct_append)
  show \<^marker>\<open>provenance human\<close> ?thesis
    using \<^marker>\<open>provenance ai\<close> p Q pre suf ab
    by blast
qed \<^marker>\<open>provenance human\<close>

lemma split_list_pure_pref_suff:
  assumes "x\<in>(set p)" "\<forall>y\<in>set p. Q y  \<longrightarrow> x = y" "distinct p"
  shows "\<exists>p1 p2. p = p1 @ x # p2 \<and> (\<forall>x\<in>set p1. \<not> Q x) \<and> (\<forall>x\<in>set p2. \<not> Q x)"
proof-
  obtain p1 p2 where p1p2: "p = p1 @ x # p2"
    using assms(1)
    by (auto dest: split_list)
  then have "\<forall>x\<in>set p1. \<not> Q x" "\<forall>x\<in>set p2. \<not> Q x"
    using assms(2,3)
    by auto
  then show ?thesis
    using p1p2
    by blast
qed

lemma card2_subset:
  assumes "card s = 2" "s \<noteq> {}"
  shows "\<exists>x y. {x, y} \<subseteq> s"  
  using assms
  by(auto simp: numeral_2_eq_2 card_le_Suc_iff)

subsection \<open>Odd Cycles\<close>

definition odd_cycle where
  "odd_cycle p = ( (length p \<ge> 3) \<and> odd (length (edges_of_path p)) \<and> hd p = last p)"

lemma odd_cycle_nempty:
  assumes "odd_cycle p"
  shows "p \<noteq> []"
  using \<^marker>\<open>provenance ai\<close> assms
  unfolding odd_cycle_def
  by \<^marker>\<open>provenance ai\<close> (cases p; auto)

lemma odd_cycleD:
  assumes "odd_cycle p"
  shows "(length p \<ge> 3)" "odd (length (edges_of_path p))" "hd p = last p"
  using assms
  unfolding odd_cycle_def
  by simp+

lemma odd_cycle_even_verts: assumes "odd_cycle C" shows "even (length C)"
  using odd_cycleD[OF assms(1)]
  by (auto simp: Suc_le_length_iff numeral_3_eq_3 edges_of_path_length split: if_splits)

subsection \<open>Blossoms\<close>

text \<open>The definition of what a blossom is w.r.t. a matching.\<close>

definition match_blossom where
  "match_blossom M stem C = ( alt_path M (stem @ C) \<and> distinct (stem @ (butlast C)) \<and>
                      odd_cycle C \<and> hd (stem @ C) \<notin> Vs M \<and>
                      even (length (edges_of_path (stem @ [hd C]))))"

lemma match_blossomD:
  assumes "match_blossom M stem C"
  shows "alt_path M (stem @ C)"
    "distinct (stem @ (butlast C))" "odd_cycle C" "hd (stem @ C) \<notin> Vs M"
    "even (length (edges_of_path (stem @ [hd C])))"
  using assms
  unfolding match_blossom_def
  by auto

lemma match_blossom_alt_cycle:
  assumes "match_blossom M stem C"
  shows "alt_path M C"
proof(cases "(edges_of_path (stem @ [hd C])) = []")
  case True
  then have "stem = []"
    using edges_of_path_snoc snoc_eq_iff_butlast
    by fastforce
  then show ?thesis
    using match_blossomD(1)[OF assms]
    by auto
next
  have "C \<noteq> []"
    using assms match_blossomD(3) odd_cycle_nempty
    by auto
  then have eq: "edges_of_path (stem @ [hd C]) @ edges_of_path C  = edges_of_path (stem @ C)"
    using edges_of_path_append_2
    by force
  then have "alt_path M (stem @ [hd C])"
    using match_blossomD(1)[OF assms]
    by (auto dest: alt_list_append_1 simp flip: eq)
  moreover case False
  ultimately have "last (edges_of_path (stem @ [hd C])) \<in> M"
    using match_blossomD(5)[OF assms]
    using alternating_eq_iff_even alternating_list_even_last
    by blast
  then show ?thesis
    using \<^marker>\<open>provenance ai\<close> alt_list_append_1'[of "\<lambda>e. e \<notin> M" "\<lambda>e. e \<in> M" "edges_of_path (stem @ [hd C])" "edges_of_path C"]
          match_blossomD(1)[OF assms] eq False
    by \<^marker>\<open>provenance ai\<close> auto
qed

abbreviation "blossom G M stem C \<equiv> path G (stem @ C) \<and> match_blossom M stem C"

lemma blossomD: assumes "blossom G M stem C"
  shows "path G (stem @ C)" "match_blossom M stem C"
  using assms
  by auto

subsection \<open>Quotient graph\<close>

definition quot_graph where
  "quot_graph P G = {e'. \<exists>e\<in>G. e' = P ` e}"

lemma edge_in_graph_in_quot:
  "e \<in> M \<Longrightarrow> (P ` e) \<in> (quot_graph P M)"
  by (auto simp: quot_graph_def)

(*definition rev_map where
  "rev_map P s u  \<equiv> SOME v. v \<in> s \<and> P v = u"*)

lemma Vs_quot_graph:
  shows "v \<in> Vs E \<Longrightarrow> P v \<in> Vs (quot_graph P E)"
  by (auto simp: quot_graph_def image_def Vs_def)

lemma path_is_quot_path:
  assumes "path M p"
  shows "path (quot_graph P M) (map P p)"
  using assms
proof(induction)
  case (path1 v)
  then show ?case
    using Vs_quot_graph
    by simp
next
  case (path2 v v' vs)
  then show ?case
    using edge_in_graph_in_quot[OF path2.hyps(1)]
    by auto
qed simp

text\<open>Locale that fixes the constants concerning graph quotients a.k.a.\ graph contractions\<close>



locale quot = graph_abs E for E :: "'a set set" +
  fixes s::"'a set" and u::'a
  assumes good_quot_map: "u \<notin> s" "s \<subset> Vs E"
begin

abbreviation "P v \<equiv> (if v \<in> s then v else u)"

lemma edge_in_quot_in_graph_1:
  assumes edge: "(P ` e) \<in> (quot_graph P E)" "e \<subseteq> s"
  shows "e \<in> E"
proof \<^marker>\<open>provenance ai\<close>-
  obtain \<^marker>\<open>provenance human\<close> e' where e': "e' \<in> E" "P ` e = P ` e'"
    using \<^marker>\<open>provenance ai\<close> edge(1)
    unfolding quot_graph_def
    by \<^marker>\<open>provenance ai\<close> auto
  have Pe: "P ` e = e"
    using edge(2)
    by \<^marker>\<open>provenance human\<close> (auto simp: subset_iff)
  have "e' \<subseteq> s"
  proof
    fix x
    assume "x \<in> e'"
    then have "P x \<in> P ` e"
      using e'(2)
      by blast
    then have "P x \<in> e"
      by \<^marker>\<open>provenance human\<close> (simp only: Pe)
    then have "P x \<in> s"
      using edge(2)
      by blast
    then show "x \<in> s"
      using good_quot_map(1)
      by \<^marker>\<open>provenance human\<close> (auto split: if_splits)
  qed
  then have "P ` e' = e'"
    by \<^marker>\<open>provenance human\<close> (auto simp: subset_iff)
  then \<^marker>\<open>provenance human\<close> show \<^marker>\<open>provenance human\<close> ?thesis
    using \<^marker>\<open>provenance ai\<close> e' Pe
    by \<^marker>\<open>provenance ai\<close> simp
qed

lemma edge_in_quot_in_graph_1':
  assumes edge: "e \<in> (quot_graph P M)" "e \<subseteq> s" "M \<subseteq> E"
  shows "e \<in> M"
proof \<^marker>\<open>provenance ai\<close>-
  obtain \<^marker>\<open>provenance human\<close> e' where e': "e' \<in> M" "e = P ` e'"
    using \<^marker>\<open>provenance ai\<close> edge(1)
    unfolding quot_graph_def
    by auto
  have "e' \<subseteq> s"
  proof
    fix x
    assume "x \<in> e'"
    then have "P x \<in> e"
      using e'(2)
      by blast
    then have "P x \<in> s"
      using edge(2)
      by blast
    then show "x \<in> s"
      using good_quot_map(1)
      by \<^marker>\<open>provenance human\<close> (auto split: if_splits)
  qed \<^marker>\<open>provenance human\<close>
  then have "P ` e' = e'"
    by \<^marker>\<open>provenance human\<close> (auto simp: subset_iff)
  then show ?thesis
    using e'
    by \<^marker>\<open>provenance human\<close> simp
qed

lemma edge_in_quot_in_graph_2':
  assumes edge: "e \<in> (quot_graph P M)" "u \<in> e" "M \<subseteq> E"
  shows "\<exists>e' v. e' \<in> M \<and> P ` e' = e \<and> v \<notin> s \<and> v \<in> e' \<and> e \<inter> s = e' \<inter> s"
proof-
  obtain e' v where e'v: "e' \<in> M \<and> P ` e' = e \<and> v \<notin> s \<and> v \<in> e'"
    using assms good_quot_map
    by (auto simp: quot_graph_def Vs_def image_def)
  then have "e \<inter> s = e' \<inter> s"
    using good_quot_map
    unfolding image_def
    by auto
  then show ?thesis
    using e'v
    by auto
qed

lemma edge_in_quot_in_graph_2'_doubleton:
  assumes edge: "{u, v} \<in> (quot_graph P M)" "v \<in> s" "M \<subseteq> E"(*and
    graph: "(\<forall>e\<in>E. \<exists>u v. e = {u, v})"*)
  shows "\<exists>w. {v,w} \<in> M \<and> w \<notin> s"
proof-
  obtain v1 v2 where v1v2: "{v1, v2} \<in> M" "P ` {v1, v2} = {u, v}"
    using edge dblton_E
    by(auto simp add: quot_graph_def image_def )
  then have "(v1 = v \<and> v2 \<notin> s) \<or> (v2 = v  \<and> v1 \<notin> s)"
    using good_quot_map edge(2)
    by (force simp add: doubleton_eq_iff)
  then show ?thesis
    using v1v2(1)
    by (auto simp: insert_commute)
qed

text\<open>Quoteint graph w/o self-loops\<close>

abbreviation "quotG G \<equiv> (quot_graph P G) - {{u}}" 

lemma edge_in_quotG_2'_doubleton:
  assumes edge: "{u, v} \<in> (quotG M)" "v \<in> s" "M \<subseteq> E"
  shows "\<exists>w. {v,w} \<in> M \<and> w \<notin> s"
  using edge_in_quot_in_graph_2'_doubleton assms dblton_E
  by (blast elim: dblton_graphE)

lemma edge_in_quot_in_graph_2'':
  assumes edge: "e \<in> (quotG M)" "u \<in> e" \<open>M \<subseteq> E\<close>
  shows "\<exists>e' v. e' \<in> M \<and> P ` e' = e \<and> v \<notin> s \<and> v \<in> e' \<and> e \<inter> s = e' \<inter> s"
  using edge_in_quot_in_graph_2' assms
  by auto

lemma path_is_quot_path:
  assumes path: "path (quotG E) p" "set p \<subseteq> s"
  shows "path E p"
  using assms
proof (induction)
  case path0
  then show ?case
    by simp
next
  case (path1 v)
  then show ?case
    using good_quot_map
    by auto
next
  case (path2 v v' vs)
  then show ?case
    using edge_in_quot_in_graph_1'
    by auto
qed

lemma path_is_quot_path':
  assumes path: "path (quotG E) p" "set p \<subseteq> s"
  shows "path E p"
  using \<^marker>\<open>provenance ai\<close> assms
  by (rule path_is_quot_path)

lemma edge_of_path_in_graph_iff_in_quot:
  assumes "set p \<subseteq> s" "e \<in> set (edges_of_path p)" "M \<subseteq> E"
  shows "e \<in> M \<longleftrightarrow> e \<in> quotG M"
proof-
  have e_sub_s: "e \<subseteq> s"
    using assms
    by (auto simp: subset_iff dest: v_in_edge_in_path_gen)
  then have imP: "e = P ` e"
    using assms
    by(simp add: image_def subset_iff)
  then have "e \<in> quotG M" if "e \<in> M"
    unfolding quot_graph_def
    using that
    using e_sub_s good_quot_map(1)
    by blast
  moreover have "e \<in> M" if "e \<in> quotG M"
    using e_sub_s edge_in_quot_in_graph_1' that \<open>M \<subseteq> E\<close>
    by auto
  ultimately show ?thesis
    by blast
qed

lemma vert_in_graph_iff_in_quot:
  assumes path: "v \<in> s" "M \<subseteq> E"
  shows "v \<in> Vs M \<longleftrightarrow> v \<in> Vs (quot_graph P M)"
proof-
  have "v = P v"
    using assms
    by (simp add: good_quot_map(1))
  then have "v \<in> Vs (quot_graph P M)" if "v \<in> Vs M"
    using that path
    by (auto simp: quot_graph_def Vs_def)
  moreover have "v \<in> Vs M" if "v \<in> Vs (quot_graph P M)"
    using that assms good_quot_map
    by (auto simp add: quot_graph_def Vs_def)
  ultimately show ?thesis
    by auto
qed

lemma v_in_quot_iff_minus_u:
  assumes "v \<in> s" "M \<subseteq> E"
  shows "v \<in> Vs (quotG M) \<longleftrightarrow> v \<in> Vs (quot_graph P M)"
proof-
  have v_neq_u: "v \<noteq> u"
    using good_quot_map(1) assms
    by auto
  then show ?thesis
    using assms vert_in_graph_iff_in_quot
    unfolding Vs_def
    by blast
qed

lemma vert_in_graph_iff_in_quot_diff_u:
  assumes path: "v \<in> s" "M \<subseteq> E"
  shows "v \<in> Vs M \<longleftrightarrow> v \<in> Vs (quotG M)"
  using v_in_quot_iff_minus_u[OF assms] vert_in_graph_iff_in_quot[OF assms]
  by simp

text\<open>An augmenting path in the graph is one iff it is an augmenting path in the quotient, if it does
      not touch any of the contracted vertices\<close>

theorem qug_path_iff_case_1_i:
  assumes path: "set p \<subseteq> s" "M \<subseteq> E"
  shows "matching_augmenting_path M p = matching_augmenting_path (quotG M) p"
proof-
  have "alt_path M p = alt_path (quotG M) p"
    using edge_of_path_in_graph_iff_in_quot path assms
    by (intro alt_list_cong_eq; blast)
  moreover have hl: "length p \<ge> 2 \<Longrightarrow> hd p \<in> s \<and> last p \<in> s"
  proof \<^marker>\<open>provenance ai\<close>-
    assume \<^marker>\<open>provenance human\<close> "length p \<ge> 2"
    then \<^marker>\<open>provenance human\<close> have \<^marker>\<open>provenance human\<close> "p \<noteq> []"
      by (auto simp: Suc_le_length_iff)
    then \<^marker>\<open>provenance human\<close> show \<^marker>\<open>provenance human\<close> "hd p \<in> s \<and> last p \<in> s"
      using path
      by auto
  qed
  then have "length p \<ge> 2 \<and> hd p \<notin> Vs M \<and> last p \<notin> Vs M \<longleftrightarrow> length p \<ge> 2 \<and> hd p \<notin> Vs (quotG M) \<and> last p \<notin> Vs (quotG M)"
    using vert_in_graph_iff_in_quot_diff_u \<open>M \<subseteq> E\<close>
    by auto
  ultimately show ?thesis
    unfolding matching_augmenting_path_def
    by auto
qed

subsection\<open>Lifting a quotient augmenting path\<close>

text\<open>This is the proof of lifting a contracted augmenting path to a concrete graph, if it
     intersects with a contracted vertex.\<close>

lemma path_is_quot_path_diff_u:
  assumes "path E p" "set p \<subseteq> s" "s \<subseteq> Vs E"
  shows "path (quotG E) (map P p)"
  using assms
proof(induction)
case path0
  then show ?case
   by simp
next
  case (path1 v)
  then have "P v \<in> Vs (quot_graph P E)"
    using \<^marker>\<open>provenance ai\<close> Vs_quot_graph[of v E P]
    by \<^marker>\<open>provenance ai\<close> simp
  then show ?case
    using v_in_quot_iff_minus_u path1
    by (simp add: good_quot_map(1))
next
  case (path2 v v' vs)
  have "{v, v'} \<in> quot_graph P E"
    using edge_in_graph_in_quot[OF path2.hyps(1), of P] path2.prems(1)
    by \<^marker>\<open>provenance ai\<close> simp
  then show ?case
    using path2 good_quot_map
    by (auto simp: path2.IH)

qed

lemma qug_path_iff_case_1_ii:
  assumes path: "set p \<subseteq> s" 
  shows "path E p = path (quotG E) p"
proof \<^marker>\<open>provenance ai\<close>-
  have mp: "map P p = p"
    using path
    by \<^marker>\<open>provenance human\<close> (auto intro!: map_idI simp: subset_iff)
  show ?thesis
    using \<^marker>\<open>provenance human\<close> path path_is_quot_path'[OF _ path] path_is_quot_path_diff_u[OF _ path] good_quot_map mp
    by \<^marker>\<open>provenance human\<close> auto
qed


lemma path_with_cycle_at_beginning:
  assumes path: "set p1 \<subseteq> s" "set p2 \<subseteq> s"
                "path (quotG E) (u # p2)"
  (*and
  graph: "(\<forall>e\<in>E. \<exists>u v. e = {u, v})"*)
shows "\<exists>uinv. path E (uinv # p2) \<and> uinv \<in> (Vs E) - s"
  using assms
  proof(induction p2)
    case nil2: Nil
    then show ?case
      using good_quot_map(2)
      by (auto simp: psubset_imp_ex_mem)
  next
    case (Cons a p2)
    show ?case
    proof-
      obtain w where w: "{a, w} \<in> E \<and> w \<notin> s"
        using edge_in_quot_in_graph_2'_doubleton Cons
        by force
      moreover have "w \<in> Vs E"
        using w
        by (auto simp: edges_are_Vs insert_commute)
      moreover have "path E (a # p2)"
        using Cons
        by (intro path_is_quot_path'; auto)
      ultimately show ?thesis
        by (auto simp: insert_commute)
  qed
qed

text\<open>If u is not in the quotient matching, then no matching edge connects a vertex from the odd cycle
   and another from outside of it.\<close>

lemma no_edges_to_cycle_if_u_unmatched:
  assumes matching: "v \<notin> s" "e \<in> M" "v \<in> e"  and
          quot: "u \<notin> Vs (quotG M)"
  shows "e \<inter> s = {}"
proof(rule ccontr; auto)
  fix x 
  assume ass: "x\<in>s" "x\<in>e"
  then have "v \<noteq> x"
    using matching
    by auto
  then have "P ` e \<in> quotG M" "{u,x} \<subseteq> P ` e"
    using good_quot_map matching ass
    by (fastforce simp: quot_graph_def image_def)+
  moreover have "u \<noteq> x"
    using ass good_quot_map
    by auto
  ultimately show False
    using quot
    by blast
qed

end

text\<open>Since it is an odd cycle, then either both the first and last edges are matching edges or no.\<close>

lemma odd_cycle_hd_last_or:
  assumes cycle: "odd_cycle p" "alt_path M p"
  shows "(hd (edges_of_path p) \<in> M \<and> last (edges_of_path  p) \<in> M) \<or>
                (hd (edges_of_path p) \<notin> M \<and> last (edges_of_path p) \<notin> M)"
proof-
  let ?ep = "edges_of_path p"
  show ?thesis
  proof(cases "length (filter (\<lambda>e. e \<notin> M) ?ep) < length (filter (\<lambda>e. e \<in> M) ?ep)")
    case True
    then have "alt_list (\<lambda>e. e \<in> M) (\<lambda>e. e \<notin> M) (edges_of_path p)"
      using cycle
      unfolding odd_cycle_def
      using alternating_list_gt_or
      by blast
    then show ?thesis
      using cycle
      unfolding odd_cycle_def
      using alt_list_not_commute True
      by (intro disjI1 alternating_list_gt; blast)
  next
    have "odd (length (edges_of_path p))"
      using cycle
      unfolding odd_cycle_def
      by simp
    then have "length (filter (\<lambda>e. e \<notin> M) ?ep) \<noteq> length (filter (\<lambda>e. e \<in> M) ?ep)"
      using cycle
      unfolding odd_cycle_def
      by (intro alternating_eq_even'; simp)
    moreover case False
    ultimately have "length (filter (\<lambda>e. e \<in> M) ?ep) < length (filter (\<lambda>e. e \<notin> M) ?ep)"
      by simp
    then show ?thesis
      using cycle
      unfolding odd_cycle_def
      by (intro disjI2 alternating_list_gt; auto)
  qed
qed

lemma matching_odd_cycle_hd_last_unmatched:
  assumes cycle: "odd_cycle p" "alt_path M p" "distinct (tl p)" and
          matching: "matching M"
  shows "(hd (edges_of_path p) \<notin> M \<and> last (edges_of_path p) \<notin> M)"
proof(rule ccontr)
  assume "\<not> (hd (edges_of_path p) \<notin> M \<and> last (edges_of_path p) \<notin> M)"
  then have inM: "hd (edges_of_path p) \<in> M \<and> last (edges_of_path p) \<in> M"
    using odd_cycle_hd_last_or[OF cycle(1,2)]
    by auto
  have "distinct (edges_of_path (tl p))"
    using cycle(3)
    by (simp add: distinct_edges_of_vpath)
  then have "distinct (edges_of_path p)"
    using cycle[unfolded odd_cycle_def]
    by (cases p; simp add: distinct_edges_of_vpath split: if_splits; use alternating_list_odd_last inM in blast)
  moreover have "length (edges_of_path p) \<ge> 2"
    using cycle(1)
    unfolding odd_cycle_def
    by (auto simp: edges_of_path_length)
  ultimately have "hd (edges_of_path p) \<noteq> last (edges_of_path p)"
    by (cases "edges_of_path p"; auto)
  moreover have "last p \<in> (hd (edges_of_path p))" "last p \<in> (last (edges_of_path p))"
    using cycle
    unfolding odd_cycle_def
    using alternating_list_odd_last inM
    by (auto intro: hd_v_in_hd_e)
  moreover have "last p \<in> Vs M"
    using inM
    using Vs_def calculation(2)
    by fastforce
  ultimately show False
    using matching[unfolded matching_def2] inM
    unfolding matching_def2
    by auto
qed

text\<open>Thus, if @{term "u \<notin> quotM"}, there no cycle or non cycle matching edges that include it. Accordingly it is 
  unmatched.\<close>

lemma alt_path_vert_is_matched:
  assumes "alt_path M p" "v \<in> set p" "v \<noteq> hd p" "v \<noteq> last p" "p \<noteq> []"
  shows "\<exists>e \<in> set (edges_of_path p). v \<in> e \<and> e \<in> M"
  using assms
proof(induction "length p" arbitrary: p rule: nat_less_induct)
  case ass: 1
  then show ?case
  proof(cases p)
    case Nil
    then show ?thesis
      using ass.prems
      by simp
  next
    case cons1: (Cons a' p')
    show ?thesis
    proof(cases p')
      case Nil
      then show ?thesis
        using ass.prems cons1
        by simp
    next
      case cons2: (Cons a'' p'')
      show \<^marker>\<open>provenance ai\<close> ?thesis
      proof(cases p'')
        case Nil
        then \<^marker>\<open>provenance human\<close> show \<^marker>\<open>provenance human\<close> ?thesis
          using ass.prems cons1 cons2
          by \<^marker>\<open>provenance ai\<close> simp
      next
        case (Cons y ys)
        then have \<^marker>\<open>provenance human\<close> alt: "{a', a''} \<notin> M" "{a'', y} \<in> M" "alt_path M (y # ys)"
          using ass.prems(1) cons1 cons2
          by (auto simp: alt_list_step)
        show ?thesis
        proof \<^marker>\<open>provenance human\<close>(cases "v = a'' \<or> v = y")
          case \<^marker>\<open>provenance ai\<close> True
          then \<^marker>\<open>provenance ai\<close> show \<^marker>\<open>provenance ai\<close> ?thesis
            using \<^marker>\<open>provenance human\<close> alt(2) cons1 cons2 Cons
            by auto
        next \<^marker>\<open>provenance ai\<close>
          case \<^marker>\<open>provenance ai\<close> False
          then \<^marker>\<open>provenance ai\<close> have \<^marker>\<open>provenance ai\<close> "v \<in> set ys"
            using \<^marker>\<open>provenance human\<close> ass.prems(2,3) cons1 cons2 Cons
            by auto
          moreover \<^marker>\<open>provenance ai\<close> have "length (y # ys) < length p"
            using cons1 cons2 Cons
            by \<^marker>\<open>provenance ai\<close> simp
          ultimately \<^marker>\<open>provenance ai\<close> have "\<exists>e\<in>set (edges_of_path (y # ys)). v \<in> e \<and> e \<in> M"
            using \<^marker>\<open>provenance ai\<close> ass.hyps[rule_format, of "length (y # ys)" "y # ys"] ass.prems(4) alt(3) cons1 cons2 Cons False
            by \<^marker>\<open>provenance ai\<close> auto
          then \<^marker>\<open>provenance ai\<close> show \<^marker>\<open>provenance ai\<close> ?thesis
            using cons1 cons2 Cons
            by auto
        qed \<^marker>\<open>provenance ai\<close>
      qed
    qed
  qed
qed

lemma alt_path_vert_is_matched':
  assumes "alt_path M p" "v \<in> set p" "v \<noteq> hd p" "v \<noteq> last p" "p \<noteq> []"
  shows "v \<in> Vs M"
  using alt_path_vert_is_matched[OF assms]
  unfolding Vs_def
  by auto   

context quot
begin

lemma not_in_quot_matching_not_in_matching:
  assumes (*doubleton_neq_edges: "dblton_graph E" and*)
          match: "matching M" "M \<subseteq> E" and
          cycle: "odd_cycle p" "alt_path M p" "distinct (tl p)" and
          quot: "s = (Vs E) - set p" and
          notin: "u \<notin> Vs (quotG M)"
        shows "last p \<notin> Vs M"
proof(rule ccontr; simp)
  assume "last p \<in> Vs M"
  then obtain e where e: "e \<in> M" "last p \<in> e"
    unfolding Vs_def
    by auto
  show False
  proof(cases "e \<in> set (edges_of_path p)")
    have "e = last (edges_of_path (tl p))" if "last (tl p) \<in> e" "e \<in> set (edges_of_path (tl p))" for e
      using cycle[unfolded odd_cycle_def]
      by (intro last_vert_in_last_edge that; auto)
    moreover have "last p = last (tl p)"
      using cycle(1)[unfolded odd_cycle_def]
      by (auto simp: Suc_le_length_iff numeral_3_eq_3)
    ultimately have "e = last (edges_of_path p) \<or> e = hd (edges_of_path p)" if "last p \<in> e" "e \<in> set (edges_of_path p)" for e
      using in_edges_of_path_hd_or_tl[OF that(2)] that
      by (cases p rule: edges_of_path.cases; auto)
    moreover case True
    ultimately show ?thesis
      using e matching_odd_cycle_hd_last_unmatched[OF cycle match(1)]
      by auto
  next
    case F1: False
    moreover have "e \<in> E"
      using match e
      by auto
    ultimately obtain v where v: "e = {v, last p}" "v \<noteq> last p"
      using dblton_E e
      by (fastforce simp: dblton_graph_def)
    have "{hd (tl p), hd (tl (tl p))} \<in> M"
      using odd_cycleD[OF cycle(1)] cycle(2)
      by(auto simp add: Suc_le_length_iff numeral_3_eq_3 alt_list_step)
    show ?thesis
    proof(cases "v \<in> set p")
      case T1: True
      moreover have "\<exists>e' \<in> set (edges_of_path p). v \<in> e' \<and> e' \<in> M" 
        using odd_cycleD[OF cycle(1)] cycle(2) v
        by (intro alt_path_vert_is_matched v T1 odd_cycleD[OF cycle(1)]; auto)
      ultimately show ?thesis
        using match[unfolded matching_def2]
              e v F1
        by \<^marker>\<open>provenance ai\<close> auto
    next
      case F2: False
      moreover have *: "last p \<notin> s"
        using quot odd_cycle_nempty[OF cycle(1)]
        by simp
      moreover have "v \<in> s"
        using quot F2 \<open>e \<in> E\<close>
        unfolding Vs_def
        using v(1)
      by blast
      ultimately show ?thesis
        using no_edges_to_cycle_if_u_unmatched[OF * e(1) _ notin] e(2) v
        by simp        
    qed
  qed
qed

end

subsubsection\<open>Finding where a given vertex is connected in an odd cycle\<close>

text\<open>A function to find the prefix of a list until a given element is found. It is used to find
     where a vertex mounts onto an alternating cycle that is a par of a blossom.\<close>

fun find_pfx::"('b \<Rightarrow> bool) \<Rightarrow> 'b list \<Rightarrow> 'b list" where
 "find_pfx Q [] = []" |
 "find_pfx Q (h # l) = (if (Q h) then [h] else h # (find_pfx Q l))"

lemma find_pfx_works_1:
  assumes "y \<in> set l" "Q y"
  shows "Q (last (find_pfx Q l))"
  using assms
proof(induction l arbitrary: y)
  case Nil
  then show ?case
    by simp
next
  case (Cons a' l')
  then show ?case
  proof \<^marker>\<open>provenance ai\<close>(cases "Q a'")
    case True
    then show ?thesis
      by \<^marker>\<open>provenance human\<close> simp
  next
    case False
    then have "y \<in> set l'"
      using \<^marker>\<open>provenance human\<close> Cons.prems
      by auto
    then have \<^marker>\<open>provenance human\<close> "Q (last (find_pfx Q l'))"
      using Cons.IH Cons.prems(2)
      by \<^marker>\<open>provenance ai\<close> blast
    moreover have \<^marker>\<open>provenance human\<close> "find_pfx Q l' \<noteq> []"
      using \<open>y \<in> set l'\<close>
      by \<^marker>\<open>provenance ai\<close> (cases l'; auto)
    ultimately show ?thesis
      using False
      by \<^marker>\<open>provenance human\<close> simp
  qed
qed

lemma find_pfx_works_2:
  assumes "y \<in> set l" "Q y"
  shows "Q(last (find_pfx Q (rev l)))"
  using assms
proof(induction l)
  case Nil
  then show ?case
    by simp
next
  case (Cons a' l')
  then show ?case
    by (simp add: find_pfx_works_1)
qed

lemma find_pfx_nempty:
  assumes "x \<in> set l" "Q x"
  shows "(find_pfx Q l) \<noteq> []"
  using assms
  by(induction l; simp)

lemma last_find_pfx_val:
  assumes "\<forall>x\<in>set l1. \<not> Q x" "Q y"
  shows "last (find_pfx Q (l1 @ [y])) = y"
  using assms
proof(induction l1)
  case Nil
  then show ?case
    by simp
next
  case (Cons a' l1')
  then show ?case
    using \<^marker>\<open>provenance ai\<close> find_pfx_nempty[of y "l1' @ [y]" Q]
    by auto
qed

lemma find_pfx_append:
  assumes "Q y"
  shows "(find_pfx Q (l1 @ [y] @ l2)) = (find_pfx Q (l1 @ [y]))"
  using assms
  by(induction l1; auto)

lemma find_pfx_alt_list:
  assumes "Q x" "Q y"
          "\<forall>a\<in>set l. Q a \<longrightarrow> (a = x \<or> a = y)"
          "x \<notin> set l1 \<and> x \<notin> set l2 \<and> y \<notin> set l1 \<and> y \<notin> set l2"
          "l = (l1 @ x # y # l2)"
          "alt_list P1 P2 l"
        shows "(P1 (last (find_pfx Q l)) \<and> P2 (last (find_pfx Q (rev l)))) \<or>
                  (P2 (last (find_pfx Q l)) \<and> P1 (last (find_pfx Q (rev l))))"
  using assms
proof(induction l1 arbitrary: l P1 P2)
  case Nil
  then have "last (find_pfx Q (rev l2 @ [y])) = y"
    by (intro last_find_pfx_val; auto)
  moreover have "[y, x] = [y] @ [x]"
    by simp
  ultimately have "(last (find_pfx Q (rev l))) = y"
    using \<^marker>\<open>provenance ai\<close> Nil find_pfx_append[of Q y "rev l2" "[x]"]
    by simp
  moreover have "(last (find_pfx Q l)) = x"
    using Nil
    by auto
  ultimately show ?case
    using Nil
    by (simp add: alt_list_step)
next
  case (Cons a' l') 
  then obtain l'' where "l = a' # l''"
    by auto
  moreover have
    "P2 (last (find_pfx Q (l' @ x # y # l2))) \<and> P1 (last (find_pfx Q (rev (l' @ x # y # l2)))) \<or>
          P1 (last (find_pfx Q (l' @ x # y # l2))) \<and> P2 (last (find_pfx Q (rev (l' @ x # y # l2))))"
    using Cons
    by (intro Cons; auto simp add: alt_list_step)
  moreover \<^marker>\<open>provenance ai\<close> have \<^marker>\<open>provenance ai\<close> nQ: "\<not> Q a'"
    using Cons.prems(3-5)
    by auto
  moreover \<^marker>\<open>provenance ai\<close> have "last (find_pfx Q l) = last (find_pfx Q (l' @ x # y # l2))"
    using \<^marker>\<open>provenance ai\<close> nQ Cons.prems(5) find_pfx_nempty[of x "l' @ x # y # l2" Q] Cons.prems(1)
    by \<^marker>\<open>provenance ai\<close> auto
  moreover \<^marker>\<open>provenance ai\<close> have "last (find_pfx Q (rev l)) = last (find_pfx Q (rev (l' @ x # y # l2)))"
    using \<^marker>\<open>provenance ai\<close> nQ Cons.prems(2,5) find_pfx_append[of Q y "rev l2" "x # rev l'"] find_pfx_append[of Q y "rev l2" "x # rev l' @ [a']"]
    by \<^marker>\<open>provenance ai\<close> auto
  ultimately show ?case
    using \<^marker>\<open>provenance ai\<close> Cons.prems(2,5)
    by \<^marker>\<open>provenance ai\<close> auto
qed

lemma edges_of_path_find_pfx:
  assumes "length p \<ge> 2" "x \<noteq> hd p"
  shows "edges_of_path (find_pfx ((=) x) p) = find_pfx ((\<in>) x) (edges_of_path p)"
  using assms
proof(induction p arbitrary: x)
  case Nil
  then show ?case
    by simp
next
  case cons1: (Cons a' p')
  then show ?case
    using Suc_le_eq
    by (cases p'; simp; fastforce)
qed

lemma find_pfx_append_2:
  "\<exists>l2. l = find_pfx Q l @ l2"
  by (induction l) auto

lemma find_pfx_edges_of_path_alt_list:
  assumes cycle: "odd_cycle p" "alt_path M p" "distinct (tl p)" "v \<in> set p" "v \<noteq> hd p"
  shows "alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path (find_pfx ((=) v) p))" (is ?g1)
        "((last (edges_of_path (find_pfx ((=) v) p))) \<notin> M \<and> (last (edges_of_path (find_pfx ((=) v) (rev p)))) \<in> M) \<or>
                  ((last (edges_of_path (find_pfx ((=) v) p))) \<in> M \<and> (last (edges_of_path (find_pfx ((=) v) (rev p)))) \<notin> M)" (is ?g2)
proof-
  obtain ep where eq: "edges_of_path p = find_pfx ((\<in>) v) (edges_of_path p) @ ep"
    using find_pfx_append_2
    by auto
  then have "alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (find_pfx ((\<in>) v) (edges_of_path p))"
    using \<^marker>\<open>provenance ai\<close> cycle(2) alt_list_append_1[of _ _ "find_pfx ((\<in>) v) (edges_of_path p)" ep]
    by \<^marker>\<open>provenance ai\<close> (auto simp flip: eq)
  moreover have eofp_pfx: "(edges_of_path (find_pfx ((=) v) p)) = (find_pfx ((\<in>) v) (edges_of_path p))"
    using odd_cycleD(1)[OF cycle(1)]
    by (intro edges_of_path_find_pfx cycle; simp)
  ultimately show ?g1
    by simp
  have rev_eofp_pfx: "(edges_of_path (find_pfx ((=) v) (rev p))) = (find_pfx ((\<in>) v) (edges_of_path (rev p)))"
    using odd_cycleD(1,3)[OF cycle(1)] cycle(5)
    by (intro edges_of_path_find_pfx cycle; simp add: hd_rev)
  have rev_eop: "(edges_of_path (rev p)) = rev (edges_of_path p)"
    by (simp add: edges_of_path_rev)
  obtain p' p'' where p'p''[simp]: "p = p' @ (v # p'')"
    using cycle
    by (auto dest: split_list_last)
  show ?g2
    unfolding eofp_pfx rev_eofp_pfx rev_eop
  proof(intro find_pfx_alt_list[where x = "{last p', v}" and y = "{v, hd p''}" and ?l1.0 = "(edges_of_path p')" and ?l2.0 = "(edges_of_path p'')"] cycle, goal_cases)
    case \<^marker>\<open>provenance ai\<close> 1
    show \<^marker>\<open>provenance ai\<close> ?case
      by \<^marker>\<open>provenance human\<close> simp
  next \<^marker>\<open>provenance ai\<close>
    case \<^marker>\<open>provenance ai\<close> 2
    show \<^marker>\<open>provenance ai\<close> ?case
      by \<^marker>\<open>provenance human\<close> simp
  next \<^marker>\<open>provenance ai\<close>
    case \<^marker>\<open>provenance ai\<close> 3
    show \<^marker>\<open>provenance ai\<close> ?case
      using \<^marker>\<open>provenance human\<close> assms(3,5)
      by \<^marker>\<open>provenance human\<close> (intro ballI impI where_is_v; cases p'; auto)
  next \<^marker>\<open>provenance ai\<close>
    case \<^marker>\<open>provenance ai\<close> 4
    show \<^marker>\<open>provenance ai\<close> ?case
    proof \<^marker>\<open>provenance human\<close>-
      have "v \<notin> set p'"
        using cycle
        by (cases p'; auto simp: distinct_append)
      moreover have "v \<notin> set p''"
        using cycle
        by (cases p'; auto simp: distinct_append)
      ultimately show ?thesis
        by (auto simp add: v_in_edge_in_path_gen)
    qed
  next \<^marker>\<open>provenance ai\<close>
    case \<^marker>\<open>provenance ai\<close> 5
    have nn: "p' \<noteq> []" "p'' \<noteq> []"
      using cycle(5) odd_cycleD(3)[OF cycle(1)]
      by \<^marker>\<open>provenance ai\<close> auto
    then \<^marker>\<open>provenance ai\<close> show \<^marker>\<open>provenance ai\<close> ?case
      using \<^marker>\<open>provenance human\<close> edges_of_path_append_3[of p' "v # p''"]
      by (cases p''; auto)
  qed \<^marker>\<open>provenance ai\<close>
qed

text\<open>This is a function that chooses an edge connecting a vertex to another vertex in a given set of
     vertices.\<close>


(*definition choose_con_vert where
  "choose_con_vert vs E v \<equiv> (SOME v'. v' \<in> vs \<and> {v, v'} \<in> E)"*)



lemma path_adj_verts_edge:
  assumes "path E (l1 @ (v1 # v2 # l2))"
  shows "{v1, v2} \<in> E"
  using assms
proof(induction l1 arbitrary: v1)
  case Nil
  then show ?case
    by simp
next 
  case (Cons a1' l1')
  then show ?case 
    using \<^marker>\<open>provenance ai\<close> Cons.prems path_suff[of E "[a1']"]
    by simp
qed

context quot
begin

lemma in_quot_graph_neq_u:
  assumes "v \<in> Vs(quot_graph P M)" "v \<noteq> u"
  shows "v \<in> s"
  using assms good_quot_map
  unfolding Vs_def quot_graph_def
  by (simp; force)

lemma Vs_quotG_subset_Vs_quot_graph:
  "Vs (quotG M) \<subseteq> Vs(quot_graph P M)"
  unfolding Vs_def quot_graph_def
  by auto

lemma in_quotG_neq_u:
  assumes "v \<in> Vs (quotG M)" "v \<noteq> u"
  shows "v \<in> s"
proof-
  have "v \<in> Vs(quot_graph P M)"
    using assms in_quot_graph_neq_u[OF _ assms(2)] Vs_quotG_subset_Vs_quot_graph
    by force
  then show ?thesis
    using in_quot_graph_neq_u assms
    by blast
qed

lemma neq_u_notin_quot_graph:
  assumes "v \<notin> s" "v \<noteq> u"
  shows "v \<notin> Vs (quot_graph P E)"
  using assms
  by (auto dest: in_quot_graph_neq_u)

lemma neq_u_notin_quotG:
  assumes "v \<notin> s" "v \<noteq> u"
  shows "v \<notin> Vs (quotG E)"
  using assms
  using in_quotG_neq_u
  by blast

end


subsection\<open>Quotienting/conracting an augmenting path\<close>

text\<open>We prove an augmenting path in a concrete graph can be abstracted into an augmenting path in a
     quotient graph\<close>

lemma in_odd_cycle_in_M:
  assumes "v \<in> set C" "odd_cycle C" "alt_path M C" "v \<noteq> last C"
  shows "v \<in>  Vs M"
  using assms(1,4)
  using alt_path_vert_is_matched' odd_cycleD(2,3)[OF assms(2)] assms(3)
  by fastforce

lemma matching_edge_incident_on_cycle:
  assumes "odd_cycle C" "alt_path M C" "e \<in> M" "v1 \<in> set C" "v2 \<notin> set C" "{v1, v2} \<subseteq> e" "matching M"
  shows "v1 = last C"
proof(rule ccontr)
  assume "v1 \<noteq> last C"
  then obtain p1 p2 where p1p2: "C = p1 @ v1 # p2" "p1 \<noteq> []" "p2 \<noteq> []"
    using odd_cycleD(3)[OF assms(1)] assms(4) split_list_last
    by fastforce
  have "(edges_of_path p1) @ [{last p1, v1}] = edges_of_path (p1 @ [v1])"
    using edges_of_path_snoc[OF p1p2(2)]
    by auto
  moreover have "edges_of_path (v1 # p2) = {v1, hd p2} # edges_of_path p2"
    using p1p2(3)
    by \<^marker>\<open>provenance ai\<close> (cases p2; auto)
  moreover have "edges_of_path C = (edges_of_path (p1 @ [v1])) @ (edges_of_path (v1 # p2))"
    using edges_of_path_append_2[where p' = "v1 # p2"] p1p2(1)
    by auto
  ultimately have eqC: "edges_of_path C = (edges_of_path p1) @ {last p1, v1} # {v1, hd p2} # edges_of_path p2"
    using p1p2(1)
    by auto
  then have i: "{last p1, v1} \<in> M \<or> {v1, hd p2} \<in> M"
    using odd_cycleD(2)[OF assms(1)] assms(2)[unfolded eqC]
    by (cases "{last p1, v1} \<in> M"; auto dest: alt_list_append_1'')
  have "last p1 \<in> set C" "hd p2 \<in> set C"
    using p1p2
    by auto
  then have ii: "{last p1, v1} \<noteq> e" "{v1, hd p2} \<noteq> e"
    using assms(4-6)
    by fastforce+

  have \<^marker>\<open>provenance ai\<close> "v1 \<in> Vs M"
    using assms(3,6)
    by (auto simp: Vs_def)
  then \<^marker>\<open>provenance ai\<close> have "\<exists>!f. f \<in> M \<and> v1 \<in> f"
    using \<^marker>\<open>provenance ai\<close> assms(7)
    unfolding matching_def2
    by \<^marker>\<open>provenance ai\<close> blast
  then \<^marker>\<open>provenance ai\<close> show False
    using i ii assms(3,6)
    by \<^marker>\<open>provenance ai\<close> auto
qed

context quot
begin

lemma not_in_quot_matching_not_in_matching_2:
  assumes match: "matching M" "M \<subseteq> E" and
          cycle: "odd_cycle p" "alt_path M p" and
          quot: "s = (Vs E) - set p" and
          notin: "last p \<notin> Vs M"
        shows "u \<notin> Vs (quotG M)"
proof(rule ccontr; simp)
  assume "u \<in> Vs (quotG M)"
  then obtain quote where quote: "quote \<in> quotG M" "u \<in> quote"
    unfolding Vs_def
    by auto
  then obtain e v w where evw: "e \<in> M" "quote = P ` e" "v \<in> e" "v \<in> s" "w \<in> e" "w \<notin> s"
    unfolding quot_graph_def
    using good_quot_map
    by auto
  then have "w \<in> Vs E"
    unfolding Vs_def
    using match(2)
    by auto
  then have "w \<in> set p" "v \<notin> set p"
    using quot evw
    by auto
  then have "w = last p"
    using matching_edge_incident_on_cycle[OF cycle evw(1)] evw match(1)
    by blast
  then show False
    using notin evw
    unfolding Vs_def
    by auto
qed

lemma edge_in_graph_edge_in_quot:
  assumes "v \<in> s" "w \<notin> s" "{v, w} \<in> E" 
  shows "{v, u} \<in> quotG E "
proof \<^marker>\<open>provenance ai\<close>-
  have \<^marker>\<open>provenance human\<close> "P ` {v, w} = {v, u}"
    using \<^marker>\<open>provenance ai\<close> assms(1,2)
    by (simp add: insert_commute)
  then have \<^marker>\<open>provenance human\<close> "{v, u} \<in> quot_graph P E"
    using edge_in_graph_in_quot[OF assms(3), of P]
    by \<^marker>\<open>provenance ai\<close> simp
  moreover have \<^marker>\<open>provenance human\<close> "{v, u} \<noteq> {u}"
    using assms(1) good_quot_map(1)
    by \<^marker>\<open>provenance ai\<close> auto
  ultimately show ?thesis
    by simp
qed

text\<open>Constructing an absrtact aumenting path from a concrete path, given that the blossom's base is
     not matched.\<close>

lemma aug_path_works_in_contraction_unmatched_base:
  assumes cycle: "odd_cycle C" "alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path C)" and
    aug_path: "matching_augmenting_path M p" "path E p" "distinct p" "(set p) \<inter> (set C) \<noteq> {}" "last C \<notin> Vs M" and 
    matching: "matching M" "M \<subseteq> E" and
    quot: "s = (Vs E) - set C" "u \<notin>  Vs E"(* and
    graph: "dblton_graph E"*)
  shows "\<exists>p'. matching_augmenting_path (quotG M) p' \<and>
              path (quotG E) p' \<and>
              distinct p'"
proof-
  have alt_list_p1_u: False
    if p1_nempty: "p1 \<noteq> []" and wx: "p = p1 @ w # p2" "w \<in> set C" and
      p1_subset_s: "set p1 \<subseteq> s" and last_p1_w_in_m: "{last p1, w} \<in> M"
    for w and p p1 p2:: "'a list"
  proof-
    have False
      if "v \<in> s" and w: "w \<in> set C" and last_p1_w_in_m: "{v,w}\<in>M"
      for v w
    proof-
      have "v \<notin> set C"
        using quot \<open>v \<in> s\<close>
        by auto
      hence "w = last C"
        using matching_edge_incident_on_cycle[OF cycle _ _ _ _ matching(1)]
          w last_p1_w_in_m
          (*since p1 is disjoint with the cycle, then it can only be matched with the base*)
        by blast
      then show False
        using aug_path(5) last_p1_w_in_m
        unfolding Vs_def
        by auto
    qed
    thus False
      using last_in_set that
      by blast
  qed

  have path_p1_u: "path (quotG E) p1 \<and> {last p1, u} \<in> quotG E"
    if p1_nempty: "p1 \<noteq> []" and
      wx: "p = p1 @ w # p2" "w \<in> set C" and
      p1_subset_s: "set p1 \<subseteq> s" and
      aug_path: "path E p"
    for w and p p1 p2:: "'a list"
  proof-
    have last_p1_in_s: "last p1 \<in> s"
      using p1_nempty p1_subset_s
      by (auto intro: last_in_set)
    have "{last p1, u} \<in> quotG E"
    proof-
      have "last p1 \<in> Vs E"
        using last_p1_in_s quot(1)
        by blast
      then have "last p1 \<noteq> u"
        using quot(2)
        by auto
      moreover have "w \<notin> s"
        using quot(1) wx(2)
        by auto
      moreover have "{last p1, w} \<in> E"
      proof-
        have *: "p1 @ [w] = butlast p1 @ last p1 # w # []"
          using p1_nempty
          by auto
        have "p = (p1 @ [w]) @ p2"
          using wx(1)
          by auto
        have \<^marker>\<open>provenance ai\<close> "path E (p1 @ [w])"
          using aug_path path_pref[of E "p1 @ [w]" p2] wx(1)
          by auto
        then have "path E (butlast p1 @ (last p1 # w # []))"
          by (simp only: *[symmetric])
        then show ?thesis
          by \<^marker>\<open>provenance ai\<close> (rule path_adj_verts_edge[of E "butlast p1" "last p1" w "[]"])
      qed
      ultimately show ?thesis 
        by (intro edge_in_graph_edge_in_quot[OF last_p1_in_s]; auto)
    qed
    moreover have path_p1: "path E p1"
      using aug_path path_pref wx p1_subset_s
      by auto
    then have path_p1: "path (quotG E) p1"
      using p1_subset_s qug_path_iff_case_1_ii quot(1)
      by blast
    ultimately show "path (quotG E) p1 \<and> {last p1, u} \<in> quotG E"
      by auto
  qed     


  have path_u_p3: "path (quotG E) (u # p3)"
    if wx: "p = p1 @ x # p3" "x \<in> set C" "\<forall>x\<in>set p3. x \<notin> set C" and
      aug_path: "path E p" and
      p3_subset_s: "set p3 \<subseteq> s" and
      p3_nempty: "p3 \<noteq> []"
    for p1 x p3 p
  proof-
    have path_xp3: "path E (x # p3)"
      using wx(1) aug_path path_suff
      by blast
    then have "path E p3"
      by (cases p3; auto)
    then have "path (quotG E) p3"
      using p3_subset_s qug_path_iff_case_1_ii quot(1)
      by blast
    moreover have "{hd p3, u} \<in> quotG E"
    proof-
      have "hd p3 \<in> Vs E"
        using p3_nempty p3_subset_s quot(1)
        using hd_in_set
        by blast
      then have "hd p3 \<noteq> u"
        using quot(2)
        by auto
      moreover have "x \<notin> s"
        using quot(1) wx(2)
        by auto
      moreover have "{x, hd p3} \<in> E"
        using path_xp3 p3_nempty
        by(cases p3; auto) 
      moreover have "hd p3 \<in> s"
        using p3_subset_s p3_nempty
        by auto
      ultimately show ?thesis 
        by (intro edge_in_graph_edge_in_quot[where w = x]; auto simp add: insert_commute)
    qed
    ultimately show "path (quotG E) (u # p3)"
      using p3_nempty
      by(cases p3; auto simp add: insert_commute)
  qed 

  have "set p \<subseteq> Vs E"
    using aug_path(2)
    by (simp add: subset_path_Vs)
  then have u_nin_p: "u \<notin> set p"
    using quot
    by auto

  have "u \<notin> Vs E"
    using quot
    by auto
  then have u_nin_VsM: "u \<notin> Vs M"
    using matching(2)
    by (auto simp add: Vs_def)

  show ?thesis
  proof(cases "\<exists>v. (set p) \<inter> (set C) = {v}")
    have alt_list_u_p3: "alt_path (quotG M) (u # p3)" 
      if wx: "p = p1 @ x # p3" "x \<in> set C" "\<forall>x\<in>set p1. x \<notin> set C" "\<forall>x\<in>set p3. x \<notin> set C" and
        aug_path: "matching_augmenting_path M p" "distinct p" "last C \<notin> Vs M" and
        p3_subset_s: "set p3 \<subseteq> s" and
        p3_nempty[simp]: "p3 \<noteq> []"
      for p1 x p3 p
    proof-
      have "{last p1, x} \<noteq> {hd p3 , x}" if "p1 \<noteq> []"
      proof-
        have "last p1 \<noteq> hd p3"
          using aug_path(2) wx(1) that p3_nempty
          by (auto simp: distinct_append dest: last_in_set hd_in_set)
        then show ?thesis
          by (auto simp add: doubleton_eq_iff)
      qed
      then have hdp3_x_nin_M: "{x, hd p3} \<notin> M"
        using matching(1)
        unfolding Vs_def matching_def2
        using \<^marker>\<open>provenance ai\<close> alt_list_p1_u[of "rev p3" "rev p" x "rev p1"] p3_nempty p3_subset_s wx(1,2)
        by (auto simp: last_rev insert_commute)
      have "edges_of_path p = edges_of_path (p1  @ [x])@ edges_of_path (x # p3)"
        unfolding wx(1)
        using edges_of_path_append_2[where p' = "x # p3"]
        by \<^marker>\<open>provenance ai\<close> simp
      then have "alt_path M (x # p3) \<or> 
                alt_list (\<lambda>e. e \<in> M) (\<lambda>e. e \<notin> M) (edges_of_path (x # p3))"
        using matching_augmenting_path_feats(2)[OF aug_path(1)]
        by (intro conjunct2[OF alt_list_append_1]; auto)
      then have *: "alt_path M (x # p3)"
        using hdp3_x_nin_M
        by(cases p3; auto simp: alt_list_step)
      then have "alt_list (\<lambda>e. e \<in> M) (\<lambda>e. e \<notin> M) (edges_of_path p3)"
        by(cases p3; auto simp: alt_list_step)
      then have "alt_list (\<lambda>e. e \<in> quotG M) (\<lambda>e. e \<notin> quotG M) (edges_of_path p3)"
        by (rule alt_list_cong; use edge_of_path_in_graph_iff_in_quot[OF p3_subset_s _ \<open>M \<subseteq> E\<close>] in blast)
      moreover have "{u, hd p3} \<notin> quotG M"
      proof(rule ccontr)
        have hd_p3_in_s: "hd p3 \<in> s"
          using p3_nempty p3_subset_s
          by (auto intro: hd_in_set)
        assume "\<not> {u, hd p3} \<notin> quotG M"
        then have "{u, hd p3} \<in> quotG M"
          by simp
        then have "\<exists>v. {v, hd p3} \<in> M \<and> v \<notin> s"
          using \<^marker>\<open>provenance ai\<close> hd_p3_in_s matching(2) edge_in_quotG_2'_doubleton[of "hd p3" M]
          by (auto simp: insert_commute)
        moreover have "v \<in> set C" if "v \<in> Vs E" "v \<notin> s" for v
          using that quot(1)
          by fastforce
        ultimately obtain v where v: "{v, hd p3} \<in> M" "v \<in> set C"
          using quot(1) matching(2)
          unfolding Vs_def
          by auto
        then have v_eq_last_C: "v = last C"
        proof-
          have hdp3_nin_C: "hd p3 \<notin> set C"
            using wx
            by (simp add: p3_nempty)
          show ?thesis
            using matching_edge_incident_on_cycle[OF cycle v hdp3_nin_C _ matching(1)]
            by simp
        qed
        then have lastC_in_M: "last C \<in> Vs M"
          using v(1)
          unfolding Vs_def
          by auto
        then show False
          using aug_path(3)
          by simp
      qed
      ultimately show "alt_path (quotG M) (u # p3)" 
        using p3_nempty
        by (auto simp add:  alt_list_step neq_Nil_conv simp del: p3_nempty)
    qed

    case T1: True
    then obtain x where x: "set p \<inter> set C = {x}"
      by auto
    then have "\<exists>p1 p2. p = p1 @ x # p2 \<and> (\<forall>x\<in>set p1. x \<notin> set C) \<and> (\<forall>x\<in>set p2. x \<notin> set C)"
      using aug_path(3)
      by (intro split_list_pure_pref_suff; auto)
    then obtain p1 p2 where p1p2x[simp]: "p = p1 @ x # p2" "x \<in> set C" "\<forall>x\<in>set p1. x \<notin> set C" "\<forall>x\<in>set p2. x \<notin> set C"
      using x
      by auto
    have p1_subset_s[simp]: "set p1 \<subseteq> s"
    proof-
      have "path E p1"
        using p1p2x(1) aug_path(2) path_pref
        by (auto dest: path_pref)
      then show ?thesis
        using quot p1p2x(3)
        using mem_path_Vs
        by fastforce
    qed
    have p2_subset_s[simp]: "set p2 \<subseteq> s"
    proof-
      have "path E p2"
        using p1p2x(1) aug_path(2) path_suff[of E "p1 @ [x]" p2]
        by \<^marker>\<open>provenance ai\<close> auto
      then show ?thesis
        using quot p1p2x(4)
        using mem_path_Vs
        by fastforce
    qed

    show ?thesis
    proof(cases "p1 = []")
      case p1_empty: True
      show ?thesis
      proof(cases "p2 = []")
        case p2_empty: True
        then have False
          using p1p2x matching_augmenting_path_feats(1)[OF aug_path(1)] p1_empty
          by auto
        then show ?thesis
          by simp
      next
        case p2_nempty: False
        have "x \<notin> Vs M"
          using matching_augmenting_path_feats(3)[OF aug_path(1)] p1p2x(1) p1_empty
          by auto
        then have "alt_path (quotG M) (u # p2)"
          using alt_list_u_p3[OF p1p2x aug_path(1,3,5) p2_subset_s p2_nempty]
          by auto
        moreover have "path (quotG E) (u # p2)"
          using path_u_p3[OF p1p2x(1,2,4) aug_path(2) p2_subset_s p2_nempty]
          .
        moreover have "distinct (u # p2)"
          using p1p2x(1) u_nin_p aug_path(3)
          by auto
        moreover have "last (u # p2) \<notin> Vs (quotG M)"
        proof \<^marker>\<open>provenance ai\<close>-
          have "last p2 \<in> s"
            by (rule subsetD[OF p2_subset_s last_in_set[OF p2_nempty]])
          moreover have \<^marker>\<open>provenance human\<close> "last p2 \<notin> Vs M"
            using p1p2x(1) matching_augmenting_path_feats(4)[OF aug_path(1)] p1_empty p2_nempty
            by \<^marker>\<open>provenance ai\<close> auto
          ultimately have \<^marker>\<open>provenance human\<close> "last p2 \<notin> Vs (quotG M)"
            using vert_in_graph_iff_in_quot_diff_u \<open>M \<subseteq> E\<close>
            by \<^marker>\<open>provenance ai\<close> blast
          then show ?thesis
            using p2_nempty
            by simp
        qed
        moreover have "hd (u # p2) \<notin> Vs (quotG M)"
          using not_in_quot_matching_not_in_matching_2[OF matching(1,2) cycle quot(1) aug_path(5)]
          by simp
        moreover have "length (u # p2) \<ge> 2"
          using p2_nempty
          by (auto simp add: neq_Nil_conv)
        ultimately show ?thesis
          unfolding matching_augmenting_path_def
          by blast
      qed
    next
      case p1_nempty[simp]: False
      show ?thesis
      proof(cases "p2 = []")
        case p2_empty: True
        have "alt_path (quotG M) (u # (rev p1))"
          using aug_path(3) distinct_rev
          by \<^marker>\<open>provenance ai\<close> (intro alt_list_u_p3[of "rev p" "rev p2" x] matching_augmenting_path_rev[OF aug_path(1)] aug_path(5); auto)
        moreover have "path (quotG E) (u # (rev p1))"
          by (intro path_u_p3[of "rev p" "rev p2" x] rev_path_is_path[OF aug_path(2)]; simp)
        moreover have "distinct (u # (rev p1))"
          using p1p2x(1) u_nin_p aug_path(3)
          by auto
        moreover have "hd (u # (rev p1)) \<notin> Vs (quotG M)"
          using not_in_quot_matching_not_in_matching_2[OF matching(1,2) cycle quot(1) aug_path(5)]
          by simp
        moreover have "last (u # (rev p1)) \<notin> Vs (quotG M)"
        proof \<^marker>\<open>provenance ai\<close>-
          have "hd p1 \<in> s"
            by \<^marker>\<open>provenance human\<close> (rule subsetD[OF p1_subset_s hd_in_set[OF p1_nempty]])
          moreover have \<^marker>\<open>provenance human\<close> "hd p1 \<notin> Vs M"
            using p1p2x(1) matching_augmenting_path_feats(3)[OF aug_path(1)] p1_nempty
            by \<^marker>\<open>provenance ai\<close> auto
          ultimately have \<^marker>\<open>provenance human\<close> "hd p1 \<notin> Vs (quotG M)"
            using vert_in_graph_iff_in_quot_diff_u \<open>M \<subseteq> E\<close>
            by \<^marker>\<open>provenance ai\<close> blast
          then show ?thesis
            using p1_nempty
            by \<^marker>\<open>provenance human\<close> (simp add: last_rev)
        qed
        moreover have "length (u # (rev p1)) \<ge> 2"
          by (auto simp add: leI)
        ultimately show ?thesis
          unfolding matching_augmenting_path_def
          by blast
      next
        case p2_nempty[simp]: False
        show ?thesis
        proof(cases "{last p1, x} \<in> M")
          case lastp1_x_in_M: True
          have False
            by(rule alt_list_p1_u[OF p1_nempty p1p2x(1,2) p1_subset_s lastp1_x_in_M])+
          then show ?thesis
            by simp
        next
          case p1_x_nin_M: False
          have hdp2_x_in_M: "{hd p2, x} \<in> M"
          proof-
            have rw1: "edges_of_path p = (edges_of_path (p1 @ [x])) @ edges_of_path (x # p2)"
              using edges_of_path_append_2 p1p2x(1)
              by fastforce
            have rw2: "(edges_of_path (p1 @ [x])) = (edges_of_path p1) @ [{last p1, x}]"
              using p1_nempty
              by (simp add: edges_of_path_snoc)
            have rw3: "(edges_of_path (x # p2)) =  {hd p2, x} # (edges_of_path p2)"
              using p2_nempty
              by (auto simp add: neq_Nil_conv simp del: p2_nempty)
            show ?thesis
              using matching_augmenting_path_feats(2)[OF aug_path(1), unfolded rw1 rw2 rw3]
              using \<^marker>\<open>provenance ai\<close> alt_list_append_1'[of "\<lambda>e. e \<notin> M" "\<lambda>e. e \<in> M" "edges_of_path p1 @ [{last p1, x}]" "{hd p2, x} # edges_of_path p2"]
                    p1_x_nin_M
              by (auto simp: alt_list_step)
          qed
          have False
            using hdp2_x_in_M
            by \<^marker>\<open>provenance ai\<close> (intro alt_list_p1_u[of "rev p2" "rev p" x "rev p1"]; simp add: last_rev)
          then show ?thesis
            by simp
        qed
      qed
    qed
  next
    case F1: False
    then obtain w' x' where wx': "w' \<in> set p" "w' \<in> set C" "x' \<in> set p" "x' \<in> set C" "w' \<noteq> x'"
      using aug_path(4)
      by blast
    then have "\<exists>p1 p2 p3 w x. p = p1 @ w # p2 @ x # p3 \<and> w \<in> set C \<and> x \<in> set C \<and> w \<noteq> x \<and> (\<forall>x\<in>set p1. x \<notin> set C) \<and> (\<forall>x\<in>set p3. x \<notin> set C)"
      using two_mem_list_split''[OF wx'(1,3) _ _ _ aug_path(3)]
      by auto
    then obtain w x p1 p2 p3 where wx[simp]: "p = p1 @ w # p2 @ x # p3" "w \<in> set C" "x \<in> set C" "w \<noteq> x" "(\<forall>x\<in>set p1. x \<notin> set C)" " (\<forall>x\<in>set p3. x \<notin> set C)"
      by auto
    have p1_subset_s[simp]: "set p1 \<subseteq> s"
    proof-
      have "path E p1"
        using wx(1) aug_path(2) path_pref
        by (auto dest: path_pref)
      then show ?thesis
        using quot wx(5)
        using mem_path_Vs
        by fastforce
    qed
    have p3_subset_s: "set p3 \<subseteq> s"
    proof-
      have "path E p3"
        using wx(1) aug_path(2) path_suff[of E "p1 @ w # p2 @ [x]" p3]
        by \<^marker>\<open>provenance ai\<close> auto
      then show ?thesis
        using quot wx(6)
        using mem_path_Vs
        by fastforce
    qed
    have alt_list_u_p3: "alt_path (quotG M) (u # p3)" 
      if wx: "p = p1 @ w # p2 @ x # p3" "w \<in> set C" "\<forall>x\<in>set p1. x \<notin> set C" "\<forall>x\<in>set p3. x \<notin> set C" and
        aug_path: "matching_augmenting_path M p" "last C \<notin> Vs M" and
        p3_subset_s: "set p3 \<subseteq> s" and
        "{x, hd p3} \<notin> M" and
        p3_nempty: "p3 \<noteq> []"
      for p1 w p2 x p3 p
    proof-
      have "edges_of_path p = edges_of_path (p1 @ w # p2 @ [x])@ edges_of_path (x # p3)"
        unfolding wx(1)
        using edges_of_path_append_2[where p' = "x # p3" and p = "p1 @ w # p2"]
        by \<^marker>\<open>provenance ai\<close> simp
      then have "alt_path M (x # p3) \<or> 
                alt_list (\<lambda>e. e \<in> M) (\<lambda>e. e \<notin> M) (edges_of_path (x # p3))"
        using matching_augmenting_path_feats(2)[OF aug_path(1)]
        by (intro conjunct2[OF alt_list_append_1]; auto)
      hence *: "alt_path M (x # p3)"
        using \<open>{x, hd p3} \<notin> M\<close>
        by(cases p3; auto simp: alt_list_step alt_list_empty)
      hence "alt_list (\<lambda>e. e \<in> M) (\<lambda>e. e \<notin> M) (edges_of_path p3)"
        using p3_nempty
        by(cases p3; auto simp: alt_list_step)
      then have "alt_list (\<lambda>e. e \<in> quotG M) (\<lambda>e. e \<notin> quotG M) (edges_of_path p3)"
        by (rule alt_list_cong; use edge_of_path_in_graph_iff_in_quot[OF p3_subset_s _ \<open>M \<subseteq> E\<close>] in blast)
      moreover have "{u, hd p3} \<notin> quotG M"
      proof(rule ccontr)
        have hd_p3_in_s: "hd p3 \<in> s"
          using p3_nempty p3_subset_s
          by (auto intro: hd_in_set)
        assume "\<not> {u, hd p3} \<notin> quotG M"
        then have "{u, hd p3} \<in> quotG M"
          by simp
        then have "\<exists>v. {v, hd p3} \<in> M \<and> v \<notin> s"
          using \<^marker>\<open>provenance ai\<close> hd_p3_in_s matching(2) edge_in_quotG_2'_doubleton[of "hd p3" M]
          by (auto simp: insert_commute)
        moreover have "v \<in> set C" if "v \<in> Vs E" "v \<notin> s" for v
          using that quot(1)
          by fastforce
        ultimately obtain v where v: "{v, hd p3} \<in> M" "v \<in> set C"
          using quot(1) matching(2)
          unfolding Vs_def
          by auto
        then have v_eq_last_C: "v = last C"
        proof-
          have hdp3_nin_C: "hd p3 \<notin> set C"
            using wx
            by (simp add: p3_nempty)
          show ?thesis
            using matching_edge_incident_on_cycle[OF cycle v hdp3_nin_C _ matching(1)]
            by simp
        qed
        then have lastC_in_M: "last C \<in> Vs M"
          using v(1)
          unfolding Vs_def
          by auto
        then show False
          using aug_path(2)
          by auto
      qed
      ultimately show "alt_path (quotG M) (u # p3)" 
        using p3_nempty
        by (auto simp add:  alt_list_step neq_Nil_conv)
    qed

    have x_hdp3_nin_M: "{x, hd p3} \<notin> M"
      if w_nin_M: "w \<notin> Vs M" and
        p3_nempty: "p3 \<noteq> []" and
        wx: "w \<in> set C" "x \<in> set C" "w \<noteq> x" "(\<forall>x\<in>set p3. x \<notin> set C)"
      for w x and p p1 p2 p3::"'a list"
    proof-
      have x_eq_last_C: "x = last C" if "{x, hd p3} \<in> M"
      proof-
        have hdp3_nin_C: "hd p3 \<notin> set C"
          using wx
          by (simp add: that p3_nempty)
        show ?thesis
          using matching_edge_incident_on_cycle[OF cycle that(1) wx(2) hdp3_nin_C _ matching(1)]
          by simp
      qed
      show ?thesis 
        using w_nin_M wx in_odd_cycle_in_M[OF _ cycle] x_eq_last_C
        by blast
    qed

    show ?thesis
    proof(cases "p1 = []")
      case T2: True
      have w_nin_M: "w \<notin> Vs M"
        using wx(1) matching_augmenting_path_feats(3)[OF aug_path(1)] T2
        by auto
      have p3_nempty: "p3 \<noteq> []"
      proof(rule ccontr)
        assume "\<not> p3 \<noteq> []"
        then have "x \<notin> Vs M"
          using wx(1) matching_augmenting_path_feats(4)[OF aug_path(1)]
          by auto
        then have \<^marker>\<open>provenance ai\<close> "x = last C"
          using \<^marker>\<open>provenance human\<close> wx(3) in_odd_cycle_in_M[OF _ cycle]
          by blast
        moreover \<^marker>\<open>provenance ai\<close> have \<^marker>\<open>provenance ai\<close> "w = last C"
          using \<^marker>\<open>provenance human\<close> w_nin_M wx(2) in_odd_cycle_in_M[OF _ cycle]
          by blast
        ultimately \<^marker>\<open>provenance ai\<close> show False
          using \<^marker>\<open>provenance ai\<close> wx(4)
          by simp
      qed
      have "{x, hd p3} \<notin> M"
        using x_hdp3_nin_M[OF w_nin_M p3_nempty wx(2,3,4,6)] .
      then have "alt_path (quotG M) (u # p3)"
        using alt_list_u_p3[OF wx(1,2,5,6) aug_path(1,5) p3_subset_s _ p3_nempty] w_nin_M
        by simp          
      moreover have "path (quotG E) (u # p3)"
        using path_u_p3[OF _ _ _ aug_path(2) p3_subset_s p3_nempty] wx
        by auto
      moreover have "distinct (u # p3)"
        using wx(1) u_nin_p aug_path(3)
        by auto
      moreover have "hd (u # p3) \<notin> Vs (quotG M)"
        using not_in_quot_matching_not_in_matching_2[OF matching(1,2) cycle quot(1) aug_path(5)]
        by simp
      moreover have "last (u # p3) \<notin> Vs (quotG M)"
      proof \<^marker>\<open>provenance ai\<close>-
        have "last p3 \<in> s"
          by (rule subsetD[OF p3_subset_s last_in_set[OF p3_nempty]])
        moreover have \<^marker>\<open>provenance human\<close> "last p3 \<notin> Vs M"
          using wx(1) matching_augmenting_path_feats(4)[OF aug_path(1)] p3_nempty
          by \<^marker>\<open>provenance ai\<close> auto
        ultimately have \<^marker>\<open>provenance human\<close> "last p3 \<notin> Vs (quotG M)"
          using vert_in_graph_iff_in_quot_diff_u \<open>M \<subseteq> E\<close>
          by \<^marker>\<open>provenance ai\<close> blast
        then show ?thesis
          using p3_nempty
          by simp
      qed
      moreover have "length (u # p3) \<ge> 2"
        using p3_nempty
        by (auto simp add: neq_Nil_conv)
      ultimately show ?thesis
        unfolding matching_augmenting_path_def
        by blast
    next
      case p1_nempty[simp]: False
      then have rev_p1_nempty: "rev p1 \<noteq> []"
        by auto
      show ?thesis
      proof(cases "{last p1, w} \<in> M")
        case lastp1_w_in_M: True
        have False
          by(rule alt_list_p1_u[OF p1_nempty wx(1) wx(2) p1_subset_s lastp1_w_in_M])+
        then show ?thesis
          by simp
      next
        case F4: False
        have "alt_path (quotG M) (u # rev p1)"
          using F4
          by \<^marker>\<open>provenance ai\<close> (intro alt_list_u_p3[of "rev p" "rev p3" x "rev p2" w] matching_augmenting_path_rev[OF aug_path(1)] aug_path(5); simp add: insert_commute hd_rev)
        moreover have "path (quotG E) (u # (rev p1))"
          by (intro path_u_p3[of "rev p" "rev (p2 @ x # p3)" w] rev_path_is_path[OF aug_path(2)]; auto)
        moreover have "distinct (u # (rev p1))"
          using u_nin_p aug_path(3)
          by auto
        moreover have "hd (u # (rev p1)) \<notin> Vs (quotG M)"
          using not_in_quot_matching_not_in_matching_2[OF matching(1,2) cycle quot(1) aug_path(5)]
          by simp
        moreover have "last (u # (rev p1)) \<notin> Vs (quotG M)"
        proof \<^marker>\<open>provenance ai\<close>-
          have "hd p1 \<in> s"
            by \<^marker>\<open>provenance human\<close> (rule subsetD[OF p1_subset_s hd_in_set[OF p1_nempty]])
          moreover have \<^marker>\<open>provenance human\<close> "hd p1 \<notin> Vs M"
            using wx(1) matching_augmenting_path_feats(3)[OF aug_path(1)] p1_nempty
            by \<^marker>\<open>provenance ai\<close> auto
          ultimately have \<^marker>\<open>provenance human\<close> "hd p1 \<notin> Vs (quotG M)"
            using vert_in_graph_iff_in_quot_diff_u \<open>M \<subseteq> E\<close>
            by \<^marker>\<open>provenance ai\<close> blast
          then show ?thesis
            using p1_nempty
            by \<^marker>\<open>provenance human\<close> (simp add: last_rev)
        qed
        moreover have "length (u # (rev p1)) \<ge> 2"
          by (simp add: Suc_leI)
        ultimately show ?thesis
          unfolding matching_augmenting_path_def
          by blast
      qed
    qed
  qed
qed

lemma aug_path_works_in_contraction_unmatched_base':
  assumes cycle: "odd_cycle C" "alt_path M C" and
    aug_path: "matching_augmenting_path M p" "path E p" "distinct p" "last C \<notin> Vs M" and 
    matching: "matching M" "M \<subseteq> E" and
    quot: "s = (Vs E) - set C" "u \<notin>  Vs E"(* and
    graph: "dblton_graph E"*)
  shows "\<exists>p'. matching_augmenting_path (quotG M) p' \<and>
              path (quotG E) p' \<and>
              distinct p'"
proof(cases "(set p) \<inter> (set C) \<noteq> {}")
  case True
  then show ?thesis
    using assms aug_path_works_in_contraction_unmatched_base
    by (auto elim!: )
next
  case False
  then have "(set p) \<inter> (set C) = {}"
    by simp
  then have "set p \<subseteq> s"
    using aug_path(2) quot(1) subset_path_Vs 
    by fastforce
  moreover have "s \<subseteq> Vs E"
    by (simp add: quot(1))
  ultimately have "matching_augmenting_path (quotG M) p"
                  "path (quotG E) p"
    using qug_path_iff_case_1_i qug_path_iff_case_1_ii
    using aug_path(1,2) \<open>M \<subseteq> E\<close>
    by blast+
  then show ?thesis
    unfolding matching_augmenting_path_def
    using aug_path(3)
    by auto
qed

text\<open>Handling the more general case by taking the symmetric difference of the stem\<close>

lemma u_nin_edge_in_quot:
  assumes "u \<notin> qe" "qe \<in> quotG M"
  shows "qe \<subseteq> s"
  using assms
  by (force simp:  quot_graph_def image_def)

lemma quot_edge_inter_s:
  assumes "qe \<in> quotG M" "M \<subseteq> E"
  shows "\<exists>e \<in> M. qe \<inter> s \<subseteq> e"
proof(cases "u \<in> qe")
  case True
  then show ?thesis
    using edge_in_quot_in_graph_2''[OF assms(1) _ assms(2)]
    by force
next
  case False
  then have "qe \<subseteq> s"
    using u_nin_edge_in_quot[OF _ assms(1)]
    by simp
  then have "qe \<in> M"
    using assms edge_in_quot_in_graph_1'
    by auto
  then show ?thesis
    by auto
qed

lemma quot_is_matching:
  assumes "{e. e \<in> M \<and> (\<exists>v\<in>e. v \<notin> s) \<and> (\<exists>v\<in>e. v \<in> s)} \<subseteq> {dume}"
    "matching M" "M \<subseteq> E"
  shows "matching (quotG M)"
proof(rule ccontr)
  assume "\<not> matching (quotG M)"
  then obtain v where v: "v\<in>Vs (quotG M)" "(\<forall>e\<in>quotG M. \<exists>e'\<in>quotG M. v \<in> e' \<and> e \<noteq> e')"
    by (auto simp add: matching_def2, insert vs_member, fastforce)
  moreover obtain qe where qe: "v \<in> qe" "qe \<in> quotG M"
    using v(1)
    unfolding Vs_def
    by auto 
  ultimately obtain qe' where qe': "v \<in> qe'" "qe \<noteq> qe'" "qe' \<in> quotG M"
    by (auto dest: bspec[of _ _ qe])
  have \<^marker>\<open>provenance ai\<close> aux2: "\<exists>w. w \<in> qq \<and> w \<noteq> u \<and> w \<in> s \<and> qq = {u, w}" if "qq \<in> quotG M" "u \<in> qq" for qq
    using \<^marker>\<open>provenance human\<close> that assms(3) good_quot_map(1) dblton_E
    unfolding \<^marker>\<open>provenance human\<close> quot_graph_def
    by \<^marker>\<open>provenance human\<close> (auto simp: image_iff)
  show False
  proof(cases "v \<in> s")
    text\<open>if v in s, then due to the way the quot mapping works, and since qe, qe' in quotG M,
      we will have two different matched edges in M that both include M. This leads to a
      contradiction.\<close>
    case True
    have \<^marker>\<open>provenance ai\<close> aux: "\<exists>e\<in>M. qq = P ` e \<and> v \<in> e" if "qq \<in> quotG M" "v \<in> qq" for qq
      using \<^marker>\<open>provenance human\<close> that True good_quot_map(1)
      unfolding \<^marker>\<open>provenance human\<close> quot_graph_def
      by \<^marker>\<open>provenance human\<close> (auto simp: image_iff)
    then obtain e e' where e: "v \<in> e" "v \<in> e'" "e \<in> M" "e' \<in> M" "e \<noteq> e'"
      using aux[OF qe(2) qe(1)] aux[OF qe'(3) qe'(1)] qe'(2)
      by \<^marker>\<open>provenance ai\<close> auto
    moreover have "v \<in> Vs M"
      using True \<open>M\<subseteq>E\<close>
      by (simp add: v(1) vert_in_graph_iff_in_quot_diff_u)
    ultimately show ?thesis
      using assms(2)
      unfolding matching_def2
      by auto
  next
    text\<open>if v = u, then we have two edges that cross from s to outside of s, which violates our first
      assumption.\<close>
    case False
    then have vu: "v = u"
      using in_quotG_neq_u v(1) \<open>M \<subseteq> E\<close>
      by blast
    moreover obtain w x where wx: "w \<noteq> x" "w \<in> qe" "w \<noteq> u" "w \<in> s" "x \<in> qe'" "x \<noteq> u" "x \<in> s"
    proof \<^marker>\<open>provenance ai\<close>-
      obtain \<^marker>\<open>provenance human\<close> w where w: "w \<in> qe" "w \<noteq> u" "w \<in> s" "qe = {u, w}"
        using aux2[OF qe(2)] qe(1) vu
        by \<^marker>\<open>provenance ai\<close> auto
      obtain \<^marker>\<open>provenance human\<close> x where x: "x \<in> qe'" "x \<noteq> u" "x \<in> s" "qe' = {u, x}"
        using aux2[OF qe'(3)] qe'(1) vu
        by \<^marker>\<open>provenance ai\<close> auto
      show thesis
        using that w x qe'(2)
        by auto
    qed
    ultimately obtain e e' v1 v2 where ee': "e \<in> M" "e' \<in> M" "w \<in> e" "x \<in> e'" "v1 \<in> e" "v2 \<in> e'"
                                            "v1 \<notin> s" "v2 \<notin> s" "e \<noteq> e'"
      using edge_in_quot_in_graph_2''[OF qe(2)] qe(1) edge_in_quot_in_graph_2''[OF qe'(3)] qe'(1,2)
            \<open>M\<subseteq>E\<close>
      by auto
    then have "e \<in> {e \<in> M. (\<exists>v\<in>e. v \<notin> s) \<and> (\<exists>v\<in>e. v \<in> s)}"
              "e' \<in> {e. e \<in> M \<and> (\<exists>v\<in>e. v \<notin> s) \<and> (\<exists>v\<in>e. v \<in> s)}"
      using wx(4,7)
      by auto
    moreover have "e \<noteq> dume \<or> e' \<noteq> dume"
      using ee'(9)
      by auto
    ultimately show False
      using assms(1)
      by auto
  qed
qed

lemma image_edge_sing_u:
  assumes "e \<inter> s = {}" "e \<noteq> {}"
  shows "P ` e = {u}"
      using assms
      unfolding image_def
      using good_quot_map
      by auto

lemma finite_quot:
  assumes "finite M"
  shows "finite (quotG M)"
  unfolding quot_graph_def
  using assms
  by simp

lemma card_quot_matching:
  assumes "finite M" "\<And>e. e\<in>M \<Longrightarrow> e \<noteq> {}" "{e. e \<in> M \<and> (\<exists>v\<in>e. v \<notin> s) \<and> (\<exists>v\<in>e. v \<in> s)} \<subseteq> {dume}"
          "M \<subseteq> E"
  shows "card (quotG M) = card M - card {e. e \<in> M \<and> e \<inter> s = {}}"
  using assms
proof(induction M)
  case empty
  then show ?case
    by (auto simp add: quot_graph_def)
next
  case (insert e E')
  then have card_ins: "card (insert e E') = card E' + 1"
    by auto
  have hyp: "card (quotG E') = card E' - card {e \<in> E'. e \<inter> s = {}}"
    using insert
    by (simp add: subset_iff)
  show ?case
  proof(cases "e \<inter> s = {}")
    case True
    then have "{e' \<in> insert e E'. e' \<inter> s = {}} = insert e {e' \<in> E'. e' \<inter> s = {}}"
      by auto
    then have "card {e' \<in> insert e E'. e' \<inter> s = {}} = card {e' \<in> E'. e' \<inter> s = {}} + 1"
      using insert(1,2)
      by auto
    moreover have "quotG (insert e E') = quotG E'"
      using image_edge_sing_u[OF True] insert(4)
      unfolding quot_graph_def
      by auto
    ultimately show ?thesis
      using hyp card_ins
      by auto
  next
    case False
    have "P ` e \<noteq> {u}"
      using False good_quot_map
      by (auto simp: image_iff set_eq_iff)
    then have "(quotG (insert e E')) =  insert (P ` e) (quotG E')"
      by (auto simp add: quot_graph_def)
    moreover have "P ` e \<notin> (quotG E')"
    proof(cases "\<exists>v\<in>e. v \<notin> s")
      case True
      moreover have "\<exists>v\<in>s. v\<in>e"
        using False
        by blast
      ultimately have "e = dume"
        using insert(5)
        by auto
      moreover have "\<forall>e'\<in>E'. e \<noteq> e'"
        using insert(2)
        by auto
      ultimately have disj: "\<forall>e'\<in>E'. (\<forall>v\<in>e'. v \<in> s) \<or> (\<forall>v\<in>e'. v \<notin> s)"
        using insert(5)
        by blast
      have uin: "u \<in> P ` e"
        using \<^marker>\<open>provenance ai\<close> True
        by (auto simp: image_iff)
      have sin: "\<exists>x\<in>s. x \<in> P ` e"
        using \<^marker>\<open>provenance ai\<close> False
        by (auto simp: image_iff)
      then have "\<forall>e'\<in>E'. P ` e \<noteq> P ` e'"
      proof \<^marker>\<open>provenance ai\<close>(intro ballI notI)
        fix e'
        assume e': "e' \<in> E'" "P ` e = P ` e'"
        have "u \<in> P ` e'"
          using uin
          by \<^marker>\<open>provenance human\<close> (simp only: e')
        moreover have \<^marker>\<open>provenance human\<close> "\<exists>x\<in>s. x \<in> P ` e'"
          using \<^marker>\<open>provenance ai\<close> sin
          by (simp only: e')
        ultimately show False
          using \<^marker>\<open>provenance human\<close> disj e'(1) good_quot_map(1)
          by \<^marker>\<open>provenance human\<close> (auto simp: image_iff)
      qed
      then show ?thesis
        unfolding quot_graph_def
        by auto
    next
      case F2: False
      moreover have neq: "\<forall>e'\<in>E'. e \<noteq> e'"
        using insert(2)
        by auto
      ultimately have "\<forall>e'\<in>E'. P ` e \<noteq> P ` e'"
      proof \<^marker>\<open>provenance ai\<close>(intro ballI notI)
        fix e'
        assume e': "e' \<in> E'" "P ` e = P ` e'"
        have "e \<subseteq> s"
          using F2
          by auto
        then have Pe: "P ` e = e"
          by \<^marker>\<open>provenance human\<close> (auto simp: subset_iff)
        have "e' \<subseteq> s"
        proof
          fix x
          assume "x \<in> e'"
          then have "P x \<in> e"
            using \<^marker>\<open>provenance human\<close> e'(2) Pe
            by blast
          then have "P x \<in> s"
            using \<^marker>\<open>provenance human\<close> \<open>e \<subseteq> s\<close>
            by blast
          then show "x \<in> s"
            using \<^marker>\<open>provenance human\<close> good_quot_map(1)
            by \<^marker>\<open>provenance human\<close> (auto split: if_splits)
        qed
        then have "P ` e' = e'"
          by \<^marker>\<open>provenance human\<close> (auto simp: subset_iff)
        then show False
          using e' Pe neq
          by auto
      qed
      then show ?thesis
        unfolding quot_graph_def
        by auto
    qed
    ultimately have " card (quotG (insert e E')) =  card (quotG E') + 1"
      using finite_quot[OF insert(1)]
      using \<open>P ` e \<notin> quotG E'\<close>
      by auto
    moreover have "{e' \<in> insert e E'. e' \<inter> s = {}} = {e' \<in> E'. e' \<inter> s = {}}"
      using False
      by auto
    moreover have "card (insert e E') = card E' + 1"
      using insert(1,2)
      by auto
    ultimately show ?thesis
      using insert(1,2) hyp
      by (simp add: Suc_diff_le card_mono)
  qed
qed

end

lemma symm_diff_is_matching':
  assumes 
    "alt_path M p"
    "matching M"
    "hd p \<notin> Vs M"
    "length p \<ge> 2 \<longrightarrow> last (edges_of_path p) \<in> M"
    "distinct p"
  shows "matching (M \<oplus> (set (edges_of_path p)))"
  using assms
proof(induction "length p" arbitrary: p M rule: less_induct)
  case less
  have distinct_edges: "distinct (edges_of_path p)"
    by (rule distinct_edges_of_vpath, rule less)
  show ?case
  proof(cases p)
    case Nil
    then show ?thesis
      using less
      by (simp add: symmetric_diff_def)
  next
    case [simp]: (Cons a' p')
    show ?thesis
    proof(cases "p'")
      case Nil
      then show ?thesis
        using less
        by (simp add: symmetric_diff_def)
    next
      case [simp]: (Cons a'' p'')
      show ?thesis
      proof(cases p'')
        case Nil
        then show ?thesis
          using less
          by (simp add: alt_list_step matching_def2 symmetric_diff_def Vs_def)
      next
        case p''[simp]: (Cons a''' p''')
        have a'''nin: "a''' \<notin> Vs (M - {{a'', a'''}})"
        proof(rule ccontr)
          assume "\<not> a''' \<notin> Vs (M - {{a'', a'''}})"
          then have "a''' \<in> Vs (M - {{a'', a'''}})"
            by simp
          then obtain e where e: "e \<in> (M  - {{a'', a'''}}) " "a''' \<in> e" "e \<noteq> {a'', a'''}"
            unfolding Vs_def
            by auto
          moreover have "{a'', a'''} \<in> M"
            using less.prems(1)
            by (simp add: alt_list_step alt_list_empty)
          ultimately show False
            using less.prems(2)
            unfolding matching_def2 Vs_def
            by \<^marker>\<open>provenance ai\<close> auto
        qed
        have "matching ((M - {{a'', a'''}}) \<oplus> set (edges_of_path (a''' # p''')))"
        proof(intro less, goal_cases)
          case \<^marker>\<open>provenance ai\<close> 1
          show \<^marker>\<open>provenance ai\<close> ?case
            by \<^marker>\<open>provenance human\<close> simp
        next \<^marker>\<open>provenance ai\<close>
          case \<^marker>\<open>provenance ai\<close> 2
          have *: "alt_path M p''"
            using less
            by (auto simp add: alt_list_step)
          show ?case
            using distinct_edges
            by (intro alt_list_cong[OF *[simplified]]; auto simp add: alt_list_step)
        next \<^marker>\<open>provenance ai\<close>
          case \<^marker>\<open>provenance ai\<close> 3
          show \<^marker>\<open>provenance ai\<close> ?case
            using \<^marker>\<open>provenance human\<close> less.prems(2)
            by \<^marker>\<open>provenance human\<close> (rule matching_delete)
        next \<^marker>\<open>provenance ai\<close>
          case \<^marker>\<open>provenance ai\<close> 4
          show \<^marker>\<open>provenance ai\<close> ?case
            using \<^marker>\<open>provenance human\<close> a'''nin
            by \<^marker>\<open>provenance human\<close> simp
        next \<^marker>\<open>provenance ai\<close>
          case \<^marker>\<open>provenance ai\<close> 5
          have "last (edges_of_path (a''' # p''')) \<noteq> {a'', a'''}" if "2 \<le> length (a''' # p''')"
          proof(cases p''')
            case Nil
            then show ?thesis
              using that
              by simp
          next
            case (Cons a'''' p'''')
            moreover have "a'' \<notin> set p'''"
              using less.prems(5)
              by simp
            ultimately show ?thesis
              using v_in_edge_in_path_gen last_in_set
              by (simp add: doubleton_eq_iff; fastforce)
          qed
          then show ?case
            using a'''nin less.prems(4)
            by (cases p'''; simp split: if_splits)
        next \<^marker>\<open>provenance ai\<close>
          case \<^marker>\<open>provenance ai\<close> 6
          show \<^marker>\<open>provenance ai\<close> ?case
            using \<^marker>\<open>provenance human\<close> less.prems(5)
            by simp
        qed
        moreover have "(M \<oplus> set (edges_of_path p)) - {{a', a''}} =  (M - {{a'', a'''}} \<oplus> set (edges_of_path (a''' # p''')))"
        proof(intro equalityI subsetI, goal_cases)
          case \<^marker>\<open>provenance ai\<close> (1 x)
          then \<^marker>\<open>provenance ai\<close> show \<^marker>\<open>provenance ai\<close> ?case
            using \<^marker>\<open>provenance human\<close> less.prems(1)
            by \<^marker>\<open>provenance human\<close> (simp add: alt_list_step alt_list_empty symmetric_diff_def; blast)
        next \<^marker>\<open>provenance ai\<close>
          case \<^marker>\<open>provenance ai\<close> (2 x)
          then \<^marker>\<open>provenance ai\<close> show \<^marker>\<open>provenance ai\<close> ?case
            using \<^marker>\<open>provenance human\<close> less.prems(1,5) v_in_edge_in_path
            by \<^marker>\<open>provenance human\<close> (simp add: alt_list_step alt_list_empty symmetric_diff_def; fastforce)
        qed \<^marker>\<open>provenance ai\<close>
        ultimately have "matching ((M \<oplus> set (edges_of_path p)) - {{a', a''}})"
          by simp
        moreover have "a' \<notin> Vs ((M \<oplus> set (edges_of_path p)) - {{a', a''}})"
        proof(rule ccontr)
          assume "\<not> a' \<notin> Vs ((M \<oplus> set (edges_of_path p)) - {{a', a''}})"
          then have "a' \<in> Vs ((M \<oplus> set (edges_of_path p)) - {{a', a''}})"
            by simp
          then obtain e where e: "e \<noteq> {a', a''}" "a' \<in> e" "e \<in> M \<or> e \<in> set (edges_of_path p)"
            unfolding symmetric_diff_def Vs_def
            by (auto simp del: p'')
          moreover have False if "e \<in> M"
          proof-
            have "a' \<in> Vs M"
              unfolding Vs_def
              using that e 
              by auto
            then show False
              using less.prems(3)
              by (simp)
          qed
          moreover have False if "e \<in> set (edges_of_path p)"
          proof-
            have "e \<in> set (edges_of_path p')"
              using that less.prems(1) e(1)
              by (auto)
            then have "a' \<in> set p'"
              using v_in_edge_in_path_gen e(2)
              by force
            then show False
              using less.prems(5)
              by (auto)
          qed
          ultimately show False
            by auto
        qed
        moreover have "a'' \<notin> Vs ((M \<oplus> set (edges_of_path p)) - {{a', a''}})"
        proof(rule ccontr)
          assume "\<not> a'' \<notin> Vs ((M \<oplus> set (edges_of_path p)) - {{a', a''}})"
          then have "a'' \<in> Vs ((M \<oplus> set (edges_of_path p)) - {{a', a''}})"
            by simp
          then obtain e where e: "e \<noteq> {a', a''}" "a'' \<in> e" "e \<in> M \<or> e \<in> set (edges_of_path p)" "e \<notin> M \<or> e \<notin> set (edges_of_path p)"
            unfolding symmetric_diff_def Vs_def
            by (auto simp del: p'')
           have a''a'''_in_both: "{a'', a'''} \<in> M" "{a'', a'''} \<in> set (edges_of_path p)"
              using less.prems(1)
              by (auto simp add: alt_list_step)
          show False
          proof(cases "e = {a'', a'''}")
            case True
            then show ?thesis
              using e a''a'''_in_both
              by auto
          next
            case False
            moreover have False if "e \<in> M"
              using less.prems(2) False e(2) that a''a'''_in_both(1)
              by (auto simp add: matching_def2 Vs_def)
            moreover have False if "e \<in> set (edges_of_path p)"
            proof-
              have "e \<in> set (edges_of_path p'')"
                using less.prems(5) that e(1) False
                by (auto)
              then have "a'' \<in> set p''"
                using v_in_edge_in_path_gen e(2)
                by force
              then show False
                using less.prems(5)
                by (auto)
            qed
            ultimately show ?thesis
              using e(3)
              by auto
          qed
        qed
        moreover have "insert {a', a''} ((M \<oplus> set (edges_of_path p)) - {{a', a''}}) = ((M \<oplus> set (edges_of_path p)))"
          using less.prems(3) Vs_def
          by(auto simp: symmetric_diff_def)
        ultimately show ?thesis
          using \<^marker>\<open>provenance ai\<close> matching_insert[of "{a', a''}" "(M \<oplus> set (edges_of_path p)) - {{a', a''}}"]
          by \<^marker>\<open>provenance ai\<close> auto
      qed
    qed
  qed
qed

lemma card_symm_diff_matching:
  assumes 
    "finite M"
    "alt_path M p"
    "even (length (edges_of_path p))"
    "distinct p"
  shows "card (M \<oplus> (set (edges_of_path p))) = card M"
proof-
  have "card (M \<inter> set (edges_of_path p)) = card (set (filter (\<lambda>e. e \<in> M) (edges_of_path p)))"
    by (simp add: Collect_conj_eq inf_commute)
  moreover have "card (set (filter (\<lambda>e. e \<in> M) (edges_of_path p))) = length (filter (\<lambda>e. e \<in> M) (edges_of_path p))"
    by(intro distinct_card distinct_filter distinct_edges_of_vpath assms)
  moreover have "card (set (edges_of_path p) - M) = card (set (filter (\<lambda>e. e \<notin> M) (edges_of_path p)))"
    by (simp add: Collect_conj_eq set_diff_eq)
  moreover have "card (set (filter (\<lambda>e. e \<notin> M) (edges_of_path p))) = length (filter (\<lambda>e. e \<notin> M) (edges_of_path p))"
    by(intro distinct_card distinct_filter distinct_edges_of_vpath assms)
  moreover have "length (filter (\<lambda>e. e \<notin> M) (edges_of_path p)) = length (filter (\<lambda>e. e \<in> M) (edges_of_path p))"
    using alternating_eq_iff_even assms(2,3)
    by auto
  ultimately have "card (set (edges_of_path p) - M) = card (M \<inter> set (edges_of_path p))"
    by auto
  then show ?thesis
    by(intro card_symm_diff assms finite_set)
qed

lemma alt_path_in_symm_diff:
  assumes "alt_path E C" "set (edges_of_path C) \<inter> E' = {}"
  shows "alt_path (E \<oplus> E') C"
proof-
  have "\<forall>e\<in>set (edges_of_path C). e \<in> E = (e \<in> (E \<oplus> E'))"
    using assms(2)
    by (simp add: disjoint_iff symmetric_diff_def)

  then show ?thesis
    using alt_list_cong assms(1)
    by fastforce
qed

lemma graph_subset_quot_subset:
  assumes "E \<subseteq> E'"
  shows "quot_graph P E \<subseteq> quot_graph P E'"
  using assms
  unfolding quot_graph_def
  by auto

lemma Vs_quot_graph_is_img:
  shows "(Vs (quot_graph P E)) = P` (Vs E)"
  unfolding Vs_def quot_graph_def image_def
  by auto

lemma Vs_quot_graph_finite:
  assumes "finite (Vs E)"
  shows "finite (Vs (quot_graph P E))"
  using assms
  by (simp add: Vs_quot_graph_is_img)


lemma quot_graph_finite:
  assumes "finite E"
  shows "finite (quot_graph P E)"
  using assms
  by (simp add: quot_graph_def)

lemma quot_graph_finite':
  assumes "finite (Vs E)"
  shows "finite (quot_graph P E)"
  using quot_graph_finite[OF finite_Vs_then_finite[OF assms]].

context quot
begin

lemma Vs_quotG_finite:
  assumes "finite (Vs E)"
  shows "finite (Vs (quotG E))"
  using assms Vs_quot_graph_finite Vs_quotG_subset_Vs_quot_graph finite_subset
  by fastforce

lemma doubleton_quot: 
  assumes"M \<subseteq> E"
  shows "dblton_graph (quotG M)"
proof(rule dblton_graphI, goal_cases)
  have "dblton_graph M"
    using \<open>M \<subseteq> E\<close> dblton_E
    by (fastforce intro!: dblton_graphI elim!: dblton_graphE)
  case (1 quote)
  have card_quote: "card quote \<le> 2"
  proof(rule ccontr)
    assume "\<not> card quote \<le> 2"
    then obtain v1 v2 v3 where "{v1,v2,v3} \<subseteq> quote" "v1 \<noteq> v2" "v1 \<noteq> v3" "v2 \<noteq> v3"
      using card3_subset not_less_eq_eq
      by force
    then obtain e w1 w2 w3 where "e \<in> M" "{w1,w2,w3} \<subseteq> e" "w1 \<noteq> w2" "w1 \<noteq> w3" "w2 \<noteq> w3"
      using 1
      by (auto simp: quot_graph_def) 
    then show False
      using \<open>dblton_graph M\<close>
      by (auto elim: dblton_graphE)
  qed
  have "finite e" if "e \<in> M" for e
    using \<open>dblton_graph M\<close> that
    by (fastforce elim: dblton_graphE)
  then have finite_quote: "finite quote"
    using 1
    unfolding quot_graph_def
    by blast
  show ?case
  proof(cases "\<exists>v. quote = {v}")
    case qtuoe_eq_v: True
    then obtain v where v: "quote = {v}"
      by auto
    show ?thesis
    proof(cases "v = u")
      case True
      then show ?thesis
        using 1 v
        by auto
    next
      case False
      have \<^marker>\<open>provenance ai\<close> "u \<notin> quote"
        using v False
        by simp
      then \<^marker>\<open>provenance ai\<close> have "quote \<subseteq> s"
        using 1 u_nin_edge_in_quot
        by \<^marker>\<open>provenance ai\<close> blast
      then \<^marker>\<open>provenance ai\<close> have \<^marker>\<open>provenance ai\<close> "quote \<in> M"
        using \<^marker>\<open>provenance human\<close> 1 edge_in_quot_in_graph_1' \<open>M \<subseteq> E\<close>
        by blast
      then have False
        using \<open>dblton_graph M\<close> v
        by (auto elim: dblton_graphE)
      then show ?thesis
        by simp
    qed
  next
    case quote_nsing: False
    show ?thesis
    proof(cases "quote = {}")
      case True
      then obtain e where "e \<in> E" "e = {}"
        using "1" edge_in_quot_in_graph_1' \<open>M\<subseteq>E\<close>
        by auto
      then show ?thesis
        using dblton_E
        by (auto elim!: dblton_graphE)
    next
      case False
      then have "card quote \<noteq> 1" "card quote \<noteq> 0"
        using finite_quote quote_nsing card_1_singletonE card_eq_0_iff
        by auto
      then have "card quote = 2"
        using card_quote
        by auto
      then obtain v1 v2 where "quote = {v1,v2}" "v1 \<noteq> v2"
        by (auto simp: card_2_iff)
      then show ?thesis
        by auto
    qed
  qed
qed

end

context quot
begin

text\<open>A concrete augmenting path can be contracted, in the general case\<close>

theorem aug_path_works_in_contraction:
  assumes match_blossom: "blossom E M stem C" and
    aug_path: "graph_augmenting_path E M p" and 
    matching: "matching M" "M \<subseteq> E" "finite M" and
    quot: "s = (Vs E) - set C" "u \<notin>  Vs E"(* and
    graph: "dblton_graph G" "finite (Vs G)"*)
  shows "\<exists>p'. graph_augmenting_path (quotG E) (quotG M) p'"
proof(cases "(set p) \<inter> (set C) \<noteq> {}")
  case has_s_verts: True
  have "match_blossom M stem C" 
    using blossomD(2)[OF match_blossom] .
  show ?thesis
  proof(cases "last C \<notin> Vs M")
    case True
    then show ?thesis
      using aug_path_works_in_contraction_unmatched_base' assms(2-) match_blossom(1)
            match_blossomD[OF \<open>match_blossom M stem C\<close>]
            match_blossom_alt_cycle[OF \<open>match_blossom M stem C\<close>]
            dblton_E finite_E
      by fastforce
  next
    case False
    then have "last C \<in> Vs M"
      by simp
    show ?thesis
    proof(cases "stem = []")
      case stem_empty: True
      then have "last C \<notin> Vs M"
        using match_blossomD(4)[OF \<open>match_blossom M stem C\<close>] odd_cycleD(3)[OF match_blossomD(3)[OF \<open>match_blossom M stem C\<close>]]
        by simp
      then show ?thesis
        using aug_path_works_in_contraction_unmatched_base' assms(2-)
              match_blossomD[OF \<open>match_blossom M stem C\<close>]
              match_blossom_alt_cycle[OF \<open>match_blossom M stem C\<close>]
        by blast
    next
      case stem_nempty: False
      define M' where "M' = M \<oplus> (set (edges_of_path (stem @ [hd C])))"
      then have M'_finite: "finite M'"
        using matching(3)
        by (simp add: finite_symm_diff)
      have alt_list_stem_hdC: "alt_path M (stem @ [hd C])"
      proof \<^marker>\<open>provenance ai\<close>-
        have \<^marker>\<open>provenance human\<close> eq: "edges_of_path (stem @ C) = edges_of_path (stem @ [hd C]) @ edges_of_path C"
          using odd_cycle_nempty[OF match_blossomD(3)[OF \<open>match_blossom M stem C\<close>]] edges_of_path_append_2
          by \<^marker>\<open>provenance ai\<close> blast
        then show ?thesis
          using \<^marker>\<open>provenance human\<close> match_blossomD(1)[OF \<open>match_blossom M stem C\<close>] alt_list_append_1
          by auto
      qed
      have distinct_stem_hdC: "distinct (stem @ [hd C])"
      proof-
        have bl: "butlast C = hd C # tl (butlast C)"
          using odd_cycleD(1)[OF match_blossomD(3)[OF \<open>match_blossom M stem C\<close>]]
          by \<^marker>\<open>provenance ai\<close> (cases C; auto)
        then show ?thesis
          using match_blossomD(2)[OF \<open>match_blossom M stem C\<close>] bl
          by (cases "butlast C"; auto simp: distinct_append)
      qed
      have path_stem_hdC: "path E (stem @ [hd C])"
        using match_blossom(1) odd_cycle_nempty[OF match_blossomD(3)[OF \<open>match_blossom M stem C\<close>]]
        using \<^marker>\<open>provenance ai\<close> path_pref[of E "stem @ [hd C]" "tl C"]
        by \<^marker>\<open>provenance ai\<close> (cases C; auto)
      have stem_hdC_nempty: "edges_of_path (stem @ [hd C]) \<noteq> []"
        using \<^marker>\<open>provenance ai\<close> stem_nempty edges_of_path_snoc[OF stem_nempty, of "hd C"]
        by (auto simp flip: edges_of_path_snoc)
      have "(edges_of_path (stem @ C)) = (edges_of_path (stem @ [hd C])) @ (edges_of_path (C))"
        using odd_cycle_nempty[OF match_blossomD(3)[OF \<open>match_blossom M stem C\<close>]]
        using edges_of_path_append_2
        by blast
      then have "alt_path M (stem @ [hd C])"
        using match_blossomD(1)[OF \<open>match_blossom M stem C\<close>] alt_list_append_1
        by auto
      then have last_stem_hdC: "last (edges_of_path (stem @ [hd C])) \<in> M"
        using match_blossomD(5)[OF \<open>match_blossom M stem C\<close>] stem_hdC_nempty
              alternating_list_even_last
        by auto
      have stem_C_disj: "set C \<inter> set stem = {}"
        using match_blossomD(2)[OF \<open>match_blossom M stem C\<close>] distinct_stem_hdC odd_cycleD(3)[OF match_blossomD(3)[OF \<open>match_blossom M stem C\<close>]]
        by (cases C rule: rev_cases; auto simp: distinct_append)
      have M'_matching: "matching M'"
        unfolding M'_def
      proof(intro symm_diff_is_matching' distinct_stem_hdC, goal_cases)
        case \<^marker>\<open>provenance ai\<close> 1
        show \<^marker>\<open>provenance ai\<close> ?case
          using \<^marker>\<open>provenance human\<close> alt_list_stem_hdC
          by \<^marker>\<open>provenance human\<close> auto
      next \<^marker>\<open>provenance ai\<close>
        case \<^marker>\<open>provenance ai\<close> 2
        show \<^marker>\<open>provenance ai\<close> ?case
          using \<^marker>\<open>provenance human\<close> matching(1)
          by \<^marker>\<open>provenance human\<close> auto
      next \<^marker>\<open>provenance ai\<close>
        case \<^marker>\<open>provenance ai\<close> 3
        show \<^marker>\<open>provenance ai\<close> ?case
          using \<^marker>\<open>provenance human\<close> match_blossomD(4)[OF \<open>match_blossom M stem C\<close>]
          by \<^marker>\<open>provenance human\<close> (simp add: stem_nempty)
      next \<^marker>\<open>provenance ai\<close>
        case \<^marker>\<open>provenance ai\<close> 4
        have "last (edges_of_path (stem @ [hd C])) \<in> M"
          by (rule alternating_list_even_last[where ?P1.0 = "(\<lambda>e. e \<notin> M)", OF alt_list_stem_hdC match_blossomD(5)[OF \<open>match_blossom M stem C\<close>] stem_hdC_nempty])
        then show ?case
          by auto
      qed
      moreover have cardM'_eq_cardM: "card M' = card M"
        unfolding M'_def
        by(intro card_symm_diff_matching matching(3) match_blossomD[OF \<open>match_blossom M stem C\<close>] alt_list_stem_hdC distinct_stem_hdC)
      moreover obtain M_large where "matching M_large" "card M_large > card M" "M_large \<subseteq> E"
        using Berge_2[OF graph_augmenting_path_feats(1)[OF aug_path] matching(2) graph_augmenting_path_feats(3,2)[OF aug_path] matching(3,1)]
        by auto
      moreover have M'_subset_G: "M' \<subseteq> E"
        unfolding M'_def
        using matching(2)
        using \<^marker>\<open>provenance ai\<close> sym_diff_subset[of M "set (edges_of_path (stem @ [hd C]))"] path_edges_subset[OF path_stem_hdC]
        by \<^marker>\<open>provenance ai\<close> blast
      ultimately obtain p_M' where aug_M': "matching_augmenting_path M' p_M'" "path E p_M'" "distinct p_M'"
        using Berge[OF M'_finite _ _ dblton_E finite_Vs]
        by auto

      moreover have lastC_nin_M': "last C \<notin> Vs M'"
      proof-
        have lastnin: "last (edges_of_path (stem @ [hd C])) \<notin> M'"
          unfolding M'_def symmetric_diff_def
          using match_blossomD(5)[OF \<open>match_blossom M stem C\<close>] alternating_list_even_last
                last_in_set last_stem_hdC \<open>edges_of_path (stem @ [hd C]) \<noteq> []\<close>
          by blast
        text\<open>The rest of the proof depends on the fact that hd C should be in any matched edge in M,
           other that {last stem, hd C}, and thus it is unmatched in M'.\<close>
        moreover have memlast: "\<forall>e\<in>set(edges_of_path (stem @ [hd C])). hd C \<in> e \<longrightarrow> e = last (edges_of_path (stem @ [hd C]))"
          using mem_eq_last_edge[OF distinct_stem_hdC]
          by simp
        moreover have Mhd: "\<forall>e\<in>M. e \<noteq> last (edges_of_path (stem @ [hd C])) \<longrightarrow> hd C \<notin> e"
        proof-
          have "hd C \<in> last (edges_of_path (stem @ [hd C]))"
            using stem_nempty
            by (auto simp flip: edges_of_path_snoc)
          then show ?thesis
            using matching(1) last_stem_hdC
            by (auto dest: matching_unique_match)
        qed
        ultimately have "\<forall>e\<in>M'. hd C \<notin> e"
          unfolding M'_def
        proof \<^marker>\<open>provenance ai\<close>(intro ballI notI)
          fix e
          assume \<^marker>\<open>provenance human\<close> e: "e \<in> M \<oplus> set (edges_of_path (stem @ [hd C]))" "hd C \<in> e"
          have \<^marker>\<open>provenance human\<close> "e \<in> M \<or> e \<in> set (edges_of_path (stem @ [hd C]))"
            using \<^marker>\<open>provenance ai\<close> e(1)
            by (auto simp: symmetric_diff_def)
          then have \<^marker>\<open>provenance human\<close> "e = last (edges_of_path (stem @ [hd C]))"
            using \<^marker>\<open>provenance ai\<close> e(2) memlast Mhd
            by \<^marker>\<open>provenance ai\<close> blast
          then show False
            using e(1) lastnin
            unfolding \<^marker>\<open>provenance human\<close> M'_def
            by blast
        qed
        then show ?thesis
          unfolding Vs_def
          using odd_cycleD(3)[OF match_blossomD(3)[OF \<open>match_blossom M stem C\<close>]]
          by auto
      qed
      moreover have alt_M'C: "alt_path M' C"
        unfolding M'_def
      proof(rule alt_path_in_symm_diff, goal_cases)
        case \<^marker>\<open>provenance ai\<close> 1
        show \<^marker>\<open>provenance ai\<close> ?case
          using \<^marker>\<open>provenance human\<close> match_blossom_alt_cycle[OF \<open>match_blossom M stem C\<close>] . \<^marker>\<open>provenance human\<close>
      next \<^marker>\<open>provenance ai\<close>
        case \<^marker>\<open>provenance ai\<close> 2
        show \<^marker>\<open>provenance ai\<close> ?case
        proof \<^marker>\<open>provenance human\<close>-
          have *: "(edges_of_path (stem @ [hd C])) = (edges_of_path (stem)) @ [{last stem, hd C}]"
            using stem_nempty
            by (simp add: edges_of_path_snoc)
          have "last stem \<notin> set C"
            using stem_C_disj stem_nempty
            by (auto dest: last_in_set)
          then have "{last stem, hd C} \<notin> set (edges_of_path C)"
            by (auto dest: v_in_edge_in_path)
          moreover have "set C \<inter> set stem = {}"
            by \<^marker>\<open>provenance ai\<close> (rule stem_C_disj)
          ultimately show ?thesis
            unfolding *
            by (auto dest: edges_of_path_disj)
        qed
      qed \<^marker>\<open>provenance ai\<close>
      ultimately obtain p'_quotM' where p'_M': "alt_path (quotG M') p'_quotM'" 
        "path (quotG E) p'_quotM'"
        "distinct p'_quotM'"
        "hd p'_quotM' \<notin> Vs (quotG M')"
        "last p'_quotM' \<notin> Vs (quotG M')"
        "length p'_quotM' \<ge> 2"
        using aug_path_works_in_contraction_unmatched_base'[OF match_blossomD(3)[OF \<open>match_blossom M stem C\<close>] alt_M'C aug_M'(1) aug_M'(2) aug_M'(3) lastC_nin_M' M'_matching M'_subset_G quot(1,2)]
        by (auto simp: matching_augmenting_path_def)
               
      then have qaug: "matching_augmenting_path (quotG M') p'_quotM'" 
        "path (quotG E) p'_quotM'"
        "distinct p'_quotM'"
        unfolding matching_augmenting_path_def
        by auto
      moreover have fin_qM': "finite (quotG M')"
        unfolding M'_def
        by(rule finite_quot finite_symm_diff matching(3) finite_set)+
      moreover have match_qM': "matching (quotG M')"
      proof-
        have "v \<in> s" if "e \<in> M'" "v \<in> e" "w \<in> s" "w \<in> e" for w v e
        proof(rule ccontr)
          assume "v \<notin> s"
          moreover have v_inM': "v \<in> Vs M'"
            using that(1,2)
            unfolding Vs_def
            by auto
          moreover have "v \<in> Vs E" if "v \<in> Vs M'"
            using that
            using M'_subset_G Vs_subset
            by blast
          moreover have "v \<in> set C" if "(v \<notin> s)" "v \<in> Vs E" for v
            using quot that
            by blast
          ultimately have "v \<in> set C"
            using that
            by auto
          show False
          proof(cases "v = hd C \<or> v = last C")
            case True
            then show ?thesis
              using lastC_nin_M' odd_cycleD(3)[OF match_blossomD(3)[OF \<open>match_blossom M stem C\<close>]] v_inM'
              by auto
          next
            case False
            then show ?thesis
              using M'_matching 
                    \<open>v \<in> set C\<close>
                    matching_edge_incident_on_cycle[OF match_blossomD(3)[OF \<open>match_blossom M stem C\<close>]
                                              \<open>alt_path M' C\<close>]
              using quot(1) that(1) that(2) that(3) that(4)
              by fastforce
          qed
        qed
        then show ?thesis
          using M'_subset_G
          by (intro quot_is_matching M'_matching; blast)
      qed
      moreover have sub_qM': "quotG M' \<subseteq> quotG E"
        using graph_subset_quot_subset M'_subset_G
        by auto
      ultimately obtain quotM'_large where quotM'_large: "matching quotM'_large" "card quotM'_large > card (quotG M')" "quotM'_large \<subseteq> quotG E"
        using Berge_2[OF qaug(1) sub_qM' qaug(2) qaug(3) fin_qM' match_qM']
        by \<^marker>\<open>provenance ai\<close> auto
      have finite_quotG_M: "finite (quotG M)"
        using finite_quot matching(3)
        by blast
      have quotM_sub_quotG: "quotG M \<subseteq> quotG E"
        using graph_subset_quot_subset matching(2)
        by auto
      have matching_quotM: "matching (quotG M)"
      proof-
        have "v = last C" (is ?p1) "w = last stem" (is ?p2) if "e \<in> M" "v \<in> e" "w \<in> s" "w \<in> e" "v \<notin> s" for w v e
        proof-
          have v_inM: "v \<in> Vs M"
            using that(1,2)
            unfolding Vs_def
            by auto
          moreover have w_inM: "w \<in> Vs M"
            using that(1,4)
            unfolding Vs_def
            by auto
          moreover have "v \<in> Vs E" if "v \<in> Vs M"
            using that
            using matching(2) Vs_subset
            by blast
          moreover have "v \<notin> set C" if "(v \<in> s)" "v \<in> Vs E" for v
            using quot that
            by blast
          moreover have "v \<in> set C" if "(v \<notin> s)" "v \<in> Vs E" for v
            using quot that
            by blast
          ultimately have "v \<in> set C" "w \<notin> set C"
            using that quot(1)
            by blast+
          then show ?p1
            using matching_edge_incident_on_cycle[OF match_blossomD(3)[OF \<open>match_blossom M stem C\<close>] match_blossom_alt_cycle[OF \<open>match_blossom M stem C\<close>] that(1) _ _ _ matching(1)] that(2,4)
            by simp
          moreover have "{last stem, last C} \<in> M"
            using last_stem_hdC stem_nempty odd_cycleD(3)[OF match_blossomD(3)[OF \<open>match_blossom M stem C\<close>]]
            by (simp flip: edges_of_path_snoc[OF stem_nempty])
          ultimately show ?p2
            using that(1,2,4) matching(1) \<open>v \<in> set C\<close> \<open>w \<notin> set C\<close>
            unfolding matching_def2 Vs_def
            by auto
        qed
        then show ?thesis
          using dblton_E matching(2)
          by (intro quot_is_matching[where dume = "{last stem, last C}"] matching(1,2); auto elim!: dblton_graphE)
      qed
      have quotG_graph: "dblton_graph (quotG E)"
        using doubleton_quot graph(1)
        by simp
      have finite_Vs_quotG: "finite (Vs (quotG E))"
        using Vs_quotG_finite[OF finite_Vs] .
      have card_quotM_eq_quotM': "card (quotG M) = card (quotG M')"
      proof-
        have "v \<in> s" if "e \<in> M'" "v \<in> e" "w \<in> s" "w \<in> e" for w v e
        proof(rule ccontr)
          assume "v \<notin> s"
          moreover have v_inM': "v \<in> Vs M'"
            using that(1,2)
            unfolding Vs_def
            by auto
          moreover have "v \<in> Vs E" if "v \<in> Vs M'"
            using that M'_subset_G Vs_subset
            by blast
          moreover have "v \<in> set C" if "(v \<notin> s)" "v \<in> Vs E" for v
            using quot that
            by blast
          ultimately have "v \<in> set C"
            using that
            by auto
          show False
          proof(cases "v = hd C \<or> v = last C")
            case True
            then show ?thesis
              using lastC_nin_M' odd_cycleD(3)[OF match_blossomD(3)[OF \<open>match_blossom M stem C\<close>]] v_inM'
              by auto
          next
            case False
            then show ?thesis
              using M'_matching  \<open>v \<in> set C\<close>
              using matching_edge_incident_on_cycle[OF match_blossomD(3)[OF \<open>match_blossom M stem C\<close>]
                                              \<open>alt_path M' C\<close>]
              using quot(1) that(1) that(2) that(3) that(4)
              by fastforce
          qed
        qed
        moreover have "\<forall>e\<in>M'. e \<noteq> {}"
          using M'_subset_G graph(1)
          by (auto elim: dblton_graphE)
        ultimately have i: "card (quotG M') = card M' - card {e \<in> M'. e \<inter> s = {}}"
          by (intro card_quot_matching M'_finite M'_subset_G; blast)
        have "v = last C" (is ?p1) "w = last stem" (is ?p2) if "e \<in> M" "v \<in> e" "w \<in> s" "w \<in> e" "v \<notin> s" for w v e
        proof-
          have v_inM: "v \<in> Vs M"
            using that(1,2)
            unfolding Vs_def
            by auto
          moreover have w_inM: "w \<in> Vs M"
            using that(1,4)
            unfolding Vs_def
            by auto
          moreover have "v \<in> Vs E" if "v \<in> Vs M"
            using that
            using matching(2) Vs_subset
            by blast
          moreover have "v \<notin> set C" if "(v \<in> s)" "v \<in> Vs E" for v
            using quot that
            by blast
          moreover have "v \<in> set C" if "(v \<notin> s)" "v \<in> Vs E" for v
            using quot that
            by blast
          ultimately have "v \<in> set C" "w \<notin> set C"
            using that quot(1)
            by blast+
          then show ?p1
            using matching_edge_incident_on_cycle[OF match_blossomD(3)[OF \<open>match_blossom M stem C\<close>] match_blossom_alt_cycle[OF \<open>match_blossom M stem C\<close>] that(1) _ _ _ matching(1)] that(2,4)
            by simp
          moreover have "{last stem, last C} \<in> M"
            using last_stem_hdC stem_nempty odd_cycleD(3)[OF match_blossomD(3)[OF \<open>match_blossom M stem C\<close>]]
            by (simp flip: edges_of_path_snoc[OF stem_nempty])
          ultimately show ?p2
            using that(1,2,4) matching(1) \<open>v \<in> set C\<close> \<open>w \<notin> set C\<close>
            unfolding matching_def2 Vs_def
            by auto
        qed
        moreover have "\<forall>e\<in>M. e \<noteq> {}"
          using matching(2) graph(1)
          by (auto elim: dblton_graphE)
        ultimately have "card (quotG M) = card M - card {e \<in> M. e \<inter> s = {}}"
          by (intro card_quot_matching[where dume = "{last stem, last C}"] matching; blast)
        moreover have "card {e \<in> M. e \<inter> s = {}} = card {e \<in> M'. e \<inter> s = {}}"
        proof-
          have "{e. e \<inter> s = {}} \<inter> set (edges_of_path (stem @ [hd C])) = {}"
          proof-
            have *: "(edges_of_path (stem @ [hd C])) = (edges_of_path (stem)) @ [{last stem, hd C}]"
              using stem_nempty
              by (simp add: edges_of_path_snoc)
            have "set stem \<subseteq> s"
            proof-
              have "path E stem"
                using match_blossom(1) path_pref
                by blast
              moreover have "set C \<inter> set stem = {}"
                by \<^marker>\<open>provenance ai\<close> (rule stem_C_disj)
              ultimately show ?thesis
                using quot (1) mem_path_Vs 
                by fastforce
            qed
            then have "{e. e \<inter> s = {}} \<inter> set (edges_of_path stem) = {}"
              using v_in_edge_in_path_gen edges_of_path_nempty_edges
              by fastforce
            then show ?thesis
              unfolding *
              using stem_nempty \<open>set stem \<subseteq> s\<close>
              by auto
          qed
          then show ?thesis
            unfolding M'_def
            by (intro arg_cong[where f = card]; auto simp: symmetric_diff_def)
        qed
        ultimately show ?thesis
          using i cardM'_eq_cardM
          by linarith
      qed
      obtain p'_quotM where "matching_augmenting_path (quotG M) p'_quotM \<and> path (quotG E) p'_quotM \<and> distinct p'_quotM"
        using Berge[OF finite_quotG_M matching_quotM quotM_sub_quotG quotG_graph finite_Vs_quotG] quotM'_large card_quotM_eq_quotM'
        by auto
      then show ?thesis
        unfolding matching_augmenting_path_def
        by auto
    qed
  qed
next
  case no_s_verts: False
  then have p_subset_s: "set p \<subseteq> s"
    using quot(1) mem_path_Vs graph_augmenting_path_feats(3)[OF aug_path]
    by fastforce
  then have "path (quotG E) p"
    using graph_augmenting_path_feats(3)[OF aug_path]
    using qug_path_iff_case_1_ii quot(1)
    by blast
  then show ?thesis
    using aug_path qug_path_iff_case_1_i p_subset_s matching(2)
    by blast
qed

lemma card_Vs_quotG:
  assumes "finite (Vs E)" "1 < card (Vs E - s)"
  shows "card (Vs (quotG E)) < card (Vs E)"
proof-              
  have "insert u (Vs (quotG E)) = insert u (P ` (Vs E) - (Vs E - s))"
    unfolding Vs_def quot_graph_def image_def
    by auto
  moreover have "... = insert u (Vs E \<inter> s)"
    unfolding Vs_def quot_graph_def image_def
    by auto
  moreover have C: "card (Vs E \<inter> s) < card (Vs E) - 1"
    using assms
    by (simp add: card_Diff_subset_Int)
  ultimately have eq: "insert u (Vs (quotG E)) = insert u (Vs E \<inter> s)"
    by \<^marker>\<open>provenance ai\<close> simp
  have fin: "finite (insert u (Vs E \<inter> s))"
    using \<^marker>\<open>provenance ai\<close> assms(1)
    by \<^marker>\<open>provenance ai\<close> simp
  have cu: "card (insert u (Vs E \<inter> s)) = card (Vs E \<inter> s) + 1"
    using assms(1) good_quot_map(1)
    by \<^marker>\<open>provenance ai\<close> simp
  have "card (Vs (quotG E)) \<le> card (insert u (Vs E \<inter> s))"
    using \<^marker>\<open>provenance ai\<close> eq fin
    by (intro card_mono; auto)
  then \<^marker>\<open>provenance ai\<close> show ?thesis
    using \<^marker>\<open>provenance ai\<close> cu C
    by \<^marker>\<open>provenance ai\<close> simp
qed

lemma matching_quotM:
  assumes match_blossom: "match_blossom M stem C" and
    matching: "matching M" "M \<subseteq> E"  and
    quot: "s = (Vs E) - set C"
  shows "matching (quotG M)"
proof(cases "stem = []")
  case True
  then have lastC_nin_M: "hd C \<notin> Vs M"
    using match_blossomD[OF match_blossom]
    by auto
  show ?thesis
  proof-
    have "v \<in> s" if "e \<in> M" "v \<in> e" "w \<in> s" "w \<in> e" for w v e
    proof(rule ccontr)
      assume "v \<notin> s"
      moreover have v_inM: "v \<in> Vs M"
        using that(1,2)
        unfolding Vs_def
        by auto
      moreover have "v \<in> Vs E" if "v \<in> Vs M"
        using that
        using matching(2) Vs_subset
        by blast
      moreover have "v \<in> set C" if "(v \<notin> s)" "v \<in> Vs E" for v
        using quot that
        by blast
      ultimately have "v \<in> set C"
        using that
        by auto
      show False
      proof(cases "v = hd C \<or> v = last C")
        case True
        then show ?thesis
          using lastC_nin_M odd_cycleD(3)[OF match_blossomD(3)[OF match_blossom]] v_inM
          by auto
      next
        case False
        then show ?thesis
          using matching(1) match_blossom_alt_cycle[OF match_blossom] match_blossomD[OF match_blossom] \<open>v \<in> set C\<close> matching_edge_incident_on_cycle quot(1) that(1) that(2) that(3) that(4)
          by fastforce
      qed
    qed
    then show ?thesis
      by (intro quot_is_matching matching(1) matching(2); blast)
  qed
next
  case stem_nempty: False
  have "v = last C" (is ?p1) "w = last stem" (is ?p2) if "e \<in> M" "v \<in> e" "w \<in> s" "w \<in> e" "v \<notin> s" for w v e
  proof-
    have stem_hdC_nempty: "edges_of_path (stem @ [hd C]) \<noteq> []"
      using \<^marker>\<open>provenance ai\<close> edges_of_path_snoc[OF stem_nempty, of "hd C"]
      by (auto simp flip: edges_of_path_snoc)
    have "(edges_of_path (stem @ C)) = (edges_of_path (stem @ [hd C])) @ (edges_of_path (C))"
      using odd_cycle_nempty[OF match_blossomD(3)[OF match_blossom]]
      using edges_of_path_append_2
      by blast
    then have "alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path (stem @ [hd C]))"
      using match_blossomD(1)[OF match_blossom] alt_list_append_1
      by auto
    then have last_stem_hdC: "last (edges_of_path (stem @ [hd C])) \<in> M"
      using match_blossomD(5)[OF match_blossom] stem_hdC_nempty
            alternating_list_even_last
      by blast
    have v_inM: "v \<in> Vs M"
      using that(1,2)
      unfolding Vs_def
      by auto
    moreover have w_inM: "w \<in> Vs M"
      using that(1,4)
      unfolding Vs_def
      by auto
    moreover have "v \<in> Vs E" if "v \<in> Vs M"
      using that
      using matching(2) Vs_subset
      by blast
    moreover have "v \<notin> set C" if "(v \<in> s)" "v \<in> Vs E" for v
      using quot that
      by blast
    moreover have "v \<in> set C" if "(v \<notin> s)" "v \<in> Vs E" for v
      using quot that
      by blast
    ultimately have "v \<in> set C" "w \<notin> set C"
      using that quot(1)
      by blast+
    then show ?p1
      using matching_edge_incident_on_cycle[OF match_blossomD(3)[OF match_blossom] match_blossom_alt_cycle[OF match_blossom] that(1) _ _ _ matching(1)] that(2,4)
      by simp
    moreover have "{last stem, last C} \<in> M"
      using last_stem_hdC stem_nempty odd_cycleD(3)[OF match_blossomD(3)[OF match_blossom]]
      by (simp flip: edges_of_path_snoc[OF stem_nempty])
    ultimately show ?p2
      using that(1,2,4) matching(1) \<open>v \<in> set C\<close> \<open>w \<notin> set C\<close>
      by (auto simp add: matching_def2 Vs_def)
  qed
  then show ?thesis
    using dblton_E matching(2)
    by (intro quot_is_matching[where dume = "{last stem, last C}"] matching(1,2); auto elim!: dblton_graphE)
qed


end

end

