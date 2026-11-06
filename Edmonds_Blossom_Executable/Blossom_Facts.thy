(*
  Author: Mohammad Abdulaziz
  Author: Thomas Ammer
*)

theory Blossom_Facts
imports Blossom_Misc Undirected_Set_Graphs.Pair_Graph_Berge_Adaptor Undirected_Set_Graphs.Undirected_Set_Graphs
        "Basic_Matching.Berge"
         
begin

provenance human

hide_const Pair_Graph.neighbourhood

subsection \<open>List Auxiliary Lemmas\<close>

lemma neq_Nil_conv_2:
  "l \<noteq> [] \<longleftrightarrow> (\<exists>l' x. l = l' @ [x])"
  by \<^marker>\<open>provenance ai\<close> (auto intro: rev_exhaust)

lemma tl_distinct_rev:
  assumes "hd l = last l" "distinct (tl l)"
  shows "distinct (tl (rev l))"
proof-
  have "l \<noteq> [] \<Longrightarrow> rev (butlast l) = tl (rev l)"
    by (induction l; auto)
  then have "(butlast (tl (rev l))) = rev (butlast (tl l))"
    proof(induction l)
      case (Cons a l)
      then show ?case
        by (cases "l = []"; auto)
    qed auto
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
    by \<^marker>\<open>provenance ai\<close> (cases l rule: rev_cases; auto)
qed

lemma two_mem_list_split:
  assumes "v1 \<in> set p" "v2 \<in> set p" "Q v1" "Q v2" "v1 \<noteq> v2"
  shows "\<exists>w x p1 p2 p3. p = p1 @ w # p2 @ x # p3 \<and> Q w \<and> Q x"
  using \<^marker>\<open>provenance ai\<close> extract_first_and_last[of v1 p v2 Q, OF assms]
  by \<^marker>\<open>provenance ai\<close> fastforce

lemma two_mem_list_split':
  assumes "v1 \<in> set p" "v2 \<in> set p" "Q v1" "Q v2" "v1 \<noteq> v2"
  shows "\<exists>w x p1 p2 p3. p = p1 @ w # p2 @ x # p3 \<and> Q w \<and> Q x \<and> (\<forall>x\<in>set p1. \<not> Q x)"
proof \<^marker>\<open>provenance ai\<close>-
  obtain a b as bs cs where "p = as @ a # bs @ b # cs" "Q a" "Q b" "\<forall>z\<in>set as. \<not> Q z"
    using extract_first_and_last[of v1 p v2 Q, OF assms]
    by auto
  then show ?thesis
    by (intro exI[of _ a] exI[of _ b] exI[of _ as] exI[of _ bs] exI[of _ cs]) simp
qed

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
    using extract_first_and_last[of v1 p v2 Q, OF assms(1-5)]
    by auto
  have ab: "a \<noteq> b"
    using assms(6) p
    by (simp add: distinct_append)
  show ?thesis
    using p Q pre suf ab
    by blast
qed

lemma split_list_pure_pref_suff:
  assumes "x\<in>(set p)" "\<forall>y\<in>set p. Q y  \<longrightarrow> x = y" "distinct p"
  shows "\<exists>p1 p2. p = p1 @ x # p2 \<and> (\<forall>x\<in>set p1. \<not> Q x) \<and> (\<forall>x\<in>set p2. \<not> Q x)"
proof-
  obtain p1 p2 where p1p2: "p = p1 @ x # p2"
    using \<^marker>\<open>provenance ai\<close> assms(1)
    by \<^marker>\<open>provenance ai\<close> (auto dest: split_list)
  then have "\<forall>x\<in>set p1. \<not> Q x" "\<forall>x\<in>set p2. \<not> Q x"
    using assms(2,3)
    by auto
  then show ?thesis
    using \<^marker>\<open>provenance ai\<close> p1p2
    by \<^marker>\<open>provenance ai\<close> blast
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
  unfolding \<^marker>\<open>provenance ai\<close> odd_cycle_def
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

lemma odd_cycle_length_edges_ge_3:
  assumes "odd_cycle p"
  shows "length (edges_of_path p) \<ge> 3"
  using \<^marker>\<open>provenance ai\<close> odd_cycleD[OF assms] odd_cycle_even_verts[OF assms]
  by \<^marker>\<open>provenance ai\<close> (simp add: edges_of_path_length; presburger)

lemma odd_cycle_length_verts_ge_4:
  assumes "odd_cycle p"
  shows "length p \<ge> 4"
  using \<^marker>\<open>provenance ai\<close> odd_cycle_length_edges_ge_3[OF assms] odd_cycle_even_verts[OF assms]
  by \<^marker>\<open>provenance ai\<close> (auto simp: edges_of_path_length elim: evenE)

lemma odd_cycle_set_butlast_tl:
  assumes "odd_cycle C"
  shows "set (butlast C) = set (tl C)"
  using odd_cycleD[OF assms] odd_cycle_nempty[OF assms]
  by (simp add: set_butlast_tl)

lemma odd_cycle_rev:
  assumes "odd_cycle C"
  shows "odd_cycle (rev C)"
  using assms
  by (auto split: if_splits simp: hd_rev last_rev Suc_le_length_iff numeral_3_eq_3 odd_cycle_def)

lemma odd_cycle_rev_alt_list:
  assumes "odd_cycle C" "alt_path M C"
  shows "alt_path M (rev C)"
  using odd_cycleD(1)[OF assms(1)]
                 
        even_alt_path_rev[OF odd_cycle_even_verts[OF assms(1)] _ assms(2)]
  by (simp add: even_alt_path_rev assms(2))

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
    using \<^marker>\<open>provenance ai\<close> match_blossomD(1)[OF assms]
    by \<^marker>\<open>provenance ai\<close> (auto dest: alt_list_append_1 simp flip: eq)
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

lemma match_blossom_stem_even:
  assumes  "match_blossom M stem C"
  shows "even (length stem)"
proof(rule ccontr, goal_cases)
  case 1
  hence  "odd (length (edges_of_path (stem @ [hd C])))"
    by(simp add: edges_of_path_length)
  then show ?case
    using assms match_blossomD(5) by blast
qed

lemma stem_even:
  assumes  "blossom E M stem C"
  shows "even (length stem)"
  using assms match_blossom_stem_even by auto

lemma matched_flower_vertex'_edge_in_flower:
  assumes "match_blossom M stem C" "{x, y} \<in> M" "x \<in> set (stem@C)" "matching M"
  shows "{x, y} \<in> set (edges_of_path (stem@C))"
proof-
  note match_blossomD= match_blossomD[OF assms(1)]
  have stemC_nempty:"stem @C \<noteq> []"
    using assms(3) by fastforce
  show ?thesis
  proof(cases "x= hd (stem @ C)")
    case True
      (*contradictory case: base of stem is matched*)
    hence False
      using match_blossomD(4) assms(2) edges_are_Vs[of x y M]
      by auto
    then show ?thesis
      by simp
  next
    case False
    obtain i where "i < length (stem @C)" "i > 0" "(stem@C) ! i = x"
      using False assms(3) stemC_nempty
      by(cases "stem @C")(fastforce simp add: in_set_conv_nth)+
    hence "\<exists> i. i +1 < length (stem @C) \<and> i > 0 \<and> (stem@C) ! i = x"
    proof(cases "x = last (stem@C)", goal_cases)
      case 1
      thus ?case
        using odd_cycleD(1,3)[OF match_blossomD(3)] False last_append[of _ C]
          nth_append_length_plus[of _ C "0"] assms(1) hd_conv_nth[of C]
        by(cases stem)(auto intro!: exI[of _ "length stem"])
    next
      case 2
      thus ?case
        using less_Suc_eq
        by(cases "stem @ C" rule: rev_cases)(auto intro!: exI[of _ i])
    qed
    then obtain i where i: "i +1 < length (stem @C)" "i > 0" "(stem@C) ! i = x"
      by auto
    have "x \<in> (edges_of_path (stem@C)) ! i"
      using edges_of_path_index i(1,3) by force
    moreover have "x \<in> (edges_of_path (stem@C)) ! (i - 1)"
      using edges_of_path_index[of "i-1" "stem@C"] i by simp
    moreover have "(edges_of_path (stem@C)) ! i \<in> M \<or> (edges_of_path (stem@C)) ! (i - 1) \<in> M"
    proof(cases "even i")
      case True
      have "Suc (i - 1) < length (stem @ C) \<and> odd (i-1)"
        using True i(1,2) by auto
      then show ?thesis
        using alt_path_intersected_with_matching[OF assms(4) match_blossomD(1)]
        by fast
    next
      case False
      have "Suc i < length (stem @ C) \<and> odd i"
        using False i(1) by force
      then show ?thesis
        using alt_path_intersected_with_matching[OF assms(4) match_blossomD(1)]
        by fast
    qed
    ultimately have "{x, y} = edges_of_path (stem @ C) ! i \<or>
         {x, y} = edges_of_path (stem @ C) ! (i-1)"
      using matchingD[OF assms(4,2), of "edges_of_path (stem @ C) ! i"]
        matchingD[OF assms(4,2), of "edges_of_path (stem @ C) ! (i-1)"]
      by auto
    moreover have "edges_of_path (stem @ C) ! (i-1) \<in> set (edges_of_path (stem @ C))"
      using i(1,2) edges_of_path_length[of "stem @ C"]
      by auto
    moreover have "edges_of_path (stem @ C) ! i \<in> set (edges_of_path (stem @ C))"
      using i(1,2) edges_of_path_length[of "stem @ C"]
      by auto
    ultimately show ?thesis
      by auto
  qed
qed

lemma matched_blossom_vertex'_partner_last_in_stem:
  assumes "match_blossom M stem C" "{x, y} \<in> M" "x = hd C" "matching M"
  shows "stem \<noteq> []" "y = last stem"
proof-
  note match_blossomD= match_blossomD[OF assms(1)]
  show  stem_nempty:"stem \<noteq> []"
    using local.match_blossomD(4) assms(2,3) edges_are_Vs[of x y M]
    by auto
  have "alt_path M (stem@[hd C])"
    using local.match_blossomD(1,3) odd_cycle_nempty[of "[]"]
      edges_of_path_append_2[of C stem]
      alt_list_append_1[of "\<lambda>R. R \<notin> M" "\<lambda>R. R \<in> M" "edges_of_path (stem @ [hd C])" "edges_of_path C"]
    by force
  hence "last (edges_of_path (stem@[hd C])) \<in> M"
    using stem_nempty edges_of_path_snoc[of stem "hd C"]
    by(auto intro!: last_even_P2[of "\<lambda>a. a \<notin> M" "\<lambda>a. a \<in> M"]
        match_blossom_stem_even[OF assms(1)]
        simp add: edges_of_path_length)
  hence "{last stem, hd C} = {x, y}"
    using assms stem_nempty last_snoc[of "edges_of_path stem" "{last stem, x}"]
      edges_of_path_snoc[of stem x]
    by (intro matching_revD) force+
  thus "y = last stem"
    using assms(3) by (auto simp add: doubleton_eq_iff)
qed

lemma blossom_matched_in_C:
  assumes "match_blossom M stem C" "matching M"
  shows "set (tl (butlast C)) \<subseteq> Vs (M \<lbrakk>set C\<rbrakk>)"
proof(rule, goal_cases)
  case (1 x)
  hence "even (length C)"
    using assms(1) match_blossomD(3) odd_cycle_even_verts by blast
  moreover have "tl (butlast C) = butlast (tl C)"
    by (simp add: butlast_tl)
  ultimately obtain i where i: "x \<in> edges_of_path C ! i" "Suc i <length C" "odd i"
    using verts_of_odd_edges[of C, symmetric] 1
    by (auto simp add: vs_member)
  moreover hence "edges_of_path C ! i \<in> M"
    using alt_path_intersected_with_matching[OF assms(2), of C]
    using assms(1) match_blossom_alt_cycle by fastforce
  ultimately have "edges_of_path C ! i \<in> M \<lbrakk> set C\<rbrakk>"
    by (simp add: edges_of_path_length edges_of_path_subset_path in_graph_inter_VsI)
  thus ?case
    using i by auto
qed

lemma blossom_matched:
  assumes "match_blossom M stem C" "matching M"
  shows "set (tl (butlast C)) \<subseteq> Vs M"
  using blossom_matched_in_C[OF assms] Vs_subset[OF graph_inter_Vs_subset(1)]
  by fast

lemma flower_matched_in_C:
  assumes "match_blossom M stem C" "matching M" "stem \<noteq> []"
  shows "set (tl (stem @ C)) \<subseteq> Vs (M \<lbrakk> set (stem @ C)\<rbrakk>)"
proof(rule,  goal_cases)
  case (1 x)
  have even_len:"even (length (stem @ C))"
    using assms(1) odd_cycle_even_verts[of C] match_blossom_stem_even[of M stem C]
    by (auto dest: match_blossomD(3))
  have "butlast (tl (stem @ C)) = tl stem @ butlast C"
    using  assms(1,3) butlast_append[of "tl stem" C] odd_cycle_nempty
    by (auto dest: match_blossomD(3))
  moreover have "set (butlast C) = set C"
    using last_in_set match_blossomD(3)[OF assms(1)] odd_cycleD[of C]
    by(cases C rule: list_cases_hd_and_last) auto
  ultimately have "x \<in>  set (butlast (tl (stem @ C)))"
    using 1 assms(3) by(cases stem) auto
  then obtain i where i: "x \<in> edges_of_path (stem @ C) ! i" "Suc i < length (stem @ C)" "odd i"
    using verts_of_odd_edges[of "stem@C", symmetric] even_len
    by(auto simp add: vs_member)
  moreover hence "edges_of_path (stem@C) ! i \<in> M"
    "edges_of_path (stem@C) ! i \<in> set (edges_of_path (stem@C))"
    using alt_path_intersected_with_matching[OF assms(2), of "stem@C"]
      alt_path_prefix assms(1) match_blossomD(1) by fast+
  ultimately have "edges_of_path (stem@C) ! i \<in> M \<lbrakk> set (stem @ C)\<rbrakk>"
    using edges_of_path_subset_path[of "edges_of_path (stem @ C) ! i" "stem@C"]
    by(auto intro!: in_graph_inter_VsI)
  thus ?case
    using i by auto
qed

lemma flower_matched:
  assumes "match_blossom M stem C" "matching M" "stem \<noteq> []"
  shows "set (tl (stem @ C)) \<subseteq> Vs M"
  using flower_matched_in_C[OF assms] Vs_subset[OF graph_inter_Vs_subset(1)]
  by fast

lemma blossom_stem_nempty_bloss_base_parter:
  assumes "match_blossom M stem C" "matching M" "stem \<noteq> []"
  shows "{hd C, last stem} \<in> M"
proof-
  note match_blossomD= match_blossomD[OF assms(1)]
  have pos: "Suc (length stem - 1) < length (stem @ C)"
    by (simp add: assms(3) local.match_blossomD(3) odd_cycle_nempty)
  hence "edges_of_path (stem@C) ! (length stem - 1) = {last stem, hd C}"
    by(subst edges_of_path_index)
      (auto simp add: assms(3) hd_conv_nth last_conv_nth nth_append)
  moreover have "edges_of_path (stem@C) ! (length stem - 1) \<in> M"
    using pos assms(3) match_blossom_stem_even[OF assms(1)]
      edges_of_path_length[of "stem @ C"] edges_of_path_length[of stem] pos
      zero_less_diff[of "length (stem @ C) - 1" "length (edges_of_path stem)"]
    by(auto intro!: alternating_list_odd_index[OF match_blossomD(1)])
  ultimately show ?thesis
    by(auto simp add: insert_commute)
qed

lemma blossom_cycle_longer_2:
  assumes "match_blossom M stem cyc"
  shows "card (set cyc) \<ge> 2"
proof-
  have "distinct (butlast cyc)" "length cyc \<ge> 3"
    using match_blossomD[OF assms] odd_cycleD by auto
  hence "card (set (butlast cyc)) \<ge> 2"
    by (simp add: distinct_card)
  moreover have "card (set (butlast cyc)) \<le> card (set cyc)"
    by (rule card_mono[OF finite_set]) (auto dest: in_set_butlastD)
  ultimately show ?thesis
    by linarith
qed

lemma blossom_diff:
assumes
  "graph_invar E"
  "match_blossom M stem cyc"
  "path E (stem @ cyc)"
shows "((Vs E) - set cyc) \<subset> (Vs E)" (is "?s \<subset> _")
proof-
  have "set cyc \<subseteq> Vs E"
    using path_suff subset_path_Vs assms
    by metis
  then have "Vs E - ?s = set cyc"
    by auto
  moreover have "?s \<subseteq> Vs E"
    by auto
  moreover have "card (set cyc) \<ge> 2"
    using blossom_cycle_longer_2[OF assms(2)] .
  moreover have "finite (Vs E)"
    by (simp add: assms)
  ultimately show ?thesis
    by auto
qed

lemma match_blossom_distinct_tl:
  assumes "match_blossom M stem cyc"
  shows "distinct (tl cyc)"
proof-
  obtain \<^marker>\<open>provenance ai\<close> a b cs where cyc: "cyc = a # b # cs"
    using odd_cycleD(1)[OF match_blossomD(3)[OF assms]]
    by (cases cyc; cases "tl cyc"; auto)
  have cycle_shape: "distinct (butlast cyc)" "hd cyc = last cyc"
    using match_blossomD[OF assms] odd_cycleD
    unfolding distinct_append[symmetric]
    by auto
  then have "distinct (tl (butlast cyc))" "hd cyc \<notin> set (tl (butlast cyc))"
    using \<^marker>\<open>provenance ai\<close> distinct_tl
    by \<^marker>\<open>provenance ai\<close> (auto simp: cyc)
  then have "distinct ((tl (butlast cyc)) @ [last cyc])"
    using cycle_shape(2)
    by auto
  moreover have "(tl (butlast cyc)) @ [last cyc] = tl cyc" if "length cyc \<ge> 3" for cyc::"'a list"
    using that
  proof(induction cyc)
    case Nil
    then show ?case
      by auto
  next
    case (Cons a' cyc')
    then show ?case
      by auto
  qed
  moreover have "length cyc \<ge> 3"
    using odd_cycleD(1)[OF match_blossomD(3)[OF assms]]
    by auto
  ultimately show ?thesis
    by auto
qed

lemma cycle_set_tl_eq_butlast:
  assumes "match_blossom M stem cyc"
  shows "set (tl cyc) = set (butlast cyc)"
  using \<^marker>\<open>provenance ai\<close> match_blossomD(3)[OF assms]
  by \<^marker>\<open>provenance ai\<close> (auto simp: set_butlast_tl[symmetric] odd_cycle_nempty odd_cycleD(3))

lemma nempty_blossom_stem_last_stem_hd_C_in_C_Delta:
  assumes "match_blossom M stem C" "stem \<noteq> []" "matching M"
  shows "{last stem, hd C} \<in> Delta M (set C)"
proof-
  have "{hd C, last stem} \<in> M"
    using assms
    by(auto intro!: blossom_stem_nempty_bloss_base_parter)
  moreover have "hd C \<in> set C"
    using assms(1) list.set_sel(1) match_blossomD(3) odd_cycle_nempty by blast
  moreover have "last stem \<notin> set C"
    using assms match_blossomD[of M stem C]
    by (cases stem rule: rev_cases; cases C rule: list_cases_hd_and_last)
      (auto simp add: odd_cycle_def)
  ultimately show ?thesis
    by (auto intro: in_DeltaI simp add: insert_commute)
qed

lemma match_flower_reverse_blossom:
  assumes "match_blossom M stem C"
  shows  "match_blossom M stem (rev C)"
proof-
  note match_blossomD = match_blossomD[OF assms(1)]
  have C_nempty: "C \<noteq> []"
    using local.match_blossomD(3) odd_cycle_nempty by blast
  have "alt_path M (stem @ rev C)"
  proof(subst edges_of_path_append_2, goal_cases)
    case 1
    then show ?case 
      by (simp add: local.match_blossomD(3) odd_cycle_nempty)
  next
    case 2
    then show ?case
    proof(rule alt_list_append_3, goal_cases)
      case 1
      then show ?case 
        using match_blossomD(1)
        by(auto simp add: edges_of_path_append_2[OF C_nempty] hd_rev match_blossomD(3) odd_cycleD(3)
                    dest: alt_list_append_1)
    next
      case 2
      then show ?case
       using match_blossomD(3) assms  
       by (auto intro!: even_alt_path_rev 
                 intro: match_blossom_alt_cycle 
                  dest: odd_cycleD(1) 
              simp add: odd_cycle_even_verts)
    next
      case 3
      then show ?case
        using match_blossomD(5) odd_cycleD[OF match_blossomD(3)] 
        by(cases C rule: rev_cases) auto
    qed
  qed
  moreover have "distinct (stem @ butlast (rev C))"
    using assms match_blossomD(2,3) match_blossom_distinct_tl odd_cycle_set_butlast_tl by fastforce
  moreover have "odd_cycle (rev C)"
    by (simp add: local.match_blossomD(3) odd_cycle_rev)
  moreover have "hd (stem @ rev C) \<notin> Vs M"
    using match_blossomD(3,4) hd_rev[of C] odd_cycleD(3)[of "stem @ C"]
    by(cases stem) auto
  moreover have "even (length (edges_of_path (stem @ [hd (rev C)])))"
    by (simp add: calculation(3) last_rev match_blossomD(5) odd_cycleD(3))
  ultimately show ?thesis
    by(auto simp add: match_blossom_def)
qed

lemma match_blossom_path_rev_stem:
  assumes 
    path: "path G (stem @ C)" and
    match_blossom: "match_blossom M stem C"
  shows "path G (C @ (rev stem))"
  apply(cases stem)
  subgoal using path by simp
  subgoal apply(rule path_append)
    subgoal using path_suff[OF path] .
    subgoal using rev_path_is_path[OF path_pref[OF path]] .
    subgoal by (smt match_blossom match_blossomD(3) edge_between_pref_suff hd_rev insert_commute
                    list.simps(3) odd_cycleD(3) odd_cycle_nempty path)
    done
  done

lemma flower_reverse_blossom:
  assumes  "blossom E M stem C" 
  shows   "blossom E M stem (rev C)"  
proof-
  show ?thesis
    using assms rev_path_is_path_iff[of E "stem @ rev C"] match_blossom_path_rev_stem[of E stem C M]
    by(auto intro: match_flower_reverse_blossom)
qed

subsection \<open>Alternating Paths and Odd Cycles\<close>

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
    using \<^marker>\<open>provenance ai\<close> cycle[unfolded odd_cycle_def]
    by \<^marker>\<open>provenance ai\<close> (cases p; simp add: distinct_edges_of_vpath split: if_splits; use alternating_list_odd_last inM in blast)
  moreover have "length (edges_of_path p) \<ge> 2"
    using \<^marker>\<open>provenance ai\<close> cycle(1)
    unfolding \<^marker>\<open>provenance ai\<close> odd_cycle_def
    by \<^marker>\<open>provenance ai\<close> (auto simp: edges_of_path_length)
  ultimately have "hd (edges_of_path p) \<noteq> last (edges_of_path p)"
    by \<^marker>\<open>provenance ai\<close> (cases "edges_of_path p"; auto)
  moreover have "last p \<in> (hd (edges_of_path p))" "last p \<in> (last (edges_of_path p))"
    using \<^marker>\<open>provenance ai\<close> cycle
    unfolding \<^marker>\<open>provenance ai\<close> odd_cycle_def
    using \<^marker>\<open>provenance ai\<close> alternating_list_odd_last inM
    by \<^marker>\<open>provenance ai\<close> (auto intro: hd_v_in_hd_e)
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
      show ?thesis
      proof \<^marker>\<open>provenance ai\<close>(cases p'')
        case Nil
        then show ?thesis
          using ass.prems cons1 cons2
          by simp
      next
        case (Cons y ys)
        then have alt: "{a', a''} \<notin> M" "{a'', y} \<in> M" "alt_path M (y # ys)"
          using ass.prems(1) cons1 cons2
          by (auto simp: alt_list_step)
        show ?thesis
        proof(cases "v = a'' \<or> v = y")
          case True
          then show ?thesis
            using alt(2) cons1 cons2 Cons
            by auto
        next
          case False
          then have "v \<in> set ys"
            using ass.prems(2,3) cons1 cons2 Cons
            by auto
          moreover have "length (y # ys) < length p"
            using cons1 cons2 Cons
            by simp
          ultimately have "\<exists>e\<in>set (edges_of_path (y # ys)). v \<in> e \<and> e \<in> M"
            using ass.hyps[rule_format, of "length (y # ys)" "y # ys"] ass.prems(4) alt(3) cons1 cons2 Cons False
            by auto
          then show ?thesis
            using cons1 cons2 Cons
            by auto
        qed
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
    using \<^marker>\<open>provenance ai\<close> p1p2(3)
    by \<^marker>\<open>provenance ai\<close> (cases p2; auto)
  moreover have "edges_of_path C = (edges_of_path (p1 @ [v1])) @ (edges_of_path (v1 # p2))"
    using edges_of_path_append_2[where p' = "v1 # p2"] p1p2(1)
    by auto
  ultimately have eqC: "edges_of_path C = (edges_of_path p1) @ {last p1, v1} # {v1, hd p2} # edges_of_path p2"
    using p1p2(1)
    by auto
  then have i: "{last p1, v1} \<in> M \<or> {v1, hd p2} \<in> M"
    using \<^marker>\<open>provenance ai\<close> odd_cycleD(2)[OF assms(1)] assms(2)[unfolded eqC]
    by \<^marker>\<open>provenance ai\<close> (cases "{last p1, v1} \<in> M"; auto dest: alt_list_append_1'')
  have "last p1 \<in> set C" "hd p2 \<in> set C"
    using p1p2
    by auto
  then have ii: "{last p1, v1} \<noteq> e" "{v1, hd p2} \<noteq> e"
    using assms(4-6)
    by fastforce+

  have \<^marker>\<open>provenance ai\<close> "v1 \<in> Vs M"
    using assms(3,6)
    by (auto simp: Vs_def)
  then \<^marker>\<open>provenance ai\<close> have \<^marker>\<open>provenance ai\<close> "\<exists>!f. f \<in> M \<and> v1 \<in> f"
    using assms(7)
    unfolding matching_def2
    by blast
  then \<^marker>\<open>provenance ai\<close> show False
    using \<^marker>\<open>provenance ai\<close> i ii assms(3,6)
    by \<^marker>\<open>provenance ai\<close> auto
qed

subsection \<open>Matching Symmetric Differences\<close>

lemma symm_diff_is_matching':
  assumes 
    "alt_path M p"
    "matching M"
    "hd p \<notin> Vs M"
    "length p \<ge> 2 \<longrightarrow> last (edges_of_path p) \<in> M"
    "distinct p"
  shows "matching (M \<oplus> (set (edges_of_path p)))"
proof (rule symm_diff_is_matching[OF assms(1-3) _ assms(5)])
  assume even: "2 \<le> length p \<and> even (length p)"
  then have "odd (length (edges_of_path p))"
    by (auto simp add: edges_of_path_length)
  then have "last (edges_of_path p) \<notin> M"
    by (rule alternating_list_odd_last[OF assms(1)])
  then show "last p \<notin> Vs M"
    using assms(4) even
    by blast
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
      by simp
  next
    case False
    then have "y \<in> set l'"
      using Cons.prems
      by auto
    then have "Q (last (find_pfx Q l'))"
      using Cons.IH Cons.prems(2)
      by blast
    moreover have "find_pfx Q l' \<noteq> []"
      using \<open>y \<in> set l'\<close>
      by (cases l'; auto)
    ultimately show ?thesis
      using False
      by simp
  qed
qed

lemma find_pfx_works_2:
  assumes "y \<in> set l" "Q y"
  shows "Q(last (find_pfx Q (rev l)))"
  using assms
  by (auto intro: find_pfx_works_1)

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
    by \<^marker>\<open>provenance ai\<close> auto
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
    by \<^marker>\<open>provenance ai\<close> simp
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
  moreover \<^marker>\<open>provenance ai\<close> have \<^marker>\<open>provenance ai\<close> "last (find_pfx Q l) = last (find_pfx Q (l' @ x # y # l2))"
    using nQ Cons.prems(5) find_pfx_nempty[of x "l' @ x # y # l2" Q] Cons.prems(1)
    by auto
  moreover \<^marker>\<open>provenance ai\<close> have \<^marker>\<open>provenance ai\<close> "last (find_pfx Q (rev l)) = last (find_pfx Q (rev (l' @ x # y # l2)))"
    using nQ Cons.prems(2,5) find_pfx_append[of Q y "rev l2" "x # rev l'"] find_pfx_append[of Q y "rev l2" "x # rev l' @ [a']"]
    by auto
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
    using \<^marker>\<open>provenance ai\<close> odd_cycleD(1,3)[OF cycle(1)] cycle(5)
    by \<^marker>\<open>provenance ai\<close> (intro edges_of_path_find_pfx cycle; simp add: hd_rev)
  have rev_eop: "(edges_of_path (rev p)) = rev (edges_of_path p)"
    by (simp add: edges_of_path_rev)
  obtain p' p'' where p'p''[simp]: "p = p' @ (v # p'')"
    using \<^marker>\<open>provenance ai\<close> cycle
    by \<^marker>\<open>provenance ai\<close> (auto dest: split_list_last)
  show ?g2
    unfolding eofp_pfx rev_eofp_pfx rev_eop
  proof(intro find_pfx_alt_list[where x = "{last p', v}" and y = "{v, hd p''}" and ?l1.0 = "(edges_of_path p')" and ?l2.0 = "(edges_of_path p'')"] cycle, goal_cases)
    case 1
    show ?case
      by simp
  next
    case 2
    show ?case
      by simp
  next
    case 3
    show ?case
      using assms(3,5)
      by (intro ballI impI where_is_v; cases p'; auto)
  next
    case 4
    show ?case
    proof-
      have "v \<notin> set p'"
        using \<^marker>\<open>provenance ai\<close> cycle
        by \<^marker>\<open>provenance ai\<close> (cases p'; auto simp: distinct_append)
      moreover have "v \<notin> set p''"
        using \<^marker>\<open>provenance ai\<close> cycle
        by \<^marker>\<open>provenance ai\<close> (cases p'; auto simp: distinct_append)
      ultimately show ?thesis
        by (auto simp add: v_in_edge_in_path_gen)
    qed
  next
    case 5
    have \<^marker>\<open>provenance ai\<close> nn: "p' \<noteq> []" "p'' \<noteq> []"
      using cycle(5) odd_cycleD(3)[OF cycle(1)]
      by auto
    then \<^marker>\<open>provenance ai\<close> show ?case
      using \<^marker>\<open>provenance ai\<close> edges_of_path_append_3[of p' "v # p''"]
      by \<^marker>\<open>provenance ai\<close> (cases p''; auto)
  qed
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
    by \<^marker>\<open>provenance ai\<close> simp
qed

end
