theory Graph_Quotient
imports choose "Berge_Lemma.Berge"
         
begin

subsection \<open>List Auxiliary Lemmas\<close>

lemma neq_Nil_conv_2:
  "l \<noteq> [] \<longleftrightarrow> (\<exists>l' x. l = l' @ [x])"
  by (metis snoc_eq_iff_butlast)

lemma tl_distinct_rev:
  assumes "hd l = last l" "distinct (tl l)"
  shows "distinct (tl (rev l))"
proof-
  have "l \<noteq> [] \<Longrightarrow> rev (butlast l) = tl (rev l)"
    by (induction l; auto)
  then have "(butlast (tl (rev l))) = rev (butlast (tl l))"
    apply(induction l; auto)
    subgoal for a l
      by(cases "l = []"; auto)
    done
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
  then show ?case by auto
next
  case (Cons a l)
  then show ?case
    apply auto
    subgoal by (metis distinct_butlast not_distinct_conv_prefix snoc_eq_iff_butlast)
    subgoal by (simp add: distinct_butlast)
    done
qed

lemma two_mem_list_split:
  assumes "v1 \<in> set p" "v2 \<in> set p" "Q v1" "Q v2" "v1 \<noteq> v2"
  shows "\<exists>w x p1 p2 p3. p = p1 @ w # p2 @ x # p3 \<and> Q w \<and> Q x"
  using assms
proof(induction p)
  case Nil
  then show ?case by simp
next
  case (Cons a' p')
  then show ?case
    by (auto; metis append_Nil in_set_conv_decomp_first append_Cons) 
qed

lemma two_mem_list_split':
  assumes "v1 \<in> set p" "v2 \<in> set p" "Q v1" "Q v2" "v1 \<noteq> v2"
  shows "\<exists>w x p1 p2 p3. p = p1 @ w # p2 @ x # p3 \<and> Q w \<and> Q x \<and> (\<forall>x\<in>set p1. \<not> Q x)"
  using assms
proof(induction p)
  case Nil
  then show ?case by simp
next
  case (Cons a' p')
  then show ?case
    apply auto 
    subgoal using split_list by fastforce
    subgoal using assms(4) set_empty split_list by fastforce
    by(metis Cons_eq_appendI all_not_in_conv append.left_neutral append_Cons assms(3) assms(4) empty_set set_ConsD)+
qed

lemma one_mem_pure_suff:
  assumes "v \<in> set p" "Q v"
  shows "\<exists>w p1 p2 . p = p1 @ w # p2 \<and> Q w \<and> (\<forall>x\<in>set p2. \<not> Q x)"
  using assms
proof(induction p)
  case Nil
  then show ?case by simp
next
  case (Cons a' p')
  then show ?case
    apply auto 
    subgoal by (metis (no_types, lifting) Cons.prems(1) split_list_last_prop)
    subgoal by (meson Cons_eq_appendI)
    subgoal by (metis append_Cons)
    done
qed

lemma one_mem_pure_pref:
  assumes "v \<in> set p" "Q v"
  shows "\<exists>w p1 p2 . p = p1 @ w # p2 \<and> Q w \<and> (\<forall>x\<in>set p1. \<not> Q x)"
  using assms
proof(induction p)
  case Nil
  then show ?case by simp
next
  case (Cons a' p')
  then show ?case
    apply auto 
    subgoal by fastforce
    subgoal by (metis Cons_eq_append_conv all_not_in_conv append_Cons assms(2) list.set(1) set_ConsD)
    subgoal by (metis Cons_eq_append_conv all_not_in_conv append_Cons list.set(1) set_ConsD)
    done
qed

lemma two_mem_list_split'':
  assumes "v1 \<in> set p" "v2 \<in> set p" "Q v1" "Q v2" "v1 \<noteq> v2" "distinct p"
  shows "\<exists>p1 p2 p3 w x. p = p1 @ w # p2 @ x # p3 \<and> Q w \<and> Q x \<and> w \<noteq> x \<and> (\<forall>x\<in>set p1. \<not> Q x) \<and> (\<forall>x\<in>set p3. \<not> Q x)"
  using assms
proof(induction p arbitrary: v1 v2)
  case Nil
  then show ?case by simp
next
  case (Cons a p)
  show ?case
  proof(cases "v1 = a")
    case v1_eq_a: True
    show ?thesis
    proof(cases "v2 = a")
      case v2_eq_a: True
      then show ?thesis
        using Cons v1_eq_a 
        by simp
    next
      case v2_neq_a: False
      then have "v2 \<in> set p"
        using Cons        
        by auto
      then obtain w p1 p2 where "p = p1 @ w # p2 \<and> Q w \<and> (\<forall>x\<in>set p2. \<not> Q x)"
        using one_mem_pure_suff Cons
        by metis
      then have "a # p = [] @ v1 # p1 @ w # p2 \<and> Q v1 \<and> Q w \<and> v1 \<noteq> w \<and> (\<forall>x\<in>set []. \<not> Q x) \<and> (\<forall>x\<in>set p2. \<not> Q x)"
        using v1_eq_a Cons.prems by auto
      then show ?thesis
        by metis
    qed
  next
    case v1_neq_a: False
    show ?thesis
    proof(cases "v2 = a")
      case v2_eq_a: True
      then have "v1 \<in> set p"
        using Cons        
        by auto
      then obtain w p1 p2 where "p = p1 @ w # p2 \<and> Q w \<and> (\<forall>x\<in>set p2. \<not> Q x)"
        using one_mem_pure_suff Cons
        by metis
      then have "a # p = [] @ v2 # p1 @ w # p2 \<and> Q v2 \<and> Q w \<and> v2 \<noteq> w \<and> (\<forall>x\<in>set []. \<not> Q x) \<and> (\<forall>x\<in>set p2. \<not> Q x)"
        using v2_eq_a Cons.prems by auto
      then show ?thesis
        by metis
    next
      case v2_neq_a: False
      show ?thesis
      proof(cases "Q a")
        case Qa: True
        have "v1 \<in> set p"
          using Cons v1_neq_a
          by auto
        then obtain w p1 p2 where "p = p1 @ w # p2 \<and> Q w \<and> (\<forall>x\<in>set p2. \<not> Q x)"
          using one_mem_pure_suff Cons
          by metis
        then have "a # p = [] @ a # p1 @ w # p2 \<and> Q a \<and> Q w \<and> a \<noteq> w \<and> (\<forall>x\<in>set []. \<not> Q x) \<and> (\<forall>x\<in>set p2. \<not> Q x)"
          using Cons.prems Qa by auto
        then show ?thesis
          by metis
      next
        have "v2 \<in> set p"
          using Cons v2_neq_a
          by auto
        moreover have "v1 \<in> set p"
          using Cons v1_neq_a
          by auto
        ultimately have "\<exists>p1 p2 p3 w x . p = p1 @ w # p2 @ x # p3 \<and> Q w \<and> Q x \<and> w \<noteq> x \<and> (\<forall>x\<in>set p1. \<not> Q x) \<and> (\<forall>x\<in>set p3. \<not> Q x)"
          apply(intro Cons.IH[of v1 v2])
          using Cons.prems by auto
        then obtain w x p1 p2 p3 where wxp1p2p3: "a#p = (a#p1) @ w # p2 @ x # p3 \<and> Q w \<and> Q x \<and> w \<noteq> x \<and> (\<forall>x\<in>set p1. \<not> Q x) \<and> (\<forall>x\<in>set p3. \<not> Q x)"
          by auto
        moreover case False
        ultimately show ?thesis
          by (metis set_ConsD)
      qed
    qed
  qed
qed

lemma split_list_pure_pref_suff:
  assumes "x\<in>(set p)" "\<forall>y\<in>set p. Q y  \<longrightarrow> x = y" "distinct p"
  shows "\<exists>p1 p2. p = p1 @ x # p2 \<and> (\<forall>x\<in>set p1. \<not> Q x) \<and> (\<forall>x\<in>set p2. \<not> Q x)"
proof-
  obtain p1 p2 where p1p2: "p = p1 @ x # p2"
    using assms(1)
    by (meson split_list_last)
  then have "\<forall>x\<in>set p1. \<not> Q x" "\<forall>x\<in>set p2. \<not> Q x"
    using assms(2,3)
    by auto
  then show ?thesis
    using p1p2
    by metis
qed

lemma card2_subset:
  assumes "card s = 2" "s \<noteq> {}"
  shows "\<exists>x y. {x, y} \<subseteq> s"  
  using assms by(auto simp: numeral_2_eq_2 card_le_Suc_iff)

subsection \<open>Odd Cycles\<close>

definition odd_cycle where
  "odd_cycle p = ( (length p \<ge> 3) \<and> odd (length (edges_of_path p)) \<and> hd p = last p)"

lemma odd_cycle_nempty:
  assumes "odd_cycle p"
  shows "p \<noteq> []"
  unfolding odd_cycle_def
  by (metis One_nat_def assms list.size(3) not_less_eq_eq one_le_numeral odd_cycle_def)

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
    using edges_of_path_snoc snoc_eq_iff_butlast by fastforce
  then show ?thesis
    using match_blossomD(1)[OF assms]
    by auto
next
  have "C \<noteq> []"
    using assms match_blossomD(3) odd_cycle_nempty by auto
  then have "edges_of_path (stem @ [hd C]) @ edges_of_path C  = edges_of_path (stem @ C)"
    using edges_of_path_append_2 by force
  then have "alt_path M (stem @ [hd C])"
    by (metis alt_list_append_1 match_blossomD(1)[OF assms])
  moreover case False
  ultimately have "last (edges_of_path (stem @ [hd C])) \<in> M"
    using match_blossomD(5)[OF assms]
    using alternating_eq_iff_even alternating_list_even_last by blast
  then show ?thesis
    using alt_list_append_1' match_blossomD(1)[OF assms]
    by (metis False \<open>edges_of_path (stem @ [hd C]) @ edges_of_path C = edges_of_path (stem @ C)\<close>)
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



locale pre_quot = choose sel +
              graph_abs E 
  for sel::"'a set \<Rightarrow> 'a" and E::"'a set set" (* +
  fixes rev_P s u
  assumes good_quot_map: (*"\<forall>v\<in>s. P v = v"*) "u\<notin>s" (*"(\<forall>v. v\<notin>s \<longrightarrow> P v = u)"*) and
          rev_map: "s \<subset> Vs E \<Longrightarrow> (rev_P E u) \<in> Vs E - s" "\<And>v. v\<in>s \<Longrightarrow> rev_P E v = v"*)
         

locale quot = pre_quot sel E for sel E +
  fixes s::"'a set" and u::'a
  assumes good_quot_map: "u \<notin> s" "s \<subset> Vs E"
begin

abbreviation "P v \<equiv> (if v \<in> s then v else u)"
abbreviation "rev_P v \<equiv> (if v \<noteq> u then v else sel (Vs E - s))"

lemma sel'[simp]: "sel (Vs E - s) \<in> (Vs E - s)"
  apply(rule sel)
  using good_quot_map
  by (auto simp add: finite_Vs)

lemma rev_map_works_1:
  assumes "v \<in> s"
  shows "rev_P v = v"
  using assms rev_map good_quot_map
  by (auto simp add: subset_iff)


lemma rev_map_works_2:
  assumes "u \<in> Vs (quot_graph P E)" "s \<subset> Vs E"
  shows "(rev_P u) \<in> Vs E \<and> (rev_P u) \<notin> s"
proof-
  have "(rev_P u) \<in> Vs E \<and> P (rev_P u) = u"
    using assms rev_map good_quot_map sel'
    by (auto simp: quot_graph_def)
  then show ?thesis
    using good_quot_map
    by auto
qed

lemma edge_in_quot_in_graph_1:
  assumes edge: "(P ` e) \<in> (quot_graph P E)" "e \<subseteq> s"
  shows "e \<in> E"
  using assms good_quot_map
  unfolding quot_graph_def image_def
  by (smt dual_order.antisym mem_Collect_eq subset_eq)

lemma edge_in_quot_in_graph_1':
  assumes edge: "e \<in> (quot_graph P M)" "e \<subseteq> s" "M \<subseteq> E"
  shows "e \<in> M"
  using assms good_quot_map
  unfolding quot_graph_def Vs_def image_def
  apply simp
  by (smt dual_order.antisym mem_Collect_eq subset_eq)

(*lemma edge_in_quot_in_graph_2:
  assumes edge: "(P ` e) \<in> (quot_graph P E)" "u \<in> P ` e"
  shows "\<exists>e' v. e' \<in> E \<and> P ` e' = P ` e \<and> v \<notin> s \<and> v \<in> e'"
proof-
  obtain e' v where e'v: "e' \<in> E \<and> P ` e' = P`e \<and> v \<notin> s \<and> v \<in> e'"
    using assms good_quot_map
    apply (auto simp: quot_graph_def Vs_def image_def)
    sledgehammer
  then have "e \<inter> s = e' \<inter> s"
    using good_quot_map
    unfolding image_def
    by auto
  then show ?thesis
    using e'v
    by auto
  apply (auto simp add: quot_graph_def image_def)
*)

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
  shows "path E (map rev_P p)"
  using assms
proof(induction )
case (path0)
  then show ?case
   by simp
next
  case (path1 v)
  then show ?case
    using rev_map_works_1 good_quot_map
    apply simp
    by blast
next
  case (path2 v v' vs)
  then show ?case
    using rev_map_works_1
    using edge_in_quot_in_graph_1' by auto
qed

lemma edge_of_path_in_graph_iff_in_quot:
  assumes "set p \<subseteq> s" "e \<in> set (edges_of_path p)" "M \<subseteq> E"
  shows "e \<in> M \<longleftrightarrow> e \<in> quotG M"
proof-
  have e_sub_s: "e \<subseteq> s"
    using assms
    by (meson subset_iff v_in_edge_in_path_gen)
  then have imP: "e = P ` e"
    using assms
    by(simp add: image_def subset_iff)
  then have "e \<in> quotG M" if "e \<in> M"
    unfolding quot_graph_def
    using that
    using e_sub_s good_quot_map(1) by blast
  moreover have "e \<in> M" if "e \<in> quotG M"
    using e_sub_s edge_in_quot_in_graph_1' that \<open>M \<subseteq> E\<close> by auto
  ultimately show ?thesis
    by blast
qed

lemma rev_map_map:
  assumes "set p \<subseteq> s" "s \<subseteq> t"
  shows "(map rev_P p) = p"
  using rev_map
  by (simp add: assms(1) assms(2) map_idI rev_map_works_1 set_rev_mp)

lemma quot_alt_path_iff_alt_path:
  assumes path: "set p \<subseteq> s" "s \<subseteq> t"
  shows "alt_list (\<lambda>e. e \<notin> (quotG E)) (\<lambda>e. e \<in> (quotG E)) (edges_of_path p) =
                      alt_list (\<lambda>e. e \<notin> E) (\<lambda>e. e \<in> E) (edges_of_path (map rev_P p))"
  using edge_of_path_in_graph_iff_in_quot[OF path(1)]
  by(auto intro!: alt_list_cong_eq simp: rev_map_map[OF path])

lemma path_is_quot_path':
  assumes path: "path (quotG E) p" "set p \<subseteq> s"
  shows "path E p"
  using rev_map_map path_is_quot_path[OF assms] path(2) good_quot_map
  by auto

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
    apply(rule alt_list_cong_eq)
    using edge_of_path_in_graph_iff_in_quot path assms
    by blast+
  moreover {
    assume "length p \<ge> 2"
    then have "p \<noteq> []"
      by (auto simp: Suc_le_length_iff)
    then have "hd p \<in> s" "last p \<in> s"
      using path
      by auto
  } then have "length p \<ge> 2 \<and> hd p \<notin> Vs M \<and> last p \<notin> Vs M \<longleftrightarrow> length p \<ge> 2 \<and> hd p \<notin> Vs (quotG M) \<and> last p \<notin> Vs (quotG M)"
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
    using Vs_quot_graph
    by (smt (verit, ccfv_SIG))
  then show ?case
    using v_in_quot_iff_minus_u path1
    by (simp add: good_quot_map(1))
next
  case (path2 v v' vs)
  then show ?case
    using good_quot_map edge_in_graph_in_quot[OF path2.hyps(1)]
    apply (auto simp: image_def)
    by (smt (verit, ccfv_threshold) \<open>\<And>P. P ` {v, v'} \<in> quot_graph P E\<close> image_empty image_insert)

qed

lemma qug_path_iff_case_1_ii:
  assumes path: "set p \<subseteq> s" 
  shows "path E p = path (quotG E) p"
  using path path_is_quot_path'[OF _ path] path_is_quot_path_diff_u[OF _ path] good_quot_map
  apply auto
  by (smt (verit, del_insts) map_idI path(1) subset_eq)


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
      apply simp
      using good_quot_map(2) by blast
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
        apply(rule path_is_quot_path')
        using Cons
        by auto
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
  then have "v \<noteq> x" using matching
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
      apply(intro disjI1 alternating_list_gt)
      using alt_list_not_commute
        True
      by blast+
  next
    have "odd (length (edges_of_path p))"
      using cycle
      unfolding odd_cycle_def
      by simp
    then have "length (filter (\<lambda>e. e \<notin> M) ?ep) \<noteq> length (filter (\<lambda>e. e \<in> M) ?ep)"
      apply(intro alternating_eq_even'; simp)
      using cycle
      unfolding odd_cycle_def by simp
    moreover case False
    ultimately have "length (filter (\<lambda>e. e \<in> M) ?ep) < length (filter (\<lambda>e. e \<notin> M) ?ep)"
      by simp
    then show ?thesis
      apply(intro disjI2 alternating_list_gt)
      using cycle
      unfolding odd_cycle_def
      by auto    
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
    apply (cases p; simp add: distinct_edges_of_vpath split: if_splits)
    by (metis alt_list.cases inM length_greater_0_conv list.sel(1) odd_pos)
  moreover have "length (edges_of_path p) \<ge> 2"
    using cycle(1)
    unfolding odd_cycle_def
    using edges_of_path_length
    by (smt One_nat_def Suc_1 Suc_leI antisym_conv diff_Suc_Suc diff_zero eq_diff_iff le_trans less_le numeral_3_eq_3 odd_pos one_le_numeral)
  ultimately have "hd (edges_of_path p) \<noteq> last (edges_of_path p)"
    by (metis One_nat_def Suc_1 Suc_le_length_iff distinct.simps(2) last.simps last_in_set le_zero_eq length_0_conv list.sel(1) nat.simps(3))
  moreover have "last p \<in> (hd (edges_of_path p))" "last p \<in> (last (edges_of_path p))"
    using cycle
    unfolding odd_cycle_def
    subgoal by (metis One_nat_def Suc_1 hd_v_in_hd_e linear not_less_eq_eq numeral_3_eq_3)
    subgoal
      using alternating_list_odd_last cycle(1) cycle(2) inM odd_cycleD(2) by blast
    done
  moreover have "last p \<in> Vs M"
    using inM
    using Vs_def calculation(2) by fastforce
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
      then show ?thesis
        using ass cons1
        apply (simp add: neq_Nil_conv split: if_splits)
        apply clarify
        by (metis Suc_lessD alt_list_step edges_of_path.simps(3) insert_iff lessI list.sel(1) list.simps(15))
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
      apply(intro last_vert_in_last_edge that)
      using cycle[unfolded odd_cycle_def]
      by auto
    moreover have "last p = last (tl p)"
      using cycle(1)[unfolded odd_cycle_def]
      by (auto simp: Suc_le_length_iff numeral_3_eq_3)
    ultimately have "e = last (edges_of_path p) \<or> e = hd (edges_of_path p)" if "last p \<in> e" "e \<in> set (edges_of_path p)" for e
      using in_edges_of_path_hd_or_tl[OF that(2)] that
      by (metis edges_of_path.elims empty_iff empty_set last_ConsR list.sel(3))
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
        apply(intro alt_path_vert_is_matched v T1 odd_cycleD[OF cycle(1)])
        using odd_cycleD[OF cycle(1)] cycle(2) v
        by auto
      ultimately show ?thesis
        using match[unfolded matching_def2]
              e v F1
        by (metis edges_are_Vs insertI1)
    next
      case F2: False
      moreover have *: "last p \<notin> s"
        using quot odd_cycle_nempty[OF cycle(1)]
        by simp
      moreover have "v \<in> s"
        using quot F2 \<open>e \<in> E\<close>
        unfolding Vs_def
        using v(1) by blast
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
    apply simp
    by (metis empty_iff empty_set find_pfx.elims list.distinct(1))
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
    apply simp
    using find_pfx_nempty in_set_conv_decomp
    by metis
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
    apply(intro last_find_pfx_val)
    by auto
  moreover have "[y, x] = [y] @ [x]"
    by simp
  ultimately have "(last (find_pfx Q (rev l))) = y"
    using Nil
    apply simp
    by (smt \<open>[y, x] = [y] @ [x]\<close> find_pfx_append)
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
    apply(intro Cons)
    using Cons
    by (auto simp add: alt_list_step)
  ultimately show ?case
    using Cons
    apply (auto simp add: alt_list_step)
    by (metis find_pfx_nempty in_set_conv_decomp append_Cons append_Nil find_pfx_append)+
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
    apply (cases p'; simp)
    using Suc_le_eq by fastforce
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
  obtain ep where "edges_of_path p = find_pfx ((\<in>) v) (edges_of_path p) @ ep"
    using find_pfx_append_2 by auto
  then have "alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (find_pfx ((\<in>) v) (edges_of_path p))"
    by (metis alt_list_append_1 cycle(2))
  moreover have eofp_pfx: "(edges_of_path (find_pfx ((=) v) p)) = (find_pfx ((\<in>) v) (edges_of_path p))"
    apply(intro edges_of_path_find_pfx cycle)
    using odd_cycleD(1)[OF cycle(1)] by simp
  ultimately show ?g1
    by simp
  have rev_eofp_pfx: "(edges_of_path (find_pfx ((=) v) (rev p))) = (find_pfx ((\<in>) v) (edges_of_path (rev p)))"
    apply(intro edges_of_path_find_pfx cycle)
    subgoal using odd_cycleD(1,3)[OF cycle(1)] cycle(5) by simp
    subgoal using odd_cycleD(1,3)[OF cycle(1)] cycle(5)
      by (metis hd_rev rev.simps(1))
    done
  have rev_eop: "(edges_of_path (rev p)) = rev (edges_of_path p)"
    by (simp add: edges_of_path_rev)
  obtain p' p'' where p'p''[simp]: "p = p' @ (v # p'')"
    using cycle
    by (meson split_list_last)
  show ?g2
    unfolding eofp_pfx rev_eofp_pfx rev_eop
    apply(intro find_pfx_alt_list[where x = "{last p', v}" and y = "{v, hd p''}" and ?l1.0 = "(edges_of_path p')" and ?l2.0 = "(edges_of_path p'')"] cycle)
    subgoal by simp
    subgoal by simp
    subgoal apply(intro ballI impI where_is_v)
      using assms(3,5)
      by(cases p'; auto)+
    subgoal proof-
      have "v \<notin> set p'"
        using cycle
        apply simp
        by (metis disjoint_insert(1) distinct_append hd_append list.sel(1) list.sel(3) list.set_cases list.simps(15) tl_append2)
      moreover have "v \<notin> set p''"
        using cycle
        apply simp
        by (metis distinct.simps(2) distinct_append hd_append list.sel(1) tl_append2)
      ultimately show ?thesis
        by (auto simp add: v_in_edge_in_path_gen)
    qed
    subgoal unfolding p'p''
      using edges_of_path_append_2 edges_of_path_snoc
      by (smt append.assoc append_Cons cycle(1) cycle(5) edges_of_path.simps(3) last.simps last_appendR list.distinct(1) list.sel(1) odd_cycleD(3) p'p'' self_append_conv2)
    done
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
    apply simp
    by (meson Cons.prems path_2 path_suff)
qed

context quot
begin

subsubsection \<open>Choosing a neighbour from a given set\<close>

definition choose_con_vert where
  "choose_con_vert vs v = sel (vs \<inter> (neighbourhood E v))"

lemma choose_vert_works_1:
  assumes cycle: "distinct (tl C)" and
    quot_aug_path: "p' = (p1 @ u # p2)" "distinct p'" "path (quotG E) p'" "p2 \<noteq> []" and 
    quot: "s = (Vs E) - set C" (*and
    graph: "dblton_graph E"*)
shows "(choose_con_vert (set C) (hd p2)) \<in> set C \<and> {hd p2, (choose_con_vert (set C) (hd p2))} \<in> E"
  using assms
proof-
  have *: "\<exists>w. {hd p2, w} \<in> E \<and> w \<notin> s"
    apply(rule edge_in_quotG_2'_doubleton[where M = E])
    subgoal using quot_aug_path path_adj_verts_edge
      apply(simp add: neq_Nil_conv) 
      by fastforce
    subgoal using \<open>{u, hd p2} \<in> quot_graph P E - {{u}}\<close> edge_in_quot_in_graph_2'' by auto    
    subgoal using dblton_E by (auto elim: dblton_graphE)
    done
  then obtain w where "w \<in> neighbourhood E (hd p2)" "w \<notin> s"
    by (auto simp: neighbourhood_def insert_commute)
  moreover hence "w \<in> set C"
    using edges_are_Vs quot insert_absorb
    by auto 
  ultimately have "sel (set C \<inter> neighbourhood E (hd p2)) \<in> set C \<inter> neighbourhood E (hd p2)"
    apply -
    apply(rule sel)
    using edges_are_Vs quot insert_absorb
    by auto
  hence "choose_con_vert (set C) (hd p2) \<in> (set C \<inter> neighbourhood E (hd p2))"
    apply (subst choose_con_vert_def)
    by auto
  thus ?thesis
    by(fastforce simp: neighbourhood_def)
qed

lemma choose_vert_works_2:
  assumes cycle: "distinct (tl C)" and
    quot_aug_path: "p' = (p1 @ u # p2)" "distinct p'" "path (quotG E) p'" "p1 \<noteq> []" and 
    quot: "s = (Vs E) - set C" and
    graph: "\<forall>e\<in>E. \<exists>u v. e = {u, v} \<and> u \<noteq> v"
shows "(choose_con_vert (set C) (last p1)) \<in> set C \<and> {last p1, (choose_con_vert (set C) (last p1))} \<in> E"
  using assms
proof-
  have *: "\<exists>w. {last p1, w} \<in> E \<and> w \<notin> s"
    apply(rule edge_in_quotG_2'_doubleton[where M = E])
    subgoal using quot_aug_path path_adj_verts_edge
      apply(auto simp add: neq_Nil_conv_2)
      by (smt Diff_subset insert_commute path_adj_verts_edge subsetCE)
    subgoal using \<open>{u, last p1} \<in> quot_graph P E - {{u}}\<close> edge_in_quot_in_graph_2'' by auto    
    subgoal using graph by blast
    done
  then obtain w where "w \<in> neighbourhood E (last p1)" "w \<notin> s"
    by (auto simp: neighbourhood_def insert_commute)
  moreover hence "w \<in> set C"
    using edges_are_Vs quot insert_absorb
    by auto 
  ultimately have "sel (set C \<inter> neighbourhood E (last p1)) \<in> set C \<inter> neighbourhood E (last p1)"
    apply -
    apply(rule sel)
    using edges_are_Vs quot insert_absorb
    by auto
  hence "choose_con_vert (set C) (last p1) \<in> (set C \<inter> neighbourhood E (last p1))"
    apply (subst choose_con_vert_def)
    by auto
  thus ?thesis
    by(fastforce simp: neighbourhood_def)
qed

subsubsection \<open>Finding an Edge in the Concrete Graph\<close>

text\<open>A function to choose a vertex in the concrete graph connected to a vertex in the quotient graph,
     if the vertex in the quotient graph is connected to the contracted odd cycle.\<close>

definition stem2vert_path where
"stem2vert_path C M v =(
let find_pfx' = (\<lambda>C. find_pfx ((=) (choose_con_vert (set C) v)) C) in
  if (last (edges_of_path (find_pfx' C)) \<in> M) then
    (find_pfx' C)
  else
    (find_pfx' (rev C)))"

lemma find_pfx_subset:
  "set (find_pfx Q l) \<subseteq> set l"
  by (metis Un_iff find_pfx_append_2 set_append subsetI)

lemma stem2vert_path_subset:
  "set (stem2vert_path C M v) \<subseteq> (set C)"
  using find_pfx_subset
  apply(simp add: stem2vert_path_def Let_def)
  by fastforce

lemma hd_stem2vert_path:
  "C \<noteq> [] \<Longrightarrow> (hd (stem2vert_path C M a2') = hd C \<or> hd (stem2vert_path C M a2') = last C)"
  apply(simp add: stem2vert_path_def Let_def)
  by (smt find_pfx.elims hd_rev list.sel(1))

lemma hd_stem2vert_nempty:
  "C \<noteq> [] \<Longrightarrow> ((stem2vert_path C M a2') \<noteq> [])"
  apply(simp add: stem2vert_path_def Let_def)
  by (metis find_pfx.elims list.distinct(1) rev_is_Nil_conv)

subsubsection \<open>Lifting the Path\<close>

text\<open>A function to lift an augmenting path from a quotient to a concrete graph. It does so by
     replacing the contracted odd cycle with a subpath of the cycle that correctly matches the
     polarity of the edges connected to the odd cycle.\<close> 

definition replace_cycle where
  "replace_cycle C M p1 p2 =(
   let stem2p2 = stem2vert_path C M (hd p2);
       p12stem = stem2vert_path C M (last p1) in
   if p1 = [] then
     stem2p2 @ p2
   else
     (if p2 = [] then 
        p12stem @ (rev p1)
      else
       (if {u, hd p2} \<notin> quotG M then
         p1 @ stem2p2 @ p2
       else
         (rev p2) @ p12stem @ (rev p1))))"

lemma in_quot_graph_neq_u:
  assumes "v \<in> Vs(quot_graph P M)" "v \<noteq> u"
  shows "v \<in> s"
  using assms good_quot_map
  unfolding Vs_def quot_graph_def
  apply simp
  by force

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

end

lemma len_find_pfx:
  assumes "l \<noteq> []"
  shows "length (find_pfx Q l) \<ge> 1"
  using assms
proof(induction l)
  case Nil
  then show ?case
    by simp
next
  case (Cons a l)
  then show ?case
    by simp
qed

context quot
begin

lemma length_replace_cycle:
  assumes "C \<noteq> []" "p1 \<noteq> [] \<or> p2 \<noteq> []"
  shows "length (replace_cycle C M p1 p2) \<ge> length p1 + length p2 + 1"
proof(cases p1)
  case nil1: Nil
  show ?thesis
  proof(cases p2)
    case nil2: Nil
    then show ?thesis
      using nil1 assms
      by(simp add: replace_cycle_def split: if_splits)
  next
    case cons2: (Cons a1' p1')
    then show ?thesis
      using nil1 assms len_find_pfx
      by(auto simp add: replace_cycle_def stem2vert_path_def split: if_splits)
  qed
next
  case cons1: (Cons a1' p1')
  show ?thesis
  proof(cases p2)
    case nil2: Nil
    then show ?thesis
      using cons1 assms len_find_pfx
      by(auto simp add: replace_cycle_def stem2vert_path_def split: if_splits)
  next
    case cons2: (Cons a list)
    then show ?thesis
      using cons1 assms len_find_pfx
      by(auto simp add: replace_cycle_def stem2vert_path_def split: if_splits)
  qed
qed

lemma neq_u_notin_quot_graph:
  assumes "v \<notin> s" "v \<noteq> u"
  shows "v \<notin> Vs (quot_graph P E)"
  using assms
  by (metis in_quot_graph_neq_u)

lemma neq_u_notin_quotG:
  assumes "v \<notin> s" "v \<noteq> u"
  shows "v \<notin> Vs (quotG E)"
  using assms
  using in_quotG_neq_u by blast

end

lemma in_aug_path_in_Vs:
  assumes "matching_augmenting_path M p" "v \<in> set p" "v \<noteq> hd p" "v \<noteq> last p" "p \<noteq> []"
  shows "v \<in> Vs M"
  using alt_path_vert_is_matched'[OF matching_augmenting_path_feats(2)[OF assms(1)] assms(2-5)]
  .

context quot
begin

lemma alt_list_quotG_then_alt_list_1:
  assumes "set p \<subseteq> s" "alt_path (quotG M) p" \<open>M \<subseteq> E\<close>
  shows "alt_path M p"
  apply(intro alt_list_cong[OF assms(2)] ballI)
  using assms(1,3) edge_of_path_in_graph_iff_in_quot
  by blast+

lemma alt_list_quotG_then_alt_list_2:
  assumes "set p \<subseteq> s" "alt_list (\<lambda>e. e \<in> (quotG M)) (\<lambda>e. e \<notin> (quotG M)) (edges_of_path p)" "M \<subseteq> E"
  shows "alt_list (\<lambda>e. e : M) (\<lambda>e. e \<notin> M) (edges_of_path p)"
  apply(intro alt_list_cong[OF assms(2)] ballI)
  using assms(1,3) edge_of_path_in_graph_iff_in_quot
  by blast+

end

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

text\<open>showing that given an augmenting path, "replace cycle" produces an augmeting path.\<close>

context quot
begin

lemma inBetinM:
  assumes cycle: "odd_cycle C" "alt_path M C" "distinct (tl C)" and
    matching: "matching M" "M \<subseteq> E" and
    quot: "s = (Vs E) - set C"  and
    (*graph: "dblton_graph E" and*)
    p1_nempty[simp]: "p1 \<noteq> []" and 
    p1_subset_s[simp]: "set p1 \<subseteq> s" and
    inM: "{last p1, u} \<in> quotG M"
  shows "{last p1, hd (stem2vert_path C M (hd p2))} \<in> M"
proof-
  have "dblton_graph M"
    using graph subsetD[OF matching(2)]
    by (metis dblton_graph_def)

  show "{last p1, hd (stem2vert_path C  M (hd p2))} \<in> M"
  proof-
    have "last p1 \<in> s"
      using p1_subset_s p1_nempty by fastforce
    then have *: "\<exists>w. {last p1, w} \<in> M \<and> w \<notin> s"
      using edge_in_quotG_2'_doubleton

      apply(intro edge_in_quotG_2'_doubleton)
      using inM using \<open>M \<subseteq> E\<close> dblton_E by (fastforce simp: insert_commute dblton_graph_def)+
    then obtain vC where vC: "{last p1, vC} \<in> M "" vC \<notin> s"
      by auto
    moreover have vCinC: "vC \<in> set C"
      using quot(1) vC matching(2)
      unfolding Vs_def
      by auto
    have "vC = last C"
    proof(rule ccontr)
      assume ass: "vC \<noteq> last C"
      then have "vC \<noteq> hd C"
        using odd_cycleD(3)[OF cycle(1)] by auto
      have "C \<noteq> []"
        using vCinC
        by auto
      obtain e where e: "e \<in> set (edges_of_path C)" "vC \<in> e" "e \<in> M"
        using alt_path_vert_is_matched[OF cycle(2) vCinC \<open>vC \<noteq> hd C\<close> ass(1) \<open>C \<noteq> []\<close>]
        by metis
      moreover have "e \<noteq> {last p1, vC}"
        using p1_subset_s quot(1) e(1) v_in_edge_in_path \<open>last p1 \<in> s\<close>
        by fastforce
      ultimately show False
        using vC(1) matching(1) edges_are_Vs
        unfolding matching_def2
        by (metis insert_commute insert_iff)
    qed
    moreover have "hd (stem2vert_path C  M (hd p2)) = last C"
      using hd_stem2vert_path[OF odd_cycle_nempty[OF cycle(1)]] odd_cycleD[OF cycle(1)]
      by auto
    ultimately show ?thesis using vC
      by auto
  qed
qed

lemma rw3:"(edges_of_path (p1 @ u # p2)) = ((edges_of_path (p1 @ [u]))  @ (edges_of_path (u # p2)))" for p1 p2
  using edges_of_path_append_2 by fastforce

lemma rw4:
  fixes p1 p2::"'a list"
  assumes p1_nempty: "p1 \<noteq> []"
  assumes p2_nempty: "p2 \<noteq> []"
  shows "(edges_of_path (p1 @ u # p2)) = ((edges_of_path p1) @ {last p1, u} # {u, hd p2} # (edges_of_path p2))"
    proof-
      have "p1 = (butlast p1) @ [last p1]"
        using p1_nempty 
        by simp
      moreover have "p2 = hd p2 # (tl p2)"
        using p2_nempty 
        by simp
      ultimately show ?thesis
        by (metis append_Cons append_eq_append_conv2 append_self_conv edges_of_path.simps(3) edges_of_path_append_2 list.distinct(1) list.sel(1))
    qed

lemma rw5:
  fixes p1 p2::"'a list"
  assumes len_ge_2: "length p1 \<ge> 2"
  shows "edges_of_path (p1 @ u # p2) = ((edges_of_path (butlast p1)) @ {last (butlast p1), last p1} # {last p1, u} # (edges_of_path (u # p2)))"
proof-
  have p1_nempty: "p1 \<noteq> []"
    using assms
    by auto
  show ?thesis 
  proof-
    have butlast: "p = (butlast p) @ [last p]" if "p \<noteq> []" for p::"'a list"
      using that by simp
    have butlast_nempty: "butlast p1 \<noteq> []"
      using len_ge_2
      by (metis One_nat_def Suc_1 Suc_le_eq butlast length_append_singleton list.size(3) not_less_eq_eq not_less_iff_gr_or_eq)
    show ?thesis
      unfolding rw3[of p1 p2] edges_of_path_snoc[OF p1_nempty, symmetric]
      using edges_of_path_snoc[OF butlast_nempty, symmetric]
        butlast[OF p1_nempty] butlast[OF butlast_nempty]
      by (metis append.assoc append_Cons append_Nil)
  qed
qed

lemma empty_rev_imp: "C \<noteq> [] \<Longrightarrow> rev C \<noteq> []"
  by simp

lemma stem2vert_path_append_1:
  "last (edges_of_path (find_pfx ((=) (choose_con_vert (set C) a2')) C)) \<in> M 
   \<Longrightarrow> \<exists>Ctail. C = (stem2vert_path C M a2') @ Ctail"
  unfolding stem2vert_path_def
  by (auto split: if_splits intro: find_pfx_append_2)

lemma stem2vert_path_append_2:
  assumes "(choose_con_vert (set C) a2') = last C" and "odd_cycle C"
  shows "\<exists>Ctail. C = (stem2vert_path C M a2') @ Ctail"
proof(cases "last (edges_of_path (find_pfx ((=) (choose_con_vert (set C) a2')) C)) \<in> M")
  case True
  then show ?thesis
    by(intro stem2vert_path_append_1)
next
  have "choose_con_vert (set C) a2' = hd C \<Longrightarrow> 
                    (find_pfx ((=) (choose_con_vert (set C) a2')) C) = [hd C]"
    using odd_cycle_nempty[OF \<open>odd_cycle C\<close>]
    by (auto simp: neq_Nil_conv)
  moreover have "find_pfx ((=) (last C)) (rev C) = [last C]" if "C \<noteq> []"
    using empty_rev_imp[OF that, unfolded neq_Nil_conv]
    by auto
  moreover case False
  ultimately show ?thesis
    using assms(1)
    apply (cases "C = []")
    by (auto split: if_splits simp: neq_Nil_conv stem2vert_path_def
        odd_cycleD(3)[OF \<open>odd_cycle C\<close>, symmetric])
qed

lemma find_pfx_sing: "find_pfx Q l = [x] \<Longrightarrow> x = hd l"
  by(cases "l"; auto split: if_splits)

lemma alt_list_replace_cycle:
  assumes cycle: "odd_cycle C" "alt_path M C" "distinct (tl C)" and
    quot_aug_path: "p' = (p1 @ u # p2)" "graph_augmenting_path (quotG E) (quotG M) p'" and 
    matching: "matching M" "M \<subseteq> E" and
    quot: "s = (Vs E) - set C" "set C \<subseteq> Vs E"(* and
    graph: "dblton_graph E"*)
  shows "alt_path M (replace_cycle C M p1 p2)"
proof-

  {
    fix C fix p1 p2::"'a list"
    assume "p2 \<noteq> []"
    define a2' where "a2' = hd p2"
    define p2' where "p2' = tl p2"
    have Cons: "p2 = a2' # p2'"
      unfolding a2'_def p2'_def
      using \<open>p2 \<noteq> []\<close> by auto
    assume quot_aug_path: "alt_path (quotG M) (u # p2)" "distinct (u # p2)" "path (quotG E) (u # p2)"
    assume p2_subset_s: "set p2 \<subseteq> s"
    assume cycle: "odd_cycle C" "alt_path M C" "distinct (tl C)"
    have "C \<noteq> []"
      using odd_cycle_nempty(1)[OF cycle(1)] .
    then have "hd C = hd (rev C)"
      using odd_cycleD(3)[OF cycle(1)] 
      by (simp add: hd_rev)
    assume quot: "s = (Vs E) - set C"
    have hd_stem2vert_path_nin_append: "hd (stem2vert_path C M a2' @ a2' # p2') = hd (stem2vert_path C M a2' @ [a2'])"
      by (simp add: hd_append)
    define chv where "chv = (choose_con_vert (set C) a2')"
    have choose_vert_works: "chv \<in> set C" "{a2', chv} \<in> E"
      unfolding chv_def
      using choose_vert_works_1[OF cycle(3) _ _ _  _ quot] Cons quot_aug_path(1,2,3)
      by (metis (no_types, lifting) \<open>p2 \<noteq> []\<close> a2'_def append_self_conv2)+
    have "last (stem2vert_path C M a2') = chv"
      using choose_vert_works(1)
      unfolding stem2vert_path_def
      apply (simp; intro impI conjI)
      subgoal using chv_def find_pfx_works_1 by fastforce
      subgoal using chv_def find_pfx_works_2 by fastforce
      done
    then obtain chp where chp: "(stem2vert_path C M a2') = chp @ [chv]"
      unfolding stem2vert_path_def
      by (smt append_butlast_last_id cycle(1) len_find_pfx list.size(3) not_one_le_zero odd_cycle_nempty rev_is_Nil_conv)
    {
      fix chp
      assume ass: "(last (edges_of_path (chp @ [chv])) \<in> M \<and> chp \<noteq> []) \<or> chv = last C" "set (chp @ [chv]) \<subseteq> set C"
      have chva2': "{chv, a2'} \<notin> M"
      proof(cases "chv = last C")
        case T2: True
        then show ?thesis
          using quot_aug_path Cons edge_in_quot_in_graph_2'_doubleton
          apply (simp add: alt_list_step)
          by (smt Diff_disjoint choose_vert_works contra_subsetD good_quot_map(1) 
                  image_empty image_insert insert_Diff insert_disjoint(2) list.set_intros(1)
                  mem_Collect_eq p2_subset_s quot quot_graph_def)
      next
        case F2: False
        then have True: "last (edges_of_path (chp @ [chv])) \<in> M"
          using ass(1) by auto
        have "a2' \<notin> last (edges_of_path (chp @ [chv]))"
        proof(rule ccontr; simp)
          assume "a2' \<in> last (edges_of_path (chp @ [chv]))"
          then have "a2' \<in> set (chp @ [chv])"
            using ass F2
            by (metis Nil_is_append_conv edges_of_path_snoc last_in_set list.distinct(1) v_in_edge_in_path_gen)
          then show False
            by (metis Diff_iff ass(2) contra_subsetD list.set_intros(1) local.Cons p2_subset_s quot)
        qed
        then have "last (edges_of_path (chp @ [chv])) \<noteq> {chv, a2'}"
          by auto
        moreover have "last (chp @ [chv]) = chv "
          unfolding stem2vert_path_def
          using choose_vert_works chv_def find_pfx_works_1 find_pfx_works_2 by fastforce
        moreover have "last (chp @ [chv]) \<in> last (edges_of_path (chp @ [chv]))"
          apply(rule last_v_in_last_e)
          using F2 ass(1) not_less_eq_eq
          by auto
        ultimately show ?thesis
          using matching(1)
          unfolding matching_def2
          apply auto
          subgoal by (metis True \<open>last (edges_of_path (chp @ [chv])) \<noteq> {chv, a2'}\<close> edges_are_Vs insertI1)
          subgoal by (metis True \<open>last (edges_of_path (chp @ [chv])) \<noteq> {chv, a2'}\<close> edges_are_Vs insertI1)
          done
      qed
      then have alt_list_p2: "alt_path M (chv # a2' # p2')"
        apply (simp add: alt_list_step)
        apply(rule alt_list_quotG_then_alt_list_2)
        subgoal using Cons quot_aug_path(1) p2_subset_s
          by blast
        subgoal proof-
          have "alt_path (quotG M) (u # a2' # p2') \<or>
                       alt_list (\<lambda>e. e \<in> quotG M) (\<lambda>e. e \<notin> quotG M) (edges_of_path (u # a2' # p2'))"
            apply(rule conjunct2[OF alt_list_append_1[where ?l1.0 = "[]"]])
            using  Cons quot_aug_path(1) quot_aug_path(2)
            by simp
          moreover have "{u, a2'} \<notin> quotG M"
            using quot_aug_path(1,2) Cons
            by (simp add: alt_list_step)
          ultimately have "alt_path (quotG M) (u # a2' # p2')"
            by(auto simp add: alt_list_step)
          then show ?thesis
            by(auto simp add: alt_list_step)
        qed
        subgoal using \<open>M \<subseteq> E\<close> .
        done
    }note alt_list_p2 = this
    have e_of_p_chp: "(edges_of_path (chp @ [chv, a2'])) = edges_of_path(chp @ [chv]) @ edges_of_path ([chv, a2'])"
      using edges_of_path_append_2
      by (metis list.distinct(1) list.sel(1))
    assume True: "last (edges_of_path (find_pfx ((=) (choose_con_vert (set C) a2')) C)) \<in> M \<or>
                  (choose_con_vert (set C) a2') = last C"
    then obtain Ctail where Ctail: "C = (stem2vert_path C M a2') @ Ctail"
      using stem2vert_path_append_1 stem2vert_path_append_2[OF _ cycle(1)]
      by metis
    then have "edges_of_path C = edges_of_path(chp @ [chv]) @ edges_of_path (chv # Ctail)"
      using edges_of_path_append_2 chp
      by fastforce
    then have alt_list_chp_chv: "alt_path M (chp @ [chv])"
      using cycle(2) alt_list_append_1
      by force
    moreover have "alt_path M (chp @ ([chv] @ [a2'] @ p2'))"
    proof-
      have "find_pfx ((=) (choose_con_vert (set C) a2')) C = [chv] \<Longrightarrow> chv = hd C"
        by (rule find_pfx_sing)
      then have "chp = [] \<Longrightarrow> last (edges_of_path (chp @ [chv])) \<in> M \<and> chp \<noteq> [] \<or> chv = hd C"
        using chp
        by (auto simp: \<open>hd C = hd (rev C)\<close> stem2vert_path_def split: if_splits intro: find_pfx_sing)
      moreover have "chp \<noteq> [] \<Longrightarrow> last (edges_of_path (chp @ [chv])) \<in> M \<and> chp \<noteq> [] \<or> chv = hd C"
        using True chp
        by (auto simp: \<open>hd C = hd (rev C)\<close> stem2vert_path_def \<open>C \<noteq> []\<close> chv_def hd_rev)
      ultimately have "last (edges_of_path (chp @ [chv])) \<in> M \<and> chp \<noteq> [] \<or> chv = hd C"
        by auto
      moreover have "set (chp @ [chv]) \<subseteq> set C"
        by (metis chp stem2vert_path_subset) 
      ultimately have "alt_path M (chv # a2' # p2')"
        using alt_list_p2[where ?chpa7 = chp] odd_cycleD(3)[OF cycle(1)]
        by simp
      moreover have "alt_path M (chp @ [chv])"
        using alt_list_chp_chv .
      moreover have "edges_of_path (chp @ [chv]) \<noteq> [] \<longrightarrow> last (edges_of_path (chp @ [chv])) \<in> M"
        by (metis (mono_tags, lifting) \<open>C \<noteq> []\<close> \<open>hd C = hd (rev C)\<close> \<open>last (edges_of_path (chp @ [chv])) \<in> M \<and> chp \<noteq> [] \<or> chv = hd C\<close> chp chv_def edges_of_path.simps(2) find_pfx.simps(2) list.exhaust_sel rev_is_Nil_conv set_rev stem2vert_path_def)
      moreover have "\<forall>x\<in>set (edges_of_path (chp @ [chv])). (x \<notin> M) = (x \<notin> M)"
        by auto
      ultimately have "alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path ((chp @ [chv])) @ edges_of_path (chv # a2' # p2'))"
        apply(intro alt_list_append_3)
        using alternating_list_odd_last
        by auto
      moreover have "(edges_of_path (chp @ [chv]) @ edges_of_path (chv # a2' # p2')) =
                           (edges_of_path ((chp @ [chv] @ [a2']) @ p2'))"
        by (metis append_Cons append_Nil append_assoc edges_of_path_append_2 list.sel(1) list.simps(3))
      ultimately show ?thesis
        by simp
    qed
    ultimately have "alt_path M (stem2vert_path C M (hd p2) @ p2)"
      using Cons chp
      by (auto simp add: replace_cycle_def)
  } note d1 = this

  have "path (quotG E) (u # p2)"
    using path_suff quot_aug_path
    by blast
  then have "set p2 \<subseteq> Vs (quotG E)"
    using quot
    using  tl_path_is_path
    by (metis list.sel(3) subset_path_Vs)

  moreover have u_nin_p2: "u \<notin> set p2"
    using quot_aug_path
    by auto
  ultimately have p2_subset_s: "set p2 \<subseteq> s"
    using quot good_quot_map
    by (smt (verit) Vs_quotG_subset_Vs_quot_graph in_mono in_quot_graph_neq_u subsetI)

  have "path (quotG E) (p1 @ [u])"
    using quot_aug_path
    by (auto simp: path_pref)
  then have "set p1 \<subseteq> Vs (quotG E)"
    using quot
    by (metis path_pref subset_path_Vs)
  moreover have u_nin_p1: "u \<notin> set (rev p1)"
    using quot_aug_path
    by auto
  ultimately have p1_subset_s: "set (rev p1) \<subseteq> s"
    using quot good_quot_map
    by (metis (no_types, lifting) in_quotG_neq_u set_rev subset_eq)


  note inBetinM = 
         inBetinM[OF cycle matching quot(1)]


  {
    fix p1 p2 ::"'a list"
    assume up2_nin_M: "{u, hd p2} \<notin> quotG M"
    assume p1_subset_s: "set p1 \<subseteq> s"
    assume quot_aug_path: "matching_augmenting_path (quotG M) (p1 @ u # p2)"
    assume len_ge_2: "length p1 \<ge> 2"
    assume p2_nempty: "p2 \<noteq> []"
    have alt_list_app: "alt_path M (p1 @ stem2vert_path C M (hd p2) @ p2)"
      if  "alt_path M (stem2vert_path C M (hd p2) @ p2)"
    proof-
      have p1_nempty: "p1 \<noteq> []" using len_ge_2 by auto
      show ?thesis
      proof-
        have inM: "{last p1, u} \<in> quotG M"
          using alt_list_append_1'''[OF matching_augmenting_path_feats(2)[OF quot_aug_path, unfolded rw4[OF p1_nempty p2_nempty]] _ up2_nin_M]
          by auto
        define chp where "chp = (stem2vert_path C M (hd p2))"
        have i: "{last p1, hd chp} \<in> M"
          using inBetinM[OF p1_nempty _ inM] p1_subset_s
          unfolding chp_def
          by auto
        have rw: "(edges_of_path (p1 @ chp @ p2)) = (edges_of_path (p1 @ [hd chp]) @ (edges_of_path (chp @ p2)))"
        proof-
          have "C \<noteq> []"
            using odd_cycle_nempty[OF cycle(1)].
          then have "chp \<noteq> []"
            unfolding chp_def
            by (simp add: hd_stem2vert_nempty)
          then have "chp = ((hd chp) # (tl chp))"
            by auto
          then show ?thesis
            by (metis Nil_is_append_conv \<open>chp \<noteq> []\<close> edges_of_path_append_2 hd_append2)
        qed
        have "alt_path M (p1 @ chp @ p2)"
          unfolding rw
          apply(intro alt_list_append_3)
          subgoal proof-
            have rw:"(edges_of_path (p1 @ [hd chp])) = (edges_of_path (p1)  @ [{last p1, hd chp}])"
              unfolding chp_def
              by (simp add: edges_of_path_snoc p1_nempty)
            have rw2:"(edges_of_path (p1 @ l)) = (edges_of_path p1  @ (edges_of_path (last p1 # l)))" for l
              by (smt append_Cons append_assoc append_butlast_last_id append_self_conv2 edges_of_path_append_2 list.sel(1) list.simps(3) p1_nempty)
            show ?thesis
              unfolding rw
              apply(rule alt_list_append_2)
              subgoal using alt_list_quotG_then_alt_list_1[OF _ conjunct1[OF alt_list_append_1[OF matching_augmenting_path_feats(2)[OF quot_aug_path, unfolded rw2]]]]
                using p1_subset_s matching(2) by linarith
              subgoal using i by(simp add: alt_list_step alt_list_empty)
              subgoal proof-
                have rw6: "last (edges_of_path p1) = {last(butlast p1), last p1}"
                  using len_ge_2
                  by (metis Suc_1 diff_is_0_eq edges_of_path_snoc length_butlast list.size(3) not_less_eq_eq p1_nempty snoc_eq_iff_butlast)
                then show ?thesis
                  using alt_list_append_1''''[OF matching_augmenting_path_feats(2)[OF quot_aug_path, unfolded rw5[OF len_ge_2]] _ inM]
                  using p1_subset_s inM 
                  apply auto
                  by (metis (no_types, lifting) \<open>\<forall>x\<in>{{last (butlast p1), last p1}, {last p1, u}}. (x \<notin> quot_graph P M - {{u}}) = (x \<notin> quot_graph P M - {{u}}) \<Longrightarrow> {last (butlast p1), last p1} \<notin> quot_graph P M - {{u}}\<close> \<open>alt_path M p1\<close> alternating_list_even_last edge_of_path_in_graph_iff_in_quot edges_of_path_nempty last_in_set len_ge_2 matching(2))
              qed
              done
          qed
          subgoal using that
            unfolding chp_def
            by auto
          subgoal using i
            by (metis \<open>alt_path M (p1 @ [hd chp])\<close> alternating_list_odd_last edges_of_path_snoc last_snoc p1_nempty)
          done
        then show ?thesis
          unfolding chp_def
          by auto
      qed
    qed
  } note append_works = this

  {
    fix p1 p2::"'a list"
    assume p2_subset_s: "set p2 \<subseteq> s"
    assume p2_nempty[simp]: "p2 \<noteq> []" "({u, hd p2} \<notin> quotG M) \<or> p1 = []"
    assume quot_aug_path: "alt_path (quotG M) (u # p2)" (is ?p1) "distinct (u # p2)" (is ?p2) "path (quotG E) (u # p2)" (is ?p3)
    assume alt_list_app: "alt_path M (p1 @ stem2vert_path C M (hd p2) @ p2)"
      if  "alt_path M (stem2vert_path C M (hd p2) @ p2)"
    have "alt_path M (replace_cycle C M p1 p2)"
    proof(cases "last (edges_of_path (find_pfx ((=) (choose_con_vert (set C) (hd p2))) C)) \<in> M")
      case T3: True
      then have i: "alt_path M (stem2vert_path C M (hd p2) @ p2)"
        using d1[OF p2_nempty(1) quot_aug_path p2_subset_s cycle quot(1)]
        by simp
      with alt_list_app[OF i] p2_nempty show ?thesis
        unfolding replace_cycle_def Let_def
        by(simp split: if_splits; intro impI conjI)+
    next
      define chv where "chv = (choose_con_vert (set C) (hd p2))"
      case F1: False
      show ?thesis
      proof(cases "chv = last C")
        case T2: True
        then have i: "alt_path M (stem2vert_path C M (hd p2) @ p2)"
          using d1[OF p2_nempty(1) quot_aug_path p2_subset_s cycle quot(1)]
          using chv_def
          by simp
        with alt_list_app[OF i] p2_nempty show ?thesis
          unfolding replace_cycle_def Let_def
          by(simp split: if_splits; intro impI conjI)+
      next
        case F2: False
        have choose_vert_works: "chv \<in> set C"
          unfolding chv_def
          using choose_vert_works_1[OF cycle(3) _ _ _ _ quot(1)] quot_aug_path  p2_nempty
          by blast
        moreover have "chv \<noteq> hd C"
          using odd_cycleD(3)[OF cycle(1)] F2
          by auto
        ultimately have i: "last (edges_of_path (find_pfx ((=) chv) (rev C))) \<in> M"
          using F1 find_pfx_edges_of_path_alt_list(2)[OF cycle]
          using chv_def by blast
        have ii: "distinct (tl (rev C))"
          using cycle(3) odd_cycleD(3)[OF cycle(1)] tl_distinct_rev
          by auto
        have iii: "s = Vs E - set (rev C)"
          using quot by auto
        have i: "alt_path M (stem2vert_path C M (hd p2) @ p2)"
          using F1 using d1[OF p2_nempty(1) quot_aug_path p2_subset_s odd_cycle_rev[OF cycle(1)] odd_cycle_rev_alt_list[OF cycle(1,2)] ii iii] i
          by (auto simp add: chv_def  stem2vert_path_def hd_rev)
        then show ?thesis
          unfolding replace_cycle_def Let_def
          apply(simp split: if_splits; intro impI conjI)
          subgoal
            unfolding replace_cycle_def stem2vert_path_def
            apply (simp add: p2_nempty chv_def)
            apply(intro conjI)
            subgoal using F1
              by (simp add: hd_rev)
            subgoal proof-
              show ?thesis
                using alt_list_app[OF i]
                unfolding replace_cycle_def
                by (metis set_rev stem2vert_path_def)
            qed
            done
          subgoal using p2_nempty by simp
          done
      qed
    qed
  } note replace_cycle_cases = this

  {
    fix p1 p2::"'a list"
    assume p1_subset_s: "set (rev p1) \<subseteq> s"
    assume up2_in_M: "{u, hd p2} \<in> quotG M \<or> p2 = []"
    assume p1_nempty[simp]: "p1 \<noteq> []"
    have rev_p1_nempty: "rev p1 \<noteq> []" using p1_nempty by auto
    assume quot_aug_path: "alt_path (quotG M) (u # rev p1)" (is ?p1) "distinct (u # rev p1)" (is ?p2) "path (quotG E) (u # rev p1)" (is ?p3)
    assume alt_list_rev: "alt_path M (rev p2 @ stem2vert_path C M (last p1) @ rev p1)"
      if  "alt_path M (stem2vert_path C M (hd (rev p1)) @ rev p1)"
    have "alt_path M (replace_cycle C M p1 p2)"
    proof(cases "last (edges_of_path (find_pfx ((=) (choose_con_vert (set C) (hd (rev p1)))) C)) \<in> M")
      case True
      then have i: "alt_path M (stem2vert_path C M (hd (rev p1)) @ rev p1)"
        using d1[OF rev_p1_nempty quot_aug_path p1_subset_s cycle quot(1)]
        by (simp add: rev_p1_nempty)
      with alt_list_rev i[unfolded hd_rev] up2_in_M show ?thesis
        unfolding replace_cycle_def Let_def
        by(simp add: hd_rev split: if_splits; intro impI conjI)+
    next
      define chv where "chv = (choose_con_vert (set C) (last p1))"
      case F1: False
      show ?thesis
      proof(cases "chv = last C")
        case True
        then have i: "alt_path M (stem2vert_path C M (hd (rev p1)) @ rev p1)"
          using d1[OF rev_p1_nempty quot_aug_path p1_subset_s cycle quot(1)]
          using chv_def
          by (simp add: p1_nempty replace_cycle_def hd_rev)
        with up2_in_M alt_list_rev i[unfolded hd_rev]  show ?thesis
          unfolding replace_cycle_def Let_def
          by(simp add: hd_rev split: if_splits; intro impI conjI)+
      next
        case False
        have choose_vert_works: "chv \<in> set C"
          unfolding chv_def
          using choose_vert_works_1[OF cycle(3) _ _ _ _ quot(1)] quot_aug_path p1_nempty rev_p1_nempty
          by (metis (no_types, lifting) append_self_conv2 hd_rev)
        moreover have "chv \<noteq> hd C"
          using odd_cycleD(3)[OF cycle(1)] False
          by auto
        ultimately have i: "last (edges_of_path (find_pfx ((=) chv) (rev C))) \<in> M"
          using F1 find_pfx_edges_of_path_alt_list(2)[OF cycle]
          using chv_def hd_rev p1_nempty
          by metis
        have ii: "distinct (tl (rev C))"
          using cycle(3) odd_cycleD(3)[OF cycle(1)] tl_distinct_rev
          by auto
        have iii: "s = Vs E - set (rev C)"
          using quot by auto
        have i: "alt_path M (stem2vert_path C M (hd (rev p1)) @ rev p1)"
          using F1 using d1[OF rev_p1_nempty quot_aug_path p1_subset_s odd_cycle_rev[OF cycle(1)] odd_cycle_rev_alt_list[OF cycle(1,2)] ii iii] i
          by (auto simp add: chv_def p1_nempty stem2vert_path_def hd_rev)
        moreover have " alt_path M (rev p2 @ stem2vert_path C M (last p1) @ rev p1)"
          unfolding replace_cycle_def stem2vert_path_def
          apply (simp add: p1_nempty chv_def)
          apply(intro conjI)
          subgoal using F1  p1_nempty
            by (simp add: hd_rev)
          subgoal proof-
            show ?thesis
              using alt_list_rev[OF i]
              unfolding replace_cycle_def
              using p1_nempty
              by (metis set_rev stem2vert_path_def)
          qed
          done
        ultimately show ?thesis
          unfolding replace_cycle_def Let_def
          using up2_in_M
          by(simp add: hd_rev split: if_splits; intro impI conjI)+
      qed
    qed
  } note replace_cycle_cases_p1 = this
    (*To be able to give up replace_cycle_cases_p1 and use replace_cycle_cases instead of it, we need
    to show that rev (replace_cycle) = replace_cycle.*)

  have "matching_augmenting_path (quotG M) p'" "path (quotG E) p'"
    using quot_aug_path(2) by simp+

  note p'_feats = matching_augmenting_path_feats[OF \<open>matching_augmenting_path (quotG M) p'\<close>]

  show ?thesis
  proof(cases "p1 = []")
    case nil1: True
    show ?thesis
    proof(cases "p2 = []")
      case nil2: True
      then show ?thesis
        using p'_feats quot_aug_path(1)
        by (simp add: nil1 )
    next
      case p2_nempty: False
      show ?thesis
        using replace_cycle_cases[OF p2_subset_s p2_nempty _ ] nil1 p'_feats quot_aug_path
        by (auto simp add: p2_nempty nil1)
    qed
  next
    case p1_nempty: False
    show ?thesis
    proof(cases "alt_path (quotG M) (u # p2)")
      case T1: True
      show ?thesis
      proof(cases "p2 = []")
        case T2: True
        have quot_aug_path_p1: "alt_path (quotG M) (u # rev p1)" (is ?p1) "distinct (u # rev p1)" (is ?p2) "path (quotG E) (u # rev p1)" (is ?p3)
        proof-
          have "alt_path (quotG M) (p1 @ [u])"
            using p'_feats quot_aug_path(1) T2
            by simp
          have rw: "edges_of_path p' = (edges_of_path (p1 @ [u])) @ edges_of_path (u # p2)"
            using edges_of_path_append_2 quot_aug_path(1) by fastforce
          have eop_nempty: "edges_of_path (p1 @ [u]) \<noteq> []"
            by (metis Nil_is_append_conv edges_of_path_snoc list.distinct(1) p1_nempty)
          have "alt_path (quotG M) (rev (p1 @ [u]))"
            unfolding edges_of_path_rev[symmetric]
            apply(intro alt_list_rev)
            subgoal 
              using T2 matching_augmenting_path_last_edge_nin quot_aug_path(1) quot_aug_path(2)
              using \<open>alt_path (quotG M) (p1 @ [u])\<close> by blast
            subgoal
              using T2 matching_augmenting_path_odd_length quot_aug_path(1) quot_aug_path(2) by blast
            done
          then show ?p1
            by simp
          show ?p2
            using quot_aug_path
            by simp
          show ?p3
            using quot_aug_path
            using T2 rev_path_is_path by force
        qed
        have rev_p1_nempty: "rev p1 \<noteq> []" using p1_nempty by simp
        show ?thesis
          using replace_cycle_cases_p1[OF p1_subset_s _ p1_nempty quot_aug_path_p1] T2
          by (simp add: hd_rev)
      next
        case p2_nempty: False
        then have up2_nin_M: "{u, hd p2} \<notin> quotG M"
          using T1
          by(cases p2; auto simp add: alt_list_step)
        show ?thesis
        proof(cases "length p1 \<ge> 2")
          case len_ge_2: True
          have alt_list_app: "alt_path M (p1 @ stem2vert_path C M (hd p2) @ p2)"
            if  "alt_path M (stem2vert_path C M (hd p2) @ p2)"
            using append_works[OF up2_nin_M _ graph_augmenting_path_feats(1)[OF quot_aug_path(2), unfolded quot_aug_path(1)] len_ge_2 p2_nempty] p1_subset_s
            by (simp add: that)
          have quot_aug_path_p2: "alt_path (quotG M) (u # p2)" (is ?p1) "distinct (u # p2)" (is ?p2) "path (quotG E) (u # p2)" (is ?p3)
          proof-
            show ?p1
              using T1 by blast
            show ?p2
              using quot_aug_path
              by simp
            show ?p3
              using quot_aug_path rev_path_is_path  \<open>path (quotG E) (u # p2)\<close>
              by fastforce
          qed
          show ?thesis
            using replace_cycle_cases[OF p2_subset_s p2_nempty _ quot_aug_path_p2 alt_list_app] up2_nin_M
            by blast
        next
          case False                                                                                                    
          then have "length p1 = 1"
            by (metis One_nat_def Suc_1 Suc_leI eq_iff length_greater_0_conv not_less_eq_eq p1_nempty)
          then obtain a where "p1 = [a]"
            by (metis One_nat_def add.commute add.right_neutral length_0_conv length_tl list.collapse list.sel(3) list.size(4))
          then have False
            using quot_aug_path(1) p'_feats up2_nin_M p2_nempty
            by(auto simp add: alt_list_step neq_Nil_conv)
          then show ?thesis by simp
        qed        
      qed
    next
      case p2_nalt: False
      have last_p1_nin: "alt_path (quotG M) (p1 @ [u])" (is ?p1)
        "last (edges_of_path (p1 @ [u])) \<notin> quotG M" (is ?p2)
      proof-
        have rw: "edges_of_path p' = (edges_of_path (p1 @ [u])) @ edges_of_path (u # p2)"
          using edges_of_path_append_2 quot_aug_path(1) by fastforce
        have eop_nempty: "edges_of_path (p1 @ [u]) \<noteq> []"
          by (metis Nil_is_append_conv edges_of_path_snoc list.distinct(1) p1_nempty)
        show ?p1 ?p2
          using alt_list_append_1'[OF p'_feats(2)[unfolded rw] eop_nempty] p2_nalt
          by blast+
      qed
      have up2_nin_M: "{last p1 , u} \<notin> quotG M"
      proof-
        have "last (edges_of_path (p1 @ [u])) = {last p1, u}"
          using p1_nempty
          by (metis edges_of_path_snoc last_snoc)
        then show ?thesis 
          using last_p1_nin by auto
      qed
      have rev_p1_nempty: "rev p1 \<noteq> []" using p1_nempty by auto
      have up2_in_M: "{u, hd p2} \<in> quotG M" if "p2 \<noteq> []"
        using p'_feats
        unfolding rw4[OF p1_nempty that] quot_aug_path(1)
        using alt_list_append_1'' p2_nalt up2_nin_M
        by (metis (no_types, lifting))
      show ?thesis
      proof(cases "length p2 \<ge> 2")
        case len_p2_ge_2: True
        have app_works: "alt_path M (rev p2 @ stem2vert_path C M (last p1) @ rev p1)"
          if  "alt_path M (stem2vert_path C M (last p1) @ rev p1)"
          unfolding hd_rev[symmetric]
          apply(rule append_works)
          subgoal using up2_nin_M by (simp add: hd_rev p1_nempty insert_commute)
          subgoal using p2_subset_s by auto
          subgoal proof-
            have "rev p2 @ u # rev p1 = rev p'"
              by (simp add: quot_aug_path(1))
            then show ?thesis
              using quot_aug_path(1,2) matching_augmenting_path_rev by force
          qed
          subgoal using len_p2_ge_2 by auto
          subgoal using p1_nempty by auto
          subgoal using that[unfolded hd_rev[symmetric]] .
          done
        have quot_aug_path_p1: "alt_path (quotG M) (u # rev p1)" (is ?p1) "distinct (u # rev p1)" (is ?p2) "path (quotG E) (u # rev p1)" (is ?p3)
        proof-
          have "alt_path (quotG M) (rev (p1 @ [u]))"
            unfolding edges_of_path_rev[symmetric]
            apply(intro alt_list_rev)
            using last_p1_nin(1) apply blast
            subgoal
              using alternating_list_even_last edges_of_path_snoc last_p1_nin(1,2) p1_nempty
                    snoc_eq_iff_butlast
              by fastforce
            done
          then show ?p1
            by simp
          show ?p2
            using quot_aug_path
            by simp
          show ?p3
            using quot_aug_path rev_path_is_path  \<open>path (quotG E) (p1 @ [u])\<close>
            by fastforce
        qed
        show "alt_path M (replace_cycle C M p1 p2)"
          using replace_cycle_cases_p1[OF p1_subset_s _ p1_nempty quot_aug_path_p1 app_works] up2_in_M
          using hd_rev p1_nempty
          by (metis (no_types, lifting)) 
      next
        case len_p2_nge_2: False
        show ?thesis
        proof(cases "p2 = []")
          case True
          then have False
            using p2_nalt alt_list.intros(1) by auto
          then show ?thesis by simp
        next
          case p2_nempty: False
          then have "length p2 = 1"
            using len_p2_nge_2
            by (metis One_nat_def Suc_1 Suc_leI eq_iff length_greater_0_conv not_less_eq_eq p2_nempty)
          then obtain a where "p2 = [a]"
            by (metis One_nat_def add.commute add.right_neutral length_0_conv length_tl list.collapse list.sel(3) list.size(4))
          then have False
            using quot_aug_path(1) p'_feats up2_nin_M p2_nempty
            by (metis (no_types, lifting) insert_iff last.simps last_appendR list.distinct(1)
                                          list.sel(1) up2_in_M vs_member)
          then show ?thesis by simp
        qed
      qed
    qed
  qed
qed
end

lemma path_find_pref:
  assumes "path E C"
  shows "path E (find_pfx Q C)"
  using assms
  by (metis find_pfx_append_2 path_pref)

context quot
begin

lemma path_stem2vert_path:
  assumes "path E C"
  shows "path E (stem2vert_path C M v)"
  unfolding stem2vert_path_def
  using rev_path_is_path assms path_find_pref
  by (simp; blast)+


lemma path_replace_cycle:
  assumes cycle: "odd_cycle C" "alt_path M C" "distinct (tl C)" "path E C" and
    quot_aug_path: "p' = (p1 @ u # p2)" "graph_augmenting_path (quotG E) (quotG M) p'" and 
    matching: "matching M" "M \<subseteq> E" and
    quot: "s = (Vs E) - set C"(*and
    graph: "dblton_graph E"*)
  shows "path E (replace_cycle C M p1 p2)"
proof-


  {
    fix C fix p1 p2::"'a list"
    define a2' where "a2' = hd p2"
    assume quot_aug_path: "distinct (u # p2)" "path (quotG E) (u # p2)"
    assume p2_subset_s: "set p2 \<subseteq> s"
    assume cycle: "distinct (tl C)" "path E C"
    assume quot: "s = (Vs E) - set C"
    define p2' where "p2' = tl p2"
    have "path E (stem2vert_path C M (hd p2) @ p2)"
    proof(cases "p2 = []")
      case True
      then show ?thesis
        using path_stem2vert_path[OF cycle(2)]
        by simp
    next
      case False
      have Cons: "p2 = a2' # p2'"
        unfolding a2'_def p2'_def
        using \<open>p2 \<noteq> []\<close> by auto
      have hd_stem2vert_path_nin_append: 
        "hd (stem2vert_path C M a2' @ a2' # p2') = hd (stem2vert_path C M a2' @ [a2'])"
        by (simp add: hd_append)
      define chv where "chv = (choose_con_vert (set C)a2')"
      have choose_vert_works: "chv \<in> set C" "{a2', chv} \<in> E"
        unfolding chv_def
        using choose_vert_works_1[OF cycle(1) _ _ _  _ quot] quot_aug_path False a2'_def
        by blast+
      moreover have chv_last: "last (stem2vert_path C M a2') = chv"
        using choose_vert_works(1)
        apply (simp add: stem2vert_path_def; intro impI conjI)
        subgoal using find_pfx_works_1 chv_def by fastforce
        subgoal using find_pfx_works_2 chv_def by fastforce
        done
      moreover have path_p2: "path (quotG E) p2"
        using quot_aug_path tl_path_is_path
        by fastforce
      then have "path E p2"
        by(intro path_is_quot_path'[OF path_p2] p2_subset_s)
      ultimately show ?thesis
        apply(intro path_append)
        using path_stem2vert_path[OF cycle(2)]
        by (simp add: a2'_def insert_commute)+
    qed
  } note d1 = this


  note inBetinM = inBetinM[OF cycle(1-3) matching quot]

  {
    fix p1 p2 ::"'a list"
    assume up2_nin_M: "{u, hd p2} \<notin> quotG M"
    assume p1_subset_s: "set p1 \<subseteq> s"
    assume quot_aug_path: "matching_augmenting_path (quotG M) (p1 @ u # p2)" "path (quotG E) (p1 @ u # p2)"
    assume len_ge_2: "length p1 \<ge> 2"
    assume p2_nempty: "p2 \<noteq> []"
    have alt_list_app: "path E (p1 @ stem2vert_path C M (hd p2) @ p2)"
      if  "path E (stem2vert_path C M (hd p2) @ p2)"
    proof-
      have p1_nempty: "p1 \<noteq> []" using len_ge_2 by auto
      show ?thesis
      proof-
        have inM: "{last p1, u} \<in> quotG M"
          using alt_list_append_1'''[OF matching_augmenting_path_feats(2)[OF quot_aug_path(1), unfolded rw4[OF p1_nempty p2_nempty]] _ up2_nin_M]
          by auto
        have i: "{last p1, hd (stem2vert_path C M (hd p2))} \<in> M"
          using inBetinM[OF p1_nempty _ inM] p1_subset_s
          by auto
        show ?thesis
          apply(rule path_append)
          subgoal using path_pref[OF quot_aug_path(2)]
            using path_is_quot_path'[OF _ p1_subset_s] quot by blast
          subgoal using that . 
          subgoal using i matching(2)
            by (metis contra_subsetD cycle(1) hd_append2 hd_stem2vert_nempty odd_cycle_nempty)
          done
      qed
    qed
  } note append_works = this  

  {
    fix p1 p2::"'a list"
    assume p2_subset_s: "set p2 \<subseteq> s"
    assume p2_nempty[simp]: "p2 \<noteq> []" "({u, hd p2} \<notin> quotG M) \<or> p1 = []"
    assume quot_aug_path: "alt_path (quotG M) (u # p2)" (is ?p1) "distinct (u # p2)" (is ?p2) "path (quotG E) (u # p2)" (is ?p3)
    assume alt_list_app: "path E (p1 @ stem2vert_path C M (hd p2) @ p2)"
      if  "path E (stem2vert_path C M (hd p2) @ p2)"
    have "path E (replace_cycle C M p1 p2)"
    proof(cases "last (edges_of_path (find_pfx ((=) (choose_con_vert (set C)(hd p2))) C)) \<in> M")
      case T3: True
      then have i: "path E (stem2vert_path C M (hd p2) @ p2)"
        using d1 p2_nempty(1) quot_aug_path p2_subset_s cycle quot(1)
        by simp
      then show ?thesis
        unfolding replace_cycle_def Let_def
        apply(simp split: if_splits; intro impI conjI)
        subgoal using alt_list_app[OF i] by simp
        subgoal using p2_nempty by simp
        done
    next
      define chv where "chv = (choose_con_vert (set C)(hd p2))"
      case F1: False
      show ?thesis
      proof(cases "chv = last C")
        case T2: True
        then have i: "path E (stem2vert_path C M (hd p2) @ p2)"
          using d1 p2_nempty(1) quot_aug_path p2_subset_s cycle quot(1)
          using chv_def
          by simp
        then show ?thesis
          unfolding replace_cycle_def Let_def
          apply(simp split: if_splits; intro impI conjI)
          subgoal using alt_list_app[OF i] by simp
          subgoal using p2_nempty by simp
          done
      next
        case F2: False
        have choose_vert_works: "chv \<in> set C"
          unfolding chv_def
          using choose_vert_works_1[OF cycle(3) _ _ _ _ quot(1)] quot_aug_path  p2_nempty
          by blast
        moreover have "chv \<noteq> hd C"
          using odd_cycleD(3)[OF cycle(1)] F2
          by auto
        ultimately have i: "last (edges_of_path (find_pfx ((=) chv) (rev C))) \<in> M"
          using F1 find_pfx_edges_of_path_alt_list(2)[OF cycle(1,2,3)]
          using chv_def by blast
        have ii: "distinct (tl (rev C))"
          using cycle(3) odd_cycleD(3)[OF cycle(1)] tl_distinct_rev
          by auto
        have iii: "s = Vs E - set (rev C)"
          using quot by auto
        have iv: "path E (rev C)"
          using cycle(4)
          by (simp add: rev_path_is_path)
        have i: "path E (stem2vert_path C M (hd p2) @ p2)"
          using F1 using d1[OF quot_aug_path(2,3) p2_subset_s ii iv iii] odd_cycle_rev[OF cycle(1)] i
          by (auto simp add: chv_def  stem2vert_path_def hd_rev)
        moreover have "path E (p1 @ stem2vert_path C M (hd p2) @ p2)"
            apply (simp add: chv_def replace_cycle_def stem2vert_path_def)
            apply(intro conjI)
            subgoal using F1
              by (simp add: hd_rev)
            subgoal proof-
              show ?thesis
                using alt_list_app[OF i]
                unfolding replace_cycle_def
                by (metis set_rev stem2vert_path_def)
            qed
            done
        ultimately show ?thesis
          unfolding replace_cycle_def Let_def
          apply(simp split: if_splits; intro impI conjI)
          subgoal using p2_nempty by simp
          done
      qed
    qed
  } note replace_cycle_cases = this


  {
    fix p1 p2::"'a list"
    assume p1_subset_s: "set (rev p1) \<subseteq> s"
    assume up2_in_M: "{u, hd p2} \<in> quotG M \<or> p2 = []"
    assume p1_nempty[simp]: "p1 \<noteq> []"
    have rev_p1_nempty: "rev p1 \<noteq> []" using p1_nempty by auto
    assume quot_aug_path: "alt_path (quotG M) (u # rev p1)" (is ?p1) "distinct (u # rev p1)" (is ?p2) "path (quotG E) (u # rev p1)" (is ?p3)
    assume alt_list_rev: "path E (rev p2 @ stem2vert_path C M (last p1) @ rev p1)"
      if  "path E (stem2vert_path C M (hd (rev p1)) @ rev p1)"
    have "path E (replace_cycle C M p1 p2)"
    proof(cases "last (edges_of_path (find_pfx ((=) (choose_con_vert (set C)(hd (rev p1)))) C)) \<in> M")
      case True
      then have i: "path E (stem2vert_path C M (hd (rev p1)) @ rev p1)"
        using d1 rev_p1_nempty quot_aug_path p1_subset_s cycle quot(1)
        by (simp add: rev_p1_nempty)
      with up2_in_M alt_list_rev show ?thesis
        unfolding replace_cycle_def Let_def
        by(simp add: hd_rev split: if_splits; intro impI conjI)+
    next
      define chv where "chv = (choose_con_vert (set C) (last p1))"
      case F1: False
      show ?thesis
      proof(cases "chv = last C")
        case True
        then have i: "path E (stem2vert_path C M (hd (rev p1)) @ rev p1)"
          using d1[OF] rev_p1_nempty quot_aug_path p1_subset_s cycle quot(1)
          using chv_def
          by blast
        with up2_in_M alt_list_rev show ?thesis
          unfolding replace_cycle_def Let_def
          by(simp add: hd_rev split: if_splits; intro impI conjI)+
      next
        case False
        have choose_vert_works: "chv \<in> set C"
          unfolding chv_def
          using choose_vert_works_1[OF cycle(3) _ _ _ _ quot(1)] quot_aug_path p1_nempty rev_p1_nempty
          by (metis (no_types,lifting) append_Nil hd_rev)
        moreover have "chv \<noteq> hd C"
          using odd_cycleD(3)[OF cycle(1)] False
          by auto
        ultimately have i: "last (edges_of_path (find_pfx ((=) chv) (rev C))) \<in> M"
          using F1 find_pfx_edges_of_path_alt_list(2)[OF cycle(1,2,3)]
          using chv_def hd_rev p1_nempty by metis
        have ii: "distinct (tl (rev C))"
          using cycle(3) odd_cycleD(3)[OF cycle(1)] tl_distinct_rev
          by auto
        have iii: "s = Vs E - set (rev C)"
          using quot by auto
        have iv: "path E (rev C)"
          using cycle(4)
          by (simp add: rev_path_is_path)
        have i: "path E (stem2vert_path C M (hd (rev p1)) @ rev p1)"
          using F1 
          using cycle(3,4) d1 p1_subset_s quot quot_aug_path(2) quot_aug_path(3) by blast
        moreover have "path E (rev p2 @ stem2vert_path C M (last p1) @ rev p1)"
          unfolding replace_cycle_def stem2vert_path_def
          apply (simp add: p1_nempty chv_def)
          apply(intro conjI)
          subgoal using F1  p1_nempty
            by (simp add: hd_rev)
          subgoal proof-
            show ?thesis
              using alt_list_rev[OF i]
              unfolding replace_cycle_def
              using p1_nempty
              by (metis set_rev stem2vert_path_def)
          qed
          done
        ultimately show ?thesis
          unfolding replace_cycle_def Let_def
          using up2_in_M
          by(simp add: hd_rev split: if_splits; intro impI conjI)+
      qed
    qed
  } note replace_cycle_cases_p1 = this
    (*To be able to give up replace_cycle_cases_p1 and use replace_cycle_cases instead of it, we need
    to show that rev (replace_cycle) = replace_cycle.*)




  have "path (quotG E) (u # p2)"
    using path_suff quot_aug_path
    by blast
  then have "set p2 \<subseteq> Vs (quotG E)"
    using quot
    using split_list_first tl_path_is_path
    by (metis list.sel(3) subset_path_Vs)
  moreover have u_nin_p2: "u \<notin> set p2"
    using quot_aug_path
    by auto
  ultimately have p2_subset_s[simp]: "set p2 \<subseteq> s"
    using quot good_quot_map
    by (metis (no_types, lifting) neq_u_notin_quotG set_rev_mp subsetI)

  have "path (quotG E) (p1 @ [u])"
    using quot_aug_path(1) quot_aug_path(2)
    by (auto simp: path_pref)
  then have "set p1 \<subseteq> Vs (quotG E)"
    using quot
    using split_list_first tl_path_is_path
    by (metis path_pref subset_path_Vs)
  moreover have u_nin_p1: "u \<notin> set (rev p1)"
    using quot_aug_path
    by auto
  ultimately have p1_subset_s: "set (rev p1) \<subseteq> s"
    using quot good_quot_map
    by (metis (no_types,lifting)  in_quotG_neq_u set_rev subset_code(1))

  have [simp]: "matching_augmenting_path (quotG M) p'" "path (quotG E) p'"
    using quot_aug_path(2) by simp+

  show ?thesis
  proof(cases "p1 = []")
    case nil1: True
    show ?thesis
    proof(cases "p2 = []")
      case nil2: True
      then show ?thesis
        using matching_augmenting_path_feats(1)[OF \<open>matching_augmenting_path (quotG M) p'\<close>] quot_aug_path(1)
        by (simp add: nil1 )
    next
      case p2_nempty: False
      show ?thesis
        using replace_cycle_cases[OF p2_subset_s p2_nempty _ ] matching_augmenting_path_feats(2)[OF \<open>matching_augmenting_path (quotG M) p'\<close>]
              quot_aug_path
        by (simp add: p2_nempty nil1)
    qed
  next
    case p1_nempty[simp]: False
    show ?thesis
    proof(cases "alt_path (quotG M) (u # p2)")
      case T1: True
      show ?thesis
      proof(cases "p2 = []")
        case T2: True
        have quot_aug_path_p1: "alt_path (quotG M) (u # rev p1)" (is ?p1) "distinct (u # rev p1)" (is ?p2) "path (quotG E) (u # rev p1)" (is ?p3)
        proof-
          have "alt_path (quotG M) (p1 @ [u])"
            using matching_augmenting_path_feats[OF \<open>matching_augmenting_path (quotG M) p'\<close>] quot_aug_path(1) T2
            by simp
          have rw: "edges_of_path p' = (edges_of_path (p1 @ [u])) @ edges_of_path (u # p2)"
            using edges_of_path_append_2 quot_aug_path(1) by fastforce
          have eop_nempty: "edges_of_path (p1 @ [u]) \<noteq> []"
            by (metis Nil_is_append_conv edges_of_path_snoc list.distinct(1) p1_nempty)
          have "alt_path (quotG M) (rev (p1 @ [u]))"
            unfolding edges_of_path_rev[symmetric]
            apply(intro alt_list_rev)
            subgoal 
              using T2 matching_augmenting_path_last_edge_nin quot_aug_path(1) quot_aug_path(2)
              using \<open>alt_path (quotG M) (p1 @ [u])\<close> by fastforce
            subgoal
              using T2 matching_augmenting_path_odd_length quot_aug_path(1) quot_aug_path(2) by blast
            done
          then show ?p1
            by simp
          show ?p2
            using quot_aug_path
            by simp
          show ?p3
            using quot_aug_path
            using T2 rev_path_is_path by force
        qed
        have rev_p1_nempty: "rev p1 \<noteq> []" using p1_nempty by simp
        show ?thesis
          using replace_cycle_cases_p1[OF p1_subset_s _ p1_nempty quot_aug_path_p1] T2
          by (simp add: hd_rev)
      next
        case p2_nempty: False
        then have up2_nin_M: "{u, hd p2} \<notin> quotG M"
          using T1
          by(cases p2; auto simp add: alt_list_step)
        show ?thesis
        proof(cases "length p1 \<ge> 2")
          case len_ge_2: True
          have path_app: "path E (p1 @ stem2vert_path C M (hd p2) @ p2)"
            if  "path E (stem2vert_path C M (hd p2) @ p2)"
            using append_works[OF up2_nin_M _ _ _ len_ge_2 p2_nempty] p1_subset_s
                  quot_aug_path[unfolded quot_aug_path(1)]
            by (simp add: that)
          have quot_aug_path_p2: "alt_path (quotG M) (u # p2)" (is ?p1) "distinct (u # p2)" (is ?p2) "path (quotG E) (u # p2)" (is ?p3)
          proof-
            show ?p1
              using T1 by blast
            show ?p2
              using quot_aug_path
              by simp
            show ?p3
              using quot_aug_path rev_path_is_path  \<open>path (quotG E) (u # p2)\<close>
              by fastforce
          qed
          show ?thesis
            using replace_cycle_cases[OF p2_subset_s p2_nempty _ quot_aug_path_p2 path_app] up2_nin_M
            by blast
        next
          case False                                                                                                    
          then have "length p1 = 1"
            by (metis One_nat_def Suc_1 Suc_leI eq_iff length_greater_0_conv not_less_eq_eq p1_nempty)
          then obtain a where "p1 = [a]"
            by (metis One_nat_def add.commute add.right_neutral length_0_conv length_tl list.collapse list.sel(3) list.size(4))
          then have False
            using quot_aug_path(1) matching_augmenting_path_feats(2)[OF \<open>matching_augmenting_path (quotG M) p'\<close>] up2_nin_M p2_nempty
            by(auto simp add: alt_list_step neq_Nil_conv)
          then show ?thesis by simp
        qed        
      qed
    next
      case p2_nalt: False
      have last_p1_nin: "alt_path (quotG M) (p1 @ [u])" (is ?p1)
        "last (edges_of_path (p1 @ [u])) \<notin> quotG M" (is ?p2)
      proof-
        have rw: "edges_of_path p' = (edges_of_path (p1 @ [u])) @ edges_of_path (u # p2)"
          using edges_of_path_append_2 quot_aug_path(1) by fastforce
        have eop_nempty: "edges_of_path (p1 @ [u]) \<noteq> []"
          by (metis Nil_is_append_conv edges_of_path_snoc list.distinct(1) p1_nempty)
        show ?p1 ?p2
          using alt_list_append_1'[OF matching_augmenting_path_feats(2)[OF \<open>matching_augmenting_path (quotG M) p'\<close>, unfolded rw] eop_nempty] p2_nalt
          by blast+
      qed
      have up2_nin_M: "{last p1 , u} \<notin> quotG M"
      proof-
        have "last (edges_of_path (p1 @ [u])) = {last p1, u}"
          using p1_nempty
          by (metis edges_of_path_snoc last_snoc)
        then show ?thesis 
          using last_p1_nin by auto
      qed
      have rev_p1_nempty: "rev p1 \<noteq> []" using p1_nempty by auto
      have up2_in_M: "{u, hd p2} \<in> quotG M" if "p2 \<noteq> []"
        using  matching_augmenting_path_feats(2)[OF \<open>matching_augmenting_path (quotG M) p'\<close>]
        unfolding rw4[OF p1_nempty that] quot_aug_path(1)
        using alt_list_append_1'' p2_nalt up2_nin_M
        by (metis (no_types,lifting)) 
      show ?thesis
      proof(cases "length p2 \<ge> 2")
        case len_p2_ge_2[simp]: True
        have *:"rev p2 @ u # rev p1 = rev p'"
          by (simp add: quot_aug_path(1))
        hence "matching_augmenting_path (quotG M) p'"
          using \<open>matching_augmenting_path (quotG M) p'\<close>
          by simp
        moreover have "path (quotG E) p'"
          using \<open>path (quotG E) p'\<close> rev_path_is_path
          by auto
        have "{u, hd (rev p1)} \<notin> quotG M"
          using up2_nin_M
          by (simp add: hd_rev insert_commute)
        then have app_works: "path E (rev p2 @ stem2vert_path C M (last p1) @ rev p1)"
          if  "path E (stem2vert_path C M (last p1) @ rev p1)"
          unfolding hd_rev[symmetric]   
          apply(intro append_works)
          using that[unfolded hd_rev[symmetric]]
          by (simp add: * matching_augmenting_path_rev rev_path_is_path)+
        have quot_aug_path_p1: "alt_path (quotG M) (u # rev p1)" (is ?p1) "distinct (u # rev p1)" (is ?p2) "path (quotG E) (u # rev p1)" (is ?p3)
        proof-
          have "alt_path (quotG M) (rev (p1 @ [u]))"
            unfolding edges_of_path_rev[symmetric]
            apply(intro alt_list_rev)
            using last_p1_nin
            by (metis(no_types,lifting) alternating_list_even_last edges_of_path_snoc last_p1_nin(1) last_p1_nin(2) p1_nempty snoc_eq_iff_butlast)+
          then show ?p1
            by simp
          show ?p2
            using quot_aug_path
            by simp
          show ?p3
            using quot_aug_path rev_path_is_path  \<open>path (quotG E) (p1 @ [u])\<close>
            by fastforce
        qed
        show "path E (replace_cycle C M p1 p2)"
          using replace_cycle_cases_p1[OF p1_subset_s _ p1_nempty quot_aug_path_p1 app_works] up2_in_M
          using hd_rev p1_nempty by (metis(no_types,lifting))
      next
        case len_p2_nge_2: False
        show ?thesis
        proof(cases "p2 = []")
          case True
          then have False
            using p2_nalt alt_list.intros(1) 
            by auto
          then show ?thesis by simp
        next
          case p2_nempty: False
          then have "length p2 = 1"
            using len_p2_nge_2
            by (metis One_nat_def Suc_1 Suc_leI eq_iff length_greater_0_conv not_less_eq_eq p2_nempty)
          then obtain a where "p2 = [a]"
            by (metis One_nat_def add.commute add.right_neutral length_0_conv length_tl list.collapse list.sel(3) list.size(4))
          then have False
            using quot_aug_path(1) matching_augmenting_path_feats(2)[OF \<open>matching_augmenting_path (quotG M) p'\<close>] up2_nin_M p2_nempty
            by (metis matching_augmenting_path_last_edge_nin edges_of_path.simps(2) edges_of_path.simps(3) edges_of_path_append last_snoc list.sel(1) quot_aug_path(2) up2_in_M)
          then show ?thesis by simp
        qed
      qed
    qed
  qed
qed

end

lemma find_pfx_butlast:
  assumes "\<not> (Q (last C))" "v \<in> set C" "Q v"
  shows "(\<exists>suf. find_pfx Q C @ suf = butlast C)"
  using assms
proof(induction C arbitrary: v)
  case Nil
  then show ?case by simp
next
  case (Cons a C)
  then show ?case 
    by auto
qed

context quot
begin

lemma stem2vert_path_pref_or_suc:
  assumes "odd_cycle C" "alt_path M C" "w \<noteq> last C" "w \<in> set C" "w = (choose_con_vert (set C) v)"
  shows "(\<exists>pref. pref @ (rev (stem2vert_path C M v)) = tl C) \<or> (\<exists>suf. ((stem2vert_path C M v)) @ suf = butlast C)"
  unfolding stem2vert_path_def
  apply(simp split: if_splits; intro conjI impI)
  subgoal using odd_cycleD(3)[OF assms(1)] find_pfx_butlast[where Q = "((=) w)", OF assms(3,4)] assms(5)
    by blast
  subgoal proof-
    have i: "w \<noteq> last (rev C)"
      using odd_cycle_nempty[OF assms(1)] odd_cycleD(3)[OF assms(1)] assms(3)
      by (simp add: last_rev)
    moreover have ii: "w \<in> set (rev C)"
      using assms(4) by auto
    show ?thesis
      using find_pfx_butlast[where Q = "((=) w)", OF i ii] assms(5)
      by (metis append_Cons append_Nil butlast_snoc list.exhaust_sel rev_append rev_rev_ident rev_singleton_conv)
  qed
  done

lemma stem2vert_path_distinct_neq_lastC:
  assumes "odd_cycle C" "alt_path M C" "w \<noteq> last C" "w \<in> set C" "w = choose_con_vert (set C) v" "distinct (tl C)"
  shows "distinct (stem2vert_path C M v)"
  using stem2vert_path_pref_or_suc[OF assms(1-4)] 
  using distinct_tl_then_butlast[OF assms(6)  odd_cycleD(3)[OF assms(1)] odd_cycle_nempty[OF assms(1)]]
  by (metis assms(5) assms(6) distinct_append distinct_rev)

lemma stem2vert_path_distinct:
  assumes "odd_cycle C" "alt_path M C" "w \<in> set C" "w = choose_con_vert (set C) v" "distinct (tl C)"
  shows "distinct (stem2vert_path C M v)"
proof(cases "w = last C")
  case True
  then show ?thesis
    using assms
    unfolding stem2vert_path_def
    by (smt distinct.simps(1) distinct.simps(2) empty_iff empty_set find_pfx.simps(2) hd_rev list.exhaust_sel odd_cycleD(3) set_rev)
next
  case False
  then show ?thesis
    using stem2vert_path_distinct_neq_lastC[OF assms(1,2) False assms(3-5)]
    by auto
qed

lemma distinct_replace_cycle:
  assumes cycle: "odd_cycle C" "alt_path M C" "distinct (tl C)" "path E C" and
    quot_aug_path: "p' = (p1 @ u # p2)" "graph_augmenting_path (quotG E) (quotG M) p'" and 
    matching: "matching M" "M \<subseteq> E" and
    quot: "s = (Vs E) - set C"(*  and
    graph: "dblton_graph E"*)
  shows "distinct (replace_cycle C M p1 p2)"
proof-


  {
    fix C fix p1 p2::"'a list"
    define a2' where "a2' = hd p2"
    assume quot_aug_path: "distinct (u # p2)" "path (quotG E) (u # p2)"
    assume p2_subset_s: "set p2 \<subseteq> s"
    assume cycle: "odd_cycle C" "alt_path M C" "distinct (tl C)" "path E C"
    assume quot: "s = (Vs E) - set C"
    assume p2_nempty: "p2 \<noteq> []"
    define p2' where "p2' = tl p2"
    have Cons: "p2 = a2' # p2'"
      unfolding a2'_def p2'_def
      using \<open>p2 \<noteq> []\<close> by auto
    have hd_stem2vert_path_nin_append: "hd (stem2vert_path C M a2' @ a2' # p2') = hd (stem2vert_path C M a2' @ [a2'])"
      by (simp add: hd_append)
    define chv where "chv = (choose_con_vert (set C) a2')"
    have choose_vert_works: "chv \<in> set C" "{a2', chv} \<in> E"
      unfolding chv_def
      using choose_vert_works_1[OF cycle(3) _ _ _  _ quot] quot_aug_path
      by (metis (no_types,lifting)\<open>(p2::'a::type list) \<noteq> []\<close> a2'_def append_Nil)+
    have "distinct (stem2vert_path C M (hd p2) @ p2)"
      unfolding distinct_append
      apply(intro conjI)
      subgoal apply(intro stem2vert_path_distinct[OF cycle(1,2) choose_vert_works(1)] cycle(3))
        unfolding chv_def a2'_def by simp
      subgoal using quot_aug_path(1) by auto
      subgoal using quot stem2vert_path_subset p2_subset_s
        by fastforce
      done
  } note d1 = this

  {
    fix p1 p2 ::"'a list"
    assume up2_nin_M: "{u, hd p2} \<notin> quotG M"
    assume p1_subset_s: "set p1 \<subseteq> s"
    assume p2_subset_s: "set p2 \<subseteq> s"
    assume quot_aug_path: "matching_augmenting_path (quotG M) (p1 @ u # p2)"  "distinct (p1 @ u # p2)" "path (quotG E) (p1 @ u # p2)"
    assume len_ge_2: "length p1 \<ge> 2"
    assume p2_nempty: "p2 \<noteq> []"
    have alt_list_app: "distinct (p1 @ stem2vert_path C M (hd p2) @ p2)"
      if  "distinct (stem2vert_path C M (hd p2) @ p2)"
    proof-
      have p1_nempty: "p1 \<noteq> []" using len_ge_2 by auto
      show ?thesis
        apply(subst distinct_append)
        apply(intro conjI)
        subgoal using quot_aug_path(2)
          by simp
        subgoal using that.
        subgoal using quot stem2vert_path_subset p1_subset_s p2_subset_s quot_aug_path(2)
          by fastforce
        done
    qed
  } note append_works = this  

  {
    fix p1 p2::"'a list"
    assume p2_subset_s: "set p2 \<subseteq> s"
    assume p2_nempty: "p2 \<noteq> []" "({u, hd p2} \<notin> quotG M) \<or> p1 = []"
    assume quot_aug_path:  "distinct (u # p2)" (is ?p2) "path (quotG E) (u # p2)" (is ?p3)
    assume distinct_app: "distinct (p1 @ stem2vert_path C M (hd p2) @ p2)"
      if  "distinct (stem2vert_path C M (hd p2) @ p2)"
    have "distinct (replace_cycle C M p1 p2)"
    proof(cases "last (edges_of_path (find_pfx ((=) (choose_con_vert (set C) (hd p2))) C)) \<in> M")
      case T3: True
      then have i: "distinct (stem2vert_path C M (hd p2) @ p2)"
        using d1 p2_nempty(1) quot_aug_path p2_subset_s cycle quot(1)
        by simp
      show ?thesis
        unfolding replace_cycle_def Let_def
        apply(simp split: if_splits; intro impI conjI)
        using p2_nempty i distinct_app[OF i] by simp+
    next
      define chv where "chv = (choose_con_vert (set C) (hd p2))"
      case F1: False
      show ?thesis
      proof(cases "chv = last C")
        case T2: True
        then have i: "distinct (stem2vert_path C M (hd p2) @ p2)"
          using d1 p2_nempty(1) quot_aug_path p2_subset_s cycle quot(1)
          using chv_def
          by simp
        show ?thesis
          unfolding replace_cycle_def Let_def
          apply(simp split: if_splits; intro impI conjI)
          using p2_nempty i distinct_app[OF i] by simp+
      next
        case F2: False
        have choose_vert_works: "chv \<in> set C"
          unfolding chv_def
          using choose_vert_works_1[OF cycle(3) _ _ _ _ quot(1)] quot_aug_path  p2_nempty
          by (metis (no_types,lifting) append_Nil)
        moreover have "chv \<noteq> hd C"
          using odd_cycleD(3)[OF cycle(1)] F2
          by auto
        ultimately have i: "last (edges_of_path (find_pfx ((=) chv) (rev C))) \<in> M"
          using F1 find_pfx_edges_of_path_alt_list(2)[OF cycle(1-3)]
          using chv_def by blast
        have i: "distinct (stem2vert_path C M (hd p2) @ p2)"
          using F1 using d1[OF quot_aug_path p2_subset_s] odd_cycle_rev[OF cycle(1)]
          using cycle(1-4) p2_nempty(1) quot by blast
        show ?thesis
          unfolding replace_cycle_def Let_def
          apply(simp split: if_splits; intro impI conjI)
          using p2_nempty i distinct_app[OF i] by simp+
      qed
    qed
  } note replace_cycle_cases = this


  {
    fix p1 p2::"'a list"
    assume p1_subset_s: "set (rev p1) \<subseteq> s"
    assume up2_in_M: "{u, hd p2} \<in> quotG M \<or> p2 = []"
    assume p1_nempty: "p1 \<noteq> []"
    have rev_p1_nempty: "rev p1 \<noteq> []" using p1_nempty by auto
    assume quot_aug_path: "distinct (u # rev p1)" (is ?p2) "path (quotG E) (u # rev p1)" (is ?p3)
    assume distinct_rev: "distinct (rev p2 @ stem2vert_path C M (last p1) @ rev p1)"
      if  "distinct (stem2vert_path C M (hd (rev p1)) @ rev p1)"
    have "distinct (replace_cycle C M p1 p2)"
    proof(cases "last (edges_of_path (find_pfx ((=) (choose_con_vert (set C) (hd (rev p1)))) C)) \<in> M")
      case True
      then have i: "distinct (stem2vert_path C M (hd (rev p1)) @ rev p1)"
        by(intro d1 rev_p1_nempty quot_aug_path p1_subset_s cycle quot(1))
      show ?thesis
        unfolding replace_cycle_def Let_def
        apply(simp split: if_splits; intro impI conjI)
        using p1_nempty i distinct_rev[OF i] up2_in_M by simp+
    next
      define chv where "chv = (choose_con_vert (set C) (last p1))"
      case F1: False
      show ?thesis
      proof(cases "chv = last C")
        case True
        then have i: "distinct (stem2vert_path C M (hd (rev p1)) @ rev p1)"
          using d1[OF] rev_p1_nempty quot_aug_path p1_subset_s cycle quot(1)
          using chv_def
          by blast
        show ?thesis
          unfolding replace_cycle_def Let_def
          apply(simp split: if_splits; intro impI conjI)
          using p1_nempty i distinct_rev[OF i] up2_in_M by simp+
      next
        case False
        have choose_vert_works: "chv \<in> set C"
          unfolding chv_def
          using choose_vert_works_1[OF cycle(3) _ _ _ _ quot(1)] quot_aug_path p1_nempty rev_p1_nempty
          by (metis (no_types,lifting) append_Nil hd_rev)
        moreover have "chv \<noteq> hd C"
          using odd_cycleD(3)[OF cycle(1)] False
          by auto
        ultimately have i: "last (edges_of_path (find_pfx ((=) chv) (rev C))) \<in> M"
          using F1 find_pfx_edges_of_path_alt_list(2)[OF cycle(1-3)]
          using chv_def hd_rev p1_nempty
          by metis
        have ii: "distinct (tl (rev C))"
          using cycle(3) odd_cycleD(3)[OF cycle(1)] tl_distinct_rev
          by auto
        have iii: "s = Vs E - set (rev C)"
          using quot by auto
        have iv: "path E (rev C)"
          using cycle(4)
          by (simp add: rev_path_is_path)
        have i: "distinct (stem2vert_path C M (hd (rev p1)) @ rev p1)"
          using d1 p1_subset_s quot quot_aug_path
                cycle(1-4) rev_p1_nempty
          by blast
        show ?thesis
          unfolding replace_cycle_def Let_def
          apply(simp split: if_splits; intro impI conjI)
          using p1_nempty i distinct_rev[OF i] up2_in_M by simp+
      qed
    qed
  } note replace_cycle_cases_p1 = this
    (*To be able to give up replace_cycle_cases_p1 and use replace_cycle_cases instead of it, we need
    to show that rev (replace_cycle) = replace_cycle.*)

  have "path (quotG E) (u # p2)"
    using path_suff quot_aug_path
    by blast
  then have "set p2 \<subseteq> Vs (quotG E)"
    using quot
    using split_list_first tl_path_is_path
    by (metis list.sel(3) subset_path_Vs)
  moreover have u_nin_p2: "u \<notin> set p2"
    using quot_aug_path
    by auto
  ultimately have p2_subset_s: "set p2 \<subseteq> s"
    using quot good_quot_map
    by (metis (no_types,lifting) neq_u_notin_quotG set_rev_mp subsetI)

  have "path (quotG E) (p1 @ [u])"
    using quot_aug_path
    by (auto simp: path_pref)
  then have "set p1 \<subseteq> Vs (quotG E)"
    using quot
    using split_list_first tl_path_is_path
    by (metis (no_types,lifting) path_pref subset_path_Vs)
  moreover have u_nin_p1: "u \<notin> set (rev p1)"
    using quot_aug_path
    by auto
  ultimately have p1_subset_s: "set (rev p1) \<subseteq> s"
    using quot good_quot_map
    by (metis (no_types,lifting) in_quotG_neq_u order_refl set_rev subset_code(1))

  have "matching_augmenting_path (quotG M) p'"
    using quot_aug_path(2) by simp
  note p'_feats = matching_augmenting_path_feats[OF \<open>matching_augmenting_path (quotG M) p'\<close>]

  show ?thesis
  proof(cases "p1 = []")
    case nil1: True
    show ?thesis
    proof(cases "p2 = []")
      case nil2: True
      then show ?thesis
        using quot_aug_path(1) p'_feats
        by (simp add: nil1 )
    next
      case p2_nempty: False
      show ?thesis
        using replace_cycle_cases[OF p2_subset_s p2_nempty _ ] nil1 p'_feats quot_aug_path
        by (simp add: p2_nempty nil1)
    qed
  next
    case p1_nempty: False
    show ?thesis
    proof(cases "alt_path (quotG M) (u # p2)")
      case T1: True
      show ?thesis
      proof(cases "p2 = []")
        case T2: True
        have quot_aug_path_p1: "distinct (u # rev p1)" (is ?p2) "path (quotG E) (u # rev p1)" (is ?p3)
        proof-
          show ?p2
            using quot_aug_path
            by simp
          show ?p3
            using quot_aug_path
            using T2 rev_path_is_path by force
        qed
        have rev_p1_nempty: "rev p1 \<noteq> []" using p1_nempty by simp
        show ?thesis
          using replace_cycle_cases_p1[OF p1_subset_s _ p1_nempty quot_aug_path_p1] T2
          by (simp add: hd_rev)
      next
        case p2_nempty: False
        then have up2_nin_M: "{u, hd p2} \<notin> quotG M"
          using T1
          by(cases p2; auto simp add: alt_list_step)
        show ?thesis
        proof(cases "length p1 \<ge> 2")
          case len_ge_2: True
          have path_app: "distinct (p1 @ stem2vert_path C M (hd p2) @ p2)"
            if  "distinct (stem2vert_path C M (hd p2) @ p2)"
            using append_works up2_nin_M _ p'_feats(2,4)[unfolded quot_aug_path(1)] len_ge_2 p2_nempty p1_subset_s
            using p2_subset_s quot_aug_path(1) quot_aug_path that
            by auto
          have quot_aug_path_p2: "distinct (u # p2)" (is ?p2) "path (quotG E) (u # p2)" (is ?p3)
          proof-
            show ?p2
              using quot_aug_path
              by simp
            show ?p3
              using quot_aug_path rev_path_is_path  \<open>path (quotG E) (u # p2)\<close>
              by fastforce
          qed
          show ?thesis
            using replace_cycle_cases[OF p2_subset_s p2_nempty _ quot_aug_path_p2 path_app] up2_nin_M
            by blast
        next
          case False                                                                                                    
          then have "length p1 = 1"
            by (metis One_nat_def Suc_1 Suc_leI eq_iff length_greater_0_conv not_less_eq_eq p1_nempty)
          then obtain a where "p1 = [a]"
            by (metis One_nat_def add.commute add.right_neutral length_0_conv length_tl list.collapse list.sel(3) list.size(4))
          then have False
            using quot_aug_path(1) p'_feats up2_nin_M p2_nempty
            by(auto simp add: alt_list_step neq_Nil_conv)
          then show ?thesis by simp
        qed        
      qed
    next
      case p2_nalt: False
      have last_p1_nin: "alt_path (quotG M) (p1 @ [u])" (is ?p1)
        "last (edges_of_path (p1 @ [u])) \<notin> quotG M" (is ?p2)
      proof-
        have rw: "edges_of_path p' = (edges_of_path (p1 @ [u])) @ edges_of_path (u # p2)"
          using edges_of_path_append_2 quot_aug_path(1) by fastforce
        have eop_nempty: "edges_of_path (p1 @ [u]) \<noteq> []"
          by (metis Nil_is_append_conv edges_of_path_snoc list.distinct(1) p1_nempty)
        show ?p1 ?p2
          using alt_list_append_1'[OF p'_feats(2)[unfolded rw] eop_nempty] p2_nalt
          by blast+
      qed
      have up2_nin_M: "{last p1 , u} \<notin> quotG M"
      proof-
        have "last (edges_of_path (p1 @ [u])) = {last p1, u}"
          using p1_nempty
          by (metis edges_of_path_snoc last_snoc)
        then show ?thesis 
          using last_p1_nin by auto
      qed
      have rev_p1_nempty: "rev p1 \<noteq> []" using p1_nempty by auto
      have up2_in_M: "{u, hd p2} \<in> quotG M" if "p2 \<noteq> []"
        using p'_feats(2)
        unfolding rw4[OF p1_nempty that] quot_aug_path(1)
        using alt_list_append_1'' p2_nalt up2_nin_M
        by (metis(no_types,lifting)) 
      show ?thesis
      proof(cases "length p2 \<ge> 2")
        case len_p2_ge_2: True
        have app_works: "distinct (rev p2 @ stem2vert_path C M (last p1) @ rev p1)"
          if  "distinct (stem2vert_path C M (last p1) @ rev p1)"
          unfolding hd_rev[symmetric]
          apply(rule append_works)
          subgoal using up2_nin_M by (simp add: hd_rev p1_nempty insert_commute)
          subgoal using p2_subset_s by auto
          subgoal using p1_subset_s by auto
          subgoal proof-
            have "rev p2 @ u # rev p1 = rev p'"
              by (simp add: quot_aug_path(1))
            then show ?thesis
              using quot_aug_path(1,2) matching_augmenting_path_rev by force
          qed
          subgoal using quot_aug_path rev_path_is_path
            by fastforce
          subgoal using quot_aug_path rev_path_is_path
            by fastforce
          subgoal using len_p2_ge_2 by auto
          subgoal using p1_nempty by auto
          subgoal using that[unfolded hd_rev[symmetric]] .
          done
        have quot_aug_path_p1: "distinct (u # rev p1)" (is ?p2) "path (quotG E) (u # rev p1)" (is ?p3)
        proof-
          show ?p2
            using quot_aug_path
            by simp
          show ?p3
            using quot_aug_path rev_path_is_path  \<open>path (quotG E) (p1 @ [u])\<close>
            by fastforce
        qed
        show "distinct (replace_cycle C M p1 p2)"
          using replace_cycle_cases_p1[OF p1_subset_s _ p1_nempty quot_aug_path_p1 app_works] up2_in_M
          using hd_rev p1_nempty by (metis(no_types,lifting))
      next
        case len_p2_nge_2: False
        show ?thesis
        proof(cases "p2 = []")
          case True
          then have False
            using p2_nalt alt_list.intros(1) by auto
          then show ?thesis by simp
        next
          case p2_nempty: False
          then have "length p2 = 1"
            using len_p2_nge_2
            by (metis One_nat_def Suc_1 Suc_leI eq_iff length_greater_0_conv not_less_eq_eq p2_nempty)
          then obtain a where "p2 = [a]"
            by (metis One_nat_def add.commute add.right_neutral length_0_conv length_tl list.collapse list.sel(3) list.size(4))
          then have False
            using quot_aug_path(1) p'_feats(2) up2_nin_M p2_nempty
            by (metis (no_types,lifting) matching_augmenting_path_last_edge_nin edges_of_path.simps(2) edges_of_path.simps(3) edges_of_path_append last_snoc list.sel(1) quot_aug_path(2) up2_in_M)
          then show ?thesis by simp
        qed
      qed
    qed
  qed
qed

lemma hd_nin_last_nin_replace_cycle:
  assumes cycle: "odd_cycle C" "alt_path M C" "distinct (tl C)" "path E C" and
    quot_aug_path: "p' = (p1 @ u # p2)" "graph_augmenting_path (quotG E) (quotG M) p'" and 
    matching: "matching M" "M \<subseteq> E" and
    quot: "s = (Vs E) - set C"(*  and
    graph: "dblton_graph E"*)
  shows "hd (replace_cycle C M p1 p2) \<notin> Vs M \<and> last (replace_cycle C M p1 p2) \<notin> Vs M"
proof-
  {
    fix C fix p1 p2::"'a list"
    define a2' where "a2' = hd p2"
    assume quot_aug_path: "matching_augmenting_path (quotG M) (u # p2)"
    assume p2_subset_s: "set p2 \<subseteq> s"
    assume cycle: "odd_cycle C" "alt_path M C" "distinct (tl C)"
    assume quot: "s = (Vs E) - set C"
    assume p2_nempty: "p2 \<noteq> []"
    define p2' where "p2' = tl p2"
    have Cons: "p2 = a2' # p2'"
      unfolding a2'_def p2'_def
      using \<open>p2 \<noteq> []\<close> by auto
    have hd_stem2vert_path_nin_append: "hd (stem2vert_path C M a2' @ a2' # p2') = hd (stem2vert_path C M a2' @ [a2'])"
      by (simp add: hd_append)
    define chv where "chv = (choose_con_vert (set C) a2')"
    have "hd (stem2vert_path C M (hd p2) @ p2) \<notin> Vs M \<and> last (stem2vert_path C M (hd p2) @ p2) \<notin> Vs M"
      apply(intro conjI)
      subgoal proof-
        have "hd (stem2vert_path C M (hd p2) @ p2) = hd C"
          by (metis cycle(1) hd_append2 hd_stem2vert_nempty hd_stem2vert_path odd_cycleD(3) odd_cycle_nempty)
        then show ?thesis
          using matching_augmenting_path_feats(3)[OF quot_aug_path(1)]
                quot
          using cycle(1-3) graph matching(1) matching(2) odd_cycleD(3) not_in_quot_matching_not_in_matching by fastforce
      qed
      subgoal proof-
        have "last (stem2vert_path C M (hd p2) @ p2) = last p2"
          using p2_nempty
          by simp
        then show ?thesis
          using matching_augmenting_path_feats(4)[OF quot_aug_path(1)]
          using p2_nempty
          by (metis (no_types, lifting) last.simps last_in_set matching(2) p2_subset_s subsetD vert_in_graph_iff_in_quot_diff_u)
      qed
      done
  } note d1 = this

  {
    fix p1 p2 p3 ::"'a list"
    assume p1_subset_s: "set p1 \<subseteq> s"
    assume p2_subset_s: "set p2 \<subseteq> s"
    assume quot_aug_path: "matching_augmenting_path (quotG M) (p1 @ u # p2)"
    assume p1_nempty: "p1 \<noteq> []"
    assume p2_nempty: "p2 \<noteq> []"
    have alt_list_app: "hd (p1 @ p3 @ p2) \<notin> Vs M \<and> last (p1 @ p3 @ p2) \<notin> Vs M"
      apply(intro conjI)
      subgoal using matching_augmenting_path_feats(3)[OF quot_aug_path(1)] p1_nempty
        by (metis (no_types,lifting) matching(2) hd_append2 list.set_sel(1) p1_subset_s rev_subsetD vert_in_graph_iff_in_quot_diff_u)
      subgoal using matching_augmenting_path_feats(4)[OF quot_aug_path(1)] p2_nempty
        by (metis (no_types,lifting) matching(2) append_is_Nil_conv last_ConsR last_append last_in_set list.simps(3) p2_subset_s subsetCE vert_in_graph_iff_in_quot_diff_u)
      done
  } note append_works = this  

  {
    fix p1 p2::"'a list"
    assume p2_subset_s: "set p2 \<subseteq> s"
    assume p2_nempty: "p2 \<noteq> []"
    assume nin_app: "hd (p1 @ p3 @ p2) \<notin> Vs M \<and> last (p1 @ p3 @ p2) \<notin> Vs M" for p3
    have "hd (replace_cycle C M p1 p2) \<notin> Vs M \<and> last (replace_cycle C M p1 p2) \<notin> Vs M"
      unfolding replace_cycle_def Let_def
      apply(simp split: if_splits; intro impI conjI)
      using p2_nempty nin_app by (simp add: hd_rev last_rev)+
  } note replace_cycle_cases = this

  have "matching_augmenting_path (quotG M) p'" "path (quotG E) p'"
    using quot_aug_path(2)
    by simp+
  note p'_feats = matching_augmenting_path_feats[OF \<open>matching_augmenting_path (quotG M) p'\<close>]

  have "path (quotG E) (u # p2)"
    using path_suff \<open>path (quotG E) p'\<close> quot_aug_path(1)
    by auto
  then have "set p2 \<subseteq> Vs (quotG E)"
    using quot
    using split_list_first tl_path_is_path
    by (metis list.sel(3) subset_path_Vs)
  moreover have u_nin_p2: "u \<notin> set p2"
    using quot_aug_path
    by auto
  ultimately have p2_subset_s: "set p2 \<subseteq> s"
    using quot good_quot_map
    by (metis (no_types,lifting) neq_u_notin_quotG set_rev_mp subsetI)

  have "path (quotG E) (p1 @ [u])"
    using quot_aug_path
    by (auto simp: path_pref)
  then have "set p1 \<subseteq> Vs (quotG E)"
    using quot
    using split_list_first tl_path_is_path
    by (metis path_pref subset_path_Vs)
  moreover have u_nin_p1: "u \<notin> set (rev p1)"
    using quot_aug_path
    by auto
  ultimately have p1_subset_s: "set (rev p1) \<subseteq> s"
    using quot good_quot_map
    by (metis (no_types,lifting) in_quotG_neq_u order_refl set_rev subset_code(1))

  show ?thesis
  proof(cases "p1 = []")
    case nil1: True
    show ?thesis
    proof(cases "p2 = []")
      case nil2: True
      then show ?thesis
        using p'_feats quot_aug_path(1)
        by (simp add: nil1)
    next
      case p2_nempty: False
      show ?thesis
        using nil1 p'_feats quot_aug_path
        using cycle(1-3) d1 p2_nempty p2_subset_s quot replace_cycle_def by auto
    qed
  next
    case p1_nempty: False
    show ?thesis
    proof(cases "p2 = []")
      case T2: True
      have rev_p1_nempty: "rev p1 \<noteq> []" using p1_nempty by simp
      show ?thesis
        by (smt T2 matching_augmenting_path_rev cycle(1-3) d1 hd_rev p1_nempty p1_subset_s quot quot_aug_path(1) quot_aug_path(2) replace_cycle_def rev_eq_Cons_iff rev_p1_nempty rev_rev_ident)
    next
      case p2_nempty: False
      show ?thesis
        apply(rule replace_cycle_cases)
        subgoal using p2_subset_s by auto
        subgoal using p2_nempty by auto
        subgoal using append_works p1_nempty p1_subset_s p2_nempty p2_subset_s quot_aug_path(1) quot_aug_path(2) by auto
        done         
    qed
  qed
qed

lemma length_replace_cycle_works:
  assumes cycle: "odd_cycle C" and
    quot_aug_path: "p' = (p1 @ u # p2)" "matching_augmenting_path (quotG M) p'"
  shows "2 \<le> length (replace_cycle C  M p1 p2)"
proof-
  have "p1 \<noteq> [] \<or> p2 \<noteq> []"
    using quot_aug_path(1,2)
    by(auto simp add: matching_augmenting_path_def split: if_splits)
  moreover have "C \<noteq> []"
    using odd_cycle_nempty[OF cycle(1)].
  ultimately show ?thesis
    using length_replace_cycle
    by (smt One_nat_def Suc_1 add_Suc_right add_leE dual_order.antisym le_zero_eq length_0_conv not_less_eq_eq)
qed

text\<open>Lifting a path in case it intersects with a contracted vertex\<close>

lemma replace_cycle_works:
  assumes cycle: "odd_cycle C" "alt_path M C" "distinct (tl C)"
                 "path E C" and
    quot_aug_path: "p' = (p1 @ u # p2)" "graph_augmenting_path (quotG E) (quotG M) p'" and 
    matching: "matching M" "M \<subseteq> E" and
    quot: "s = (Vs E) - set C"(*  and
    graph: "dblton_graph E"*)
  shows "matching_augmenting_path M (replace_cycle C M p1 p2) \<and> path E (replace_cycle C M p1 p2) \<and> distinct (replace_cycle C M p1 p2)"
  unfolding matching_augmenting_path_def
  by(intro conjI path_replace_cycle[OF assms]
  distinct_replace_cycle[OF assms]
  conjunct1[OF hd_nin_last_nin_replace_cycle[OF assms]]
  conjunct2[OF hd_nin_last_nin_replace_cycle[OF assms]]
  alt_list_replace_cycle[OF assms(1-3) assms(5-9)]  
  subset_path_Vs assms length_replace_cycle_works[OF _ quot_aug_path(1)]
  graph_augmenting_path_feats[OF quot_aug_path(2)])

text\<open>A function to find the shortest prefix of a list which has a given vertex.\<close>

fun pref_suf where
  "pref_suf pref v [] = (pref,[])" |
  "pref_suf pref v (a # l) = (if a = v then (pref, l) else pref_suf (pref @  [a]) v l)"

lemma pref_suf_append_1:
  assumes "v \<notin> set pref"
  shows "fst (pref_suf (pref1 @ pref2) v l) = pref1 @ fst (pref_suf pref2 v l)"
  using assms
proof(induction l arbitrary: pref2)
  case Nil
  then show ?case
    by auto
next
  case (Cons a' l')
  then show ?case 
    by auto
qed

lemma pref_suf_append_2:
  "snd (pref_suf pref1 v l) = snd (pref_suf pref2 v l)"
proof(induction l arbitrary: pref1 pref2)
  case Nil
  then show ?case
    by auto
next
  case (Cons a' l')
  then show ?case 
    by auto
qed

lemma pref_suf_works:
  assumes "v \<in> set l"
  shows "l = fst (pref_suf [] v l) @ v # snd (pref_suf [] v l)"
  using assms
proof(induction l)
  case Nil
  then show ?case
    by auto
next
  case (Cons a' l')
  show ?case
  proof(cases "v = a'")
    case True
    then show ?thesis
      by auto
  next
    case False
    then have "l' = fst (pref_suf [] v l') @ v # snd (pref_suf [] v l')"
      using Cons
      by auto
    moreover have "fst (pref_suf ([a'] @ []) v l') = [a'] @ fst (pref_suf [] v l')"
      apply(intro pref_suf_append_1[where pref = "[a']"])
      using False 
      by auto
    moreover have "snd (pref_suf [] v l') = snd (pref_suf l'' v l')" for l''
      using pref_suf_append_2
      by force
    ultimately show ?thesis
      by (metis False append_Cons append_Nil pref_suf.simps(2))
  qed
qed

text\<open>The function the refines an augmenting path from a quotient graph to a concrete one.\<close>

definition refine where
  "refine C M p =(
   if (u \<in> set p) then
     (replace_cycle C M (fst (pref_suf [] u p)) (snd (pref_suf [] u p)))
   else p)"

theorem refine:
  assumes cycle: "odd_cycle C" "alt_path M C" "distinct (tl C)" "path E C" and
    quot_aug_path: "graph_augmenting_path (quotG E) (quotG M) p'" and 
    matching: "matching M" "M \<subseteq> E" and
    quot: "s = (Vs E) - set C"(*  and
    graph: "dblton_graph G"*)
  shows "graph_augmenting_path E M (refine C M p')"
proof(cases "u \<in> set p'")
  define aug_path where "aug_path = (replace_cycle C M (fst (pref_suf [] u p')) (snd (pref_suf [] u p')))"
  case True
  then have "matching_augmenting_path M aug_path \<and> path E aug_path \<and> distinct aug_path"
    unfolding aug_path_def
    apply(intro replace_cycle_works[OF cycle _ quot_aug_path matching quot])
    using pref_suf_works .
  then show ?thesis
    using True
    unfolding refine_def aug_path_def
    by auto
next
  case False
  then have p_subset_s: "set p' \<subseteq> s"
    using quot(1) mem_path_Vs in_quotG_neq_u quot_aug_path
    by (metis (no_types, lifting) subsetI)
  then have "path E p'"
    using quot_aug_path
    using qug_path_iff_case_1_ii quot(1) by blast
  then show ?thesis
    using quot_aug_path qug_path_iff_case_1_i p_subset_s \<open>M \<subseteq> E\<close>
    by (metis (no_types,lifting) False refine_def)
qed

theorem refine_works:
  assumes cycle: "blossom E M stem C" and
    quot_aug_path: "graph_augmenting_path (quotG E) (quotG M) p'" and 
    matching: "matching M" "M \<subseteq> E" and
    quot: "s = (Vs E) - set C"
  shows "graph_augmenting_path E M (refine C M p')"
proof-

  have *: "tl C = butlast (tl C) @ [last C]"
    using odd_cycleD[OF match_blossomD(3)[OF blossomD(2)[OF cycle]]]
    by (fastforce simp add: eval_nat_numeral Suc_le_length_iff dest!:)

  have butlast_nempty_conv: "butlast xs = x # xs' \<longleftrightarrow> (\<exists>x'. xs = x # xs' @ [x'])" for x xs xs'
    by(cases xs) (auto simp add: snoc_eq_iff_butlast')

  have "distinct (tl (butlast C))"
    using match_blossomD[OF blossomD(2)[OF cycle]] match_blossom_alt_cycle[OF blossomD(2)[OF cycle]]
    by (auto simp add: \<open>alt_path M C\<close> distinct_tl dest!: blossomD odd_cycleD)
  moreover have "hd C \<notin> set (tl (butlast C))"
    using match_blossomD[OF blossomD(2)[OF cycle]]
    by(cases "(butlast C)") (auto simp add: butlast_nempty_conv)
  ultimately have "distinct (tl C)"
    using odd_cycleD(3)[OF match_blossomD(3)[OF blossomD(2)[OF cycle]]]
    apply(subst *)
    by (simp add: butlast_tl)
  moreover have "path E C"
    using cycle path_suff'
    by auto
  ultimately show ?thesis
    apply -
    apply(rule refine[OF _ _ _ _ assms(2-)])
    using match_blossomD[OF blossomD(2)[OF cycle]] match_blossom_alt_cycle[OF blossomD(2)[OF cycle]]
    by auto
qed

end

subsection\<open>Quotienting/conracting an augmenting path\<close>

text\<open>We prove an augmenting path in a concrete graph can be abstracted into an augmenting path in a
     quotient graph\<close>

lemma in_odd_cycle_in_M:
  assumes "v \<in> set C" "odd_cycle C" "alt_path M C" "v \<noteq> last C"
  shows "v \<in>  Vs M"
  using assms(1,4)
  using alt_path_vert_is_matched' odd_cycleD(2,3)[OF assms(2)] assms(3) by fastforce

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
    by (metis edges_of_path.simps(3) list.exhaust_sel)
  moreover have "edges_of_path C = (edges_of_path (p1 @ [v1])) @ (edges_of_path (v1 # p2))"
    using edges_of_path_append_2[where p' = "v1 # p2"] p1p2(1)
    by auto
  ultimately have "edges_of_path C = (edges_of_path p1) @ {last p1, v1} # {v1, hd p2} # edges_of_path p2"
    using p1p2(1)
    by auto
  then have i: "{last p1, v1} \<in> M \<or> {v1, hd p2} \<in> M"
    using odd_cycleD(2)[OF assms(1)] assms(2)
    by (metis alt_list_append_1'')
  have "last p1 \<in> set C" "hd p2 \<in> set C"
    using p1p2 by auto
  then have ii: "{last p1, v1} \<noteq> e" "{v1, hd p2} \<noteq> e"
    using assms(4-6)
    by fastforce+

  show False
    using i ii assms(4-7)
    unfolding matching_def2 Vs_def
    by (metis UnionI assms(3) insertI1 insert_commute insert_subset)
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
  using assms good_quot_map
  apply(simp add: image_def quot_graph_def)
  by (smt (verit, best) Collect_cong Int_insert_left_if0 Un_Int_eq(3) insertCI insert_commute 
                        insert_def mk_disjoint_insert singleton_conv)

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
      using last_in_set that by blast
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
      by (meson contra_subsetD in_set_butlastD last_in_set)
    have "{last p1, u} \<in> quotG E"
    proof-
      have "last p1 \<in> Vs E"
        using last_p1_in_s quot(1) by blast
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
        have "p = (p1 @ [w]) @ p2" using wx(1)
          by auto
        then have "path E (butlast p1 @ (last p1 # w # []))"
          using aug_path path_pref *
          by metis
        then show ?thesis
          using path_adj_verts_edge
          by metis
      qed
      ultimately show ?thesis 
        apply(intro edge_in_graph_edge_in_quot[OF last_p1_in_s])
        by auto
    qed
    moreover have path_p1: "path E p1"
      using aug_path path_pref wx p1_subset_s
      by auto
    then have path_p1: "path (quotG E) p1"
      using p1_subset_s qug_path_iff_case_1_ii quot(1) by blast
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
      using p3_subset_s qug_path_iff_case_1_ii quot(1) by blast
    moreover have "{hd p3, u} \<in> quotG E"
    proof-
      have "hd p3 \<in> Vs E"
        using p3_nempty p3_subset_s quot(1)
        using hd_in_set by blast
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
        apply(intro edge_in_graph_edge_in_quot[where w = x])
        by (auto simp add: insert_commute)
    qed
    ultimately show "path (quotG E) (u # p3)"
      using p3_nempty
      by(cases p3; auto simp add: insert_commute)
  qed 

  have "set p \<subseteq> Vs E"
    using aug_path(2)
    by (simp add: subset_path_Vs)
  then have u_nin_p: "u \<notin> set p"
    using quot by auto

  have "u \<notin> Vs E"
    using quot by auto
  then have u_nin_VsM: "u \<notin> Vs M"
    using matching(2) by (auto simp add: Vs_def)

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
          by (metis IntI distinct_append empty_iff last_in_set list.distinct(1) list.sel(3) list.set_sel(1) list.set_sel(2))
        then show ?thesis
          by (auto simp add: doubleton_eq_iff)
      qed
      then have hdp3_x_nin_M: "{x, hd p3} \<notin> M"
        using matching(1)
        unfolding Vs_def matching_def2
        by (metis alt_list_p1_u insert_commute last_rev p3_nempty p3_subset_s rev_is_Nil_conv set_rev wx(2))
      have "edges_of_path p = edges_of_path (p1  @ [x])@ edges_of_path (x # p3)"
        unfolding wx(1)
        using edges_of_path_append_2[where p' = "x # p3"]
        by (metis list.distinct(1) list.sel(1))
      then have "alt_path M (x # p3) \<or> 
                alt_list (\<lambda>e. e \<in> M) (\<lambda>e. e \<notin> M) (edges_of_path (x # p3))"
        apply(intro conjunct2[OF alt_list_append_1] )
        using matching_augmenting_path_feats(2)[OF aug_path(1)]
        by auto
      then have *: "alt_path M (x # p3)"
        using hdp3_x_nin_M
        by(cases p3; auto simp: alt_list_step)
      then have "alt_list (\<lambda>e. e \<in> M) (\<lambda>e. e \<notin> M) (edges_of_path p3)"
        by(cases p3; auto simp: alt_list_step)
      then have "alt_list (\<lambda>e. e \<in> quotG M) (\<lambda>e. e \<notin> quotG M) (edges_of_path p3)"
        apply(rule alt_list_cong[OF ])
        using edge_of_path_in_graph_iff_in_quot[OF p3_subset_s] \<open>M \<subseteq> E\<close>
        by blast+
      moreover have "{u, hd p3} \<notin> quotG M"
      proof(rule ccontr)
        have hd_p3_in_s: "hd p3 \<in> s"
          using p3_nempty p3_subset_s
          by (meson contra_subsetD in_set_butlastD hd_in_set)
        assume "\<not> {u, hd p3} \<notin> quotG M"
        then have "{u, hd p3} \<in> quotG M" by simp
        then have "\<exists>v. {v, hd p3} \<in> M \<and> v \<notin> s"
          using hd_p3_in_s edge_in_quotG_2'_doubleton graph matching(2)
          by (smt dblton_graphE Diff_eq_empty_iff Diff_iff empty_iff insert_commute)
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
      apply(intro split_list_pure_pref_suff)
      using aug_path(3)
      by auto
    then obtain p1 p2 where p1p2x[simp]: "p = p1 @ x # p2" "x \<in> set C" "\<forall>x\<in>set p1. x \<notin> set C" "\<forall>x\<in>set p2. x \<notin> set C"
      using x by auto
    have p1_subset_s[simp]: "set p1 \<subseteq> s"
    proof-
      have "path E p1"
        using p1p2x(1) aug_path(2) path_pref
        by metis
      then show ?thesis
        using quot p1p2x(3)
        using mem_path_Vs by fastforce
    qed
    have p2_subset_s[simp]: "set p2 \<subseteq> s"
    proof-
      have "path E p2"
        using p1p2x(1) aug_path(2) path_suff
        by (metis list.sel(3) tl_path_is_path)
      then show ?thesis
        using quot p1p2x(4)
        using mem_path_Vs by fastforce
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
          using p1p2x(1) matching_augmenting_path_feats(4)[OF aug_path(1)] p2_nempty
            \<open>M \<subseteq> E\<close>
          by (metis (no_types,lifting) last_ConsR last_in_set p1_empty p2_subset_s self_append_conv2 
              subsetCE vert_in_graph_iff_in_quot_diff_u)
        moreover have "hd (u # p2) \<notin> Vs (quotG M)"
          apply simp
          by(rule not_in_quot_matching_not_in_matching_2[OF matching(1,2) cycle quot(1) aug_path(5)])
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
          apply(intro alt_list_u_p3[of "rev p" "rev p2" x] matching_augmenting_path_rev[OF aug_path(1)] aug_path(5))
          using aug_path(3) distinct_rev by auto
        moreover have "path (quotG E) (u # (rev p1))"
          apply(intro path_u_p3[of "rev p" "rev p2" x] rev_path_is_path[OF aug_path(2)])
          by simp+
        moreover have "distinct (u # (rev p1))"
          using p1p2x(1) u_nin_p aug_path(3)
          by auto
        moreover have "hd (u # (rev p1)) \<notin> Vs (quotG M)"
          apply simp
          by(rule not_in_quot_matching_not_in_matching_2[OF matching(1,2) cycle quot(1) aug_path(5)])
        moreover have "last (u # (rev p1)) \<notin> Vs (quotG M)"
          using p1p2x(1) matching_augmenting_path_feats(3)[OF aug_path(1)] p1_nempty
            \<open>M \<subseteq> E\<close>
          by (metis (no_types,lifting) hd_append2 hd_in_set last.simps last_rev p1_subset_s 
              rev_is_Nil_conv set_rev_mp vert_in_graph_iff_in_quot_diff_u)
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
              using edges_of_path_append_2 p1p2x(1) by fastforce
            have rw2: "(edges_of_path (p1 @ [x])) = (edges_of_path p1) @ [{last p1, x}]"
              using p1_nempty
              by (simp add: edges_of_path_snoc)
            have rw3: "(edges_of_path (x # p2)) =  {hd p2, x} # (edges_of_path p2)"
              using p2_nempty
              by (auto simp add: neq_Nil_conv simp del: p2_nempty)
            show ?thesis
              using matching_augmenting_path_feats(2)[OF aug_path(1), unfolded rw1 rw2 rw3]
              by (metis (no_types, lifting) alt_list_append_1' alt_list_step append_is_Nil_conv last_snoc list.simps(3) p1_x_nin_M)
          qed
          have False
            apply(rule alt_list_p1_u[of "rev p2" "rev p" x "rev p1"])
            using hdp2_x_in_M by (simp add: last_rev)+
          then show ?thesis
            by metis
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
        by metis
      then show ?thesis
        using quot wx(5)
        using mem_path_Vs by fastforce
    qed
    have p3_subset_s: "set p3 \<subseteq> s"
    proof-
      have "path E p3"
        using wx(1) aug_path(2) path_suff
        by (metis list.sel(3) tl_path_is_path)
      then show ?thesis
        using quot wx(6)
        using mem_path_Vs by fastforce
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
        using edges_of_path_append_2[where p' = "x # p3"]
        by (metis append_Cons append_assoc list.distinct(1) list.sel(1))
      then have "alt_path M (x # p3) \<or> 
                alt_list (\<lambda>e. e \<in> M) (\<lambda>e. e \<notin> M) (edges_of_path (x # p3))"
        apply(intro conjunct2[OF alt_list_append_1] )
        using matching_augmenting_path_feats(2)[OF aug_path(1)]
        by auto
      hence *: "alt_path M (x # p3)"
        using \<open>{x, hd p3} \<notin> M\<close>
        by(cases p3; auto simp: alt_list_step alt_list_empty)
      hence "alt_list (\<lambda>e. e \<in> M) (\<lambda>e. e \<notin> M) (edges_of_path p3)"
        using p3_nempty
        by(cases p3; auto simp: alt_list_step)
      then have "alt_list (\<lambda>e. e \<in> quotG M) (\<lambda>e. e \<notin> quotG M) (edges_of_path p3)"
        apply(rule alt_list_cong[OF ])
        using edge_of_path_in_graph_iff_in_quot[OF p3_subset_s] \<open>M \<subseteq> E\<close> 
        by blast+
      moreover have "{u, hd p3} \<notin> quotG M"
      proof(rule ccontr)
        have hd_p3_in_s: "hd p3 \<in> s"
          using p3_nempty p3_subset_s
          by (meson contra_subsetD in_set_butlastD hd_in_set)
        assume "\<not> {u, hd p3} \<notin> quotG M"
        then have "{u, hd p3} \<in> quotG M" by simp
        then have "\<exists>v. {v, hd p3} \<in> M \<and> v \<notin> s"
          using hd_p3_in_s edge_in_quotG_2'_doubleton graph matching(2)
          by (smt dblton_graphE Diff_eq_empty_iff Diff_iff empty_iff insert_commute)
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
        then show False
          using w_nin_M wx(2,3,4) in_odd_cycle_in_M[OF _ cycle]
          by metis
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
        apply simp
        by(rule not_in_quot_matching_not_in_matching_2[OF matching(1,2) cycle quot(1) aug_path(5)])
      moreover have "last (u # p3) \<notin> Vs (quotG M)"
        using wx(1) matching_augmenting_path_feats(4)[OF aug_path(1)] p3_nempty
          \<open>M \<subseteq> E\<close>
        by (metis (no_types, lifting) append_is_Nil_conv calculation(2) calculation(4) last_ConsR
            last_appendR last_in_set list.discI list.sel(1) mem_path_Vs neq_u_notin_quotG
            vert_in_graph_iff_in_quot_diff_u)
      moreover have "length (u # p3) \<ge> 2"
        using p3_nempty
        by (auto simp add: neq_Nil_conv)
      ultimately show ?thesis
        unfolding matching_augmenting_path_def
        by blast
    next
      case p1_nempty[simp]: False
      then have rev_p1_nempty: "rev p1 \<noteq> []" by auto
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
          apply(intro alt_list_u_p3[of "rev p" "rev p3" x "rev p2" w] matching_augmenting_path_rev[OF aug_path(1)] aug_path(5))
          using F4 by (simp add: insert_commute hd_rev)+
        moreover have "path (quotG E) (u # (rev p1))"
          apply(intro path_u_p3[of "rev p" "rev (p2 @ x # p3)" w] rev_path_is_path[OF aug_path(2)])
          by auto
        moreover have "distinct (u # (rev p1))"
          using u_nin_p aug_path(3)
          by auto
        moreover have "hd (u # (rev p1)) \<notin> Vs (quotG M)"
          apply simp
          by(rule not_in_quot_matching_not_in_matching_2[OF matching(1,2) cycle quot(1) aug_path(5)])
        moreover have "last (u # (rev p1)) \<notin> Vs (quotG M)"
          using wx(1) matching_augmenting_path_feats(3)[OF aug_path(1)] p1_nempty \<open>M \<subseteq> E\<close>
          by (metis (no_types,lifting) hd_append2 last_ConsR last_rev list.set_sel(1) p1_subset_s
              rev_p1_nempty subsetCE vert_in_graph_iff_in_quot_diff_u)
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
    using assms edge_in_quot_in_graph_1' by auto
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
    by (metis (no_types,lifting))
  show False
  proof(cases "v \<in> s")
    text\<open>if v in s, then due to the way the quot mapping works, and since qe, qe' in quotG M,
      we will have two different matched edges in M that both include M. This leads to a
      contradiction.\<close>
    case True
    then obtain e e' where e: "v \<in> e" "v \<in> e'" "e \<in> M" "e' \<in> M" "e \<noteq> e'"
      using qe qe' quot_edge_inter_s[OF qe(2) \<open>M\<subseteq>E\<close>] quot_edge_inter_s[OF qe'(3) \<open>M\<subseteq> E\<close>]
            edge_in_quot_in_graph_1'[OF _ _ \<open>M \<subseteq> E\<close>] edge_in_quot_in_graph_2'' u_nin_edge_in_quot
      by (smt (verit, best) DiffD1 Int_iff assms(3) subset_iff)
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
    then have "v = u"
      using in_quotG_neq_u v(1) \<open>M \<subseteq> E\<close> by blast
    moreover obtain w x where wx: "w \<noteq> x" "w \<in> qe" "w \<noteq> u" "w \<in> s" "x \<in> qe'" "x \<noteq> u" "x \<in> s"
      using qe qe'
      unfolding quot_graph_def image_def
      by (auto; metis (no_types, lifting) calculation good_quot_map(1))
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
  then show ?case by (auto simp add: quot_graph_def)
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
      by (simp add: image_def set_eq_iff; metis)
    then have "(quotG (insert e E')) =  insert (P ` e) (quotG E')"
      by (auto simp add: quot_graph_def)
    moreover have "P ` e \<notin> (quotG E')"
    proof(cases "\<exists>v\<in>e. v \<notin> s")
      case True
      moreover have "\<exists>v\<in>s. v\<in>e"
        using False by blast
      ultimately have "e = dume"
        using insert(5)
        by auto
      moreover have "\<forall>e'\<in>E'. e \<noteq> e'"
        using insert(2)
        by auto
      ultimately have "\<forall>e'\<in>E'. (\<forall>v\<in>e'. v \<in> s) \<or> (\<forall>v\<in>e'. v \<notin> s)"
        using insert(5)
        by blast
      then have "\<forall>e'\<in>E'. P ` e \<noteq> P ` e'"
        using True False good_quot_map insert(2)
        by (auto simp add: image_def set_eq_iff; metis)
      then show ?thesis
        unfolding quot_graph_def
        by auto
    next
      case F2: False
      moreover have "\<forall>e'\<in>E'. e \<noteq> e'"
        using insert(2)
        by auto
      ultimately have "\<forall>e'\<in>E'. P ` e \<noteq> P ` e'"
        using good_quot_map insert(2)
        by (simp add: image_def set_eq_iff; metis)
      then show ?thesis
        unfolding quot_graph_def
        by auto
    qed
    ultimately have " card (quotG (insert e E')) =  card (quotG E') + 1"
      using finite_quot[OF insert(1)]
      using \<open>P ` e \<notin> quotG E'\<close> by auto
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
            apply simp
            by (metis (full_types) insertI1 insert_commute)
        qed
        have "matching ((M - {{a'', a'''}}) \<oplus> set (edges_of_path (a''' # p''')))"
          apply (intro less)
          subgoal by(simp)
          subgoal proof-
            have *: "alt_path M p''"
              using less 
              by (auto simp add: alt_list_step)
            show ?thesis
              apply(rule alt_list_cong[OF *[simplified]])
              using distinct_edges
              by (auto simp add: alt_list_step)
          qed
          subgoal using less
            apply (simp add: alt_list_step matching_def2 Vs_def)
            by (metis DiffD1 DiffD2 singleton_iff)
          subgoal using a'''nin by simp
          subgoal proof-
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
                apply(simp add: doubleton_eq_iff)
                using v_in_edge_in_path_gen last_in_set
                by force
            qed
            then show ?thesis
              using a'''nin less.prems(4) by (cases p'''; simp split: if_splits)
          qed
          subgoal using less.prems(5) by (simp)
          done
        moreover have "(M \<oplus> set (edges_of_path p)) - {{a', a''}} =  (M - {{a'', a'''}} \<oplus> set (edges_of_path (a''' # p''')))"
          apply(intro equalityI subsetI)
          subgoal using less.prems(1)
            apply (simp add: alt_list_step alt_list_empty symmetric_diff_def)
            by blast
          subgoal using less.prems(1,5)
            apply (simp add: alt_list_step alt_list_empty symmetric_diff_def)
            using v_in_edge_in_path by fastforce
          done
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
              using e a''a'''_in_both by auto
          next
            case False
            moreover have False if "e \<in> M"
              using less.prems(2) False e(2) that a''a'''_in_both(1)
              apply (simp add: matching_def2 Vs_def)
              by (metis insertI1)
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
          using matching_insert
          by (metis Diff_disjoint Diff_insert_absorb insert_disjoint(1))
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
      using card3_subset not_less_eq_eq by force
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
      then have False
        using \<open>dblton_graph M\<close> \<open>M\<subseteq>E\<close> 1 good_quot_map dblton_E
        apply(simp add: image_def)
        by (metis (no_types, lifting) "1" Undirected_Set_Graphs.dblton_graphE \<open>dblton_graph M\<close> 
                  doubleton_eq_iff edge_in_quot_in_graph_1' qtuoe_eq_v singleton_iff 
                  singleton_insert_inj_eq' u_nin_edge_in_quot)+

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
        by (metis Suc_1 card_1_singletonE card_eq_SucD singletonI)
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
        by (metis alt_list_append_1 match_blossomD(1,3)[OF \<open>match_blossom M stem C\<close>] edges_of_path_append_2 odd_cycle_nempty)
      have distinct_stem_hdC: "distinct (stem @ [hd C])"
      proof-
        have "butlast C = hd C # tl (butlast C)"
          using odd_cycleD(1)
          by (metis One_nat_def append_butlast_last_id match_blossomD(3)[OF \<open>match_blossom M stem C\<close>] hd_append2
                    length_append_singleton list.exhaust_sel list.size(3) numeral_le_one_iff
                    odd_cycle_nempty semiring_norm(70))
        then show ?thesis
          using match_blossomD(2)[OF \<open>match_blossom M stem C\<close>]
          by (metis append_Nil2 disjoint_insert(1) distinct_append distinct_singleton list.simps(15))
      qed
      have path_stem_hdC: "path E (stem @ [hd C])"
        using match_blossom(1) odd_cycle_nempty[OF match_blossomD(3)[OF \<open>match_blossom M stem C\<close>]]
        by (metis append_Cons append_Nil append_assoc list.collapse path_pref)
      have stem_hdC_nempty: "edges_of_path (stem @ [hd C]) \<noteq> []"
        using stem_nempty
        by (metis edges_of_path_snoc snoc_eq_iff_butlast)
      have "(edges_of_path (stem @ C)) = (edges_of_path (stem @ [hd C])) @ (edges_of_path (C))"
        using odd_cycle_nempty[OF match_blossomD(3)[OF \<open>match_blossom M stem C\<close>]]
        using edges_of_path_append_2 by blast
      then have "alt_path M (stem @ [hd C])"
        using match_blossomD(1)[OF \<open>match_blossom M stem C\<close>] alt_list_append_1
        by auto
      then have last_stem_hdC: "last (edges_of_path (stem @ [hd C])) \<in> M"
        using match_blossomD(5)[OF \<open>match_blossom M stem C\<close>] stem_hdC_nempty
              alternating_list_even_last
        by auto
      have M'_matching: "matching M'"
        unfolding M'_def
        apply(intro symm_diff_is_matching' distinct_stem_hdC)
        subgoal using alt_list_stem_hdC by auto
        subgoal using matching(1) by auto
        subgoal using match_blossomD(4)[OF \<open>match_blossom M stem C\<close>] by (simp add: stem_nempty)
        subgoal proof-
          have "last (edges_of_path (stem @ [hd C])) \<in> M"
            apply(rule alternating_list_even_last[where ?P1.0 = "(\<lambda>e. e \<notin> M)", OF _ _ stem_hdC_nempty])
            subgoal using alt_list_stem_hdC .
            subgoal using match_blossomD(5)[OF \<open>match_blossom M stem C\<close>] .
            done
          then show ?thesis by auto
        qed
        done
      moreover have cardM'_eq_cardM: "card M' = card M"
        unfolding M'_def
        by(intro card_symm_diff_matching matching(3) match_blossomD[OF \<open>match_blossom M stem C\<close>] alt_list_stem_hdC distinct_stem_hdC)
      moreover obtain M_large where "matching M_large" "card M_large > card M" "M_large \<subseteq> E"
        using Berge_2[OF graph_augmenting_path_feats(1)[OF aug_path] matching(2) graph_augmenting_path_feats(3,2)[OF aug_path] matching(3,1)]
        by auto
      moreover have M'_subset_G: "M' \<subseteq> E"
        unfolding M'_def
        using matching(2)
        using path_edges_subset sym_diff_subset path_stem_hdC
        by (metis le_supI order.trans)
      ultimately obtain p_M' where "matching_augmenting_path M' p_M'" "path E p_M'" "distinct p_M'"
        using Berge[OF M'_finite] graph
        by metis

      moreover have lastC_nin_M': "last C \<notin> Vs M'"
      proof-
        have "last (edges_of_path (stem @ [hd C])) \<notin> M'"
          unfolding M'_def symmetric_diff_def
          using match_blossomD(5)[OF \<open>match_blossom M stem C\<close>] alternating_list_even_last
                last_in_set last_stem_hdC \<open>edges_of_path (stem @ [hd C]) \<noteq> []\<close>
          by blast
        text\<open>The rest of the proof depends on the fact that hd C should be in any matched edge in M,
           other that {last stem, hd C}, and thus it is unmatched in M'.\<close>
        moreover have "\<forall>e\<in>set(edges_of_path (stem @ [hd C])). hd C \<in> e \<longrightarrow> e = last (edges_of_path (stem @ [hd C]))"
          using mem_eq_last_edge[OF distinct_stem_hdC]
          by simp
        moreover have "\<forall>e\<in>M. e \<noteq> last (edges_of_path (stem @ [hd C])) \<longrightarrow> hd C \<notin> e"
        proof-
          have "hd C \<in> last (edges_of_path (stem @ [hd C]))"
            using stem_nempty
            by (metis edges_of_path_snoc insert_iff last_snoc)
          then show ?thesis
            using matching(1)
            by (metis \<open>last (edges_of_path (stem @ [hd C])) \<in> M\<close> \<open>last C \<in> Vs M\<close> match_blossomD(3)[OF \<open>match_blossom M stem C\<close>] match_blossom_alt_cycle[OF \<open>match_blossom M stem C\<close>] matching_def2 odd_cycleD(3))
        qed
        ultimately have "\<forall>e\<in>M'. hd C \<notin> e"
          unfolding M'_def
          by (metis in_symm_diff_eq_2)
        then show ?thesis
          unfolding Vs_def
          using odd_cycleD(3)[OF match_blossomD(3)[OF \<open>match_blossom M stem C\<close>]]
          by auto
      qed
      moreover have "alt_path M' C"
        unfolding M'_def
        apply(rule alt_path_in_symm_diff)
        subgoal using match_blossom_alt_cycle[OF \<open>match_blossom M stem C\<close>] .
        subgoal proof-
          have *: "(edges_of_path (stem @ [hd C])) = (edges_of_path (stem)) @ [{last stem, hd C}]"
            using stem_nempty
            by (simp add: edges_of_path_snoc)
          have "last stem \<notin> set C"
            using match_blossomD(2)[OF \<open>match_blossom M stem C\<close>] stem_nempty
            by (smt Un_iff append_butlast_last_id match_blossomD(3)[OF \<open>match_blossom M stem C\<close>] disjoint_insert(1) distinct_append distinct_stem_hdC insert_Diff last_in_set odd_cycleD(3) odd_cycle_nempty set_append)
          then have "{last stem, hd C} \<notin> set (edges_of_path C)"
            by (meson v_in_edge_in_path)
          moreover have "set C \<inter> set stem = {}"
            using match_blossomD(2)[OF \<open>match_blossom M stem C\<close>] odd_cycleD(3)[OF match_blossomD(3)[OF \<open>match_blossom M stem C\<close>]]
            by (smt Un_iff append_butlast_last_id disjoint_iff_not_equal distinct_append distinct_stem_hdC empty_iff empty_set set_append)
          ultimately show ?thesis
            unfolding *
            apply simp
            by(rule edges_of_path_disj; simp)
        qed
        done
      ultimately obtain p'_quotM' where p'_M': "alt_path (quotG M') p'_quotM'" 
        "path (quotG E) p'_quotM'"
        "distinct p'_quotM'"
        "hd p'_quotM' \<notin> Vs (quotG M')"
        "last p'_quotM' \<notin> Vs (quotG M')"
        "length p'_quotM' \<ge> 2"
        using match_blossomD(3)[OF \<open>match_blossom M stem C\<close>] M'_subset_G M'_matching graph has_s_verts aug_path_works_in_contraction_unmatched_base'[OF _ _ _ _ _ _ _ _ quot(1,2)]
        apply (simp add: matching_augmenting_path_def)
        by meson
               
      then have "matching_augmenting_path (quotG M') p'_quotM'" 
        "path (quotG E) p'_quotM'"
        "distinct p'_quotM'"
        unfolding matching_augmenting_path_def
        by auto
      moreover have "finite (quotG M')"
        unfolding M'_def
        by(rule finite_quot finite_symm_diff matching(3) finite_set)+
      moreover have "matching (quotG M')"
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
          apply(intro quot_is_matching M'_matching)
          using M'_subset_G
          by blast+
      qed
      moreover have "quotG M' \<subseteq> quotG E"
        using graph_subset_quot_subset M'_subset_G
        by auto
      ultimately obtain quotM'_large where quotM'_large: "matching quotM'_large" "card quotM'_large > card (quotG M')" "quotM'_large \<subseteq> quotG E"
        using Berge_2
        by (metis (no_types, lifting))
      have finite_quotG_M: "finite (quotG M)"
        using finite_quot matching(3) by blast
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
            using matching(2) Vs_subset by blast
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
            by (metis edges_of_path_snoc last_snoc)
          ultimately show ?p2
            using that(1,2,4) matching(1)
            unfolding matching_def2 Vs_def
            apply auto
            by (metis \<open>v \<in> set C\<close> \<open>w \<notin> set C\<close> insert_iff singletonD)
        qed
        then show ?thesis
          apply(intro quot_is_matching[where dume = "{last stem, last C}"] matching(1,2))
          by (auto simp add: doubleton_eq_iff; metis)
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
          apply (intro card_quot_matching M'_finite M'_subset_G)
          by blast+
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
            using matching(2) Vs_subset by blast
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
            by (metis edges_of_path_snoc last_snoc)
          ultimately show ?p2
            using that(1,2,4) matching(1)
            unfolding matching_def2 Vs_def
            apply auto
            by (metis \<open>v \<in> set C\<close> \<open>w \<notin> set C\<close> insert_iff singletonD)
        qed
        moreover have "\<forall>e\<in>M. e \<noteq> {}"
          using matching(2) graph(1)
          by (auto elim: dblton_graphE)
        ultimately have "card (quotG M) = card M - card {e \<in> M. e \<inter> s = {}}"
          apply (intro card_quot_matching[where dume = "{last stem, last C}"] matching)
          by blast+
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
                using match_blossom(1) path_pref by blast
              moreover have "set C \<inter> set stem = {}"
                using match_blossomD(2)[OF \<open>match_blossom M stem C\<close>] odd_cycleD(3)[OF match_blossomD(3)[OF \<open>match_blossom M stem C\<close>]]
                by (smt Un_iff append_butlast_last_id disjoint_iff_not_equal distinct_append distinct_stem_hdC empty_iff empty_set set_append)
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
            using in_symm_diff_eq_2
            by (metis (mono_tags, lifting) disjoint_iff_not_equal mem_Collect_eq)
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
    using qug_path_iff_case_1_ii quot(1) by blast
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
  moreover have "card (Vs E \<inter> s) < card (Vs E) - 1"
    using assms
    by (simp add: card_Diff_subset_Int)
  ultimately show ?thesis
    by (smt (verit, ccfv_SIG) Diff_insert_absorb Suc_leI assms(1) card.insert card_Diff_singleton
                              diff_le_self finite_Int insert_absorb leD order.trans order_less_le)
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
        using matching(2) Vs_subset by blast
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
          using matching(1) match_blossom_alt_cycle[OF match_blossom] match_blossomD[OF match_blossom] \<open>v \<in> set C\<close> matching_edge_incident_on_cycle quot(1) that(1) that(2) that(3) that(4) by fastforce
      qed
    qed
    then show ?thesis
      apply(intro quot_is_matching matching(1) matching(2))
      by blast
  qed
next
  case stem_nempty: False
  have "v = last C" (is ?p1) "w = last stem" (is ?p2) if "e \<in> M" "v \<in> e" "w \<in> s" "w \<in> e" "v \<notin> s" for w v e
  proof-
    have stem_hdC_nempty: "edges_of_path (stem @ [hd C]) \<noteq> []"
      by (metis edges_of_path_snoc snoc_eq_iff_butlast stem_nempty)
    have "(edges_of_path (stem @ C)) = (edges_of_path (stem @ [hd C])) @ (edges_of_path (C))"
      using odd_cycle_nempty[OF match_blossomD(3)[OF match_blossom]]
      using edges_of_path_append_2 by blast
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
      using matching(2) Vs_subset by blast
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
      by (metis edges_of_path_snoc last_snoc)
    ultimately show ?p2
      using that(1,2,4) matching(1)
      apply (simp add: matching_def2 Vs_def)
      by (metis \<open>v \<in> set C\<close> \<open>w \<notin> set C\<close> insert_iff singletonD)
  qed
  then show ?thesis
    apply(intro quot_is_matching[where dume = "{last stem, last C}"] matching(1,2))
    by (auto simp add: doubleton_eq_iff; metis)
qed


end

end
