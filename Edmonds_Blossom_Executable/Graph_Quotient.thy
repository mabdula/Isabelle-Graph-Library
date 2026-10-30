(*
  Author: Mohammad Abdulaziz
  Author: Thomas Ammer
*)

theory Graph_Quotient
  imports Blossom_Facts
begin

provenance human

subsection \<open>Quotient graph\<close>

definition quot_graph where
  "quot_graph P G = {e'. \<exists>e\<in>G. e' = P ` e}"

lemma quot_graph_gen_comp:
   "quot_graph P2 (quot_graph P1 G) = quot_graph (P2 o P1) G"
  by(auto simp add: quot_graph_def)

lemma quot_id: "quot_graph (image id) G = G"  "quot_graph id G = G"
  by(auto simp add: quot_graph_def)

lemma quot_graph_cong:
  "(\<And> e. e \<in> G \<Longrightarrow> P `e = P' ` e) \<Longrightarrow> quot_graph P G = quot_graph P' G"
  by(auto simp add: quot_graph_def)

lemma dblton_graph_contract_into_one_vert:
  assumes "dblton_graph G"
     and contr_def: "contr = (\<lambda> x. if x \<in> S then new_vert else x)"
    shows "dblton_graph (quot_graph contr G - {{new_vert}})"
proof(rule dblton_graphI, goal_cases)
  case (1 e)
  then obtain e' where e': "e'\<in>G" "e = contr ` e'" "e \<noteq> {new_vert}"
    by (auto simp add: quot_graph_def)
  then obtain u v where uv: "e' = {u, v}" "u \<noteq> v"
    using assms(1) by(auto elim!: dblton_graphE)
  have "e = {contr u, contr v}"
    using uv e' by auto
  moreover have "contr u \<noteq> contr v"
    using uv e' by(auto simp add: contr_def)
  ultimately show ?case
    by auto
qed

lemma quot_graph_subset:
  "G \<subseteq> G' \<Longrightarrow> quot_graph contr G \<subseteq> quot_graph contr G'"
  by(auto simp add: quot_graph_def)

lemma quot_graph_comp:
  assumes contr1_def: "contr1 = (\<lambda> x. if x \<in> S then new_vert' else x)"
      and contr2_def: "contr2 = (\<lambda> x. if x \<in> insert new_vert' T then new_vert else x)"
      and contr_def: "contr = (\<lambda> x. if x \<in> S \<union> insert new_vert' T then new_vert else x)"
  shows"quot_graph contr2 (quot_graph contr1 G - {{new_vert'}}) - {{new_vert}}
      = quot_graph contr G - {{new_vert}}"
proof-
  have contrs_comp: "contr = contr2 o contr1"
    by(auto intro!: ext simp add: contr_def contr1_def contr2_def)
  show ?thesis
    unfolding quot_graph_def
  proof ((rule subset_antisym; rule subsetI), goal_cases)
    case (1 e)
    then obtain e' e'' where es:
      "e''\<in>G" "e' = contr1 ` e''" "e = contr2 ` e'" "e \<noteq> {new_vert}"
      "e' \<noteq>  {new_vert'}"
      by fastforce
    have e_contr:"e = contr ` e''"
      using contrs_comp es(2,3) by auto
    show ?case
      using e_contr es(3,4,5)
      by (auto intro!: bexI[OF _ es(1)] simp add: contr2_def)
  next
    case (2 e)
    then obtain e' where e': "e'\<in>G" "e = contr ` e'" "e \<noteq> {new_vert}"
      by auto
    show ?case
    proof(rule, goal_cases)
      case 1
      show ?case
      proof(rule, rule bexI[of _ "contr1 ` e'"], goal_cases)
        case 1
        then show ?case
          using contrs_comp e'(2) by auto
      next
        case 2
        have "contr1 ` e' \<noteq> {new_vert}"  "contr1 ` e' \<noteq> {new_vert'}"
          using e'(2,3) by(auto simp add: contr_def contr1_def)
        then show ?case
          using e'(1)
          by (auto intro!: bexI[of _ e'])
      qed
    next
      case 2
      then show ?case
        using e'(3) by simp
    qed
  qed
qed

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
  obtain e' where e': "e' \<in> E" "P ` e = P ` e'"
    using edge(1)
    unfolding quot_graph_def
    by auto
  have Pe: "P ` e = e"
    using edge(2)
    by (auto simp: subset_iff)
  have "e' \<subseteq> s"
  proof
    fix x
    assume "x \<in> e'"
    then have "P x \<in> P ` e"
      using e'(2)
      by blast
    then have "P x \<in> e"
      by (simp only: Pe)
    then have "P x \<in> s"
      using edge(2)
      by blast
    then show "x \<in> s"
      using good_quot_map(1)
      by (auto split: if_splits)
  qed
  then have "P ` e' = e'"
    by (auto simp: subset_iff)
  then show ?thesis
    using e' Pe
    by simp
qed

lemma edge_in_quot_in_graph_1':
  assumes edge: "e \<in> (quot_graph P M)" "e \<subseteq> s" "M \<subseteq> E"
  shows "e \<in> M"
proof \<^marker>\<open>provenance ai\<close>-
  obtain e' where e': "e' \<in> M" "e = P ` e'"
    using edge(1)
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
      by (auto split: if_splits)
  qed
  then have "P ` e' = e'"
    by (auto simp: subset_iff)
  then show ?thesis
    using e'
    by simp
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

lemma edge_in_graph_edge_in_quot:
  assumes "v \<in> s" "w \<notin> s" "{v, w} \<in> E"
  shows "{v, u} \<in> quotG E "
proof \<^marker>\<open>provenance ai\<close>-
  have "P ` {v, w} = {v, u}"
    using assms(1,2)
    by (simp add: insert_commute)
  then have "{v, u} \<in> quot_graph P E"
    using edge_in_graph_in_quot[OF assms(3), of P]
    by simp
  moreover have "{v, u} \<noteq> {u}"
    using assms(1) good_quot_map(1)
    by auto
  ultimately show ?thesis
    by simp
qed

lemma quotG_mono:
  "G \<subseteq> G' \<Longrightarrow> quotG G \<subseteq> quotG G'"
  by (intro Diff_mono quot_graph_subset subset_refl)

lemma edge_in_graph_edge_in_quot':
  assumes "v \<in> s" "w \<notin> s" "{w, v} \<in> E"
  shows "{u, v} \<in> quotG E "
  using edge_in_graph_edge_in_quot[of v w] assms
  by(auto simp add: insert_commute)

lemma edge_in_s_in_quotG:
  assumes "e \<subseteq> s" "G \<subseteq> E"
  shows "e \<in> quotG G \<longleftrightarrow> e \<in> G"
proof-
  have helper1:
    "\<lbrakk>(\<lambda>x. u) ` (ea \<inter> {v. v \<notin> s}) \<subseteq> s; ea \<in> G; ea \<inter> s \<union> (\<lambda>x. u) ` (ea \<inter> {v. v \<notin> s}) \<notin> G\<rbrakk>
      \<Longrightarrow> x = u" for ea x
    using good_quot_map(1) all_not_in_conv[of "ea \<inter> {R. R \<notin> s}"] inf_sup_aci(1)[of s ea]
          subsetI[of ea s] subsetI[of "{}" "(\<lambda>Q. u) ` bot"] inf.absorb2[of ea s]
    by auto
  have helper2:
    "\<lbrakk>(\<lambda>x. u) ` (ea \<inter> {v. v \<notin> s}) \<subseteq> s; ea \<in> G; ea \<inter> s \<union> (\<lambda>x. u) ` (ea \<inter> {v. v \<notin> s}) \<notin> G\<rbrakk>
      \<Longrightarrow> u \<in> ea" for ea
    using assms(2) subset_edges_G[of G ea] helper1[of ea]
    by force
  have helper3:
    "\<lbrakk>ea \<in> G; ea \<inter> s \<union> (\<lambda>x. u) ` (ea \<inter> {v. v \<notin> s}) \<notin> G;
       u \<notin> (\<lambda>x. u) ` (ea \<inter> {v. v \<notin> s})\<rbrakk> \<Longrightarrow> u \<in> s"
    for ea
    using rev_image_eqI[of u "ea \<inter> {R. R \<notin> s}" u "\<lambda>Q. u"]
      helper2[of ea]
    by auto
  show ?thesis
    using assms
    by(auto simp add: quot_graph_def intro: helper1 helper2 helper3)
qed

lemma edge_in_s_then_in_quotG:
  "\<lbrakk>e \<subseteq> s;  e \<in> E\<rbrakk> \<Longrightarrow> e \<in> quotG E"
 and edge_in_s_id_in_quotG:
  "\<lbrakk>e \<subseteq> s; e \<in> quotG E\<rbrakk> \<Longrightarrow> e \<in> E"
 and edge_in_s_then_in_quot_graph:
  "\<lbrakk>e \<subseteq> s;  e \<in> E\<rbrakk> \<Longrightarrow> e \<in> quot_graph P E"
  using edge_in_s_in_quotG by auto

lemma edge_in_s_then_in_quotG_subgraph:
  "\<lbrakk>e \<subseteq> s; e \<in> G; G \<subseteq> E\<rbrakk> \<Longrightarrow> e \<in> quotG G"
 and edge_in_s_id_in_quotG_subgraph:
  "\<lbrakk>e \<subseteq> s; e \<in> quotG G; G \<subseteq> E\<rbrakk> \<Longrightarrow> e \<in> G"
  using edge_in_s_in_quotG by auto

lemma in_quotG_subset_E:
  "\<lbrakk>e \<in> quotG G; G \<subseteq> E;
    \<And> ua va. \<lbrakk>e = {ua, va}; ua \<noteq> va; {ua, va} \<subseteq> s; e \<in> G; e \<noteq> {u}; P ` {ua, va} = e\<rbrakk> \<Longrightarrow> Q;
    \<And> va ua. \<lbrakk>e = {u, va}; va \<in> s; ua \<notin> s; {ua, va} \<in> G; ua \<noteq> va; e \<noteq> {u}; P ` {ua, va} = e\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
proof(goal_cases)
  case 1
  then obtain e' where e':  "e' \<in> E" "e = P ` e'" "e \<noteq> {u}"  "e' \<in> G"
    by(auto simp add: quot_graph_def)
  then obtain ua va where uava: "e' = {ua, va}" "ua \<noteq> va"
    by (auto elim!: dblton_graphE)
  show ?case
  proof(cases "{ua, va} \<subseteq> s")
    case True
    hence "e = e'"
      by (simp add: e'(2) uava(1))
    then show ?thesis
      using True uava e'(4)
      by(auto intro!: 1(3)[of ua va])
  next
    case False
    then obtain ua va where uava: "e' = {ua, va}" "ua \<noteq> va" "ua \<notin> s" "va \<in> s"
      using e'(2,3) uava(1) by auto
    then show ?thesis
      using e' by(auto intro!: 1(4)[of va ua])
  qed
qed

lemma in_quotGE:
  "\<lbrakk>e \<in> quotG E; \<And> ua va. \<lbrakk>e = {ua, va}; ua \<noteq> va; {ua, va} \<subseteq> s; e \<in> E; e \<noteq> {u}; P ` {ua, va} = e\<rbrakk> \<Longrightarrow> Q;
     \<And> va ua. \<lbrakk>e = {u, va}; va \<in> s; ua \<notin> s; {ua, va} \<in> E; ua \<noteq> va; e \<noteq> {u}; P ` {ua, va} = e\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
  by (rule in_quotG_subset_E[OF _ subset_refl])

lemma in_quot_graphE:
  "\<lbrakk>e \<in> quot_graph P E; \<And> ua va. \<lbrakk>e = {ua, va}; ua \<noteq> va; {ua, va} \<subseteq> s; e \<in> E; e \<noteq> {u}; P ` {ua, va} = e\<rbrakk> \<Longrightarrow> Q;
     \<And> va ua. \<lbrakk>e = {u, va}; va \<in> s; ua \<notin> s; {ua, va} \<in> E; ua \<noteq> va; e \<noteq> {u}; P ` {ua, va} = e\<rbrakk> \<Longrightarrow> Q;
     \<And> ua va. \<lbrakk>e = {u}; {ua, va} \<inter> s = {}; {ua, va} \<in> E; P ` {ua, va} = e\<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
proof (goal_cases)
  case H: 1
  show ?case
  proof (cases "e = {u}")
    case True
    obtain original where original: "original \<in> E" "e = P ` original"
      using H(1) unfolding quot_graph_def by auto
    obtain a b where shape: "original = {a, b}"
      using original(1) dblton_E by auto
    have edge: "{a, b} \<in> E" "e = P ` {a, b}"
      using original shape by simp_all
    have "{P a, P b} = {u}"
      using edge(2) True by (simp only: image_insert image_empty)
    hence "P a = u" "P b = u"
      by auto
    hence "{a, b} \<inter> s = {}"
      using good_quot_map(1) by (auto split: if_splits)
    then show ?thesis
      using H(4)[of a b] True edge by auto
  next
    case False
    hence "e \<in> quotG E"
      using H(1) by simp
    then show ?thesis
      by (rule in_quotGE[OF _ H(2,3)])
  qed
qed

lemma subgraph_edge_in_graph_edge_in_quot:
  assumes "v \<in> s" "w \<notin> s" "{v, w} \<in> G" "G \<subseteq> E"
  shows "{v, u} \<in> quotG G"
  using assms good_quot_map
  apply(simp add: image_def quot_graph_def)
  by (smt (verit, best) Collect_cong Int_insert_left_if0 Un_Int_eq(3) insertCI insert_commute
                        insert_def mk_disjoint_insert singleton_conv)

lemma subgraph_edge_in_graph_edge_in_quot':
  assumes "v \<in> s" "w \<notin> s" "{w, v} \<in> G" "G \<subseteq> E"
  shows "{u, v} \<in> quotG G"
  using subgraph_edge_in_graph_edge_in_quot[of v w] assms
  by(auto simp add: insert_commute)

lemma edge_in_quotG_2'_doubleton:
  assumes edge: "{u, v} \<in> (quotG M)" "v \<in> s" "M \<subseteq> E"
  shows "\<exists>w. {v,w} \<in> M \<and> w \<notin> s"
  using edge_in_quot_in_graph_2'_doubleton assms dblton_E
  by blast

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

lemma edge_of_path_in_graph_iff_in_quot:
  assumes "set p \<subseteq> s" "e \<in> set (edges_of_path p)" "M \<subseteq> E"
  shows "e \<in> M \<longleftrightarrow> e \<in> quotG M"
proof -
  have "e \<subseteq> s"
    using assms(1,2)
    by (auto dest: v_in_edge_in_path_gen)
  then show ?thesis
    using edge_in_s_in_quotG[OF _ assms(3)]
    by blast
qed

context
  fixes sel :: "'a set \<Rightarrow> 'a"
  assumes select: "\<And>A. \<lbrakk>finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow> sel A \<in> A"
begin

abbreviation "rev_P v \<equiv> (if v \<noteq> u then v else sel (Vs E - s))"

lemma sel': "sel (Vs E - s) \<in> Vs E - s"
  using good_quot_map finite_Vs by (intro select) auto

lemma rev_map_works_1:
  "v \<in> s \<Longrightarrow> rev_P v = v"
  using good_quot_map(1) by auto

lemma rev_map_works_2:
  "\<lbrakk>u \<in> Vs (quot_graph P E); s \<subset> Vs E\<rbrakk>
    \<Longrightarrow> rev_P u \<in> Vs E \<and> rev_P u \<notin> s"
  using sel' by auto

lemma rev_map_map:
  "\<lbrakk>set p \<subseteq> s; s \<subseteq> t\<rbrakk> \<Longrightarrow> map rev_P p = p"
  by (auto intro!: map_idI simp: rev_map_works_1)

lemma quot_alt_path_iff_alt_path:
  assumes path: "set p \<subseteq> s" "s \<subseteq> t"
  shows "alt_list (\<lambda>e. e \<notin> (quotG E)) (\<lambda>e. e \<in> (quotG E)) (edges_of_path p) =
                      alt_list (\<lambda>e. e \<notin> E) (\<lambda>e. e \<in> E) (edges_of_path (map rev_P p))"
  using edge_of_path_in_graph_iff_in_quot[OF path(1)]
  by(auto intro!: alt_list_cong_eq simp: rev_map_map[OF path])


end

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
  moreover have hl: "hd p \<in> s" "last p \<in> s" if "length p \<ge> 2"
  proof-
    from that have "p \<noteq> []"
      by (auto simp: Suc_le_length_iff)
    then show "hd p \<in> s" "last p \<in> s"
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
  have \<^marker>\<open>provenance ai\<close> "{v, v'} \<in> quot_graph P E"
    using edge_in_graph_in_quot[OF path2.hyps(1), of P] path2.prems(1)
    by simp
  then \<^marker>\<open>provenance ai\<close> show ?case
    using \<^marker>\<open>provenance ai\<close> path2 good_quot_map
    by \<^marker>\<open>provenance ai\<close> (auto simp: path2.IH)

qed

lemma qug_path_iff_case_1_ii:
  assumes path: "set p \<subseteq> s" 
  shows "path E p = path (quotG E) p"
proof \<^marker>\<open>provenance ai\<close>-
  have mp: "map P p = p"
    using path
    by (auto intro!: map_idI simp: subset_iff)
  show ?thesis
    using path path_is_quot_path[OF _ path] path_is_quot_path_diff_u[OF _ path] good_quot_map mp
    by auto
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
        by (intro path_is_quot_path; auto)
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
      using \<^marker>\<open>provenance ai\<close> in_edges_of_path_hd_or_tl[OF that(2)] that
      by \<^marker>\<open>provenance ai\<close> (cases p rule: edges_of_path.cases; auto)
    moreover case True
    ultimately show ?thesis
      using e matching_odd_cycle_hd_last_unmatched[OF cycle match(1)]
      by auto
  next
    case F1: False
    have "e \<in> E"
      using match e by auto
    then obtain a b where ends: "e = {a, b}" "a \<noteq> b"
      using dblton_E by auto
    then obtain v where v: "e = {v, last p}" "v \<noteq> last p"
      using e(2) by (auto simp: insert_commute)
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
        using \<^marker>\<open>provenance ai\<close> match[unfolded matching_def2]
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

context quot
begin

lemma quot_Vs_in_s: "Vs (quotG E) \<supseteq> s"
  using vert_in_graph_iff_in_quot_diff_u good_quot_map(2) by auto

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
  using \<^marker>\<open>provenance ai\<close> assms
  by \<^marker>\<open>provenance ai\<close> (auto dest: in_quot_graph_neq_u)

lemma neq_u_notin_quotG:
  assumes "v \<notin> s" "v \<noteq> u"
  shows "v \<notin> Vs (quotG E)"
  using assms
  using in_quotG_neq_u
  by blast

lemma s_not_in_quot_Delta_s_empty:
  assumes"u \<notin> Vs (quotG E)"
  shows "Delta E s= {}"
proof(rule ccontr, goal_cases)
  case 1
  then obtain x y where "x \<in> s" "y \<notin> s" "{x, y} \<in> E"
    by(auto elim!: in_DeltaE)
  hence "{y, u} \<in> (quotG E)"
    unfolding quot_graph_def
    using assms edge_in_graph_edge_in_quot edges_are_Vs_2
    by(auto intro!: bexI[of _ "{y, u}"])
  hence "u \<in> Vs (quotG E)"
    by auto
  then show ?case
    using assms by auto
qed

lemma Delta_s_empty_s_not_in_quot:
  assumes "Delta E s= {}"
  shows"u \<notin> Vs (quotG E)"
proof-
  have "xc = u"
    if "\<And> x u v. \<lbrakk>u \<in> s; {u, v} \<in> E; x = {u, v}\<rbrakk> \<Longrightarrow> v \<in> s"
       "e \<in> E" "xb \<in> e" "xb \<notin> s" "xc \<in> e" "xc \<in> s"
     for e xb xc
    using that(2)
  proof(elim dblton_graphE[of e], goal_cases)
    case (1 u v)
    then show ?case
      using that(2,3,4,5,6) that(1)[of v u "{v, u}"] that(1)[of u v "{u, v}"]
      by (auto simp add: insert_commute)
  qed
  thus ?thesis
    using good_quot_map assms(1)
    by(auto simp add: Delta_def quot_graph_def vs_member)
qed

lemma Delta_s_empty_iff_s_not_in_quot:
 "Delta E s = {} \<longleftrightarrow> u \<notin> Vs (quotG E)"
  using Delta_s_empty_s_not_in_quot s_not_in_quot_Delta_s_empty by blast

lemma Delta_s_Delta_compl_s_iff_empty:
  "Delta E s = {} \<longleftrightarrow> Delta E (Vs E - s) = {}"
proof-
  have helper:"v \<in> s"
    if "\<And> x u v. \<lbrakk>u \<in> Vs E; {u, v} \<in> E; x = {u, v}\<rbrakk> \<Longrightarrow> u \<in> s \<or> v \<in> Vs E \<and> v \<notin> s"
    "u \<in> s" "{u, v} \<in> E" for u v
    using that insert_commute[of u v "{}"] edges_are_Vs[of v u E]
    by auto
  show ?thesis
    by(auto simp add: Delta_def insert_commute| rule helper)+
qed

lemma Delta_wth_s_empty_quot_Vs:
 "Delta E (Vs E - s) = {} \<Longrightarrow> Vs (quotG E) = s"
 using Delta_s_Delta_compl_s_iff_empty Delta_s_empty_iff_s_not_in_quot quot_Vs_in_s
  by (auto intro!: in_quotG_neq_u)

lemma Delta_wth_s_nonempty_quot_Vs:
 "Delta E (Vs E - s) \<noteq> {} \<Longrightarrow> Vs (quotG E) = insert u s"
  using quot_Vs_in_s  neq_u_notin_quotG  Delta_s_Delta_compl_s_iff_empty s_not_in_quot_Delta_s_empty
  by force+

lemma connected_set_of_vertices_quot_iff:
  assumes "X \<subseteq> s" "Y \<subseteq> s"
  shows "X \<longleftrightarrow>\<^bsub>quot_graph P E - {{u}}\<^esub> Y \<longleftrightarrow> X \<longleftrightarrow>\<^bsub>E\<^esub> Y"
proof-
  have "\<exists>ua v. {ua, v} \<in> quot_graph P E \<and> (ua = u \<longrightarrow> v \<noteq> u) \<and> ua \<in> X \<and> v \<in> Y"
    if "X \<subseteq> s" "Y \<subseteq> s" "{ua, v} \<in> E" "ua \<in> X" "v \<in> Y"
    for ua v
   using that
   by(auto intro!: exI[of _ ua, OF exI[of _ v]]
         simp add: edge_in_s_then_in_quot_graph subset_iff)
  thus ?thesis
    using assms
    by (auto simp add: connected_set_of_vertices_def dest!: edge_in_quot_in_graph_1')
qed

lemma connected_set_of_vertices_quot_iff_u:
  assumes "u \<in> X" "Y \<subseteq> s"
  shows "X \<longleftrightarrow>\<^bsub>quotG E\<^esub> Y \<longleftrightarrow> X - {u} \<union> (Vs E - s) \<longleftrightarrow>\<^bsub>E\<^esub> Y"
proof(rule, goal_cases)
  case 1
  then obtain ua va where "{ua, va} \<in> quotG E" "ua \<in> X" "va \<in> Y"
    by(auto simp add: connected_set_of_vertices_def)
  then show ?case
  proof(elim in_quotGE, goal_cases)
    case (1 uaa vaa)
    then obtain uaa vaa where  "uaa \<in> X - {u}" "vaa \<in> Y" "{uaa, vaa} \<in> E"
      using good_quot_map(1) by(auto simp add: doubleton_eq_iff)
    then show ?case
      by(auto simp add: connected_set_of_vertices_def)
  next
    case (2 y x)
    hence unfolds: "ua = u" "va = y"
      using assms(2) good_quot_map(1)
      by(auto simp add: doubleton_eq_iff)
    note 2 = 2[simplified unfolds]
    hence "x \<in> Vs E - s"
      by blast
    thus ?thesis
      using 2
      by(auto intro!: exI[of _ x, OF exI[of _ y]]
            simp add: connected_set_of_vertices_def)
  qed
next
  case 2
  then obtain x y where xy: "{x, y} \<in> E" "x \<in> X - {u} \<union> (Vs E - s)" "y \<in> Y"
    by(auto simp add: connected_set_of_vertices_def)
  then show ?case
  proof(cases "x \<in> (Vs E - s)", goal_cases)
    case 1
    have "{y, u} \<in> quotG E"
      using assms(2) xy(3)  "1"(4)
      by(intro edge_in_graph_edge_in_quot[where w = x])
        (auto simp add: insert_commute xy(1))
    then show ?case
      using assms(1) 1(3)
      by(auto intro!: exI[of _ u, OF exI[of _ y]]
          simp add: connected_set_of_vertices_def insert_commute)
  next
    case 2
    hence x_in_s:"x \<in> s"
      by blast
    hence "{x, y} \<in> quotG E"
      using 2 assms(2)
      by (intro edge_in_s_then_in_quotG) auto
    then show ?case
      using 2
      by(auto simp add: connected_set_of_vertices_def)
  qed
qed

lemma u_in_X_Neighbourhood_expanded:
  assumes "u \<in> X"
  shows "Neighbourhood (quotG E) X = Neighbourhood E (X - {u} \<union> (Vs E - s))"
proof ((rule subset_antisym; rule subsetI; elim in_NeighbourhoodE), goal_cases)
  case (1 x y)
  then show ?case
  proof(elim in_quotGE, goal_cases)
    case (1 ua va)
    then show ?case
       using good_quot_map(1)
       by(auto intro: in_NeighbourhoodI[of ua va]  in_NeighbourhoodI[of va ua]
            simp add: doubleton_eq_iff in_NeighbourhoodI)
  next
    case (2 va ua)
    hence "u \<in> Vs (quotG E)"
      using "1"(1) by auto
    thus ?case
      using 2 assms
      by (auto simp add: doubleton_eq_iff  edges_are_Vs in_NeighbourhoodI)
  qed
next
  case (2 x y)
  have "\<lbrakk>{y, x} \<in> E; u \<notin> s; u \<in> X; y \<in> X; y \<noteq> u; x \<notin> X; x \<in> s\<rbrakk>
         \<Longrightarrow> x \<in> Neighbourhood (quot_graph P E - {{u}}) X"
    using  edge_in_graph_edge_in_quot'[of x y] edge_in_s_then_in_quotG[of "{y, x}"]
           in_NeighbourhoodI[of y x "quot_graph P E - {{u}}" X]
           in_NeighbourhoodI[of u x "quot_graph P E - {{u}}" X]
    by auto
  then show ?case
     using 2 good_quot_map(1) assms(1) edge_in_graph_edge_in_quot[of x y]
           in_NeighbourhoodI[of u x "quot_graph P E - {{u}}" X]
     by(auto simp add: insert_commute)
  qed

lemma u_not_in_subgraph_same_subgraph:
  assumes "u \<notin> X"  "X \<subseteq> Vs (quotG E)" "G \<subseteq> E"
  shows "(quotG G) \<lbrakk>X\<rbrakk> = G \<lbrakk>X\<rbrakk>"
proof ((rule subset_antisym; rule subsetI; elim in_graph_inter_VsE), goal_cases)
  case (1 e)
  thus ?case
  proof(elim in_quotG_subset_E[OF _ assms(3)], goal_cases)
    case (1 ua va)
    then show ?case
      by(auto intro!: in_graph_inter_VsI)
  next
    case (2 va ua)
    then show ?case
      using assms by auto
  qed
next
  case (2 e)
  then obtain x y where xy: "e = {x, y}" "x \<noteq> y" "{x, y} \<in> G"
    using assms(3) by force
  hence "e \<subseteq> s"
    using 2  assms(1,2) neq_u_notin_quotG by auto
  then show ?case
  proof(intro  in_graph_inter_VsI, goal_cases)
    case 1
    then show ?case
      using 2 assms(1)
      by(auto intro!: bexI[of _ e] simp add: quot_graph_def)
  qed (simp add: 2)
qed

lemma quot_Delta_no_change:
 "\<lbrakk>Undirected_Set_Graphs.neighbourhood (quotG G) u \<subseteq> X; G \<subseteq> E; u\<in> X\<rbrakk>
    \<Longrightarrow> Delta (quotG G) X = Delta G (X - {u} \<union> (Vs E - s))"
proof ((rule subset_antisym; rule subsetI; elim in_DeltaE), goal_cases)
  case (1 e u1 v1)
  then show ?case
  proof(elim in_quotG_subset_E, goal_cases)
    case 1
    then show ?case
      by auto
  next
    case (2 ua va)
    then show ?case
      using  good_quot_map(1)
      by(auto intro!: in_DeltaI[of "{u1, v1}" u1 v1 G "X - {u} \<union> (Vs E - s)"]
                      in_DeltaI[of "{v1, u1}" u1 v1 G "X - {u} \<union> (Vs E - s)"]
            simp add: doubleton_eq_iff)
  next
    case (3 va ua)
    hence "{u, va} \<in> quotG G"
      using "1"(5) by presburger
    hence "va \<in> Undirected_Set_Graphs.neighbourhood (quotG G) u"
      by(auto simp add: Undirected_Set_Graphs.neighbourhood_def doubleton_eq_iff insert_commute)
    hence "va \<in> X"
      using "3"(1) by blast
    thus ?case
      using "3"(3,4,6,7) by(auto simp add: doubleton_eq_iff)
  qed
next
  case (2 e u1 v1)
  have u1: "u1 \<notin> Vs E - s"
  proof(rule ccontr, goal_cases)
    case 1
    hence "{u, v1} \<in> quotG G"
      using "2"(2,4,5,7) subgraph_edge_in_graph_edge_in_quot' vs_member' by auto
    hence "v1 \<in> Undirected_Set_Graphs.neighbourhood (quotG G) u" "v1 \<noteq> u"
      by(auto simp add: Undirected_Set_Graphs.neighbourhood_def insert_commute)
    hence "v1 \<in> X" "v1 \<noteq> u"
      using "2"(1) by blast+
    then show ?case
      using "2"(7) by force
  qed
  hence "e \<in> quotG G"
    using "2"(2,4,5,7) empty_subsetI[of s] edge_in_s_in_quotG[of e G]
    by auto
  thus ?case
    using 2 u1 good_quot_map(1)
    by (intro in_DeltaI[of e u1 v1 "quotG G" X]) auto
qed

lemma quot_Delta_no_change2:
  "\<lbrakk>u \<notin> X; u \<notin> Neighbourhood (quotG G) X; G \<subseteq> E; X \<subseteq> s\<rbrakk> \<Longrightarrow>
   Delta (quotG G) X = Delta G X"
proof ((rule subset_antisym; rule subsetI; elim in_DeltaE not_in_NeighbourhoodE), goal_cases)
  case (1 e uu vv)
  then show ?case
  proof(elim in_quotG_subset_E, goal_cases)
    case 1
    then show ?case
      by simp
  next
    case (2 ua va)
    then show ?case
      by(intro in_DeltaI[of e uu vv G X])(auto simp add: doubleton_eq_iff)
  next
    case (3 va ua)
    then show ?case
      using 1
      by(auto simp add: doubleton_eq_iff)
  qed
next
  case (2 e uu vv)
  have "vv \<in> s"
  proof(rule ccontr, goal_cases)
    case 1
    hence "{uu, u} \<in> quotG G"
      using "2"(2,3,4,5,6) subgraph_edge_in_graph_edge_in_quot by blast
    then show ?case
      using "2"(1,6,8) by blast
  qed
  moreover hence "{uu, vv} \<in> quotG G"
    using "2"(2,3,4,5,6,7) edge_in_s_then_in_quotG_subgraph by auto
  ultimately show ?case
    using 2
    by(auto intro!: in_DeltaI[of "{uu, vv}" uu vv "quotG G" X])
qed

lemma Neighbourhood_quot:
  assumes "u \<notin> Vs E"  "Vs E - s \<subseteq> X"
  shows "Neighbourhood (quotG E) (X - (Vs E - s) \<union> {u}) = Neighbourhood E X"
proof ((rule subset_antisym; rule subsetI; elim in_NeighbourhoodE), goal_cases)
  case (1 x y)
  then show ?case
  proof(elim in_quotGE, goal_cases)
    case (1 ua va)
    then show ?case
      using good_quot_map(1)
      by (auto simp add: doubleton_eq_iff in_NeighbourhoodI)
  next
    case (2 va ua)
    then show ?case
      using assms(2)
      by (auto simp add: doubleton_eq_iff edges_are_Vs in_mono
          intro!: in_NeighbourhoodI[of ua va])
  qed
next
  case (2 x y)
  then show ?case
  proof(cases "y \<in> Vs E - s", goal_cases)
    case 1
    then show ?case
      using assms
      by (intro in_NeighbourhoodI[of u x] edge_in_graph_edge_in_quot')
        (auto dest: edges_are_Vs_2)
  next
    case 2
    then show ?case
      using assms
      by(auto intro!: in_NeighbourhoodI[of y x] edge_in_s_then_in_quot_graph
          intro: edges_are_Vs_2)
  qed
qed

lemma quotG_graph_inter_Vs_flip:
  assumes "G \<subseteq> E" "u \<in> X"
  shows "quotG (G \<lbrakk>X - {u} \<union> (Vs E - s)\<rbrakk>) = (quotG G) \<lbrakk>X\<rbrakk>"
proof ((rule subset_antisym; rule subsetI), goal_cases)
  case (1 e)
  then show ?case
  proof(elim in_quotG_subset_E, goal_cases)
    case 1
    then show ?case
      using assms graph_inter_Vs_subset(1) by blast
  next
    case (2 ua va)
    then show ?case
      using good_quot_map(1)  edge_in_graph_in_quot[of e G P] in_graph_inter_VsD(1)[of e G X]
      by (auto intro!: in_graph_inter_VsI[of "{ua, va}"] elim: in_graph_inter_VsE)
  next
    case (3 va ua)
    then show ?case
      using assms "3"(7) edge_in_graph_in_quot[of "{ua, va}" G P]
        graph_inter_Vs_subset(2)[of G "X - {u} \<union> (Vs E - s)"]
        edges_are_Vs_2[of ua va " G \<lbrakk>X - {u} \<union> (Vs E - s)\<rbrakk>"]
      by (auto intro!: in_graph_inter_VsI[of "{u, va}"] elim!: in_graph_inter_VsE)
  qed
next
  case (2 e)
  then show ?case
  proof(elim in_graph_inter_VsE in_quotG_subset_E[OF _ assms(1)], goal_cases)
    case (1 ua va)
    then show ?case
      using good_quot_map(1)  assms(1) graph_inter_Vs_subset(1)
      by (intro edge_in_s_then_in_quotG_subgraph)
        (auto intro!: in_graph_inter_VsI[of "{ua, va}" G "X- {u} \<union> (Vs E - s)"])
  next
    case (2 va ua)
    then show ?case
      using assms unfolding 2
      by(intro subgraph_edge_in_graph_edge_in_quot'[of va ua])
        (auto intro!: in_graph_inter_VsI elim!: in_graph_inter_VsE)
  qed
qed

end


subsection\<open>Quotienting/conracting an augmenting path\<close>

text\<open>We prove an augmenting path in a concrete graph can be abstracted into an augmenting path in a
     quotient graph\<close>

lemma alt_path_matching_quot:
  assumes "matching M" "{v, hd p} \<in> M" "alt_path M p" "odd (length p)"
          "dblton_graph M" "distinct p" "new_vert \<notin> Vs M -  set p"
       and contr_def: "contr = (\<lambda> x. if x \<in> set p then new_vert else x)"
     shows "quot_graph contr M - {{new_vert}} =
           M - set (edges_of_path (v#p)) \<union> {{v, new_vert}}"
proof-
have rev_alt_path_here:"rev_alt_path M (tl p)"
  by (simp add: alt_path_tl_rev_alt_path assms(3))
  have v_not_hp_p:"v \<noteq> hd p"
    using assms(2,5) by auto
  have hd_p_in_p:"hd p \<in> set p"
    using assms(4) by(cases p) auto
  have v_not_in_p: "v \<notin> set p"
    using assms by(intro beginning_of_alt_path_matched_partner_not_in_path) auto
    show ?thesis
proof ((rule subset_antisym; rule subsetI), goal_cases)
  case (1 e)
  then obtain e' where e':"e' \<in> M" "e = contr ` e'" "e \<noteq> {new_vert}"
    by(auto simp add: quot_graph_def)
  obtain ua va where ua_va:"e' = {ua, va}"
    using assms(5) e'(1) by auto
  have rev_alt_path_here:"rev_alt_path M (tl p)"
    by (simp add: alt_path_tl_rev_alt_path assms(3))
  then show ?case
  proof(cases rule: matching_edge_rev_alt_path_cases[OF rev_alt_path_here e'(1) assms(5,1)])
    case (1 u' v' i)
    then show ?thesis
      using e' by auto (auto simp add: contr_def nth_tl)
  next
    case (2 u v)
    then show ?thesis
      by (simp add: assms(4))
  next
    case 3
    show ?thesis
    proof(cases "v \<in> e'")
      case True
      hence "e' = {hd p, v}"
        using e'(1) matchingD[OF assms(1,2)] by force
      then show ?thesis
        using e' hd_p_in_p by(auto simp add: contr_def)
    next
      case False
      hence "ua \<in> set p \<longleftrightarrow> va \<in> set p"
        using assms e'(1)
        by(intro odd_len_alt_path_matching_edge_both_verts) (auto simp add: ua_va)
      hence ua_not_in_p: "ua \<notin> set p" "va \<notin> set p"
        using e'(2,3)  by (force simp add: contr_def ua_va)+
      hence "contr ` e' = e'"
        by(auto simp add: ua_va contr_def)
      moreover have "e' \<notin> set (edges_of_path (v # p))"
        using False ua_not_in_p(1) ua_va v_in_edge_in_path by fastforce
     ultimately show ?thesis
       by (simp add: e'(1,2))
    qed
  qed
next
  case (2 e)
  then show ?case
  proof(rule UnE, goal_cases)
    case 1
    hence eM: "e \<in> M" "e \<notin> set (edges_of_path (v # p))"
      by auto
    then obtain ua va where uava: "e = {ua, va}"
      using assms(5) by auto
    show ?case
  proof(cases rule: matching_edge_rev_alt_path_cases[OF rev_alt_path_here eM(1) assms(5,1)])
    case (1 u' v' i)
    hence "e \<in> set (edges_of_path (v # p))"
      unfolding in_set_conv_nth
      by(intro exI[of _ "Suc (Suc i)"] )
        (auto simp add: edges_of_path_index_append_tl edges_of_path_length )
    then show ?thesis
      using eM(2) by simp
  next
    case (2 u' v')
    then show ?thesis
      by (simp add: assms(4))
  next
    case 3
    have  "e \<noteq> {hd p, v}"
      using eM(2) assms(4) by(cases p rule: list_cases4) auto
    hence "ua \<in> set p \<longleftrightarrow> va \<in> set p"
      using doubleton_in_matching(1)[OF assms(1)] assms(2) eM(1)
        by(intro odd_len_alt_path_matching_edge_both_verts[OF assms(1) _ assms(3,4,5,6), of v])
          (auto simp add: uava insert_commute)
      hence ua_not_in_p: "ua \<notin> set p" "va \<notin> set p"
        using eM 3 matching_partner_eqI[OF assms(1)] assms(2)
        by (cases p; auto simp: contr_def uava)+
      hence "contr ` e = e" "e \<noteq> {new_vert}"
        using assms(7) eM(1) by(auto simp add: uava contr_def)
      thus ?thesis
        by(auto intro!: bexI[of _ e] simp add: quot_graph_def eM(1))
    qed
  next
    case 2
    hence "contr ` {v, hd p} = e" "e \<noteq> {new_vert}"
      using hd_p_in_p  v_not_in_p assms(2,7) by(auto simp add: contr_def)
    thus ?case
      by(auto intro!: bexI[of _ "{v, hd p}"] simp add: quot_graph_def assms(2))
  qed
qed
qed

lemma set_minus_absorb: "A - B = A - (A \<inter> B)" by auto

lemma alt_path_contract_matching:
  assumes "graph_matching G M" "{v, hd p} \<in> M" "alt_path M p" "odd (length p)"
          "dblton_graph M" "distinct p" "new_vert \<notin> Vs M -  set p"
and contr_def: "contr = (\<lambda> x. if x \<in> set p then new_vert else x)"
shows "graph_matching (quot_graph contr G - {{new_vert}})
                      (quot_graph contr M - {{new_vert}})"
proof
  have matchingM:"matching M"
    using assms(1) by auto
  have rev_alt_hre:"rev_alt_path M (v # p)"
    using assms(2,3,4) by(cases p) (auto simp add: alt_list_step)
  note M_inter_p = rev_alt_path_intersected_with_matching[OF matchingM rev_alt_hre]
  show "matching (quot_graph contr M - {{new_vert}})"
    unfolding alt_path_matching_quot[OF matchingM assms(2-)]
  proof (rule matching_vertex_disj_union, goal_cases)
    case 3
    then show ?case
      using assms(4,7) M_inter_p
      by (subst set_minus_absorb[of M], unfold M_inter_p,
          subst remove_matching_edges_Vs[OF matchingM])
         (auto simp: verts_of_even_edges[of "v#p", simplified] Vs_of_edge)
  qed (auto simp add: matching_singleton matchingM matching_delete)
  show "quot_graph contr M - {{new_vert}} \<subseteq> quot_graph contr G - {{new_vert}}"
    using assms(1) by (auto simp: quot_graph_def)
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

text\<open>Constructing an absrtact aumenting path from a concrete path, given that the blossom's base is
     not matched.\<close>

lemma aug_path_works_in_contraction_unmatched_base:
  assumes cycle: "odd_cycle C" "alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path C)" and
    aug_path: "matching_augmenting_path M p" "path E p" "distinct p" "(set p) \<inter> (set C) \<noteq> {}" "last C \<notin> Vs M" and 
    matching: "matching M" "M \<subseteq> E" and
    quot: "s = (Vs E) - set C" "u \<notin>  Vs E"
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
      using \<^marker>\<open>provenance ai\<close> p1_nempty p1_subset_s
      by \<^marker>\<open>provenance ai\<close> (auto intro: last_in_set)
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
        then \<^marker>\<open>provenance ai\<close> have "path E (butlast p1 @ (last p1 # w # []))"
          by \<^marker>\<open>provenance ai\<close> (simp only: *[symmetric])
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
          using \<^marker>\<open>provenance ai\<close> aug_path(2) wx(1) that p3_nempty
          by \<^marker>\<open>provenance ai\<close> (auto simp: distinct_append dest: last_in_set hd_in_set)
        then show ?thesis
          by (auto simp add: doubleton_eq_iff)
      qed
      then have hdp3_x_nin_M: "{x, hd p3} \<notin> M"
        using \<^marker>\<open>provenance ai\<close> matching(1)
        unfolding \<^marker>\<open>provenance ai\<close> Vs_def matching_def2
        using \<^marker>\<open>provenance ai\<close> alt_list_p1_u[of "rev p3" "rev p" x "rev p1"] p3_nempty p3_subset_s wx(1,2)
        by \<^marker>\<open>provenance ai\<close> (auto simp: last_rev insert_commute)
      have "edges_of_path p = edges_of_path (p1  @ [x])@ edges_of_path (x # p3)"
        unfolding \<^marker>\<open>provenance ai\<close> wx(1)
        using \<^marker>\<open>provenance ai\<close> edges_of_path_append_2[where p' = "x # p3"]
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
          using \<^marker>\<open>provenance ai\<close> p3_nempty p3_subset_s
          by \<^marker>\<open>provenance ai\<close> (auto intro: hd_in_set)
        assume "\<not> {u, hd p3} \<notin> quotG M"
        then have "{u, hd p3} \<in> quotG M"
          by simp
        then have "\<exists>v. {v, hd p3} \<in> M \<and> v \<notin> s"
          using \<^marker>\<open>provenance ai\<close> hd_p3_in_s matching(2) edge_in_quotG_2'_doubleton[of "hd p3" M]
          by \<^marker>\<open>provenance ai\<close> (auto simp: insert_commute)
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
        using \<^marker>\<open>provenance ai\<close> p1p2x(1) aug_path(2) path_pref
        by \<^marker>\<open>provenance ai\<close> (auto dest: path_pref)
      then show ?thesis
        using quot p1p2x(3)
        using mem_path_Vs
        by fastforce
    qed
    have p2_subset_s[simp]: "set p2 \<subseteq> s"
    proof-
      have "path E p2"
        using \<^marker>\<open>provenance ai\<close> p1p2x(1) aug_path(2) path_suff[of E "p1 @ [x]" p2]
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
          moreover have "last p2 \<notin> Vs M"
            using p1p2x(1) matching_augmenting_path_feats(4)[OF aug_path(1)] p1_empty p2_nempty
            by auto
          ultimately have "last p2 \<notin> Vs (quotG M)"
            using vert_in_graph_iff_in_quot_diff_u \<open>M \<subseteq> E\<close>
            by blast
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
          by (intro alt_list_u_p3[of "rev p" "rev p2" x] matching_augmenting_path_rev[OF aug_path(1)] aug_path(5); auto)
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
            by (rule subsetD[OF p1_subset_s hd_in_set[OF p1_nempty]])
          moreover have "hd p1 \<notin> Vs M"
            using p1p2x(1) matching_augmenting_path_feats(3)[OF aug_path(1)] p1_nempty
            by auto
          ultimately have "hd p1 \<notin> Vs (quotG M)"
            using vert_in_graph_iff_in_quot_diff_u \<open>M \<subseteq> E\<close>
            by blast
          then show ?thesis
            using p1_nempty
            by (simp add: last_rev)
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
              using \<^marker>\<open>provenance ai\<close> matching_augmenting_path_feats(2)[OF aug_path(1), unfolded rw1 rw2 rw3]
              using \<^marker>\<open>provenance ai\<close> alt_list_append_1'[of "\<lambda>e. e \<notin> M" "\<lambda>e. e \<in> M" "edges_of_path p1 @ [{last p1, x}]" "{hd p2, x} # edges_of_path p2"]
                    p1_x_nin_M
              by \<^marker>\<open>provenance ai\<close> (auto simp: alt_list_step)
          qed
          have False
            using hdp2_x_in_M
            by (intro alt_list_p1_u[of "rev p2" "rev p" x "rev p1"]; simp add: last_rev)
          then show ?thesis
            by \<^marker>\<open>provenance ai\<close> simp
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
        using \<^marker>\<open>provenance ai\<close> wx(1) aug_path(2) path_pref
        by \<^marker>\<open>provenance ai\<close> (auto dest: path_pref)
      then show ?thesis
        using quot wx(5)
        using mem_path_Vs
        by fastforce
    qed
    have p3_subset_s: "set p3 \<subseteq> s"
    proof-
      have "path E p3"
        using \<^marker>\<open>provenance ai\<close> wx(1) aug_path(2) path_suff[of E "p1 @ w # p2 @ [x]" p3]
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
        unfolding \<^marker>\<open>provenance ai\<close> wx(1)
        using \<^marker>\<open>provenance ai\<close> edges_of_path_append_2[where p' = "x # p3" and p = "p1 @ w # p2"]
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
          using \<^marker>\<open>provenance ai\<close> p3_nempty p3_subset_s
          by \<^marker>\<open>provenance ai\<close> (auto intro: hd_in_set)
        assume "\<not> {u, hd p3} \<notin> quotG M"
        then have "{u, hd p3} \<in> quotG M"
          by simp
        then have "\<exists>v. {v, hd p3} \<in> M \<and> v \<notin> s"
          using \<^marker>\<open>provenance ai\<close> hd_p3_in_s matching(2) edge_in_quotG_2'_doubleton[of "hd p3" M]
          by \<^marker>\<open>provenance ai\<close> (auto simp: insert_commute)
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
        then \<^marker>\<open>provenance ai\<close> have \<^marker>\<open>provenance ai\<close> "x = last C"
          using wx(3) in_odd_cycle_in_M[OF _ cycle]
          by blast
        moreover \<^marker>\<open>provenance ai\<close> have \<^marker>\<open>provenance ai\<close> "w = last C"
          using w_nin_M wx(2) in_odd_cycle_in_M[OF _ cycle]
          by blast
        ultimately \<^marker>\<open>provenance ai\<close> show False
          using \<^marker>\<open>provenance ai\<close> wx(4)
          by \<^marker>\<open>provenance ai\<close> simp
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
        moreover have "last p3 \<notin> Vs M"
          using wx(1) matching_augmenting_path_feats(4)[OF aug_path(1)] p3_nempty
          by auto
        ultimately have "last p3 \<notin> Vs (quotG M)"
          using vert_in_graph_iff_in_quot_diff_u \<open>M \<subseteq> E\<close>
          by blast
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
          by (intro alt_list_u_p3[of "rev p" "rev p3" x "rev p2" w] matching_augmenting_path_rev[OF aug_path(1)] aug_path(5); simp add: insert_commute hd_rev)
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
            by (rule subsetD[OF p1_subset_s hd_in_set[OF p1_nempty]])
          moreover have "hd p1 \<notin> Vs M"
            using wx(1) matching_augmenting_path_feats(3)[OF aug_path(1)] p1_nempty
            by auto
          ultimately have "hd p1 \<notin> Vs (quotG M)"
            using vert_in_graph_iff_in_quot_diff_u \<open>M \<subseteq> E\<close>
            by blast
          then show ?thesis
            using p1_nempty
            by (simp add: last_rev)
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
    by \<^marker>\<open>provenance ai\<close> (auto dest: bspec[of _ _ qe])
  have \<^marker>\<open>provenance ai\<close> aux2: "\<exists>w. w \<in> qq \<and> w \<noteq> u \<and> w \<in> s \<and> qq = {u, w}" if "qq \<in> quotG M" "u \<in> qq" for qq
    using that assms(3) good_quot_map(1) dblton_E
    unfolding quot_graph_def
    by (auto simp: image_iff)
  show False
  proof(cases "v \<in> s")
    text\<open>if v in s, then due to the way the quot mapping works, and since qe, qe' in quotG M,
      we will have two different matched edges in M that both include M. This leads to a
      contradiction.\<close>
    case True
    have \<^marker>\<open>provenance ai\<close> aux: "\<exists>e\<in>M. qq = P ` e \<and> v \<in> e" if "qq \<in> quotG M" "v \<in> qq" for qq
      using that True good_quot_map(1)
      unfolding quot_graph_def
      by (auto simp: image_iff)
    then obtain e e' where e: "v \<in> e" "v \<in> e'" "e \<in> M" "e' \<in> M" "e \<noteq> e'"
      using \<^marker>\<open>provenance ai\<close> aux[OF qe(2) qe(1)] aux[OF qe'(3) qe'(1)] qe'(2)
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
      obtain w where w: "w \<in> qe" "w \<noteq> u" "w \<in> s" "qe = {u, w}"
        using aux2[OF qe(2)] qe(1) vu
        by auto
      obtain x where x: "x \<in> qe'" "x \<noteq> u" "x \<in> s" "qe' = {u, x}"
        using aux2[OF qe'(3)] qe'(1) vu
        by auto
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
      using \<^marker>\<open>provenance ai\<close> False good_quot_map
      by \<^marker>\<open>provenance ai\<close> (auto simp: image_iff set_eq_iff)
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
      have \<^marker>\<open>provenance ai\<close> uin: "u \<in> P ` e"
        using True
        by (auto simp: image_iff)
      have \<^marker>\<open>provenance ai\<close> sin: "\<exists>x\<in>s. x \<in> P ` e"
        using False
        by (auto simp: image_iff)
      then have "\<forall>e'\<in>E'. P ` e \<noteq> P ` e'"
      proof \<^marker>\<open>provenance ai\<close>(intro ballI notI)
        fix e'
        assume e': "e' \<in> E'" "P ` e = P ` e'"
        have "u \<in> P ` e'"
          using uin
          by (simp only: e')
        moreover have "\<exists>x\<in>s. x \<in> P ` e'"
          using sin
          by (simp only: e')
        ultimately show False
          using disj e'(1) good_quot_map(1)
          by (auto simp: image_iff)
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
          by (auto simp: subset_iff)
        have "e' \<subseteq> s"
        proof
          fix x
          assume "x \<in> e'"
          then have "P x \<in> e"
            using e'(2) Pe
            by blast
          then have "P x \<in> s"
            using \<open>e \<subseteq> s\<close>
            by blast
          then show "x \<in> s"
            using good_quot_map(1)
            by (auto split: if_splits)
        qed
        then have "P ` e' = e'"
          by (auto simp: subset_iff)
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

lemmas graph_subset_quot_subset = quot_graph_subset

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
  by (rule dblton_graph_contract_into_one_vert[OF dblton_graph_subset[OF dblton_E assms],
        where S = "-s"]) (auto intro!: ext)

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
        have eq: "edges_of_path (stem @ C) = edges_of_path (stem @ [hd C]) @ edges_of_path C"
          using odd_cycle_nempty[OF match_blossomD(3)[OF \<open>match_blossom M stem C\<close>]] edges_of_path_append_2
          by blast
        then show ?thesis
          using match_blossomD(1)[OF \<open>match_blossom M stem C\<close>] alt_list_append_1
          by auto
      qed
      have distinct_stem_hdC: "distinct (stem @ [hd C])"
      proof-
        have bl: "butlast C = hd C # tl (butlast C)"
          using \<^marker>\<open>provenance ai\<close> odd_cycleD(1)[OF match_blossomD(3)[OF \<open>match_blossom M stem C\<close>]]
          by \<^marker>\<open>provenance ai\<close> (cases C; auto)
        then show ?thesis
          using \<^marker>\<open>provenance ai\<close> match_blossomD(2)[OF \<open>match_blossom M stem C\<close>] bl
          by \<^marker>\<open>provenance ai\<close> (cases "butlast C"; auto simp: distinct_append)
      qed
      have path_stem_hdC: "path E (stem @ [hd C])"
        using \<^marker>\<open>provenance ai\<close> match_blossom(1) odd_cycle_nempty[OF match_blossomD(3)[OF \<open>match_blossom M stem C\<close>]]
        using \<^marker>\<open>provenance ai\<close> path_pref[of E "stem @ [hd C]" "tl C"]
        by \<^marker>\<open>provenance ai\<close> (cases C; auto)
      have stem_hdC_nempty: "edges_of_path (stem @ [hd C]) \<noteq> []"
        using \<^marker>\<open>provenance ai\<close> stem_nempty edges_of_path_snoc[OF stem_nempty, of "hd C"]
        by \<^marker>\<open>provenance ai\<close> (auto simp flip: edges_of_path_snoc)
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
      have \<^marker>\<open>provenance ai\<close> stem_C_disj: "set C \<inter> set stem = {}"
        using match_blossomD(2)[OF \<open>match_blossom M stem C\<close>] distinct_stem_hdC odd_cycleD(3)[OF match_blossomD(3)[OF \<open>match_blossom M stem C\<close>]]
        by (cases C rule: rev_cases; auto simp: distinct_append)
      have M'_matching: "matching M'"
        unfolding M'_def
      proof(intro symm_diff_is_matching' distinct_stem_hdC, goal_cases)
        case 1
        show ?case
          using alt_list_stem_hdC
          by auto
      next
        case 2
        show ?case
          using matching(1)
          by auto
      next
        case 3
        show ?case
          using match_blossomD(4)[OF \<open>match_blossom M stem C\<close>]
          by (simp add: stem_nempty)
      next
        case 4
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
        unfolding \<^marker>\<open>provenance ai\<close> M'_def
        using \<^marker>\<open>provenance ai\<close> matching(2)
        using \<^marker>\<open>provenance ai\<close> sym_diff_subset[of M "set (edges_of_path (stem @ [hd C]))"] path_edges_subset[OF path_stem_hdC]
        by \<^marker>\<open>provenance ai\<close> blast
      ultimately obtain p_M' where aug_M': "matching_augmenting_path M' p_M'" "path E p_M'" "distinct p_M'"
        using \<^marker>\<open>provenance ai\<close> Berge[OF M'_finite _ _ dblton_E finite_Vs]
        by \<^marker>\<open>provenance ai\<close> auto

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
          unfolding \<^marker>\<open>provenance ai\<close> M'_def
        proof \<^marker>\<open>provenance ai\<close>(intro ballI notI)
          fix e
          assume e: "e \<in> M \<oplus> set (edges_of_path (stem @ [hd C]))" "hd C \<in> e"
          have "e \<in> M \<or> e \<in> set (edges_of_path (stem @ [hd C]))"
            using e(1)
            by (auto simp: symmetric_diff_def)
          then have "e = last (edges_of_path (stem @ [hd C]))"
            using e(2) memlast Mhd
            by blast
          then show False
            using e(1) lastnin
            unfolding M'_def
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
        case 1
        show ?case
          using match_blossom_alt_cycle[OF \<open>match_blossom M stem C\<close>] .
      next
        case 2
        show ?case
        proof-
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
      qed
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
        using \<^marker>\<open>provenance ai\<close> Berge_2[OF qaug(1) sub_qM' qaug(2) qaug(3) fin_qM' match_qM']
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
  have p_subset_s: "set p \<subseteq> s"
    using no_s_verts subset_path_Vs[OF graph_augmenting_path_feats(3)[OF aug_path]]
    by (auto simp only: quot(1))
  have "path (quotG E) p"
    using graph_augmenting_path_feats(3)[OF aug_path]
    by (simp only: qug_path_iff_case_1_ii[OF p_subset_s, symmetric])
  moreover have "matching_augmenting_path (quotG M) p"
    using graph_augmenting_path_feats(1)[OF aug_path]
    by (simp only: qug_path_iff_case_1_i[OF p_subset_s matching(2), symmetric])
  ultimately show ?thesis
    using graph_augmenting_path_feats(2)[OF aug_path]
    by (intro exI[of _ p]) simp
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
  ultimately \<^marker>\<open>provenance ai\<close> have \<^marker>\<open>provenance ai\<close> eq: "insert u (Vs (quotG E)) = insert u (Vs E \<inter> s)"
    by simp
  have \<^marker>\<open>provenance ai\<close> fin: "finite (insert u (Vs E \<inter> s))"
    using assms(1)
    by simp
  have \<^marker>\<open>provenance ai\<close> cu: "card (insert u (Vs E \<inter> s)) = card (Vs E \<inter> s) + 1"
    using assms(1) good_quot_map(1)
    by simp
  have \<^marker>\<open>provenance ai\<close> "card (Vs (quotG E)) \<le> card (insert u (Vs E \<inter> s))"
    using eq fin
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
      by \<^marker>\<open>provenance ai\<close> (auto simp flip: edges_of_path_snoc)
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
      using \<^marker>\<open>provenance ai\<close> last_stem_hdC stem_nempty odd_cycleD(3)[OF match_blossomD(3)[OF match_blossom]]
      by \<^marker>\<open>provenance ai\<close> (simp flip: edges_of_path_snoc[OF stem_nempty])
    ultimately show ?p2
      using \<^marker>\<open>provenance ai\<close> that(1,2,4) matching(1) \<open>v \<in> set C\<close> \<open>w \<notin> set C\<close>
      by \<^marker>\<open>provenance ai\<close> (auto simp add: matching_def2 Vs_def)
  qed
  then show ?thesis
    using \<^marker>\<open>provenance ai\<close> dblton_E matching(2)
    by \<^marker>\<open>provenance ai\<close> (intro quot_is_matching[where dume = "{last stem, last C}"] matching(1,2); auto elim!: dblton_graphE)
qed


lemma graph_invar_quotG:
  "graph_invar (quotG E)"
  by (simp add: Vs_quotG_finite doubleton_quot finite_Vs)


end

end

