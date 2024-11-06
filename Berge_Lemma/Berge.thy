(*
  Author: Mohammad Abdulaziz
*)

theory Berge
imports Undirected_Set_Graphs.Undirected_Set_Graphs Alternating_Lists
begin

subsection \<open>Misc\<close>

lemma distinct_singleton_set: "distinct xs \<Longrightarrow> set xs = {x} \<longleftrightarrow> xs = [x]"
  by (induction xs arbitrary:) (fastforce simp add: neq_Nil_conv intro: ccontr[where P = "_ = []"])+

lemma empty_iff_card_0: "finite s \<Longrightarrow> s = {} \<longleftrightarrow> card s = 0"
  by auto

lemma degree_insert_leq: "degree G e \<le> degree (insert e' G) e"
  by (simp add: subset_edges_less_degree subset_insertI)

lemma in_singleton: "\<lbrakk>s = {x}; y \<in> s\<rbrakk> \<Longrightarrow> x = y"
  by auto

subsection \<open>Symmetric Difference\<close>

definition symmetric_diff (infixl "\<oplus>" 65) where
  "symmetric_diff s t = (s - t) \<union> (t - s)"

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


subsection \<open>Matchings\<close>

definition matching where
  "matching M \<longleftrightarrow> 
     (\<forall>e1 \<in> M. \<forall>e2 \<in> M. e1 \<noteq> e2 \<longrightarrow> e1 \<inter> e2 = {})"

lemma matchingE:
  "matching M \<Longrightarrow> 
    ((\<And>e1 e2. \<lbrakk>e1 \<in> M; e2 \<in> M; e1 \<noteq> e2\<rbrakk> \<Longrightarrow> e1 \<inter> e2 = {}) \<Longrightarrow> P) \<Longrightarrow> P"
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

lemma degree_symm_diff:
  assumes "matching M" "matching M'"
  shows "degree (M \<oplus> M') v \<le> 2"
proof-
  have "{e. v \<in> e} \<inter> ((M - M') \<union> (M' - M)) \<subseteq> ({e. v \<in> e} \<inter> M) \<union> ({e. v \<in> e} \<inter> M')"
    by blast
  hence "degree (M \<oplus> M') v \<le> degree (M \<union> M') v"
    by (simp add: card'_mono Int_Un_distrib degree_def symmetric_diff_def)
  also have "... \<le> degree M v + degree M' v"
    by (simp add: Int_Un_distrib card'_def card_Un_le degree_def)
  also have "... \<le> degree M v + 1"
    using degree_matching[OF \<open>matching M'\<close>]
    by auto
  also have "... \<le> 2"
    using degree_matching[OF \<open>matching M\<close>]
    by (subst one_add_one[symmetric]) (fastforce intro!:  add_right_mono)
  finally show ?thesis .
qed


subsection \<open>Augmenting Paths\<close>

definition matching_augmenting_path where
  "matching_augmenting_path M p = ( 
    (length p \<ge> 2) \<and>
     alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path p) \<and> 
     hd p \<notin> Vs M \<and> last p \<notin> Vs M)"

abbreviation "graph_augmenting_path G M p \<equiv>
  path G p \<and> distinct p \<and> matching_augmenting_path M p"

lemma matching_augmenting_path_feats:
  assumes "matching_augmenting_path M p"
  shows "(length p \<ge> 2)" "alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path p)" "hd p \<notin> Vs M" "last p \<notin> Vs M"
  using assms
  by (auto simp: matching_augmenting_path_def)

lemma graph_augmenting_path_feats:
  assumes "graph_augmenting_path G M p"
  shows "matching_augmenting_path M p" "distinct p" "path G p"
  using assms
  by auto

lemma matching_augmenting_pathE:
  "\<lbrakk>matching_augmenting_path M p; \<lbrakk>(length p \<ge> 2); alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path p); hd p \<notin> Vs M; last p \<notin> Vs M\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
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
  by (fastforce
            simp add: eval_nat_numeral Suc_le_length_iff edges_of_path_length'[where p = p]
                      matching_augmenting_path_last_edge_nin
            dest!: alternating_list_even_last
            elim!: matching_augmenting_pathE)

subsection\<open>Direction 1 of Berge\<close>
text\<open>If there is a bigger matching, then there is an augmenting path\<close>

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

lemma one_unbalanced_comp_edges:
  assumes finite: "finite G" and
          card_lt: "card G < card G'" and
          finite_conn_comps: "finite (connected_components (G \<oplus> G'))" and
          doubleton_edges: "\<forall>e\<in>(G \<oplus> G'). \<exists>u v. e = {u, v}"
  shows "\<exists>eC \<in> components_edges (G \<oplus> G'). card (eC \<inter> G) < card (eC \<inter> G')"
proof(intro Union_lt assms)
  have *: "(G \<oplus> G') \<inter> {{x, y} |x y. True} = (G \<oplus> G')" 
    using doubleton_edges
    by auto
  show "card (\<Union> (components_edges (G \<oplus> G')) \<inter> G) < card (\<Union> (components_edges (G \<oplus> G')) \<inter> G')"
    unfolding component_edges_partition *
    by(intro smaller_matching_less_members finite card_lt)
  show "\<forall>eC\<in>components_edges (G \<oplus> G'). \<forall>s'\<in>components_edges (G \<oplus> G'). eC \<noteq> s' \<longrightarrow> eC \<inter> s' = {}"
    unfolding components_edges_def
    using component_edges_disj
    by auto
  show "finite G'"
    using finite card_lt
    using card_gt_0_iff by fastforce
qed(auto simp add: components_edges_def finite_conn_comps)

lemma matchings_in_diff:
  assumes "matching M" "matching M'" "{a, b} \<in> M \<oplus> M'" "{b, c} \<in> M \<oplus> M'" "a \<noteq> c"
  shows "{a, b} \<in> M \<longleftrightarrow> {b, c} \<in> M'"
proof-
  have sym_def: "x \<in> M \<oplus> M' \<Longrightarrow> x \<in> M \<or> x \<in> M' \<and> (x \<in> M \<longrightarrow> x \<notin> M') \<and> (x \<in> M' \<longrightarrow> x \<notin> M)" for x
    unfolding symmetric_diff_def by blast
  have aneqc: "{a, b} \<noteq> {b, c}"
    by(auto simp: \<open>a \<noteq> c\<close> doubleton_eq_iff)
  hence notbothM: "\<not> ({a, b} \<in> M \<and> {b, c} \<in> M)" 
    using \<open>matching M\<close>
    by(fastforce simp: matching_def)
  from aneqc
  have notbothM': "\<not> ({a, b} \<in> M' \<and> {b, c} \<in> M')"
    using \<open>matching M'\<close>
    by(fastforce simp: matching_def)
  show ?thesis
  proof
    assume "{a, b} \<in> M"
    then show "{b, c} \<in> M'" using sym_def[OF assms(4)] notbothM by simp
  next
    assume "{b, c} \<in> M'"
    then show "{a, b} \<in> M" using sym_def[OF assms(3)] notbothM' by simp
  qed
qed

lemma matching_paths_alternate:
  assumes "path (M \<oplus> M') p" "matching M" "matching M'" "distinct (edges_of_path p)"
  shows "alt_list (\<lambda>e. e \<in> M) (\<lambda>e. e \<in> M') (edges_of_path p) \<or>
         alt_list (\<lambda>e. e \<in> M') (\<lambda>e. e \<in> M) (edges_of_path p)"
  using assms
proof(induction p rule: induct_list0123)
  case (list2 v v')
  then show ?case
    using distinct_edges_of_paths_cons sym_diff_subset
    by (fastforce simp add: alt_list_empty alt_list_step split: if_splits)
next
  case (list3 v v' v'' vs)
  have "v \<noteq> v''" using list3.prems(4) by auto
  from list3 consider
    "alt_list (\<lambda>e. e \<in> M) (\<lambda>e. e \<in> M') (edges_of_path (v'#v''#vs))"
    | "alt_list (\<lambda>e. e \<in> M') (\<lambda>e. e \<in> M) (edges_of_path (v'#v''#vs))"
    by fastforce
  then show ?case
  proof cases
    case 1
    hence "{v', v''} \<in> M" by (simp add: alt_list_step)
    hence "{v, v'} \<in> M'"
      using path_2 list3.prems(1,4) matchings_in_diff[OF list3.prems(2,3)]
      by (fastforce simp: \<open>v\<noteq>v''\<close> insert_commute)
    thus ?thesis
      using "1" alt_list.simps
      by force
  next
    case 2
    hence "{v', v''} \<in> M'" by (simp add: alt_list_step)
    hence "{v, v'} \<in> M"
      using path_2 list3.prems(1,4) matchings_in_diff[OF list3.prems(2,3)]
      by (fastforce simp: \<open>v\<noteq>v''\<close> insert_commute)
    thus ?thesis using "2" alt_list.simps by force
  qed
qed (simp_all add: alt_list_empty)

(*
  Gvery edge in the set of edges belonging to the connected component with more edges from M'
  belongs to the edge path representing that connected component.
*)

definition component_path' where
  "component_path' G C = (SOME p. path G p \<and> C = set p \<and> distinct p)"

lemma (in graph_abs) component_path'_works':
  "\<lbrakk> C \<in> connected_components G;
    \<And>v. v\<in>Vs G \<Longrightarrow> degree G v \<le> 2 \<rbrakk> \<Longrightarrow>
    path G (component_path' G C) \<and> C = set (component_path' G C) \<and> distinct (component_path' G C)"
  unfolding component_path'_def
  apply(rule someI_ex)
  using component_has_path_distinct .

lemma (in graph_abs) component_path'_works:
  assumes "C \<in> connected_components G" "\<And>v. v\<in>Vs G \<Longrightarrow> degree G v \<le> 2"
  shows "path G (component_path' G C)" "set (component_path' G C) = C" "distinct (component_path' G C)"
  using component_path'_works'[OF assms]
  by auto

lemma (in graph_abs) rev_component_path'_works:
  assumes "C \<in> connected_components G" "\<And>v. v\<in>Vs G \<Longrightarrow> degree G v \<le> 2"
  shows "path G (rev (component_path' G C))" "set (rev (component_path' G C)) = C"
        "distinct (rev (component_path' G C))"
  using component_path'_works[OF assms]
  by (auto intro: rev_path_is_path)

lemma component_edges_subset:
  shows "component_edges G C \<subseteq> G"
  by (auto simp: component_edges_def)

lemma edges_path_subset_edges:
  assumes "path G p" "set p \<subseteq> C"
  shows "set (edges_of_path p) \<subseteq> component_edges G C"
  using assms
  by (induction) (auto simp add: component_edges_def)

lemma degree_edges_of_path_ge_2_all:
  assumes "distinct p" "length p \<ge> 3" "v\<in>set p"
  shows "degree (set (edges_of_path (last p # p))) v \<ge> 2"
proof(cases "v = hd p \<or> v = last p")
  case True
  moreover obtain a a' a'' p' where p: "p = a # a' # a'' # p'"
    using assms(2)
    by(auto simp add: Suc_le_length_iff eval_nat_numeral)
  ultimately have "v = a \<or> v = last (a'' # p')"
    by auto
  moreover have "2 \<le> degree (set (edges_of_path (last p # p))) a"
  proof-
    have "last p \<noteq> a'" using assms(1) p by auto
    hence "{last p, a} \<noteq> {a, a'}" by (auto simp: doubleton_eq_iff)
    hence "2 \<le> degree {{last p, a}, {a, a'}} a"
      by (simp add: degree_insert eval_enat_numeral one_eSuc)
    moreover have "{{last p, a}, {a, a'}} \<subseteq> set (edges_of_path (last p # p))"
      by (simp add: p)
    ultimately show ?thesis
      using order.trans 
      by (force dest!: subset_edges_less_degree[where v = a])
  qed
  moreover have "2 \<le> degree (set (edges_of_path (last p # p))) (last (a'' # p'))"
  proof-
    obtain u where u: "{u, last (a'' # p')} \<in> set (edges_of_path (a' # a'' # p'))" "u \<in> set (a' # a'' # p')"
      by (elim exists_conj_elims, rule exE[OF last_in_edge]) force
    hence "{u, last (a'' # p')} \<noteq> {a, last (a'' # p')}"
      using assms(1) u
      by (auto simp add: p doubleton_eq_iff)
    hence "2 \<le> degree {{u, last (a'' # p')}, {a, last (a'' # p')}} (last (a'' # p'))"
      by (simp add: degree_insert eval_enat_numeral one_eSuc)
    moreover have "{{u, last (a'' # p')}, {a, last (a'' # p')}} \<subseteq> set (edges_of_path (last p # p))"
      using p u(1) by fastforce
    ultimately show ?thesis
      using order.trans
      by (fastforce dest!: subset_edges_less_degree[where v = "(last (a'' # p'))"])
  qed
  ultimately show ?thesis
    by fastforce
next
  case False
  hence "2 = degree (set (edges_of_path p)) v"
    by (simp add: assms(1) assms(3) degree_edges_of_path_ge_2)
  moreover have "set (edges_of_path p) \<subseteq> set (edges_of_path (last p # p))"
    by (cases p) fastforce+
  then show ?thesis
    by (simp add: \<open>2 = degree (set (edges_of_path p)) v\<close> subset_edges_less_degree)
qed

lemma all_edges_covered:
  assumes matchings: "matching M" "matching M'" and
    con_comp: "C \<in> connected_components (M \<oplus> M')" and
    more_M'_edges: "card (M' \<inter> (component_edges (M \<oplus> M') C)) > card (M \<inter> (component_edges (M \<oplus> M') C))" and
    doubleton_neq_edges: "\<And>e. e\<in>(M \<oplus> M') \<Longrightarrow> \<exists>u v. e = {u,v} \<and> u \<noteq> v" and
    finite_comp: "finite C" and
    finite_symm_diff: "finite (M \<oplus> M')"
  shows "component_edges (M \<oplus> M') C \<subseteq> set (edges_of_path (component_path' (M \<oplus> M') C))"
proof(cases "C ={}")
  case True
  then show ?thesis
    using assms
    unfolding component_edges_def component_path'_def
    by simp
next
  case C_nempty: False
  show ?thesis
  proof(cases "card C = 1")
    case True
    then obtain u where "C = {u}"
      using card_1_singletonE by blast
    then show ?thesis
      using assms
      unfolding component_edges_def component_path'_def
      by auto
  next
    case False
    then have comp_ge_2: "card C \<ge> 2"
      by (simp add: C_nempty Suc_leI finite_comp order_less_le eval_nat_numeral)
    interpret graph_abs "(M \<oplus> M')"
      using assms
      by (simp add: dblton_graphI finite_dbl_finite_verts graph_abs_def)

    show ?thesis
    proof(safe; rule ccontr)                                          
      fix e
      assume ass: 
        "e \<in> component_edges (M \<oplus> M') C"
        "e \<notin> set (edges_of_path (component_path' (M \<oplus> M') C))"
      define vs where "vs = (component_path' (M \<oplus> M') C)"
      define es where "es = (edges_of_path (component_path' (M \<oplus> M') C))"
      have doubleton_edges: "\<exists>u v. e = {u,v} \<and> u \<noteq> v" if "e\<in>(M \<oplus> M')" for e
        using doubleton_neq_edges that
        by fastforce
      have deg_le_2: "degree (M \<oplus> M') v \<le> 2" if "v\<in> Vs (M \<oplus> M')" for v
        using matchings
        by (simp add: degree_symm_diff)
      note finite_bla = finite_symm_diff
      note comp_works = component_path'_works[OF con_comp deg_le_2]
      show False    
      proof(cases "hd vs \<in> e \<and> last vs \<in> e")
        case T1: True
        moreover have "distinct vs"
          unfolding vs_def 
          using comp_ge_2
          by (auto intro!: comp_works)
        moreover have "length vs \<ge> 2"
          unfolding vs_def
          using comp_ge_2 card_length distinct_card[OF comp_works(3)]
          by (simp add: comp_works(2))
        ultimately have vpath_hd_neq_last: "hd vs \<noteq> last vs"
          by (auto simp: Suc_le_length_iff eval_nat_numeral split: if_splits)
        hence e: "e = {hd vs, last vs}"
          using doubleton_edges component_edges_subset ass(1) T1
          by fastforce
        show ?thesis
        proof(cases "(component_edges (M \<oplus> M') C = insert e (set es))")
          case T2: True
          have vs_ge2: "length vs \<ge> 2"
            using comp_ge_2 comp_works distinct_card
            by (fastforce simp: vs_def)
          define vs' where "vs' = (last vs # vs)"
          have *: "set (edges_of_path vs') = component_edges (M \<oplus> M') C"
            using vs_ge2
            by (auto simp: es_def e vs_def vs'_def T2 Suc_le_length_iff eval_nat_numeral)
          have horrid_lt_expr: 
            "length (filter (\<lambda>x. x \<in> M) (edges_of_path vs')) <
                length (filter (\<lambda>e. e \<in> M') (edges_of_path vs'))"
          proof-
            have "component_path' (M \<oplus> M') C \<noteq> []"
              using C_nempty comp_works(2)
              by fastforce
            hence "\<exists>v vs. component_path' (M \<oplus> M') C = v # vs"
              by(auto simp add: neq_Nil_conv)
            hence "distinct (edges_of_path vs')"
              using comp_works(3) ass(1,2) "*"
              by (auto simp: vs'_def vs_def e distinct_edges_of_vpath insert_absorb)
            hence "length (filter (\<lambda>x. x \<in> N) (edges_of_path vs')) = 
                     card (N \<inter> (component_edges (M \<oplus> M') C))"
              for N
              using *
              by (simp add: distinct_length_filter)
            then show ?thesis
              using more_M'_edges
              by auto
          qed
          moreover have horrid_eq_expr: "\<forall>x\<in>set (edges_of_path vs'). (x \<in> M') = (x \<notin> M)"
            using sym_diff_subset symm_diff_mutex component_edges_subset[where G = "M \<oplus> M'"]
            by (fastforce simp: *)
          moreover have "alt_list (\<lambda>e. e \<in> M') (\<lambda>e. e \<in> M) (edges_of_path vs')"
          proof-
            have "path (M \<oplus> M') (last vs # vs)"
            proof-
              obtain a l where l: "vs = a # l"
                using vs_ge2
                by (auto simp: Suc_le_length_iff eval_nat_numeral)
              show ?thesis
              proof(cases l)
                case Nil
                then show ?thesis 
                  using l comp_ge_2 comp_works
                  by (auto simp: vs_def)
              next
                case l': (Cons a' l')

                show ?thesis
                  using e 
                  apply(clarsimp simp add: l' l split: if_splits)
                  subgoal using \<open>e \<notin> set (edges_of_path (component_path' (M \<oplus> M') C))\<close> l l'
                    by (auto simp: vs_def)
                  subgoal apply(rule conjI)
                    subgoal using T2 component_edges_subset
                      by fastforce
                    subgoal using e ass l l' vs_def comp_works
                      by simp
                    done
                  done
              qed
            qed
            moreover have "distinct (edges_of_path vs)"
              by (simp add: component_path'_works(3) con_comp deg_le_2 distinct_edges_of_vpath
                            doubleton_edges finite_bla vs_def)
            hence "distinct (edges_of_path (last vs # vs))"
              using \<open>e \<notin> set (edges_of_path (component_path' (M \<oplus> M') C))\<close> e vs_ge2
              by (cases vs, auto simp: vs_def insert_commute)
            moreover with vs_ge2 
              have "alt_list (\<lambda>e. e \<in> M) (\<lambda>e. e \<in> M') (edges_of_path (last vs # vs)) \<or>
                 alt_list (\<lambda>e. e \<in> M') (\<lambda>e. e \<in> M) (edges_of_path  (last vs # vs))"
              by (intro calculation(1) matching_paths_alternate assms; simp add: vs_def )
            ultimately show ?thesis
              using alternating_list_gt_or horrid_eq_expr horrid_lt_expr vs'_def by blast
          qed
          ultimately have "hd (edges_of_path vs') \<in> M' \<and> last (edges_of_path vs') \<in> M'"
            by(intro alternating_list_gt; simp)
          moreover have "hd (edges_of_path vs') \<noteq> last (edges_of_path vs')"
            unfolding vs'_def
            apply(intro hd_edges_neq_last)
            using \<open>e \<notin> set (edges_of_path (component_path' (M \<oplus> M') C))\<close> e comp_works 
                  comp_ge_2 vpath_hd_neq_last
              by (auto simp: vs_def)
          moreover have "last vs' \<in> hd (edges_of_path vs')"
            using vs_ge2
            by (cases vs, auto simp add: vs'_def)
          moreover have "last vs' \<in> last (edges_of_path vs')"
            apply(subst rev_rev_ident[symmetric])
            apply(subst last_rev)
            apply(subst (3) rev_rev_ident[symmetric])
            apply(subst edges_of_path_rev)
            using vs_ge2
            by (auto simp add: vs'_def last_rev intro: hd_v_in_hd_e)
          ultimately have "degree M (last vs') \<ge> 2"
            using \<open>matching M'\<close>[unfolded matching_def2]            
            by fastforce
          then show ?thesis
            using degree_matching[OF \<open>matching M\<close>] not_eSuc_ilei0
            by (fastforce simp add: eval_enat_numeral one_eSuc dest: order_trans)
        next
          case F2: False
          show ?thesis
          proof(cases "card C \<ge> 3")
            case T3: True
            obtain e' where e': "e' \<in> component_edges (M \<oplus> M') C" "e' \<notin> insert e (set es)"
              using F2
              unfolding es_def
              using edges_path_subset_edges comp_works(1,2) ass(1)
              by blast
            obtain u v where uv: "e' = {u, v}" "v \<in> C"
              using e'(1)[unfolded component_edges_def] doubleton_edges
              by auto
            have "3 \<le> degree (insert e' (insert e (set es))) v"
            proof-
              have "degree (insert e (set es)) x \<ge> 2" if "x \<in> C" for x
              proof-
                have rw: "insert e (set es) = set (edges_of_path((last vs) # vs))"
                proof-
                  obtain a l where "vs = a # l"
                    using component_path'_works(2)[OF con_comp deg_le_2] 
                          uv(2)
                    by (cases vs, simp add: vs_def)
                  then show ?thesis
                    unfolding es_def vs_def e
                    by auto
                qed
                show ?thesis
                  using comp_works T3 distinct_card \<open>x \<in> C\<close>        
                  by (fastforce simp: rw vs_def intro!: degree_edges_of_path_ge_2_all)
              qed
              then have "degree (insert e (set es)) v \<ge> 2"
                using uv
                by simp
              moreover have "v \<in> e'"
                using uv(1) by force
              ultimately show ?thesis
                using e'(2)
                by (auto simp: degree_insert eval_enat_numeral)
            qed
            moreover have "(insert e' (insert e (set es))) \<subseteq> component_edges (M \<oplus> M') C"
              using ass(1) e' edges_path_subset_edges comp_works
              by (auto simp: es_def e vs_def)
            ultimately have "3 \<le> degree (component_edges (M \<oplus> M') C) v"
              using  order_trans
              by (fastforce dest!: subset_edges_less_degree)
            moreover have "(component_edges (M \<oplus> M') C) \<subseteq> (M \<oplus> M')"
              unfolding component_edges_def
              by auto
            ultimately have "3 \<le> degree (M \<oplus> M') v"
              using order_trans
              by (fastforce dest!: subset_edges_less_degree)
            then have "(3 :: enat) \<le> 2"
              using degree_symm_diff[OF matchings(1) matchings(2)] order_trans
              by fastforce
            then show False by simp
          next
            case F3: False
            then have C2: "card C = 2"
              using comp_ge_2
              by simp
            moreover obtain u v where uv: "C = {u, v}" "u \<noteq> v"
              using C2 
              by (auto simp add: eval_nat_numeral dest!: card_eq_SucD)
            moreover hence "e = {u,v}"
              using ass(1)[unfolded component_edges_def] e vpath_hd_neq_last
              by force
            ultimately have "component_edges (M \<oplus> M') C = {{u, v}}"
              using ass(1)[unfolded component_edges_def] doubleton_neq_edges
              by (auto simp: doubleton_eq_iff component_edges_def)
            moreover have "set (edges_of_path (component_path' (M \<oplus> M') C)) \<subseteq> component_edges (M \<oplus> M') C"
              by (simp add: comp_works(1,2) edges_path_subset_edges)
            ultimately have "False"
              using F2 ass(1) 
              by (simp add: es_def)
            then show ?thesis .
          qed
        qed
      next
        case False
        then obtain u v where "e = {u, v}"" v \<in> C"" u \<in> C" "u \<noteq> v"
          using ass(1)[unfolded component_edges_def] doubleton_neq_edges[of e]
          by fastforce
        moreover hence "(v \<noteq> hd vs \<and> v \<noteq> last vs) \<or> (u \<noteq> hd vs \<and> u \<noteq> last vs)"
          using False
          by auto
        ultimately obtain u v where uv: "e = {u, v}"" v \<in> C"" u \<in> C" "v \<noteq> hd vs" "v \<noteq> last vs"
          by auto
        have "3 \<le> degree (insert e (set es)) v"
        proof-
          have "2 = degree (set es) x" 
            if "x \<in> C" "x \<noteq> hd (component_path' (M \<oplus> M') C)" 
               "x \<noteq> last (component_path' (M \<oplus> M') C)"
            for x
          proof-
            have rw: "(set es) = set (edges_of_path(vs))"
              unfolding es_def vs_def
              by simp
            show ?thesis
              unfolding rw vs_def
              using comp_works that
              by (fastforce intro: degree_edges_of_path_ge_2)
          qed
          then have "degree (set es) v \<ge> 2"
            using uv
            by (simp add: vs_def)
          moreover have "v \<in> e"
            using uv(1) by force
          ultimately show ?thesis
            using degree_insert ass(2) es_def
            by(auto simp add: eval_enat_numeral degree_insert)
        qed
        moreover have "(insert e (set es)) \<subseteq> component_edges (M \<oplus> M') C"
          using ass(1) edges_path_subset_edges comp_works
          by (auto simp: es_def vs_def)
        ultimately have "3 \<le> degree (component_edges (M \<oplus> M') C) v"
          by (fastforce dest!: subset_edges_less_degree dest: order.trans)
        moreover have "(component_edges (M \<oplus> M') C) \<subseteq> (M \<oplus> M')"
          by (auto simp: component_edges_def)
        ultimately have "3 \<le> degree (M \<oplus> M') v"          
          by (fastforce dest!: subset_edges_less_degree dest: order.trans)
        moreover have "degree (M \<oplus> M') v \<le> 2"
          by (force intro!: deg_le_2 con_comp connected_comp_verts_in_verts uv(2))
        ultimately show False
          by (auto simp add: eval_enat_numeral one_eSuc dest: order.trans)
      qed
    qed
  qed
qed

lemma all_edges_covered_eq:
  assumes matchings: "matching M" "matching M'" and
    con_comp: "C \<in> connected_components (M \<oplus> M')" and
    more_M'_edges: "card (M' \<inter> (component_edges (M \<oplus> M') C)) > card (M \<inter> (component_edges (M \<oplus> M') C))" and
    doubleton_neq_edges: "\<And>e. e\<in>(M \<oplus> M') \<Longrightarrow> \<exists>u v. e = {u,v} \<and> u \<noteq> v" and
    finite_comp: "finite C" and
    finite_symm_diff: "finite (M \<oplus> M')"
  shows "component_edges (M \<oplus> M') C = set (edges_of_path (component_path' (M \<oplus> M') C))"
proof-
    interpret graph_abs "(M \<oplus> M')"
      using assms
      by (simp add: dblton_graphI finite_dbl_finite_verts graph_abs_def)
    show ?thesis  
      using assms
      apply(intro equalityI edges_path_subset_edges all_edges_covered assms component_path'_works)
      subgoal
        by auto
      subgoal by (auto simp add: degree_symm_diff matchings(1) matchings(2))
      subgoal apply (intro equalityD1 component_path'_works(2) assms)
        subgoal by (simp add: degree_symm_diff matchings(1) matchings(2))
        done
  done
qed

lemma con_comp_card_2:
  assumes con_comp: "C \<in> connected_components G"
  assumes finite_comp: "finite C"
  assumes doubleton_edges: "\<And>e. e\<in>G \<Longrightarrow> \<exists>u v. e = {u, v} \<and> u \<noteq> v"
  shows "card C \<ge> 2"
proof-
  obtain X where "X \<in> C" "X \<in> Vs G"
    using con_comp connected_comp_nempty connected_component_subs_Vs by blast
  then obtain F where "F \<in> G" "X \<in> F" unfolding Vs_def by blast
  then obtain Y where "X \<noteq> Y" "F = {X, Y}" using doubleton_edges by force
  hence "Y \<in> C"
    using \<open>F \<in> G\<close> \<open>X \<in> C\<close> con_comp 
    by (fastforce intro: in_connected_componentI4 dest: edges_are_walks)
  show "card C \<ge> 2"
    using finite_comp \<open>X \<in> C\<close> \<open>X \<noteq> Y\<close> \<open>Y \<in> C\<close>
    by(auto simp: eval_nat_numeral not_less_eq_eq[symmetric] dest: card_le_Suc0_iff_eq)
qed

lemma matching_augmenting_path_exists_1_1_1:
  assumes matchings: "matching M" "matching M'" and
    con_comp: "C \<in> connected_components (M \<oplus> M')" and
    more_M'_edges: "card (M' \<inter> (component_edges (M \<oplus> M') C)) > card (M \<inter> (component_edges (M \<oplus> M') C))" and
    doubleton_edges: "\<And>e. e\<in>(M \<oplus> M') \<Longrightarrow> \<exists>u v. e = {u, v} \<and> u \<noteq> v" and 
    finite_comp: "finite C" and
    finite_symm_diff: "finite (M \<oplus> M')" and 
    comp_edges_contained: "set (edges_of_path (component_path' (M \<oplus> M') C)) = component_edges (M \<oplus> M') C"
  shows "alt_list (\<lambda>e. e \<in> M') (\<lambda>e. e \<in> M) (edges_of_path (component_path' (M \<oplus> M') C))" (is ?g1)
        "hd (edges_of_path (component_path' (M \<oplus> M') C)) \<in> M' \<and>
         last (edges_of_path (component_path' (M \<oplus> M') C)) \<in> M'" (is ?g2)
proof-
  note comp_ge_2 = con_comp_card_2[OF con_comp finite_comp doubleton_edges]

  define vs where "vs = (component_path' (M \<oplus> M') C)"
  then have *: "set (edges_of_path vs) = component_edges (M \<oplus> M') C"
    using comp_edges_contained
    by simp
  have deg_le_2: "\<And>v. v\<in>Vs (M \<oplus> M') \<Longrightarrow> degree (M \<oplus> M') v \<le> 2"
    using matchings
    by (simp add: degree_symm_diff)
  note finite_bla = finite_symm_diff
  interpret graph_abs "(M \<oplus> M')"
    using assms
    by (simp add: dblton_graphI finite_dbl_finite_verts graph_abs_def)

  note comp_works = component_path'_works[OF con_comp deg_le_2]
  have vs_ge2: "length vs \<ge> 2"
    using comp_ge_2 comp_works
    unfolding vs_def
    using distinct_card by fastforce
  have horrid_lt_expr: "length (filter (\<lambda>x. x \<in> M) (edges_of_path vs)) < length (filter (\<lambda>e. e \<in> M') (edges_of_path vs))"
  proof-
    have "distinct (edges_of_path vs)"
      by (auto simp: vs_def intro!: comp_works distinct_edges_of_vpath)
    then have "length (filter (\<lambda>x. x \<in> N) (edges_of_path vs)) = card (N \<inter> (component_edges (M \<oplus> M') C))"
      for N
      by (simp add: distinct_length_filter *)
    then show ?thesis
      using more_M'_edges
      by auto
  qed
  moreover have "e \<in> M \<oplus> M'" "e \<in> M \<union> M'"
    if "e \<in> component_edges (M \<oplus> M') C"
    for e
    using component_edges_subset sym_diff_subset that
    by fastforce+
  hence M_M'_comp: "\<forall>x\<in>set (edges_of_path vs). (x \<in> M') = (x \<notin> M)"
    by(auto dest!: symm_diff_mutex simp: *)
  moreover have "alt_list (\<lambda>e. e \<in> M') (\<lambda>e. e \<in> M) (edges_of_path vs)"
  proof-
    have "path (M \<oplus> M') (vs)"
      unfolding vs_def
      using comp_works
      by simp
    moreover with vs_ge2
    have "alt_list (\<lambda>e. e \<in> M) (\<lambda>e. e \<in> M') (edges_of_path vs) \<or>
             alt_list (\<lambda>e. e \<in> M') (\<lambda>e. e \<in> M) (edges_of_path  vs)"
      using component_path'_works(3)[OF con_comp deg_le_2]
      by (intro matching_paths_alternate assms) (simp add: vs_def distinct_edges_of_vpath)+
    ultimately show ?thesis
      using *
      using alternating_list_gt_or M_M'_comp horrid_lt_expr by blast
  qed
  thus ?g1 
    by (auto simp: vs_def)
  ultimately show ?g2
    by(intro alternating_list_gt) (simp add: vs_def)+
qed

lemma matching_augmenting_path_exists_1_1:
  assumes matchings: "matching M" "matching M'" and
    con_comp: "C \<in> connected_components (M \<oplus> M')" and
    more_M'_edges: "card (M' \<inter> (component_edges (M \<oplus> M') C)) > card (M \<inter> (component_edges (M \<oplus> M') C))" and
    doubleton_edges: "\<And>e. e\<in>M\<oplus>M' \<Longrightarrow> \<exists>u v. e = {u,v} \<and> u \<noteq> v" "\<And>e. e\<in>M \<Longrightarrow> \<exists>u v. e = {u,v} \<and> u \<noteq> v" and 
    finite_comp: "finite C" and
    finite_symm_diff: "finite (M \<oplus> M')" and 
    comp_edges_contained: "set (edges_of_path (component_path' (M \<oplus> M') C)) = component_edges (M \<oplus> M') C"
  shows "matching_augmenting_path M (component_path' (M \<oplus> M') C)"
proof-
  interpret graph_abs "(M \<oplus> M')"
    using assms
    by (simp add: dblton_graphI finite_dbl_finite_verts graph_abs_def)

  note comp_ge_2 = con_comp_card_2[OF con_comp finite_comp doubleton_edges(1)]

  have deg_le_2: "\<And>v. v\<in>Vs (M \<oplus> M') \<Longrightarrow> degree (M \<oplus> M') v \<le> 2"
    using matchings
    by (simp add: degree_symm_diff)
  note finite_bla = finite_symm_diff
  define vs where "vs = (component_path' (M \<oplus> M') C)"
  then have f1: "alt_list (\<lambda>e. e \<in> M') (\<lambda>e. e \<in> M) (edges_of_path vs)" and
    f2: "hd (edges_of_path vs) \<in> M'" "last (edges_of_path vs) \<in> M'"
    using matching_augmenting_path_exists_1_1_1[OF assms(1-5,7-9), unfolded vs_def]
    by auto
  have *:"hd vs \<notin> Vs M"
    if 
      ass: "path (M \<oplus> M') (vs)"
      "set vs = C"
      "distinct vs"
      "edges_of_path vs = es"
      "alt_list (\<lambda>e. e \<in> M') (\<lambda>e. e \<in> M) es"
      "set es = component_edges (M \<oplus> M') C"
    for vs es
  proof(rule ccontr)
    obtain u v vs' where uv[simp]: "vs = u # v # vs'"
      using ass more_M'_edges nat_neq_iff
      apply(elim edges_of_path.elims)
      by auto
    assume "\<not> hd vs \<notin> Vs M"
    then have "hd vs \<in> Vs M" by simp
    then obtain w e where we[simp]: "e = {w, u}" "e \<in> M"
      using doubleton_edges
      by (force simp add: insert_commute Vs_def)
    show False
    proof(cases "e \<in> M'")
      case T1: True
      then have "w = v"
        using ass(4,5) matchings(2)
        by (fastforce elim: matchingE simp add: alt_list_step doubleton_eq_iff)
      moreover have "{u,v} \<in> (M \<oplus> M')"
        using ass(1)
        by (simp add: vs_def)
      ultimately show ?thesis
        using we(2) T1
        by (simp add: insert_commute symmetric_diff_def)
    next
      case F1 :False
      then have "e \<in> (M \<oplus> M')"
        using we
        by (simp add: symmetric_diff_def)
      hence "e \<in> component_edges (M \<oplus> M') C"
        using ass(2) in_con_comp_insert[where v = w and G = "(M \<oplus> M')" and u = u]
          connected_components_closed''[OF con_comp]
        by (auto simp add: insert_absorb insert_commute component_edges_def)
      hence "e \<in> set (edges_of_path vs)"
        using ass 
        by simp
      hence "w = v"
        using ass(3)
        by (fastforce dest: v_in_edge_in_path_gen)
      then show ?thesis
        using F1 ass(4,5)
        by (auto simp add: alt_list_step insert_commute)
    qed    
  qed
  have "alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path vs)"
    using comp_edges_contained component_edges_subset contra_subsetD
    by (force simp add: vs_def dest!: symm_diff_mutex intro!: alt_list_cong_2[OF f1])
  moreover have "hd vs \<notin> Vs M"
    using *[OF component_path'_works[OF con_comp deg_le_2] _ f1[unfolded vs_def] comp_edges_contained]
    by (auto simp: vs_def)
  moreover have "last vs \<notin> Vs M"
  proof-
    have "edges_of_path vs \<noteq> []"
      using  comp_edges_contained more_M'_edges 
      by (auto simp: vs_def)
    hence "alt_list (\<lambda>e. e \<in> M') (\<lambda>e. e \<in> M) (edges_of_path (rev vs))"
      using comp_edges_contained[symmetric] component_edges_subset f1 f2(2) 
      by (force simp: edges_of_path_rev[symmetric] vs_def
          dest: symm_diff_mutex alternating_list_even_last
          intro: alt_list_rev f2 f1)+
    hence "hd (rev vs) \<notin> Vs M"
      by (intro *[unfolded vs_def[symmetric]]
          rev_component_path'_works[OF con_comp deg_le_2,
                                       unfolded vs_def[symmetric]])
        (auto simp add: edges_of_path_rev[symmetric] comp_edges_contained vs_def)+
    then show ?thesis
      by (simp add: hd_rev)
  qed
  moreover have "2 \<le> length (component_path' (M \<oplus> M') C)"
    using component_path'_works(2,3)[OF con_comp deg_le_2]
      comp_ge_2
    by (fastforce dest: distinct_card)
  ultimately show ?thesis
    using component_path'_works(1)[OF con_comp deg_le_2]
    by (auto simp: matching_augmenting_path_def vs_def)
qed

lemma matching_augmenting_path_exists_1:
  assumes matchings: "matching M" "matching M'" and
    con_comp: "C \<in> connected_components (M \<oplus> M')" and
    more_M'_edges: 
      "card (M' \<inter> (component_edges (M \<oplus> M') C)) > card (M \<inter> (component_edges (M \<oplus> M') C))" and
    doubleton_neq_edges: "\<And>e. e\<in>(M \<oplus> M') \<Longrightarrow> \<exists>u v. e = {u,v} \<and> u \<noteq> v"
                         "\<And>e. e\<in>M \<Longrightarrow> \<exists>u v. e = {u, v} \<and> u \<noteq> v" and
    finite_comp: "finite C" and
    finite_symm_diff: "finite (M \<oplus> M')"
  shows "graph_augmenting_path (M \<oplus> M') M (component_path' (M \<oplus> M') C)" (is "?g1 \<and> ?g2 \<and> ?g3")
proof(intro conjI)
  have deg_le_2: "\<And>v. v\<in>Vs (M \<oplus> M') \<Longrightarrow> degree (M \<oplus> M') v \<le> 2"
    using matchings
    by (simp add: degree_symm_diff)
  note finite_bla = finite_symm_diff
  interpret graph_abs "(M \<oplus> M')"
    using assms
    by (simp add: dblton_graphI finite_dbl_finite_verts graph_abs_def)

  have doubleton_edges: "\<And>e. e\<in>(M \<oplus> M') \<Longrightarrow> \<exists>u v. e = {u, v} \<and> u \<noteq> v"
    by (simp add: doubleton_neq_edges)
  have "card C \<noteq> 1"
  proof(rule ccontr; subst (asm) not_not)
    assume ass: "card C = 1"
    then obtain v where v: "C = {v}"
      by(fastforce elim: card_1_singletonE)
    moreover have C_nempty: "C \<noteq> {}" 
      by (simp add: v)
    ultimately have lv: "(component_path' (M \<oplus> M') C) = [v]"
      using component_path'_works(2,3)[OF con_comp deg_le_2]
      by (simp add: distinct_singleton_set)
    obtain e where e: "e \<in> (M \<oplus> M')" "v \<in> e"
      using con_comp v
      by (force simp add: connected_components_def connected_component_def Vs_def)
    then obtain u where u: "e = {u, v}" "u \<noteq> v"
      using doubleton_neq_edges(1) e by fastforce
    moreover have "u \<in> connected_component (M \<oplus> M') v"
      using e(1)
      by (auto simp: insert_commute u(1) intro!: in_connected_componentI edges_reachable)
    moreover have "C = connected_component (M \<oplus> M') v"
      using con_comp 
      by (auto simp: connected_components_closed' v)
    ultimately show False using v by auto
  qed
  have C_nempty: "C \<noteq> {}"
    using con_comp
    by (fastforce simp add: connected_components_def connected_component_def intro!: ccontr[where P = "_ = [] "])+
  have comp_ge_2: "card C \<ge> 2"
    using \<open>card C \<noteq> 1\<close> C_nempty 
    by (simp add: empty_iff_card_0[OF \<open>finite C\<close>])
  then show ?g3
    using matching_augmenting_path_exists_1_1(1)[OF assms]
          all_edges_covered_eq(1)[symmetric, OF assms(1,2,3,4,5) finite_comp finite_symm_diff]
    by auto
  interpret graph_abs "(M \<oplus> M')"
    using assms
    by (simp add: dblton_graphI finite_dbl_finite_verts graph_abs_def)

  show ?g1 ?g2
    using matchings
    by (auto intro!: component_path'_works[OF assms(3) degree_symm_diff])
qed

lemma finite_con_comps:
  "finite (Vs G) \<Longrightarrow> finite (connected_components G)"
  by (auto simp: connected_components_def)

lemma Berge_1:
  assumes finite: "finite M" "finite M'" and
    matchings: "matching M" "matching M'" and
    lt_matching: "card M < card M'" and
    doubleton_neq_edges: 
      "\<And>e. e\<in>(M \<oplus> M') \<Longrightarrow> \<exists>u v. e = {u,v} \<and> u \<noteq> v"
      "\<And>e. e\<in>M \<Longrightarrow> \<exists>u v. e = {u, v} \<and> u \<noteq> v"
  shows "\<exists>p. matching_augmenting_path M p \<and> path (M \<oplus> M') p \<and> distinct p"
proof-
  have finite_symm_diff: "finite (M \<oplus> M')"
    using finite
    by (simp add: finite_symm_diff)
  then have finiteVs: "finite (Vs (M \<oplus> M'))"
    using doubleton_neq_edges(1)
    by(auto simp: Vs_def)
  have "\<And>e. e\<in>M \<oplus> M' \<Longrightarrow> \<exists>u v. e = {u, v}"
    using doubleton_neq_edges
    by fastforce
  then obtain C where 
    con_comp:
      "C \<in> connected_components (M \<oplus> M')" and
    more_M'_edges:
      "card (M' \<inter> (component_edges (M \<oplus> M') C)) > card (M \<inter> (component_edges (M \<oplus> M') C))"
    using one_unbalanced_comp_edges[OF finite(1) lt_matching finite_con_comps[OF finiteVs]]
    by (auto simp add: inf_commute components_edges_def)
  moreover have finite_comp: "finite C"
    using finiteVs connected_component_subs_Vs[OF con_comp]
    by (auto intro: rev_finite_subset)
  moreover note finite_symm_diff
  ultimately have "graph_augmenting_path (M \<oplus> M') M (component_path' (M \<oplus> M') C)"
    by(intro matching_augmenting_path_exists_1 assms; auto)+
  then show ?thesis
    by auto
qed

subsection\<open>Direction 2 of Berge\<close>

text\<open>An augmenting path can be used to construct a larger matching.\<close>

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

lemma last_edge_in_last_vert_in:
  assumes "length p \<ge> 2" "last (edges_of_path p) \<in> G"
  shows "last p \<in> Vs G"
  using Vs_def assms last_v_in_last_e by fastforce

lemma hd_edge_in_hd_vert_in:
  "\<lbrakk>length p \<ge> 2; hd (edges_of_path p) \<in> G\<rbrakk> \<Longrightarrow> hd p \<in> Vs G"
  using Vs_def hd_v_in_hd_e
  by fastforce

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

lemma new_matching_bigger:
  assumes "matching_augmenting_path M p"
  assumes "distinct p"
  assumes "finite M"
  shows "card M < card (M \<oplus> set (edges_of_path p))"
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
  then show ?thesis
    using condition_for_greatness[OF _ assms(3)]
    by simp
qed

lemma Berge_2:         
  assumes aug_path: "matching_augmenting_path M p" "M \<subseteq> G" "path G p" "distinct p" and
    finite: "finite M" and
    matchings: "matching M"
  shows "matching (M \<oplus> set (edges_of_path p))" (is ?g1)
        "card M < card (M \<oplus> set (edges_of_path p))" (is ?g2)
        "(M \<oplus> set (edges_of_path p)) \<subseteq> G" (is ?g3)
proof-
  show ?g1
    by (auto intro: symm_diff_is_matching assms simp: aug_path[unfolded matching_augmenting_path_def])
  show ?g2
    by (intro new_matching_bigger assms)
  show ?g3
    using path_edges_subset sym_diff_subset aug_path(2,3)
    by force
qed

theorem Berge:
  assumes matching: "finite M" "matching M" "M \<subseteq> G" and
    graph: "dblton_graph G" "finite (Vs G)"
  shows "(\<exists>p. matching_augmenting_path M p \<and> path G p \<and> distinct p) =
            (\<exists>M' \<subseteq> G. matching M' \<and> card M < card M')"
proof
  assume "\<exists>p. matching_augmenting_path M p \<and> path G p \<and> distinct p"
  then obtain p where "matching_augmenting_path M p" "path G p" "distinct p"
    by blast
  then obtain M' where "M' \<subseteq> G" "matching M'" "card M < card M'"
    using Berge_2 matching
    by metis
  then show "\<exists>M'\<subseteq>G. matching M' \<and> card M < card M'"
    by blast
next
  assume "\<exists>M'\<subseteq>G. matching M' \<and> card M < card M'"
  then obtain M' where M': "M' \<subseteq> G" "matching M'" "card M < card M'"
    by blast
  then have finiteM': "finite M'"
    using card.infinite by force
  have MM'_subset: "M \<oplus> M' \<subseteq> G"
    using sym_diff_subset matching(3) M'(1)
    by fast
  have "\<And>e. e \<in> M \<oplus> M' \<Longrightarrow> \<exists>u v. e = {u,v} \<and> u \<noteq> v"
    using MM'_subset graph(1) by (blast elim: dblton_graphE)
  moreover have "\<And>e. e \<in> M \<Longrightarrow> \<exists>u v. e = {u,v} \<and> u \<noteq> v"
    using matching(3) graph(1)
    by (blast elim: dblton_graphE)
  ultimately obtain p where "matching_augmenting_path M p" "path (M \<oplus> M') p" "distinct p"
    using Berge_1[OF matching(1) finiteM' matching(2) M'(2, 3)]
    by blast
  moreover then have "path G p"
    using path_subset MM'_subset
    by blast
  ultimately show "\<exists>p. matching_augmenting_path M p \<and> path G p \<and> distinct p"
    by auto
qed

abbreviation "graph_matching G M \<equiv> matching M \<and> M \<subseteq> G"

lemma laterally_transfer_aug_path':
  assumes "card M = card M'"
  assumes matching: "graph_matching G M'" "finite M'"
  assumes matching': "graph_matching G M" "finite M" 
  assumes graph: "dblton_graph G" "finite (Vs G)"
  assumes graph_augmenting_path: "graph_augmenting_path G M p"
  obtains q where "graph_augmenting_path G M' q"
proof-
  from graph_augmenting_path
  obtain N where N_def: "N \<subseteq> G" "matching N" "card M < card N" using Berge matching' graph by metis
  hence "card M' < card N" using assms(1) by linarith
  then obtain q where "graph_augmenting_path G M' q" using Berge matching graph N_def(1, 2) by metis
  then show ?thesis using that by simp
qed

lemma laterally_transfer_aug_path:
  assumes "card M = card M'"
  assumes matching: "graph_matching G M'" "finite M'"
  assumes matching': "graph_matching G M" "finite M" 
  assumes graph: "dblton_graph G" "finite (Vs G)"
  shows "(\<exists>p. graph_augmenting_path G M p) \<longleftrightarrow> (\<exists>p. graph_augmenting_path G M' p)"
proof-
  from assms(1) have card': "card M' = card M" by simp
  show ?thesis
    using laterally_transfer_aug_path'[OF assms(1) matching matching' graph]
          laterally_transfer_aug_path'[OF card' matching' matching graph]
    by metis
qed

locale graph_matching_defs =
  graph_defs +
  fixes M :: "'a set set"

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

end