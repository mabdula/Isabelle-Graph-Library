theory Compute_Alt_Path_Invars
  imports Blossom_Prefixes Basic_Matching.Alternating_Forest_Spec Graph_Matching_Specs
    Data_Structures.Fixed_Univ_Set_Specs
begin

provenance ai_human

section \<open>Alternating forest search\<close>

locale compute_alt_path =
  match G M +
  alternating_forest_ordinary_extension_spec
    where abstract_forest = abstract_forest and evens = evens
  for abstract_forest :: "'F \<Rightarrow> 'a set set"
    and evens :: "'F \<Rightarrow> 'vset"
    and G M :: "'a set set"
begin

notation abstract_forest ("\<lbrace> _ \<rbrace>")
abbreviation "aevens F \<equiv> vset_to_set (evens F)"
abbreviation "aodds F \<equiv> vset_to_set (odds F)"
abbreviation "aroots F \<equiv> vset_to_set (roots F)"
abbreviation "FVs F \<equiv> Vs (\<lbrace>F\<rbrace>)"

definition "if1_cond F =
      (\<exists>v1 v2. {v1, v2} \<in> G - \<lbrace>F\<rbrace> \<and> v1 \<in> aevens F \<and> v2 \<notin> FVs F \<and> (\<exists>v3. {v2, v3} \<in> M))"

definition if1 where (*I am using this because when the RHS is in the function the function package messes up the pairing.*)
  "if1 F v1 v2 v3 = ({v1, v2} \<in> G - \<lbrace>F\<rbrace> \<and> v1 \<in> aevens F \<and> v2 \<notin> FVs F \<and> {v2, v3} \<in> M)"

interpretation matching_graph: graph_abs M
  apply(unfold_locales)
  using graph_invar_subset[OF graph matching(2)] .

definition if2_cond where "if2_cond F =
   (\<exists>v1 v2. {v1, v2} \<in> G \<and> v1 \<in> aevens F \<and> v2 \<in> aevens F)"

definition if2 where
  "if2 F v1 v2 = ({v1, v2} \<in> G \<and> v1 \<in> aevens F \<and> v2 \<in> aevens F)"

lemma if1_cond_props:
  "if1_cond F \<Longrightarrow> (\<exists>v1 v2. {v1, v2} \<in> G - \<lbrace>F\<rbrace> \<and> v1 \<in> aevens F \<and> v2 \<notin> FVs F \<and> (\<exists>v3. {v2, v3} \<in> M))"
  unfolding if1_cond_def
  .

lemma if1_cond_props':
  "if1_cond F \<Longrightarrow> (\<exists>v1 v2 v3. if1 F v1 v2 v3)"
  unfolding if1_cond_def if1_def by simp

lemma if2_cond_props:
  "if2_cond F \<Longrightarrow> (\<exists>v1 v2. {v1, v2} \<in> G \<and> v1 \<in> aevens F \<and> v2 \<in> aevens F)"
  unfolding if2_cond_def if2_def
  .

lemma if1_props:
  assumes "if1 F v1 v2 v3"
  shows
    "{v1, v2} \<in> G - \<lbrace>F\<rbrace>" "v1 \<in>  aevens F" "v2 \<notin> FVs F" "{v2, v3} \<in> M"
  using assms
  unfolding if1_def
  by auto

lemma if_1_forest_extension_precond:
  "\<lbrakk>forest_invar M F; if1 F v1 v2 v3\<rbrakk> \<Longrightarrow> forest_extension_precond F M v1 v2 v3"
proof(unfold forest_extension_precond_def, intro conjI, goal_cases)
  case 3
  then show ?case
    using  evens_and_odds(3)[of M F] higher_forest_properties(2)[of M F v2 v3]
    by(auto simp add: if1_def)
next
  case 4
  then show ?case
    using evens_and_odds(3)[of M F] higher_forest_properties(2)[of M F v1 v2]
    by(auto simp add: if1_def)
next
  case 7
  then show ?case
    by (simp add: graph_abs.edge_iff_edge_1 graph_abs_axioms if1_def no_self_loops_2)
next
  case 8
  then show ?case
    using if1_props(4) by fastforce
next
  case 9
  then show ?case
    using
        evens_and_odds(3)[of M F] higher_forest_properties(2)[of M F v1 v2]
    by(auto simp add: if1_def insert_commute)
qed (simp_all add: if1_props  matching(1))

lemma forest_paths_sound:
  assumes "forest_invar M F" "abstract_forest F \<subseteq> G"
    "{v1, v2} \<in> G" "v1 \<in> aevens F" "v2 \<in> aevens F"
    "p1 = get_path F v1" "p2 = get_path F v2"
  shows "compute_alt_path_spec G M (Some (p1, p2))"
proof-
  have s: "v1 \<in> aevens F" "p1 = get_path F v1"
    "v2 \<in> aevens F" "p2 = get_path F v2" "{v1, v2} \<in> G"
    using assms by auto
    note p1_props = get_path[OF assms(1) s(1,2)]
    note p2_props = get_path[OF assms(1) s(3,4)]
    have v1v2_not_in_M: "{v1, v2} \<notin> M"
    proof(rule ccontr, goal_cases)
      case 1
      have "{v1, v2} \<inter> (FVs F \<union> vset_to_set (roots F)) \<noteq> {}"
        using assms(1) evens_and_odds(3) s(1) by auto
      hence "{v1, v2} \<in> \<lbrace> F \<rbrace>"
        using higher_forest_properties(2)[OF assms(1), of v1 v2] 1 by auto
      thus False
        using higher_forest_properties(3)[OF assms(1), of v1 v2]
              assms(1) evens_and_odds(4) s(1,3)
        by auto
    qed
    have hds: "v1 = hd p1" "v2 = hd p2"
      using get_path[OF assms(1), of v1 p1] get_path[OF assms(1), of v2 p2] s walk_reflexive'
      by(unfold walk_betw_def) force+
    hence "hd p1 \<noteq> hd p2" "{hd p1, hd p2} \<in> G"
      using edge_iff_edge_1 no_self_loops_2 s(5) by presburger+
    moreover have "\<lbrakk>p1 = pref1 @ x # post1; p2 = pref2 @ x # post2\<rbrakk>\<Longrightarrow> post1 = post2"
      for x pref1 post1 pref2 post2
      by(auto intro!: get_path_prefices[OF assms(1), of pref1 x post1 v1 pref2 post2 v2]
              simp add: s(2,4))
    moreover have "last p1 \<notin> Vs M" "odd (length p1)" "distinct p1"
      using p1_props roots(3)[OF assms(1)]
      by auto
    moreover have "path G p1"
      using edges_are_Vs[OF s(5)] p1_props roots(3)[OF assms(1)] graph_abs_axioms assms(2)
      by(cases "p1 = [v1]")
        (auto intro: path_subset[of "\<lbrace>F\<rbrace>" _ G]
                     graph_abs.walk_between_nonempty_path'(1)[of "\<lbrace>F\<rbrace>"] graph_abs_subset)
    moreover have "last p2 \<notin> Vs M" "odd (length p2)" "distinct p2"
      using p2_props roots(3)[OF assms(1)]
      by auto
    moreover have "path G p2"
      using edges_are_Vs_2[OF s(5)] p2_props roots(3)[OF assms(1)] graph_abs_axioms assms(2)
      by(cases "p2 = [v2]")
        (auto intro: path_subset[of "\<lbrace>F\<rbrace>" _ G]
                     graph_abs.walk_between_nonempty_path'(1)[of "\<lbrace>F\<rbrace>"] graph_abs_subset)
    moreover have "alt_path M (hd p1 # p2)"
      using hds v1v2_not_in_M p2_props
      by(auto intro!: nin_M_alt_path)
    moreover have "alt_path M (hd p2 # p1)"
      using hds v1v2_not_in_M p1_props
      by(auto intro!: nin_M_alt_path simp add: insert_commute)
    ultimately show ?thesis
      by (auto simp: compute_alt_path_spec_def)
qed

lemma finial_forest_evens'_Neighbourhood:
  assumes "\<not> if1_cond F" "\<not> if2_cond F" "forest_invar M F" "Vs G - Vs M \<subseteq> aevens F" "\<lbrace>F\<rbrace> \<subseteq> G"
  shows "Neighbourhood G (aevens F) = aodds F"
proof((rule equalityI; rule subsetI; (elim in_NeighbourhoodE)?), goal_cases)
  case (1 x y)
  then show ?case
  proof(cases "{x, y} \<in> \<lbrace> F \<rbrace>", goal_cases)
    case 1
    then show ?case
      using  assms(3) higher_forest_properties(3)[of M F y x]
      by (auto simp add: insert_commute)
  next
    case 2
    then show ?case
    proof(cases "x \<in> FVs F", goal_cases)
      case 1
      then show ?case
        using assms(3) evens_and_odds(3) by auto
    next
      case 2
      then show ?case
      proof(cases "\<exists>v3. {x, v3} \<in> M", goal_cases)
        case 1
        then show ?case
         using assms(1) by(auto simp add: if1_cond_def)
      next
        case 2
        moreover hence "x \<in> Vs G - Vs M"
         using matching(2)
         by (auto simp add:  graph_abs.vs_member'[OF  graph_abs_subset] insert_commute)
       ultimately have False
         using assms(4) by auto
       thus ?case
         by simp
     qed
   qed
 qed
next
  case (2 x)
  hence "x \<in> Vs \<lbrace>F\<rbrace>"
    using evens_and_odds(3,4)[OF assms(3)] roots(2)[OF assms(3)]
    by auto
  then obtain e where e: "e \<in> \<lbrace>F\<rbrace>" "x \<in> e"
    by(auto elim!: vs_member_elim)
  obtain y where y: "{x, y} \<in> \<lbrace>F\<rbrace>" "x \<noteq> y"
  proof(rule Undirected_Set_Graphs.dblton_graphE[OF dblton_graph_subset[OF conjunct1[OF graph] assms(5)] e(1)], goal_cases)
    case 1
    thus ?case
    using e
    by (auto simp add: insert_commute)+
  qed
  hence "y \<in> aevens F"
    using "2"  higher_forest_properties(3)[OF assms(3), of y x]
    by(auto simp add: insert_commute)
  moreover have "x \<notin> aevens F"
    using "2" assms(3) evens_and_odds(4) by blast
  moreover have "{x, y} \<in> G"
    using assms(5) y(1) by blast
  ultimately show ?case
    by(auto intro!: in_NeighbourhoodI simp add: insert_commute)
qed

lemma termination_conditions_alt_paths_alternating_labels:
  assumes  "\<not> if1_cond F" "\<not> if2_cond F" "forest_invar M F" "Vs G - Vs M \<subseteq> aevens F"
       "alt_path M (p1)" "length (p1) \<ge> 1" "hd (p1) \<notin> Vs M"
        "l = length p1" "set (p1) \<subseteq> Vs G" "set (edges_of_path p1) \<subseteq> G"
  shows "alt_list (\<lambda> x. x \<in> aevens F) (\<lambda> x. x \<in> aodds F) p1"
  using assms(5-)
proof(induction l arbitrary: p1 rule: less_induct)
  case (less l)
  show ?case
  proof(cases l)
    case 0
    then show ?thesis
      by (simp add: alt_list_empty less.prems(4))
  next
    case (Suc ll)
    note suc = Suc
    then obtain p11 x where p1_split_off_last:"p1 = p11@[x]"
      using less.prems(4) by(cases p1 rule: rev_cases) auto
    show ?thesis
    proof(cases ll)
      case 0
      hence p1_is:"p1 = [x]" and "x \<notin> Vs M" "x \<in> Vs G"
        using less.prems(3,4,5) p1_split_off_last suc by auto
      hence "x \<in> aevens F"
        using assms(4) less(6) p1_is by auto
      then show ?thesis
        by(auto simp add: p1_is intro!: alt_list.intros)
    next
      case (Suc nat)
      then obtain p12 y where p11_split_off_last: "p11 = p12@[y]"
        using less.prems(4) p1_split_off_last suc by(cases p11 rule: rev_cases) auto
      hence p1_is: "p1 = p12@[y, x]"
        by (simp add: p1_split_off_last)
      have alt_path_p11:      "alt_path M p11"
       and hd_p1_not_matched: "hd p11 \<notin> Vs M"
        using  alt_list_append_1 less.prems(1-6)  p11_split_off_last p1_split_off_last
              edges_of_path_append_3[of "p12@[y]" "[x]", simplified] hd_append2[of p11 "[x]"]
        by auto
      have p11_length: "1 \<le> length p11"
          using less.prems(3) p1_split_off_last
          by(simp add: p11_split_off_last)
      have IH_applied:
       "alt_list (\<lambda>x. x \<in> aevens F) (\<lambda>x. x \<in> aodds F) p11"
        using suc less.prems(4,5,6) p11_length edges_of_path_append_subset_2 p1_split_off_last
        by (intro less(1)[of ll p11, OF _ alt_path_p11, OF _ _  hd_p1_not_matched]) auto
      hence either_odd_or_even:
         "\<And> y . y \<in> set p11 \<Longrightarrow> y \<in> aevens F = (y \<notin> aodds F)"
        using assms(3) by(auto dest!: alt_list_or evens_and_odds(4))
      hence y_label_or: "y \<in> aevens F \<or> y \<in> aodds F"
        using p11_split_off_last alt_list_or[OF IH_applied(1), of y] by auto
      show ?thesis
      proof(cases "{y, x} \<in> M")
        case True
        note xy_in_M = this
        show ?thesis
        proof(cases rule: disjE[OF y_label_or], goal_cases)
          case 1
          hence x_Odd:"x \<in> aodds F"
            using xy_in_M evens_and_odds(3)[OF assms(3)] higher_forest_properties(2,3)[OF assms(3)]
            by blast
          show ?case
            using IH_applied either_odd_or_even 1 x_Odd
            by(auto intro!: alt_list_last_known_append_one(1)[of _ _ "p12@[y]" x, simplified]
                  simp add: p1_split_off_last p11_split_off_last)
        next
          case 2
          hence x_Even:"x \<in> aevens F"
            using xy_in_M evens_and_odds(3)[OF assms(3)]
                  higher_forest_properties(2,3)[OF assms(3), of x y]
            by(auto simp add: insert_commute)
          show ?case
            using IH_applied either_odd_or_even 2 x_Even
            by(auto intro!: alt_list_last_known_append_one(2)[of _ _ "p12@[y]" x, simplified]
                  simp add: p1_split_off_last p11_split_off_last)
        qed
        next
          case False
          note yx_not_matching = this
          moreover have "alt_path M (p12@[y,x])"
            using less.prems(1) p1_is by simp
          ultimately have odd_edge_length: "odd (length (edges_of_path (p12@[y,x])))"
            using alternating_list_even_last edges_of_path_snoc_2[of p12 y x]
            by fastforce
          hence even_edge_length:"even (length (p12@[y,x]))" "odd (length (p12@[y]))"
                 "even (length p12)"
            unfolding edges_of_path_length even_Suc[symmetric]
            by auto
           hence y_Even: "y \<in> aevens F"
             using last_odd_P2[OF IH_applied(1), simplified p11_split_off_last]
             by auto
           show ?thesis
           proof(cases "{y, x} \<in> \<lbrace>F\<rbrace>")
             case True
             hence x_Odd: "x \<in> aodds F"
               using y_Even assms(4)  assms(3) higher_forest_properties(3) by force
             show ?thesis
               using IH_applied either_odd_or_even y_Even x_Odd
               by(auto intro!: alt_list_last_known_append_one(1)[of _ _ "p12@[y]" x, simplified]
                     simp add: p1_split_off_last p11_split_off_last)
           next
             case False
             note false = False
             have yx_in_G:"{x, y} \<in> G"
               using  edges_of_path_append_2'[of "[y,x]" p12] less.prems(6)
               by (fastforce simp add:  p1_is)
             show ?thesis
             proof(cases "\<exists> e \<in> M. x \<in> e")
               case True
               then obtain v1 v2 where v1v2:"{v1, v2} \<in> M" "x \<in> {v1, v2}"
                 using matching(2) by blast
               hence v1v2_neq_xy:"{v1, v2} \<noteq> {x, y}"
                 using rev_pair_set yx_not_matching by force
               have "x \<notin> aodds F  \<Longrightarrow> if1_cond F"
                 using false y_Even yx_in_G assms(2) evens_and_odds(3)[OF assms(3)] True
                  by(auto intro!: exI[of "\<lambda> y. \<exists> x. _ x y" y, OF exI[of _ x]]
                        simp add: if1_cond_def insert_commute if2_cond_def
                                  matching_graph.vs_member'[symmetric])
              hence x_Odd: "x \<in> aodds F"
                  using assms(1) by blast
              show ?thesis
                using IH_applied either_odd_or_even y_Even x_Odd
                by(auto intro!: alt_list_last_known_append_one(1)[of _ _ "p12@[y]" x, simplified]
                  simp add: p1_split_off_last p11_split_off_last)
        next
          case False
          hence "x \<notin> Vs M"
            by (simp add: vs_member)
          moreover have "x \<in> Vs G"
            using yx_in_G by blast
          ultimately have "x \<in> aevens F"
            using assms(5,4) by auto
          thus ?thesis
            using assms(2) y_Even yx_in_G
            by(auto simp add: if2_cond_def)
        qed
      qed
    qed
  qed
 qed
qed

lemma termination_conditions_no_augpath:
  assumes "\<not> if1_cond F" "\<not> if2_cond F" "forest_invar M F" "Vs G - Vs M \<subseteq> aevens F"
          "graph_augmenting_path G M p"
    shows False
proof-
  have p_simple_props: "length p \<ge> 2" "hd p \<notin> Vs M" "path G p" "hd p \<notin> Vs M" "last p \<notin> Vs M"
    using assms(5)
    by(auto elim: matching_augmenting_pathE)
  have p_harder_props: "set p \<subseteq> Vs G" "set (edges_of_path p) \<subseteq> G" "last p \<in> Vs G"
    using  mem_path_Vs[OF p_simple_props(3) last_in_set] p_simple_props(1)
    by  (simp add: p_simple_props(3) subset_path_Vs path_edges_subset | force)+
  have path_looks_like:
     "alt_list (\<lambda>x. x \<in> aevens F) (\<lambda>x. x \<in> aodds F) p"
    using termination_conditions_alt_paths_alternating_labels[OF assms(1-4), of p]
           p_harder_props  p_simple_props
    by (auto simp add: assms(5) matching_augmenting_path_feats(2))
  have length_p: "even (length p)"
    using assms(5) aug_paths_are_even by auto
  have last_in_p_Odd: "last p \<in> aodds F"
    using last_even_P2[OF path_looks_like(1) length_p] p_simple_props(1) by fastforce
  moreover have "last p \<in> aevens F"
    using p_simple_props(3,5) assms(4,5) p_harder_props(3)
    by auto
  ultimately show False
    using assms(3) evens_and_odds(4) by auto
qed

end

record ('v, 'forest) Compute_Alt_Path_state =
  queue :: "'v list"
  unscanned :: "('v \<times> 'v) list"
  search_forest :: 'forest

locale Compute_Alt_Path =
  Graph_Matching_Specs where lookup = lookup and mate_empty = mate_empty +
  Fset: fixed_univ_set K fset_invar fset_to_set fset_empty fset_insert fset_delete fset_isin +
  Forest: alternating_forest_ordinary_extension_spec
    where vset_invar = fset_invar and vset_to_set = fset_to_set
      and evens = evens and odds = odds and roots = roots
      and get_path = get_path and abstract_forest = abstract_forest
      and forest_invar = forest_invar
      and extend_forest_even_unclassified = extend_forest_even_unclassified
      and empty_forest = empty_forest and forest_univ = K and vset_empty = fset_empty
  for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option"
    and mate_empty :: 'mate
    and fset_invar :: "'fset \<Rightarrow> bool"
    and fset_to_set :: "'fset \<Rightarrow> 'v set"
    and fset_empty :: 'fset
    and fset_insert :: "'v \<Rightarrow> 'fset \<Rightarrow> 'fset"
    and fset_delete :: "'v \<Rightarrow> 'fset \<Rightarrow> 'fset"
    and fset_isin :: "'fset \<Rightarrow> 'v \<Rightarrow> bool"
    and evens odds roots :: "'forest \<Rightarrow> 'fset"
    and get_path :: "'forest \<Rightarrow> 'v \<Rightarrow> 'v list"
    and abstract_forest :: "'forest \<Rightarrow> 'v set set"
    and forest_invar :: "'v set set \<Rightarrow> 'forest \<Rightarrow> bool"
    and extend_forest_even_unclassified :: "'forest \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'forest"
    and empty_forest :: "'fset \<Rightarrow> 'forest" +
  fixes G :: 'adjmap and vs :: "'v list" and M :: 'mate
begin

definition "Compute_Alt_Path_axiom \<longleftrightarrow> graph_input G vs \<and> matching_invar G M"

abbreviation "aevens state \<equiv> fset_to_set (evens (search_forest state))"
abbreviation "aodds state \<equiv> fset_to_set (odds (search_forest state))"
abbreviation "aroots state \<equiv> fset_to_set (roots (search_forest state))"
abbreviation "abs_examined state \<equiv> abstract_forest (search_forest state)"

definition "invar_forest state \<longleftrightarrow>
  forest_invar (matching_abs M) (search_forest state) \<and>
  abs_examined state \<subseteq> ugraph_abs G \<and>
  aroots state = Vs (ugraph_abs G) - Vs (matching_abs M)"

definition "invar_unscanned state \<longleftrightarrow>
  (\<forall>v w. (v, w) \<in> set (unscanned state) \<longrightarrow>
     {v, w} \<in> ugraph_abs G \<and> v \<in> aevens state)"

definition "invar_queue state \<longleftrightarrow> set (queue state) \<subseteq> aevens state"

definition "invar_scanned state \<longleftrightarrow>
  (\<forall>v \<in> aevens state. v \<in> set (queue state) \<or>
    (\<forall>w. {v, w} \<in> ugraph_abs G \<longrightarrow>
      (v, w) \<in> set (unscanned state) \<or> w \<in> aodds state))"

lemma invar_forestD:
  "invar_forest state \<Longrightarrow> forest_invar (matching_abs M) (search_forest state)"
  "invar_forest state \<Longrightarrow> abs_examined state \<subseteq> ugraph_abs G"
  "invar_forest state \<Longrightarrow> aroots state = Vs (ugraph_abs G) - Vs (matching_abs M)"
  by (auto simp: invar_forest_def)

lemma forest_sets_invar:
  assumes "invar_forest state"
  shows "fset_invar (evens (search_forest state))"
    "fset_invar (odds (search_forest state))"
    "fset_invar (roots (search_forest state))"
  using Forest.evens_and_odds(1,2)[OF invar_forestD(1)[OF assms]]
    Forest.roots(1)[OF invar_forestD(1)[OF assms]]
  by auto

lemma forest_isin:
  assumes "invar_forest state"
  shows "fset_isin (evens (search_forest state)) v \<longleftrightarrow> v \<in> aevens state"
    "fset_isin (odds (search_forest state)) v \<longleftrightarrow> v \<in> aodds state"
  using forest_sets_invar[OF assms]
  by (simp_all add: Fset.fixed_univ_set_isin)

lemma aevens_subset_Vs:
  assumes "invar_forest state"
  shows "aevens state \<subseteq> Vs (ugraph_abs G)"
  using Forest.evens_and_odds(3)[OF invar_forestD(1)[OF assms]]
    invar_forestD(3)[OF assms] Vs_subset[OF invar_forestD(2)[OF assms]]
  by auto

end

end

