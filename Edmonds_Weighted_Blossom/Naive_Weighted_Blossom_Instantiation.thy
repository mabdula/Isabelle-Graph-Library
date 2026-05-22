theory Naive_Weighted_Blossom_Instantiation
  imports Naive_Weighted_Blossom Pre_Edmonds_Gallai
begin

section \<open>Instantiation of the Abstract Algorithm\<close>

text \<open>We use the reduced Edmonds-Gallai Decomposition to instantiate our abstract 
      weighted matching algorithm.\<close>

locale find_aug_path_pedg_use = find_aug_path_use where sel = sel and E = E + 
  find_aug_path_pedg where sel = sel 
for sel::"'a set \<Rightarrow> 'a" and E::"'a set set"
begin

interpretation find_max_match_intrp: find_max_match E find_aug_path
  using find_aug_path_complete[OF _ _ _ graph] find_aug_path_sound[OF _ _ _ graph]
  by unfold_locales auto

definition "find_matching_or_decomposition=
  (let M = find_max_matching {}
   in if Vs M = Vs E then MOD.match M
   else decomp (find_pedg E M))"

lemma find_matching_has_max_card:
  "max_card_matching E (find_max_matching {})"
  using find_max_matching_works(1,2,4) finite_subset finite_E
  by(auto intro!: max_card_matchingI')

lemma max_card_matching_is_perfect_matching:
  "\<lbrakk>max_card_matching G M; perfect_matching G M'; graph_invar G\<rbrakk> \<Longrightarrow>
    perfect_matching G M" 
proof(goal_cases)
  case 1
  moreover hence "max_card_matching G M'" 
    using graph_abs.intro graph_abs.perfect_matching_is_max_card_matching by auto
  moreover hence "card M'= card M"
    using "1"(1) max_card_matchings_same_size by blast
  ultimately show ?case
    using "1"(1,3) graph_abs.matching_card_vs[of M] graph_abs.matching_card_vs[of M'] 
      card_subset_eq[of "Vs G" "Vs M"] Vs_subset[of M G] graph_abs.intro[of M] 
      graph_abs.intro[of M'] graph_invar_subset[of G M] graph_invar_subset[of G M']
    by (intro perfect_matching_max_card_matchingI)
      (auto elim!: perfect_matchingE simp add:  max_card_matching_def)
qed

lemma find_max_matching_perfect:
  "(\<exists> M. perfect_matching E M) \<longleftrightarrow> perfect_matching E (find_max_matching {})"
  "(\<exists> M. perfect_matching E M) \<longleftrightarrow> Vs (find_max_matching {}) = Vs E"
  using find_matching_has_max_card Vs_subset[OF find_max_matching_works(1)] graph 
  by (auto intro: perfect_matching_max_card_matchingI 
      max_card_matching_is_perfect_matching[of E "find_max_matching {}"]
      perfect_matchingE[of E "find_max_matching {}"]
      simp add: graph max_card_matching_is_perfect_matching)+

lemmas compute_pedg_spec = pedg_search_sound

lemma find_matching_or_decomposition_correct:
  "\<exists> M. perfect_matching E M
         \<Longrightarrow> \<exists> M. find_matching_or_decomposition = MOD.match M"
  "\<nexists> M. perfect_matching E M 
         \<Longrightarrow> \<exists> D. find_matching_or_decomposition = decomp D"
  "\<And> M. find_matching_or_decomposition = MOD.match M \<Longrightarrow>
           perfect_matching E M"  
  "\<And> D. find_matching_or_decomposition = decomp D \<Longrightarrow>
          disjoint D"
  "\<And> D.  find_matching_or_decomposition = decomp D \<Longrightarrow>
          \<Union> D \<subseteq> Vs E"
  "\<And> D X Y.  \<lbrakk>find_matching_or_decomposition = decomp D; X \<in> D; Y \<in> D; X \<noteq> Y\<rbrakk> \<Longrightarrow>
          \<nexists> u v. {u, v} \<in> E \<and> u \<in> X \<and> v \<in> Y"
  "\<And> D. find_matching_or_decomposition = decomp D \<Longrightarrow>
          card D > card (Neighbourhood E (\<Union> D))"  
  "\<And> D X x.  \<lbrakk>find_matching_or_decomposition = decomp D; X \<in> D; x \<in> X\<rbrakk> \<Longrightarrow>
          \<exists> M. graph_matching (E\<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x}"   
  "\<And> D X.  \<lbrakk>find_matching_or_decomposition = decomp D; X \<in> D\<rbrakk> \<Longrightarrow> X\<noteq>{}" 
proof(goal_cases)
  case 1
  then show ?case
    using find_matching_has_max_card find_max_matching_perfect
    by(auto simp add: find_matching_or_decomposition_def Let_def)
next
  case 2
  then show ?case 
    using find_matching_has_max_card find_max_matching_perfect
    by(auto simp add: find_matching_or_decomposition_def Let_def)
next
  case (3 M)
  then show ?case 
    using find_matching_has_max_card find_max_matching_perfect
    by(auto simp add: find_matching_or_decomposition_def Let_def)
next
  case (4 D)
  find_theorems pedg_search
  hence pedg: "pre_edmonds_gallai E (find_max_matching {}) (find_pedg E (find_max_matching {}))"
    using find_matching_has_max_card Vs_subset[OF find_max_matching_works(1)] graph
    by(intro find_pedg_correct[of E "find_max_matching {}"])
      (auto simp add: find_matching_or_decomposition_def Let_def if_split[of "\<lambda> x. x = _"])
  moreover have "D = find_pedg E (find_max_matching {})"
    using 4 
    by(auto simp add: find_matching_or_decomposition_def Let_def if_split[of "\<lambda> x. x = _"])
  ultimately show ?case 
    by(auto dest!: pre_edmonds_gallaiD(1))
next
  case (5 D)
  hence pedg: "pre_edmonds_gallai E (find_max_matching {}) (find_pedg E (find_max_matching {}))"
    using find_matching_has_max_card Vs_subset[OF find_max_matching_works(1)] graph
    by(intro find_pedg_correct[of E "find_max_matching {}"])
      (auto simp add: find_matching_or_decomposition_def Let_def if_split[of "\<lambda> x. x = _"])
  moreover have "D = find_pedg E (find_max_matching {})"
    using 5
    by(auto simp add: find_matching_or_decomposition_def Let_def if_split[of "\<lambda> x. x = _"])
  ultimately show ?case 
    by(auto dest!: pre_edmonds_gallaiD(2))
next
  case (6 D X Y)
  hence pedg: "pre_edmonds_gallai E (find_max_matching {}) (find_pedg E (find_max_matching {}))"
    using find_matching_has_max_card Vs_subset[OF find_max_matching_works(1)] graph
    by(intro find_pedg_correct[of E "find_max_matching {}"])
      (auto simp add: find_matching_or_decomposition_def Let_def if_split[of "\<lambda> x. x = _"])
  have D_def: "D = find_pedg E (find_max_matching {})"
    using 6 
    by(auto simp add: find_matching_or_decomposition_def Let_def if_split[of "\<lambda> x. x = _"])
  show ?case 
    using pre_edmonds_gallaiD(4)[OF pedg, folded D_def, OF 6(2-)]
    by(auto simp add: connected_set_of_vertices_def)
next
  case (7 D)
  hence pedg: "pre_edmonds_gallai E (find_max_matching {}) (find_pedg E (find_max_matching {}))"
    using find_matching_has_max_card Vs_subset[OF find_max_matching_works(1)] graph
    by(intro find_pedg_correct[of E "find_max_matching {}"])
      (auto simp add: find_matching_or_decomposition_def Let_def if_split[of "\<lambda> x. x = _"])
  have D_def: "D = find_pedg E (find_max_matching {})"
    using 7 
    by(auto simp add: find_matching_or_decomposition_def Let_def if_split[of "\<lambda> x. x = _"])
  show ?case 
    using pre_edmonds_gallaiD(5)[OF pedg, folded D_def]
    by simp
next
  case (8 D X x)
  hence pedg: "pre_edmonds_gallai E (find_max_matching {}) (find_pedg E (find_max_matching {}))"
    using find_matching_has_max_card Vs_subset[OF find_max_matching_works(1)] graph
    by(intro find_pedg_correct[of E "find_max_matching {}"])
      (auto simp add: find_matching_or_decomposition_def Let_def if_split[of "\<lambda> x. x = _"])
  have D_def: "D = find_pedg E (find_max_matching {})"
    using 8
    by(auto simp add: find_matching_or_decomposition_def Let_def if_split[of "\<lambda> x. x = _"])
  show ?case 
    using pre_edmonds_gallaiD(6)[OF pedg, folded D_def, OF 8(2-)]
    by simp
next
  case (9 D X)
  hence pedg: "pre_edmonds_gallai E (find_max_matching {}) (find_pedg E (find_max_matching {}))"
    using find_matching_has_max_card Vs_subset[OF find_max_matching_works(1)] graph
    by(intro find_pedg_correct[of E "find_max_matching {}"])
      (auto simp add: find_matching_or_decomposition_def Let_def if_split[of "\<lambda> x. x = _"])
  have D_def: "D = find_pedg E (find_max_matching {})"
    using 9
    by(auto simp add: find_matching_or_decomposition_def Let_def if_split[of "\<lambda> x. x = _"])
  show ?case 
    using pre_edmonds_gallaiD(3)[OF pedg, folded D_def, OF 9(2-)]
    by simp
qed
end

locale compute_match_blossom'_pedg_use =
  compute_match_blossom'_use where E = E
for E::"'a set set"+
fixes compute_pedg::"'a set set \<Rightarrow>'a set set \<Rightarrow> 'a set set" 
  and sel_from_sets::"('a set \<Rightarrow> bool) \<Rightarrow> 'a set set \<Rightarrow> 'a set"
assumes compute_pedg: 
  "\<And> E M.  \<lbrakk>graph_invar E; matching M; M \<subseteq> E; compute_alt_path E M = None; Vs E - Vs M \<noteq> {}\<rbrakk>
            \<Longrightarrow> pre_edmonds_gallai E M (compute_pedg E M)"
assumes sel_from_sets:
  "\<And> \<D> P. \<lbrakk>finite \<D>; \<exists> D \<in> \<D>. P D\<rbrakk> \<Longrightarrow> sel_from_sets P \<D> \<in> \<D>"
  "\<And> \<D> P. \<lbrakk>finite \<D>; \<exists> D \<in> \<D>. P D\<rbrakk> \<Longrightarrow> P (sel_from_sets P \<D>)"
begin

interpretation find_aug_path_pedg_use_intrp: find_aug_path_pedg_use create_vert
  "\<lambda>G M. compute_match_blossom'.compute_match_blossom sel G M (compute_alt_path G M)"
  compute_pedg sel_from_sets sel E
proof(rule find_aug_path_pedg_use.intro, goal_cases)
  case 2
  then show ?case
  proof(rule find_aug_path_pedg.intro, goal_cases)
    case 1
    then show ?case 
      using find_aug_path_use.axioms(1) find_aug_path_use_satisfied by blast
  next
    case 2
    then show ?case
    proof(rule find_aug_path_pedg_axioms.intro, goal_cases)
      case (1 G M)
      then interpret compute_match_blossom' sel G M "compute_alt_path G M"
        using compute_alt_path_spec compute_alt_path_complete
        by unfold_locales
      from 1 show ?case
        by(auto intro!: compute_pedg blossom_None_alt_path_None)
    qed (auto simp add: sel_from_sets)
  qed
qed (simp add: find_aug_path_use_satisfied)

abbreviation "find_matching_or_decomposition \<equiv>
  find_aug_path_pedg_use_intrp.find_matching_or_decomposition"

lemmas find_matching_or_decomposition_correct =
  find_aug_path_pedg_use_intrp.find_matching_or_decomposition_correct
end

locale compute_alt_path_and_pedg_use = 
  compute_alt_path_use +
  fixes sel_from_sets::"('a set \<Rightarrow> bool) \<Rightarrow> 'a set set \<Rightarrow> 'a set"
  assumes sel_from_sets:
    "\<And> \<D> P. \<lbrakk>finite \<D>; \<exists> D \<in> \<D>. P D\<rbrakk> \<Longrightarrow> sel_from_sets P \<D> \<in> \<D>"
    "\<And> \<D> P. \<lbrakk>finite \<D>; \<exists> D \<in> \<D>. P D\<rbrakk> \<Longrightarrow> P (sel_from_sets P \<D>)"
begin

definition "compute_pedg G M = 
  compute_alt_path.compute_pedg id 
     get_path extend_forest_even_unclassified
     empty_forest abstract_forest evens G M sel (Vs G - Vs M)"

context 
  fixes G M::"'a set set"
  assumes "graph_invar G" "matching M" "M \<subseteq> G"
begin

interpretation path_compute: compute_alt_path
  where vset_invar = "\<lambda> V. finite V"
    and vset_to_set = id
    and odds = odds
    and get_path = get_path
    and forest_invar = forest_invar
    and roots = roots
    and vset_empty = "{}"
    and extend_forest_even_unclassified = extend_forest_even_unclassified
    and empty_forest = empty_forest
    and abstract_forest = abstract_forest
    and evens = evens
    and G = G
    and M = M
    and sel = sel
    and unmatcheds = "Vs G - Vs M"
  using forest_satisfied[OF \<open>graph_invar G\<close>  \<open>matching M\<close> \<open>M \<subseteq> G\<close>]
  by(auto intro!: compute_alt_path.intro choose_axioms compute_alt_path_axioms.intro
      simp add: graph_abs.intro match_axioms.intro match_def g.graph_abs_axioms 
      \<open>M \<subseteq> G\<close> \<open>matching M\<close> match_axioms_def  \<open>graph_invar G\<close> graph_abs_def)
find_theorems path_compute.compute_pedg
lemmas compute_alt_path_props = 
  path_compute.compute_alt_path_from_tree_sound'
  path_compute.compute_alt_path_from_tree_complete
  path_compute.compute_pedg_correct

end


interpretation usage:
  compute_match_blossom'_pedg_use sel create_vert compute_paths E compute_pedg sel_from_sets
proof(unfold_locales,goal_cases)  
  case (2 G M)
  thus  ?case
    using compute_alt_path_props(2)[OF 2(1,2,3)]
    by(auto simp add: compute_paths_def)
next
  case (1 G M)
  thus  ?case
    using compute_alt_path_props(1)[OF 1(1,2,3)]
    by(auto simp add: compute_paths_def)
next
  case (3 G M)
  thus ?case
    unfolding compute_pedg_def compute_paths_def 
    by(intro compute_alt_path_props(3)[of G M]) auto
qed (auto simp add: sel_from_sets)

abbreviation "find_matching_or_decomposition \<equiv> usage.find_matching_or_decomposition"

lemmas find_matching_or_decomposition_correct =
  usage.find_matching_or_decomposition_correct

end

locale naive_weighted_blossom_instantiation =
  graph_abs where G = G +
  choose Bsel+
  create_vert create_vert 
for G::"'v set set" and Bsel::"'v set set \<Rightarrow> 'v set" and create_vert::"'v set set \<Rightarrow> 'v set"+
fixes w::"'v set \<Rightarrow> real"
  and sel_with_P::"('v set \<Rightarrow> bool) \<Rightarrow> 'v set set \<Rightarrow> 'v set"
  and sel_from_sets::"('v set set \<Rightarrow> bool) \<Rightarrow> 'v set set set \<Rightarrow> 'v set set"
  and remove_set::"'v set \<Rightarrow> 'v"
assumes remove_set: "\<And> x. remove_set {x} = x"
assumes sel_from_sets:
  "\<And> \<D> P. \<lbrakk>finite \<D>; \<exists> D \<in> \<D>. P D\<rbrakk> \<Longrightarrow> sel_from_sets P \<D> \<in> \<D>"
  "\<And> \<D> P. \<lbrakk>finite \<D>; \<exists> D \<in> \<D>. P D\<rbrakk> \<Longrightarrow> P (sel_from_sets P \<D>)"
assumes sel_with_P_correct: "\<And> P X. \<exists> x \<in> X. P x \<Longrightarrow> sel_with_P P X \<in> X"
  "\<And> P X. \<lbrakk>\<exists> x \<in> X. P x; finite X\<rbrakk> \<Longrightarrow> P (sel_with_P P X)"
begin

context
  fixes E::"'v set set set"
  assumes graph_invar: "graph_invar E"
begin

interpretation pedg: compute_alt_path_and_pedg_use Bsel create_vert E sel_from_sets
  using graph_invar sel_from_sets
  by unfold_locales

abbreviation "find_matching_or_decomposition \<equiv> pedg.find_matching_or_decomposition"
lemmas find_matching_or_decomposition_correct=pedg.find_matching_or_decomposition_correct
end

interpretation  naive_weighted_blossom: naive_weighted_blossom_with_cleanup
  find_matching_or_decomposition w sel_with_P G remove_set
  using find_matching_or_decomposition_correct
  by unfold_locales (auto simp add: sel_with_P_correct remove_set)

abbreviation "\<pi>\<^sub>0 \<equiv> naive_weighted_blossom.\<pi>\<^sub>0"
abbreviation "\<OO>\<^sub>0 \<equiv> naive_weighted_blossom.\<OO>\<^sub>0"
abbreviation "top_loop_dom \<equiv> naive_weighted_blossom.top_loop_dom"
abbreviation "naive_min_weight_perfect_matching \<equiv>
  naive_weighted_blossom.naive_min_weight_perfect_matching"
lemmas naive_min_weight_perfect_matching_partial_correctness =
  naive_weighted_blossom.naive_min_weight_perfect_matching_partial_correctness

end
end