theory Naive_Weighted_Blossom_Instantiation
  imports Naive_Weighted_Blossom Pre_Edmonds_Gallai
    Edmonds_Gallai_Decomposition.Edmonds_Gallai_Computation
    Blossom_Executable.Find_Max_Matching
begin

section \<open>Instantiation of the Abstract Algorithm\<close>

text \<open>The matching and reduced decomposition are computed on the graph, matching and
  forest ADTs. We reuse the data-structure setup of the full decomposition, and instantiate
  the reduced search and contraction loops required for the weighted algorithm. Only the
  final result is abstracted to the sets used by its mathematical specification.\<close>

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

locale Pre_Edmonds_Gallai_ADTs = Edmonds_Gallai_ADTs
begin

definition "compute_pedg G vs N = Search.compute_pedg G vs N"

lemma compute_pedg_props:
  assumes "GM.graph_input E vs'" "GM.matching_invar E N" "compute_paths E vs' N = None"
    "Vs (GM.ugraph_abs E) - Vs (Matching.\<M> N) \<noteq> {}"
  shows "fset_invar (compute_pedg E vs' N)"
    "pre_edmonds_gallai (GM.ugraph_abs E) (Matching.\<M> N)
      {{v} |v. v \<in> fset_to_set (compute_pedg E vs' N)}"
proof-
  have axiom: "Search.Compute_Alt_Path_axiom E vs' N"
    unfolding Search.Compute_Alt_Path_axiom_def
    by (rule conjI[OF assms(1,2)])
  show "fset_invar (compute_pedg E vs' N)"
    "pre_edmonds_gallai (GM.ugraph_abs E) (Matching.\<M> N)
      {{v} |v. v \<in> fset_to_set (compute_pedg E vs' N)}"
    using Search.compute_pedg_correct(1,3)[OF axiom] assms(3,4)
    by (auto simp only: compute_pedg_def compute_paths_def Search.Compute_Alt_Path_run_impl_def
        Search.Compute_Alt_Path_impl_to_Compute_Alt_Path[OF axiom])
qed

interpretation pedg: find_aug_path_pedg
  where empty = empty and delete = delete and lookup = lookup and update = update
    and adjmap_inv = adjmap_inv and insert = insert and isin = isin and t_set = t_set
    and sel = sel and vset_empty = vset_empty and vset_delete = vset_delete and vset_inv = vset_inv
    and K = K and mate_empty = buddy_empty
    and matching_invar_abs = Matching.invar_matching and matching_abs = "Matching.\<M>"
    and mate_lookup = Matching.buddy_lookup and mate_partner = Matching.get_partner
    and mate_augment = Matching.augment_impl and mate_contract = Matching.contract_path
    and mate_expand = Matching.expand_path_at_matched and mate_add_alternatingly = Matching.add_alternatingly
    and vset_to_list = vset_to_list
    and G = G and vs = vs and M = N
    and blos_search = Subprocedures.compute_match_blossom and create_vert = create_vert
    and fset_invar = fset_invar and fset_to_set = fset_to_set
    and fset_empty = fset_empty and fset_insert = fset_insert
    and fset_delete = fset_delete and fset_isin = fset_isin
    and pedg_search = compute_pedg
  for G vs N
  apply (intro find_aug_path_pedg.intro Find_Aug_Path.intro GM.Graph_Matching_Specs_axioms
      Find_Aug_Path_axioms.intro Fset.fixed_univ_set_axioms find_aug_path_pedg_axioms.intro)
  apply (rule Subprocedures.compute_match_blossom(1); assumption)
  apply (rule Subprocedures.compute_match_blossom(2); assumption)
  apply (rule Subprocedures.compute_match_blossom(3); assumption)
  apply (rule create_vert)
  apply (erule create_vert_in_univ)
  apply (simp only: compute_blossom_None; rule compute_pedg_props(2); assumption)
  by (simp only: compute_blossom_None; rule compute_pedg_props(1); assumption)

interpretation max_matching: Find_Max_Matching
  where empty = empty and delete = delete and lookup = lookup and update = update
    and adjmap_inv = adjmap_inv and insert = insert and isin = isin and t_set = t_set
    and sel = sel and vset_empty = vset_empty and vset_delete = vset_delete and vset_inv = vset_inv
    and K = K and mate_empty = buddy_empty
    and matching_invar_abs = Matching.invar_matching and matching_abs = "Matching.\<M>"
    and mate_lookup = Matching.buddy_lookup and mate_partner = Matching.get_partner
    and mate_augment = Matching.augment_impl and mate_contract = Matching.contract_path
    and mate_expand = Matching.expand_path_at_matched and mate_add_alternatingly = Matching.add_alternatingly
    and vset_to_list = vset_to_list
    and G = G and vs = vs and aug_path_search = "Decomposition.Find_Aug_Path_run_impl G vs"
  for G vs
  apply (intro Find_Max_Matching.intro GM.Graph_Matching_Specs_axioms
      Find_Max_Matching_axioms.intro)
  apply (rule Decomposition.Find_Aug_Path_run_impl_correct(1)[
      unfolded Decomposition.Find_Aug_Path_axiom_def])
  apply (rule conjI; assumption)
  apply assumption
  apply (rule Decomposition.Find_Aug_Path_run_impl_correct(2)[
      unfolded Decomposition.Find_Aug_Path_axiom_def])
  apply (rule conjI; assumption)
  by assumption

definition "maximum_matching G vs =
  current_matching (max_matching.Find_Max_Matching_run_impl G vs)"

lemma maximum_matching_correct:
  assumes "GM.graph_input G vs"
  shows "max_card_matching (GM.ugraph_abs G) (Matching.\<M> (maximum_matching G vs))"
    "GM.matching_invar G (maximum_matching G vs)"
proof-
  interpret proofs: Find_Max_Matching_thms
  where empty = empty and delete = delete and lookup = lookup and update = update
    and adjmap_inv = adjmap_inv and insert = insert and isin = isin and t_set = t_set
    and sel = sel and vset_empty = vset_empty and vset_delete = vset_delete and vset_inv = vset_inv
    and K = K and mate_empty = buddy_empty
    and matching_invar_abs = Matching.invar_matching and matching_abs = "Matching.\<M>"
    and mate_lookup = Matching.buddy_lookup and mate_partner = Matching.get_partner
    and mate_augment = Matching.augment_impl and mate_contract = Matching.contract_path
    and mate_expand = Matching.expand_path_at_matched and mate_add_alternatingly = Matching.add_alternatingly
    and vset_to_list = vset_to_list
    and G = G and vs = vs and aug_path_search = "Decomposition.Find_Aug_Path_run_impl G vs"
    by (intro Find_Max_Matching_thms.intro max_matching.Find_Max_Matching_axioms
        Find_Max_Matching_thms_axioms.intro)
       (simp only: max_matching.Find_Max_Matching_axiom_def assms)
  show "max_card_matching (GM.ugraph_abs G) (Matching.\<M> (maximum_matching G vs))"
    "GM.matching_invar G (maximum_matching G vs)"
    using proofs.Find_Max_Matching_correct_1 proofs.Find_Max_Matching_correct_2
    by (simp_all only: maximum_matching_def max_matching.Find_Max_Matching_run_impl_def
        proofs.Find_Max_Matching_impl_to_Find_Max_Matching)
qed

definition "find_matching_or_decomposition G vs =
  (let N = maximum_matching G vs
   in if pedg.pedg_perfect G vs N then MOD.match (Matching.\<M> N)
      else decomp (fset_to_set ` set (pedg.find_pedg G vs N)))"

lemma maximum_matching_perfect:
  assumes "GM.graph_input G vs"
  shows "(\<exists>M. perfect_matching (GM.ugraph_abs G) M) \<longleftrightarrow>
    pedg.pedg_perfect G vs (maximum_matching G vs)"
  using max_card_matching_is_perfect_matching[OF maximum_matching_correct(1)[OF assms]
      _ GM.ugraph_abs_graph_invar[OF assms]]
    perfect_matching_max_card_matchingI[OF maximum_matching_correct(1)[OF assms]]
    perfect_matchingD(3)[of "GM.ugraph_abs G"]
    pedg.pedg_perfect_iff[OF assms maximum_matching_correct(2)[OF assms]]
  by blast

lemma matching_result_correct:
  assumes "GM.graph_input G vs" "find_matching_or_decomposition G vs = MOD.match N"
  shows "perfect_matching (GM.ugraph_abs G) N"
  using assms(2) perfect_matching_max_card_matchingI[OF maximum_matching_correct(1)[OF assms(1)]]
    pedg.pedg_perfect_iff[OF assms(1) maximum_matching_correct(2)[OF assms(1)]]
  by (auto simp only: find_matching_or_decomposition_def Let_def MOD.inject MOD.distinct
      split: if_splits)

lemma decomposition_result_correct:
  assumes "GM.graph_input G vs" "find_matching_or_decomposition G vs = decomp D"
  shows "pre_edmonds_gallai (GM.ugraph_abs G) (Matching.\<M> (maximum_matching G vs)) D"
proof-
  have "Vs (GM.ugraph_abs G) - Vs (Matching.\<M> (maximum_matching G vs)) \<noteq> {}"
    "D = fset_to_set ` set (pedg.find_pedg G vs (maximum_matching G vs))"
    using assms(2)
      Vs_subset[OF GM.matching_invar_props(3)[OF maximum_matching_correct(2)[OF assms(1)]]]
      pedg.pedg_perfect_iff[OF assms(1) maximum_matching_correct(2)[OF assms(1)]]
    by (auto simp only: find_matching_or_decomposition_def Let_def MOD.inject MOD.distinct
        split: if_splits)
  then show ?thesis
    using pedg.find_pedg_correct(2)[OF assms(1)
      maximum_matching_correct(2,1)[OF assms(1)]]
    by simp
qed

lemma find_matching_or_decomposition_correct:
  assumes "GM.graph_input G vs"
  shows
  "\<exists> M. perfect_matching (GM.ugraph_abs G) M
         \<Longrightarrow> \<exists> M. find_matching_or_decomposition G vs = MOD.match M"
  "\<nexists> M. perfect_matching (GM.ugraph_abs G) M
         \<Longrightarrow> \<exists> D. find_matching_or_decomposition G vs = decomp D"
  "\<And> M. find_matching_or_decomposition G vs = MOD.match M \<Longrightarrow>
           perfect_matching (GM.ugraph_abs G) M"
  "\<And> D. find_matching_or_decomposition G vs = decomp D \<Longrightarrow>
          disjoint D"
  "\<And> D.  find_matching_or_decomposition G vs = decomp D \<Longrightarrow>
          \<Union> D \<subseteq> Vs (GM.ugraph_abs G)"
  "\<And> D X Y.  \<lbrakk>find_matching_or_decomposition G vs = decomp D; X \<in> D; Y \<in> D; X \<noteq> Y\<rbrakk> \<Longrightarrow>
          \<nexists> u v. {u, v} \<in> (GM.ugraph_abs G) \<and> u \<in> X \<and> v \<in> Y"
  "\<And> D. find_matching_or_decomposition G vs = decomp D \<Longrightarrow>
          card D > card (Neighbourhood (GM.ugraph_abs G) (\<Union> D))"
  "\<And> D X x.  \<lbrakk>find_matching_or_decomposition G vs = decomp D; X \<in> D; x \<in> X\<rbrakk> \<Longrightarrow>
          \<exists> M. graph_matching ((GM.ugraph_abs G)\<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x}"
  "\<And> D X.  \<lbrakk>find_matching_or_decomposition G vs = decomp D; X \<in> D\<rbrakk> \<Longrightarrow> X\<noteq>{}"
proof(goal_cases)
  case 1
  then show ?case
    using maximum_matching_perfect[OF assms]
    by (auto simp only: find_matching_or_decomposition_def Let_def split: if_splits)
next
  case 2
  then show ?case
    using maximum_matching_perfect[OF assms]
    by (auto simp only: find_matching_or_decomposition_def Let_def split: if_splits)
next
  case (3 M)
  then show ?case
    by (rule matching_result_correct[OF assms])
next
  case (4 D)
  show ?case
    by (rule pre_edmonds_gallaiD(1)[OF decomposition_result_correct[OF assms 4(1)]])
next
  case (5 D)
  show ?case
    by (rule pre_edmonds_gallaiD(2)[OF decomposition_result_correct[OF assms 5(1)]])
next
  case (6 D X Y)
  show ?case
    by (rule pre_edmonds_gallaiD(4)[OF decomposition_result_correct[OF assms 6(1)] 6(2-),
        unfolded connected_set_of_vertices_def])
next
  case (7 D)
  show ?case
    by (rule pre_edmonds_gallaiD(5)[OF decomposition_result_correct[OF assms 7(1)]])
next
  case (8 D X x)
  show ?case
    by (rule pre_edmonds_gallaiD(6)[OF decomposition_result_correct[OF assms 8(1)] 8(2-)])
next
  case (9 D X)
  show ?case
    by (rule pre_edmonds_gallaiD(3)[OF decomposition_result_correct[OF assms 9(1)] 9(2-)])
qed

end

subsection \<open>Set interface for the weighted algorithm\<close>

locale compute_alt_path_and_pedg_use = compute_alt_path_and_edg_use
begin

interpretation reduced: Pre_Edmonds_Gallai_ADTs
  where K = "- {nil}" and empty = Map.empty and lookup = id
    and delete = "\<lambda>v m. m(v := None)" and update = "\<lambda>v S m. m(v := Some S)"
    and adjmap_inv = "\<lambda>_. True"
    and vset_empty = "{}" and insert = Set.insert and vset_delete = "\<lambda>v S. S - {v}"
    and isin = "\<lambda>S v. v \<in> S" and t_set = id and vset_inv = finite and sel = sel
    and parent_invar = "\<lambda>_. True" and parent_update = "\<lambda>m v w. m(v := w)" and parent_get = id
    and origin_invar = "\<lambda>_. True" and origin_update = "\<lambda>m v w. m(v := w)" and origin_get = id
    and buddy_invar = "\<lambda>_. True" and buddy_update = "\<lambda>m v w. m(v := w)" and buddy_get = id
    and fset_invar = "\<lambda>S. finite S \<and> S \<subseteq> - {nil}" and fset_to_set = id
    and fset_empty = "{}" and fset_insert = Set.insert and fset_delete = "\<lambda>v S. S - {v}"
    and fset_isin = "\<lambda>S v. v \<in> S"
    and parent_empty = "\<lambda>_. nil" and origin_empty = "\<lambda>_. nil" and buddy_empty = "\<lambda>_. nil"
    and nil = nil and vset_to_list = edg_list_of_set and fset_to_list = edg_list_of_set
    and create_vert = "\<lambda>vs. create_vert (Set.insert nil (set vs))"
  by unfold_locales
     (auto simp: fun_eq_iff edg_list_of_set create_vert_list intro: choose)

definition "find_matching_or_decomposition =
  reduced.find_matching_or_decomposition (graph_of_set E) (edg_list_of_set (Vs E))"

lemmas find_matching_or_decomposition_correct =
  reduced.find_matching_or_decomposition_correct[
    OF graph_of_set_input[OF graph nil_not_in_Vs],
    unfolded find_matching_or_decomposition_def[symmetric] graph_of_set_abs[OF graph]]

end

locale naive_weighted_blossom_instantiation =
  graph_abs where G = G
for G::"'v set set" and Bsel::"'v set set \<Rightarrow> 'v set" and create_vert::"'v set set \<Rightarrow> 'v set"+
fixes w::"'v set \<Rightarrow> real"
  and sel_with_P::"('v set \<Rightarrow> bool) \<Rightarrow> 'v set set \<Rightarrow> 'v set"
  and sel_from_sets::"('v set set \<Rightarrow> bool) \<Rightarrow> 'v set set set \<Rightarrow> 'v set set"
  and remove_set::"'v set \<Rightarrow> 'v"
assumes choose: "\<And>S. S \<noteq> {} \<Longrightarrow> Bsel S \<in> S"
assumes create_vert: "\<And>S. finite S \<Longrightarrow> create_vert S \<notin> S"
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

interpretation pedg: compute_alt_path_and_pedg_use
  where E = E and sel = Bsel and create_vert = create_vert and sel_from_sets = sel_from_sets
  using graph_invar sel_from_sets create_vert choose
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
