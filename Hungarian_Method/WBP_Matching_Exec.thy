theory WBP_Matching_Exec
  imports Basic_Matching.WBP_Matching_Reductions_Exec  "HOL-Library.Product_Lexorder"
          Hungarian_Method_Instantiation
begin

hide_const PST_RBT.delete PST_RBT.update left

section \<open>Executable Algorithms for Weighted Bipartite Matching\<close>

instantiation bp_vertex_wrapper :: (linorder) linorder
begin

fun less_eq_bp_vertex_wrapper where
"less_eq_bp_vertex_wrapper (old_vertex u) (old_vertex v) \<longleftrightarrow> u \<le> v"|
"less_eq_bp_vertex_wrapper (old_vertex u) (new_vertex i) \<longleftrightarrow> True"|
"less_eq_bp_vertex_wrapper (new_vertex i) (old_vertex u) \<longleftrightarrow> False"|
"less_eq_bp_vertex_wrapper (new_vertex i) (new_vertex j) \<longleftrightarrow> i \<le> j"

fun less_bp_vertex_wrapper where
"less_bp_vertex_wrapper (old_vertex u) (old_vertex v) \<longleftrightarrow> u < v"|
"less_bp_vertex_wrapper (old_vertex u) (new_vertex i) \<longleftrightarrow> True"|
"less_bp_vertex_wrapper (new_vertex i) (old_vertex u) \<longleftrightarrow> False"|
"less_bp_vertex_wrapper (new_vertex i) (new_vertex j) \<longleftrightarrow> i < j"

instance 
proof(standard, goal_cases)
  case (1 x y)
  then show ?case
    by(cases x, all \<open>cases y\<close>) auto
next
  case (2 x)
  then show ?case 
   by(cases x) auto
next
  case (3 x y z)
  then show ?case 
   by(cases x, all \<open>cases y\<close>, all \<open>cases z\<close>) auto
next
  case (4 x y)
  then show ?case
   by(cases x, all \<open>cases y\<close>) auto
next
  case (5 x y)
  then show ?case 
   by(cases x, all \<open>cases y\<close>) auto
qed

end

lemma trivial_map: "Map (\<lambda>x. None) (\<lambda>x y f. f(x \<mapsto> y)) (\<lambda>x f. f(x := None)) (\<lambda>f. f) (\<lambda>f. True)"
  by(auto intro!: Map.intro)

global_interpretation graph_completer_spec_rbt: graph_completer_spec
  where delete = delete
  and lookup = lookup
  and isin = isin
  and t_set = t_set
  and sel = sel
  and update = update
  and adjmap_inv= M.invar
  and vset_delete = vset_delete
  and vset_inv = vset_inv
  and empty = map_empty
  and vset_empty = vset_empty
  and insert = vset_insert
  and oempty = "\<lambda> x. None"
  and odelete = "\<lambda> x f. fun_upd f x None"
  and olookup = "\<lambda> f x. f x"
  and oinsert = vset_insert
  and oisin = isin
  and ot_set = t_set
  and osel = sel
  and oupdate =  "\<lambda> x y f. fun_upd f x (Some y)"
  and oadjmap_inv="\<lambda> f. True"
  and ovset_empty = vset_empty
  and ovset_delete = vset_delete
  and ovset_inv = vset_inv
  and ovset_fold_reals = "\<lambda> f T x. rbt_set_fold T f x"
  and cempty = Leaf
  and cupdate = update
  and cdelete = delete
  and clookup = lookup
  and cinvar = M.invar
  and obempty = Leaf
  and obupdate = update
  and obdelete= delete
  and oblookup=lookup
  and obinvar =M.invar
  and bempty="\<lambda> x. None"
  and bupdate= "\<lambda> x y f. fun_upd f x (Some y)"
  and bdelete= "\<lambda> x f. fun_upd f x None"
  and blookup= "\<lambda> f x. f x"
  and binvar = "\<lambda> f. True"
  and vset_to_list = "inorder"
  and left = left
  and right = right
  and Gimpl = Gimpl
  and edge_costs = edge_costs
for left right Gimpl edge_costs
defines lsize=graph_completer_spec_rbt.lsize
and rsize = graph_completer_spec_rbt.rsize
and new_left_list = graph_completer_spec_rbt.new_left_list
and new_right_list = graph_completer_spec_rbt.new_right_list
and new_edge_list = graph_completer_spec_rbt.new_edge_list
and bp_perfect_exec = graph_completer_spec_rbt.bp_perfected_exec
and new_left = graph_completer_spec_rbt.new_left
and new_right = graph_completer_spec_rbt.new_right
and max_abs_weight = graph_completer_spec_rbt.max_abs_weight
and penalty_exec = graph_completer_spec_rbt.penalty_exec
and new_costs_mcst = graph_completer_spec_rbt.new_costs_mcst
and bp_min_costs_to_min_perfect_costs_exec = graph_completer_spec_rbt.bp_min_costs_to_min_perfect_costs_exec
and new_costs_mcmc = graph_completer_spec_rbt.new_costs_mcmc
and bp_min_max_card_costs_to_min_perfect_costs_exec = graph_completer_spec_rbt.bp_min_max_card_costs_to_min_perfect_costs_exec
and extract_mw_matching= graph_completer_spec_rbt.extract_mw_matching
and extract_mwmc_matching=graph_completer_spec_rbt.extract_mwmc_matching
and add_edge = graph_completer_spec_rbt.new_graph.add_edge
and oheighbourhood=graph_completer_spec_rbt.old_graph.neighbourhood
and from_list = graph_completer_spec_rbt.new_graph.from_list
proof(rule graph_completer_spec.intro, goal_cases)
  case 1
  then show ?case 
    by(auto intro!: Pair_Graph_Specs.intro 
          simp add: Map_axioms_as_needed map_empty_def RBT_Set.empty_def S_C.Set_Choose_axioms)
next
  case 2
  then show ?case 
    by(auto intro!: Pair_Graph_Specs.intro trivial_map
          simp add: RBT_Set.empty_def S_C.Set_Choose_axioms)
next
  case 3
  then show ?case
  proof(rule Set_Iterable.intro, goal_cases)
    case (1 S f acc)
    then show ?case 
    using rbt_set_fold_correct[of S f acc] 
    by(auto simp add: vset_inv_def t_inv_def) 
qed
next
  case 4
  then show ?case 
    by (simp add: pd_path_search_spec.missed_map.Map_axioms)
next
  case 6
  then show ?case 
    by (simp add: aug_a_matching.buddy_map.Map_axioms)
next
  case 5
  then show ?case 
    by(simp add: trivial_map)
qed

(*TODO MOVE*)
interpretation map_iterator_rbt: Map_iterator M.invar lookup update_all
  using update_all
  by(fastforce intro!: Map_iterator.intro update_all
             simp add: M.invar_def RBT_Set.rbt_def domI rbt_red_def update_all(1)
                       color_no_change)

global_interpretation invert_costs: cost_inverter
  where invar = M.invar
  and update_all = update_all
  and lookup = lookup
defines inverted_costs = invert_costs.inverted_costs
  using update_all
  by(auto intro!: cost_inverter.intro map_iterator_rbt.Map_iterator_axioms)

hide_const right

definition "compute_min_weight_perfect_matching left right edge_costs right_neighbs
    = hungarian left right edge_costs right_neighbs lookup RBT_Map.update"

definition "compute_max_weight_perfect_matching left right edge_costs right_neighbs
         = compute_min_weight_perfect_matching left right (- edge_costs) right_neighbs"

definition "compute_max_weight_perfect_matching_inv left right edge_costs right_neighbs
         = compute_min_weight_perfect_matching left right 
            (curry (abstract_real_map (lookup (inverted_costs edge_costs)))) right_neighbs"

definition "acompute_min_matching left right edge_costs right_neighbs
            = the (
                compute_min_weight_perfect_matching
                (new_left left right) 
                (new_right left right)
                (curry (abstract_real_map (lookup 
                      (bp_min_costs_to_min_perfect_costs_exec 
                           left right right_neighbs edge_costs))))
                 (lookup (bp_perfect_exec left right)))"

definition "compute_min_weight_matching left right edge_costs right_neighbs
            = extract_mw_matching left right_neighbs edge_costs
               (lookup (acompute_min_matching left right edge_costs right_neighbs))"

definition "compute_max_weight_matching left right edge_costs right_neighbs
         = compute_min_weight_matching left right (- edge_costs) right_neighbs"

definition "compute_max_weight_matching_inv left right edge_costs right_neighbs
         = compute_min_weight_matching left right 
            (curry (abstract_real_map (lookup (inverted_costs edge_costs)))) right_neighbs"

definition "acompute_min_max_matching left right edge_costs right_neighbs
            = the (
                compute_min_weight_perfect_matching 
                (new_left left right) 
                (new_right left right)
                (curry (abstract_real_map (lookup 
                      (bp_min_max_card_costs_to_min_perfect_costs_exec 
                           left right right_neighbs edge_costs))))
                 (lookup (bp_perfect_exec left right)))"

definition "compute_min_weight_max_card_matching left right edge_costs right_neighbs
            = extract_mwmc_matching left right_neighbs
               (lookup (acompute_min_max_matching left right edge_costs right_neighbs))"

definition "compute_max_weight_max_card_matching left right edge_costs right_neighbs
         = compute_min_weight_max_card_matching left right (- edge_costs) right_neighbs"

definition "compute_max_weight_max_card_matching_inv left right edge_costs right_neighbs
         = compute_min_weight_max_card_matching left right 
            (curry (abstract_real_map (lookup (inverted_costs edge_costs)))) right_neighbs"

locale bp_min_weight_matching_algorithms_correct = 
  fixes G::"('v::linorder) set set"
    and edge_costs::"'v \<Rightarrow> 'v \<Rightarrow> real"
    and left::"('v \<times> color) tree"
    and right::"('v \<times> color) tree"
    and right_neighbs::"'v \<Rightarrow> (('v \<times> color) tree) option"

assumes G: "bipartite G (vset_to_set left) (vset_to_set right)"
  "vset_inv left" "vset_inv right"
  "(vset_to_set left) \<union> (vset_to_set right) \<subseteq> Vs G"

"\<And> v N. \<lbrakk>v \<in> vset_to_set left;right_neighbs v= Some N\<rbrakk> 
                 \<Longrightarrow> vset_inv N"
"\<And> v .  v \<in> vset_to_set left 
                     \<Longrightarrow> \<exists> N .right_neighbs v= Some N \<and>
                            vset_to_set N = {u | u. {v, u} \<in> G}"
"\<And> u v. {u, v} \<in> G \<Longrightarrow> edge_costs u v = edge_costs v u"
begin

abbreviation "\<w> \<equiv> setify_weight edge_costs"

interpretation graph_completer_min: graph_completer
  where delete = delete
  and lookup = lookup
  and isin = isin
  and t_set = t_set
  and sel = sel
  and update = update
  and adjmap_inv= M.invar
  and vset_delete = vset_delete
  and vset_inv = vset_inv
  and empty = map_empty
  and vset_empty = vset_empty
  and insert = vset_insert
  and oempty = "\<lambda> x. None"
  and odelete = "\<lambda> x f. fun_upd f x None"
  and olookup = "\<lambda> f x. f x"
  and oinsert = vset_insert
  and oisin = isin
  and ot_set = t_set
  and osel = sel
  and oupdate =  "\<lambda> x y f. fun_upd f x (Some y)"
  and oadjmap_inv="\<lambda> f. True"
  and ovset_empty = vset_empty
  and ovset_delete = vset_delete
  and ovset_inv = vset_inv
  and ovset_fold_reals = "\<lambda> f T x. rbt_set_fold T f x"
  and cempty = Leaf
  and cupdate = update
  and cdelete = delete
  and clookup = lookup
  and cinvar = M.invar
  and obempty = Leaf
  and obupdate = update
  and obdelete= delete
  and oblookup=lookup
  and obinvar =M.invar
  and bempty="\<lambda> x. None"
  and bupdate= "\<lambda> x y f. fun_upd f x (Some y)"
  and bdelete= "\<lambda> x f. fun_upd f x None"
  and blookup= "\<lambda> f x. f x"
  and binvar = "\<lambda> f. True"
  and vset_to_list = "inorder"
  and left = left
  and right = right
  and Gimpl = right_neighbs
  and edge_costs = some_edge_costs for some_edge_costs
proof(rule graph_completer.intro, goal_cases)
  case 1
  then show ?case 
proof(rule graph_completer_spec.intro, goal_cases)
  case 1
  then show ?case 
    by(auto intro!: Pair_Graph_Specs.intro 
          simp add: Map_axioms_as_needed map_empty_def RBT_Set.empty_def S_C.Set_Choose_axioms)
next
  case 2
  then show ?case 
    by(auto intro!: Pair_Graph_Specs.intro trivial_map
          simp add: RBT_Set.empty_def S_C.Set_Choose_axioms)
next
  case 3
  then show ?case
  proof(rule Set_Iterable.intro, goal_cases)
    case (1 S f acc)
    then show ?case 
    using rbt_set_fold_correct[of S f acc] 
    by(auto simp add: vset_inv_def t_inv_def) 
qed
next
  case 4
  then show ?case 
    by (simp add: pd_path_search_spec.missed_map.Map_axioms)
next
  case 6
  then show ?case 
    by (simp add: aug_a_matching.buddy_map.Map_axioms)
next
  case 5
  then show ?case 
    by(simp add: trivial_map)
qed
next
  case 2
  then show ?case
  proof(rule graph_completer_axioms.intro, goal_cases)
    case (1 V)
    then show ?case
      by (simp add: bst_distinct_inorder vset_inv_def)
  next
    case 5
    then show ?case 
    proof(rule, all \<open>rule\<close>, goal_cases)
      case (1 e)
      then obtain x y where e:"e = {x, y}" "x \<in> (vset_to_set left)" "y \<in>(vset_to_set right)"
        using G(1) by(auto elim!: bipartite_edgeE)
      moreover hence "
          right_neighbs x = Some x2 \<Longrightarrow> graph_completer_spec_rbt.old_graph.isin' y x2" for x2
       using "1" by(subst RBT.set_isin)(auto dest: G(6) G(5) simp add:  RBT.set_isin vset_inv_def)
     ultimately have "(x, y) \<in> graph_completer_spec_rbt.old_graph.digraph_abs right_neighbs" 
        by(auto simp add: graph_completer_spec_rbt.old_graph.digraph_abs_def oheighbourhood_def
                          Pair_Graph_Specs.neighbourhood_def[OF 
                            graph_completer_spec_rbt.old_graph.Pair_Graph_Specs_axioms]
                    dest: G(6)
                   split: option.split)
      thus ?case
        using e by auto
    next
      case (2 e)
      then obtain u v where e:"e = {u, v}" "u \<in> vset_to_set left"
        "(u, v) \<in> graph_completer_spec_rbt.old_graph.digraph_abs right_neighbs"
        by auto
      then obtain N where N: "right_neighbs u = Some N" "vset_to_set N = {ua | ua. {u, ua} \<in> G}"
        using G(6)[of u] by auto
      moreover have "graph_completer_spec_rbt.old_graph.isin' v N \<Longrightarrow>
             v \<in> vset_to_set N"
        using N(1) e(2) 
        by(subst (asm) RBT.set_isin)(auto dest: G(5) simp add: vset_inv_def)
      moreover hence "v \<in> vset_to_set N"
        using e
        by(auto simp add: graph_completer_spec_rbt.old_graph.digraph_abs_def
                          oheighbourhood_def N(1)
                           Pair_Graph_Specs.neighbourhood_def[OF 
                            graph_completer_spec_rbt.old_graph.Pair_Graph_Specs_axioms])
     ultimately show ?case 
        using e by simp
    qed     
  next
    case 8
    then show ?case 
      by(auto intro: graph_completer_spec_rbt.old_graph.finite_vsetsI)
  next
    case 9
    then show ?case 
      using G(4) by auto
  qed (simp add: G(1-5))+
qed

interpretation hungarian_same_graph:
  hungarian_method_together_correct G some_edge_costs left right  right_neighbs
  for some_edge_costs
proof(rule hungarian_method_together_correct.intro, goal_cases)
  case (5 v N)
  then show ?case 
    using graph_completer_min.G(3) by presburger
next
  case (6 v)
  then show ?case
    using G(6) by auto
next
  case 4
  show ?case
    using G(4) by auto
qed (simp add: G(1-3))+

lemmas hungarian_same_graph_correct =
  hungarian_same_graph.hungarian_correctness[of edge_costs, OF G(7), simplified]

abbreviation "left' \<equiv> new_left left right"
abbreviation "right' \<equiv> new_right left right"
abbreviation "right_neighbs' \<equiv> lookup (bp_perfect_exec left right)"

abbreviation "G' \<equiv> bp_perfected_G (vset_to_set left) (vset_to_set right)"

lemma completer_R_left_def: "graph_completer_spec_rbt.R left = vset_to_set left"
and completer_R_right_def: "graph_completer_spec_rbt.R right = vset_to_set right"
  by simp+

lemma bipartite_G': "bipartite G' (vset_to_set left') (vset_to_set right')"
  using graph_completer_min.bipartite_perfected
      graph_completer_min.bp_perfected_exec_correct(5,7)
  by(simp add: new_left_def new_right_def)

lemma bp_perfected_L_is_left':
      "bp_perfected_L (vset_to_set left) (vset_to_set right)= vset_to_set left'"
and bp_perfected_R_is_right':
      "bp_perfected_R (vset_to_set left) (vset_to_set right)= vset_to_set right'"
 by (simp add: graph_completer_min.bp_perfected_exec_correct(5,7) new_left_def new_right_def)+

interpretation hungarian_extended_graph:
  hungarian_method_together_correct G' some_edge_costs left' right'  right_neighbs'
  for some_edge_costs
proof(rule hungarian_method_together_correct.intro, goal_cases)
  case 1
  then show ?case 
    using  graph_completer_min.bipartite_perfected
        graph_completer_min.bp_perfected_exec_correct(5,7) 
    by(auto simp add: new_left_def new_right_def)
next
  case 2
  then show ?case 
    by (simp add: graph_completer_min.bp_perfected_exec_correct(6) new_left_def)
next
  case 3
  then show ?case
    by (simp add: graph_completer_min.bp_perfected_exec_correct(8) new_right_def)
next
  case 4
  then show ?case 
    using G(4)
    by(subst bipartite_Vs_of_complete_union_L_R[of G])
      (simp add: hungarian_same_graph.G(1) bp_perfected_L_is_left' bp_perfected_R_is_right')+
next
  case (5 v N)
  then show ?case 
    using  graph_completer_min.bp_perfected_exec_correct(1)
    by(auto simp add: bp_perfect_exec_def )
next
  case (6 v)
  obtain N where N: "right_neighbs' v = Some N" 
    using  "6" graph_completer_min.lefts_have_neighb_set
    by(force simp add: graph_completer_spec_rbt.new_graph.has_neighb_set_def
               completer_R_left_def
        completer_R_right_def bp_perfect_exec_def bp_perfected_L_is_left') 
  hence neighv_is:"N = graph_completer_spec_rbt.new_graph.neighbourhood
                     (graph_completer_spec.bp_perfected_exec lookup RBT_Map.update map_empty
                       vset_empty vset_insert left right Tree2.inorder)
                     v"
    by(auto simp add: graph_completer_spec_rbt.new_graph.neighbourhood_def bp_perfect_exec_def)
  have set_ok: "vset_to_set N = { u | u . {v, u} \<in> G'}"
    unfolding graph_completer_min.bp_perfected_exec_correct(4)[simplified, symmetric]
              graph_completer_spec_rbt.new_graph.digraph_abs_def 
  proof(rule, all \<open>rule\<close>, goal_cases)
    case (1 u)
    then show ?case 
      using  graph_completer_spec_rbt.new_graph.are_connected_abs[OF
              graph_completer_min.bp_perfected_exec_correct(1), of u v]
      by (auto intro!: in_UDI[of v u] 
             simp add: neighv_is N forest_manipulation_spec_i.vset.set_isin
          graph_completer_min.bp_perfected_exec_correct(1))
  next
    case (2 u)
    let ?nbhd = "graph_completer_spec_rbt.new_graph.neighbourhood
                      (graph_completer_spec.bp_perfected_exec lookup RBT_Map.update map_empty
                        vset_empty vset_insert left right Tree2.inorder) "
    have uv_UD:"{v, u} \<in> UD {(u, v) | u v. isin (?nbhd u) v}"
      using 2 by auto
    show ?case 
    proof(cases rule: in_UDE[OF uv_UD])
      case 1
      then show ?thesis 
        by (simp add: forest_manipulation_spec_i.vset.set_isin
            graph_completer_min.bp_perfected_exec_correct(1) neighv_is)
    next
      case 2
      hence "isin (?nbhd u) v" by force
      hence "(u, v) \<in> set (graph_completer_spec.new_edge_list left right Tree2.inorder)"
        using forest_manipulation_spec_i.vset.set_isin graph_completer_min.bp_perfected_exec_correct(1)
          graph_completer_min.directed_perfected graph_completer_min.new_edge_list_is by blast
      hence "v \<in> (vset_to_set right')"
        using graph_completer_min.bp_perfected_exec_correct(7) 
            graph_completer_min.in_new_edgesE
        by(simp add: new_right_def)
      hence False 
        using "6" bipartite_G' by(auto simp add: bipartite_def)
      then show ?thesis 
        by simp
    qed
  qed
  thus ?case 
    using N by auto
qed

lemmas hungarian_other_graph_correct = 
hungarian_extended_graph.hungarian_correctness

lemma compute_min_weight_perfect_matching_correct:
"compute_min_weight_perfect_matching left right edge_costs right_neighbs = None
  \<Longrightarrow> \<nexists> M. perfect_matching G M"
"compute_min_weight_perfect_matching left right edge_costs right_neighbs = Some M
  \<Longrightarrow> min_weight_perfect_matching G \<w> (matching_abstract M)"
  using hungarian_same_graph_correct
   by(auto simp add: compute_min_weight_perfect_matching_def)

(*TODO MOVE*)
lemma upairs_matching_abstract:
 "upairs_of_map (lookup M) = matching_abstract M"
  by(auto simp add: upairs_of_map_def matching_abstract_def
 matching_augmentation_spec.\<M>_def'[OF aug_a_matching.matching_augmentation_spec_axioms])

lemma extract_mw_matching_same:
      "graph_completer_spec.extract_mw_matching (\<lambda>f. f) isin vset_empty (\<lambda>f. f) \<langle>\<rangle> RBT_Map.update
       left edge_costs Tree2.inorder right_neighbs =
       extract_mw_matching left right_neighbs edge_costs"
  by(auto simp add: extract_mw_matching_def)

abbreviation "min_weights_used == (curry (abstract_real_map (lookup 
                      (bp_min_costs_to_min_perfect_costs_exec 
                           left right right_neighbs edge_costs))))"

lemma weights_used_symmetric:
  assumes "{u, v} \<in> G'"
  shows "min_weights_used u v = min_weights_used v u"
  using G(7)  assms 
      graph_completer_min.bp_min_costs_to_min_perfect_costs_exec_correct(3)[of edge_costs]
  by(auto simp add: bp_min_costs_to_min_perfect_costs_exec_def)

lemma balanced_complete_bipartite_G':
 "balanced_complete_bipartite G' (vset_to_set left') (vset_to_set right')"
  using  bp_perfected_L_is_left' bp_perfected_R_is_right'
         graph_completer_min.bp_perfected_props(1) by auto

lemma finite_G': "finite G'"
  using finite_G' hungarian_same_graph.G(1) by fastforce

lemma hungarian_min_not_None:
  "hungarian left' right' min_weights_used right_neighbs' lookup RBT_Map.update \<noteq> None"
  apply(rule ccontr)
  using perfect_matching_in_balanced_complete_bipartite[OF balanced_complete_bipartite_G' finite_G']
  by(auto dest!: hungarian_other_graph_correct(1)[of
         min_weights_used, OF weights_used_symmetric, simplified])

lemma hungarian_min_is_Some:
    "hungarian left' right' min_weights_used right_neighbs' lookup RBT_Map.update =
    Some (acompute_min_matching left right edge_costs right_neighbs)"
  by(auto simp add: acompute_min_matching_def
    compute_min_weight_perfect_matching_def hungarian_min_not_None)

lemma compute_min_weight_correct:
"min_weight_matching G \<w> (matching_abstract
      (compute_min_weight_matching left right edge_costs right_neighbs))"
proof-
  note proof_rule = back_subst[of "min_weight_matching _ _", OF
    graph_completer_min.minimum_weight_matching[of edge_costs,
    simplified graph_completer_min.\<w>_def, simplified upairs_matching_abstract
               extract_mw_matching_same], OF _ _ _  refl]
  show ?thesis
  unfolding compute_min_weight_matching_def
proof(rule proof_rule, goal_cases)
  case (1 u v)
  then show ?case 
    using G(7) by blast
next
  case (2 u v)
  then show ?case 
  proof(rule hungarian_extended_graph.hungarian_symmetric[of min_weights_used],
         unfold bp_min_costs_to_min_perfect_costs_exec_def,
       rule graph_completer_min.bp_min_costs_to_min_perfect_costs_exec_correct(3), goal_cases)
    case (1 u v ua va)
    then show ?case 
      using G(7) by auto
  next
    case (2 u v)
    then show ?case
      by simp
  next
    case 3
    then show ?case 
      using  hungarian_min_is_Some
      by(auto simp add: acompute_min_matching_def
                        bp_min_costs_to_min_perfect_costs_exec_def)
  qed
next
  case 3
  then show ?case 
    using  hungarian_min_is_Some
      hungarian_other_graph_correct(2)[of min_weights_used
        "acompute_min_matching left right edge_costs right_neighbs",
                OF weights_used_symmetric, simplified]
    by(auto simp add: upairs_matching_abstract bp_min_costs_to_min_perfect_costs_exec_def)
qed
qed

lemma extract_mwmc_matching_same:
      "graph_completer_spec.extract_mwmc_matching (\<lambda>f. f) isin vset_empty (\<lambda>f. f) \<langle>\<rangle> RBT_Map.update
       left  Tree2.inorder right_neighbs =
       extract_mwmc_matching left right_neighbs"
  by(auto simp add: extract_mwmc_matching_def)

abbreviation "min_max_card_weights_used == (curry (abstract_real_map (lookup 
                      (bp_min_max_card_costs_to_min_perfect_costs_exec 
                           left right right_neighbs edge_costs))))"

lemma max_card_weights_used_symmetric:
  assumes "{u, v} \<in> G'"
  shows "min_max_card_weights_used u v = min_max_card_weights_used v u"
  using G(7)  assms 
      graph_completer_min.bp_min_max_card_to_min_perfect_costs_exec_correct(3)[of edge_costs]
  by(auto simp add: bp_min_max_card_costs_to_min_perfect_costs_exec_def)

lemma hungarian_min_max_card_not_None:
  "hungarian left' right' min_max_card_weights_used right_neighbs' lookup RBT_Map.update \<noteq> None"
  apply(rule ccontr)
  using perfect_matching_in_balanced_complete_bipartite[OF balanced_complete_bipartite_G' finite_G']
  by(auto dest!: hungarian_other_graph_correct(1)[of
         min_max_card_weights_used, OF max_card_weights_used_symmetric, simplified])

lemma hungarian_min_max_card_is_Some:
    "hungarian left' right' min_max_card_weights_used right_neighbs' lookup RBT_Map.update =
    Some (acompute_min_max_matching left right edge_costs right_neighbs)"
 by(auto simp add: acompute_min_max_matching_def
    compute_min_weight_perfect_matching_def hungarian_min_max_card_not_None)

lemma compute_min_weight_max_card_correct:
  "min_weight_max_card_matching G \<w> (matching_abstract
      (compute_min_weight_max_card_matching left right edge_costs right_neighbs))"
proof-
  note proof_rule =  back_subst[of "min_weight_max_card_matching _ _", OF
    graph_completer_min.minimum_weight_max_card_matching[of edge_costs,
    simplified graph_completer_min.\<w>_def, simplified upairs_matching_abstract
               extract_mwmc_matching_same], OF _ _ _  refl]
  show ?thesis
  unfolding compute_min_weight_max_card_matching_def
proof(rule proof_rule, goal_cases)
  case (1 u v)
  then show ?case 
    using G(7) by blast
next
  case (2 u v)
  then show ?case 
  proof(rule hungarian_extended_graph.hungarian_symmetric[
            of min_max_card_weights_used],
         unfold bp_min_max_card_costs_to_min_perfect_costs_exec_def,
       rule graph_completer_min.bp_min_max_card_to_min_perfect_costs_exec_correct(3), goal_cases)
    case (1 u v ua va)
    then show ?case 
      using G(7) by auto
  next
    case (2 u v)
    then show ?case
      by simp
  next
    case 3
    then show ?case 
      using  hungarian_min_max_card_is_Some
      by(auto simp add: acompute_min_max_matching_def
                        bp_min_max_card_costs_to_min_perfect_costs_exec_def)
  qed
next
  case 3
  then show ?case 
    using  hungarian_min_max_card_is_Some
      hungarian_other_graph_correct(2)[of min_max_card_weights_used
        "acompute_min_max_matching left right edge_costs right_neighbs",
                OF max_card_weights_used_symmetric, simplified]
    by(auto simp add: upairs_matching_abstract
                      bp_min_max_card_costs_to_min_perfect_costs_exec_def)
qed
qed

lemmas minimum_weight_matching_algos_correct = 
  compute_min_weight_perfect_matching_correct
  compute_min_weight_correct
  compute_min_weight_max_card_correct

end

locale bp_matching_algorithms_correct = 
  fixes G::"('v::linorder) set set"
    and edge_costs::"'v \<Rightarrow> 'v \<Rightarrow> real"
    and left::"('v \<times> color) tree"
    and right::"('v \<times> color) tree"
    and right_neighbs::"'v \<Rightarrow> (('v \<times> color) tree) option"

assumes G: "bipartite G (vset_to_set left) (vset_to_set right)"
  "vset_inv left" "vset_inv right"
  "(vset_to_set left) \<union> (vset_to_set right) \<subseteq> Vs G"

"\<And> v N. \<lbrakk>v \<in> vset_to_set left;right_neighbs v= Some N\<rbrakk> 
                 \<Longrightarrow> vset_inv N"
"\<And> v .  v \<in> vset_to_set left 
                     \<Longrightarrow> \<exists> N .right_neighbs v= Some N \<and>
                            vset_to_set N = {u | u. {v, u} \<in> G}"
"\<And> u v. {u, v} \<in> G \<Longrightarrow> edge_costs u v = edge_costs v u"
begin

abbreviation "\<w> \<equiv> setify_weight edge_costs"

interpretation min_version:
  bp_min_weight_matching_algorithms_correct
  G edge_costs left right right_neighbs
  using G(1-6)
  by(auto intro!: bp_min_weight_matching_algorithms_correct.intro dest: G(7))

interpretation max_version:
  bp_min_weight_matching_algorithms_correct
  G "- edge_costs" left right right_neighbs
  using G(1-6)
  by(auto intro!: bp_min_weight_matching_algorithms_correct.intro dest: G(7))

lemma minus_minus_w: "- (\<lambda>e. - min_version.\<w> e) = \<w>" 
  by auto

lemma compute_max_weight_perfect_matching_correct:
"compute_max_weight_perfect_matching left right edge_costs right_neighbs = None
  \<Longrightarrow> \<nexists> M. perfect_matching G M"
"compute_max_weight_perfect_matching left right edge_costs right_neighbs = Some M
  \<Longrightarrow> max_weight_perfect_matching G \<w> (matching_abstract M)"
  using max_version.minimum_weight_matching_algos_correct(1,2)
  by(auto simp add: compute_max_weight_perfect_matching_def
                    min_perfect_and_max_perfect_matching minus_minus_w)

lemma compute_max_weight_correct:
"max_weight_matching G \<w> (matching_abstract
      (compute_max_weight_matching left right edge_costs right_neighbs))"
  using max_version.minimum_weight_matching_algos_correct(3)
  by(auto simp add: compute_max_weight_matching_def
                    min_and_max_matching minus_minus_w)

lemma compute_max_weight_max_card_correct:
  "max_weight_max_card_matching G \<w> (matching_abstract
      (compute_max_weight_max_card_matching left right edge_costs right_neighbs))"
  using max_version.minimum_weight_matching_algos_correct(4)
  by(auto simp add: compute_max_weight_max_card_matching_def
                    min_max_card_and_max_max_card_matching  minus_minus_w)

lemmas bp_weighted_matching_algos_correct =
 min_version.minimum_weight_matching_algos_correct
 compute_max_weight_perfect_matching_correct
 compute_max_weight_correct
 compute_max_weight_max_card_correct
end

locale bp_matching_algorithms_correct_cost_map = 
  fixes G::"('v::linorder) set set"
    and edge_costs::"((('v \<times> 'v) \<times> real) \<times> color) tree"
    and left::"('v \<times> color) tree"
    and right::"('v \<times> color) tree"
    and right_neighbs::"'v \<Rightarrow> (('v \<times> color) tree) option"

assumes G: "bipartite G (vset_to_set left) (vset_to_set right)"
  "vset_inv left" "vset_inv right"
  "(vset_to_set left) \<union> (vset_to_set right) \<subseteq> Vs G"

"\<And> v N. \<lbrakk>v \<in> vset_to_set left;right_neighbs v= Some N\<rbrakk> 
                 \<Longrightarrow> vset_inv N"
"\<And> v .  v \<in> vset_to_set left 
                     \<Longrightarrow> \<exists> N .right_neighbs v= Some N \<and>
                            vset_to_set N = {u | u. {v, u} \<in> G}"
"\<And> u v. {u, v} \<in> G \<Longrightarrow> \<Parallel>lookup edge_costs\<Parallel> (u, v) =  \<Parallel>lookup edge_costs\<Parallel> (v, u)"
"M.invar edge_costs"
begin

abbreviation "\<w> \<equiv> setify_weight (curry \<Parallel>lookup edge_costs\<Parallel>)"

interpretation min_version:
  bp_min_weight_matching_algorithms_correct
  G "curry \<Parallel>lookup edge_costs\<Parallel>" left right right_neighbs
  using G(1-6)
  by(auto intro!: bp_min_weight_matching_algorithms_correct.intro dest: G(7))

lemmas inverted_costs = invert_costs.inverted_costs_correct(2)[OF G(8)]

interpretation max_version:
  bp_min_weight_matching_algorithms_correct
  G "curry \<Parallel>lookup (inverted_costs edge_costs)\<Parallel>" left right right_neighbs
  using G(1-6)
  by(auto intro!: bp_min_weight_matching_algorithms_correct.intro dest: G(7)
        simp add: inverted_costs)

lemma minus_minus_w: "- (\<lambda>e. - min_version.\<w> e) = \<w>" 
"- (\<lambda>e. - \<Parallel>lookup edge_costs\<Parallel> \<langle>e\<rangle>) = (\<lambda>e. \<Parallel>lookup edge_costs\<Parallel> \<langle>e\<rangle>)"
  by auto

lemma compute_max_weight_perfect_matching_correct:
"compute_max_weight_perfect_matching_inv left right edge_costs right_neighbs = None
  \<Longrightarrow> \<nexists> M. perfect_matching G M"
"compute_max_weight_perfect_matching_inv left right edge_costs right_neighbs = Some M
  \<Longrightarrow> max_weight_perfect_matching G \<w> (matching_abstract M)"
  using max_version.minimum_weight_matching_algos_correct(1,2)
  by(auto simp add: compute_max_weight_perfect_matching_inv_def inverted_costs
                    min_perfect_and_max_perfect_matching minus_minus_w)

lemma compute_max_weight_correct:
"max_weight_matching G \<w> (matching_abstract
      (compute_max_weight_matching_inv left right edge_costs right_neighbs))"
  using max_version.minimum_weight_matching_algos_correct(3)
  by(auto simp add: compute_max_weight_matching_inv_def inverted_costs
                    min_and_max_matching minus_minus_w)

lemma compute_max_weight_max_card_correct:
  "max_weight_max_card_matching G \<w> (matching_abstract
      (compute_max_weight_max_card_matching_inv left right edge_costs right_neighbs))"
  using max_version.minimum_weight_matching_algos_correct(4)
  by(auto simp add: compute_max_weight_max_card_matching_inv_def inverted_costs
                    min_max_card_and_max_max_card_matching  minus_minus_w)

lemmas bp_weighted_matching_algos_correct =
 min_version.minimum_weight_matching_algos_correct
 compute_max_weight_perfect_matching_correct
 compute_max_weight_correct
 compute_max_weight_max_card_correct
end
end