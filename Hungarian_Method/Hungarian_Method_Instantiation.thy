theory Hungarian_Method_Instantiation
  imports
    Primal_Dual_Path_Search
    Basic_Matching.Alternating_Forest_Executable
    Ordered_Map_Heap
    Basic_Matching.Matching_Augmentation_Executable
    Init_Potential_Collection
    Hungarian_Method_Top_Loop
    Directed_Set_Graphs.Pair_Graph_RBT
    Graph_Algorithms_Dev.RBT_Map_Extension
begin
section \<open>Instantiation of the Hungarian Method\<close>

text \<open>We use Red-Black-Trees to obtain an executable for the Hungarian Method.
In this theory, we plug the parts together.\<close>

hide_const R

definition "vset_is_empty = (\<lambda> X. X = Leaf)"

text \<open>Total maps are red-black trees whose lookup is completed by a default value. Sets are
      red-black trees without the sentinel @{term nil}. The universe of vertices is everything
      except @{term nil}.\<close>

definition "rbt_upd t k v = update k v t"
definition "rbt_get d t k = (case lookup t k of None \<Rightarrow> d | Some x \<Rightarrow> x)"

lemma rbt_fixed_univ_map: "fixed_univ_map K M.invar rbt_upd (rbt_get d)"
  by unfold_locales (auto simp add: M.map_update M.invar_update rbt_upd_def rbt_get_def)
abbreviation "vset_to_set \<equiv> Tree2.set_tree"

definition "rbt_set_invar nil S = (vset_inv S \<and> nil \<notin> vset_to_set S)"

lemma rbt_fixed_univ_set:
  "fixed_univ_set (- {nil}) (rbt_set_invar nil) vset_to_set
     vset_empty vset_insert vset_delete isin"
  by unfold_locales
     (auto simp add: set.invar_empty[folded RBT_Set.empty_def] set.invar_insert set.invar_delete
                     set.set_empty[folded RBT_Set.empty_def] set.set_insert set.set_delete 
                     set.set_isin rbt_set_invar_def)

global_interpretation aug_a_matching:
  matching_augmentation_spec "- {nil}" M.invar rbt_upd "rbt_get nil" Leaf nil
  for nil
  defines matching_augment_impl = aug_a_matching.augment_impl
    and matching_abstract = aug_a_matching.\<M>
    and matching_invar = aug_a_matching.invar_matching
    and matching_lookup = aug_a_matching.buddy_lookup
  by(auto intro!: matching_augmentation_spec.intro rbt_fixed_univ_map)

lemmas [code] = aug_a_matching.buddy_lookup_def[folded matching_lookup_def]

lemma vset_is_empty: "vset_is_empty T \<longleftrightarrow> vset_to_set T = {}"
  by(auto simp add: vset_is_empty_def)

abbreviation "rbt_iterate \<equiv> (\<lambda> f T init. fold_rbt (\<lambda> x y. f y x) init T)"

global_interpretation forest_manipulation_spec_i: forest_manipulation_spec
  "- {nil}" M.invar rbt_upd "rbt_get nil"
  M.invar rbt_upd "rbt_get nil"
  "rbt_set_invar nil" vset_to_set vset_empty vset_insert vset_delete isin
  rbt_iterate Leaf Leaf nil
  for nil
  defines get_path = forest_manipulation_spec_i.get_path
    and abstract_forest = forest_manipulation_spec_i.abstract_forest
    and extend_forest_even_unclassified =  forest_manipulation_spec_i.extend_forest_even_unclassified
    and empty_forest = forest_manipulation_spec_i.empty_forest
    and get_path_loop = forest_manipulation_spec_i.get_path_loop
  by(auto intro!: forest_manipulation_spec.intro rbt_fixed_univ_map rbt_fixed_univ_set)

lemmas [code] = 
  forest_manipulation_spec_i.get_path_loop.simps[folded get_path_loop_def]
  forest_manipulation_spec_i.get_path_def[folded get_path_def get_path_loop_def]


subsection \<open>A Collection of Iterable Neighbourhoods\<close>

text \<open>A purely functional implementation of the indexed collection of iterable sets used by
      the path search. The neighbourhood of a left vertex \<open>v\<close> is the list of elements of the
      red-black tree @{term "N v"}. The collection itself maps every vertex to the list of its
      neighbours that are still to be iterated (the cursor).\<close>

definition "nb_list N v = (case N v of None \<Rightarrow> [] | Some T \<Rightarrow> Tree2.inorder T)"
definition "nb_cursor C v = (case lookup C v of None \<Rightarrow> [] | Some xs \<Rightarrow> xs)"

definition "nb_invar K N C = 
  (M.invar C \<and> (\<forall> v \<in> K. distinct (nb_list N v)) \<and>
   (\<forall> v. \<exists> ys. nb_list N v = ys @ nb_cursor C v))"

definition "nb_abstract N (C::('v::linorder \<times> 'v list) rbt) v = set (nb_list N v)"
definition "nb_remaining C v = set (nb_cursor C v)"
definition "nb_iterated N C v = set (nb_list N v) - set (nb_cursor C v)"
definition "nb_has C v = (nb_cursor C v \<noteq> [])"
definition "nb_current C v = hd (nb_cursor C v)"
definition "nb_move C v = (case lookup C v of Some (x # xs) \<Rightarrow> update v xs C | _ \<Rightarrow> C)"
definition "nb_reset N C v = update v (nb_list N v) C"

lemma nb_cursor_update: 
  "M.invar C \<Longrightarrow> nb_cursor (update v xs C) u = (if u = v then xs else nb_cursor C u)"
  by(simp add: nb_cursor_def M.map_update)

lemma distinct_suffix: "\<lbrakk>ys = zs @ xs; distinct ys\<rbrakk> \<Longrightarrow> distinct xs"
  by simp

lemma nb_invar_suffix: "nb_invar K N C \<Longrightarrow> \<exists> ys. nb_list N v = ys @ nb_cursor C v"
  by(simp add: nb_invar_def)

lemma nb_indexed_iterable_set:
  "indexed_iterable_set (nb_invar K N) (nb_abstract N) nb_current nb_has
                        (nb_iterated N) nb_remaining nb_move (nb_reset N) K"
proof(unfold_locales, goal_cases)
  case (1 C i)
  then show ?case 
    by(auto simp add: nb_iterated_def nb_remaining_def)
next
  case (2 C i)
  obtain ys where "nb_list N i = ys @ nb_cursor C i"
    using 2(1) by(auto simp add: nb_invar_def)
  then show ?case 
    by(auto simp add: nb_iterated_def nb_remaining_def nb_abstract_def)
next
  case (3 C i)
  then show ?case 
    by(simp add: nb_has_def nb_remaining_def)
next
  case (4 C i)
  then show ?case 
    by(simp add: nb_current_def nb_remaining_def)
next
  case (5 C i)
  show ?case
  proof(cases "nb_cursor C i")
    case (Cons x xs)
    hence lookup_is: "lookup C i = Some (x # xs)"
      by(auto simp add: nb_cursor_def split: option.split_asm)
    have "\<exists> ys. nb_list N v = ys @ nb_cursor (update i xs C) v" for v
    proof(cases "v = i")
      case True
      then obtain ys where "nb_list N i = ys @ x # xs"
        using nb_invar_suffix[OF 5(1), of i] Cons by auto
      then show ?thesis 
        using 5(1) True
        by(auto intro!: exI[of _ "ys @ [x]"] simp add: nb_cursor_update nb_invar_def)
    next
      case False
      then show ?thesis 
        using 5(1) by(simp add: nb_cursor_update nb_invar_def)
    qed
    then show ?thesis 
      using 5(1)
      by(simp add: nb_move_def lookup_is nb_invar_def M.invar_update)
  qed (insert 5(1), auto simp add: nb_move_def nb_cursor_def split: option.split list.split)
next
  case (6 C i j)
  then show ?case 
    by(simp add: nb_abstract_def)
next
  case (7 C i)
  obtain x xs where Cons: "nb_cursor C i = x # xs"
    using 7(3) by(cases "nb_cursor C i")(auto simp add: nb_remaining_def)
  hence lookup_is: "lookup C i = Some (x # xs)"
    by(auto simp add: nb_cursor_def split: option.split_asm)
  obtain ys where "nb_list N i = ys @ x # xs" 
    using nb_invar_suffix[OF 7(1), of i] Cons by auto
  hence "x \<notin> set xs"
    using 7(1,2) by(auto simp add: nb_invar_def)
  then show ?case 
    using 7(1) Cons
    by(auto simp add: nb_move_def lookup_is nb_remaining_def nb_current_def
                      nb_cursor_update nb_invar_def)
next
  case (8 C i)
  obtain x xs where Cons: "nb_cursor C i = x # xs"
    using 8(3) by(cases "nb_cursor C i")(auto simp add: nb_remaining_def)
  hence lookup_is: "lookup C i = Some (x # xs)"
    by(auto simp add: nb_cursor_def split: option.split_asm)
  obtain ys where ys: "nb_list N i = ys @ x # xs" 
    using nb_invar_suffix[OF 8(1), of i] Cons by auto
  hence "x \<notin> set xs"
    using 8(1,2) by(auto simp add: nb_invar_def)
  then show ?case 
    using 8(1) Cons ys
    by(auto simp add: nb_move_def lookup_is nb_iterated_def nb_current_def
                      nb_cursor_update nb_invar_def)
next
  case (9 C i j)
  obtain x xs where Cons: "nb_cursor C i = x # xs"
    using 9(3) by(cases "nb_cursor C i")(auto simp add: nb_remaining_def)
  hence lookup_is: "lookup C i = Some (x # xs)"
    by(auto simp add: nb_cursor_def split: option.split_asm)
  then show ?case 
    using 9(1,4)
    by(auto simp add: nb_move_def nb_remaining_def nb_cursor_update nb_invar_def)
next
  case (10 C i j)
  obtain x xs where Cons: "nb_cursor C i = x # xs"
    using 10(3) by(cases "nb_cursor C i")(auto simp add: nb_remaining_def)
  hence lookup_is: "lookup C i = Some (x # xs)"
    by(auto simp add: nb_cursor_def split: option.split_asm)
  then show ?case 
    using 10(1,4)
    by(auto simp add: nb_move_def nb_iterated_def nb_cursor_update nb_invar_def)
next
  case (11 C i)
  then show ?case 
    by(auto simp add: nb_reset_def nb_invar_def nb_cursor_update M.invar_update)
next
  case (12 C i j)
  then show ?case 
    by(simp add: nb_abstract_def)
next
  case (13 C i)
  then show ?case 
    by(simp add: nb_reset_def nb_iterated_def nb_invar_def nb_cursor_update)
next
  case (14 C i)
  then show ?case 
    by(simp add: nb_reset_def nb_remaining_def nb_abstract_def nb_invar_def nb_cursor_update)
next
  case (15 C i j)
  then show ?case 
    by(simp add: nb_reset_def nb_remaining_def nb_invar_def nb_cursor_update)
next
  case (16 C i j)
  then show ?case 
    by(simp add: nb_reset_def nb_iterated_def nb_invar_def nb_cursor_update)
qed

lemma nb_invar_init:
  assumes "\<And> v T. \<lbrakk>v \<in> K; N v = Some T\<rbrakk> \<Longrightarrow> vset_inv T"
  shows "nb_invar K N Leaf"
proof-
  have "distinct (nb_list N v)" if "v \<in> K" for v
    using assms[OF that]
    by(auto simp add: nb_list_def vset_inv_def intro: RBT_Map_Extension.bst_distinct_inorder 
               split: option.split)
  thus ?thesis
    using M.invar_empty 
    by(auto simp add: nb_invar_def nb_cursor_def RBT_Set.empty_def)
qed

lemma nb_abstract_is:
  "N v = Some T \<Longrightarrow> nb_abstract N C v = vset_to_set T"
  by(simp add: nb_abstract_def nb_list_def)

global_interpretation pd_path_search_spec: primal_dual_path_search_spec
  (*the maps and sets*)
  where K = "- {nil}"
    and ben_invar = M.invar
    and ben_upd = rbt_upd
    and ben_get = "rbt_get nil"
    and missed_invar = M.invar
    and missed_upd = rbt_upd
    and missed_get = "rbt_get 0"
    and potential_invar = M.invar
    and potential_upd = rbt_upd
    and potential_get = "rbt_get 0"
    and vset_invar = "rbt_set_invar nil"
    and vset_to_set = vset_to_set
    and vset_empty = vset_empty
    and vset_insert = vset_insert
    and vset_delete = vset_delete
    and vset_isin = isin
    (*the graph*)
    and G = G
    and left = left
    and right = right
    and buddy_get = buddy_get
    and edge_costs = edge_costs
    and edge_costs_code = edge_costs
    (*the neighbourhoods*)
    and rnb_invar = "nb_invar (vset_to_set left) right_neighbs"
    and rnb_abstract = "nb_abstract right_neighbs"
    and rnb_current = nb_current
    and rnb_has = nb_has
    and rnb_iterated = "nb_iterated right_neighbs"
    and rnb_remaining = nb_remaining
    and rnb_move = nb_move
    and rnb_reset = "nb_reset right_neighbs"
    and rnb_init = Leaf
    (*the forest*)
    and evens = evens
    and odds = odds
    and abstract_forest = "abstract_forest nil"
    and get_path = "get_path nil"
    and extend_forest_even_unclassified = "extend_forest_even_unclassified nil" 
    and empty_forest = empty_forest
    (*the heap*)
    and heap_insert = queue_insert
    and heap_decrease_key = queue_decrease_key
    and heap_empty = queue_empty
    and heap_extract_min = queue_extract_min
    (*the rest*)
    and initial_pot = initial_pot
    and missed_empty = Leaf
    and ben_empty = Leaf
    and vset_is_empty = vset_is_empty
    and vset_iterate_pot = rbt_iterate
    and vset_iterate_ben = rbt_iterate
    and vset_filter = filter_rbt
    and nil = nil
  for nil G left right buddy_get edge_costs right_neighbs initial_pot

defines search_path = pd_path_search_spec.search_path
  and search_path_loop_impl = pd_path_search_spec.search_path_loop_impl
  and new_potential = pd_path_search_spec.new_potential
  and w\<^sub>\<pi> = pd_path_search_spec.w\<^sub>\<pi>
  and path_search_initial_state = pd_path_search_spec.initial_state
  and unmatched_lefts = pd_path_search_spec.unmatched_lefts
  and init_best_even_neighbour = pd_path_search_spec.init_best_even_neighbour
  and update_best_even_neighbours = pd_path_search_spec.update_best_even_neighbours
  and update_best_even_neighbour = pd_path_search_spec.update_best_even_neighbour
  and scan_neighbours = pd_path_search_spec.scan_neighbours
  and relax_neighbour = pd_path_search_spec.relax_neighbour
  and w\<^sub>\<pi>_code = pd_path_search_spec.w\<^sub>\<pi>_code
  and path_search_forest_roots = pd_path_search_spec.forest_roots
  by(auto intro!: primal_dual_path_search_spec.intro rbt_fixed_univ_map 
                  rbt_fixed_univ_set)

hide_const pd_path_search_spec.R Hungarian_Method_Instantiation.pd_path_search_spec.R

text \<open>The code equations of the specification, stated in terms of the defined constants.\<close>

lemmas path_search_defs = search_path_def search_path_loop_impl_def new_potential_def
  w\<^sub>\<pi>_def path_search_initial_state_def unmatched_lefts_def init_best_even_neighbour_def
  update_best_even_neighbours_def update_best_even_neighbour_def scan_neighbours_def
  relax_neighbour_def w\<^sub>\<pi>_code_def path_search_forest_roots_def

lemmas [code] = 
  pd_path_search_spec.search_path_def[folded path_search_defs]
  pd_path_search_spec.search_path_loop_impl.simps[folded path_search_defs]
  pd_path_search_spec.initial_state_def[folded path_search_defs]
  pd_path_search_spec.init_best_even_neighbour_def[folded path_search_defs]
  pd_path_search_spec.update_best_even_neighbours_def[folded path_search_defs]
  pd_path_search_spec.update_best_even_neighbour_def[folded path_search_defs]
  pd_path_search_spec.relax_neighbour_def[folded path_search_defs]
  pd_path_search_spec.scan_neighbours.simps[folded path_search_defs]

text \<open>The initial potential is computed by scanning the neighbourhoods of the left vertices in
      the order of the red-black tree.\<close>

definition "inorder_iterate f init T = foldl f init (Tree2.inorder T)"

global_interpretation init_pot: init_potential_coll_spec
  where potential_upd = rbt_upd
    and potential_get = "rbt_get 0"
    and rnb_current = nb_current
    and rnb_has = nb_has
    and rnb_move = nb_move
    and rnb_reset = "nb_reset right_neighbs"
    and cost = edge_costs
    and vset_iterate = inorder_iterate
  for edge_costs right_neighbs
  defines init_potential_coll = init_pot.init_potential_coll
    and init_potential_step = init_pot.init_step
    and init_potential_scan = init_pot.scan_min
    and init_potential_upd_min = init_pot.upd_min
  done

hide_const left

definition "init_potential edge_costs right_neighbs left =
              snd (init_potential_coll edge_costs right_neighbs Leaf Leaf left)"


global_interpretation hungarian_top_loop:
  hungarian_loop_spec
  where path_search =  "\<lambda> c M P. case search_path nil left
                     (rbt_get nil M)
                     (edge_costs::('a::linorder) \<Rightarrow> 'a \<Rightarrow> real) right_neighbs P of
                        (r, P') \<Rightarrow> (r, M, P', c)"
    and init_ctx = "()"
    and edge_costs = "(\<lambda> e. edge_costs (pick_one e) (pick_another e))"
    and init_potential = "init_potential edge_costs right_neighbs left"
    and potential_abstract = "rbt_get 0"
    and potential_invar = M.invar
    and empty_matching = Leaf
    and matching_invar = "matching_invar nil G"
    and augment = "matching_augment_impl"
    and matching_abstract = "matching_abstract nil"
    and card_L = "size left"
    and card_R = "size right"
    and G = G
  for nil G left right edge_costs right_neighbs
  defines hungarian = hungarian_top_loop.hungarian
    and initial_state =hungarian_top_loop.initial_state
    and hungarianl_loop_impl = hungarian_top_loop.hungarian_loop_impl
  done




hide_const R
  (*TODO MOVE*)
lemma Tree2_set_tree_is_fst_of_tree_set_tree:
  "Tree2.set_tree T = fst ` tree.set_tree T"
  by(induction T)
    (auto simp add: in_image_with_fst_eq)

lemma bst_distinct_preorder: "bst V \<Longrightarrow> distinct (map fst (preorder V))"
  by(induction V rule: preorder.induct)
    (fastforce simp add: Tree2_set_tree_is_fst_of_tree_set_tree[symmetric] in_image_with_fst_eq)+

lemma bst_distinct_postorder: "bst V \<Longrightarrow> distinct (map fst (postorder V))"
  by(induction V rule: postorder.induct)
    (fastforce simp add: Tree2_set_tree_is_fst_of_tree_set_tree[symmetric] in_image_with_fst_eq)+

lemma fold_rbt_as_needed:
  "vset_inv V \<Longrightarrow>
       \<exists>vs. vset_to_set V = set vs \<and>
            distinct vs \<and> fold_rbt (\<lambda>x y. f y x) V init = foldl f init vs"
  by(auto simp add: fold_rbt_is_foldr_of_preorder foldr_conv_foldl
      Tree2_set_tree_is_fst_of_tree_set_tree[symmetric] vset_inv_def
      intro!: exI[of _ "rev (map fst (preorder V))"] bst_distinct_preorder)

lemma fold_rbt_as_needed':
  "vset_inv V \<Longrightarrow>
       \<exists>vs. set vs = vset_to_set V  \<and>
            distinct vs \<and> fold_rbt (\<lambda>x y. f y x) V init = foldl f init vs"
  using  fold_rbt_as_needed by metis

lemma filter_rbt_as_needed:
  assumes "vset_inv V"
  shows "vset_inv (filter_rbt P V)"
    "vset_to_set (filter_rbt P V) = vset_to_set V \<inter> Collect P"
  using RBT.set_filter RBT.invar_filter assms
  by(force simp add: vset_inv_def)+

lemma rbt_map_empty: 
  "M.invar Leaf" 
  "rbt_get d Leaf = (\<lambda> _. d)"

  using M.invar_empty by(auto simp add: RBT_Set.empty_def abstract_real_map_def rbt_get_def)

lemma inorder_iterate_lst:
  "vset_inv V \<Longrightarrow> inorder_iterate f init V = foldl f init (sorted_list_of_set (vset_to_set V))"
proof-
  assume "vset_inv V"
  hence "sorted_wrt (<) (Tree2.inorder V)"
  proof(induction V rule: Tree2.bst.induct)
    case (2 l a b r)
    then show ?case 
      by(force simp add: sorted_wrt_append vset_inv_def)
  qed simp
  thus ?thesis
    by(simp add: inorder_iterate_def strict_sorted_iff sorted_list_of_set.idem_if_sorted_distinct 
           flip: Tree2.set_inorder)
qed

locale hungarian_method_together_correct = 
  fixes G::"('v::linorder) set set"
    and edge_costs::"'v \<Rightarrow> 'v \<Rightarrow> real"
    and left::"('v \<times> color) tree"
    and right::"('v \<times> color) tree"
    and right_neighbs::"'v \<Rightarrow> (('v \<times> color) tree) option"
    and nil::'v

assumes G: "bipartite G (vset_to_set left) (vset_to_set right)"
  "vset_inv left" "vset_inv right"
  "(vset_to_set left) \<union> (vset_to_set right) \<subseteq> Vs G"

  "\<And> v N. \<lbrakk>v \<in> vset_to_set left;right_neighbs v= Some N\<rbrakk>   \<Longrightarrow> vset_inv N"
  "\<And> v .  v \<in> vset_to_set left   \<Longrightarrow> \<exists> N .right_neighbs v= Some N \<and>
                                           vset_to_set N = {u | u. {v, u} \<in> G}"
  and nil: "nil \<notin> Vs G"
begin

abbreviation "L \<equiv> vset_to_set left"
abbreviation "R \<equiv> vset_to_set right"
abbreviation "vset_invar \<equiv> (rbt_set_invar nil)"

lemma rbt_iterate_as_needed:
  "vset_invar V \<Longrightarrow> 
     \<exists>vs. vset_to_set V = set vs \<and> distinct vs \<and> rbt_iterate f init V = foldl f init vs"
  using fold_rbt_as_needed[of V f init] by(simp add: rbt_set_invar_def)

lemma L_R_no_nil: "nil \<notin> L" "nil \<notin> R"
  using G(4) nil by auto

interpretation fmnlp: forest_manipulation
  where K = "- {nil}" 
    and parent_invar = M.invar
    and parent_upd = rbt_upd
    and parent_get = "rbt_get nil"
    and origin_invar = M.invar
    and origin_upd = rbt_upd
    and origin_get = "rbt_get nil"
    and vset_invar = vset_invar
    and vset_to_set = vset_to_set
    and vset_empty = vset_empty
    and vset_insert = vset_insert
    and vset_delete = vset_delete
    and vset_isin = isin
    and vset_iterate = rbt_iterate
    and parent_empty = Leaf
    and origin_empty = Leaf
    and nil = nil
  by(auto intro!: forest_manipulation.intro forest_manipulation_axioms.intro 
       forest_manipulation_spec_i.forest_manipulation_spec_axioms rbt_iterate_as_needed
       simp add: rbt_map_empty)

abbreviation "forest_invar == fmnlp.forest_invar"
abbreviation "init_potential_here \<equiv> init_potential edge_costs right_neighbs left"

interpretation init_pot_thms: init_potential_coll
  where potential_upd = rbt_upd
    and potential_get = "rbt_get 0"
    and rnb_current = nb_current
    and rnb_has = nb_has
    and rnb_move = nb_move
    and rnb_reset = "nb_reset right_neighbs"
    and cost = edge_costs
    and vset_iterate = inorder_iterate
    and potential_invar = M.invar
    and rnb_invar = "nb_invar L right_neighbs"
    and rnb_abstract = "nb_abstract right_neighbs"
    and rnb_iterated = "nb_iterated right_neighbs"
    and rnb_remaining = nb_remaining
    and K = L
    and potential_empty = Leaf
    and vset_to_set = vset_to_set
    and vset_invar = vset_inv
    and lst = sorted_list_of_set
  by(auto intro!: init_potential_coll.intro init_potential_coll_axioms.intro 
        rbt_fixed_univ_map nb_indexed_iterable_set inorder_iterate_lst
       simp add: rbt_map_empty)

lemma init_potential_props:
  "M.invar init_potential_here"
  "\<And> u v N. \<lbrakk>u \<in> L; right_neighbs u = Some N; v \<in> vset_to_set N\<rbrakk> \<Longrightarrow>
            rbt_get 0 init_potential_here u \<le> edge_costs u v"
  "\<And> u. u \<notin> L \<Longrightarrow> rbt_get 0 init_potential_here u = 0"
proof-
  have fin: "finite (nb_abstract right_neighbs Leaf u)" for u
    by(simp add: nb_abstract_def)
  have finL: "finite L" 
    by simp
  have nb0: "nb_invar L right_neighbs Leaf"
    using G(5) by(rule nb_invar_init)
  note props = init_pot_thms.init_potential_coll_props[of Leaf left,
     OF nb0 G(2) finL subset_refl fin]
  show "M.invar init_potential_here"
       "\<And> u. u \<notin> L \<Longrightarrow> rbt_get 0 init_potential_here u = 0"
    using props by(auto simp add: init_potential_def init_potential_coll_def)
  show "\<And> u v N. \<lbrakk>u \<in> L; right_neighbs u = Some N; v \<in> vset_to_set N\<rbrakk> \<Longrightarrow>
            rbt_get 0 init_potential_here u \<le> edge_costs u v"
  proof-
    fix u v N 
    assume a: "u \<in> L" "right_neighbs u = Some N" "v \<in> vset_to_set N"
    hence "v \<in> nb_abstract right_neighbs Leaf u"
      by(simp add: nb_abstract_is[of right_neighbs u N, OF a(2)])
    thus "rbt_get 0 init_potential_here u \<le> edge_costs u v"
      using props(2)[OF a(1)] by(simp add: init_potential_def init_potential_coll_def)
  qed
qed

interpretation  satisfied_simple:
  alternating_forest_spec evens odds "get_path nil" "abstract_forest nil"
  forest_invar roots vset_invar vset_to_set
  unfolding abstract_forest_def get_path_def  
proof(intro alternating_forest_spec.intro, goal_cases)
  case (1 F M) then show ?case by (rule fmnlp.simple_invariant_consequences(1))
next
  case (2 F M) then show ?case by (rule fmnlp.simple_invariant_consequences(2))
next
  case (3 F M) then show ?case using fmnlp.simple_invariant_consequences(3)[OF 3] by blast
next
  case (4 F M) then show ?case using fmnlp.simple_invariant_consequences(3,4,9)[OF 4] by blast
next
  case (5 F M) then show ?case using fmnlp.simple_invariant_consequences(4,9)[OF 5] by blast
next
  case (6 F M) then show ?case by (rule fmnlp.simple_invariant_consequences(6))
next
  case (7 F M) then show ?case by (rule fmnlp.simple_invariant_consequences(8))
next
  case (8 F M) then show ?case by (rule fmnlp.simple_invariant_consequences(9))
next
  case (9 F M) then show ?case by (rule fmnlp.simple_invariant_consequences(10))
next
  case (10 F M v p) then show ?case using fmnlp.get_path_correct(1,3,4,5)[OF 10] by blast
next
  case (11 F M) then show ?case by (rule fmnlp.simple_invariant_consequences(11))
next
  case (12 F M u v) then show ?case using fmnlp.complex_invariant_consequences(1)[OF 12] by blast
next
  case (13 F M u v) then show ?case by (rule fmnlp.complex_invariant_consequences(2))
qed

abbreviation "\<ww> \<equiv> (\<lambda> e. edge_costs (pick_one e) (pick_another e))"

context
  assumes symmetric_weights: "\<And> u v. {u, v} \<in> G \<Longrightarrow> edge_costs u v = edge_costs v u"
begin

lemma w_is_edge_costs: 
  assumes"{u, v} \<in> G" 
  shows  "\<ww> {u, v} = edge_costs u v"
proof-
  have "u \<noteq> v"
    by(rule bipartite_edgeE[OF assms G(1)])
      (auto simp add: doubleton_eq_iff)
  thus ?thesis
    using  pick_one_and_another_props(3)[of "{u, v}", OF exI[of _ u]]
    by(auto simp add: doubleton_eq_iff symmetric_weights[OF assms])
qed

lemma feasible_init:
  "feasible_min_perfect_dual G \<ww> (rbt_get 0 init_potential_here)"
proof(rule feasible_min_perfect_dualI, goal_cases)
  case (1 e u v)
  then obtain u' v' where u'v':  "e = {u', v'}" "u' \<in> L" "v' \<in> R" 
    using G(1)
    by (auto elim!: bipartite_edgeE)
  hence "v' \<notin> L" "u' \<notin> R" "u' \<noteq> v'" 
    using G(4) bipartite_vertex(2)[OF _ G(1)] by auto
  hence pot_v_0:"rbt_get 0 init_potential_here v' = 0"
    using init_potential_props(3) by auto
  have f_of_uv:"(f::_ \<Rightarrow> real) u +  f v = f u' + f v'" for f
    using 1(2) u'v'(1)
    by(auto simp add: doubleton_eq_iff)
  obtain U where neighbsU: "right_neighbs u' = Some U" 
    using u'v'  G(6) by auto
  have v'_in_U: "v' \<in> vset_to_set U"
    using G(6)[OF u'v'(2)] neighbsU "1"(1) u'v'(1) by auto
  show ?case 
    using 1(1)
    by(auto intro!: feasible_min_perfect_dualI v'_in_U
        init_potential_props(2) neighbsU
        simp add: u'v' w_is_edge_costs f_of_uv pot_v_0)
qed

interpretation fe_spec: 
  alternating_forest_ordinary_extension_spec vset_invar vset_to_set evens odds
  "get_path nil" "abstract_forest nil" forest_invar roots
  "extend_forest_even_unclassified nil" empty_forest "- {nil}"
  by(intro alternating_forest_ordinary_extension_spec.intro
      satisfied_simple.alternating_forest_spec_axioms
      alternating_forest_ordinary_extension_spec_axioms.intro)
    (simp_all add:  fmnlp.extension_main_preservation fmnlp.satisfied_simple_extension_precond_same
      fmnlp.extension_abstract_is fmnlp.extension_evens
      fmnlp.empty_forest_correctess  extend_forest_even_unclassified_def 
      abstract_forest_def empty_forest_def)

interpretation matching_augmentation_thms:
  matching_augmentation "- {nil}" M.invar rbt_upd
    "rbt_get nil" Leaf nil
  by(auto intro!: matching_augmentation.intro matching_augmentation_axioms.intro
       aug_a_matching.matching_augmentation_spec_axioms simp add: rbt_map_empty)

lemmas augmentation_correct =
  matching_augmentation_thms.augmentation_correct
  [folded matching_invar_def matching_abstract_def matching_augment_impl_def]

lemmas matching_invarD = aug_a_matching.invar_matchingD
  [of nil G, folded matching_invar_def matching_abstract_def]

lemmas empty_matching_props =
  matching_augmentation_thms.empty_matching_props
  [folded matching_invar_def matching_abstract_def]

abbreviation "path_search_precond \<equiv>
    hungarian_loop_spec.path_search_precond
        (rbt_get 0) M.invar
        (matching_invar nil G)
        (matching_abstract nil) \<ww> G"

abbreviation "search_path_core \<equiv>
   (\<lambda> M \<pi>. search_path nil left (rbt_get nil M)
             edge_costs right_neighbs \<pi>)"

abbreviation "search_path_here \<equiv>
   (\<lambda> c M \<pi>. case search_path_core M \<pi> of (r, \<pi>') \<Rightarrow> (r, M, \<pi>', c))"

abbreviation "good_search_result \<equiv>  
  hungarian_loop_spec.good_search_result (rbt_get 0) M.invar 
     (matching_abstract nil) \<ww> G"

interpretation hungarian_top_loop:
  hungarian_loop
  where path_search = search_path_here
    and edge_costs = \<ww>
    and init_potential = "init_potential_here"
    and potential_abstract = "rbt_get 0"
    and potential_invar = M.invar
    and empty_matching = Leaf
    and matching_invar = "matching_invar nil G"
    and augment = "matching_augment_impl"
    and matching_abstract = "matching_abstract nil"
    and card_L = "size left"
    and card_R = "size right"
    and G = G
    and L = L
    and R = R
    and init_ctx = "()"
    and ctx_invar = "\<lambda> _. True"
proof(rule hungarian_loop.intro, goal_cases)
  case 1
  then show ?case 
    using G(1) by simp
next
  case 2
  then show ?case 
    using G(2)
    by(auto simp add: rbt_size_correct vset_inv_def t_inv_def) 
next
  case 3
  then show ?case 
    using G(3)
    by(auto simp add: rbt_size_correct vset_inv_def t_inv_def)
next
  case 4
  then show ?case by simp
next
  case 5
  then show ?case by simp
next
  case 6
  then show ?case 
    using G(4) by simp
next
  case 7
  then show ?case
    using init_potential_props(1) by auto
next
  case 8
  then show ?case 
    using feasible_init by simp
next
  case (9 M)
  then show ?case 
    using matching_invarD by simp
next
  case 10
  then show ?case 
    using empty_matching_props nil by auto
next
  case 11
  then show ?case 
    using empty_matching_props nil by simp
next
  case (12 M p)
  then show ?case 
    by(rule augmentation_correct(1))
next
  case (13 M p)
  then show ?case 
    by(rule augmentation_correct(2))
next
  case (14 c M \<pi> r M' \<pi>' c')
  note asm = 14(1)
  note path_search_precondD = hungarian_loop_spec.path_search_precondD[OF asm]
  note symmetric_buddiesD = aug_a_matching.symmetric_buddiesD
  have \<M>_is: "pd_path_search_spec.\<M> (rbt_get nil M) nil =
             matching_abstract nil M" 
    by(force simp add: matching_abstract_def pd_path_search_spec.\<M>_def pd_path_search_spec.buddy_def
        aug_a_matching.\<M>_def' aug_a_matching.buddy_lookup_def doubleton_eq_iff)
  interpret pd_path_search: primal_dual_path_search
    where K = "- {nil}"
      and ben_invar = M.invar 
      and ben_upd = rbt_upd
      and ben_get = "rbt_get nil"
      and missed_invar = M.invar
      and missed_upd = rbt_upd
      and missed_get = "rbt_get 0"
      and potential_invar = M.invar
      and potential_upd = rbt_upd
      and potential_get = "rbt_get 0"
      and vset_invar = vset_invar
      and vset_to_set = vset_to_set
      and vset_empty = vset_empty
      and vset_insert = vset_insert
      and vset_delete = vset_delete
      and vset_isin = isin
      and G = G
      and left = left
      and right = right
      and buddy_get = "rbt_get nil M"
      and edge_costs = edge_costs
      and edge_costs_code = edge_costs
      and rnb_invar = "nb_invar L right_neighbs"
      and rnb_abstract = "nb_abstract right_neighbs"
      and rnb_current = nb_current
      and rnb_has = nb_has
      and rnb_iterated = "nb_iterated right_neighbs"
      and rnb_remaining = nb_remaining
      and rnb_move = nb_move
      and rnb_reset = "nb_reset right_neighbs"
      and rnb_init = Leaf
      and evens = evens
      and odds = odds
      and abstract_forest = "abstract_forest nil"
      and get_path = "get_path nil"
      and extend_forest_even_unclassified = "extend_forest_even_unclassified nil" 
      and empty_forest = empty_forest
      and roots = roots
      and forest_invar = forest_invar
      and heap_insert = queue_insert
      and heap_decrease_key = queue_decrease_key
      and heap_empty = queue_empty
      and heap_extract_min = queue_extract_min
      and heap_invar = "queue_invar_in (Vs G)"
      and heap_abstract = queue_abstract
      and initial_pot = \<pi>
      and missed_empty = Leaf
      and ben_empty = Leaf
      and vset_iterate_ben = rbt_iterate
      and vset_iterate_pot = rbt_iterate
      and vset_filter = filter_rbt
      and vset_is_empty = vset_is_empty
      and nil = nil
  proof(rule primal_dual_path_search.intro[OF
        pd_path_search_spec.primal_dual_path_search_spec_axioms], goal_cases)
    case 1
    thus ?case 
      using fe_spec.alternating_forest_ordinary_extension_spec_axioms
      by simp
  next
    case 2
    thus ?case
      by(rule queue_key_value_queue)
  next
    case 3
    thus ?case
      by(rule nb_indexed_iterable_set)
  next
    case 4

    have buddy_is: "pd_path_search_spec.buddy (rbt_get nil M) nil
                    = aug_a_matching.buddy_lookup nil M"
      by(auto intro!: ext simp add: pd_path_search_spec.buddy_def aug_a_matching.buddy_lookup_def)
    have M_is': "{{u, v} |u v. aug_a_matching.buddy_lookup nil M u = Some v} = 
                 matching_abstract nil M"
    proof-
      have "{{u, v} |u v. aug_a_matching.buddy_lookup nil M u = Some v} =
            {{u, v} |u v. Some v = aug_a_matching.buddy_lookup nil M u}"
        by(rule arg_cong[where f = "\<lambda> P. {{u, v} |u v. P u v}"]) (auto intro!: ext)
      thus ?thesis
        using \<M>_is by(simp add: pd_path_search_spec.\<M>_def buddy_is)
    qed
    note sym = aug_a_matching.symmetric_buddiesD[OF matching_invarD(2)[OF path_search_precondD(1)]]
    show ?case
    proof(rule primal_dual_path_search_axioms.intro, goal_cases)
      case 1 thus ?case using G(1) by simp
    next
      case 2 thus ?case using G(2) L_R_no_nil by(simp add: rbt_set_invar_def)
    next
      case 3 thus ?case using G(3) L_R_no_nil by(simp add: rbt_set_invar_def)
    next
      case 4 thus ?case using G(5) by(rule nb_invar_init)
    next
      case (5 v)
      then obtain N where N: "right_neighbs v = Some N" "vset_to_set N = {u | u. {v, u} \<in> G}"
        using G(6)[of v] by auto
      show ?case
        using nb_abstract_is[of right_neighbs v N, OF N(1)] N(2) by simp
    next
      case (6 u v) thus ?case by(rule symmetric_weights)
    next
      case (7 u v)
      thus ?case
        using feasible_min_perfect_dualD[OF path_search_precondD(5) 7 refl]
        by(simp add: w_is_edge_costs[OF 7])
    next
      case (8 u v) thus ?case using sym by(simp add: buddy_is)
    next
      case 9 thus ?case using path_search_precondD(3) by(simp add: buddy_is M_is')
    next
      case (10 u v)
      thus ?case
        by(auto dest!: set_mp[OF path_search_precondD(4)]
            simp add: tight_subgraph_def doubleton_eq_iff
            w_is_edge_costs \<M>_is symmetric_weights)
    next
      case 11 thus ?case using path_search_precondD(2) by simp
    next
      case (17 V f init) 
      thus ?case using fold_rbt_as_needed'[of V f init] by(simp add: rbt_set_invar_def)
    next
      case (18 V f init) 
      thus ?case using fold_rbt_as_needed'[of V f init] by(simp add: rbt_set_invar_def)
    next
      case (19 V P) 
      thus ?case using filter_rbt_as_needed[of V P] by(simp add: rbt_set_invar_def)
    next
      case (20 V P) 
      thus ?case using filter_rbt_as_needed[of V P] by(simp add: rbt_set_invar_def)
    next
      case (21 X) thus ?case by(simp add: vset_is_empty)
    qed (auto simp add: rbt_map_empty)
  qed
  have search_path_is:
    "pd_path_search.search_path = search_path_core M \<pi>"
    by (simp add: search_path_def)
  have M'_is: "M' = M" and core_is: "search_path_core M \<pi> = (r, \<pi>')"
    using 14(3) by(auto split: prod.splits)
  note search_path_correct = pd_path_search.search_path_correct[unfolded search_path_is]
  have same_pot: "\<nexists> p. r = Next_Iteration p \<Longrightarrow> \<pi>' = \<pi>"
    using pd_path_search.not_Next_Iteration_same_potential[unfolded search_path_is core_is]
    by simp
  have good_result: "good_search_result M \<pi>' p" if p: "r = Next_Iteration p" for p
  proof-
    note search_path_in_this_case =
      search_path_correct(3-)[OF core_is[unfolded p], unfolded \<M>_is]
    show ?thesis
    proof(rule hungarian_top_loop.good_search_resultI, goal_cases)
      case 1
      then show ?case 
        using search_path_in_this_case(5) by simp
    next
      case 2
      show ?case
      proof(rule, goal_cases)
        case (1 e)
        then obtain u v where uv: "e = {u, v}" "{u, v} \<in> G"
          using  G(1) bipartite_edgeE[OF _  G(1)] path_search_precondD(3)
          by blast
        show ?case
          using  search_path_in_this_case(2)[OF 1[unfolded uv(1)]]
          by(auto simp add: tight_subgraph_def uv w_is_edge_costs
              intro!: exI[of "\<lambda> u. \<exists> v. _ u v" u] exI[of "\<lambda> u. _ u \<and> _ u" v])
      qed
    next
      case 3
      show ?case 
      proof(rule feasible_min_perfect_dualI, goal_cases)
        case (1 e u v)
        then show ?case 
          using search_path_in_this_case(1)
          by(auto simp add: w_is_edge_costs)
      qed
    next
      case 4
      show ?case 
      proof(rule, goal_cases)
        case (1 e)
        hence "e \<in> G" 
          using search_path_in_this_case(4)
          by (auto dest: path_edges_subset)
        then obtain u v where uv: "e = {u, v}" "{u, v} \<in> G" "u \<noteq> v"
          using  G(1) bipartite_edgeE[OF _  G(1), of e] by blast
        show ?case
          using  search_path_in_this_case(3)[OF 1[unfolded uv(1)]]
          by(auto simp add: tight_subgraph_def uv w_is_edge_costs
              intro!: exI[of "\<lambda> u. \<exists> v. _ u v" u] exI[of "\<lambda> u. _ u \<and> _ u" v])
      qed
    next
      case 5
      then show ?case 
        using search_path_in_this_case(4) by simp
    qed
  qed
  show ?case
  proof(rule hungarian_top_loop.good_searchI, goal_cases)
    case 1
    show ?case
    proof(cases "\<exists> p. r = Next_Iteration p")
      case True
      then obtain p where p: "r = Next_Iteration p" by auto
      note gsr = hungarian_top_loop.good_search_resultD[OF good_result[OF p]]
      show ?thesis 
        using gsr path_search_precondD(1,3)
        by(auto intro!: hungarian_top_loop.path_search_precondI simp add: M'_is)
    next
      case False
      thus ?thesis 
        using asm by(simp add: same_pot M'_is)
    qed
  next
    case 2
    show ?case by(simp add: M'_is)
  next
    case 3
    show ?case
    proof(rule allI, goal_cases)
      case (1 B)
      obtain \<pi>'' where pi'':
        "\<And> u v. {u, v} \<in> G \<Longrightarrow> \<pi>'' u + \<pi>'' v \<le> \<w> u v"
        "B+1 \<le> sum \<pi>'' (pd_path_search.L \<union> pd_path_search.R)"
        using search_path_correct(2)[unfolded core_is, of "B+1"] 3 by auto
      show ?case
        using pi''(2)
        by(auto intro!: exI[of _ \<pi>''] feasible_min_perfect_dualI pi''(1)
            simp add: w_is_edge_costs)
    qed
  next
    case 4
    thus ?case 
      using search_path_correct(1)[unfolded core_is] by(simp add: \<M>_is M'_is)
  next
    case (5 p)
    thus ?case
      using good_result by(simp add: M'_is)
  qed
qed simp_all

lemmas hungarian_correctness = 
   hungarian_top_loop.hungarian_correctness[folded hungarian_def]
   hungarian_top_loop.hungarian_final_invar[folded hungarian_def]

lemma hungarian_symmetric:
  assumes "hungarian nil left right edge_costs right_neighbs = Some M"
  shows   "matching_lookup nil M u = Some v \<longleftrightarrow> 
           matching_lookup nil M v = Some u"
  using matching_invarD(2)[OF hungarian_correctness(3)[OF assms]]
  by(simp add: aug_a_matching.symmetric_buddies_def matching_lookup_def)
 
end
end

end