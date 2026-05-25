theory Hungarian_Method_Instantiation
  imports  Primal_Dual_Path_Search Basic_Matching.Alternating_Forest_Executable 
    Ordered_Map_Heap Naive_Primal_Dual Basic_Matching.Matching_Augmentation_Executable
    Hungarian_Method_Top_Loop
    Directed_Set_Graphs.Pair_Graph_RBT
    Graph_Algorithms_Dev.RBT_Map_Extension
begin
section \<open>Instantiation of the Hungarian Method\<close>

text \<open>We use Red-Black-Trees to obtain an executable for the Hungarian Method.
In this theory, we plug the parts together.\<close>

hide_const R

definition "vset_is_empty = (\<lambda> X. X = Leaf)"

text \<open>Let's instantiate the path search\<close>

lemma Map_axioms_as_needed: "Map \<langle>\<rangle> RBT_Map.update RBT_Map.delete lookup M.invar"
  using M.Map_axioms
  by(auto simp add: RBT_Set.empty_def)

global_interpretation aug_a_matching:
  matching_augmentation_spec Leaf update delete lookup M.invar
  defines matching_augment_impl = aug_a_matching.augment_impl
    and matching_abstract = aug_a_matching.\<M>
    and matching_invar = aug_a_matching.invar_matching
  by(auto intro!: matching_augmentation_spec.intro 
      simp add:  Map_axioms_as_needed)

abbreviation "vset_to_set \<equiv> Tree2.set_tree"

lemma vset_is_empty: "vset_is_empty T \<longleftrightarrow> vset_to_set T = {}"
  by(auto simp add: vset_is_empty_def)

global_interpretation forest_manipulation_spec_i: forest_manipulation_spec
  Leaf update delete lookup  M.invar
  Leaf update delete lookup  M.invar
  vset_empty vset_insert vset_delete isin  vset_to_set  vset_inv vset_iterate
  for vset_iterate
  defines get_path = forest_manipulation_spec_i.get_path
    and abstract_forest = forest_manipulation_spec_i.abstract_forest
    and extend_forest_even_unclassified =  forest_manipulation_spec_i.extend_forest_even_unclassified
    and empty_forest = forest_manipulation_spec_i.empty_forest
  by(auto intro!: forest_manipulation_spec.intro aug_a_matching.buddy_map.Map_axioms
      simp add: RBT_Set.empty_def set.Set_axioms)

global_interpretation pd_path_search_spec: primal_dual_path_search_spec
  (*the graph*)
  where G = G
    and left = left
    and right = right
    and buddy = buddy
    and edge_costs = edge_costs
    and right_neighbs = right_neighbs
    (*the forest*)
    and evens = evens
    and odds = odds
    and abstract_forest = "abstract_forest"
    and get_path = "get_path"
    and extend_forest_even_unclassified = 
    "extend_forest_even_unclassified" 
    and empty_forest = "empty_forest vset_iterate1"
    (*the heap*)
    and heap_insert = queue_insert
    and heap_decrease_key = queue_decrease_key
    and heap_empty = queue_empty
    and heap_extract_min = queue_extract_min
    (*the potential*)
    and initial_pot = initial_pot
    and potential_lookup = potential_lookup
    and potential_upd = potential_upd
    (*missed change in potential*)
    and missed_lookup = lookup
    and missed_empty = Leaf
    and missed_upd = update
    and missed_invar = M.invar
    and missed_delete = delete
    (*best even neighbour map*)
    and ben_upd = update
    and ben_lookup = lookup
    and ben_empty = Leaf
    and ben_delete = delete
    and ben_invar = M.invar
    (*sets of vertices*)
    and vset_isin= isin
    and vset_to_set = Tree2.set_tree
    and vset_insert = vset_insert
    and vset_empty = vset_empty
    and vset_delete = vset_delete
    and vset_invar = vset_inv
    and vset_is_empty = vset_is_empty
    and vset_iterate_pot = vset_iterate2
    and vset_iterate_ben = vset_iterate3
    and vset_filter = vset_filter
  for (*the graph*) G left right buddy edge_costs right_neighbs
    (*the potential*) initial_pot potential_lookup potential_upd
    (*sets of vertices*) vset_iterate1 vset_iterate2 vset_iterate3 vset_filter

defines search_path = pd_path_search_spec.search_path
  and search_path_loop_impl = pd_path_search_spec.search_path_loop_impl
  and new_potential = pd_path_search_spec.new_potential
  and w\<^sub>\<pi> = pd_path_search_spec.w\<^sub>\<pi>
  and path_search_initial_state = pd_path_search_spec.initial_state
  and unmatched_lefts = pd_path_search_spec.unmatched_lefts
  and init_best_even_neighbour = pd_path_search_spec.init_best_even_neighbour
  and update_best_even_neighbours = pd_path_search_spec.update_best_even_neighbours
  and update_best_even_neighbour = pd_path_search_spec.update_best_even_neighbour
  and path_search_forest_roots = pd_path_search_spec.forest_roots
  by(auto intro!: primal_dual_path_search_spec.intro  Map_axioms_as_needed set.Set_axioms
      simp add: RBT_Set.empty_def)
hide_const pd_path_search_spec.R Hungarian_Method_Instantiation.pd_path_search_spec.R

(*manual fix of "partially applied constant on left hand side of equation"*)
lemmas [code] = 
  pd_path_search_spec.search_path_def[folded  search_path_def  path_search_initial_state_def]
  pd_path_search_spec.initial_state_def[folded path_search_initial_state_def]

hide_const nbs potential_update

locale build_init_potential_spec =
  potential_map: Map potential_empty potential_upd potential_delete 
  potential_lookup potential_invar
  for potential_empty potential_upd potential_delete 
    and potential_lookup::"'potential \<Rightarrow> 'v \<Rightarrow> real option" and potential_invar +
  fixes   vs::"'vset"
    and   neighbs::"'v \<Rightarrow> 'vset option"
    and   vset_to_set::"'vset \<Rightarrow> 'v set"
    and   vset_invar::"'vset \<Rightarrow> bool"
    and   edge_costs::"'v \<Rightarrow> 'v \<Rightarrow> real"
    and   vset_iterate:: "('potential \<Rightarrow> 'v \<Rightarrow> 'potential)
                            \<Rightarrow> 'potential \<Rightarrow> 'vset \<Rightarrow> 'potential"
begin

definition "init_potential = 
  vset_iterate (\<lambda> \<pi> u. case neighbs u of None \<Rightarrow> \<pi>
                | Some nbs \<Rightarrow>
             vset_iterate (\<lambda> \<pi> v. (case potential_lookup \<pi> u of
                               None \<Rightarrow> potential_upd u (edge_costs u v) \<pi>
                              | Some r \<Rightarrow> if r \<le> edge_costs u v then \<pi>
                                          else potential_upd u (edge_costs u v) \<pi>))
                  \<pi>  nbs)
        potential_empty vs"

lemmas [code] = init_potential_def
end

global_interpretation build_init_pot: build_init_potential_spec
  where potential_lookup = lookup 
    and potential_upd = update
    and potential_empty = Leaf
    and potential_delete = delete
    and potential_invar = M.invar
    and edge_costs = edge_costs
    and vset_iterate = vset_iterate
    and neighbs = neighbs 
    and vs = vs
  for edge_costs vset_iterate neighbs vs
  defines init_potential = build_init_pot.init_potential
  by(auto intro!: build_init_potential_spec.intro Map_axioms_as_needed)

locale build_init_potential = 
  build_init_potential_spec+
  assumes  vs: "vset_invar vs"
    and neighbs: "\<And> v N. \<lbrakk> v \<in> vset_to_set vs; neighbs v = Some N\<rbrakk> \<Longrightarrow> vset_invar N"
    and vset: "\<And> V f init. vset_invar V \<Longrightarrow> \<exists> vs. vset_to_set V = set vs \<and> distinct vs
                    \<and> vset_iterate f init V = foldl f init vs"
begin

lemmas potential = 
  potential_map.invar_empty
  potential_map.map_empty
  potential_map.invar_update
  potential_map.map_update

definition "less_than_edgs_bet p E = 
           (\<forall> e \<in> E. p (fst e) \<le> edge_costs (fst e) (snd e))" 


lemma less_than_edgs_bet_empty: "less_than_edgs_bet p {}"
  by(auto simp add: less_than_edgs_bet_def)

lemma init_potential_props:
  "potential_invar init_potential"
  "\<And> u v N. \<lbrakk>u \<in> vset_to_set vs; neighbs u = Some N; v \<in> vset_to_set N\<rbrakk> \<Longrightarrow>
            abstract_real_map (potential_lookup init_potential) u \<le> edge_costs u v"
  "dom (potential_lookup init_potential) = 
    { v| v x. v \<in> vset_to_set vs \<and> neighbs v \<noteq> None \<and>
           vset_to_set (the (neighbs v)) \<noteq> {}}"
proof-
  define inner_f where "inner_f = (\<lambda> u \<pi> v. (case potential_lookup \<pi> u of
                               None \<Rightarrow> potential_upd u (edge_costs u v) \<pi>
                              | Some r \<Rightarrow> if r \<le> edge_costs u v then \<pi>
                                          else potential_upd u (edge_costs u v) \<pi>))"
  define outer_f where "outer_f = (\<lambda> \<pi> u. case neighbs u of None \<Rightarrow> \<pi>
                | Some nbs \<Rightarrow> vset_iterate (inner_f u) \<pi> nbs)"
  have inner_f_invar_pres: "potential_invar \<pi> \<Longrightarrow> potential_invar (inner_f u \<pi> v)" for u \<pi> v
    by(auto simp add: inner_f_def potential(3) split: option.split)
  have inner_f_prop_pres: 
    "less_than_edgs_bet (abstract_real_map (potential_lookup (inner_f u \<pi> v)))
           (Set.insert (u, v) E)"
    "fst ` (Set.insert (u, v) E) = dom (potential_lookup (inner_f u \<pi> v))"
    if "less_than_edgs_bet (abstract_real_map (potential_lookup \<pi>)) E" 
      "potential_invar \<pi>" 
      "fst ` E = dom (potential_lookup \<pi>)"for E \<pi> u v
    using  that 
    by(auto simp add: inner_f_def less_than_edgs_bet_def abstract_real_map_def
        potential(4) split: option.split)
  have inner_fold_invar_pres:
    "potential_invar (foldl (inner_f u) \<pi> xs)"
    if "potential_invar \<pi>" for u \<pi> xs
  proof-
    define ys where "ys = rev xs"
    show ?thesis
      using that
      unfolding foldl_conv_foldr ys_def[symmetric]
      by(induction ys)
        (auto intro!: inner_f_invar_pres)
  qed
  have inner_fold_props_pres:
    "less_than_edgs_bet (abstract_real_map (potential_lookup (foldl (inner_f u) \<pi> xs)))
           (E \<union> {(u, v) | v. v \<in> set xs})" (is ?rslt1)
    "fst `  (E \<union> {(u, v) | v. v \<in> set xs}) = dom (potential_lookup (foldl (inner_f u) \<pi> xs))" (is ?rslt2)
    if "less_than_edgs_bet (abstract_real_map (potential_lookup \<pi>)) E" 
      "potential_invar \<pi>" 
      "fst ` E = dom (potential_lookup \<pi>)"
    for u \<pi> xs E
  proof-
    define ys where "ys = rev xs"
    have  "?rslt1 \<and>?rslt2"
      using that 
      unfolding foldl_conv_foldr ys_def[symmetric] set_rev[of xs, symmetric]
    proof(induction ys)
      case Nil
      then show ?case by auto
    next
      case (Cons y ys)
      note IH_applied = conjunct1[OF Cons(1)[OF Cons(2,3,4)]] 
        conjunct2[OF Cons(1)[OF Cons(2,3,4)]]
      note potential_now = inner_fold_invar_pres[OF Cons(3), of u "rev ys",
          simplified foldl_conv_foldr rev_rev_ident]
      note inner_f_props_applied = inner_f_prop_pres[OF 
          IH_applied(1) potential_now IH_applied(2)] 

      show ?case 
      proof(rule, goal_cases)
        case 1
        show ?case
          apply (subst foldr_Cons o_apply)+
          apply(rule rev_iffD2[OF inner_f_props_applied(1)[of u y]])
          apply(rule arg_cong[of "_ ::_ set"])
          by auto
      next
        case 2
        show ?case
          apply (subst foldr_Cons o_apply inner_f_props_applied(2)[symmetric])+         
          by force
      qed
    qed
    thus ?rslt1 ?rslt2 
      by auto
  qed
  let ?new_es = "{(u, v) | u v. u \<in> vset_to_set vs \<and> neighbs u \<noteq> None \<and> v \<in> vset_to_set (the (neighbs u))}"
  have outer_iteration_pres:
    "potential_invar (vset_iterate outer_f \<pi> vs)" (is ?rslt0)
    "less_than_edgs_bet (abstract_real_map (potential_lookup (vset_iterate outer_f \<pi> vs)))
           (E \<union> ?new_es)" (is ?rslt1)
    "fst `  (E \<union> ?new_es) = dom (potential_lookup (vset_iterate outer_f \<pi> vs))" (is ?rslt2)
    if "less_than_edgs_bet (abstract_real_map (potential_lookup \<pi>)) E" 
      "potential_invar \<pi>" 
      "fst ` E = dom (potential_lookup \<pi>)"
    for \<pi> E 
  proof-
    obtain vlist where vlist: "vset_to_set vs = set vlist" "distinct vlist" 
      "vset_iterate outer_f \<pi> vs = foldl outer_f \<pi> vlist"
      using vset vs by blast
    define vvs where "vvs = rev vlist"
    have vvs_in_vs: "set vvs \<subseteq> vset_to_set vs"
      by(auto simp add: vvs_def vlist(1))
    have "?rslt0 \<and> ?rslt1 \<and> ?rslt2"
      using that
      unfolding foldl_conv_foldr vvs_def[symmetric] set_rev[of vlist, symmetric] vlist(1,3)
      using vvs_in_vs
    proof(induction vvs)
      case Nil
      then show ?case by auto
    next
      case (Cons u vvs)
      hence vvs_in_vs: "set vvs \<subseteq> vset_to_set vs" by auto
      note IH_applied_all = Cons(1)[OF Cons(2,3,4) vvs_in_vs]
      note IH_applied = conjunct1[OF IH_applied_all]
        conjunct1[OF conjunct2[OF IH_applied_all]]
        conjunct2[OF conjunct2[OF IH_applied_all]]
      show ?case
        apply(subst foldr_Cons o_apply)+ 
        apply(subst outer_f_def, subst (3) outer_f_def, subst (5) outer_f_def)
      proof(cases "neighbs u", goal_cases)
        case 1
        note one = this
        show ?case 
          apply(subst 1 option.case(1))+
        proof(rule conjI[OF IH_applied(1)], rule, goal_cases)
          case 1
          show ?case
            apply(rule rev_iffD2[OF IH_applied(2)])
            apply(rule arg_cong[of "_ ::_ set"])
            using one by auto
        next
          case 2
          show ?case
            using one
            by(subst IH_applied(3)[symmetric]) auto
        qed
      next
        case (2 N)
        note two = this
        have vset_invar_N:"vset_invar N"
          using "2" neighbs Cons.prems(4) by auto
        then obtain ns where ns: "vset_to_set N = set ns" "distinct ns"
          "vset_iterate (inner_f u) (foldr (\<lambda>x y. outer_f y x) vvs \<pi>) N =
                foldl (inner_f u) (foldr (\<lambda>x y. outer_f y x) vvs \<pi>) ns"
          using vset by blast
        show ?case 
          apply(subst 2 option.cases(2) ns)+
        proof(rule, goal_cases)
          case 1
          show ?case
            apply(rule rev_iffD2[OF inner_fold_invar_pres[OF IH_applied(1)]])
            by auto
        next
          case 2
          show ?case
          proof(rule, goal_cases)
            case 1
            show ?case
              apply(rule rev_iffD2[OF inner_fold_props_pres(1)[OF 
                      IH_applied(2,1,3), of u ns]])
              apply(rule arg_cong[of "_ ::_ set"])
              using two ns(1)
              by auto
          next 
            case 2
            show ?case
              apply(subst inner_fold_props_pres(2)[OF IH_applied(2,1,3),
                    of u ns, symmetric])
              using two ns(1) by auto
          qed
        qed
      qed
    qed

    thus ?rslt0 ?rslt1 ?rslt2 
      by auto
  qed
  note final_props =  outer_iteration_pres[OF less_than_edgs_bet_empty potential(1),
      simplified potential(2) Un_empty_left]
  note final_props' = final_props(1,2)[simplified dom_empty image_empty, OF refl]
    final_props(3)[OF trans[OF image_empty dom_empty[symmetric]]]

  have init_pot_is: "init_potential = vset_iterate outer_f potential_empty vs"
    by(subst init_potential_def outer_f_def inner_f_def)+ simp
  show  "potential_invar init_potential"
    "\<And> u v N. \<lbrakk>u \<in> vset_to_set vs; neighbs u = Some N; v \<in> vset_to_set N\<rbrakk> \<Longrightarrow>
            abstract_real_map (potential_lookup init_potential) u \<le> edge_costs u v"
    "dom (potential_lookup init_potential) = 
      { v | v x. v \<in> vset_to_set vs \<and> neighbs v \<noteq> None \<and>
           vset_to_set (the (neighbs v)) \<noteq> {}}"
    using final_props'(1,2)  final_props'(3)
    by(force simp add: init_pot_is less_than_edgs_bet_def final_props'(3)[symmetric])+
qed
end

hide_const left

definition "default_neighb D neighbs = (\<lambda> v. (case neighbs v of None \<Rightarrow> D
                                                | Some N \<Rightarrow> N))"

global_interpretation hungarian_top_loop:
  hungarian_loop_spec
  where path_search =  "\<lambda> M P. search_path left (lookup M)
                     (edge_costs::('a::linorder) \<Rightarrow> 'a \<Rightarrow> real) 
                     (default_neighb vset_empty right_neighbs) P potential_lookup potential_upd 
                     (\<lambda> f T init. fold_rbt (\<lambda> x y. f y x) init T)
                     (\<lambda> f T init. fold_rbt (\<lambda> x y. f y x) init T)
                     (\<lambda> f T init. fold_rbt (\<lambda> x y. f y x) init T)
                     filter_rbt"
    and edge_costs = "(\<lambda> e. edge_costs (pick_one e) (pick_another e))"
    and init_potential = "init_potential edge_costs 
                          (\<lambda> f T init. fold_rbt (\<lambda> x y. f y x) init T) right_neighbs left"
    and potential_abstract = "(\<lambda> \<pi> v. abstract_real_map (potential_lookup \<pi>) v)"
    and potential_invar = potential_invar
    and empty_matching = Leaf
    and matching_invar = "matching_invar  G"
    and augment = "matching_augment_impl"
    and matching_abstract = "matching_abstract"
    and card_L = "size left"
    and card_R = "size right"
    and G = G
  for 
    (*the graph*) G left right buddy edge_costs right_neighbs
    (*the potential*) initial_pot potential_lookup potential_upd empty_potential
    potential_invar
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

locale hungarian_method_together_correct = 
  fixes G::"('v::linorder) set set"
    and edge_costs::"'v \<Rightarrow> 'v \<Rightarrow> real"
    and left::"('v \<times> color) tree"
    and right::"('v \<times> color) tree"
    and right_neighbs::"'v \<Rightarrow> (('v \<times> color) tree) option"

assumes G: "bipartite G (vset_to_set left) (vset_to_set right)"
  "vset_inv left" "vset_inv right"
  "(vset_to_set left) \<union> (vset_to_set right) \<subseteq> Vs G"

  "\<And> v N. \<lbrakk>v \<in> vset_to_set left;right_neighbs v= Some N\<rbrakk>   \<Longrightarrow> vset_inv N"
  "\<And> v .  v \<in> vset_to_set left   \<Longrightarrow> \<exists> N .right_neighbs v= Some N \<and>
                                           vset_to_set N = {u | u. {v, u} \<in> G}"
begin

lemmas parent = 
  M.invar_empty
  M.map_empty
  M.invar_update
  M.map_update

lemmas potential = parent

lemmas origin = parent

lemmas vset =
  set.invar_empty[folded RBT_Set.empty_def]
  set.set_empty[folded RBT_Set.empty_def]
  set.invar_insert
  set.set_insert
  set.set_isin

lemmas missed = origin

lemmas best_even_neighbour = origin

interpretation fmnlp: forest_manipulation
  where vset_iterate = "\<lambda> f T init. fold_rbt (\<lambda> x y. f y x) init T"
    and vset_empty = vset_empty
    and vset_invar = vset_inv
    and vset_to_set = vset_to_set
    and vset_insert = vset_insert
    and vset_isin = isin
    and vset_delete = vset_delete
    and parent_empty = Leaf
    and parent_upd = update
    and parent_delete = delete
    and parent_lookup = lookup 
    and parent_invar = M.invar
    and origin_empty = Leaf
    and origin_upd = update
    and origin_delete = delete
    and origin_lookup = lookup
    and origin_invar = M.invar
  using vset(1-5) 
  by(auto intro!: forest_manipulation_axioms.intro fold_rbt_as_needed
      forest_manipulation.intro[OF forest_manipulation_spec_i.forest_manipulation_spec_axioms])

abbreviation "forest_invar == fmnlp.forest_invar"
abbreviation "L \<equiv> vset_to_set left"
abbreviation "R \<equiv> vset_to_set right"
abbreviation "init_potential_here \<equiv> 
  init_potential edge_costs (\<lambda> f T init. fold_rbt (\<lambda> x y. f y x) init T) right_neighbs left"

interpretation build_init_pot_thms: build_init_potential
  where potential_lookup = lookup 
    and potential_upd = update
    and potential_empty = Leaf
    and potential_invar = M.invar
    and potential_delete = delete
    and edge_costs = edge_costs
    and vset_iterate = "\<lambda> f T init. fold_rbt (\<lambda> x y. f y x) init T"
    and neighbs =  right_neighbs
    and vs = left
    and vset_to_set = vset_to_set
    and vset_invar = vset_inv
  using  G(2,5)
  by(force intro!: build_init_potential.intro fold_rbt_as_needed
      build_init_potential_axioms.intro
      simp add: vset potential build_init_pot.build_init_potential_spec_axioms)

lemma init_potential_def': 
  "build_init_pot_thms.init_potential = init_potential_here"
  by(simp add: build_init_potential_spec.init_potential_def
      init_potential_def )

lemmas init_potential_props=
  build_init_pot_thms.init_potential_props[unfolded init_potential_def']

interpretation  satisfied_simple:
  alternating_forest_spec evens odds "get_path" "abstract_forest"
  forest_invar roots vset_inv vset_to_set
  unfolding abstract_forest_def get_path_def  
  by(intro alternating_forest_spec.intro 
      fmnlp.simple_invariant_consequences fmnlp.complex_invariant_consequences(1,2)
      | assumption | rule conjI  fmnlp.get_path_correct(1,2,3,4,5))+

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
  "feasible_min_perfect_dual G \<ww> (abstract_real_map (lookup init_potential_here))"
proof(rule feasible_min_perfect_dualI, goal_cases)
  case (1 e u v)
  then obtain u' v' where u'v':  "e = {u', v'}" "u' \<in> L" "v' \<in> R" 
    using G(1)
    by (auto elim!: bipartite_edgeE)
  hence "v' \<notin> L" "u' \<notin> R" "u' \<noteq> v'" 
    using G(4) bipartite_vertex(2)[OF _ G(1)] by auto
  hence pot_v_0:"abstract_real_map (lookup init_potential_here) v' = 0"
    using init_potential_props(3)
    by(auto intro!: abstract_real_map_outside_dom dest: domI)
  have f_of_uv:"(f::_ \<Rightarrow> real) u +  f v = f u' + f v'" for f
    using 1(2) u'v'(1)
    by(auto simp add: doubleton_eq_iff)
  obtain U where neighbsU: "right_neighbs u' = Some U" 
    using u'v'  G(6) by auto
  hence v'_in_U: "v' \<in> vset_to_set U"
    using "1"(1) G(6) u'v'(1,2) by force
  show ?case 
    using 1(1)
    by(auto intro!: feasible_min_perfect_dualI v'_in_U
        init_potential_props(2) neighbsU
        simp add: u'v' w_is_edge_costs f_of_uv pot_v_0)
qed

interpretation fe_spec: 
  alternating_forest_ordinary_extension_spec vset_inv vset_to_set evens odds
  "get_path " "abstract_forest" forest_invar roots vset_empty
  "extend_forest_even_unclassified"
  "empty_forest (\<lambda> f T init. fold_rbt (\<lambda> x y. f y x) init T)"
  by(intro alternating_forest_ordinary_extension_spec.intro
      satisfied_simple.alternating_forest_spec_axioms
      alternating_forest_ordinary_extension_spec_axioms.intro)
    (simp_all add:  fmnlp.extension_main_preservation fmnlp.satisfied_simple_extension_precond_same
      fmnlp.extension_abstract_is fmnlp.extension_evens fmnlp.extension_odds fmnlp.extension_roots 
      fmnlp.empty_forest_correctess  extend_forest_even_unclassified_def 
      abstract_forest_def empty_forest_def)

interpretation matching_augmentation_thms:
  matching_augmentation Leaf update delete lookup M.invar
  using aug_a_matching.matching_augmentation_spec_axioms
  by(auto intro!: matching_augmentation.intro)

lemmas augmentation_correct =
  matching_augmentation_thms.augmentation_correct
  [folded matching_invar_def matching_abstract_def matching_augment_impl_def]

lemmas matching_invarD = aug_a_matching.invar_matchingD
  [of G, folded matching_invar_def matching_abstract_def]

lemmas empty_matching_props =
  matching_augmentation_thms.empty_matching_props
  [folded matching_invar_def matching_abstract_def]

abbreviation "potential_invar' \<equiv> \<lambda> \<pi> . M.invar \<pi> \<and> dom (lookup \<pi>) \<subseteq> Vs G"

abbreviation "path_search_precond \<equiv>
    hungarian_loop_spec.path_search_precond
        (\<lambda>\<pi>. abstract_real_map (lookup \<pi>)) potential_invar'
        (matching_invar G)
        matching_abstract \<ww> G"

abbreviation "search_path_here \<equiv>
   (\<lambda> M \<pi>. search_path left (lookup M) edge_costs
        (default_neighb vset_empty right_neighbs) \<pi> lookup
        update (\<lambda> f T init. fold_rbt (\<lambda> x y. f y x) init T)
                     (\<lambda> f T init. fold_rbt (\<lambda> x y. f y x) init T)
                     (\<lambda> f T init. fold_rbt (\<lambda> x y. f y x) init T)
                     filter_rbt)"

abbreviation "symmetric_buddies \<equiv> matching_augmentation_spec.symmetric_buddies"

abbreviation "good_search_result \<equiv>  
  hungarian_top_loop.good_search_result lookup potential_invar' edge_costs G"

interpretation hungarian_top_loop:
  hungarian_loop
  where path_search = search_path_here
    and edge_costs = \<ww>
    and init_potential = "init_potential_here"
    and potential_abstract = "(\<lambda> \<pi> v. abstract_real_map (lookup \<pi>) v)"
    and potential_invar = potential_invar'
    and empty_matching = Leaf
    and matching_invar = "matching_invar G"
    and augment = "matching_augment_impl"
    and matching_abstract = "matching_abstract"
    and card_L = "size left"
    and card_R = "size right"
    and G = G
    and L = L
    and R = R
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
    using init_potential_props(1,3) G(4) 
    by auto
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
    using empty_matching_props by auto
next
  case 11
  then show ?case 
    using empty_matching_props by simp
next
  case (12 M p)
  then show ?case 
    using augmentation_correct by auto
next
  case (13 M p)
  then show ?case 
    using augmentation_correct by fast
next
  fix M \<pi> B \<pi>'
  assume asm: "path_search_precond M \<pi>"
  note path_search_precondD = hungarian_loop_spec.path_search_precondD[OF asm]
  note symmetric_buddiesD = aug_a_matching.symmetric_buddiesD
  have \<M>_is: "pd_path_search_spec.\<M> (lookup M) =
             matching_abstract M" 
    by(force simp add: matching_abstract_def pd_path_search_spec.\<M>_def
        matching_augmentation_spec.\<M>_def'[OF aug_a_matching.matching_augmentation_spec_axioms]
        doubleton_eq_iff) 
  interpret pd_path_search: primal_dual_path_search
    (*the graph*)
    where G = G
      and left = left
      and right = right
      and buddy = "lookup M"
      and edge_costs = edge_costs
      and right_neighbs = "default_neighb vset_empty right_neighbs"
      (*the forest*)
      and evens = evens
      and odds = odds
      and abstract_forest = "abstract_forest"
      and get_path = "get_path"
      and extend_forest_even_unclassified = 
      "extend_forest_even_unclassified" 
      and empty_forest = 
      "empty_forest (\<lambda> f T init. fold_rbt (\<lambda> x y. f y x) init T)"
      and roots = roots
      and forest_invar = forest_invar
      (*the heap*)
      and heap_insert = queue_insert
      and heap_decrease_key = queue_decrease_key
      and heap_empty = queue_empty
      and heap_extract_min = queue_extract_min
      and heap_invar = queue_invar
      and heap_abstract = queue_abstract
      (*the potential*)
      and initial_pot = \<pi>
      and potential_lookup = lookup
      and potential_upd = update
      and potential_invar = M.invar
      (*missed change in potential*)
      and missed_lookup = lookup
      and missed_empty = Leaf
      and missed_upd = update
      and missed_invar = M.invar
      and missed_delete = delete
      (*best even neighbour map*)
      and ben_upd = update
      and ben_lookup = lookup
      and ben_empty = Leaf
      and ben_delete = delete
      and ben_invar = M.invar
      (*sets of vertices*)
      and vset_isin= isin
      and vset_to_set = Tree2.set_tree
      and vset_insert = vset_insert
      and vset_empty = vset_empty
      and vset_delete = vset_delete
      and vset_invar = vset_inv
      and vset_iterate_ben = "(\<lambda> f T init. fold_rbt (\<lambda> x y. f y x) init T)"
      and vset_iterate_pot = "(\<lambda> f T init. fold_rbt (\<lambda> x y. f y x) init T)"
      and vset_filter = filter_rbt
      and vset_is_empty = vset_is_empty
  proof(rule primal_dual_path_search.intro[OF
        pd_path_search_spec.primal_dual_path_search_spec_axioms], goal_cases)
    case 1
    thus ?case 
      using fe_spec.alternating_forest_ordinary_extension_spec_axioms
      by simp
  next
    case 2
    thus ?case
      using key_value_queue_spec_satisfied.key_value_queue_axioms by simp
  next
    case 3
    have help1:
      "v \<in> L \<Longrightarrow> vset_inv (default_neighb vset_empty right_neighbs v)" for v
      by(auto simp add: default_neighb_def split: option.split
          intro: vset G)
    have help2: "v \<in> L \<Longrightarrow>
         vset_to_set (default_neighb vset_empty right_neighbs v) = 
          {u | u. {v, u} \<in> G}" for v
      using G(6)
      by(fastforce simp add: default_neighb_def vset(2) split: option.split)
    have help3: "{u, v} \<in> G \<Longrightarrow>
           abstract_real_map (lookup \<pi>) u +
           abstract_real_map (lookup \<pi>) v
           \<le> edge_costs u v" for u v
      using feasible_min_perfect_dualD path_search_precondD(5) w_is_edge_costs
      by fastforce
    have help4: "{u, v} \<in> matching_abstract M \<Longrightarrow>
           abstract_real_map (lookup \<pi>) u +
           abstract_real_map (lookup \<pi>) v =
           edge_costs u v" for u v
      by(auto dest!: set_mp[OF path_search_precondD(4)]
          simp add: tight_subgraph_def doubleton_eq_iff
          w_is_edge_costs \<M>_is symmetric_weights)
    have help5: "dom (lookup \<pi>) \<subseteq> L \<union> R"
      using path_search_precondD(2)  G(1) bipartite_vs_subset by blast
    note help6 = symmetric_buddiesD[OF 
        matching_invarD(2)[OF path_search_precondD(1)]]
    show ?case
      apply(rule primal_dual_path_search_axioms.intro G(1,2,3) symmetric_weights help1 help2
          help3 | assumption)+
      by(unfold \<M>_is help6| intro help4 conjunct1[OF path_search_precondD(2)]
          potential best_even_neighbour vset missed help5 fold_rbt_as_needed' vset_is_empty
          path_search_precondD(3)[simplified aug_a_matching.\<M>_def'] filter_rbt_as_needed
        | assumption)+
  qed
  have search_path_is:
    "pd_path_search.search_path = search_path_here M \<pi>"
    by (simp add: search_path_def)
  note search_path_correct = pd_path_search.search_path_correct[unfolded search_path_is]

  show "search_path_here M \<pi> = Dual_Unbounded \<Longrightarrow>
       \<exists>\<pi>'. feasible_min_perfect_dual G \<ww> \<pi>' \<and> B < sum \<pi>' (L \<union> R)"
  proof(goal_cases)
    case 1
    obtain \<pi>' where pi':
      "\<And> u v. {u, v} \<in> G \<Longrightarrow> \<pi>' u + \<pi>' v \<le> \<w> u v"
      "B+1 \<le> sum \<pi>' (pd_path_search.L \<union> pd_path_search.R)"
      using search_path_correct(2)[OF 1, of "B+1"] by auto
    show ?case
      using pi'(2)
      by(auto intro!: exI[of _ \<pi>'] feasible_min_perfect_dualI pi'(1)
          simp add: w_is_edge_costs)
  qed

  show "search_path_here M \<pi> = Lefts_Matched \<Longrightarrow> L \<subseteq> Vs (matching_abstract M)"
    using search_path_correct(1) by(simp add: \<M>_is)

  show "search_path_here M \<pi> = Next_Iteration p \<pi>' \<Longrightarrow> good_search_result M \<pi>' p" for p
  proof(goal_cases)
    case 1
    note search_path_in_this_case =
      search_path_correct(3-)[OF 1, unfolded \<M>_is]
    show ?case
    proof(rule hungarian_top_loop.good_search_resultI, goal_cases)
      case 1
      then show ?case 
        using search_path_in_this_case(5,6) G(4) by blast
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
qed

lemmas hungarian_correctness = 
   hungarian_top_loop.hungarian_correctness[folded hungarian_def]
   hungarian_top_loop.hungarian_final_invar[folded hungarian_def]

lemma hungarian_symmetric:
  assumes "hungarian left right edge_costs right_neighbs lookup RBT_Map.update = Some M"
  shows   "lookup M u = Some v \<longleftrightarrow> lookup M v = Some u"
  using assms
  by(auto dest!: hungarian_correctness(3)
     simp add: aug_a_matching.invar_matchingD(2) aug_a_matching.symmetric_buddiesD)
 
end
end
end