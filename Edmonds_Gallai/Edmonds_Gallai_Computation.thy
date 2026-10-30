theory Edmonds_Gallai_Computation
  imports Edmonds_Gallai_Blossoms Blossom_Executable.Compute_Alt_Path
    Blossom_Executable.Find_Aug_Path Blossom_Executable.Find_Aug_Path_Subprocedures
    Basic_Matching.Alternating_Forest_Executable
begin 

section \<open>Computing the Decomposition with the Blossom Algorithm\<close>

subsection \<open>Obtaining the Decomposition from a Maximal Tree\<close>

text \<open>We perform alternating search as in the standard blossom algorithm.
  When there is no blossom and no augmenting path, the matching is of maximal cardinality.
  For this matching, we can obtain $\matcal{D}$ and $A$ from the final forest.
   $\mathcal{D}$ is the even and $A$ is the odd vertices.\<close>

datatype ('v, 'vset) alt_search_res =  Two_Paths "'v list" "'v list" | EDG 'vset

context compute_alt_path
begin

text \<open>We prove that the final even and odd vertices have the required properties.\<close>

lemma termination_conditions_edg:
  assumes "\<not> if1_cond F" "\<not> if2_cond F" "forest_invar M F" "Vs G - Vs M \<subseteq> aevens F" 
    "aevens F \<subseteq> Vs G" "\<lbrace> F \<rbrace> \<subseteq> G"
  shows "edmonds_gallai G M {{v} |v. v \<in> aevens F} (aodds F)" (is ?thesis1)
    "Neighbourhood G (\<Union> {{v} |v. v \<in> aevens F}) = aodds F" (is ?thesis2)
proof-               
  have goal1: "disjoint {{v} |v. v \<in> aevens F}"
    by(auto simp add: disjoint_def)
  have goal2: "\<Union> {{v} |v. v \<in> aevens F} \<subseteq> Vs G" 
    using assms(5) by blast
  have goal3: "X \<in> {{v} |v. v \<in> aevens F} \<Longrightarrow> X \<noteq> {}" for X by auto
  have goal5: "\<lbrakk>X \<in> {{v} |v. v \<in> aevens F}; Y \<in> {{v} |v. v \<in> aevens F}; X \<noteq> Y\<rbrakk>
                \<Longrightarrow> X \<leftarrow>|\<rightarrow>\<^bsub>G\<^esub> Y" for X Y
    using assms(2)
    by(auto simp add: connected_set_of_vertices_def if2_cond_def)
  have goal6: "aodds F = Neighbourhood G (\<Union> {{v} |v. v \<in> aevens F})"
    using assms
    unfolding  Union_of_singletons_in_set
    by(subst finial_forest_evens'_Neighbourhood[of F]) auto
  have goal7: "\<lbrakk>X \<in> {{v} |v. v \<in> aevens F}; x \<in> X\<rbrakk>
        \<Longrightarrow> \<exists>M. graph_matching ( G \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x}" for x X
    by(auto intro!: exI[of _ "{}"])
  have goal8: "\<lbrakk>v \<in> Vs G\<rbrakk> \<Longrightarrow> even_vert G M v \<longleftrightarrow> v \<in> \<Union> {{v} |v. v \<in> aevens F}" for v
  proof(rule, goal_cases)
    case 1
    then obtain p where "odd (length p)"
      "alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path p)"
      "hd p \<notin> Vs M" "last p = v" "distinct p" "(path G p \<or> length p = 1)"
      by(elim even_vertE) auto
    hence p_props: "odd (length p)"
      "alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path p)"
      "hd p \<notin> Vs M" "last p = v" "distinct p" "path G p" "1 \<le> length p"
      using 1(1) by(all \<open>cases p rule: list_cases3\<close>) auto
    hence p_in_G:"set p \<subseteq> Vs G"
      by (simp add: subset_path_Vs)
    have edges_p_in_G: "set (edges_of_path p) \<subseteq> G"
      by (simp add: p_props(6) path_edges_subset)
    have alt_list_p:"alt_list (\<lambda>x. x \<in> aevens F) (\<lambda>x. x \<in> aodds F) p"
      using termination_conditions_alt_paths_alternating_labels[OF
          assms(1,2,3,4) p_props(2,7,3) refl p_in_G edges_p_in_G]
      by simp
    hence "last p \<in> aevens F"
      using last_odd_P2 p_props(1) by auto
    thus ?case
      using p_props(4) by blast
  next
    case 2
    hence even_v: "v \<in> aevens F" by auto
    have "even_alt_path G M (last (get_path F v)) (rev (get_path F v)) v"
    proof-
      note get_path = get_path[OF assms(3) even_v refl]
      moreover have "path G (rev (get_path F v))"
        using "2"(1) assms(6) get_path
          path_subset[of "\<lbrace> F \<rbrace>" "get_path F v" G] path1[of v G]
        by(auto simp add:  walk_betw_def rev_path_is_path_iff)
      moreover have "alt_path M (rev (get_path F v))" 
        using get_path
        by(auto intro: rev_of_rev_alt_path_is_alt_path)
      moreover have "hd (rev (get_path F v)) = last (get_path F v)"
        by (simp add: hd_rev)
      moreover have "last (rev (get_path F v)) = v"
        using get_path last_rev[of "get_path F v"] by(auto simp add: walk_betw_def)
      moreover have "last (get_path F v) \<notin> Vs M" 
        using assms(3) get_path roots(3)[of M F] by auto
      ultimately show ?thesis
        by(auto intro!: even_alt_pathI)
    qed  
    thus ?case
      by(auto simp add: even_vert_even_alt_path)
  qed

  have goal9: "X \<in> {{v} |v. v \<in> aevens F} \<Longrightarrow> \<exists>x. x \<in> X \<and> Vs ( M \<lbrakk>X\<rbrakk>) = X - {x}" for X
    using matching(2) 
    by (auto elim!: in_graph_inter_VsE simp add: vs_member)+
  have goal10: "Delta M (\<Union> {{v} |v. v \<in> aevens F} \<union> aodds F) = {}"
  proof(rule ccontr, goal_cases)
    case 1
    then obtain e where "e \<in> Delta M (aevens F \<union> aodds F)"
      by (auto simp add: Union_of_singletons_in_set)
    thus ?case
    proof(elim in_DeltaE, goal_cases)
      case (1 u v)
      then show ?case 
      proof(elim UnE, goal_cases)
        case 1
        then show ?case 
          using assms(1,2,3,4,6) matching(2)
            finial_forest_evens'_Neighbourhood[of F] subsetD[of M G e]
            in_NeighbourhoodI[of u v G "aevens F"]
          by auto
      next
        case 2
        moreover hence "v \<in> aevens F" 
          using "1"(3) assms(3) evens_and_odds(3)[of M F] higher_forest_properties(2,3)[of M F u v]
          by auto
        ultimately show ?case 
          by auto
      qed
    qed
  qed

  have goal11: "D \<in> {{v} |v. v \<in> aevens F} \<Longrightarrow> card (Delta M D) \<le> 1" for D
  proof(goal_cases)
    case 1
    then obtain v where v: "v \<in> aevens F" "D = {v}"
      by auto
    show ?case
    proof(rule ccontr, goal_cases)
      case 1
      then obtain e1 e2 where "e1 \<in> Delta M {v}"  "e2 \<in> Delta M {v}" "e1 \<noteq> e2"
        using card_ge_1_obtain_two_distinc_elems[of "Delta M {v}"] v(2)
        by auto
      then show ?case 
        using matching(1)
        by(auto dest: matching_edges_not_eqD(1) elim!: in_DeltaE)
    qed
  qed

  have goal12: "Vs G - \<Union> {{v} |v. v \<in> aevens F} \<subseteq> Vs M"
    using assms(4)
    unfolding Union_of_singletons_in_set
    by auto

  have goal13: "M \<inter> (G \<lbrakk>aodds F\<rbrakk>) = {}"
  proof(rule equals0I, unfold Int_iff, elim conjE in_graph_inter_VsE, goal_cases)
    case (1 e)
    then obtain x y where xy: "e = {x, y}" "x \<noteq> y"
      by auto
    have "y \<in> aevens F" 
      using "1"(1,3)  evens_and_odds(3)[OF assms(3)]
        higher_forest_properties(2,3)[OF assms(3), of y x]  xy(1)
      by(auto simp add: insert_commute)
    hence "y \<notin> aodds F"
      using assms(3) evens_and_odds(4) by fastforce
    then show ?case 
      using 1 xy by auto
  qed

  show ?thesis1
    by(rule edmonds_gallaiI  goal1 goal2 goal3 goal5 goal6 goal7 goal8 goal9 goal10
        goal11 goal12 goal13 | 
        assumption)+
  show ?thesis2
    by (simp add: goal6)
qed

end

context Compute_Alt_Path
begin

function (domintros) compute_alt_path_or_edg ::
  "('v, 'forest) Compute_Alt_Path_state \<Rightarrow> ('v, 'fset) alt_search_res" where
  "compute_alt_path_or_edg state =
    (case unscanned state of
       (v, w) # rest \<Rightarrow>
         (if fset_isin (evens (search_forest state)) w then
            Two_Paths (get_path (search_forest state) v) (get_path (search_forest state) w)
          else if fset_isin (odds (search_forest state)) w then
            compute_alt_path_or_edg (state \<lparr>unscanned := rest\<rparr>)
          else case mate_lookup M w of
             Some x \<Rightarrow> compute_alt_path_or_edg
               (state \<lparr>queue := x # queue state, unscanned := rest,
                 search_forest := extend_forest_even_unclassified (search_forest state) v w x\<rparr>)
           | None \<Rightarrow> compute_alt_path_or_edg (state \<lparr>unscanned := rest\<rparr>))
     | [] \<Rightarrow>
         (case queue state of
            v # q \<Rightarrow> compute_alt_path_or_edg
              (state \<lparr>queue := q, unscanned := map (Pair v) (neighbour_list G v)\<rparr>)
          | [] \<Rightarrow> EDG (evens (search_forest state))))"
  by pat_completeness auto

lemma compute_alt_path_or_edg_same_dom:
  "compute_alt_path_or_edg_dom state \<longleftrightarrow> Compute_Alt_Path_dom state"
proof
  assume "compute_alt_path_or_edg_dom state"
  thus "Compute_Alt_Path_dom state"
    by (induction rule: compute_alt_path_or_edg.pinduct)
       (auto intro: Compute_Alt_Path.domintros)
next
  assume "Compute_Alt_Path_dom state"
  thus "compute_alt_path_or_edg_dom state"
    by (induction rule: Compute_Alt_Path.pinduct)
       (auto intro: compute_alt_path_or_edg.domintros)
qed

lemmas compute_alt_path_or_edg_psimps' =
  compute_alt_path_or_edg.psimps[simplified compute_alt_path_or_edg_same_dom]

lemma compute_alt_path_or_edg_result:
  "Compute_Alt_Path_dom state \<Longrightarrow>
    compute_alt_path_or_edg state =
      (case alternating_paths (Compute_Alt_Path state) of
         Some (p1, p2) \<Rightarrow> Two_Paths p1 p2
       | None \<Rightarrow> EDG (evens (search_forest (Compute_Alt_Path state))))"
proof (induction rule: Compute_Alt_Path.pinduct)
  case (1 state)
  show ?case
  proof (cases "unscanned state")
    case Nil
    thus ?thesis
      using 1(2-)
      by (cases "queue state")
         (simp_all add: compute_alt_path_or_edg_psimps'[OF 1(1)]
           Compute_Alt_Path.psimps[OF 1(1)] alternating_paths_def cong: option.case_cong)
  next
    case (Cons e rest)
    obtain v w where "e = (v, w)"
      by (cases e)
    with Cons show ?thesis
      using 1(2-)
      by (cases "fset_isin (evens (search_forest state)) w";
          cases "fset_isin (odds (search_forest state)) w"; cases "mate_lookup M w")
         (simp_all add: compute_alt_path_or_edg_psimps'[OF 1(1)]
           Compute_Alt_Path.psimps[OF 1(1)] alternating_paths_def cong: option.case_cong)
  qed
qed

lemma compute_alt_path_or_edg_same:
  "Compute_Alt_Path_dom state \<Longrightarrow>
    compute_alt_path_or_edg state = Two_Paths p1 p2 \<longleftrightarrow>
    alternating_paths (Compute_Alt_Path state) = Some (p1, p2)"
  by (auto simp: compute_alt_path_or_edg_result split: option.splits prod.splits)

lemma compute_alt_path_or_edg_same':
  "Compute_Alt_Path_dom state \<Longrightarrow>
    (\<exists>D. compute_alt_path_or_edg state = EDG D) \<longleftrightarrow>
    alternating_paths (Compute_Alt_Path state) = None"
  by (auto simp: compute_alt_path_or_edg_result split: option.splits prod.splits)

definition "decomposition_from_evens D =
  (D, foldl (\<lambda>A v. if fset_isin D v then
      foldl (\<lambda>A w. if fset_isin D w then A else fset_insert w A)
        A (neighbour_list G v)
    else A) fset_empty vs)"

definition "compute_edg =
  (case compute_alt_path_or_edg initial_state of
     EDG D \<Rightarrow> decomposition_from_evens D)"

context
  assumes Compute_Alt_Path_axiom: Compute_Alt_Path_axiom
begin

interpretation abs_search: compute_alt_path
  where G = "ugraph_abs G" and M = "matching_abs M"
    and vset_invar = fset_invar and vset_to_set = fset_to_set
    and evens = evens and odds = odds and roots = roots
    and get_path = get_path and abstract_forest = abstract_forest
    and forest_invar = forest_invar
    and extend_forest_even_unclassified = extend_forest_even_unclassified
    and empty_forest = empty_forest and forest_univ = K and vset_empty = fset_empty
proof (rule compute_alt_path.intro)
  show "match (ugraph_abs G) (matching_abs M)"
    by unfold_locales
       (use ugraph_abs_graph_invar[OF graph_input_G[OF Compute_Alt_Path_axiom]]
         matching_invar_props[OF matching_invar_M[OF Compute_Alt_Path_axiom]] in auto)
  show "alternating_forest_ordinary_extension_spec fset_invar fset_to_set evens odds get_path
    abstract_forest forest_invar roots extend_forest_even_unclassified empty_forest K fset_empty"
    by (rule Forest.alternating_forest_ordinary_extension_spec_axioms)
qed

lemma termination_conditions_edg:
  assumes "Compute_Alt_Path_ret_2_conds state" "invar_forest state" "invar_scanned state"
  shows "edmonds_gallai (ugraph_abs G) (matching_abs M)
    {{v} |v. v \<in> aevens state} (Neighbourhood (ugraph_abs G) (aevens state))"
proof -
  have closed: "\<And>v w. \<lbrakk>v \<in> aevens state; {v, w} \<in> ugraph_abs G\<rbrakk>
    \<Longrightarrow> w \<in> aodds state"
    using assms(1,3)
    by (auto simp: Compute_Alt_Path_ret_2_conds_def invar_scanned_def)
  have "\<not> abs_search.if1_cond (search_forest state)"
    using closed Forest.evens_and_odds_basis(4)[OF invar_forestD(1)[OF assms(2)]]
    by (auto simp: abs_search.if1_cond_def)
  moreover have "\<not> abs_search.if2_cond (search_forest state)"
    using closed Forest.evens_and_odds(4)[OF invar_forestD(1)[OF assms(2)]]
    by (auto simp: abs_search.if2_cond_def)
  moreover have "Vs (ugraph_abs G) - Vs (matching_abs M) \<subseteq> aevens state"
    using invar_forestD(3)[OF assms(2)] Forest.roots(2)[OF invar_forestD(1)[OF assms(2)]]
    by blast
  ultimately show ?thesis
    using abs_search.termination_conditions_edg[of "search_forest state"]
      invar_forestD(1,2)[OF assms(2)] aevens_subset_Vs[OF assms(2)]
    by (auto simp: Union_of_singletons_in_set)
qed

lemma compute_alt_path_or_edg_from_tree_2:
  assumes "invar_forest state" "invar_unscanned state" "invar_queue state" "invar_scanned state"
    "compute_alt_path_or_edg state = EDG D"
  shows "\<not> graph_augmenting_path (ugraph_abs G) (matching_abs M) p"
    "edmonds_gallai (ugraph_abs G) (matching_abs M)
      {{v} |v. v \<in> fset_to_set D} (Neighbourhood (ugraph_abs G) (fset_to_set D))"
    "fset_invar D" "fset_to_set D \<subseteq> Vs (ugraph_abs G)"
proof -
  have dom: "Compute_Alt_Path_dom state"
    by (rule Compute_Alt_Path_terminates[OF Compute_Alt_Path_axiom assms(1-4)])
  have final: "invar_forest (Compute_Alt_Path state)" "invar_scanned (Compute_Alt_Path state)"
    using invars_holds[OF Compute_Alt_Path_axiom dom assms(1-4)] by auto
  have result: "alternating_paths (Compute_Alt_Path state) = None"
    "D = evens (search_forest (Compute_Alt_Path state))"
    using assms(5) compute_alt_path_or_edg_result[OF dom]
    by (auto split: option.splits prod.splits)
  have ret: "Compute_Alt_Path_ret_2_conds (Compute_Alt_Path state)"
    using ret_holds[OF dom] result(1)
    by (auto simp: Compute_Alt_Path_ret_1_conds_def alternating_paths_def)
  show "\<not> graph_augmenting_path (ugraph_abs G) (matching_abs M) p"
    by (rule Compute_Alt_Path_correct_ret_2[OF Compute_Alt_Path_axiom ret final])
  show "edmonds_gallai (ugraph_abs G) (matching_abs M)
      {{v} |v. v \<in> fset_to_set D} (Neighbourhood (ugraph_abs G) (fset_to_set D))"
    using termination_conditions_edg[OF ret final] by (simp add: result(2))
  show "fset_invar D" "fset_to_set D \<subseteq> Vs (ugraph_abs G)"
    using forest_sets_invar(1)[OF final(1)] aevens_subset_Vs[OF final(1)]
    by (simp_all add: result(2))
qed

lemma decomposition_from_evens_props:
  assumes "fset_invar D" "fset_to_set D \<subseteq> Vs (ugraph_abs G)"
  shows "fst (decomposition_from_evens D) = D"
    "fset_invar (fst (decomposition_from_evens D))"
    "fset_invar (snd (decomposition_from_evens D))"
    "fset_to_set (snd (decomposition_from_evens D)) = Neighbourhood (ugraph_abs G) (fset_to_set D)"
proof -
  show "fst (decomposition_from_evens D) = D"
    "fset_invar (fst (decomposition_from_evens D))"
    using assms(1) by (simp_all add: decomposition_from_evens_def)
  let ?add = "\<lambda>A w. if fset_isin D w then A else fset_insert w A"
  have inner: "fset_invar (foldl ?add A xs) \<and>
    fset_to_set (foldl ?add A xs) = fset_to_set A \<union> (set xs - fset_to_set D)"
    if "fset_invar A" "set xs \<subseteq> K" for A xs
    using that
    by (induction xs arbitrary: A)
       (auto simp: Fset.fixed_univ_set_isin[OF assms(1)] Fset.fixed_univ_set_insert)
  have neighbours: "set (neighbour_list G v) \<subseteq> K" for v
    using graph_inputD(7)[OF graph_input_G[OF Compute_Alt_Path_axiom]]
      Vs_G_subset_vs[OF Compute_Alt_Path_axiom]
    by (auto simp: neighbour_list_ugraph_abs[OF graph_input_G[OF Compute_Alt_Path_axiom]]
        dest!: edges_are_Vs_2)
  let ?scan = "\<lambda>A v. if fset_isin D v then foldl ?add A (neighbour_list G v) else A"
  have "fset_invar (foldl ?scan A xs) \<and>
    fset_to_set (foldl ?scan A xs) =
      fset_to_set A \<union> ((\<Union>v \<in> set xs \<inter> fset_to_set D. set (neighbour_list G v)) - fset_to_set D)"
    if "fset_invar A" for A xs
    using that
    by (induction xs arbitrary: A)
       (auto simp: Fset.fixed_univ_set_isin[OF assms(1)]
         inner[OF _ neighbours, simplified Fset.fixed_univ_set_isin[OF assms(1)]]
         cong: if_cong split: if_splits)
  from this[OF Fset.fixed_univ_set_empty(1), of vs]
  have folded: "fset_invar (foldl ?scan fset_empty vs)"
    "fset_to_set (foldl ?scan fset_empty vs) =
      (\<Union>v \<in> set vs \<inter> fset_to_set D. set (neighbour_list G v)) - fset_to_set D"
    by (auto simp: Fset.fixed_univ_set_empty(2))
  have "(\<Union>v \<in> set vs \<inter> fset_to_set D. set (neighbour_list G v)) - fset_to_set D =
    Neighbourhood (ugraph_abs G) (fset_to_set D)"
    using assms(2) Vs_G_subset_vs[OF Compute_Alt_Path_axiom]
    by (auto intro!: bexI simp: Neighbourhood_def
        neighbour_list_ugraph_abs[OF graph_input_G[OF Compute_Alt_Path_axiom]])
  with folded show "fset_invar (snd (decomposition_from_evens D))"
    "fset_to_set (snd (decomposition_from_evens D)) = Neighbourhood (ugraph_abs G) (fset_to_set D)"
    by (simp_all add: decomposition_from_evens_def)
qed

lemma compute_edg_correct:
  assumes "alternating_paths (Compute_Alt_Path initial_state) = None"
  shows "fset_invar (fst compute_edg)" "fset_invar (snd compute_edg)"
    "edmonds_gallai (ugraph_abs G) (matching_abs M)
      ({{v} |v. v \<in> fset_to_set (fst compute_edg)}) (fset_to_set (snd compute_edg))"
proof -
  obtain D where result: "compute_alt_path_or_edg initial_state = EDG D"
    using compute_alt_path_or_edg_same'[OF initial_state_dom[OF Compute_Alt_Path_axiom]] assms
    by auto
  have props: "fset_invar D \<and> fset_to_set D \<subseteq> Vs (ugraph_abs G) \<and>
    edmonds_gallai (ugraph_abs G) (matching_abs M)
      {{v} |v. v \<in> fset_to_set D} (Neighbourhood (ugraph_abs G) (fset_to_set D))"
  proof (cases "free_vertices = []")
    case True
    have D: "D = initial_roots"
      using result
      unfolding compute_alt_path_or_edg_result[OF initial_state_dom[OF Compute_Alt_Path_axiom]]
        Compute_Alt_Path_empty[OF Compute_Alt_Path_axiom True]
      by (simp add: initial_state_def alternating_paths_def Forest.empty_forest(1))
    have covered: "Vs (ugraph_abs G) \<subseteq> Vs (matching_abs M)"
      using set_free_vertices[OF Compute_Alt_Path_axiom] True by auto
    have "\<not> even_vert (ugraph_abs G) (matching_abs M) v"
      if "v \<in> Vs (ugraph_abs G)" for v
    proof
      assume "even_vert (ugraph_abs G) (matching_abs M) v"
      then obtain p where p: "odd (length p)" "hd p \<notin> Vs (matching_abs M)"
        "last p = v" "path (ugraph_abs G) p \<or> length p = 1"
        by (auto simp: even_vert_def)
      have "hd p \<in> Vs (ugraph_abs G)"
        using p(1,3,4) that
        by (cases p) (auto dest: subset_path_Vs simp: hd_last_same)
      with covered p(2) show False by auto
    qed
    hence "edmonds_gallai (ugraph_abs G) (matching_abs M) {} {}"
      using covered
      by (auto simp: edmonds_gallai_def disjoint_def Neighbourhood_def Delta_def graph_inter_Vs_def
          graph_abs_no_empty[OF abs_search.graph_abs_axioms])
    moreover have "fset_to_set D = {}"
      using initial_roots_props(2)[OF Compute_Alt_Path_axiom] covered by (auto simp: D)
    ultimately show ?thesis
      using initial_roots_props(1)[OF Compute_Alt_Path_axiom]
      by (simp add: D Neighbourhood_def)
  next
    case False
    show ?thesis
      by (intro conjI compute_alt_path_or_edg_from_tree_2(2-4)[
          OF initial_state_props[OF Compute_Alt_Path_axiom False] result])
  qed
  show "fset_invar (fst compute_edg)" "fset_invar (snd compute_edg)"
    "edmonds_gallai (ugraph_abs G) (matching_abs M)
      ({{v} |v. v \<in> fset_to_set (fst compute_edg)}) (fset_to_set (snd compute_edg))"
    using props decomposition_from_evens_props[of D]
    by (auto simp: compute_edg_def result)
qed

end
end

subsection \<open>Contract Blossoms\<close>

text \<open>We repeatedly contract blossoms until we can use the previous procedure to 
 obtain a decomposition for the contracted graph.\<close>

locale find_aug_path_edg =
  Find_Aug_Path where lookup = lookup and mate_empty = mate_empty +
  Fset: fixed_univ_set K fset_invar fset_to_set fset_empty fset_insert fset_delete fset_isin
  for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option" and mate_empty :: 'mate
    and fset_invar :: "'fset \<Rightarrow> bool" and fset_to_set :: "'fset \<Rightarrow> 'v set"
    and fset_empty :: 'fset and fset_insert :: "'v \<Rightarrow> 'fset \<Rightarrow> 'fset"
    and fset_delete :: "'v \<Rightarrow> 'fset \<Rightarrow> 'fset"
    and fset_isin :: "'fset \<Rightarrow> 'v \<Rightarrow> bool" +
  fixes edg_search :: "'adjmap \<Rightarrow> 'v list \<Rightarrow> 'mate \<Rightarrow> 'fset \<times> 'fset"
  assumes edg_search_sound:
    "\<And>E vs' N. \<lbrakk>graph_input E vs'; matching_invar E N; blos_search E vs' N = None\<rbrakk>
      \<Longrightarrow> edmonds_gallai (ugraph_abs E) (matching_abs N)
        {{v} |v. v \<in> fset_to_set (fst (edg_search E vs' N))}
        (fset_to_set (snd (edg_search E vs' N)))"
  and edg_search_invar:
    "\<And>E vs' N. \<lbrakk>graph_input E vs'; matching_invar E N; blos_search E vs' N = None\<rbrakk>
      \<Longrightarrow> fset_invar (fst (edg_search E vs' N))"
    "\<And>E vs' N. \<lbrakk>graph_input E vs'; matching_invar E N; blos_search E vs' N = None\<rbrakk>
      \<Longrightarrow> fset_invar (snd (edg_search E vs' N))"
begin

definition "edg_singletons vs' D =
  List.map_filter (\<lambda>v. if fset_isin D v then Some (fset_insert v fset_empty) else None) vs'"

definition "edg_insert_list C D = foldl (\<lambda>D v. fset_insert v D) D C"

definition "edg_expand C u Ds =
  map (\<lambda>D. if fset_isin D u then edg_insert_list C (fset_delete u D) else D) Ds"

definition "edg_isolated E C S =
  list_all (\<lambda>v. list_all (fset_isin S) (neighbour_list E v)) C"

lemma edg_singletons_props:
  assumes "fset_invar D" "fset_to_set D \<subseteq> set vs'" "set vs' \<subseteq> K"
  shows "list_all fset_invar (edg_singletons vs' D)"
    "fset_to_set ` set (edg_singletons vs' D) = {{v} |v. v \<in> fset_to_set D}"
  using assms
  by (auto intro!: image_eqI simp: edg_singletons_def List.map_filter_map_filter[symmetric]
      list_all_iff image_image Fset.fixed_univ_set_isin
      Fset.fixed_univ_set_insert Fset.fixed_univ_set_empty)

lemma edg_insert_list_props:
  assumes "fset_invar D" "set C \<subseteq> K"
  shows "fset_invar (edg_insert_list C D) \<and>
    fset_to_set (edg_insert_list C D) = fset_to_set D \<union> set C"
  using assms unfolding edg_insert_list_def
  by (induction C arbitrary: D) (auto simp: Fset.fixed_univ_set_insert)

lemma edg_isolated_iff:
  "\<lbrakk>graph_input E vs'; fset_invar S; fset_to_set S = set C\<rbrakk> \<Longrightarrow>
    edg_isolated E C S \<longleftrightarrow> Delta (ugraph_abs E) (set C) = {}"
  by (auto simp: edg_isolated_def list_all_iff Fset.fixed_univ_set_isin
      neighbour_list_ugraph_abs Delta_def)

lemma edg_expand_invar:
  "\<lbrakk>list_all fset_invar Ds; set C \<subseteq> K\<rbrakk>
    \<Longrightarrow> list_all fset_invar (edg_expand C u Ds)"
  by (auto simp: edg_expand_def list_all_iff
      edg_insert_list_props Fset.fixed_univ_set_delete split: if_splits)

lemma edg_expand_abs:
  assumes "list_all fset_invar Ds" "set C \<subseteq> K"
    "disjoint (fset_to_set ` set Ds)" "D \<in> fset_to_set ` set Ds" "u \<in> D"
  shows "fset_to_set ` set (edg_expand C u Ds) =
    (fset_to_set ` set Ds) - {D} \<union> {D - {u} \<union> set C}"
proof -
  have only: "u \<in> fset_to_set S \<longleftrightarrow> fset_to_set S = D"
    if "S \<in> set Ds" for S
    using assms(3-5) that by (auto simp: disjoint_def)
  have update: "fset_to_set (if fset_isin S u then edg_insert_list C (fset_delete u S) else S) =
    (if fset_to_set S = D then D - {u} \<union> set C else fset_to_set S)"
    if "S \<in> set Ds" for S
    using assms(1,2) that only[OF that]
    by (auto simp: list_all_iff Fset.fixed_univ_set_isin
        edg_insert_list_props Fset.fixed_univ_set_delete)
  have "fset_to_set ` set (edg_expand C u Ds) =
    (\<lambda>S. if S = D then D - {u} \<union> set C else S) ` (fset_to_set ` set Ds)"
    unfolding edg_expand_def set_map image_image
    by (rule image_cong[OF refl]) (rule update)
  also have "... = (fset_to_set ` set Ds) - {D} \<union> {D - {u} \<union> set C}"
    using assms(4) by (auto simp: image_iff split: if_splits)
  finally show ?thesis .
qed

function (domintros) find_edg where
  "find_edg E vs' N =
    (case blos_search E vs' N of
       Some (Blossom stem C) \<Rightarrow>
         (let u = create_vert vs';
              (Ds, A) = find_edg (contract_graph E vs' C u)
                (contract_vertices vs' C u) (contract_matching N C u);
              S = edg_insert_list C fset_empty
          in if edg_isolated E C S
             then (S # Ds, A)
             else (edg_expand C u Ds, A))
     | _ \<Rightarrow>
         (let (D, A) = edg_search E vs' N in (edg_singletons vs' D, A)))"
  by pat_completeness auto

lemma find_edg_dom:
  assumes "graph_input E vs'" "matching_invar E N"
  shows "find_edg_dom (E, vs', N)"
  using assms
proof (induction "card (Vs (ugraph_abs E))" arbitrary: E vs' N rule: less_induct)
  case less
  have step: "find_edg_dom (contract_graph E vs' C (create_vert vs'),
    contract_vertices vs' C (create_vert vs'), contract_matching N C (create_vert vs'))"
    if "blos_search E vs' N = Some (Blossom stem C)" for stem C
  proof -
    have contract: "graph_input E vs'" "matching_invar E N"
      "blossom (ugraph_abs E) (matching_abs N) stem C"
      "create_vert vs' \<notin> set vs'" "create_vert vs' \<in> K"
      using less.prems blos_search(2)[OF less.prems that] create_vert create_vert_in_univ
      by (auto dest: graph_inputD(7))
    show ?thesis
      by (rule less.hyps[OF contract_card_Vs[OF contract]
            contract_graph_input[OF contract] contract_matching_invar[OF contract]])
  qed
  show ?case
    by (rule find_edg.domintros) (auto intro: step)
qed

lemma find_edg_correct:
  assumes "graph_input E vs'" "matching_invar E N"
    "max_card_matching (ugraph_abs E) (matching_abs N)"
  shows "list_all fset_invar (fst (find_edg E vs' N))"
    "fset_invar (snd (find_edg E vs' N))"
    "edmonds_gallai (ugraph_abs E) (matching_abs N)
      (fset_to_set ` set (fst (find_edg E vs' N))) (fset_to_set (snd (find_edg E vs' N)))"
proof -
  have "list_all fset_invar (fst (find_edg E vs' N)) \<and>
    fset_invar (snd (find_edg E vs' N)) \<and>
    edmonds_gallai (ugraph_abs E) (matching_abs N)
      (fset_to_set ` set (fst (find_edg E vs' N))) (fset_to_set (snd (find_edg E vs' N)))"
    using assms
  proof (induction "card (Vs (ugraph_abs E))" arbitrary: E vs' N rule: less_induct)
    case less
    note dom = find_edg_dom[OF less.prems(1,2)]
    show ?case
    proof (cases "blos_search E vs' N")
      case None
      have "fset_to_set (fst (edg_search E vs' N)) \<subseteq> set vs'"
        using edmonds_gallaiD(2)[OF edg_search_sound[OF less.prems(1,2) None]]
          Vs_ugraph_abs_subset_vs[OF less.prems(1)]
        by (auto simp: Union_of_singletons_in_set)
      from edg_singletons_props[OF edg_search_invar(1)[OF less.prems(1,2) None]
          this graph_inputD(7)[OF less.prems(1)]]
      show ?thesis
        using edg_search_sound[OF less.prems(1,2) None] edg_search_invar(2)[OF less.prems(1,2) None]
        by (cases "edg_search E vs' N") (simp add: find_edg.psimps[OF dom] None Let_def)
    next
      case (Some r)
      have no_path: "\<not> graph_augmenting_path (ugraph_abs E) (matching_abs N) p" for p
        using Berge[OF matching_invar_props(4)[OF less.prems(2,1)]
          matching_invar_props(2,3)[OF less.prems(2)]
          conjunct1[OF ugraph_abs_graph_invar[OF less.prems(1)]]
          conjunct2[OF ugraph_abs_graph_invar[OF less.prems(1)]]]
          max_card_matchingD[OF less.prems(3)]
        by (metis not_less)
      obtain stem C where result: "blos_search E vs' N = Some (Blossom stem C)"
        using Some blos_search(1)[OF less.prems(1,2)] no_path
        by (cases r) blast+
      let ?u = "create_vert vs'"
      have contract: "graph_input E vs'" "matching_invar E N"
        "blossom (ugraph_abs E) (matching_abs N) stem C" "?u \<notin> set vs'" "?u \<in> K"
        using less.prems(1,2) blos_search(2)[OF less.prems(1,2) result]
          create_vert create_vert_in_univ[OF graph_inputD(7)[OF less.prems(1)]]
        by auto
      interpret Q: quot "ugraph_abs E" "Vs (ugraph_abs E) - set C" ?u
        by (rule quot_here[OF contract])
      note abs = contract_graph_abs[OF contract] contract_matching_abs[OF contract]
      let ?E = "contract_graph E vs' C ?u"
      let ?vs = "contract_vertices vs' C ?u"
      let ?N = "contract_matching N C ?u"
      let ?Ds = "fst (find_edg ?E ?vs ?N)"
      let ?A = "snd (find_edg ?E ?vs ?N)"
      have matching: "graph_matching (ugraph_abs E) (matching_abs N)"
        using matching_invar_props(2,3)[OF less.prems(2)] by auto
      have max: "max_card_matching (ugraph_abs ?E) (matching_abs ?N)"
        using Q.max_card_matching_equiv_blossom_contraction[
          OF contract(3) matching refl contraction_facts(6)[OF contract]] less.prems(3)
        by (simp add: abs)
      have IH: "list_all fset_invar ?Ds" "fset_invar ?A"
        "edmonds_gallai (Q.quotG (ugraph_abs E)) (Q.quotG (matching_abs N))
          (fset_to_set ` set ?Ds) (fset_to_set ?A)"
        using less.hyps[OF contract_card_Vs[OF contract]
          contract_graph_input[OF contract] contract_matching_invar[OF contract] max]
        by (auto simp: abs)
      have C: "set C \<subseteq> K"
        using contraction_facts(2)[OF contract] Vs_ugraph_abs_subset_vs[OF less.prems(1)]
          graph_inputD(7)[OF less.prems(1)] by auto
      have cycle: "fset_invar (edg_insert_list C fset_empty)"
        "fset_to_set (edg_insert_list C fset_empty) = set C"
        using edg_insert_list_props[OF Fset.fixed_univ_set_empty(1) C]
        by (auto simp: Fset.fixed_univ_set_empty(2))
      have fresh: "?u \<notin> Vs (ugraph_abs E)"
        "create_vert (?u # vs') \<notin> Vs (ugraph_abs E)" "create_vert (?u # vs') \<noteq> ?u"
        using create_vert[of "?u # vs'"] Vs_ugraph_abs_subset_vs[OF less.prems(1)]
          contraction_facts(6)[OF contract] by auto
      show ?thesis
      proof (cases "edg_isolated E C (edg_insert_list C fset_empty)")
        case True
        have isolated: "Delta (ugraph_abs E) (set C) = {}"
          using True edg_isolated_iff[OF less.prems(1) cycle] by simp
        have "edmonds_gallai (ugraph_abs E) (matching_abs N)
          (Set.insert (set C) (fset_to_set ` set ?Ds)) (fset_to_set ?A)"
          by (rule Q.emonds_gallai_lonely_blossom[
                OF IH(3) isolated refl contract(3) less.prems(3) fresh])
        with IH(1,2) cycle show ?thesis
          by (cases "find_edg ?E ?vs ?N")
             (simp add: find_edg.psimps[OF dom] result Let_def True)
      next
        case False
        have connected: "Delta (ugraph_abs E) (set C) \<noteq> {}"
          using False edg_isolated_iff[OF less.prems(1) cycle] by simp
        obtain D where D: "D \<in> fset_to_set ` set ?Ds" "?u \<in> D"
          by (rule Q.emonds_gallai_connected_blossom_obtain_D[
                OF IH(3) connected refl contract(3) less.prems(3) fresh])
        have "edmonds_gallai (ugraph_abs E) (matching_abs N)
          ((fset_to_set ` set ?Ds) - {D} \<union> {D - {?u} \<union> set C}) (fset_to_set ?A)"
          by (rule Q.emonds_gallai_connected_blossom[
                OF IH(3) connected refl contract(3) less.prems(3) fresh D])
        with IH(2) edg_expand_invar[OF IH(1) C]
          edg_expand_abs[OF IH(1) C edmonds_gallaiD(1)[OF IH(3)] D]
        show ?thesis
          by (cases "find_edg ?E ?vs ?N")
             (simp add: find_edg.psimps[OF dom] result Let_def False)
      qed
    qed
  qed
  thus "list_all fset_invar (fst (find_edg E vs' N))"
    "fset_invar (snd (find_edg E vs' N))"
    "edmonds_gallai (ugraph_abs E) (matching_abs N)
      (fset_to_set ` set (fst (find_edg E vs' N))) (fset_to_set (snd (find_edg E vs' N)))"
    by auto
qed

end

subsection \<open>Putting Things Together\<close>

text \<open>The graph, matching and alternating forest are instantiated from set and map ADTs.
  The decomposition uses the same implementations throughout contraction and expansion.\<close>

locale Edmonds_Gallai_ADTs =
  adjmap: Map where empty = empty and delete = delete and lookup = lookup
    and update = update and invar = adjmap_inv +
  vset: Set_Choose where empty = vset_empty and insert = insert and delete = vset_delete
    and isin = isin and t_set = t_set and invar = vset_inv and sel = sel +
  parent_map: fixed_univ_map K parent_invar parent_update parent_get +
  origin_map: fixed_univ_map K origin_invar origin_update origin_get +
  buddy_map: fixed_univ_map K buddy_invar buddy_update buddy_get +
  Fset: fixed_univ_set K fset_invar fset_to_set fset_empty fset_insert fset_delete fset_isin
  for K :: "'v set" and lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option"
    and empty :: 'adjmap and delete :: "'v \<Rightarrow> 'adjmap \<Rightarrow> 'adjmap"
    and update :: "'v \<Rightarrow> 'vset \<Rightarrow> 'adjmap \<Rightarrow> 'adjmap"
    and adjmap_inv :: "'adjmap \<Rightarrow> bool"
    and vset_empty :: 'vset and insert :: "'v \<Rightarrow> 'vset \<Rightarrow> 'vset"
    and vset_delete :: "'v \<Rightarrow> 'vset \<Rightarrow> 'vset"
    and isin :: "'vset \<Rightarrow> 'v \<Rightarrow> bool" and t_set :: "'vset \<Rightarrow> 'v set"
    and vset_inv :: "'vset \<Rightarrow> bool" and sel :: "'vset \<Rightarrow> 'v"
    and parent_invar :: "'parent \<Rightarrow> bool"
    and parent_update :: "'parent \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'parent"
    and parent_get :: "'parent \<Rightarrow> 'v \<Rightarrow> 'v"
    and origin_invar :: "'origin \<Rightarrow> bool"
    and origin_update :: "'origin \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'origin"
    and origin_get :: "'origin \<Rightarrow> 'v \<Rightarrow> 'v"
    and buddy_invar :: "'mate \<Rightarrow> bool"
    and buddy_update :: "'mate \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'mate"
    and buddy_get :: "'mate \<Rightarrow> 'v \<Rightarrow> 'v"
    and fset_invar :: "'fset \<Rightarrow> bool" and fset_to_set :: "'fset \<Rightarrow> 'v set"
    and fset_empty :: 'fset and fset_insert :: "'v \<Rightarrow> 'fset \<Rightarrow> 'fset"
    and fset_delete :: "'v \<Rightarrow> 'fset \<Rightarrow> 'fset"
    and fset_isin :: "'fset \<Rightarrow> 'v \<Rightarrow> bool" +
  fixes parent_empty :: 'parent and origin_empty :: 'origin and buddy_empty :: 'mate
    and nil :: 'v
    and vset_to_list :: "'vset \<Rightarrow> 'v list" and fset_to_list :: "'fset \<Rightarrow> 'v list"
    and create_vert :: "'v list \<Rightarrow> 'v"
  assumes nil: "nil \<notin> K"
    and parent_empty: "parent_invar parent_empty" "parent_get parent_empty = (\<lambda>_. nil)"
    and origin_empty: "origin_invar origin_empty" "origin_get origin_empty = (\<lambda>_. nil)"
    and buddy_empty: "buddy_invar buddy_empty" "buddy_get buddy_empty = (\<lambda>_. nil)"
    and vset_to_list: "\<And>S. vset_inv S \<Longrightarrow> set (vset_to_list S) = t_set S"
    and fset_to_list: "\<And>S. fset_invar S \<Longrightarrow> set (fset_to_list S) = fset_to_set S"
      "\<And>S. fset_invar S \<Longrightarrow> distinct (fset_to_list S)"
    and create_vert: "\<And>vs. create_vert vs \<notin> set vs"
    and create_vert_in_univ: "\<And>vs. set vs \<subseteq> K \<Longrightarrow> create_vert vs \<in> K"
begin

sublocale Graph: Pair_Graph_Specs
  where empty = empty and delete = delete and lookup = lookup and update = update
    and adjmap_inv = adjmap_inv and insert = insert and isin = isin and t_set = t_set
    and sel = sel and vset_empty = vset_empty and vset_delete = vset_delete and vset_inv = vset_inv
  by (intro Pair_Graph_Specs.intro adjmap.Map_axioms
      Pair_Graph_Specs_Read_Only.intro vset.Set_Choose_axioms)

sublocale Matching: matching_augmentation
  where K = K and buddy_invar = buddy_invar and buddy_upd = buddy_update
    and buddy_get = buddy_get and buddy_empty = buddy_empty and nil = nil
  by (auto intro!: matching_augmentation.intro Matching_Augmentation_Specs.intro
      matching_augmentation_axioms.intro buddy_map.fixed_univ_map_axioms simp: nil buddy_empty)

sublocale Forest: forest_manipulation
  where K = K and parent_invar = parent_invar and parent_upd = parent_update and parent_get = parent_get
    and origin_invar = origin_invar and origin_upd = origin_update and origin_get = origin_get
    and vset_invar = fset_invar and vset_to_set = fset_to_set and vset_empty = fset_empty
    and vset_insert = fset_insert and vset_delete = fset_delete and vset_isin = fset_isin
    and vset_iterate = "\<lambda>f init S. foldl f init (fset_to_list S)"
    and parent_empty = parent_empty and origin_empty = origin_empty and nil = nil
  apply (auto intro!: forest_manipulation.intro forest_manipulation_spec.intro
      forest_manipulation_axioms.intro parent_map.fixed_univ_map_axioms
      origin_map.fixed_univ_map_axioms Fset.fixed_univ_set_axioms
      simp: nil parent_empty origin_empty)
  subgoal for V f init
    by (intro exI[of _ "fset_to_list V"]) (auto simp: fset_to_list)
  done

sublocale GM: Graph_Matching_Specs
  where empty = empty and delete = delete and lookup = lookup and update = update
    and adjmap_inv = adjmap_inv and insert = insert and isin = isin and t_set = t_set
    and sel = sel and vset_empty = vset_empty and vset_delete = vset_delete and vset_inv = vset_inv
    and K = K and mate_empty = buddy_empty
    and matching_invar_abs = Matching.invar_matching and matching_abs = "Matching.\<M>"
    and mate_lookup = Matching.buddy_lookup and mate_partner = Matching.get_partner
    and mate_augment = Matching.augment_impl and mate_contract = Matching.contract_path
    and mate_expand = Matching.expand_path_at_matched and mate_add_alternatingly = Matching.add_alternatingly
    and vset_to_list = vset_to_list
  by (intro Graph_Matching_Specs.intro Graph.Pair_Graph_Specs_axioms
      Matching.blossom_matching_spec_satisfied Graph_Matching_Specs_axioms.intro vset_to_list)

sublocale Search: Compute_Alt_Path
  where empty = empty and delete = delete and lookup = lookup and update = update
    and adjmap_inv = adjmap_inv and insert = insert and isin = isin and t_set = t_set
    and sel = sel and vset_empty = vset_empty and vset_delete = vset_delete and vset_inv = vset_inv
    and K = K and mate_empty = buddy_empty
    and matching_invar_abs = Matching.invar_matching and matching_abs = "Matching.\<M>"
    and mate_lookup = Matching.buddy_lookup and mate_partner = Matching.get_partner
    and mate_augment = Matching.augment_impl and mate_contract = Matching.contract_path
    and mate_expand = Matching.expand_path_at_matched and mate_add_alternatingly = Matching.add_alternatingly
    and vset_to_list = vset_to_list
    and fset_invar = fset_invar and fset_to_set = fset_to_set
    and fset_empty = fset_empty and fset_insert = fset_insert
    and fset_delete = fset_delete and fset_isin = fset_isin
    and evens = evens and odds = odds and roots = roots
    and get_path = Forest.get_path and abstract_forest = Forest.abstract_forest
    and forest_invar = Forest.forest_invar
    and extend_forest_even_unclassified = Forest.extend_forest_even_unclassified
    and empty_forest = Forest.empty_forest
    and G = G and vs = vs and M = N
  for G vs N
  by (intro Compute_Alt_Path.intro GM.Graph_Matching_Specs_axioms
      Fset.fixed_univ_set_axioms Forest.satisified)

definition "compute_paths G vs N = Search.Compute_Alt_Path_run_impl G vs N"
definition "compute_edg G vs N = Search.compute_edg G vs N"

lemma compute_paths_correct:
  "\<lbrakk>GM.graph_input E vs'; GM.matching_invar E N\<rbrakk> \<Longrightarrow>
    compute_alt_path_spec (GM.ugraph_abs E) (Matching.\<M> N) (compute_paths E vs' N)"
  "\<lbrakk>GM.graph_input E vs'; GM.matching_invar E N;
    \<exists>p. graph_augmenting_path (GM.ugraph_abs E) (Matching.\<M> N) p\<rbrakk>
    \<Longrightarrow> compute_paths E vs' N \<noteq> None"
  using Search.Compute_Alt_Path_run_impl_correct[unfolded Search.Compute_Alt_Path_axiom_def]
  by (auto simp: compute_paths_def)

lemma compute_edg_props:
  assumes "GM.graph_input E vs'" "GM.matching_invar E N" "compute_paths E vs' N = None"
  shows "fset_invar (fst (compute_edg E vs' N))" "fset_invar (snd (compute_edg E vs' N))"
    "edmonds_gallai (GM.ugraph_abs E) (Matching.\<M> N)
      {{v} |v. v \<in> fset_to_set (fst (compute_edg E vs' N))}
      (fset_to_set (snd (compute_edg E vs' N)))"
proof -
  have axiom: "Search.Compute_Alt_Path_axiom E vs' N"
    unfolding Search.Compute_Alt_Path_axiom_def
    by (rule conjI[OF assms(1,2)])
  show "fset_invar (fst (compute_edg E vs' N))" "fset_invar (snd (compute_edg E vs' N))"
    "edmonds_gallai (GM.ugraph_abs E) (Matching.\<M> N)
      {{v} |v. v \<in> fset_to_set (fst (compute_edg E vs' N))}
      (fset_to_set (snd (compute_edg E vs' N)))"
    using Search.compute_edg_correct[OF axiom] assms(3)
    by (auto simp: compute_edg_def compute_paths_def Search.Compute_Alt_Path_run_impl_def
        Search.Compute_Alt_Path_impl_to_Compute_Alt_Path[OF axiom])
qed

sublocale Subprocedures: Find_Aug_Path_subprocedures
  where empty = empty and delete = delete and lookup = lookup and update = update
    and adjmap_inv = adjmap_inv and insert = insert and isin = isin and t_set = t_set
    and sel = sel and vset_empty = vset_empty and vset_delete = vset_delete and vset_inv = vset_inv
    and K = K and mate_empty = buddy_empty
    and matching_invar_abs = Matching.invar_matching and matching_abs = "Matching.\<M>"
    and mate_lookup = Matching.buddy_lookup and mate_partner = Matching.get_partner
    and mate_augment = Matching.augment_impl and mate_contract = Matching.contract_path
    and mate_expand = Matching.expand_path_at_matched and mate_add_alternatingly = Matching.add_alternatingly
    and vset_to_list = vset_to_list
    and compute_alt_path = compute_paths
  by (intro Find_Aug_Path_subprocedures.intro GM.Graph_Matching_Specs_axioms
      Find_Aug_Path_subprocedures_axioms.intro compute_paths_correct)

lemma compute_blossom_None:
  "Subprocedures.compute_match_blossom E vs' N = None \<longleftrightarrow> compute_paths E vs' N = None"
  by (auto simp: Subprocedures.compute_match_blossom_def split: option.splits prod.splits if_splits)

sublocale Decomposition: find_aug_path_edg
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
    and edg_search = compute_edg
  for G vs N
  apply (intro find_aug_path_edg.intro Find_Aug_Path.intro GM.Graph_Matching_Specs_axioms
      Find_Aug_Path_axioms.intro Fset.fixed_univ_set_axioms find_aug_path_edg_axioms.intro)
  apply (rule Subprocedures.compute_match_blossom(1); assumption)
  apply (rule Subprocedures.compute_match_blossom(2); assumption)
  apply (rule Subprocedures.compute_match_blossom(3); assumption)
  apply (rule create_vert)
  apply (erule create_vert_in_univ)
  by (simp only: compute_blossom_None; rule compute_edg_props; assumption)+

definition "find_decomposition E vs' N = Decomposition.find_edg E vs' N"

lemma find_decomposition_correct:
  assumes "GM.graph_input E vs'" "GM.matching_invar E N"
    "max_card_matching (GM.ugraph_abs E) (Matching.\<M> N)"
  shows "list_all fset_invar (fst (find_decomposition E vs' N))"
    "fset_invar (snd (find_decomposition E vs' N))"
    "edmonds_gallai (GM.ugraph_abs E) (Matching.\<M> N)
      (fset_to_set ` set (fst (find_decomposition E vs' N)))
      (fset_to_set (snd (find_decomposition E vs' N)))"
  using Decomposition.find_edg_correct[OF assms]
  by (simp_all add: find_decomposition_def)




end

subsection \<open>Ordinary sets and functions\<close>

definition "edg_list_of_set S = (SOME xs. set xs = S \<and> distinct xs)"

lemma edg_list_of_set:
  "finite S \<Longrightarrow> set (edg_list_of_set S) = S \<and> distinct (edg_list_of_set S)"
  unfolding edg_list_of_set_def
  by (rule someI_ex) (rule finite_distinct_list)

locale compute_alt_path_and_edg_use =
  graph_abs E for E :: "'v set set" +
  fixes sel :: "'v set \<Rightarrow> 'v" and create_vert :: "'v set \<Rightarrow> 'v"
    and sel_from_sets :: "('v set \<Rightarrow> bool) \<Rightarrow> 'v set set \<Rightarrow> 'v set"
  assumes choose: "\<And>S. S \<noteq> {} \<Longrightarrow> sel S \<in> S"
    and create_vert: "\<And>S. finite S \<Longrightarrow> create_vert S \<notin> S"
    and sel_from_sets:
      "\<And>D P. \<lbrakk>finite D; \<exists>C \<in> D. P C\<rbrakk> \<Longrightarrow> sel_from_sets P D \<in> D"
      "\<And>D P. \<lbrakk>finite D; \<exists>C \<in> D. P C\<rbrakk> \<Longrightarrow> P (sel_from_sets P D)"
begin

definition "nil = create_vert (Vs E)"

lemma nil_not_in_Vs: "nil \<notin> Vs E"
  using create_vert[OF finite_Vs] by (simp add: nil_def)

lemma create_vert_list:
  "create_vert (Set.insert nil (set vs)) \<notin> set vs"
  "create_vert (Set.insert nil (set vs)) \<noteq> nil"
  using create_vert[of "Set.insert nil (set vs)"] by auto

interpretation Impl: Edmonds_Gallai_ADTs
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

definition "graph_of_set H v =
  (if v \<in> Vs H then Some {w. {v, w} \<in> H} else None)"

definition "matching_of_set M v =
  (if \<exists>w. {v, w} \<in> M then THE w. {v, w} \<in> M else nil)"

lemma graph_of_set_abs:
  assumes "graph_invar H"
  shows "Impl.GM.ugraph_abs (graph_of_set H) = H"
proof (rule equalityI)
  show "Impl.GM.ugraph_abs (graph_of_set H) \<subseteq> H"
    by (auto simp: Impl.GM.ugraph_abs_def Impl.Graph.digraph_abs_def
        Impl.Graph.neighbourhood_def graph_of_set_def)
  show "H \<subseteq> Impl.GM.ugraph_abs (graph_of_set H)"
  proof
    fix e
    assume edge: "e \<in> H"
    obtain u v where "e = {u, v}"
      by (rule Undirected_Set_Graphs.dblton_graphE[OF conjunct1[OF assms] edge])
    with edge show "e \<in> Impl.GM.ugraph_abs (graph_of_set H)"
      by (auto intro!: exI simp: Impl.GM.ugraph_abs_def Impl.Graph.digraph_abs_def
          Impl.Graph.neighbourhood_def graph_of_set_def Vs_def insert_commute)
  qed
qed

lemma graph_of_set_edges:
  "(u, v) \<in> Impl.Graph.digraph_abs (graph_of_set H) \<longleftrightarrow> {u, v} \<in> H"
  by (auto simp: Impl.Graph.digraph_abs_def Impl.Graph.neighbourhood_def graph_of_set_def
      dest!: edges_are_Vs)

lemma graph_of_set_input:
  assumes "graph_invar H" "nil \<notin> Vs H"
  shows "Impl.GM.graph_input (graph_of_set H) (edg_list_of_set (Vs H))"
proof -
  have finite_neighbours: "finite {w. {v, w} \<in> H}" for v
    by (rule finite_subset[OF _ conjunct2[OF assms(1)]])
       (auto dest!: edges_are_Vs_2)
  show ?thesis
  proof (rule Impl.GM.graph_inputI)
    show "Impl.Graph.graph_inv (graph_of_set H)" "Impl.Graph.finite_graph (graph_of_set H)"
       "Impl.Graph.finite_vsets (graph_of_set H)"
       "\<And>u v. (u, v) \<in> Impl.Graph.digraph_abs (graph_of_set H) \<Longrightarrow>
      (v, u) \<in> Impl.Graph.digraph_abs (graph_of_set H)"
       "\<And>u. (u, u) \<notin> Impl.Graph.digraph_abs (graph_of_set H)"
      using finite_neighbours assms(1)
      by (auto simp add: Impl.Graph.graph_inv_def graph_of_set_def Impl.Graph.finite_graph_def
                    Impl.Graph.finite_vsets_def graph_of_set_edges insert_commute
              split: if_splits)
    show "dVs (Impl.Graph.digraph_abs (graph_of_set H)) \<subseteq> set (edg_list_of_set (Vs H))"
      "set (edg_list_of_set (Vs H)) \<subseteq> - {nil}"
      using edg_list_of_set[OF conjunct2[OF assms(1)]] assms(2)
      by (auto simp: dVs_def graph_of_set_edges Vs_def)
  qed
qed

lemma matching_of_set_partner:
  "\<lbrakk>matching M; {u, v} \<in> M\<rbrakk> \<Longrightarrow> matching_of_set M u = v"
  unfolding matching_of_set_def
  by (auto intro!: the_equality dest: doubleton_in_matching(1))

lemma matching_of_set_lookup:
  assumes "graph_matching E M"
  shows "Impl.Matching.buddy_lookup (matching_of_set M) u = Some v \<longleftrightarrow> {u, v} \<in> M"
proof(cases "\<exists>w. {u, w} \<in> M")
  case True
  then obtain w where "{u, w} \<in> M"
    by auto
  moreover hence "w \<noteq> nil"
    using assms nil_not_in_Vs by auto
  ultimately show ?thesis
    using assms
    by (auto simp: Impl.Matching.buddy_lookup_def matching_of_set_partner
        dest: doubleton_in_matching(1))
next
  case False
  then show ?thesis
    by (auto simp: Impl.Matching.buddy_lookup_def matching_of_set_def)
qed

lemma matching_of_set_abs:
  "graph_matching E M \<Longrightarrow> Impl.Matching.\<M> (matching_of_set M) = M"
  using graph
  by (fastforce simp: Impl.Matching.\<M>_def upairs_of_map_def matching_of_set_lookup
      elim!: Undirected_Set_Graphs.dblton_graphE dest: subsetD)

lemma matching_of_set_invar:
  assumes "graph_matching E M"
  shows "Impl.GM.matching_invar (graph_of_set E) (matching_of_set M)"
  using assms graph nil_not_in_Vs
  by (auto simp: Impl.GM.matching_invar_def Impl.Matching.invar_matching_def
      Impl.Matching.symmetric_buddies_def Impl.Matching.no_self_loop_buddy_def
      graph_of_set_abs matching_of_set_abs matching_of_set_lookup insert_commute
      intro: finite_subset finite_Vs_then_finite)

text \<open>The set interface converts the input to the existing ADT implementation and
  forgets the list representation of the returned odd components.\<close>

definition "find_decomposition H M =
  (let result = Impl.find_decomposition (graph_of_set H) (edg_list_of_set (Vs H)) (matching_of_set M)
   in (set (fst result), snd result))"

lemma find_decomposition_correct:
  assumes "max_card_matching E M"
  shows "edmonds_gallai E M (fst (find_decomposition E M)) (snd (find_decomposition E M))"
proof-
  have "graph_matching E M"
    using assms by (auto dest: max_card_matchingD)
  hence "Impl.GM.matching_invar (graph_of_set E) (matching_of_set M)"
    by (auto intro: matching_of_set_invar)
  moreover have "Impl.GM.graph_input (graph_of_set E) (edg_list_of_set (Vs E))"
    using graph nil_not_in_Vs by (auto intro: graph_of_set_input)
  ultimately show ?thesis
    using Impl.find_decomposition_correct(3)[of "graph_of_set E" "edg_list_of_set (Vs E)" "matching_of_set M"]
      assms \<open>graph_matching E M\<close> graph
    by (auto simp: find_decomposition_def Let_def graph_of_set_abs matching_of_set_abs)
qed

end

end