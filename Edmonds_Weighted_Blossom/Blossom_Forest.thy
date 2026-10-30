theory Blossom_Forest
  imports Laminar_Family.Laminar_Family_Executable
          Blossom_Forest_Spec
begin

context laminar_tree
begin

fun blossom_edges where
  "blossom_edges (maxids, L) = 
   \<Union> {set (edges_of_path (ids@[hd ids])) | ids i. lookup L i = Some (subverts ids)}"

lemma blossom_edges_def:
  "blossom_edges L = 
   \<Union> {set (edges_of_path (ids@[hd ids])) | ids i. lookup (snd L) i = Some (subverts ids)}"
  by(cases L) auto

definition "branching_odd M =
   (\<forall> i vs. lookup M i = Some (subverts vs) \<longrightarrow> odd (length vs))"

lemma branching_oddE:
  "\<lbrakk>branching_odd M; (\<And>i vs. lookup M i = Some (subverts vs) \<Longrightarrow> odd (length vs)) \<Longrightarrow> P\<rbrakk>
    \<Longrightarrow> P"
and branching_oddD:
  "\<lbrakk>branching_odd M; lookup M i = Some (subverts vs)\<rbrakk> \<Longrightarrow> odd (length vs)"
and branching_oddI:
  "\<lbrakk>\<And>i vs. lookup M i = Some (subverts vs) \<Longrightarrow> odd (length vs)\<rbrakk> \<Longrightarrow> branching_odd M"
  by (auto simp: branching_odd_def)

fun blossom_forest_invar where
 "blossom_forest_invar (maxids, M) =
     (laminar_forest_invar (maxids, M) \<and> branching_odd M)"

lemma blossom_forest_invarI:
 "\<lbrakk>laminar_forest_invar F; branching_odd (snd F)\<rbrakk> \<Longrightarrow> blossom_forest_invar F"
and blossom_forest_invarE:
 "\<lbrakk>blossom_forest_invar F; \<lbrakk>laminar_forest_invar F; branching_odd (snd F)\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
and blossom_forest_invarD:
 "blossom_forest_invar F \<Longrightarrow> laminar_forest_invar F"
 "blossom_forest_invar F \<Longrightarrow> branching_odd (snd F)"
  by(all \<open>cases F\<close>) auto

lemma branching_odd_collect_verts_odd:
  assumes 
    "wf (laminar_forest_cons L)" "i \<in> dom (lookup L)" "disjoint_subids L" 
    "elem_unique_id L" "branching_properly L" "domain_recursive L"
    "distinct_children L" "branching_odd L"
 shows  "odd (card (collect_verts L i))"
  using assms(2)
proof(induction rule: collect_verts_induct[OF assms(1)])
  case (1 i)
  note IH = this
  show ?case 
  proof(cases "lookup L i")
    case None
    then show ?thesis
      using "1.prems" by auto
  next
    case (Some a)
    then show ?thesis 
    proof(cases a, goal_cases)
      case (1 x)
      then show ?case 
        by(auto simp add: collect_verts_simps[OF assms(1)])
    next
      case (2 vs)
      note two = this
      moreover have "odd (card (\<Union> (collect_verts L ` set vs)))"
      proof(rule odd_disjoint_Union, goal_cases)
        case 1
        then show ?case 
        proof(subst card_image, goal_cases)
          case 1
          then show ?case 
          proof(rule inj_onI, goal_cases)
            case (1 x y)
            then show ?case 
              using assms(1-6) two(2) Some branching_properly_children_nempty[of L]
                    disjoint_elems_if_disjoint_subids_and_elem_unique_id[of L] 
                    collect_verts_nempty[of L y]
              by (auto dest: disjoint_elem_vertsD domain_recursiveD)
          qed
          next
            case 2
            thus ?case
              using Some assms(7,8) distinct_card[of vs] two(2)
              by(auto dest!: distinct_childrenD branching_oddD)
          qed
      next
        case (2 X)
        then obtain v where "v \<in> set vs" "X = collect_verts L v"
          by auto
        moreover hence "odd (card (collect_verts L v))"
          using Some assms(6) domain_recursiveD two(2) 
          by (intro IH(1)) auto
        ultimately show ?case 
          by simp
      next
        case (3 X Y)
        then obtain v v' where "v \<in> set vs" "X = collect_verts L v"
          "v' \<in> set vs" "Y = collect_verts L v'"
          by auto
        moreover hence "collect_verts L v \<inter> collect_verts L v' = {}"
          using two 3(3)
          by (intro disjoint_elem_vertsD)
             (auto simp add: assms(1,3,4) disjoint_elems_if_disjoint_subids_and_elem_unique_id)
        ultimately show ?case
          by simp
      qed
      ultimately show ?case 
        by(simp add: collect_verts_simps[OF assms(1)])
    qed
  qed
qed

lemma blossom_edges_props:
  assumes "blossom_forest_invar (maxids, L)"
  shows   "dblton_graph (blossom_edges (maxids, L))" (is ?th1)
  and      "Vs (blossom_edges (maxids, L)) \<subseteq> dom (lookup L)" (is ?th2)
  and     "{i, j} \<in> blossom_edges (maxids, L) \<Longrightarrow>
           \<exists>m\<in>max_ids L. collect_verts L i \<subseteq> collect_verts L m
            \<and> collect_verts L j \<subseteq> collect_verts L m" (is "?asm1 \<Longrightarrow> ?th3")
proof-

  show ?th1
    using assms
    by (auto intro!: dblton_graph_Union dblton_graph_edges_of_distinct_path_clsd_hd
              elim!: laminar_forest_invarE
               dest: distinct_childrenD branching_properlyD)
  show ?th2
  proof(rule, elim vs_member_elim, goal_cases)
    case (1 x e)
    then obtain i ids where i_ids_props:"e \<in> set (edges_of_path (ids@[hd ids]))" 
           "lookup L i = Some (subverts ids)" 
      by auto
    hence "x \<in> set ids" 
      using 1 v_in_edge_in_path_gen
      by(cases ids) fastforce+
    then show ?case 
      using  assms i_ids_props(2)
      by(auto dest: domain_recursiveD)   
  qed
  show ?th3 if asm: ?asm1
  proof-
   obtain i' ids where i_ids_props:"{i, j} \<in> set (edges_of_path (ids@[hd ids]))" 
           "lookup L i' = Some (subverts ids)" 
     using asm by auto
   moreover hence "i \<in> set ids"  "j \<in> set ids"
     using edges_of_path_length[of "ids @ [hd ids]"]  hd_in_set
           length_pos_if_in_set[of "{i, j}" "edges_of_path (ids @ [hd ids])"]
           edge_not_in_edges_in_path[of i "ids @ [hd ids]" j]
      by auto
    ultimately have "collect_verts L i \<subseteq> collect_verts L i'" 
                    "collect_verts L j \<subseteq> collect_verts L i'"
      using assms by(auto simp add: collect_verts_simps[of L i'])
   moreover obtain m where m_props: "m\<in>max_ids L" "i' \<in> ids_of_sub_laminars L m"
     using assms  i_ids_props(2) in_dom_a_max_id[of L i']
     by(auto elim!:  laminar_forest_invarE)
   moreover hence " collect_verts L i' \<subseteq>  collect_verts L m" 
     using  assms by(auto simp add: collect_verts_uf[of L m])
   ultimately show ?thesis
     by(auto intro!: bexI[of _ m])
 qed
qed

interpretation blossom_forest_spec_statisfied: blossom_forest_spec
  where all_ids = "\<lambda> (maxes, L). dom (lookup L)"
  and universe =  "\<lambda> (maxes, L). all_verts L"
  and collect_elems = "\<lambda> (maxes, L). collect_verts L"
  and max_ids = "\<lambda> (maxes, L). max_ids L"
  and blossom_forest_invar = blossom_forest_invar
  and laminar_abstract = "\<lambda> (maxes, L). {collect_verts L i | i. i \<in> dom (lookup L)}"
  and compound = compound
  and blossom_edges = blossom_edges
proof(rule blossom_forest_spec.intro, goal_cases)
  case 1
  then show ?case 
  proof(rule laminar_family_spec.intro, goal_cases)
  case (1 L i)
  then show ?case  
    using collect_verts_uf'
    by (auto simp add: all_verts_def)
next
  case (2 L)
  then show ?case 
  proof(cases L, goal_cases)
    case (1 top L)
    then show ?case 
      using important_properties(5)[of top L]
      by simp
  qed
next
  case (3 L)
  then show ?case
  proof(cases L, goal_cases)
    case (1 top L)
    then show ?case 
      by(auto intro!: forw_subst[of _ _ "laminar (all_verts L)",
                   OF _ important_properties(2)[of top L]])
  qed
next
  case (4 L)
  then show ?case 
  proof(cases L, goal_cases)
    case (1 top L)
    then show ?case 
      using important_properties(3)[of top L] 
      by simp
  qed
next
  case (5 L id)
  then show ?case
  proof(cases L, goal_cases)
    case (1 top L)
    note one = this
    then show ?case 
    proof(cases "lookup L id", goal_cases)
      case 1
      then show ?thesis 
        by(auto simp add: compound_def)
    next
      case (Some a)
      then show ?thesis 
      proof(cases a, goal_cases)
        case (1 x1)
        then show ?case
          using 5
          by(auto simp add: compound_def one)
      next
        case (2 x2)
        then show ?case 
          using important_properties(6)[of top L id] 5 one 
          by simp
      qed
    qed
  qed
qed
next
  case 2
  show ?case
proof(rule blossom_forest_spec_axioms.intro, goal_cases)
  case (1  L i)
  then show ?case 
    by(cases L)(auto dest: branching_odd_collect_verts_odd)
next
  case (2 L)
  then show ?case 
    using blossom_edges_props(1)
    by(cases L) auto
next
  case (3  L)
  then show ?case
    using blossom_edges_props(2)
    by(cases L) auto
next
  case (4 L i j)
  then show ?case 
    by (cases L)(force intro!: blossom_edges_props(3)[of _ _ i j])
qed
qed

lemma merge_precond_from_forest_merge_precond:
 "blossom_forest_spec_statisfied.blossom_forest_merge_precond (maxids, L) ids new_id \<Longrightarrow>
    laminar_family_spec.laminar_merge_precond (\<lambda>(maxes, L). dom (lookup L))
     (\<lambda>(maxes, y). max_ids y) laminar_forest_invar (maxids, L) ids new_id"
  by(intro   laminar_family_spec.laminar_merge_precondI[OF laminar_family_spec_statisfied_axioms])
    (auto elim!: blossom_forest_spec_statisfied.blossom_forest_merge_precondE)

lemma blossom_forest_merge_inter:
  assumes "blossom_forest_spec_statisfied.blossom_forest_merge_precond (maxids, L) ls new_id"
  shows "blossom_forest_invar (merge (maxids, L) ls new_id)" (is ?th1)
  and "blossom_edges (merge (maxids, L) ls new_id) =
       set (edges_of_path (ls @ [hd ls])) \<union> blossom_edges (maxids, L)" (is ?th2)
proof-
  note blossom_forest_merge_precondD = blossom_forest_spec_statisfied.blossom_forest_merge_precondD[OF assms(1)]
  note blossom_forest_invarD= blossom_forest_invarD[OF blossom_forest_merge_precondD(1)]
  note laminar_forest_invarD = laminar_forest_invarD[OF blossom_forest_invarD(1)]

  show ?th1
proof(rule blossom_forest_invarI, goal_cases)
  case 1
  then show ?case 
    using assms 
    by(intro merge_props(1) merge_precond_from_forest_merge_precond)
next
  case 2
  have "branching_odd (update new_id (subverts ls) L)"
  proof(rule branching_oddI, goal_cases)
    case (1 i vs)
    then show ?case 
      using blossom_forest_merge_precondD(1,6)
      by(cases "i = new_id")
        (auto dest: branching_oddD simp add: map.map_update laminar_forest_invarD(2) )
  qed
  thus ?case
    by simp
qed

  have helper: "\<exists>xa. (\<exists>ids. xa = set (edges_of_path (ids @ [hd ids])) \<and>
                   (\<exists>i. (i = new_id \<longrightarrow> ls = ids) \<and>
                        (i \<noteq> new_id \<longrightarrow> lookup L i = Some (subverts ids)))) \<and>
            x \<in> xa"
    if " x \<in> set (edges_of_path (ids @ [hd ids]))"
       "lookup L i = Some (subverts ids)" for x i ids
    using that blossom_forest_merge_precondD(5)
    by(auto intro!: exI[of _ "set (edges_of_path (ids @ [hd ids]))"] exI[of _ ids]
             exI[of _ i])

   show ?th2 
    using blossom_forest_merge_precondD(1,5)
    by(auto intro!: helper simp add: Let_def map.map_update if_split[of "\<lambda> x. x = Some _"]) auto
qed

lemmas merge_props = 
  blossom_forest_merge_inter(1) 
  merge_props(2-)[OF merge_precond_from_forest_merge_precond] 
  blossom_forest_merge_inter(2)

interpretation blossom_forest_merge_spec_statisfied:  blossom_forest_merge_spec
  where all_ids = "\<lambda> (maxes, L). dom (lookup L)"
  and universe =  "\<lambda> (maxes, L). all_verts L"
  and collect_elems = "\<lambda> (maxes, L). collect_verts L"
  and max_ids = "\<lambda> (maxes, L). max_ids L"
  and  blossom_forest_invar =  blossom_forest_invar
  and laminar_abstract = "\<lambda> (maxes, L). {collect_verts L i | i. i \<in> dom (lookup L)}"
  and compound = compound
  and merge = merge
  and blossom_edges =  blossom_edges
proof(rule  blossom_forest_merge_spec.intro, goal_cases)
  case 1
  then show ?case
    by (simp add: blossom_forest_spec_statisfied.blossom_forest_spec_axioms)
next
  case 2
  then show ?case 
  proof(rule  blossom_forest_merge_spec_axioms.intro, goal_cases)
    case (1 L ls new_id)
    then show ?case 
      using merge_props 
      by(cases L) auto
  next
    case (2 L ls new_id)
    then show ?case 
      using merge_props 
      by(cases L) auto
  next
    case (3 L ls new_id)
    then show ?case 
      using merge_props(3)
      by(cases L)(auto simp add: all_verts_def)
  next
    case (4 L ls new_id)
    then show ?case 
      using merge_props 
      by(cases L) auto
  next
    case (5  L ls new_id)
    then show ?case
      using merge_props 
      by(cases L) auto
  next
    case (6 L ls new_id)
    then show ?case
      using merge_props 
      by(cases L) auto
  next
    case (7 L ls new_id)
    then show ?case
      using merge_props 
      by(cases L) auto
  qed
qed

lemma unmerge_precond_from_forest_unmerge_precond:
 "blossom_forest_spec_statisfied.blossom_forest_unmerge_precond (maxids, L) id \<Longrightarrow>
  laminar_family_spec.laminar_unmerge_precond (\<lambda>(maxes, y). collect_verts y)
     (\<lambda>(maxes, y). max_ids y) laminar_forest_invar (maxids, L) id" for id
  by(intro laminar_family_spec.laminar_unmerge_precondI[OF laminar_family_spec_statisfied_axioms])
    (auto elim!: blossom_forest_spec_statisfied.blossom_forest_unmerge_precondE)

lemma blossom_forest_unmerge_inter:
  fixes id
  assumes "blossom_forest_spec_statisfied.laminar_unmerge_precond (maxids, L) id"
  and result_def: "unmerge (maxids, L) id = ((maxids', L'), ids)"
shows "blossom_forest_invar (maxids', L')" (is ?th1)
and "set (edges_of_path (ids @ [hd ids])) \<subseteq> blossom_edges (maxids, L)" (is ?th2)
and "blossom_edges (maxids', L') 
     = blossom_edges (maxids, L) - set (edges_of_path (ids @ [hd ids]))" (is ?th3)
and "3 \<le> length ids" (is ?th4)
and "odd (length ids)" (is ?th5)
proof-
  note laminar_unmerge_precondD =
    blossom_forest_spec_statisfied.laminar_unmerge_precondD[OF assms(1)]
  note blossom_forest_invarD= blossom_forest_invarD[OF laminar_unmerge_precondD(1)]
  note laminar_forest_invarD = laminar_forest_invarD[OF blossom_forest_invarD(1)]

have ids_def: "lookup L id = Some (subverts ids)" 
  proof(cases "lookup L id")
    case None
    then show ?thesis 
      using in_maxidsE laminar_unmerge_precondD(2) by blast
  next
    case (Some a)
    then show ?thesis 
    proof(cases a, goal_cases)
      case (1 x)
      hence "card (collect_verts L id) = 1"
        by(auto intro!: exI[of _ x] 
              simp add: card_1_singleton_iff collect_verts_simps laminar_forest_invarD(7))
      then show ?case 
        using laminar_unmerge_precondD(3) by simp
    next
      case (2 vs)
      then show ?case 
        using result_def by auto
    qed
  qed

  show ?th1
  proof(rule blossom_forest_invarI, goal_cases)
    case 1
    then show ?case 
      using assms 
      by(intro unmerge_props(1) unmerge_precond_from_forest_unmerge_precond) simp
  next
    case 2
    then show ?case
      using result_def  blossom_forest_invarD(2)
      by(auto dest: branching_oddD 
            intro!: branching_oddI 
          simp add: Let_def map.map_delete laminar_forest_invarD(2) if_split[of "\<lambda> x. x = Some _"])
  qed
  show ?th2
    by (auto intro!: exI[of _ "set (edges_of_path (ids @ [hd ids]))"]
           simp add: ids_def exI[of _ ids] exI[of _ id])

  show ?th3
    unfolding blossom_edges.simps
  proof(rule, all \<open>rule\<close>, goal_cases)
    case (1 e)
    then obtain ids' i where ids': "e \<in> set (edges_of_path (ids' @ [hd ids']))" 
         "lookup L' i = Some (subverts ids')"
      by auto
    hence i_not_id:"i \<noteq> id" 
      using assms(1) result_def unmerge_precond_from_forest_unmerge_precond unmerge_props(2)
      by fastforce
    hence  "lookup L i = Some (subverts ids')" 
      using result_def  blossom_forest_invarD(1) ids'(2)
      by(auto elim!: laminar_forest_invarE simp add: map.map_delete Let_def)
    moreover have "e \<notin> set (edges_of_path (ids @ [hd ids]))"
    proof(rule notI, goal_cases)
      case 1
      then obtain k j where "e = {k, j}" "k \<in> set ids" "j \<in> set ids"
        using v_in_edge_in_path_inj[of e ids] v_in_edge_in_path_inj[of e "ids @ [hd ids]"]
              v_in_edge_in_path_gen[of e ids] v_in_edge_in_path_gen[of e "ids @ [hd ids]"] 
        by (cases ids) force+
      moreover hence "k \<in> set ids'" "j \<in> set ids'"
        using ids'(1) hd_in_set[of ids']  edge_not_in_edges_in_path[of _ ids']
            v_in_edge_in_path_gen[of "{k, j}" "[]" k] v_in_edge_in_path_gen[of e "ids' @ [hd ids']" k]
            in_append_split[of e "[]" "edges_of_path ids'"] in_append_split[of j "[]" ids']
            in_append_split[of j ids' "[hd ids']"] edge_not_in_edges_in_path[of _ "ids' @ [hd ids']" ]
        by fastforce+
      ultimately have "i = id"
        using assms(1) ids'(2) in_maxidsE[of j L']
           unmerge_props(5)[OF unmerge_precond_from_forest_unmerge_precond, OF assms(1) result_def] 
        by auto
      thus ?case 
        using i_not_id by simp
    qed
    ultimately show ?case 
      using ids' by auto
  next
    case (2 e)
    then obtain ids' i where ids': "e \<in> set (edges_of_path (ids' @ [hd ids']))" 
         "lookup L i = Some (subverts ids')" "e \<notin> set (edges_of_path (ids @ [hd ids]))"
      by auto
    moreover hence "i \<noteq> id"
      using ids_def by force
    ultimately have "lookup L' i = lookup L i"
      using   result_def 
      by(auto simp add: laminar_forest_invarD(2) map.map_delete Let_def)
    then show ?case 
      using ids'
      by(auto intro!: exI[of _ "set (edges_of_path (ids' @ [hd ids']))"] exI[of _ ids'])
  qed
  show ?th4
    using laminar_unmerge_precondD(1) ids_def 
    by (auto intro:  nat_geq_3I dest!: branching_oddD branching_properlyD)
  show ?th5
    using laminar_unmerge_precondD(1) ids_def 
    by (auto  dest!: branching_oddD )
qed

lemmas unmerge_props = 
  blossom_forest_unmerge_inter(1) 
  unmerge_props(2-)[OF unmerge_precond_from_forest_unmerge_precond] 
  blossom_forest_unmerge_inter(2-)

interpretation blossom_forest_unmerge_spec_statisfied:  blossom_forest_unmerge_spec
  where all_ids = "\<lambda> (maxes, L). dom (lookup L)"
  and universe =  "\<lambda> (maxes, L). all_verts L"
  and collect_elems = "\<lambda> (maxes, L). collect_verts L"
  and max_ids = "\<lambda> (maxes, L). max_ids L"
  and  blossom_forest_invar =  blossom_forest_invar
  and laminar_abstract = "\<lambda> (maxes, L). {collect_verts L i | i. i \<in> dom (lookup L)}"
  and compound = compound
  and unmerge = unmerge
  and blossom_edges =  blossom_edges
proof(rule  blossom_forest_unmerge_spec.intro, goal_cases)
  case 1
  then show ?case
    by (simp add: blossom_forest_spec_statisfied.blossom_forest_spec_axioms)
next
  case 2
  then show ?case 
  proof(rule blossom_forest_unmerge_spec_axioms.intro, goal_cases)
case (1 L id L' ids)
    then show ?case 
      using unmerge_props(1)[of _ _ id]
      by(cases L, cases L') auto 
  next
    case (2 L id L' ids)
    then show ?case 
      using unmerge_props(2)[of _ _ id]
      by(cases L, cases L') auto 
  next
    case (3 L id L' ids)
    then show ?case
      using unmerge_props(3)[of _ _ id]
      by(cases L, cases L') (auto simp add: all_verts_def)
  next
    case (4 L id L' ids id')
    then show ?case
      using unmerge_props(4)[of _ _ id]
      by(cases L, cases L') auto 
  next
    case (5 L id L' ids)
    then show ?case 
      using unmerge_props(5)[of _ _ id]
      by(cases L, cases L') auto 
  next
    case (6 L id L' ids)
    then show ?case 
      using unmerge_props(6)[of _ _ id]
      by(cases L, cases L') auto 
  next
    case (9 L id L' ids)
    then show ?case 
      using unmerge_props(7)[of _ _ id]
      by(cases L, cases L') auto 
  next
    case (7 L id L' ids)
    then show ?case 
      using unmerge_props(10)[of _ _ id]
      by(cases L, cases L') auto 
  next
    case (8 L id L' ids)
    then show ?case 
      using unmerge_props(9)[of _ _ id]
      by(cases L, cases L') auto 
  next
    case (10 L id L' ids)
    then show ?case 
      using unmerge_props(11)[of _ _ id]
      by(cases L, cases L') auto 
  next
    case (11 L id L' ids)
    then show ?case 
      using unmerge_props(12)[of _ _ id]
      by(cases L, cases L') auto
  qed
qed


interpretation blossom_forest_iteration_spec_statisfied: blossom_forest_iteration_spec
  where all_ids = "\<lambda> (maxes, L). dom (lookup L)"
  and universe =  "\<lambda> (maxes, L). all_verts L"
  and collect_elems = "\<lambda> (maxes, L). collect_verts L"
  and max_ids = "\<lambda> (maxes, L). max_ids L"
  and blossom_forest_invar = blossom_forest_invar
  and laminar_abstract = "\<lambda> (maxes, L). {collect_verts L i | i. i \<in> dom (lookup L)}"
  and compound = compound
  and max_qualified_iteration = "\<lambda> P (maxes, L) f acc. max_qualified_fold P L f acc maxes"
  and elems_iteration = "\<lambda> (maxes, L) i f acc . laminar_fold_singletons L f acc i"
  and blossom_edges = blossom_edges
proof(rule blossom_forest_iteration_spec.intro, goal_cases)
  case 1
  then show ?case 
    by (simp add: blossom_forest_spec_statisfied.blossom_forest_spec_axioms)
next
  case 2
  show ?case
  proof(rule blossom_forest_iteration_spec_axioms.intro, goal_cases)
    case (1 P L f acc)
    then show ?case
    proof(cases L, goal_cases)
      case (1 maxids L)
      then show ?case 
        by (intro ex_forward[OF max_qualified_fold_correct[of maxids L P f acc]]) auto
    qed
  next
    case (2 L id f acc)
    then show ?case
    proof(cases L, goal_cases)
      case (1 maxids L)
      then show ?case 
        by (auto intro!: ex_forward[OF laminar_fold_singletons_correct [of L id f acc]] 
                         disjoint_elems_if_disjoint_subids_and_elem_unique_id)
    qed
  qed
qed
end
end