theory Laminar_Family_Executable
  imports Laminar_Family.Laminar_Family "HOL-Data_Structures.Map_Specs"
           "HOL-Data_Structures.Set_Specs" Directed_Set_Graphs.More_Lists
          Laminar_Spec
begin

datatype ('v, 'id) contracted_laminar = elem_vert (the_vert: 'v) 
  | subverts (the_children :"'id list")
term foldl
locale laminar_tree = 
 map : Map where update = update + 
 top_set : Set where insert = top_insert and empty = top_empty and delete = top_delete 
               and invar = top_invar and set = top_set for
  top_insert::"'id \<Rightarrow> 'set \<Rightarrow> 'set"
 and update :: "'id \<Rightarrow> ('v, 'id) contracted_laminar \<Rightarrow> 'map \<Rightarrow> 'map"
and top_empty::'set and top_delete and top_invar and top_set +
fixes set_fold :: "('acc \<Rightarrow> 'id \<Rightarrow> 'acc) \<Rightarrow> 'acc \<Rightarrow> 'set \<Rightarrow> 'acc"
assumes set_fold: 
  "\<And> S f acc. top_invar S \<Longrightarrow> \<exists> xs. set xs = top_set S \<and> distinct xs \<and>
             set_fold f acc S = foldl f acc xs"
begin

subsection \<open>Function Definitions\<close>

context 
  fixes M :: 'map
begin

function (domintros) ids_of_sub_laminars where 
 "ids_of_sub_laminars i =
          (case lookup M i of None \<Rightarrow> {} 
           | Some B \<Rightarrow> 
             (case B of elem_vert _ \<Rightarrow> {i} |
                        subverts vs \<Rightarrow> {i} 
               \<union> \<Union> (ids_of_sub_laminars `  set vs)))"
  by pat_completeness auto

definition "laminar_forest_rel = (\<lambda> j i. \<exists> vs. lookup M i = Some (subverts vs) \<and> j \<in> set vs)"

definition "laminar_forest_cons = {(j, i) | i j vs. lookup M i = Some (subverts vs) \<and>j \<in> set vs}"

lemma ids_of_sub_laminars_rel_def[simp]:
  "ids_of_sub_laminars_rel = laminar_forest_rel"
  unfolding ids_of_sub_laminars_rel.simps laminar_forest_rel_def
  by (auto intro!: ext)

lemma ids_dom_if_wf:
  assumes "wf laminar_forest_cons"
  shows "ids_of_sub_laminars_dom i"
proof-
  show ?thesis
    apply(rule accp_wfpD)
    unfolding wfp_def
    apply(rule forw_subst[where P= wf, OF _ assms])
    unfolding ids_of_sub_laminars_rel_def laminar_forest_cons_def laminar_forest_rel_def
    by auto
 qed

lemmas ids_of_sub_laminars_simps =
   ids_of_sub_laminars.psimps[OF ids_dom_if_wf]

lemma in_ids_of_sub_laminars_cases:
  assumes "wf laminar_forest_cons"
          "j \<in> ids_of_sub_laminars i"
          "\<And> x. \<lbrakk>lookup M i = Some (elem_vert x); i = j\<rbrakk> \<Longrightarrow> P"
          "\<And> vs.\<lbrakk>lookup M i = Some (subverts vs); i = j\<rbrakk> \<Longrightarrow> P"
         "\<And> vs i'. \<lbrakk>lookup M i = Some (subverts vs); i' \<in> set vs; j  \<in> ids_of_sub_laminars i'\<rbrakk> \<Longrightarrow> P"
       shows P
  using assms(2)
  unfolding ids_of_sub_laminars_simps[OF assms(1), of i]
proof(cases "lookup M i", goal_cases)
  case 1
  then show ?case 
    by auto
next
  case (2 a)
  then show ?case 
  proof(cases a, goal_cases)
    case (1 x1)
    then show ?thesis 
      by (auto  intro!: assms(3))
  next
    case (2 x2)
    then show ?thesis
      by(auto intro: assms(4,5))
  qed
qed

lemma ids_of_sub_laminars_induct:
assumes "wf laminar_forest_cons"
shows "(\<And>i. (\<And>x2 x2a x.
          lookup M i = Some x2 \<Longrightarrow>
          x2 = subverts x2a \<Longrightarrow> x \<in> set x2a \<Longrightarrow> P x) \<Longrightarrow>
      P i) \<Longrightarrow> P i"
  using ids_of_sub_laminars.pinduct ids_dom_if_wf[OF assms] 
  by auto

lemma ids_mono:
 assumes "wf laminar_forest_cons"
   shows "j \<in> ids_of_sub_laminars i \<Longrightarrow> ids_of_sub_laminars j \<subseteq> ids_of_sub_laminars i"
proof(induction rule: ids_of_sub_laminars_induct[OF assms])
  case (1 i)
  note IH = this
  show ?case 
    using 1(2)
    unfolding ids_of_sub_laminars_simps[OF assms, of i]
  proof(cases "lookup M i", goal_cases)
    case 1
    then show ?case by simp
  next
    case (2 a)
    then show ?case
    proof(cases a, goal_cases)
      case (1 x1)
      then show ?case 
        by(simp add: ids_of_sub_laminars_simps[OF assms])
    next
      case (2 vs)
      then show ?case 
      proof(cases "j = i", goal_cases)
        case 1
        then show ?case
          by(auto simp add: ids_of_sub_laminars_simps[OF assms])
      next
        case 2
        then obtain i' where i': "i' \<in> set vs" "j \<in> ids_of_sub_laminars i'"
          by auto
        then show ?case
          using  IH(1) 2 by fastforce         
      qed
    qed
  qed
qed

lemma ids_in_dom:
assumes "wf laminar_forest_cons"
shows "ids_of_sub_laminars i \<subseteq> dom (lookup M)"
proof(induction rule: ids_of_sub_laminars_induct[OF assms])
  case (1 i)
  note IH = this
  show ?case 
    unfolding ids_of_sub_laminars_simps[OF assms, of i]
  proof(cases "lookup M i", goal_cases)
    case 1
    then show ?case by simp
  next
    case (2 a)
    then show ?case
    proof(cases a, goal_cases)
      case (1 x1)
      then show ?case 
        by(auto simp add: ids_of_sub_laminars_simps[OF assms])
    next
      case (2 vs)
      note two = this
      have "{i} \<union> \<Union> (ids_of_sub_laminars ` set vs) \<subseteq> dom (lookup M)"
      proof(rule, elim UnE, goal_cases)
        case (1 x)
        then show ?case 
          using 2 by auto
      next
        case (2 x)
        then obtain i' where i': "i' \<in> set vs" "x \<in> ids_of_sub_laminars i'"
          by auto
        then show ?case
          using  IH(1)[OF two] by fastforce         
      qed
      thus ?case
        using two by auto
    qed
  qed
qed

lemma not_in_subtree:
  assumes "wf laminar_forest_cons" "lookup M i = Some (subverts vs)" "j \<in> set vs"
   shows  "i \<notin> ids_of_sub_laminars j"
  using assms(3,2)
proof(induction arbitrary: i vs rule: ids_of_sub_laminars_induct[OF assms(1)])
  case (1 j)
  note IH = this
  show ?case 
    using IH(2-3)
  unfolding ids_of_sub_laminars_simps[OF assms(1), of j]
  proof(cases "lookup M j", goal_cases)
    case 1
    then show ?case by simp
  next
    case (2 a)
    then show ?case
    proof(cases a, goal_cases)
      case (1 x1)
      then show ?case 
        by(auto simp add: ids_of_sub_laminars_simps[OF assms(1)])
    next
      case (2 vsa)
      note two = this
      moreover have "\<lbrakk>x \<in> set vsa; i \<in> ids_of_sub_laminars x\<rbrakk> \<Longrightarrow> False" for x
      proof(goal_cases)
        case 1
        hence "j \<notin> ids_of_sub_laminars x"
          using 2
          by(intro IH(1)[OF 2(3,4), of x vsa j]) auto
        moreover have "j \<in> ids_of_sub_laminars i"
          using assms(1) ids_of_sub_laminars_simps two(1,2,3,4)
          by fastforce
        moreover have "ids_of_sub_laminars i \<subseteq> ids_of_sub_laminars x" 
          using 1 assms(1) ids_mono by blast
        ultimately show ?case 
          by auto
      qed
      thus ?case
        using two(1,2,3,4)
        by (fastforce simp add: ids_of_sub_laminars_simps[OF assms(1), of j])
    qed
  qed
qed

lemma self_in_ids:
  assumes "wf laminar_forest_cons" "lookup M i \<noteq> None"
    shows "i \<in> ids_of_sub_laminars i"
  using assms(2)
  by(auto simp add: ids_of_sub_laminars_simps[OF assms(1)]
             split: option.split contracted_laminar.split)

lemma self_in_ids':
  assumes "ids_of_sub_laminars_dom i" "lookup M i \<noteq> None"
    shows "i \<in> ids_of_sub_laminars i"
  using assms(2)
  by(auto simp add: ids_of_sub_laminars.psimps[OF assms(1)]
             split: option.split contracted_laminar.split)

lemma immediate_childrenin_ids:
  assumes "wf laminar_forest_cons"
          "lookup M i = Some (subverts vs)" "j \<in> set vs" "lookup M j \<noteq> None"
    shows "j \<in> ids_of_sub_laminars i"
  using assms(2,3) self_in_ids[OF assms(1,4)]
  by(auto simp add: ids_of_sub_laminars_simps[OF assms(1), of i]
             split: option.split contracted_laminar.split)


function (domintros) collect_verts where 
 "collect_verts i =
          (case lookup M i of None \<Rightarrow> {} 
           | Some B \<Rightarrow> 
             (case B of elem_vert x \<Rightarrow> {x} |
                        subverts vs \<Rightarrow>  \<Union> (collect_verts `  set vs)))"
  by pat_completeness auto

lemma collect_verts_rel_def:
  "collect_verts_rel = laminar_forest_rel"
  unfolding collect_verts_rel.simps laminar_forest_rel_def
  by (auto intro!: ext)

lemma collected_verts_dom_if_wf:
  assumes "wf laminar_forest_cons"
  shows "collect_verts_dom i"
proof-
  show ?thesis
    apply(rule accp_wfpD)
    unfolding wfp_def
    apply(rule forw_subst[where P= wf, OF _ assms])
     unfolding collect_verts_rel_def laminar_forest_cons_def laminar_forest_rel_def
     by auto
 qed

lemmas collect_verts_simps =
   collect_verts.psimps[OF collected_verts_dom_if_wf]

lemma collect_verts_induct:
assumes "wf laminar_forest_cons"
shows "(\<And>i. (\<And>x2 x2a x.
          lookup M i = Some x2 \<Longrightarrow>
          x2 = subverts x2a \<Longrightarrow> x \<in> set x2a \<Longrightarrow> P x) \<Longrightarrow>
      P i) \<Longrightarrow> P i"
  using collect_verts.pinduct collected_verts_dom_if_wf[OF assms] 
  by auto

lemma collect_verts_uf:
  assumes "wf laminar_forest_cons"
  shows "collect_verts i = \<Union> (collect_verts ` (ids_of_sub_laminars i))"
proof(rule, goal_cases)
  case 1
  then show ?case 
    by(auto simp add: ids_of_sub_laminars_simps[OF assms, of i]
                collect_verts_simps[OF assms, of i] 
              split: option.split contracted_laminar.split)
next
  case 2
  then show ?case
  proof(induction rule: collect_verts_induct[OF assms])
    case (1 i)
    thus ?case
      by(auto simp add: ids_of_sub_laminars_simps[OF assms, of i]
                        collect_verts_simps[OF assms, of i]
                 split: option.split contracted_laminar.split) blast
  qed
qed

lemma collect_verts_uf':
  assumes "wf laminar_forest_cons"
  shows "collect_verts i = {x | x i'. i' \<in> ids_of_sub_laminars i \<and> lookup M i' = Some (elem_vert x)}"
  proof(induction rule: collect_verts_induct[OF assms])
    case (1 i)
    thus ?case
     by(auto simp add: ids_of_sub_laminars_simps[OF assms, of i]
                        collect_verts_simps[OF assms, of i]
                 split: option.split contracted_laminar.split) 
 qed

lemma Nil_iff_no_elem: "xs \<noteq> Nil \<Longrightarrow> \<exists> x. x \<in> set xs"
  by(cases xs) auto

function (domintros) laminar_tree_fold where 
 "laminar_tree_fold f acc i =
       (case lookup M i of None \<Rightarrow> acc 
           | Some B \<Rightarrow> 
             (case B of elem_vert x \<Rightarrow> f acc i |
                        subverts vs \<Rightarrow> foldl (\<lambda> acc i. laminar_tree_fold f acc i) (f acc i) vs))"
  by pat_completeness auto

function (domintros) laminar_fold_singletons where 
 "laminar_fold_singletons f acc i =
       (case lookup M i of None \<Rightarrow> acc 
           | Some B \<Rightarrow> 
             (case B of elem_vert x \<Rightarrow> f acc x |
                        subverts vs \<Rightarrow> foldl (\<lambda> acc i. laminar_fold_singletons f acc i) acc vs))"
  by pat_completeness auto

lemma  laminar_forest_cons_def': 
  "laminar_forest_cons = {(x, y) |x y. laminar_forest_rel x y}"
  by(auto simp add:  laminar_forest_cons_def laminar_forest_rel_def)

lemma laminar_tree_fold_dom:
  assumes "wf laminar_forest_cons"
  shows "laminar_tree_fold_dom (f, acc, i)" 
  by(induction arbitrary: f acc rule: ids_of_sub_laminars_induct[OF assms])
    (auto intro: laminar_tree_fold.domintros)

lemmas laminar_tree_fold_simps = laminar_tree_fold.psimps[OF laminar_tree_fold_dom]

lemma laminar_tree_fold_rel_wf:
  assumes "wf laminar_forest_cons"
  shows "wf {(x, y). laminar_tree_fold_rel x y}" 
  using laminar_tree_fold_dom[OF assms]
  unfolding wfp_def[of laminar_tree_fold_rel,  symmetric]
  by(force intro!: accp_wfpI)

lemma laminar_tree_fold_rel_wf':
  assumes "wf laminar_forest_cons"
  shows  "wf {(x, y) | x y . laminar_tree_fold_rel x y}" 
  by(rule forw_subst[of _ "{(x, y) . laminar_tree_fold_rel x y}"])
    (auto intro!:  laminar_tree_fold_rel_wf[OF assms])

lemma laminar_fold_singletons_dom:
  assumes "wf laminar_forest_cons"
  shows "laminar_fold_singletons_dom (f, acc, i)" 
  by(induction arbitrary: f acc rule: ids_of_sub_laminars_induct[OF assms])
    (auto intro: laminar_fold_singletons.domintros)

lemmas laminar_fold_singletons_simps = laminar_fold_singletons.psimps[OF laminar_fold_singletons_dom]

lemma laminar_fold_singletons_rel_wf:
  assumes "wf laminar_forest_cons"
  shows "wf {(x, y). laminar_fold_singletons_rel x y}" 
  using laminar_fold_singletons_dom[OF assms]
  unfolding wfp_def[of laminar_fold_singletons_rel,  symmetric]
  by(force intro!: accp_wfpI)

lemma laminar_fold_singletons_rel_wf':
  assumes "wf laminar_forest_cons"
  shows  "wf {(x, y) | x y . laminar_fold_singletons_rel x y}" 
  by(rule forw_subst[of _ "{(x, y) . laminar_fold_singletons_rel x y}"])
    (auto intro!:  laminar_fold_singletons_rel_wf[OF assms])

end

definition 
  "max_qualified_fold P M f acc S =
     set_fold (\<lambda> acc i. if P i then laminar_tree_fold M f acc i else acc) acc S"

definition
  "compound = (\<lambda> (maxes, L) id. case lookup L id of None \<Rightarrow> False
                                    | Some node \<Rightarrow>
                                       case node of elem_vert _ \<Rightarrow> False
                                      | subverts _ \<Rightarrow> True)"

fun merge where
 "merge (maxes, L) ids newid =
     (let new_maxes = foldl (\<lambda> S x. top_delete x S) maxes ids;
          new_L = update newid (subverts ids) L
      in (top_insert newid new_maxes, new_L))"

fun unmerge where
 "unmerge (maxes, L) id =
     (let ids = the_children (the (lookup L id));
          new_maxes = foldl (\<lambda> S x. top_insert x S) maxes ids;
          new_L = delete id L
      in ((top_delete id new_maxes, new_L), ids))" 
for id

subsection \<open>Invariant Definitions\<close>

definition "max_ids M = 
   {i | i. lookup M i \<noteq> None \<and> 
           (\<nexists> i' vs. lookup M i' = Some (subverts vs) \<and> i \<in> set vs)}"

lemma in_maxidsI:
 "\<lbrakk> lookup M i \<noteq> None; \<And> i' vs. \<lbrakk>lookup M i' = Some (subverts vs); i \<in> set vs\<rbrakk> \<Longrightarrow> False\<rbrakk> 
  \<Longrightarrow> i \<in> max_ids M"
  by (auto simp add: max_ids_def)

lemma in_maxidsE:
 "\<lbrakk>i \<in> max_ids M; 
   \<lbrakk>lookup M i \<noteq> None; \<And> i' vs. \<lbrakk>lookup M i' = Some (subverts vs); i \<in> set vs\<rbrakk> \<Longrightarrow> False\<rbrakk> \<Longrightarrow> P\<rbrakk> 
  \<Longrightarrow> P"
  by (auto simp add: max_ids_def)

definition "children_nempty M =
   (\<forall> i vs. lookup M i = Some (subverts vs) \<longrightarrow> vs \<noteq> [])"

lemma children_nemptyI:
  "(\<And>i vs. lookup M i = Some (subverts vs) \<Longrightarrow> vs \<noteq> []) 
  \<Longrightarrow> children_nempty M"
  unfolding children_nempty_def by blast

lemma children_nemptyE:
  "\<lbrakk>children_nempty M;
    (\<And>i vs. lookup M i = Some (subverts vs) \<Longrightarrow> vs \<noteq> []) \<Longrightarrow> P\<rbrakk> 
  \<Longrightarrow> P"
  unfolding children_nempty_def by blast

lemma children_nemptyD:
  "\<lbrakk>children_nempty M; lookup M i = Some (subverts vs)\<rbrakk> 
  \<Longrightarrow> vs \<noteq> []"
  unfolding children_nempty_def by blast

definition "domain_recursive M =
   (\<forall> i j vs. lookup M i = Some (subverts vs) \<and> j \<in> set vs \<longrightarrow> lookup M j \<noteq> None)"

lemma domain_recursiveI:
  "(\<And>i j vs. \<lbrakk>lookup M i = Some (subverts vs); j \<in> set vs\<rbrakk> \<Longrightarrow> lookup M j \<noteq> None) 
  \<Longrightarrow> domain_recursive M"
  unfolding domain_recursive_def by blast

lemma domain_recursiveE:
  "\<lbrakk>domain_recursive M;
    (\<And>i j vs. \<lbrakk>lookup M i = Some (subverts vs); j \<in> set vs\<rbrakk> \<Longrightarrow> lookup M j \<noteq> None) \<Longrightarrow> P\<rbrakk> 
  \<Longrightarrow> P"
  unfolding domain_recursive_def by blast

lemma domain_recursiveD:
  "\<lbrakk>domain_recursive M; lookup M i = Some (subverts vs); j \<in> set vs\<rbrakk> 
  \<Longrightarrow> lookup M j \<noteq> None"
  unfolding domain_recursive_def by blast

definition "disjoint_subids M = 
 (\<forall> i vs. lookup M i = Some (subverts vs) \<longrightarrow>
      (\<forall> j k. j \<in> set vs \<and> k \<in> set vs \<and> j \<noteq> k 
         \<longrightarrow> ids_of_sub_laminars M j \<inter> ids_of_sub_laminars M k = {}))"

lemma disjoint_subidsI:
  "(\<And>i vs j k. \<lbrakk>lookup M i = Some (subverts vs); j \<in> set vs; k \<in> set vs; j \<noteq> k\<rbrakk> 
     \<Longrightarrow> ids_of_sub_laminars M j \<inter> ids_of_sub_laminars M k = {}) 
  \<Longrightarrow> disjoint_subids M"
  unfolding disjoint_subids_def by simp

lemma disjoint_subidsD:
  "\<lbrakk>disjoint_subids M; lookup M i = Some (subverts vs); j \<in> set vs; k \<in> set vs; j \<noteq> k\<rbrakk> 
  \<Longrightarrow> ids_of_sub_laminars M j \<inter> ids_of_sub_laminars M k = {}"
  unfolding disjoint_subids_def by blast

lemma disjoint_subidsE:
  "\<lbrakk>disjoint_subids M; 
    (\<And> i j k. \<lbrakk>lookup M i = Some (subverts vs); j \<in> set vs; k \<in> set vs; j \<noteq> k\<rbrakk> \<Longrightarrow>
    ids_of_sub_laminars M j \<inter> ids_of_sub_laminars M k = {}) \<Longrightarrow> P\<rbrakk> 
  \<Longrightarrow> P"
  unfolding disjoint_subids_def by blast

definition "disjoint_trees M = 
  (\<forall> i j. i \<in> max_ids M \<and> j \<in> max_ids M \<and> i \<noteq> j 
          \<longrightarrow> ids_of_sub_laminars M j \<inter> ids_of_sub_laminars M i = {})"

lemma disjoint_treesI:
  "(\<And>i j. \<lbrakk>i \<in> max_ids M; j \<in> max_ids M; i \<noteq> j\<rbrakk> 
     \<Longrightarrow> ids_of_sub_laminars M j \<inter> ids_of_sub_laminars M i = {}) 
  \<Longrightarrow> disjoint_trees M"
  unfolding disjoint_trees_def by simp

lemma disjoint_treesD:
  "\<lbrakk>disjoint_trees M; i \<in> max_ids M; j \<in> max_ids M; i \<noteq> j\<rbrakk> 
  \<Longrightarrow> ids_of_sub_laminars M j \<inter> ids_of_sub_laminars M i = {}"
  unfolding disjoint_trees_def by blast

lemma disjoint_treesE:
  "\<lbrakk>disjoint_trees M; (\<And> i k. \<lbrakk>i \<in> max_ids M; j \<in> max_ids M; i \<noteq> j\<rbrakk>
    \<Longrightarrow> ids_of_sub_laminars M j \<inter> ids_of_sub_laminars M i = {}) \<Longrightarrow> P\<rbrakk> 
  \<Longrightarrow> P"
  unfolding disjoint_trees_def by blast

definition "elem_unique_id M =
  (\<forall> x i j. lookup M i = Some (elem_vert x) \<and> lookup M j = Some (elem_vert x)
            \<longrightarrow> i = j)"

lemma elem_unique_idI:
  "(\<And>x i j. \<lbrakk>lookup M i = Some (elem_vert x); lookup M j = Some (elem_vert x)\<rbrakk> \<Longrightarrow> i = j) 
  \<Longrightarrow> elem_unique_id M"
  unfolding elem_unique_id_def by blast

lemma elem_unique_idE:
  "\<lbrakk>elem_unique_id M; 
    (\<And>x i j. \<lbrakk>lookup M i = Some (elem_vert x); lookup M j = Some (elem_vert x)\<rbrakk> \<Longrightarrow> i = j) \<Longrightarrow> P\<rbrakk> 
  \<Longrightarrow> P"
  unfolding elem_unique_id_def by blast

lemma elem_unique_idD:
  "\<lbrakk>elem_unique_id M; lookup M i = Some (elem_vert x); lookup M j = Some (elem_vert x)\<rbrakk> 
  \<Longrightarrow> i = j"
  unfolding elem_unique_id_def by blast

definition "disjoint_elem_verts M = 
 (\<forall> i vs. lookup M i = Some (subverts vs) \<longrightarrow>
      (\<forall> j k. j \<in> set vs \<and> k \<in> set vs \<and> j \<noteq> k 
         \<longrightarrow> collect_verts M j \<inter> collect_verts M k = {}))"

lemma disjoint_elem_vertsI:
  "(\<And>i vs j k. \<lbrakk>lookup M i = Some (subverts vs); j \<in> set vs; k \<in> set vs; j \<noteq> k\<rbrakk> 
     \<Longrightarrow> collect_verts M j \<inter> collect_verts M k = {}) 
  \<Longrightarrow> disjoint_elem_verts M"
  unfolding disjoint_elem_verts_def by blast

lemma disjoint_elem_vertsE:
  "\<lbrakk>disjoint_elem_verts M;
    (\<And>i vs j k. \<lbrakk>lookup M i = Some (subverts vs); j \<in> set vs; k \<in> set vs; j \<noteq> k\<rbrakk> 
     \<Longrightarrow> collect_verts M j \<inter> collect_verts M k = {}) \<Longrightarrow> P\<rbrakk> 
  \<Longrightarrow> P"
  unfolding disjoint_elem_verts_def by blast

lemma disjoint_elem_vertsD:
  "\<lbrakk>disjoint_elem_verts M; lookup M i = Some (subverts vs); j \<in> set vs; k \<in> set vs; j \<noteq> k\<rbrakk> 
  \<Longrightarrow> collect_verts M j \<inter> collect_verts M k = {}"
  unfolding disjoint_elem_verts_def by blast

definition "disjoint_elems_over_trees M = 
  (\<forall> i j. i \<in> max_ids M \<and> j \<in> max_ids M \<and> i \<noteq> j 
          \<longrightarrow> collect_verts M j \<inter> collect_verts M i = {})"

lemma disjoint_elems_over_treesI:
  "(\<And>i j. \<lbrakk>i \<in> max_ids M; j \<in> max_ids M; i \<noteq> j\<rbrakk> 
     \<Longrightarrow> collect_verts M j \<inter> collect_verts M i = {}) 
  \<Longrightarrow> disjoint_elems_over_trees M"
  unfolding disjoint_elems_over_trees_def by blast

lemma disjoint_elems_over_treesE:
  "\<lbrakk>disjoint_elems_over_trees M;
    (\<And>i j. \<lbrakk>i \<in> max_ids M; j \<in> max_ids M; i \<noteq> j\<rbrakk> 
     \<Longrightarrow> collect_verts M j \<inter> collect_verts M i = {}) \<Longrightarrow> P\<rbrakk> 
  \<Longrightarrow> P"
  unfolding disjoint_elems_over_trees_def by blast

lemma disjoint_elems_over_treesD:
  "\<lbrakk>disjoint_elems_over_trees M; i \<in> max_ids M; j \<in> max_ids M; i \<noteq> j\<rbrakk> 
  \<Longrightarrow> collect_verts M j \<inter> collect_verts M i = {}"
  unfolding disjoint_elems_over_trees_def by blast

definition "branching_properly M =
   (\<forall> i vs. lookup M i = Some (subverts vs) \<longrightarrow> length vs \<ge> 2)"

lemma branching_properlyI:
  "(\<And>i vs. lookup M i = Some (subverts vs) \<Longrightarrow> length vs \<ge> 2) 
  \<Longrightarrow> branching_properly M"
  unfolding branching_properly_def by blast

lemma branching_properlyE:
  "\<lbrakk>branching_properly M;
    (\<And>i vs. lookup M i = Some (subverts vs) \<Longrightarrow> length vs \<ge> 2) \<Longrightarrow> P\<rbrakk> 
  \<Longrightarrow> P"
  unfolding branching_properly_def by blast

lemma branching_properlyD:
  "\<lbrakk>branching_properly M; lookup M i = Some (subverts vs)\<rbrakk> 
  \<Longrightarrow> length vs \<ge> 2"
  unfolding branching_properly_def by blast

definition "distinct_children M = (\<forall> i vs. lookup M i = Some (subverts vs) \<longrightarrow> distinct vs)"

lemma distinct_childrenI:
  "(\<And>i vs. lookup M i = Some (subverts vs) \<Longrightarrow> distinct vs) 
  \<Longrightarrow> distinct_children M"
  unfolding distinct_children_def by blast

lemma distinct_childrenE:
  "\<lbrakk>distinct_children M;
    (\<And>i vs. lookup M i = Some (subverts vs) \<Longrightarrow> distinct vs) \<Longrightarrow> P\<rbrakk> 
  \<Longrightarrow> P"
  unfolding distinct_children_def by blast

lemma distinct_childrenD:
  "\<lbrakk>distinct_children M; lookup M i = Some (subverts vs)\<rbrakk> 
  \<Longrightarrow> distinct vs"
  unfolding distinct_children_def by blast

fun laminar_forest_invar where
 "laminar_forest_invar (tops, M) = 
  (top_invar tops \<and> invar M \<and> top_set tops = max_ids M  \<and> 
   disjoint_subids M \<and> disjoint_trees M \<and> elem_unique_id M
  \<and> wf (laminar_forest_cons M) \<and> finite (dom (lookup M)) \<and>
  branching_properly M \<and> domain_recursive M \<and> distinct_children M)"

lemma laminar_forest_invarI:
  "\<lbrakk>top_invar tops; invar M; max_ids M = top_set tops; 
    disjoint_subids M; disjoint_trees M; elem_unique_id M; 
    wf (laminar_forest_cons M); finite (dom (lookup M));
    branching_properly M; domain_recursive M; distinct_children M \<rbrakk> 
  \<Longrightarrow> laminar_forest_invar (tops, M)"
  by simp

lemma laminar_forest_invarE:
  "\<lbrakk>laminar_forest_invar (tops, M);
    \<lbrakk>top_invar tops; invar M; max_ids M = top_set tops; 
     disjoint_subids M; disjoint_trees M; elem_unique_id M; 
     wf (laminar_forest_cons M); finite (dom (lookup M));
     branching_properly M; domain_recursive M;distinct_children M\<rbrakk> \<Longrightarrow> P\<rbrakk> 
  \<Longrightarrow> P"
  by simp

lemma laminar_forest_invarD:
  "laminar_forest_invar (tops, M) \<Longrightarrow> top_invar tops" 
  "laminar_forest_invar (tops, M) \<Longrightarrow> invar M" 
  "laminar_forest_invar (tops, M) \<Longrightarrow> max_ids M = top_set tops" 
  "laminar_forest_invar (tops, M) \<Longrightarrow> disjoint_subids M" 
  "laminar_forest_invar (tops, M) \<Longrightarrow> disjoint_trees M" 
  "laminar_forest_invar (tops, M) \<Longrightarrow> elem_unique_id M" 
  "laminar_forest_invar (tops, M) \<Longrightarrow> wf (laminar_forest_cons M)"
  "laminar_forest_invar (tops, M) \<Longrightarrow> finite (dom (lookup M))"
  "laminar_forest_invar (tops, M) \<Longrightarrow> branching_properly M"
  "laminar_forest_invar (tops, M) \<Longrightarrow> domain_recursive M"
  "laminar_forest_invar (tops, M) \<Longrightarrow> distinct_children M"
  by simp_all

definition "all_verts M = {v | i v. lookup M i = Some (elem_vert v)}"

subsection \<open>Properties\<close>

lemma in_dom_a_max_id:
  assumes "wf (laminar_forest_cons M)"
          "finite (dom (lookup M))" "x \<in> dom (lookup M)"
    shows "\<exists> i \<in> max_ids M. x \<in> ids_of_sub_laminars M i"
proof-
  define n where 
   "n = card {i | i. x \<in> ids_of_sub_laminars M i}"
  then show ?thesis
    using assms(3)
  proof(induction n arbitrary: x rule: less_induct)
    case (less n)
    have finit4ea:"finite {i |i. x \<in> ids_of_sub_laminars M i}" for x
      by(auto intro!: finite_subset[OF _ assms(2)]
            simp add: ids_of_sub_laminars_simps[OF assms(1)] option.split)
    show ?case 
    proof(cases "x \<in> max_ids M")
      case False
      then obtain x' vs where x': "lookup M x' = Some (subverts vs)" "x \<in> set vs"
        using less.prems(2) by (auto simp add: max_ids_def)
      moreover hence "x \<notin> {i | i. x' \<in> ids_of_sub_laminars M i}"
        using not_in_subtree[OF assms(1)] by auto
      moreover have "x \<in> {i | i. x \<in> ids_of_sub_laminars M i}"
      using less(3) x'
      by(auto simp add: ids_of_sub_laminars_simps[OF assms(1), of x]
                 split: contracted_laminar.split)
    moreover have subst:"{i | i. x \<in> ids_of_sub_laminars M i} 
                           \<supseteq> {i | i. x' \<in> ids_of_sub_laminars M i}"
      using x' ids_mono[OF assms(1)] immediate_childrenin_ids[OF assms(1)] less.prems(2)
      by force
    ultimately have "{i | i. x \<in> ids_of_sub_laminars M i} \<supset> {i | i. x' \<in> ids_of_sub_laminars M i}"
      by auto
    hence card_less: "card {i | i. x' \<in> ids_of_sub_laminars M i} < n"
        using finit4ea ids_mono[OF assms(1)]
        by(auto intro!: psubset_card_mono simp add: less(2))
    obtain i where "i \<in> max_ids M" "x' \<in> ids_of_sub_laminars M i" 
      using less(1)[OF card_less refl] x'(1) by auto
    moreover hence "x \<in> ids_of_sub_laminars M i" 
      using local.subst by auto
    ultimately show ?thesis
      by auto
    next
      case True
      then show ?thesis 
        using less.prems(2) self_in_ids[OF assms(1)]
        by(auto intro!: bexI[of _ x])
    qed
  qed
qed

lemma dom_is_ids_of_sub_laminars_of_max_ids:
  assumes "wf (laminar_forest_cons M)"
          "finite (dom (lookup M))"
    shows "\<Union> (ids_of_sub_laminars M ` (max_ids M)) = dom (lookup M)"
proof(rule, goal_cases)
  case 1
  then show ?case
    using ids_in_dom[OF assms(1)] by auto
next
  case 2
  then show ?case 
    using in_dom_a_max_id[OF assms] by auto
qed

lemma disjoint_elems_if_disjoint_subids_and_elem_unique_id:
  assumes "wf (laminar_forest_cons M)" "elem_unique_id M" "disjoint_subids M"
  shows "disjoint_elem_verts M"                   
proof(rule disjoint_elem_vertsI, rule ccontr, goal_cases)
  case (1 i vs j k)
  then obtain x where x: "x \<in> collect_verts M j" "x \<in> collect_verts M k"
    by auto
  then obtain jx kx where jx_kx:"lookup M jx = Some (elem_vert x)" "jx \<in> ids_of_sub_laminars M j"
           "lookup M kx = Some (elem_vert x)" "kx \<in> ids_of_sub_laminars M k"
    using "1"(1,2,3,4) assms(2,3)
    by(auto simp add: collect_verts_uf' [OF assms(1), of j] collect_verts_uf' [OF assms(1), of k])
  hence "j = k" 
    using "1"(1,2,3) assms(2,3)  disjoint_subidsD elem_unique_idD by blast
  then show ?case 
    using 1 by simp
qed

lemma disjoint_elems_over_trees_if_disjoint_subids_and_elem_unique_id:
  assumes "wf (laminar_forest_cons M)" "elem_unique_id M" "disjoint_trees M"
  shows "disjoint_elems_over_trees M"                   
proof(rule disjoint_elems_over_treesI, rule ccontr, goal_cases)
  case (1 j k)
  then obtain x where x: "x \<in> collect_verts M j" "x \<in> collect_verts M k"
    by auto
  then obtain jx kx where jx_kx:"lookup M jx = Some (elem_vert x)" "jx \<in> ids_of_sub_laminars M j"
           "lookup M kx = Some (elem_vert x)" "kx \<in> ids_of_sub_laminars M k"
    using "1"(1,2,3,4) assms(2,3)
    by(auto simp add: collect_verts_uf' [OF assms(1), of j] collect_verts_uf' [OF assms(1), of k])
  hence "j = k" 
    using "1"(1,2,3) assms(2,3)
    by(auto dest: disjoint_treesD elem_unique_idD)
  then show ?case 
    using 1 by simp
qed

lemma disjoint_elem_verts_prelaminarity:
  assumes "wf (laminar_forest_cons M)" 
    "X = collect_verts M i"  "Y = collect_verts M j" 
    "i \<in> ids_of_sub_laminars M t " "j \<in> ids_of_sub_laminars M t"
    "disjoint_elem_verts M"
  shows "X \<subseteq> Y \<or> Y \<subseteq> X \<or> X \<inter> Y = {}"
  using assms(2-5)
proof(induction rule: ids_of_sub_laminars_induct[OF assms(1)])
  case (1 i)
  note IH = this
  show ?case 
  proof(cases rule: in_ids_of_sub_laminars_cases[OF assms(1) IH(4)], goal_cases)
    case (1 x)
    then show ?case 
      using assms(1,2) IH(3,5)  collect_verts_uf[of M i] by auto
  next
    case (2 vs)
    then show ?case 
      using assms(1,2) IH(3,5)  collect_verts_uf[of M i] by auto
  next
    case (3 vs i')
    then show ?case 
    proof(cases rule: in_ids_of_sub_laminars_cases[OF assms(1) IH(5)], goal_cases)
      case (1 x)
      then show ?case 
        by simp
    next
      case (2 vs')
      then show ?case 
        using assms(1,2,3) IH(4) collect_verts_uf[of M i]
        by auto
    next
      case (3 vs' i'')
      hence vs_eq:"subverts vs = subverts vs'" by auto
      show ?case 
      proof(cases "i' = i''")
        case True
        then show ?thesis 
          using IH(1)[OF 3(1) vs_eq 3(5) IH(2,3) ] 3 by auto
      next
        case False
        hence "X \<inter> Y = {}"
          using disjoint_elem_vertsD[OF assms(6) 3(1,2) _ False] 3  assms(1,2,3) vs_eq 
          by(auto simp add: collect_verts_uf[of M i'] collect_verts_uf[of M i''])
        then show ?thesis 
          by simp
      qed
    qed  
  qed  
qed

lemma disjoint_ids_prelaminarity:
  assumes "wf (laminar_forest_cons M)" 
    "X = ids_of_sub_laminars M i"  "Y = ids_of_sub_laminars M j" 
    "i \<in> ids_of_sub_laminars M t " "j \<in> ids_of_sub_laminars M t"
    "disjoint_subids M"
  shows "X \<subseteq> Y \<or> Y \<subseteq> X \<or> X \<inter> Y = {}"
  using assms(2-5)
proof(induction rule: ids_of_sub_laminars_induct[OF assms(1)])
  case (1 i)
  note IH = this
  show ?case 
  proof(cases rule: in_ids_of_sub_laminars_cases[OF assms(1) IH(4)], goal_cases)
    case (1 x)
    then show ?case 
      using assms(1,2) IH(3,5)
      by (simp add: ids_mono) 
  next
    case (2 vs)
    then show ?case 
      using assms(1,2) IH(3,5)
      by (simp add: ids_mono)
  next
    case (3 vs i')
    then show ?case 
    proof(cases rule: in_ids_of_sub_laminars_cases[OF assms(1) IH(5)], goal_cases)
      case (1 x)
      then show ?case 
        by simp
    next
      case (2 vs')
      then show ?case 
        using assms(1,2,3) IH(4) by (simp add: ids_mono)
    next
      case (3 vs' i'')
      hence vs_eq:"subverts vs = subverts vs'" by auto
      show ?case 
      proof(cases "i' = i''")
        case True
        then show ?thesis 
          using IH(1)[OF 3(1) vs_eq 3(5) IH(2,3) ] 3 by auto
      next
        case False
        hence "X \<inter> Y = {}"
          using disjoint_subidsD[OF assms(6) 3(1,2) _ False] 3  assms(1,2,3) vs_eq 
                Int_mono[of X "ids_of_sub_laminars M i'" Y "ids_of_sub_laminars M i''"] ids_mono
          by auto
        then show ?thesis 
          by simp
      qed
    qed  
  qed  
qed

lemma branching_properly_children_nempty:
  "branching_properly M \<Longrightarrow> children_nempty M"
  by(auto intro!: children_nemptyI dest!: branching_properlyD)

lemma laminar_tree_fold_correct:
  assumes "wf (laminar_forest_cons M)"  "distinct_children M" "disjoint_subids M"
    shows "\<exists> xs. set xs = ids_of_sub_laminars M i \<and> distinct xs 
                \<and> laminar_tree_fold M f acc i = foldl f acc xs"
proof(induction arbitrary: acc rule: ids_of_sub_laminars_induct[OF assms(1)])
  case (1 i)
  note IH = this
  show ?case
  proof(cases "lookup M i")
    case None
    then show ?thesis 
      by(auto simp add: ids_of_sub_laminars_simps[OF assms(1)]
                        laminar_tree_fold_simps[OF assms(1)])
  next
    case (Some a)
    then show ?thesis 
    proof(cases a)
      case (elem_vert x1)
      then show ?thesis
        by(auto intro!: exI[of _ "[i]"]
              simp add: ids_of_sub_laminars_simps[OF assms(1)]
                        laminar_tree_fold_simps[OF assms(1)] Some)
    next
      case (subverts vs)
      note IH = IH[OF Some subverts]
      moreover have "distinct vs" 
        using assms(2) Some by(auto elim!: distinct_childrenE simp add: subverts) 
      moreover have "\<And> v v'. \<lbrakk>v \<in> set vs; v' \<in> set vs; v \<noteq> v'\<rbrakk> 
               \<Longrightarrow> ids_of_sub_laminars M v \<inter> ids_of_sub_laminars M v' = {}"
        using Some assms(3) disjoint_subidsD subverts by blast
      ultimately have "\<exists>xs. set xs = \<Union> (ids_of_sub_laminars M ` set vs) \<and>
         distinct xs \<and> foldl (laminar_tree_fold M f) acc vs = foldl f acc xs" for acc
      proof(induction vs arbitrary: acc)
        case Nil
        then show ?case 
          by (auto intro!: exI[of _ "[i]"])
      next
        case (Cons a vs)
        obtain xs where xs: "set xs = \<Union> (ids_of_sub_laminars M ` set vs)" "distinct xs"
           "foldl (laminar_tree_fold M f) (laminar_tree_fold M f acc a) vs =
                foldl f (laminar_tree_fold M f acc a) xs" 
          using Cons(1)[of "laminar_tree_fold M f acc a", OF Cons(2) _ Cons(4), simplified] Cons(3)
          by auto
        obtain xs' where xs': "set xs' = ids_of_sub_laminars M a" "distinct xs'" 
                "laminar_tree_fold M f acc a = foldl f acc xs'"
          using Cons(2)[of a acc] by auto
        have eq: "foldl (laminar_tree_fold M f) (laminar_tree_fold M f acc a) vs 
                   = foldl f (foldl f acc xs') xs"
          unfolding xs(3) unfolding xs'(3) by simp
        show ?case 
         using Cons.prems(2,3)
         by(auto intro!: exI[of _ "xs'@xs"] simp add: eq xs'(1,2) xs)+
     qed
     then obtain xs where xs: "set xs = \<Union> (ids_of_sub_laminars M ` set vs)"
         "distinct xs" "foldl (laminar_tree_fold M f)  (f acc i) vs = foldl f  (f acc i) xs"
       by blast
     thus ?thesis 
       using not_in_subtree[OF assms(1)]
       by(auto intro!: exI[of _ "i#xs"]
           simp add: ids_of_sub_laminars_simps[OF assms(1), of i] 
             Some laminar_tree_fold_simps[OF assms(1)] subverts)
    qed
  qed
qed

lemma laminar_fold_singletons_correct:
  assumes "wf (laminar_forest_cons M)" "distinct_children M" "disjoint_elem_verts M"
    shows "\<exists> xs. set xs = collect_verts M i \<and> distinct xs 
                \<and> laminar_fold_singletons M f acc i = foldl f acc xs"
proof(induction arbitrary: acc rule: ids_of_sub_laminars_induct[OF assms(1)])
  case (1 i)
  note IH = this
  show ?case
  proof(cases "lookup M i")
    case None
    then show ?thesis 
      by(auto simp add: collect_verts_simps[OF assms(1)]
                        laminar_fold_singletons_simps[OF assms(1)])
  next
    case (Some a)
    then show ?thesis 
    proof(cases a)
      case (elem_vert x)
      then show ?thesis
        by(auto intro!: exI[of _ "[x]"]
              simp add: collect_verts_simps[OF assms(1)]
                        laminar_fold_singletons_simps[OF assms(1)] Some)
    next
      case (subverts vs)
      note IH = IH[OF Some subverts]
      moreover have "distinct vs" 
        using assms(2) Some by(auto elim!: distinct_childrenE simp add: subverts) 
      moreover have "\<And> v v'. \<lbrakk>v \<in> set vs; v' \<in> set vs; v \<noteq> v'\<rbrakk> 
               \<Longrightarrow> collect_verts M v \<inter> collect_verts M v' = {}"
        using Some assms(3) disjoint_elem_vertsD subverts by blast
      ultimately have "\<exists>xs. set xs = \<Union> (collect_verts M ` set vs) \<and>
         distinct xs \<and> foldl (laminar_fold_singletons M f) acc vs = foldl f acc xs" for acc
      proof(induction vs arbitrary: acc)
        case (Cons a vs)
        obtain xs where xs: "set xs = \<Union> (collect_verts M ` set vs)" "distinct xs"
           "foldl (laminar_fold_singletons M f) (laminar_fold_singletons M f acc a) vs =
                foldl f (laminar_fold_singletons M f acc a) xs" 
          using Cons(1)[of "laminar_fold_singletons M f acc a", OF Cons(2) _ Cons(4), simplified] Cons(3)
          by auto
        obtain xs' where xs': "set xs' = collect_verts M a" "distinct xs'" 
                "laminar_fold_singletons M f acc a = foldl f acc xs'"
          using Cons(2)[of a acc] by auto
        have eq: "foldl (laminar_fold_singletons M f) (laminar_fold_singletons M f acc a) vs 
                   = foldl f (foldl f acc xs') xs"
          unfolding xs(3) unfolding xs'(3) by simp
        show ?case 
         using Cons.prems(2,3)
         by(auto intro!: exI[of _ "xs'@xs"] simp add: eq xs'(1,2) xs)+
     qed simp
     thus ?thesis 
       using not_in_subtree[OF assms(1)]
       by(auto simp add: collect_verts_simps[OF assms(1), of i] 
             Some laminar_fold_singletons_simps[OF assms(1)] subverts)
    qed
  qed
qed

lemma collect_verts_nempty:
  assumes "wf (laminar_forest_cons M)" "children_nempty M" "i \<in> dom (lookup M)" "domain_recursive M"
  shows "collect_verts M i \<noteq> {}"
  using assms(3)
proof(induction rule: collect_verts_induct[OF assms(1)])
  case (1 i)
  note IH =this
  show ?case
    unfolding collect_verts_simps[OF assms(1), of i] 
  proof(cases "lookup M i", goal_cases)
    case 1
    then show ?case 
      using IH by auto
  next
    case (2 a)
    then show ?case 
    proof(cases a)
      case (elem_vert x1)
      then show ?thesis 
        using 2 by auto
    next
      case (subverts vs)
      hence "vs \<noteq> []" 
        using assms(2) 2 by(auto elim!: children_nemptyE)
      then obtain x where x: "x \<in> set vs"
        by(cases vs) auto
      have "collect_verts M x \<noteq> {}"
        using assms(4) subverts 2 x
        by(intro IH(1)[OF 2 subverts x])(auto dest!: domain_recursiveD[of _ i vs])
      thus ?thesis
        using 2 subverts x by auto
    qed
  qed
qed

lemma collect_verts_empty:
  assumes "wf (laminar_forest_cons M)"  "i \<notin> dom (lookup M)"
  shows "collect_verts M i = {}"
  using assms
  by(auto simp add: collect_verts_simps)

lemma disjoint_elem_verts_pre_inj_of_collect:
  assumes "wf (laminar_forest_cons M)" 
    "collect_verts M i = collect_verts M j" 
    "i \<in> ids_of_sub_laminars M t " "j \<in> ids_of_sub_laminars M t"
    "disjoint_elem_verts M" "distinct_children M" "branching_properly M"
    "domain_recursive M" "elem_unique_id M"
  shows "i = j"
  using assms(2-4)
proof(induction arbitrary: i j rule: ids_of_sub_laminars_induct[OF assms(1)])
  case (1 t)
  note IH = this
  show ?case 
  proof(cases rule: in_ids_of_sub_laminars_cases[OF assms(1) IH(4)], goal_cases)
    case (1 x)
    then show ?case
      using IH(3) assms(1) ids_of_sub_laminars_simps by auto
  next
    case (2 vs)
      then show ?case 
       proof(cases rule: in_ids_of_sub_laminars_cases[OF assms(1) IH(3)], goal_cases)
         case (3 vs' i')
       then obtain i'' where i''': " i'' \<in> set vs'" "i'' \<noteq> i'"
            using branching_properlyD[OF assms(7), of t vs']
                  distinct_childrenD[OF assms(6), of t vs']
            by(cases vs' rule: list_cases3) auto
          hence "collect_verts M i' \<inter> collect_verts M i'' = {}" 
            using  disjoint_elem_vertsD collect_verts_uf[OF assms(1)]  "3"(3,4) assms(5) by blast
          moreover have "collect_verts M i'' \<noteq> {}" 
            using assms(1,7,8) i'''(1) "3"(3) collect_verts_nempty[of M i'']
            by (auto dest: domain_recursiveD simp add: branching_properly_children_nempty)
          ultimately have "collect_verts M i \<subset> collect_verts M j" 
            using "3"(2,3,5) i''' assms(8) 
              disjoint_iff[of "collect_verts M i''" "collect_verts M i''"]
              disjoint_iff[of "collect_verts M i'" "collect_verts M i''"] IH(2) 
              immediate_childrenin_ids[OF assms(1), of j vs' i'']
            by (force dest!: domain_recursiveD 
                   simp add: collect_verts_uf[OF assms(1), of j]  collect_verts_uf[OF assms(1), of i'])
          then show ?case
            by (simp add: IH(2))
        qed simp+
  next
    case (3 vs i')
    then show ?case 
    proof(cases rule: in_ids_of_sub_laminars_cases[OF assms(1) IH(3)], goal_cases)
      case (2 vs')
           then obtain i'' where i''': " i'' \<in> set vs'" "i'' \<noteq> i'"
            using branching_properlyD[OF assms(7), of t vs']
                  distinct_childrenD[OF assms(6), of t vs']
            by(cases vs' rule: list_cases3) auto
          hence "collect_verts M i' \<inter> collect_verts M i'' = {}"
            using "2"(4) "3"(1,2) assms(5) disjoint_elem_vertsD by auto
          moreover have "collect_verts M i'' \<noteq> {}" 
            using assms(1,7,8) i'''(1) "2"(4) collect_verts_nempty[of M i'']
            by (auto dest: domain_recursiveD simp add: branching_properly_children_nempty)
          ultimately have "collect_verts M i \<subset> collect_verts M j" 
            using assms(1) "2"(4,5) i'''(1) "3"(3)  IH(2)
            by(auto simp add: collect_verts_uf[of M i'] collect_verts_simps[of M i])
          then show ?case
            by (simp add: IH(2))
      then show ?case 
        using assms(1,2,3) IH(4) collect_verts_uf[of M i]
        by auto
    next
      case (3 vs' i'')
      hence vs_eq:"subverts vs = subverts vs'" by auto
      show ?case 
      proof(cases "i' = i''")
        case True
        then show ?thesis
          using "1.IH" "3"(1,2,3,6) IH(2) by blast
      next
        case False
        hence "collect_verts M i' \<inter> collect_verts M i''  = {}" 
          using "3"(1,2,5) assms(5) disjoint_elem_vertsD vs_eq by auto
        moreover have "collect_verts M i \<subseteq> collect_verts M i'"
          using assms(1) "3"(3) IH(2) collect_verts_uf[of M i']
          by blast
        moreover have "collect_verts M j \<subseteq> collect_verts M i''" 
          using assms(1) "3"(6) IH(2) collect_verts_uf[of M i''] by auto
        ultimately have "collect_verts M i \<inter> collect_verts M j  = {}" 
          by auto
        moreover have "collect_verts M i \<noteq> {}"
          using "3"(6) assms(1,7,8) branching_properly_children_nempty collect_verts_nempty ids_in_dom
          by fastforce
        moreover have "collect_verts M j \<noteq> {}"
          using "3"(3) assms(1,7,8) branching_properly_children_nempty collect_verts_nempty ids_in_dom
          by fastforce
        ultimately have "collect_verts M i \<noteq> collect_verts M j"
          by blast
        hence False
          using IH(2) by auto
        thus ?thesis
          by simp
      qed
    qed  
  qed  
qed

lemma psubsetI': "A \<subseteq> B \<Longrightarrow> B \<noteq> A \<Longrightarrow> A \<subset> B"
  unfolding less_le by blast

lemma elem_cong: "x \<in> X \<Longrightarrow> Y = X \<Longrightarrow> x \<in> Y" by auto

lemma strict_subids_immediate_parent:
  assumes "wf (laminar_forest_cons M)" 
    "disjoint_subids M" "i \<in> dom (lookup M)" "ids_of_sub_laminars M i \<subset> ids_of_sub_laminars M j"
  shows "\<exists> i' vs. lookup M i' = Some (subverts vs) \<and> i \<in> set vs"
  using  assms(4)
proof(induction j rule: ids_of_sub_laminars_induct[OF assms(1)], goal_cases)
  case (1 j)
  note IH = this
  show ?case 
  proof(cases "lookup M j")
    case None
    then show ?thesis
      using IH(2) assms(1) 
      by (auto simp add: ids_of_sub_laminars_simps[OF assms(1), of j]) 
  next
    case (Some a)
    then show ?thesis 
    proof(cases a, goal_cases)
      case (1 x)
      then show ?case 
        using IH(2) self_in_ids[OF assms(1)] assms(3)
        by (auto simp add: ids_of_sub_laminars_simps[OF assms(1), of j])
    next
      case (2 vs)
      then show ?case 
      proof(cases "i \<in> set vs")
        case True
        then show ?thesis
          using 2
          by(auto intro!: exI[of _ j] exI[of _ vs] )
      next
        case False
        then obtain j' where j': "ids_of_sub_laminars M i \<subseteq> ids_of_sub_laminars M j'" "j' \<in> set vs"
          using assms(1,3) "2"(2) Some IH(2)
            inf.absorb_iff2[of "ids_of_sub_laminars M i" "ids_of_sub_laminars M j"] 
            self_in_ids[OF assms(1), of i] ids_mono[OF assms(1), of i]
            in_ids_of_sub_laminars_cases[OF assms(1), of i j]
            IntE[of i "ids_of_sub_laminars M j" "ids_of_sub_laminars M i"] 
          by force
        moreover hence "j' \<in> ids_of_sub_laminars M j" 
          using 2(2) Some assms(3) ids_of_sub_laminars_simps[OF assms(1), of j'] 
                self_in_ids[OF assms(1), of i] self_in_ids[OF assms(1), of j'] 
          by(force simp add: ids_of_sub_laminars_simps[OF assms(1), of j]
                      split: option.split contracted_laminar.split)
        moreover have "j' \<notin> ids_of_sub_laminars M i"
          using False calculation(1,2) assms(3) self_in_ids[OF assms(1), of i]
                ids_mono[OF assms(1), of j'] not_in_subtree[OF assms(1), of i]
          by(force elim!: in_ids_of_sub_laminars_cases[OF assms(1), of j' i])
        ultimately have i_in_j':"ids_of_sub_laminars M i \<subset> ids_of_sub_laminars M j'" 
          using assms(1,3) ids_of_sub_laminars_simps[of M j'] self_in_ids[of M i] self_in_ids[of M j']
          by force
        then obtain i' vs where "lookup M i' = Some (subverts vs)" "i \<in> set vs"
          using IH(1)[OF 2 j'(2) i_in_j'] by auto
        then show ?thesis
          by auto
      qed
    qed
  qed
qed
lemma Union_singleton_iff: "\<Union> A = {x} \<longleftrightarrow> A = {{x}} \<or> A = {{x},{}}"
proof(rule, goal_cases)
  case 1
  then show ?case 
    using Union_upper[of _ A] subset_singleton_iff[of _ x]
    by auto
next
  case 2
  then show ?case 
    by (auto dest!:  subset_singletonD) 
qed

lemma two_sets_union_singleton_iff:
  "A \<union> B = {x} \<longleftrightarrow> (A = {x} \<and> B = {} \<or> B = {x} \<and> A = {} \<or> A = {x} \<and> B = {x})"
  by auto

lemma strict_elem_verts_immediate_parent:
  assumes "wf (laminar_forest_cons M)" 
    "disjoint_elem_verts M" "lookup M i = Some (subverts vs)"
    "branching_properly M" "domain_recursive M" "distinct_children M"
  shows "\<nexists> x. collect_verts M i = {x}"
  using assms(3)
proof(induction i rule: ids_of_sub_laminars_induct[OF assms(1)], goal_cases)
  case (1 i)
  note IH = this
  thm collect_verts_nempty[OF assms(1) children_nemptyI _ assms(5)]
  have vs_nempty:"vs \<noteq> []" 
    using IH(2) assms(4) branching_properly_children_nempty children_nemptyD by blast
  obtain x y xs where vs_split:"vs = x#y#xs" 
    using assms(4) IH(2) by(cases vs rule: list_cases3)(auto dest!: branching_properlyD)
  have y_empty_False:"collect_verts M y = {} \<Longrightarrow> False"
   and x_empty_False: "collect_verts M x = {} \<Longrightarrow> False" 
    using assms(1,3) branching_properly_children_nempty[OF assms(4)] 
          collect_verts_nempty[OF assms(1) _ _ assms(5), of i] IH(1)
    by(auto simp add: vs_split assms(5) collect_verts_nempty domIff domain_recursiveD)
  have x_y_same_elem_False: "\<lbrakk>collect_verts M x = {xa}; collect_verts M y = {xa}\<rbrakk> \<Longrightarrow> False" for xa
    using disjoint_elem_vertsD[OF assms(2) IH(2), of x y] assms(3,6)
    by(auto dest: distinct_childrenD simp add: vs_split)
  show ?case
    by (auto dest: y_empty_False x_empty_False x_y_same_elem_False
         simp add: two_sets_union_singleton_iff vs_split  collect_verts_simps[OF assms(1), of i] IH(2))
qed   
(*
lemma strict_elem_verts_immediate_parent:
  assumes "wf (laminar_forest_cons M)" 
    "disjoint_subids M" "i \<in> dom (lookup M)" "collect_verts M i \<subset> collect_verts M j"
    "branching_properly M" "domain_recursive M" "distinct_children M"
    "disjoint_elem_verts M"
  shows "\<exists> i' vs. lookup M i' = Some (subverts vs) \<and> i \<in> set vs"
  using  assms(4)
proof(induction j rule: ids_of_sub_laminars_induct[OF assms(1)], goal_cases)
  case (1 j)
  note IH = this
  show ?case 
  proof(cases "lookup M j")
    case None
    then show ?thesis
      using IH(2) assms(1) 
      by (auto simp add: collect_verts_simps[OF assms(1), of j]) 
  next
    case (Some a)
    then show ?thesis 
    proof(cases a, goal_cases)
      case (1 x)
      then show ?case
        using IH(2)  assms(1,3,5,6)
             collect_verts_nempty[of M i] branching_properly_children_nempty[of M]
       by (auto simp add: collect_verts_simps[OF assms(1), of j]
                         collect_verts_simps[OF assms(1), of i] contracted_laminar.split)
    next
      case (2 vs)
      then show ?case 
      proof(cases "i \<in> set vs")
        case True
        then show ?thesis
          using 2
          by(auto intro!: exI[of _ j] exI[of _ vs] )
      next
        case False
        note one = 1
        have lookup_Mi: "lookup M j = Some (subverts vs)"
          by (simp add: "2"(2) Some)
        have "collect_verts M i \<noteq> {}"
          by (simp add: assms(1,3,5,6) branching_properly_children_nempty collect_verts_nempty)
        then obtain j' where j': "collect_verts M i \<inter> collect_verts M j' \<noteq> {}" "j' \<in> set vs"
          using 1(2) by(auto simp add: collect_verts_simps[OF assms(1), of j] Some 2)
        have "collect_verts M i \<subseteq> collect_verts M j'" 
        proof(rule ccontr, goal_cases)
          case 1
          then obtain j'' where j'': "collect_verts M i \<inter> collect_verts M j'' \<noteq> {}"
                    "j'' \<in> set vs" "j'' \<noteq> j'"
          using one(2) by(auto simp add: collect_verts_simps[OF assms(1), of j] Some 2)
          then show ?case sorry
        qed
          using 1(2) apply(auto simp add: collect_verts_simps[OF assms(1), of j] Some 2)
          subgoal for x xa xb xc
          using branching_properlyD[OF assms(5) lookup_Mi]
                disjoint_elem_vertsD[OF assms(8) lookup_Mi, of j' xa] 
                distinct_childrenD[OF assms(7) lookup_Mi]
       then obtain j' where j': "ids_of_sub_laminars M i \<subseteq> ids_of_sub_laminars M j'" "j' \<in> set vs"
        
        then obtain j' where j': "ids_of_sub_laminars M i \<subseteq> ids_of_sub_laminars M j'" "j' \<in> set vs"
          using IH(2)
          using assms(1,3) "2"(2) Some IH(2)
            inf.absorb_iff2[of "ids_of_sub_laminars M i" "ids_of_sub_laminars M j"] 
            self_in_ids[OF assms(1), of i] ids_mono[OF assms(1), of i]
            in_ids_of_sub_laminars_cases[OF assms(1), of i j]
            IntE[of i "ids_of_sub_laminars M j" "ids_of_sub_laminars M i"] 
          apply auto
           apply (metis in_mono) 
          
        moreover hence "j' \<in> ids_of_sub_laminars M j" 
          using 2(2) Some assms(3) ids_of_sub_laminars_simps[OF assms(1), of j'] 
                self_in_ids[OF assms(1), of i] self_in_ids[OF assms(1), of j'] 
          by(fo rce simp add: ids_of_sub_laminars_simps[OF assms(1), of j]
                      split: option.split contracted_laminar.split)
        moreover have "j' \<notin> ids_of_sub_laminars M i"
          using False calculation(1,2) assms(3) self_in_ids[OF assms(1), of i]
                ids_mono[OF assms(1), of j'] not_in_subtree[OF assms(1), of i]
          by(force elim!: in_ids_of_sub_laminars_cases[OF assms(1), of j' i])
        ultimately have i_in_j':"ids_of_sub_laminars M i \<subset> ids_of_sub_laminars M j'" 
          using assms(1,3) ids_of_sub_laminars_simps[of M j'] self_in_ids[of M i] self_in_ids[of M j']
          by force
        then obtain i' vs where "lookup M i' = Some (subverts vs)" "i \<in> set vs"
          using IH(1)[OF 2 j'(2) i_in_j'] by auto
        then show ?thesis
          by auto
      qed
    qed
  qed
qed
*)
lemma collect_eq_dest:"Collect P = Collect Q \<Longrightarrow> (\<And> x. P x \<longleftrightarrow> Q x)"
  by auto

lemma finite_image_subst:
 "\<lbrakk>finite A; B = f ` A\<rbrakk> \<Longrightarrow> finite B"
  by auto

lemma finite_all_verts_dom:
  "finite (dom (lookup M)) \<Longrightarrow> finite (all_verts M)"
  by(auto intro!: finite_image_subst[of " {i | i v. lookup M i = Some (elem_vert v)}" _ 
                     "\<lambda> i. the_vert (the (lookup M i))"] 
                  finite_subset[of _ "dom (lookup M)"] rev_image_eqI
        simp add: all_verts_def)

lemma ids_of_sub_laminars_dom_collect_verts_dom:
  assumes "ids_of_sub_laminars_dom M i"
  shows "collect_verts_dom M i"
  by(induction rule: ids_of_sub_laminars.pinduct[OF assms(1)]) (simp add: collect_verts_rel_def)

lemma collect_verts_dom_ids_of_sub_laminars_dom:
  assumes "collect_verts_dom M i"
  shows "ids_of_sub_laminars_dom M i"
  by(induction rule: collect_verts.pinduct[OF assms(1)]) (simp add: collect_verts_rel_def)

lemma ids_of_sub_laminars_collect_verts_dom_same:
  "ids_of_sub_laminars_dom M i \<longleftrightarrow> collect_verts_dom M i"
  "ids_of_sub_laminars_dom = collect_verts_dom"
  by (simp add: collect_verts_rel_def)+

lemma  all_sub_laminars_in_dom:
  assumes "ids_of_sub_laminars_dom M i" "j \<in> ids_of_sub_laminars M i"
  shows "ids_of_sub_laminars_dom M j"
  using assms(2)
proof(induction rule: ids_of_sub_laminars.pinduct[OF assms(1)])
  case (1 i)
  show ?case
    using 1(1,3)
  proof(cases "lookup M i", goal_cases)
    case 1
    then show ?case 
      by (simp add: ids_of_sub_laminars.psimps)
  next
    case (2 a)
    then show ?case 
    proof(cases a, goal_cases)
      case (1 x)
      then show ?case 
        by (simp add: ids_of_sub_laminars.psimps)
    next
      case (2 vs)
      then show ?case 
       by(auto intro:  1(2)[simplified] simp add: ids_of_sub_laminars.psimps[OF 1(1)])
   qed
 qed
qed

lemma dom_child:
  assumes "ids_of_sub_laminars_dom M i" "lookup M i = Some (subverts vs)" "j \<in> set vs"
  shows "ids_of_sub_laminars_dom M j"
  using accp_downward assms(1,2,3) laminar_forest_rel_def by fastforce


lemma dom_cong:
  assumes "ids_of_sub_laminars_dom M i"
          "\<And> j. j \<in> ids_of_sub_laminars M i \<union> {i} \<Longrightarrow> lookup M' j = lookup M j"
          "domain_recursive M"
        shows   "ids_of_sub_laminars_dom M' i"
  using assms(2)
proof(induction rule: ids_of_sub_laminars.pinduct[OF assms(1)], goal_cases)
  case (1 i)
  note IH = this
  show ?case 
  proof(intro ids_of_sub_laminars.domintros[of _ i], goal_cases)
    case (1 y x2a)
    note one = this
    show ?case 
    proof(rule IH(2)[of "subverts x2a" x2a], goal_cases)
      case 1
      then show ?case 
        using one IH(3)[of i, simplified] by simp
    next
      case 2
      then show ?case 
        using one by simp
    next
      case 3
      then show ?case 
        using one by simp
    next
      case (4 j)
      then show ?case 
      proof(intro IH(3), rule UnE, goal_cases)
        case 1
        then show ?case 
          using one  IH(3)[of i, simplified]
          by(auto simp add: ids_of_sub_laminars.psimps[OF IH(1)]
                            option.split contracted_laminar.split)

      next
        case 2
        then show ?case 
          unfolding ids_of_sub_laminars.psimps[OF IH(1)]
          using one IH(1,3)  assms(3) domain_recursiveD
          by(auto intro!: bexI[of _ j] self_in_ids' dom_child[simplified, of M i x2a y])
      qed
    qed
  qed
qed

lemma same_ids_same:
  assumes "ids_of_sub_laminars_dom M i"
    "\<And> j. j \<in> ids_of_sub_laminars M i \<union> {i} \<Longrightarrow> lookup M' j = lookup M j"
    "domain_recursive M"
  shows "\<And> j. j \<in> ids_of_sub_laminars M i \<Longrightarrow> ids_of_sub_laminars M' j = ids_of_sub_laminars M j"
    "\<And> j. j \<in> ids_of_sub_laminars M i \<Longrightarrow> collect_verts M' j = collect_verts M j"
proof-
  have "(\<forall> j \<in> ids_of_sub_laminars M i.
           ids_of_sub_laminars M' j = ids_of_sub_laminars M j \<and>
          collect_verts M' j = collect_verts M j)"
    using assms(2)
  proof(induction rule: ids_of_sub_laminars.pinduct[OF assms(1)], goal_cases)
    case (1 i) 
    note one = this
    note IH' = spec[OF 1(2)[simplified Ball_def]]
    note IH =  conjunct1[OF mp[OF IH']] conjunct2[OF mp[OF IH']]

    show ?case 
      using 1(1,3)
    proof(cases "lookup M i", goal_cases)
      case 1
      then show ?case 
        by(fastforce intro: ids_of_sub_laminars.domintros 
            simp add: ids_of_sub_laminars.psimps)
    next
      case (2 a)
      then show ?case 
      proof(cases a, goal_cases)
        case (1 x)
        then show ?case 
          using ids_of_sub_laminars.domintros collect_verts.domintros collect_verts.psimps 
            ids_of_sub_laminars.psimps 
          by force
      next
        case (2 vs)
        note two = this
        have in_vs_sames:"v \<in> set vs \<Longrightarrow> ids_of_sub_laminars M' v = ids_of_sub_laminars M v" for v
          using 2(3,4)
        proof(intro IH(1)[of a vs v], goal_cases)
          case (4 j)
          then show ?case 
            using assms(3) two(1)
              domain_recursiveE[of M] UN_I[of j "set vs" j "ids_of_sub_laminars M"]
              ids_of_sub_laminars.psimps[of M i] self_in_ids'[of M j] dom_child[of M i vs j]
            by (intro two(2)) auto
        next
          case 5
          thus ?case
            using assms(3) dom_child  self_in_ids' two(1)
            by(auto elim!: domain_recursiveE)
        qed simp+
        have in_vs_sames':"v \<in> set vs \<Longrightarrow> collect_verts M' v = collect_verts M v" for v
          using 2(3,4)
        proof(intro IH(2)[of a vs v], goal_cases)
          case (4 j)
          then show ?case 
            using assms(3) two(1)
              domain_recursiveE[of M] UN_I[of j "set vs" j "ids_of_sub_laminars M"]
              ids_of_sub_laminars.psimps[of M i] self_in_ids'[of M j] dom_child[of M i vs j]
            by (intro two(2)) auto
        next
          case 5
          thus ?case
            using assms(3) dom_child  self_in_ids' two(1)
            by(auto elim!: domain_recursiveE)
        qed simp+
        show ?case 
        proof(rule, rule, goal_cases)
          case (1 j)
          from 1 show ?case
            unfolding ids_of_sub_laminars.psimps[OF one(1)] two(3,4) 
              option.case contracted_laminar.case
          proof(elim UnE, goal_cases)
            case 1
            hence j_is_i:"j = i"
              by auto
            have same_lookup: "lookup M' i = lookup M i" 
              using two(2) by auto
            show ?case
              unfolding j_is_i
                ids_of_sub_laminars.psimps[OF one(1)] 
                ids_of_sub_laminars.psimps[OF dom_cong[OF one(1,3) assms(3)], simplified] 
                two(3,4) option.case contracted_laminar.case same_lookup
              using in_vs_sames by auto
          next
            case 2
            then obtain v where v: "v \<in> set vs" "j \<in> ids_of_sub_laminars M v" by auto
            show ?case 
              using assms(3) v(1) two(1,3,4) domain_recursiveE[of M] self_in_ids'[of M v] 
                dom_child[of M i vs v] ids_of_sub_laminars.psimps[of  M i]
              by (intro IH(1)[OF two(3,4) v(1) _ v(2)] two(2))auto
          qed
        next
          case (2 j)
          from 2 show ?case
            unfolding ids_of_sub_laminars.psimps[OF one(1)] two(3,4) 
              option.case contracted_laminar.case
          proof(elim UnE, goal_cases)
            case 1
            hence j_is_i:"j = i"
              by auto
            have same_lookup: "lookup M' i = lookup M i" 
              using two(2) by auto
            show ?case
              unfolding j_is_i
                collect_verts.psimps[OF one(1)[simplified ids_of_sub_laminars_collect_verts_dom_same]] 
                collect_verts.psimps[OF dom_cong[OF one(1,3) assms(3),
                    simplified ids_of_sub_laminars_collect_verts_dom_same], simplified] 
                two(3,4) option.case contracted_laminar.case same_lookup
              using in_vs_sames' by auto
          next
            case 2
            then obtain v where v: "v \<in> set vs" "j \<in> ids_of_sub_laminars M v" by auto
            show ?case 
              using assms(3) v(1) two(1,3,4) domain_recursiveE[of M] self_in_ids'[of M v] 
                dom_child[of M i vs v] collect_verts.psimps[of  M i]
                ids_of_sub_laminars_collect_verts_dom_same
              by (intro IH(2)[OF two(3,4) v(1) _ v(2)] two(2)) 
                (auto simp add: ids_of_sub_laminars.psimps[OF one(1)])
          qed
        qed
      qed
    qed
  qed
  thus "\<And> j. j \<in> ids_of_sub_laminars M i \<Longrightarrow> ids_of_sub_laminars M' j = ids_of_sub_laminars M j"
    "\<And> j. j \<in> ids_of_sub_laminars M i \<Longrightarrow> collect_verts M' j = collect_verts M j"
    by auto
qed

lemma important_properties:
  assumes "laminar_forest_invar (tops, M)"
  shows  "inj_on (collect_verts M) (dom (lookup M))" (is ?th1)
  and "laminar (all_verts M) ({collect_verts M i| i. i \<in> dom (lookup M)})" (is ?th2)
  and "bij_betw (collect_verts M) (dom (lookup M)) {collect_verts M i| i. i \<in> dom (lookup M)}" (is ?th3)
  and "card (dom (lookup M)) \<le> 2 * card (all_verts M) - 1" (is ?th4)
  and "max_ids M = {i | i. i \<in> dom (lookup M) \<and>
          collect_verts M i \<in> maximal_sets {collect_verts M i| i. i \<in> dom (lookup M)}}" (is ?th5)
  and "\<And> i vs. lookup M i = Some (subverts vs) \<Longrightarrow> card (collect_verts M i) > 1" 
             (is "\<And> i vs. ?asm i vs \<Longrightarrow> ?th6 i")
proof-
  note laminar_forest_invarD = laminar_forest_invarD[OF assms]
  note disjointness_over_verts = 
        disjoint_elems_over_trees_if_disjoint_subids_and_elem_unique_id 
          [OF laminar_forest_invarD(7,6,5)]
        disjoint_elems_if_disjoint_subids_and_elem_unique_id
          [OF laminar_forest_invarD(7,6,4)]
show th2: ?th2
proof(rule laminarI, goal_cases)
  case (1 X Y)
  then obtain i j where ij: "i \<in> dom (lookup M)" "X = collect_verts M i"
                        "j \<in> dom (lookup M)" "Y = collect_verts M j"
    by auto
  then obtain i' j' where i'j':"i' \<in> max_ids M" "i \<in> ids_of_sub_laminars M i'"
       "j' \<in> max_ids M" "j \<in> ids_of_sub_laminars M j'"
    by (meson assms laminar_forest_invar.simps in_dom_a_max_id)
  show ?case 
  proof(rule ccontr, goal_cases)
    case 1
    hence props: "\<not> X \<subseteq> Y" "\<not> Y \<subseteq> X" "X \<inter> Y \<noteq> {}"
      by auto
    hence "i' = j'"
      using ij(2,4) i'j' disjoint_elems_over_treesD[OF disjointness_over_verts(1) i'j'(1,3)] 
      by(auto simp add: collect_verts_uf[OF laminar_forest_invarD(7), of i'] 
                        collect_verts_uf[OF laminar_forest_invarD(7), of j'])
    hence "X \<subseteq> Y \<or> Y \<subseteq> X \<or> X \<inter> Y = {}"
      using i'j'(2,4) disjointness_over_verts(2)
      by(intro disjoint_elem_verts_prelaminarity[of M _ i _ j j'] laminar_forest_invarD(7) ij(2,4))
     simp+
    thus False 
      using props by simp
  qed
next
  case (2 X)
  then obtain i where i: "i \<in> dom (lookup M)" "X = collect_verts M i"
    by auto
  thus ?case
    using all_verts_def laminar_forest_invarD(10,7,9) collect_verts_nempty collect_verts_uf'
    by (auto simp add: branching_properly_children_nempty)
qed
  show th1: ?th1
  proof (rule inj_onI, rule ccontr, goal_cases)
    case (1 i j)
    note one = this
    then obtain i' j' where i'j': "i' \<in> max_ids M" "i \<in> ids_of_sub_laminars M i'"
       "j' \<in> max_ids M" "j \<in> ids_of_sub_laminars M j'"
      by (meson assms laminar_forest_invar.simps in_dom_a_max_id)
    hence "(ids_of_sub_laminars M i' \<inter> ids_of_sub_laminars M j' = {} \<and> i' \<noteq> j') \<or> i' = j'"
      using laminar_forest_invarD(5) disjoint_treesD by force
    thus ?case
    proof(elim disjE,goal_cases)
      case 1
      hence "collect_verts M j' \<inter> collect_verts M i' = {}"
        using disjoint_elems_over_treesD[OF disjointness_over_verts(1) i'j'(1,3)] by auto
      moreover have "collect_verts M i \<subseteq> collect_verts M i'" 
        using i'j'(2)  collect_verts_uf[OF laminar_forest_invarD(7)] by fast
      moreover have "collect_verts M j \<subseteq> collect_verts M j'" 
        using i'j'(4)  collect_verts_uf[OF laminar_forest_invarD(7)] by fast
      moreover have "collect_verts M j' \<inter> collect_verts M i' \<noteq>{}"
        using laminar_forest_invarD(10,7,9) calculation(2,3) collect_verts_nempty one(1,3)
              branching_properly_children_nempty
        by fastforce
      ultimately show False
        by simp
    next
      case 2
      thus False
        using laminar_forest_invarD(10,11,6,7,9) disjoint_elem_verts_pre_inj_of_collect
          disjointness_over_verts(2) i'j'(2,4) one(3,4) by blast
    qed
  qed
  show ?th3
  proof(rule bij_betw_imageI, goal_cases)
    case 1
    then show ?case
      using th1 by simp
  next
    case 2
    then show ?case 
      by blast
  qed
  thus th4: ?th4
    by(auto intro!: laminar_family_number_of_sets[simplified] finite_all_verts_dom
          simp add: bij_betw_same_card th2 laminar_forest_invarD(8))
  show th5: ?th5
  proof(rule, all \<open>rule\<close>, goal_cases)
    case (1 i)
    note one = this
    hence i_props:"lookup M i \<noteq> None"
           "(\<nexists> i' vs. lookup M i' = Some (subverts vs) \<and> i \<in> set vs)" 
      by(auto simp add: max_ids_def)
    have "collect_verts M i \<in> maximal_sets {collect_verts M i |i. i \<in> dom (lookup M)}"
    proof(rule in_maximal_setsI, goal_cases)
      case 1
      then show ?case 
        using i_props(1) by auto
    next
      case 2
      then show ?case 
      proof(rule ccontr, goal_cases)
        case 1
        then obtain i' where i': "i' \<in> dom (lookup M)" "collect_verts M i \<subset> collect_verts M i'" 
          by auto
        then obtain vs where "lookup M i' = Some (subverts vs)"
        proof(cases "lookup M i'", goal_cases)
          case 1
          then show ?thesis 
            by auto
        next
          case (2 a)
          then show ?thesis 
            using i_props(1) laminar_forest_invarD(10,7,9)
              all_not_in_conv[of "collect_verts M i"] domIff[of i "lookup M"]
              collect_verts_nempty[of M i]
              branching_properly_children_nempty[of M] in_mono[of "collect_verts M i" "collect_verts M i'"]
            by (cases a)(auto simp add: collect_verts_simps[of M i'])
        qed
        moreover then obtain k where k: "k\<in>max_ids M" "i' \<in> ids_of_sub_laminars M k"
          using in_dom_a_max_id laminar_forest_invarD(7,8) by auto
        moreover hence "ids_of_sub_laminars M i \<inter> ids_of_sub_laminars M k = {}" 
          using  laminar_forest_invarD(7) i'(2)
          by (intro disjoint_treesD[OF laminar_forest_invarD(5)])
             (auto simp add: one  collect_verts_uf[of _ i]) 
        moreover have "collect_verts M i \<inter> collect_verts M k = {}"
          using laminar_forest_invarD(7) i'(2) one k
          by (intro disjoint_elems_over_treesD[OF disjointness_over_verts(1)])
             (auto simp add: one  collect_verts_uf[of _ i]) 
        moreover have "collect_verts M i \<noteq> {}"
          by (simp add: branching_properly_children_nempty collect_verts_nempty domIff i_props(1)
              laminar_forest_invarD(10,7,9))
        ultimately obtain i'' vs' where "lookup M i'' = Some (subverts vs')" "i \<in> set vs'"
          using i'(2) by(force simp add: collect_verts_uf[OF laminar_forest_invarD(7), of k])
        then show ?case 
          using i_props by simp
      qed
    qed
    then show ?case
      using i_props(1) by blast
  next
    case (2 i)
    note two = this
    hence i_props: "i \<in> dom (lookup M)"
          "\<And> j. j \<in> dom (lookup M) \<Longrightarrow> \<not> collect_verts M j \<supset> collect_verts M i"
      by(auto simp add: maximal_sets_def)
    show ?case 
    proof(rule ccontr, goal_cases)
      case 1
      then obtain i' vs where i': "lookup M i' = Some (subverts vs)" "i \<in> set vs" 
        using i_props(1) by (auto simp add: max_ids_def)
      then obtain j where j:"j \<in> set vs" "j \<noteq> i" 
        using laminar_forest_invarD(11,9)
        by(cases vs rule: list_cases3)
          (fastforce elim!: distinct_childrenE branching_properlyE)+
      have "collect_verts M j \<subseteq> collect_verts M i'" "collect_verts M i \<subseteq> collect_verts M i'"
        using laminar_forest_invarD(10,7) i' j(1) immediate_childrenin_ids
        by(force elim!: domain_recursiveE simp add: collect_verts_uf[of M i'])+
      moreover have "collect_verts M j \<inter> collect_verts M i = {}"
        using disjoint_elem_verts_def disjointness_over_verts(2) i'(1,2) j(1,2) by blast
      moreover have "collect_verts M j \<noteq> {}"  "collect_verts M i' \<noteq> {}"
        using  i'(1)  j(1) laminar_forest_invarD(10,7,9)
        by(auto elim!:  domain_recursiveE 
             simp add: laminar_forest_invarD(10)  branching_properly_children_nempty 
                       collect_verts_nempty domIff domain_recursiveD)
      ultimately have "collect_verts M i \<subset> collect_verts M i'"
        by auto
      then show ?case 
        using i_props i'(1) by auto
    qed
  qed
  show "\<And> i vs. ?asm i vs \<Longrightarrow> ?th6 i"
  proof(goal_cases)
    case (1 i vs)
    then obtain v1 v2 vs' where vs_split: "vs = v1#v2#vs'"
      using  laminar_forest_invarD(9)
      by(cases vs rule: list_cases3)(auto dest: branching_properlyD)
    have h1:"collect_verts M i \<supseteq> collect_verts M v1" 
          "collect_verts M i \<supseteq> collect_verts M v2" 
      by (auto simp add: "1" collect_verts_simps laminar_forest_invarD(7) vs_split)
    moreover have h2:"collect_verts M v1 \<inter> collect_verts M v2 = {}" 
      using laminar_forest_invarD(11) disjointness_over_verts(2) 1
      by(fastforce elim!: distinct_childrenD disjoint_elem_vertsE distinct_childrenE 
             simp add: vs_split) 
    moreover have h3:"finite (collect_verts M i)"
      using disjointness_over_verts(2) 
          laminar_forest_invarD(11,7)
      by(auto dest!: laminar_fold_singletons_correct[of M i undefined undefined] sym[of "set _"]) 
    ultimately have "card (collect_verts M i)
                \<ge> card (collect_verts M v1) + card (collect_verts M v2)"
      using 
        card_Un_disjoint[of "collect_verts M v1" "collect_verts M v2"]
        card_mono[of "collect_verts M i" "collect_verts M v1 \<union> collect_verts M v2"]
        finite_subset[of "collect_verts M v1" "collect_verts M i"]
        finite_subset[of "collect_verts M v2" "collect_verts M i"]
      by auto
    moreover have "card (collect_verts M v1) \<ge> 1" 
    proof-
      have "collect_verts M v1 \<noteq> {}"
        using laminar_forest_invarD(10,7,9) 1
        by(intro collect_verts_nempty[of M v1])
          (auto elim!: domain_recursiveE simp add: branching_properly_children_nempty vs_split)
      thus ?thesis
      using h1(1) h3 rev_finite_subset by(auto simp add: card_geq_1_iff)
  qed
    moreover have "card (collect_verts M v2) \<ge> 1" 
    proof-
      have "collect_verts M v2 \<noteq> {}"
        using laminar_forest_invarD(10,7,9) 1
        by(intro collect_verts_nempty[of M v2])
          (auto elim!: domain_recursiveE simp add: branching_properly_children_nempty vs_split)
      thus ?thesis
      using h1(2) h3 rev_finite_subset by(auto simp add: card_geq_1_iff)
  qed
  ultimately show ?case
    by linarith
qed
qed

interpretation laminar_family_spec_statisfied: laminar_family_spec
  where all_ids = "\<lambda> (maxes, L). dom (lookup L)"
  and universe =  "\<lambda> (maxes, L). all_verts L"
  and collect_elems = "\<lambda> (maxes, L). collect_verts L"
  and max_ids = "\<lambda> (maxes, L). max_ids L"
  and laminar_invar = laminar_forest_invar
  and laminar_abstract = "\<lambda> (maxes, L). {collect_verts L i | i. i \<in> dom (lookup L)}"
  and compound = compound
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

lemma image_cong:
  "(\<And> x. x \<in> X \<Longrightarrow> f x = g x) \<Longrightarrow> f ` X = g ` X"
  by auto

lemma wf_fan:
   "x \<notin> X \<Longrightarrow> wf {(y, x) | y. y \<in> X}"
   "x \<notin> X \<Longrightarrow> wf {(x, y) | y. y \<in> X}"
  by(auto simp add: wf_def) metis

lemma merge_props:
  assumes "laminar_family_spec_statisfied.laminar_merge_precond (maxids, L) ids new_id"
  shows "laminar_forest_invar (merge (maxids, L) ids new_id)" (is ?th1)
   and  "dom (lookup (update new_id (subverts ids) L)) = insert new_id (dom (lookup L))" (is ?th2)
   and "{v | i v. lookup (update new_id (subverts ids) L) i = Some (elem_vert v)} = 
        {v | i v. lookup L i = Some (elem_vert v)}" (is ?th3)
   and "collect_verts (update new_id (subverts ids) L) = 
       (\<lambda> x. if x = new_id then \<Union> (collect_verts L ` set ids)
             else collect_verts L x)" (is ?th4)
   and "max_ids (update new_id (subverts ids) L) = 
       max_ids L - set ids \<union> {new_id}" (is ?th5)
   and "{collect_verts (update new_id (subverts ids) L) i |
               i. i \<in> dom (lookup (update new_id (subverts ids) L))} = 
        insert (\<Union> (collect_verts L ` set ids)) {collect_verts L i |i. i \<in> dom (lookup L)}" (is ?th6)
proof-
  note laminar_merge_precondD =
   laminar_family_spec_statisfied.laminar_merge_precondD[OF assms(1), simplified prod.case]
  note laminar_forest_invarD = laminar_forest_invarD[OF laminar_merge_precondD(1)]
  define rev_ids where "rev_ids = rev ids"
  have rev_ids_def: "rev ids = rev_ids" "set ids = set rev_ids"
    by(auto simp add: rev_ids_def)
  have new_L_props:"top_invar (foldl (\<lambda>S x. top_delete x S) maxids ids) \<and>
        top_set (foldl (\<lambda>S x. top_delete x S) maxids ids) = top_set maxids - set ids"
    using laminar_forest_invarD(1)
    unfolding foldl_conv_foldr rev_ids_def
    by(induction rev_ids)
      (auto simp add: top_set.invar_delete top_set.set_delete)
  show new_max_ids_are: ?th5
  proof(rule, all \<open>rule\<close>, goal_cases)
    case (1 i)
    hence i_props:"lookup (update new_id (subverts ids) L) i \<noteq> None"
          "\<nexists>i' vs. lookup (update new_id (subverts ids) L) i' = Some (subverts vs) \<and> i \<in> set vs"
      by(auto simp add: max_ids_def)
    show ?case 
      using i_props
      unfolding map.map_update[OF laminar_forest_invarD(2)]
    proof(cases "i = new_id", goal_cases)
      case 1
      then show ?thesis 
        by simp
    next
      case 2
      hence two: "\<exists>y. lookup L i = Some y"
       "\<And> vs. i \<notin> set ids"
       "\<And> i' vs. \<lbrakk>i' \<noteq> new_id; lookup L i' = Some (subverts vs)\<rbrakk> \<Longrightarrow>  i \<notin> set vs"
       "i \<noteq> new_id" 
        by fastforce+
      have "i \<in> max_ids L"
      proof(rule in_maxidsI, goal_cases)
        case 1
        then show ?case 
          by (simp add: two(1))
      next
        case (2 i' vs)
        then show ?case 
          using laminar_merge_precondD(5) two(3) by force
      qed
      moreover have "i \<notin> set ids" 
        using two(2) by auto
      ultimately show ?thesis 
        by simp
    qed
  next
    case (2 i)
    then show ?case 
    proof(rule UnE, goal_cases)
      case 1
      then show ?case 
        by(auto intro!: in_maxidsI
              simp add: laminar_forest_invarD(2) map.map_update max_ids_def)
    next
      case 2
      then show ?case 
        using laminar_forest_invarD(10) laminar_merge_precondD(2,5)
        by(auto intro!: in_maxidsI 
              simp add: laminar_forest_invarD(2) map.map_update if_split[of "\<lambda> x. x = Some _"] 
                        domain_recursiveD  max_ids_def)
    qed
  qed

  have laminar_forest_cons_after_is:
       "(laminar_forest_cons (update new_id (subverts ids) L)) = 
        (laminar_forest_cons L) \<union> { (j, new_id) | j. j \<in> set ids}"
    using laminar_merge_precondD(5) 
    by(auto simp add: laminar_forest_cons_def laminar_forest_invarD(2) map.map_update)

  have wf_after: 
   "wf (laminar_forest_cons (update new_id (subverts ids) L))"
    unfolding laminar_forest_cons_after_is
  proof(rule wf_Un, goal_cases)
    case 1
    then show ?case
      by (simp add: laminar_forest_invarD(7))
  next
    case 2
    then show ?case
      using laminar_merge_precondD(2,5)
      by (auto intro!: wf_fan simp add: max_ids_def)
  next
    case 3
    then show ?case
      using  laminar_forest_invarD(10) laminar_merge_precondD(5)
      by (auto elim!: domain_recursiveE simp add: laminar_forest_cons_def' laminar_forest_rel_def)
  qed

  have same_sub_laminars:
  "j \<noteq> new_id \<Longrightarrow> ids_of_sub_laminars (update new_id (subverts ids) L) j = 
           ids_of_sub_laminars L j" for j
  proof(cases "lookup L j", goal_cases)
    case 1
    hence same_lookup:"lookup (update new_id (subverts ids) L) j= lookup L j" 
      by (simp add: laminar_forest_invarD(2) map.map_update)
    moreover have "ids_of_sub_laminars L j = {}"
      by (simp add: "1"(2) ids_of_sub_laminars_simps laminar_forest_invarD(7))
    moreover have "ids_of_sub_laminars (update new_id (subverts ids) L) j = {}" 
      by (simp add: "1"(2) ids_of_sub_laminars_simps same_lookup wf_after)
    ultimately show ?thesis 
      by simp
  next
    case 2
    note two = this
    show ?case
  proof(rule same_ids_same(1)[of _ j], goal_cases)
    case 1
    then show ?case
      using ids_dom_if_wf laminar_forest_invarD(7) by auto
  next
    case (2 jj)
    then show ?case
      using laminar_merge_precondD(5) laminar_forest_invarD(2,7) ids_in_dom two
      by (auto simp add: map.map_update)
  next
    case 3
    then show ?case 
      by (simp add: laminar_forest_invarD(10))
  next
    case 4
    then show ?case
      by (simp add: laminar_forest_invarD(7) self_in_ids two(2))  
  qed
qed

have same_collect_verts:
  "j \<noteq> new_id \<Longrightarrow> collect_verts (update new_id (subverts ids) L) j = 
           collect_verts L j" for j
  proof(cases "lookup L j", goal_cases)
    case 1
    hence same_lookup:"lookup (update new_id (subverts ids) L) j= lookup L j" 
      by (simp add: laminar_forest_invarD(2) map.map_update)
    moreover have "collect_verts L j = {}"
      by (simp add: "1"(2) collect_verts_simps laminar_forest_invarD(7))
    moreover have "collect_verts (update new_id (subverts ids) L) j = {}" 
      by (simp add: "1"(2) collect_verts_simps same_lookup wf_after)
    ultimately show ?thesis 
      by simp
  next
    case 2
    note two = this
    show ?case
  proof(rule same_ids_same(2)[of _ j], goal_cases)
    case 1
    then show ?case
      using ids_dom_if_wf laminar_forest_invarD(7) by auto
  next
    case (2 jj)
    then show ?case
      using laminar_merge_precondD(5) laminar_forest_invarD(2,7) ids_in_dom two
      by (auto simp add: map.map_update)
  next
    case 3
    then show ?case 
      by (simp add: laminar_forest_invarD(10))
  next
    case 4
    then show ?case
      by (simp add: laminar_forest_invarD(7) self_in_ids two(2))  
  qed
qed

  have disjoint_subids_after: 
    "disjoint_subids (update new_id (subverts ids) L)"
  proof(rule disjoint_subidsI, goal_cases)
    case (1 i vs j k)
    then show ?case 
      unfolding map.map_update[OF laminar_forest_invarD(2)]
    proof(cases "new_id = i", goal_cases)
      case 1
      have j_same: "ids_of_sub_laminars (update i (subverts ids) L) j = 
           ids_of_sub_laminars L j"
      proof(rule same_ids_same(1)[of _ j], goal_cases)
        case 1
        then show ?case 
          using ids_dom_if_wf laminar_forest_invarD(7) by blast
      next
        case (2 jj)
        then show ?case 
          using "1"(1,2,5) laminar_merge_precondD(2,5) ids_in_dom laminar_forest_invarD(7)  
          by (auto simp add: max_ids_def  map.map_update[OF laminar_forest_invarD(2)])
      next
        case 4
        then show ?case 
          using "1"(1,2,5) laminar_forest_invarD(7) laminar_merge_precondD(2) max_ids_def self_in_ids
          by auto
      qed (simp add: laminar_forest_invarD(10))
      have k_same: "ids_of_sub_laminars (update i (subverts ids) L) k = 
           ids_of_sub_laminars L k"
      proof(rule same_ids_same(1)[of _ k], goal_cases)
        case 1
        then show ?case 
          using ids_dom_if_wf laminar_forest_invarD(7) by blast
      next
        case (2 jj)
        then show ?case 
          using "1"(1,3,5) laminar_merge_precondD(2,5) ids_in_dom laminar_forest_invarD(7)  
          by (auto simp add: max_ids_def  map.map_update[OF laminar_forest_invarD(2)])
      next
        case 4
        then show ?case 
          using "1"(1,3,5) laminar_forest_invarD(7) laminar_merge_precondD(2) max_ids_def self_in_ids
          by auto
      qed (simp add: laminar_forest_invarD(10))
      from 1 show ?case 
        using disjoint_treesD[OF laminar_forest_invarD(5), of j k] laminar_merge_precondD(2)
              j_same k_same
        by (auto simp add: j_same k_same)
    next
      case 2
have j_same: "ids_of_sub_laminars (update new_id (subverts ids) L) j = 
           ids_of_sub_laminars L j"
      proof(rule same_ids_same(1)[of _ j], goal_cases)
        case 1
        then show ?case 
          using ids_dom_if_wf laminar_forest_invarD(7) by blast
      next
        case (2 jj)
        then show ?case 
          using "1"(1,2) laminar_merge_precondD(2,5) ids_in_dom laminar_forest_invarD(7)  
                domain_recursiveD[OF laminar_forest_invarD(10)]
          by(cases "i = j")
            (auto simp add:  max_ids_def  map.map_update[OF laminar_forest_invarD(2)])
      next
        case 4
        then show ?case
          using"2"(1,2,5) laminar_forest_invarD(10,7) self_in_ids[of L j]
          by(auto elim!:  domain_recursiveE)
      qed (simp add: laminar_forest_invarD(10))
      have k_same: "ids_of_sub_laminars (update new_id (subverts ids) L) k = 
           ids_of_sub_laminars L k"
      proof(rule same_ids_same(1)[of _ k], goal_cases)
        case 1
        then show ?case 
          using ids_dom_if_wf laminar_forest_invarD(7) by blast
      next
        case (2 jj)
        then show ?case 
          using "1"(1,3) laminar_merge_precondD(2,5) ids_in_dom laminar_forest_invarD(7)  
                domain_recursiveD[OF laminar_forest_invarD(10)]
          by(cases "i = k")
            (auto simp add:  max_ids_def  map.map_update[OF laminar_forest_invarD(2)])
      next
        case 4
        then show ?case
          using"2"(1,3,5) laminar_forest_invarD(10,7) self_in_ids[of L k]
          by(auto elim!:  domain_recursiveE)
      qed (simp add: laminar_forest_invarD(10))
      show ?case
        using "2"(1,2,3,4,5)  laminar_forest_invarD(4)
        by (auto dest: disjoint_subidsD simp add: j_same k_same)
    qed
  qed

  have disjoint_trees_after:
   "disjoint_trees (update new_id (subverts ids) L)"
  proof(rule disjoint_treesI, goal_cases)
    case (1 k j)
    then show ?case 
      unfolding new_max_ids_are
    proof(elim UnE, goal_cases)
      case 1
      have "ids_of_sub_laminars (update new_id (subverts ids) L) j =
           ids_of_sub_laminars L j"
        using "1"(3) laminar_merge_precondD(5) max_ids_def 
        by (intro same_sub_laminars) force
      moreover have "ids_of_sub_laminars (update new_id (subverts ids) L) k =
           ids_of_sub_laminars L k"
        using "1"(2) laminar_merge_precondD(5) max_ids_def 
        by (intro same_sub_laminars) force
      ultimately show ?case 
        using "1"(1,2,3) disjoint_treesD laminar_forest_invarD(5) by fastforce
    next
      case 2
      note two = this
     have "ids_of_sub_laminars (update new_id (subverts ids) L) k =
           ids_of_sub_laminars L k"
        using "2"(2) laminar_merge_precondD(5) max_ids_def 
        by (intro same_sub_laminars) force
      moreover have "ids_of_sub_laminars (update new_id (subverts ids) L) j =
                   {new_id} \<union> (\<Union> (ids_of_sub_laminars L ` set ids))"
      proof-
        have rw:"ids_of_sub_laminars (update new_id (subverts ids) L) j = 
             {j} \<union> \<Union> (ids_of_sub_laminars (update new_id (subverts ids) L) ` set ids)"
          using
           ids_of_sub_laminars_simps[OF wf_after, of j]
            laminar_forest_invarD(2) map.map_update two(3) by force
        show ?thesis
          unfolding rw
        proof(rule arg_cong2[where f = Set.union], goal_cases)
          case 1
          then show ?case
            using two(3) by blast
        next
          case 2
          then show ?case 
          proof(rule arg_cong[where f = Union], rule image_cong, goal_cases)
            case (1 i)
            then show ?case 
              using dom_def laminar_merge_precondD(2,5) max_ids_def 
              by (intro same_sub_laminars) auto
          qed
        qed
      qed
      ultimately show ?case 
        using ids_in_dom[OF laminar_forest_invarD(7)] laminar_merge_precondD(5) 
              laminar_forest_invarD(5) laminar_merge_precondD(2) two(2) 
        by(auto dest: disjoint_treesD)
    next
      case 3
      note three = this
     have "ids_of_sub_laminars (update new_id (subverts ids) L) j =
           ids_of_sub_laminars L j"
        using "3"(3) laminar_merge_precondD(5) max_ids_def 
        by (intro same_sub_laminars) force
      moreover have "ids_of_sub_laminars (update new_id (subverts ids) L) k =
                   {new_id} \<union> (\<Union> (ids_of_sub_laminars L ` set ids))"
      proof-
        have rw:"ids_of_sub_laminars (update new_id (subverts ids) L) k = 
             {k} \<union> \<Union> (ids_of_sub_laminars (update new_id (subverts ids) L) ` set ids)"
          using
           ids_of_sub_laminars_simps[OF wf_after, of k]
            laminar_forest_invarD(2) map.map_update three(2) by force
        show ?thesis
          unfolding rw
        proof(rule arg_cong2[where f = Set.union], goal_cases)
          case 1
          then show ?case
            using three(2) by blast
        next
          case 2
          then show ?case 
          proof(rule arg_cong[where f = Union], rule image_cong, goal_cases)
            case (1 i)
            then show ?case 
              using dom_def laminar_merge_precondD(2,5) max_ids_def 
              by (intro same_sub_laminars) auto
          qed
        qed
      qed
      ultimately show ?case 
        using ids_in_dom[OF laminar_forest_invarD(7)] laminar_merge_precondD(5) 
              laminar_forest_invarD(5) laminar_merge_precondD(2) three(3) 
        by(auto dest: disjoint_treesD)
    next
      case 4
      then show ?case 
        by simp
    qed
  qed

  have elem_unique_id_after:
   "elem_unique_id (update new_id (subverts ids) L)"
  proof(rule elem_unique_idI, goal_cases)
    case (1 x i j)
    hence "i \<noteq> new_id" "j \<noteq> new_id" 
      using laminar_forest_invarD(2) map.map_update by force+
    then show ?case 
      using "1"(1,2) elem_unique_idD laminar_forest_invarD(2,6) map.map_update by force
  qed

  have branching_properly_after:
   "branching_properly (update new_id (subverts ids) L)"
  proof(rule branching_properlyI, goal_cases)
    case (1 i vs)
    then show ?case 
    proof(cases "i = new_id", goal_cases)
      case 1
      then show ?case 
        using laminar_forest_invarD(2) laminar_merge_precondD(3) map.map_update by auto
    next
      case 2
      then show ?case 
        using branching_properlyE laminar_forest_invarD(2,9) map.map_update by auto
    qed
  qed

  have domain_recursive_after:
   "domain_recursive (update new_id (subverts ids) L)"
  proof(rule domain_recursiveI, goal_cases)
    case (1 i j vs)
    then show ?case 
    proof(cases "i = new_id", goal_cases)
      case 1
      then show ?case 
        using important_properties(5) laminar_merge_precondD(1,2) map.map_update by fastforce
    next
      case 2
      then show ?case 
        using laminar_forest_invarD(10,2) 
        by(auto elim!:  domain_recursiveE simp add: map.map_update)   
    qed
  qed

  have distinct_children_after:
   "distinct_children (update new_id (subverts ids) L)"
  proof(rule distinct_childrenI, goal_cases)
    case (1 i vs)
    then show ?case 
    proof(cases "i = new_id", goal_cases)
      case 1
      then show ?case 
        using laminar_forest_invarD(2) laminar_merge_precondD(4) map.map_update by auto
    next
      case 2
      then show ?case 
        using distinct_childrenD laminar_forest_invarD(11,2) map.map_update by auto
    qed
  qed

  show th2: ?th2
    by (simp add: laminar_forest_invarD(2) map.map_update)

  show th3: ?th3
    using laminar_forest_invarD(2) laminar_merge_precondD(5)
    by (auto simp add: map.map_update)

  show th4: ?th4
  proof(rule ext, goal_cases)
    case (1 i)
    then show ?case
    proof(cases "i = new_id", goal_cases)
      case 1
      moreover have "xa \<in> set ids \<Longrightarrow>
        collect_verts (update new_id (subverts ids) L) xa = 
        collect_verts L xa"  for xa
        using laminar_merge_precondD(2,5) 
        by(intro same_collect_verts)(auto simp add: max_ids_def)
      ultimately show ?case 
        by (auto simp add: collect_verts_simps[OF wf_after, of new_id]
                           map.map_update laminar_forest_invarD(2))
    next
      case 2
      then show ?case 
      using same_collect_verts by simp
    qed
  qed
       
  show th1: ?th1
  proof(unfold merge.simps Let_def, rule laminar_forest_invarI, goal_cases)
    case 1
    then show ?case 
      by (simp add: new_L_props top_set.invar_insert)
  next
    case 2
    then show ?case 
      by (simp add: laminar_forest_invarD(2) map.invar_update)
  next
    case 3
    then show ?case 
      using laminar_forest_invarD(3) new_L_props new_max_ids_are top_set.set_insert by auto
  next
    case 4
    then show ?case
      by (simp add: disjoint_subids_after)
  next
    case 5
    then show ?case 
      by (simp add: disjoint_trees_after)
  next
    case 6
    then show ?case 
      by(simp add: elem_unique_id_after)
  next
    case 7
    then show ?case 
      by (simp add: wf_after)
  next
    case 8
    then show ?case 
      by (simp add: laminar_forest_invarD(2,8) map.map_update)
  next
    case 9
    then show ?case 
      by(simp add: branching_properly_after)
  next
    case 10
    then show ?case 
      by(simp add: domain_recursive_after)
  next
    case 11
    then show ?case 
      by(simp add: distinct_children_after)
  qed

  show ?th6
    unfolding th4
  proof(rule, all \<open>rule\<close>, all \<open>elim insertE CollectE exE\<close>, goal_cases)
    case (1 x i)
    then show ?case 
    proof(cases "i = new_id", goal_cases)
    next
      case 2
      then show ?case 
        using th2
        by (auto  intro!: exI[of _ i])
    qed auto
  next
    case (2 x)
    then show ?case 
      by (auto intro!: exI[of _ new_id] exI[of _ "subverts ids"]
             simp add: laminar_forest_invarD(2) map.map_update)
  next
    case (3 x i)
    then show ?case 
      using laminar_merge_precondD(5) th2
      by(auto intro!: exI[of _ i])
  qed
qed
                                                             
interpretation laminar_family_merge_spec_statisfied: laminar_merge_spec
  where all_ids = "\<lambda> (maxes, L). dom (lookup L)"
  and universe =  "\<lambda> (maxes, L). all_verts L"
  and collect_elems = "\<lambda> (maxes, L). collect_verts L"
  and max_ids = "\<lambda> (maxes, L). max_ids L"
  and laminar_invar = laminar_forest_invar
  and laminar_abstract = "\<lambda> (maxes, L). {collect_verts L i | i. i \<in> dom (lookup L)}"
  and compound = compound
  and merge = merge
proof(rule laminar_merge_spec.intro, goal_cases)
  case 1
  then show ?case 
    by (simp add: laminar_family_spec_statisfied.laminar_family_spec_axioms)
next
  case 2
  then show ?case 
  proof(rule laminar_merge_spec_axioms.intro, goal_cases)
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
  qed
qed

lemmas laminar_family_merge_spec_statisfied_axioms =
  laminar_family_merge_spec_statisfied.laminar_merge_spec_axioms

lemmas laminar_family_spec_statisfied_axioms =
  laminar_family_spec_statisfied.laminar_family_spec_axioms

lemma unmerge_props:
  fixes id
  assumes "laminar_family_spec_statisfied.laminar_unmerge_precond (maxids, L) id"
  and result_def: "unmerge (maxids, L) id = ((maxids', L'), ids)"
  shows "laminar_forest_invar (maxids', L')" (is ?th1)
   and  "dom (lookup L') = dom (lookup L) - {id}" (is ?th2)
   and "{v | i v. lookup L' i = Some (elem_vert v)} = 
        {v | i v. lookup L i = Some (elem_vert v)}" (is ?th3)
   and "collect_verts L' = 
       (\<lambda> x. if x = id then {} else collect_verts L x)" (is ?th4)
   and "max_ids L' = max_ids L - {id} \<union> set ids" (is ?th5)
   and "{collect_verts L' i | i. i \<in> dom (lookup L')} = 
        {collect_verts L i |i. i \<in> dom (lookup L)} - {collect_verts L id}" (is ?th6)
   and "distinct ids"
   and "length ids \<ge> 2"
proof-
  note laminar_unmerge_precondD =
   laminar_family_spec_statisfied.laminar_unmerge_precondD[OF assms(1), simplified prod.case]
  note laminar_forest_invarD = laminar_forest_invarD[OF laminar_unmerge_precondD(1)]
  define rev_ids where "rev_ids = rev ids"
  have rev_ids_def: "rev ids = rev_ids" "set ids = set rev_ids"
    by(auto simp add: rev_ids_def)
  have maxids'_def: "maxids' = top_delete id (foldl (\<lambda>S x. top_insert x S) maxids ids)"
    by (metis prod.inject result_def unmerge.simps)
  have L'_def: "L' = delete id L" 
    by (metis prod.inject result_def unmerge.simps)
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
        using laminar_unmerge_precondD(3) by presburger
    next
      case (2 vs)
      then show ?case 
        using result_def by auto
    qed
  qed
  have new_L_props:"top_invar (foldl (\<lambda>S x. top_insert x S) maxids ids) \<and>
        top_set (foldl (\<lambda>S x. top_insert x S) maxids ids) = top_set maxids \<union> set ids"
    using laminar_forest_invarD(1)
    unfolding foldl_conv_foldr rev_ids_def
    by(induction rev_ids)
      (auto simp add: top_set.invar_insert top_set.set_insert)
  show new_max_ids_are: ?th5
  proof(rule, all \<open>rule\<close>, goal_cases)
    case (1 i)
    hence i_props:"lookup (delete id L) i \<noteq> None"
          "\<nexists>i' vs. lookup (delete id L) i' = Some (subverts vs) \<and> i \<in> set vs"
      by(auto simp add: max_ids_def L'_def)
    show ?case 
      using i_props
      unfolding map.map_update[OF laminar_forest_invarD(2)]
    proof(cases "i \<in> set ids", goal_cases)
      case 1
      then show ?thesis 
        by simp
    next
      case 2
      hence two: "\<exists>y. lookup L i = Some y"
       "i \<notin> set ids"
       "\<And> i' vs. \<lbrakk>i' \<noteq> id; lookup L i' = Some (subverts vs)\<rbrakk> \<Longrightarrow>  i \<notin> set vs"
       "i \<noteq> id"
        using laminar_forest_invarD(2)
        by(auto simp add: map.map_delete if_split[of "\<lambda> x. x = Some _"])
      have "i \<in> max_ids L"
      proof(rule in_maxidsI, goal_cases)
        case 1
        then show ?case 
          by (simp add: two(1))
      next
        case (2 i' vs)
        then show ?case 
          using result_def two(2) two(3)[of i' vs] by fastforce
      qed
      moreover have "i \<noteq> id"
        by (simp add: two(4))
      ultimately show ?thesis 
        by simp
    qed
  next
    case (2 i)
    then show ?case 
    proof(rule UnE, goal_cases)
      case 1
      then show ?case 
        by(auto intro!: in_maxidsI
              simp add: laminar_forest_invarD(2) map.map_delete max_ids_def L'_def)
    next
      case 2
      then show ?case 
      proof(intro in_maxidsI, goal_cases)
        case 1
        then show ?case 
          using laminar_unmerge_precondD(2) laminar_forest_invarD(10,2) ids_def
          by(auto elim!: in_maxidsE domain_recursiveE 
               simp add:  map.map_delete L'_def)
      next
        case (2 i' vs)
        hence i'_props:"i' \<noteq> id" "lookup L i' = Some (subverts vs)"
          using laminar_forest_invarD(2) 
          by(auto simp add: map.map_delete L'_def if_split[of "\<lambda> x. x = Some _"])
        hence "collect_verts L id \<noteq> collect_verts L i'"
          using laminar_unmerge_precondD(1)  ids_def
          by(intro inj_on_contraD[OF important_properties(1), of maxids]) auto
        moreover have "collect_verts L id \<inter> collect_verts L i' \<noteq> {}" 
          using  "2"(1,3) domain_recursive_def[of L] ids_def branching_properly_children_nempty
                 collect_verts_uf[of L id] immediate_childrenin_ids[of L id ids i]
                 i'_props(2) laminar_forest_invarD(7,10,9)
          by (intro inter_nemptyI[OF _ _
                 collect_verts_nempty[OF laminar_forest_invarD(7), of i]])
             (force elim!: domain_recursiveE simp add: laminar_forest_invarD(10)  collect_verts_simps)+
        moreover have "\<not> collect_verts L id \<subset> collect_verts L i'" 
                      "\<not> collect_verts L id \<supset> collect_verts L i'"
        proof-
          obtain id' where id':  "id' \<in> max_ids L" "i' \<in> ids_of_sub_laminars L id'" 
            using  i'_props(2) in_dom_a_max_id[of L i'] laminar_forest_invarD(7,8) 
            by auto
          thus  "\<not> collect_verts L id \<subset> collect_verts L i'" 
          using "2"(1,3)  i'_props(2) ids_def ids_mono[OF laminar_forest_invarD(7), of i' id']  
                immediate_childrenin_ids[OF laminar_forest_invarD(7), of i' vs i]
                immediate_childrenin_ids[OF laminar_forest_invarD(7), of id ids i] 
                laminar_forest_invarD(10,5,8) disjoint_treesD[OF laminar_forest_invarD(5), of id id'] 
                laminar_unmerge_precondD(2) option.distinct(1) psubsetE subset_eq 
          by(elim domain_recursiveE)
            (auto simp add: collect_verts_uf[OF laminar_forest_invarD(7), of id])
        show "\<not> collect_verts L id \<supset> collect_verts L i'"
        proof(rule notI, goal_cases)
          case 1
          have ids_same:"id' = id"
           using "2"(1) id' i'_props(1) ids_def 
                 ids_mono[OF laminar_forest_invarD(7), of i'] 
                 immediate_childrenin_ids[OF laminar_forest_invarD(7) ids_def 2(1)]
                 immediate_childrenin_ids[OF laminar_forest_invarD(7) i'_props(2) 2(3)]
                 laminar_forest_invarD(10) 
                 disjoint_treesD[OF laminar_forest_invarD(5) id'(1) laminar_unmerge_precondD(2)]
          by(elim domain_recursiveE) auto   
          show ?case 
              using 1 "2"(1) id' disjoint_subidsD[OF laminar_forest_invarD(4) ids_def 2(1)]
                    i'_props(1) ids_def  ids_mono[OF laminar_forest_invarD(7), of i'] 
                    immediate_childrenin_ids[OF laminar_forest_invarD(7) i'_props(2) 2(3)]
                    laminar_forest_invarD(10) not_in_subtree[OF laminar_forest_invarD(7) i'_props(2) 2(3)] 
                    self_in_ids[OF laminar_forest_invarD(7), of i] 
              unfolding ids_same
              by(elim  domain_recursiveE in_ids_of_sub_laminars_cases[OF
                                      laminar_forest_invarD(7), of i' id])
                 auto
          qed
        qed
        moreover have "id \<in> dom (lookup L)"
          using ids_def by blast
        moreover have "i' \<in> dom (lookup L)" 
          by (simp add: i'_props(2) domIff)
        moreover have "collect_verts L id \<subseteq> all_verts L"  "collect_verts L i' \<subseteq> all_verts L"
          using all_verts_def collect_verts_uf' laminar_forest_invarD(7) by auto
        ultimately have "\<not> laminar (all_verts L) {collect_verts L i |i. i \<in> dom (lookup L)}"
          by(unfold laminar_def) blast 
        thus ?case 
          using important_properties(2)[OF laminar_unmerge_precondD(1)]
          by simp
      qed
    qed
  qed

  have laminar_forest_cons_after_is:
       "(laminar_forest_cons L') = 
        (laminar_forest_cons L) - { (j, id) | j. j \<in> set ids}" 
    using laminar_forest_invarD(2) ids_def
    by(force simp add: laminar_forest_cons_def laminar_forest_invarD(2) map.map_delete L'_def)
   
  have wf_after: "wf (laminar_forest_cons L')"
    using laminar_forest_invarD(7) wf_subset 
    by (fastforce simp add: laminar_forest_cons_after_is)

  have same_ids_same_precond:
   "ids_of_sub_laminars_dom L j"
   "\<And>ja. ja \<in> ids_of_sub_laminars L j \<union> {j} \<Longrightarrow> lookup L' ja = lookup L ja"
   "domain_recursive L" "j \<in> ids_of_sub_laminars L j" 
   if "j \<noteq> id" "lookup L j \<noteq> None" for j
  proof( goal_cases)
    case 1
    then show ?case
      using ids_dom_if_wf laminar_forest_invarD(7) by auto
  next
    case (2 jj)
    hence "jj \<noteq> id"
    proof(intro notI, goal_cases)
      case 1
      moreover hence "collect_verts L j = collect_verts L id"
        using laminar_forest_invarD(4,7) laminar_unmerge_precondD(2) ids_def
              strict_subids_immediate_parent[of L id j] ids_mono[of L id j]
        by(fastforce elim!: in_maxidsE[of id L] 
                  simp add: collect_verts_uf[of L id] collect_verts_uf[of L j])
      moreover hence "ids_of_sub_laminars L id \<subseteq> ids_of_sub_laminars L j" 
        using "1"(2) "2" ids_mono laminar_forest_invarD(7) that by auto
      moreover have "ids_of_sub_laminars L j \<noteq> ids_of_sub_laminars L id"
        using that laminar_forest_invarD(10,11,4,6,7,9) calculation(2,3) "2" 
          ids_dom_if_wf[of L j] disjoint_elems_if_disjoint_subids_and_elem_unique_id[of L]
          disjoint_elem_verts_pre_inj_of_collect[of L id j id] self_in_ids'[of L j]
        by auto
      moreover obtain i' vs' where "lookup L i' = Some (subverts vs')" "id \<in> set vs'"
        using laminar_forest_invarD(4,7) ids_def calculation(4,5)
          strict_subids_immediate_parent[of L id j]
        by auto
      ultimately show ?case
      using that 1
        laminar_unmerge_precondD(2) domIff[of id "lookup L"]
        psubsetI'[of "ids_of_sub_laminars L id" "ids_of_sub_laminars L j"] 
      by(force elim!: in_maxidsE[of id L])
  qed
  thus ?case
    by (simp add: L'_def laminar_forest_invarD(2) map.map_delete)
  next
    case 3
    then show ?case 
      by (simp add: laminar_forest_invarD(10))
  next
    case 4
    then show ?case
      by (simp add: laminar_forest_invarD(7) self_in_ids that)  
  qed

  have same_sub_laminars:
    "j \<noteq> id \<Longrightarrow> ids_of_sub_laminars L' j = ids_of_sub_laminars L j" for j
  proof(cases "lookup L j", goal_cases)
    case 1
    hence same_lookup:"lookup L' j= lookup L j"
      by (simp add: L'_def laminar_forest_invarD(2) map.map_delete)
    moreover have "ids_of_sub_laminars L j = {}"
      by (simp add: "1"(2) ids_of_sub_laminars_simps laminar_forest_invarD(7))
    moreover have "ids_of_sub_laminars L' j = {}" 
      by (simp add: "1"(2) ids_of_sub_laminars_simps same_lookup wf_after)
    ultimately show ?thesis 
      by simp
  next
    case 2
    note two = this
    thus ?case
      by(intro same_ids_same(1)[OF same_ids_same_precond]) auto
  qed

  have same_collect_verts: "j \<noteq> id \<Longrightarrow> collect_verts L' j = collect_verts L j" for j
  proof(cases "lookup L j", goal_cases)
    case 1
    hence same_lookup:"lookup L' j= lookup L j"
      by (simp add: L'_def laminar_forest_invarD(2) map.map_delete)
    moreover have "collect_verts L j = {}"
      by (simp add: "1"(2) collect_verts_simps laminar_forest_invarD(7))
    moreover have "collect_verts L' j = {}"
      by (simp add: "1"(2) collect_verts_empty domIff same_lookup wf_after)
    ultimately show ?thesis 
      by simp
  next
    case (2 a)
    note two = this
    thus ?case
      by(intro same_ids_same(2)[OF same_ids_same_precond]) auto
  qed

  have disjoint_subids_after: "disjoint_subids L'"
  proof(rule disjoint_subidsI, goal_cases)
    case (1 i vs j k)
    then show ?case 
      unfolding map.map_update[OF laminar_forest_invarD(2)]
    proof(cases "id = i", goal_cases)
      case 1
      have j_same: "ids_of_sub_laminars L' j = ids_of_sub_laminars L j"
        using laminar_forest_invarD(2) 1(1,5)
        by(intro same_ids_same(1)[OF same_ids_same_precond]) 
          (auto simp add: map.map_delete L'_def)
      have k_same: "ids_of_sub_laminars L' k = ids_of_sub_laminars L k"
        using laminar_forest_invarD(2) 1(1,5)
        by(intro same_ids_same(1)[OF same_ids_same_precond]) 
          (auto simp add: map.map_delete L'_def)
      from 1 show ?case 
        using disjoint_treesD[OF laminar_forest_invarD(5), of j k] 
              j_same k_same
        by (auto simp add: j_same k_same L'_def laminar_forest_invarD(2) map.map_delete)
    next
      case 2
      have j_same: "ids_of_sub_laminars L' j = ids_of_sub_laminars L j"
        using 2(1,2,5) laminar_forest_invarD(2) laminar_unmerge_precondD(2)
              laminar_forest_invarD(10)
        by(intro same_ids_same(1)[OF same_ids_same_precond]) 
          (auto elim!: in_maxidsE 
                 dest: domain_recursiveD 
             simp add: L'_def map.map_delete)
      have k_same: "ids_of_sub_laminars L' k = ids_of_sub_laminars L k"
        using 2(1,3,5) laminar_forest_invarD(2) laminar_unmerge_precondD(2)
              laminar_forest_invarD(10)
        by(intro same_ids_same(1)[OF same_ids_same_precond]) 
          (auto elim!: in_maxidsE 
                 dest: domain_recursiveD 
             simp add: L'_def map.map_delete)
      show ?case 
        using "2"(1,2,3,4,5)  laminar_forest_invarD(2,4) L'_def j_same k_same
        by (auto simp add: j_same k_same disjoint_subids_def map.map_delete)
    qed
  qed

  have disjoint_trees_after: "disjoint_trees L'"
  proof(rule disjoint_treesI, goal_cases)
    case (1 k j)
    then show ?case 
      unfolding new_max_ids_are
    proof(elim UnE, goal_cases)
      case 1
      have "ids_of_sub_laminars L' j = ids_of_sub_laminars L j" 
        using "1"(3)  max_ids_def by (intro same_sub_laminars) force
      moreover have "ids_of_sub_laminars L' k = ids_of_sub_laminars L k"
        using "1"(2)  max_ids_def by (intro same_sub_laminars) force
      ultimately show ?case 
        using "1"(1,2,3) disjoint_treesD laminar_forest_invarD(5) by fastforce
    next
      case 2
      note two = this
     have "ids_of_sub_laminars L' k = ids_of_sub_laminars L k"
        using "2"(2) max_ids_def by (intro same_sub_laminars) force
      moreover have "ids_of_sub_laminars L' j = ids_of_sub_laminars L j"
        using "2"(3) max_ids_def ids_def laminar_unmerge_precondD(2) 
        by (intro same_sub_laminars) auto
      moreover have "ids_of_sub_laminars L j \<subseteq> ids_of_sub_laminars L id"
        using domain_recursiveD ids_def ids_mono immediate_childrenin_ids laminar_forest_invarD(10,7)
          two(3) by presburger
      ultimately show ?case 
        using ids_in_dom[OF laminar_forest_invarD(7)] laminar_forest_invarD(5) two(2) 
              laminar_unmerge_precondD(2) disjoint_treesD[of L k id]
        by auto
    next
      case 3
      note three = this
     have "ids_of_sub_laminars L' j = ids_of_sub_laminars L j"
        using "3"(3) max_ids_def by (intro same_sub_laminars) force
      moreover have "ids_of_sub_laminars L' k = ids_of_sub_laminars L k"
        using "3"(2) max_ids_def ids_def laminar_unmerge_precondD(2) 
        by (intro same_sub_laminars) auto
      moreover have "ids_of_sub_laminars L k \<subseteq> ids_of_sub_laminars L id"
        using domain_recursiveD ids_def ids_mono immediate_childrenin_ids laminar_forest_invarD(10,7)
          3(2) by presburger
      ultimately show ?case 
        using ids_in_dom[OF laminar_forest_invarD(7)] laminar_forest_invarD(5) 3(3) 
              laminar_unmerge_precondD(2) disjoint_treesD[of L j id]
        by auto
    next
      case 4
     have "ids_of_sub_laminars L' j = ids_of_sub_laminars L j"
       using "4"(3) max_ids_def ids_def laminar_unmerge_precondD(2) 
       by (intro same_sub_laminars) auto
     moreover have "ids_of_sub_laminars L' k = ids_of_sub_laminars L k"
       using "4"(2) max_ids_def ids_def laminar_unmerge_precondD(2) 
       by (intro same_sub_laminars) auto
     ultimately show ?case 
       using "4"(1,2,3) disjoint_subidsD ids_def laminar_forest_invarD(4) by blast
    qed
  qed

  have elem_unique_id_after: "elem_unique_id L'"
  proof(rule elem_unique_idI, goal_cases)
    case (1 x i j)
    hence "i \<noteq> id" "j \<noteq> id" 
      using laminar_forest_invarD(2) by (force simp add: map.map_delete L'_def)+
    then show ?case 
      using "1"(1,2) elem_unique_idD laminar_forest_invarD(2,6)  
      by (force simp add: map.map_delete L'_def)
  qed

  have branching_properly_after: "branching_properly L'"
  proof(rule branching_properlyI, goal_cases)
    case (1 i vs)
    then show ?case 
    proof(cases "i = id", goal_cases)
      case 1
      then show ?case
        by (simp add: L'_def laminar_forest_invarD(2) map.map_delete)
    next
      case 2
      then show ?case 
        using laminar_forest_invarD(2,9)
        by (auto elim: branching_properlyE simp add: L'_def map.map_delete)
    qed
  qed

  have domain_recursive_after: "domain_recursive L'"
  proof(rule domain_recursiveI, goal_cases)
    case (1 i j vs)
    then show ?case 
    proof(cases "i = id", goal_cases)
      case 1
      then show ?case
        by (simp add: L'_def laminar_forest_invarD(2) map.map_delete)
    next
      case 2
      then show ?case 
        using laminar_forest_invarD(10,2) laminar_unmerge_precondD(2)
        by(auto elim!: domain_recursiveE in_maxidsE simp add: map.map_delete L'_def)
    qed
  qed

  have distinct_children_after: "distinct_children L'"
  proof(rule distinct_childrenI, goal_cases)
    case (1 i vs)
    then show ?case 
    proof(cases "i = id", goal_cases)
      case 1
      then show ?case 
        by (simp add: L'_def laminar_forest_invarD(2) map.map_delete)
    next
      case 2
      then show ?case 
        using laminar_forest_invarD(11,2) laminar_unmerge_precondD(2)
        by(auto elim!: distinct_childrenE in_maxidsE simp add: map.map_delete L'_def)
    qed
  qed

  show th2: ?th2 
    by (simp add: laminar_forest_invarD(2) map.map_delete L'_def)

  show th3: ?th3
    using laminar_forest_invarD(2) ids_def
    by (force simp add: map.map_delete L'_def)

  show th4: ?th4
  proof(rule ext, goal_cases)
    case (1 i)
    then show ?case
    proof(cases "i = id", goal_cases)
      case 1
      thus ?case
        by (simp add: collect_verts_empty th2 wf_after)
    next
      case 2
      then show ?case 
      using same_collect_verts by simp
    qed
  qed
       
  show th1: ?th1
  proof(rule laminar_forest_invarI, goal_cases)
    case 1
    then show ?case 
      by (simp add: new_L_props top_set.invar_delete maxids'_def)
  next
    case 2
    then show ?case 
      by (simp add: laminar_forest_invarD(2) map.invar_delete L'_def)
  next
    case 3
    then show ?case 
      using new_L_props ids_def laminar_forest_invarD(3) laminar_unmerge_precondD(2)
      by(auto elim!: in_maxidsE 
           simp add: top_set.set_delete new_max_ids_are maxids'_def)
  next
    case 4
    then show ?case
      by (simp add: disjoint_subids_after)
  next
    case 5
    then show ?case 
      by (simp add: disjoint_trees_after)
  next
    case 6
    then show ?case 
      by(simp add: elem_unique_id_after)
  next
    case 7
    then show ?case 
      by (simp add: wf_after)
  next
    case 8
    then show ?case 
      by (simp add: laminar_forest_invarD(2,8) map.map_delete L'_def)
  next
    case 9
    then show ?case 
      by(simp add: branching_properly_after)
  next
    case 10
    then show ?case 
      by(simp add: domain_recursive_after)
  next
    case 11
    then show ?case 
      by(simp add: distinct_children_after)
  qed

  show ?th6
    unfolding th4 L'_def
  proof(rule, all \<open>rule\<close>, all \<open>elim DiffE CollectE exE\<close>, goal_cases)
    case (1 x i)
    then show ?case 
    proof(cases "i = id", goal_cases)
    next
      case 2
      hence "collect_verts (delete id L) i = collect_verts L i" 
        using L'_def same_collect_verts by presburger
      then show ?case 
        using 2  ids_def important_properties(1)[OF laminar_unmerge_precondD(1)]
        by (auto intro!: exI[of _ i] 
               simp add: L'_def laminar_forest_invarD(2) map.map_delete inj_on_def)
    next
      case 1
      thus ?case
        using L'_def th2 by blast
    qed 
  next
    case (2 x i)
    moreover hence "i \<noteq> id"
      by auto
    moreover hence "collect_verts (delete id L) i = collect_verts L i" 
      using L'_def same_collect_verts by blast
    ultimately show ?case 
      by (auto intro!: exI[of _ i] 
             simp add: laminar_forest_invarD(2) map.map_delete)
  qed
  show "distinct ids"  "length ids \<ge> 2"
    using ids_def laminar_forest_invarD(9,11)
    by(auto elim!: branching_properlyE distinct_childrenE)
qed

interpretation laminar_family_unmerge_spec_statisfied: laminar_unmerge_spec
  where all_ids = "\<lambda> (maxes, L). dom (lookup L)"
  and universe =  "\<lambda> (maxes, L). all_verts L"
  and collect_elems = "\<lambda> (maxes, L). collect_verts L"
  and max_ids = "\<lambda> (maxes, L). max_ids L"
  and laminar_invar = laminar_forest_invar
  and laminar_abstract = "\<lambda> (maxes, L). {collect_verts L i | i. i \<in> dom (lookup L)}"
  and compound = compound
  and unmerge = unmerge
proof(rule laminar_unmerge_spec.intro, goal_cases)
  case 1
  then show ?case 
    by (simp add: laminar_family_spec_statisfied.laminar_family_spec_axioms)
next
  case 2
  then show ?case 
  proof(rule laminar_unmerge_spec_axioms.intro, goal_cases)
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
    case (7 L id L' ids)
    then show ?case 
      using unmerge_props(7)[of _ _ id]
      by(cases L, cases L') auto 
  next
    case (8 L id L' ids)
    then show ?case 
      using unmerge_props(8)[of _ _ id]
      by(cases L, cases L') auto 
  qed
qed

lemma max_qualified_fold_correct:
  fixes id
  assumes "laminar_forest_invar (maxids, L)"
  shows "\<exists> ids. set ids = {id | id mid. mid \<in> max_ids L
                              \<and> collect_verts L id \<subseteq> collect_verts L mid \<and> P mid \<and> id \<in> dom (lookup L)}
          \<and> distinct ids \<and> max_qualified_fold P L f acc maxids = foldl f acc ids"
proof-
  note laminar_forest_invarD = laminar_forest_invarD[OF assms(1)]
  define f' where "f' = (\<lambda>acc i. if P i then laminar_tree_fold L f acc i else acc)"
  obtain ms where
     ms: "set ms = top_set maxids" "distinct ms" "set_fold f' acc maxids = foldl f' acc ms"
    using assms set_fold by(elim laminar_forest_invarE) blast
  define ms_rev where "ms_rev = rev ms"
  have ms_rev_def: "rev ms = ms_rev" "set ms = set ms_rev" "distinct ms = distinct ms_rev"
    by(auto simp add: ms_rev_def)
  have  "\<And> x m. \<lbrakk>m \<in> max_ids L; x \<in> dom (lookup L)\<rbrakk> \<Longrightarrow> 
         collect_verts L x \<subseteq> collect_verts L m \<Longrightarrow> x \<in> ids_of_sub_laminars L m"
  proof(goal_cases)
    case (1 x m)
    moreover then obtain m' where "m' \<in> max_ids L" "x \<in> ids_of_sub_laminars L m'"
      using in_dom_a_max_id laminar_forest_invarD(7,8) by blast
    moreover hence "m = m'" 
      using "1"(1,2,3)  branching_properly_children_nempty[OF laminar_forest_invarD(9)]
          collect_verts_nempty[OF laminar_forest_invarD(7), of x]
          collect_verts_uf[OF laminar_forest_invarD(7), of m'] laminar_forest_invarD(10,5,6,9)
          disjoint_elems_over_treesD
          disjoint_elems_over_trees_if_disjoint_subids_and_elem_unique_id[OF laminar_forest_invarD(7,6,5)]
      by fastforce
    ultimately show ?case
      by simp
  qed
  moreover have  "\<And> m m'. \<lbrakk>m \<in> max_ids L; m' \<in> max_ids L; m \<noteq> m'\<rbrakk> \<Longrightarrow> 
         ids_of_sub_laminars L m \<inter> ids_of_sub_laminars L m' = {}"
    by (simp add: disjoint_treesD laminar_forest_invarD(5))
  ultimately show ?thesis
    using ms(2)
    unfolding max_qualified_fold_def
    unfolding laminar_forest_invarD(3)
    unfolding ms(1)[symmetric] ms(3)[simplified f'_def] 
    unfolding foldl_conv_foldr ms_rev_def
  proof(induction ms_rev, goal_cases)
    case 1
    then show ?case by simp
  next
    case (2 m ms_rev)
    note IH = this
    then obtain ids where ids: 
     "set ids =
        {uu.
         \<exists>id mid.
            uu = id \<and> mid \<in> set ms_rev \<and> collect_verts L id \<subseteq> collect_verts L mid \<and> P mid \<and> id \<in> dom (lookup L)}"
        "distinct ids"
        "foldr (\<lambda>x y. if P x then laminar_tree_fold L f y x else y) ms_rev acc =
        foldr (\<lambda>x y. f y x) (rev ids) acc"
      by auto
    obtain ids' where ids':
      "set ids' = ids_of_sub_laminars L m"
      "distinct ids'"
      "laminar_tree_fold L f (foldr (\<lambda>x y. if P x then laminar_tree_fold L f y x else y)
               ms_rev acc) m =
      foldl f (foldr (\<lambda>x y. if P x then laminar_tree_fold L f y x else y) ms_rev acc) ids'"
     using laminar_tree_fold_correct[OF laminar_forest_invarD(7,11,4)]
     by meson
    show ?case 
      unfolding foldr.simps o_apply
    proof(cases "P m", goal_cases)
      case 1
      note Pm = this
      have ids_rw: "ids_of_sub_laminars L m = {uu.  collect_verts L uu \<subseteq> collect_verts L m \<and> uu \<in> dom (lookup L)}"
        using ids_in_dom[OF laminar_forest_invarD(7)] 
        by (auto simp add: 2(2)  laminar_forest_invarD(7) collect_verts_uf[of L m] dom_def)
       show ?case 
        unfolding if_P[OF 1]
      proof(rule exI[of _ "ids@ids'"], rule, goal_cases)
        case 1
        then show ?case 
          using Pm ids(1) ids'(1) ids_rw by auto
      next
        case 2
        then show ?case 
        proof(rule, goal_cases)
          case 1
          have "\<lbrakk>x \<in> ids_of_sub_laminars L m; mid \<in> set ms_rev;
              collect_verts L x \<subseteq> collect_verts L mid; P mid; lookup L x = Some y\<rbrakk>
               \<Longrightarrow> False" for x y mid
          proof(goal_cases)
            case 1
            have "x \<in> ids_of_sub_laminars L mid"
              using 1 by(auto intro!: IH(2)[of mid x])
            moreover have "ids_of_sub_laminars L m \<inter> ids_of_sub_laminars L mid = {}"
              using 1 IH(4) by(intro IH(3)[of m mid]) auto
            ultimately show ?case
              using 1 by auto
          qed
          then show ?case 
            by (auto simp add: ids(1,2)  ids'(1,2)) 
        next
          case 2
          then show ?case 
        unfolding ids'(3) rev_append foldr_append 
        unfolding foldl_conv_foldr
        unfolding ids(3)
        by simp
    qed
  qed
    next
      case 2
      then show ?case
        using ids
        by(auto intro!: exI[of _ ids])+
    qed
  qed
qed 

interpretation laminar_family_iteration_spec_statisfied: laminar_iteration_spec
  where all_ids = "\<lambda> (maxes, L). dom (lookup L)"
  and universe =  "\<lambda> (maxes, L). all_verts L"
  and collect_elems = "\<lambda> (maxes, L). collect_verts L"
  and max_ids = "\<lambda> (maxes, L). max_ids L"
  and laminar_invar = laminar_forest_invar
  and laminar_abstract = "\<lambda> (maxes, L). {collect_verts L i | i. i \<in> dom (lookup L)}"
  and compound = compound
  and max_qualified_iteration = "\<lambda> P (maxes, L) f acc. max_qualified_fold P L f acc maxes"
  and elems_iteration = "\<lambda> (maxes, L) i f acc . laminar_fold_singletons L f acc i"
proof(rule laminar_iteration_spec.intro, goal_cases)
  case 1
  then show ?case 
    by (simp add: laminar_family_spec_statisfied.laminar_family_spec_axioms)
next
  case 2
  show ?case
  proof(rule laminar_iteration_spec_axioms.intro, goal_cases)
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
(*
lemma new_laminar_max_ids:
  assumes  "wf {(j, i) | i j vs. lookup M i = Some (subverts vs) \<and>j \<in> set vs}"
  assumes  "set vs \<subseteq> max_ids M" "i \<notin> dom (lookup M)"
           "M' = update i (subverts vs) M"
   shows  "wf {(j, i) | i j vs. lookup M' i = Some (subverts vs) \<and>j \<in> set vs}"
          "ids_of_sub_laminars M "

inductive disjoint_subids where
  "lookup M i = Some (elem_vert x) \<Longrightarrow> disjoint_subids i" |
  "lookup M i = Some (elem_vert x) \<Longrightarrow> disjoint_subids i"
*)

end
end