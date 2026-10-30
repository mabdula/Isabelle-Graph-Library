theory Alternating_Forest_Imperative
  imports
    Alternating_Forest_Imperative_Spec
    Basic_Matching.Alternating_Forest_Executable
    Data_Structures.Fixed_Univ_Map_Specs_Imp
begin

provenance ai


section \<open>Imperative Implementation of Alternating Forests\<close>

text \<open>This is the imperative counterpart of @{locale forest_manipulation}. It is generic in the
      parent map and the vertex sets, exactly as the functional module, and it uses the
      imperative fixed-universe sets and maps only through their interfaces. All operations
      except @{term forest_empty_imp} work in place.

      A forest is represented by the imperative sets of its even and its odd vertices and the
      imperative parent map. The roots and the origins are not stored; they are ghost components of
      the functional forest, which the representation does not mention. The vertex sets are
      represented up to their abstraction, since the functional set of roots of an empty forest
      is given from outside, while the imperative one is built by insertions.\<close>

locale forest_imp =
  forest_manipulation K parent_invar parent_upd parent_get origin_invar origin_upd origin_get
    vset_invar vset_to_set vset_empty vset_insert vset_delete vset_isin vset_iterate
    parent_empty origin_empty nil +
  vs: fixed_univ_set_imp K vset_invar vset_to_set vset_empty vset_insert vset_delete
    vset_isin vset_assn vset_empty_imp vset_insert_imp vset_delete_imp vset_isin_imp +
  vit: fixed_univ_set_iterate_imp K vset_invar vset_to_set vset_assn lst
    is_it it_init it_has_next it_next +
  par: fixed_univ_map_imp K parent_invar parent_upd parent_get id parent_assn parent_upd_imp
    parent_get_imp +
  vsc: fixed_univ_set_clear_imp K vset_invar vset_to_set vset_empty vset_insert vset_delete
    vset_isin vset_assn vset_insert_imp vset_delete_imp vset_isin_imp vset_clear_imp +
  parc: fixed_univ_map_clear_imp K parent_invar parent_get id parent_assn parent_get_imp
    parent_empty parent_clear_imp +
  pari: fixed_univ_map_init_imp K parent_invar parent_get id parent_assn parent_get_imp
    parent_empty parent_empty_imp
  for K :: "'v::heap set" and parent_invar and parent_upd :: "'parent \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'parent"
    and parent_get origin_invar and origin_upd :: "'origin \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'origin"
    and origin_get vset_invar and vset_to_set :: "'vset \<Rightarrow> 'v set" and vset_empty
    and vset_insert :: "'v \<Rightarrow> 'vset \<Rightarrow> 'vset" and vset_delete vset_isin vset_iterate
    and parent_empty origin_empty nil
    and vset_assn :: "'vset \<Rightarrow> 'si \<Rightarrow> assn"
    and vset_empty_imp vset_insert_imp vset_delete_imp vset_isin_imp lst
    and is_it :: "'v set \<Rightarrow> 'si \<Rightarrow> 'v list \<Rightarrow> 'it \<Rightarrow> assn" and it_init it_has_next it_next
    and parent_assn :: "'parent \<Rightarrow> 'pi \<Rightarrow> assn" and parent_upd_imp parent_get_imp
    and vset_clear_imp :: "'si \<Rightarrow> unit Heap"
    and parent_clear_imp :: "'pi \<Rightarrow> unit Heap"
    and parent_empty_imp :: "'pi Heap"
begin

subsection \<open>Representation\<close>

definition "vs_assn V Vi =
   (\<exists>\<^sub>AS. vset_assn S Vi * \<up>(vset_invar S \<and> vset_invar V \<and> vset_to_set S = vset_to_set V))"

definition "forest_assn F Fi = (case Fi of (ei, oi, pai) \<Rightarrow>
   vs_assn (evens F) ei * vs_assn (odds F) oi * parent_assn (parents F) pai *
   \<up>(parent_invar (parents F)))"

text \<open>The iterators over the even and the odd vertices are those of the respective vertex
      set.\<close>

definition "forest_is_it p A Fi xs it = (case Fi of (ei, oi, pai) \<Rightarrow>
   (case p of Evens \<Rightarrow> is_it A ei xs it | Odds \<Rightarrow> is_it A oi xs it))"

subsection \<open>Programs\<close>

definition "forest_empty_imp =
  do { ei \<leftarrow> vset_empty_imp; oi \<leftarrow> vset_empty_imp; pai \<leftarrow> parent_empty_imp;
       return (ei, oi, pai) }"

definition "forest_clear_imp Fi = (case Fi of (ei, oi, pai) \<Rightarrow>
  do { vset_clear_imp ei; vset_clear_imp oi; parent_clear_imp pai; return Fi })"

definition "forest_add_root_imp v Fi = (case Fi of (ei, oi, pai) \<Rightarrow>
  do { vset_insert_imp v ei; return Fi })"

definition "forest_extend_imp x y z Fi = (case Fi of (ei, oi, pai) \<Rightarrow>
  do { vset_insert_imp y oi;
       vset_insert_imp z ei;
       parent_upd_imp pai y x;
       parent_upd_imp pai z y;
       return Fi })"

definition "evens_memb_imp v Fi = (case Fi of (ei, oi, pai) \<Rightarrow> vset_isin_imp ei v)"

definition "odds_memb_imp v Fi = (case Fi of (ei, oi, pai) \<Rightarrow> vset_isin_imp oi v)"

definition "forest_it_init p Fi = (case Fi of (ei, oi, pai) \<Rightarrow>
  (case p of Evens \<Rightarrow> it_init ei | Odds \<Rightarrow> it_init oi))"

partial_function \<^marker>\<open>provenance ai_human\<close> (heap) get_path_imp_loop :: "'pi \<Rightarrow> 'v array \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> nat Heap" where
  "get_path_imp_loop pai Ra k v = do {
     _ \<leftarrow> Array.upd k v Ra;
     u \<leftarrow> parent_get_imp pai v;
     (if u = nil then return (k + 1) else get_path_imp_loop pai Ra (k + 1) u) }"

definition "get_path_imp Fi Ra k v = (case Fi of (ei, oi, pai) \<Rightarrow> get_path_imp_loop pai Ra k v)"

subsection \<open>Correctness\<close>

lemma empty_forest_parts[simp]:
  "evens (empty_forest R) = R" "odds (empty_forest R) = vset_empty"
  "parents (empty_forest R) = parent_empty"
  by (auto simp: empty_forest_def)

lemma extend_forest_parts[simp]:
  "evens (extend_forest_even_unclassified F x y z) = vset_insert z (evens F)"
  "odds (extend_forest_even_unclassified F x y z) = vset_insert y (odds F)"
  "parents (extend_forest_even_unclassified F x y z) = parent_upd (parent_upd (parents F) y x) z y"
  by (auto simp: extend_forest_even_unclassified_def)

lemma \<^marker>\<open>provenance ai_human\<close> forest_empty_imp_rule:
  "\<lbrakk>vset_invar R; vset_to_set R = {}\<rbrakk> \<Longrightarrow>
   <emp> forest_empty_imp <forest_assn (empty_forest R)>"
  unfolding forest_empty_imp_def forest_assn_def vs_assn_def
  by (sep_auto simp: vset.fixed_univ_set_empty parent(1))

lemma \<^marker>\<open>provenance ai_human\<close> forest_clear_imp_rule:
  "\<lbrakk>vset_invar R; vset_to_set R = {}\<rbrakk> \<Longrightarrow>
   <forest_assn F Fi> forest_clear_imp Fi <forest_assn (empty_forest R)>"
  unfolding forest_clear_imp_def forest_assn_def vs_assn_def
  by (sep_auto split: prod.splits simp: vset.fixed_univ_set_empty parent(1))

lemma forest_empty_cong:
  "\<lbrakk>vset_invar R; vset_invar R'; vset_to_set R = vset_to_set R'\<rbrakk> \<Longrightarrow>
   forest_assn (empty_forest R) = forest_assn (empty_forest R')"
  by (auto simp: forest_assn_def vs_assn_def fun_eq_iff)

lemma \<^marker>\<open>provenance ai_human\<close> forest_add_root_imp_rule:
  "\<lbrakk>vset_invar R; vset_invar R'; vset_to_set R' = insert v (vset_to_set R)\<rbrakk> \<Longrightarrow>
   <forest_assn (empty_forest R) Fi> forest_add_root_imp v Fi <forest_assn (empty_forest R')>"
  unfolding forest_add_root_imp_def forest_assn_def vs_assn_def
  by (sep_auto split: prod.splits simp: vset.fixed_univ_set_insert dest: vset.fixed_univ_set_universe)

lemma forest_extension_precond_in_K:
  assumes "forest_extension_precond F M x y z"
  shows "y \<in> K" "z \<in> K"
  using forest_extension_precondD(5)[OF assms]
        invar_basicD(18)[OF forest_invarD(1)[OF forest_extension_precondD(1)[OF assms]]]
  by (auto simp: Vs_def)

lemma \<^marker>\<open>provenance ai_human\<close> forest_extend_imp_rule:
  assumes "forest_extension_precond F M x y z"
  shows "<forest_assn F Fi> forest_extend_imp x y z Fi
         <forest_assn (extend_forest_even_unclassified F x y z)>"
  using forest_extension_precond_in_K[OF assms]
  unfolding forest_extend_imp_def forest_assn_def vs_assn_def
  by (sep_auto split: prod.splits simp: vset.fixed_univ_set_insert parent_map.fixed_univ_map_upd_invar)

lemma \<^marker>\<open>provenance ai_human\<close> evens_memb_imp_rule:
  "v \<in> K \<Longrightarrow>
   <forest_assn F Fi> evens_memb_imp v Fi
   <\<lambda>r. forest_assn F Fi * \<up>(r \<longleftrightarrow> v \<in> vset_to_set (evens F))>"
  unfolding evens_memb_imp_def forest_assn_def vs_assn_def
  by (sep_auto split: prod.splits simp: vset.fixed_univ_set_isin)

lemma \<^marker>\<open>provenance ai_human\<close> odds_memb_imp_rule:
  "v \<in> K \<Longrightarrow>
   <forest_assn F Fi> odds_memb_imp v Fi
   <\<lambda>r. forest_assn F Fi * \<up>(r \<longleftrightarrow> v \<in> vset_to_set (odds F))>"
  unfolding odds_memb_imp_def forest_assn_def vs_assn_def
  by (sep_auto split: prod.splits simp: vset.fixed_univ_set_isin)

text \<open>The iterator of a vertex set refers to its abstraction only, so it iterates the vertex
      set whichever representation the existential in @{term vs_assn} chooses.\<close>

lemma \<^marker>\<open>provenance ai_human\<close> vs_it_init_rule:
  "<vs_assn V Vi> it_init Vi <\<lambda>it. vs_assn V Vi * is_it (vset_to_set V) Vi (lst (vset_to_set V)) it>"
  unfolding vs_assn_def
  by (sep_auto heap: vit.it_init_rule)

lemma \<^marker>\<open>provenance ai_human\<close> vs_it_next_rule:
  "<vs_assn V Vi * is_it (vset_to_set V) Vi (x # xs) it> it_next it
   <\<lambda>(y, it'). vs_assn V Vi * is_it (vset_to_set V) Vi xs it' * \<up>(y = x)>"
proof-
  have "<vset_assn S Vi * is_it (vset_to_set V) Vi (x # xs) it> it_next it
        <\<lambda>(y, it'). vset_assn S Vi * is_it (vset_to_set V) Vi xs it' * \<up>(y = x)>"
    if "vset_to_set S = vset_to_set V" for S
    using vit.it_next_rule[of S Vi x xs it] that
    by simp
  thus ?thesis
    unfolding vs_assn_def
    by sep_auto
qed

lemma \<^marker>\<open>provenance ai_human\<close> vs_it_has_next_rule:
  "<vs_assn V Vi * is_it (vset_to_set V) Vi xs it> it_has_next it
   <\<lambda>r. vs_assn V Vi * is_it (vset_to_set V) Vi xs it * \<up>(r \<longleftrightarrow> xs \<noteq> [])>"
proof-
  have "<vset_assn S Vi * is_it (vset_to_set V) Vi xs it> it_has_next it
        <\<lambda>r. vset_assn S Vi * is_it (vset_to_set V) Vi xs it * \<up>(r \<longleftrightarrow> xs \<noteq> [])>"
    if "vset_to_set S = vset_to_set V" for S
    using vit.it_has_next_rule[of S Vi xs it] that
    by simp
  thus ?thesis
    unfolding vs_assn_def
    by sep_auto
qed

lemma vs_quit_iteration: "vs_assn V Vi * is_it (vset_to_set V) Vi xs it \<Longrightarrow>\<^sub>A vs_assn V Vi"
  unfolding vs_assn_def ex_distrib_star[symmetric]
proof(rule ent_ex_preI, goal_cases)
  case (1 S)
  show ?case
  proof(cases "vset_invar S \<and> vset_invar V \<and> vset_to_set S = vset_to_set V")
    case True
    show ?thesis
      using True vit.quit_iteration[of S Vi xs it]
      by (intro ent_ex_postI[where x = S]; simp)
  next
    case False
    show ?thesis
      by (simp add: Eq_FalseI[OF False])
  qed
qed

lemma \<^marker>\<open>provenance ai_human\<close> forest_it_init_rule:
  "<forest_assn F Fi> forest_it_init p Fi
   <\<lambda>it. forest_assn F Fi *
         forest_is_it p (vset_to_set (case p of Evens \<Rightarrow> evens F | Odds \<Rightarrow> odds F)) Fi
           (lst (vset_to_set (case p of Evens \<Rightarrow> evens F | Odds \<Rightarrow> odds F))) it>"
  unfolding forest_it_init_def forest_assn_def forest_is_it_def
  by (cases p) (sep_auto split: prod.splits heap: vs_it_init_rule)+

lemma \<^marker>\<open>provenance ai_human\<close> forest_it_next_rule:
  "<forest_assn F Fi *
    forest_is_it p (vset_to_set (case p of Evens \<Rightarrow> evens F | Odds \<Rightarrow> odds F)) Fi (x # xs) it>
   it_next it
   <\<lambda>(y, it'). forest_assn F Fi *
      forest_is_it p (vset_to_set (case p of Evens \<Rightarrow> evens F | Odds \<Rightarrow> odds F)) Fi xs it' *
      \<up>(y = x)>"
  unfolding forest_assn_def forest_is_it_def
  by (cases p) (sep_auto split: prod.splits heap: vs_it_next_rule[of "evens F"],
                sep_auto split: prod.splits heap: vs_it_next_rule[of "odds F"])

lemma \<^marker>\<open>provenance ai_human\<close> forest_it_has_next_rule:
  "<forest_assn F Fi *
    forest_is_it p (vset_to_set (case p of Evens \<Rightarrow> evens F | Odds \<Rightarrow> odds F)) Fi xs it>
   it_has_next it
   <\<lambda>r. forest_assn F Fi *
      forest_is_it p (vset_to_set (case p of Evens \<Rightarrow> evens F | Odds \<Rightarrow> odds F)) Fi xs it *
      \<up>(r \<longleftrightarrow> xs \<noteq> [])>"
  unfolding forest_assn_def forest_is_it_def
  by (cases p) (sep_auto split: prod.splits heap: vs_it_has_next_rule[of "evens F"],
                sep_auto split: prod.splits heap: vs_it_has_next_rule[of "odds F"])

lemma forest_quit_iteration:
  "forest_assn F Fi *
   forest_is_it p (vset_to_set (case p of Evens \<Rightarrow> evens F | Odds \<Rightarrow> odds F)) Fi xs it
   \<Longrightarrow>\<^sub>A forest_assn F Fi"
  unfolding forest_assn_def forest_is_it_def
  by (cases p; cases Fi rule: prod_cases3; simp only: prod.case forest_part.case)
     ((sep_frame_fwd rule: vs_quit_iteration[of "evens F"], sep_auto),
      (sep_frame_fwd rule: vs_quit_iteration[of "odds F"], sep_auto))

lemma \<^marker>\<open>provenance ai_human\<close> get_path_imp_loop_rule:
  assumes "parent_spec_i.follow_dom (parent_lookup P) v"
  shows "\<lbrakk>parent_invar P; set (follow (parent_lookup P) v) \<subseteq> K;
          k + length (follow (parent_lookup P) v) \<le> length xs\<rbrakk> \<Longrightarrow>
    <parent_assn P pai * Ra \<mapsto>\<^sub>a xs> get_path_imp_loop pai Ra k v
    <\<lambda>k'. parent_assn P pai * Ra \<mapsto>\<^sub>a (take k xs @ follow (parent_lookup P) v @ drop k' xs) *
          \<up>(k' = k + length (follow (parent_lookup P) v))>"
  using assms
proof(induction arbitrary: k xs rule: parent_spec_i.follow.pinduct)
  case IH: (1 v)
  show ?case
  proof(cases "parent_lookup P v")
    case None
    hence path: "follow (parent_lookup P) v = [v]"
      by (simp add: parent_spec_i.follow.psimps[OF IH(1)])
    have "parent_get P v = nil"
      using None
      by (simp add: parent_lookup_def split: if_splits)
    thus ?thesis
      using IH(3-5)
      by (subst get_path_imp_loop.simps)
         (sep_auto simp: path upd_conv_take_nth_drop heap: par.fixed_univ_map_lookup_rule)
  next
    case (Some v')
    hence path: "follow (parent_lookup P) v = v # follow (parent_lookup P) v'"
      by (simp add: parent_spec_i.follow.psimps[OF IH(1)])
    have lookup: "parent_get P v = v'" "v' \<noteq> nil" "nil \<noteq> v'"
      using Some
      by (auto simp: parent_lookup_def split: if_splits)
    show ?thesis
      using IH(4,5)
      by (subst get_path_imp_loop.simps;
          sep_auto heap: IH(2)[OF Some IH(3)] par.fixed_univ_map_lookup_rule[OF IH(3)]
                   simp: lookup path take_Suc_conv_app_nth list_update_append)
  qed
qed

lemma get_path_follow:
  assumes "forest_invar M F"
  shows "get_path F v = follow (parent_lookup (parents F)) v"
proof-
  interpret parents_here: parent "parent_lookup (parents F)"
    using assms follow_dom_invar_parent_wf(1) forest_invarD(4)
    by auto
  show ?thesis
    using parents_here.follow_dom[folded follow_def]
    by (simp add: get_path_is_follow_impl
                  parents_here.follow_impl_is_follow[folded follow_def follow_impl_def])
qed

lemma \<^marker>\<open>provenance ai_human\<close> get_path_imp_rule:
  assumes "forest_invar M F" "v \<in> vset_to_set (evens F)" "k + length (get_path F v) \<le> length xs"
  shows "<forest_assn F Fi * Ra \<mapsto>\<^sub>a xs> get_path_imp Fi Ra k v
         <\<lambda>k'. forest_assn F Fi * Ra \<mapsto>\<^sub>a (take k xs @ get_path F v @ drop k' xs) *
               \<up>(k' = k + length (get_path F v))>"
proof-
  note basic = invar_basicD[OF forest_invarD(1)[OF assms(1)]]
  have "set (follow (parent_lookup (parents F)) v) \<subseteq> verts F"
    using assms(1,2) basic(6)
    by (intro path_follow_verts_in_verts_F[of M]) (auto dest: forest_invarD)
  moreover have "verts F \<subseteq> K"
    using basic(2,3,6) vset.fixed_univ_set_universe
    by blast
  ultimately have "set (follow (parent_lookup (parents F)) v) \<subseteq> K"
    by auto
  thus ?thesis
    using assms
    unfolding get_path_imp_def forest_assn_def get_path_follow[OF assms(1)]
    by (sep_auto split: prod.splits heap: get_path_imp_loop_rule
                 intro: follow_dom_invar_parent_wf(2) dest: forest_invarD(4))
qed

subsection \<open>Interpretation of the Imperative Forest Specification\<close>

lemma forest_fixed_univ_set_iterate_imp:
  "fixed_univ_set_iterate_imp K (\<lambda> F. vset_invar (case p of Evens \<Rightarrow> evens F | Odds \<Rightarrow> odds F))
     (\<lambda> F. vset_to_set (case p of Evens \<Rightarrow> evens F | Odds \<Rightarrow> odds F))
     forest_assn lst (forest_is_it p) (forest_it_init p) it_has_next it_next"
  by (intro fixed_univ_set_iterate_imp.intro fixed_univ_set_iterate_imp_axioms.intro
            vit.set_order_axioms)
     (rule vset.fixed_univ_set_universe forest_it_init_rule forest_it_next_rule
           forest_it_has_next_rule forest_quit_iteration | assumption)+

lemma alternating_forest_imp_spec:
  "alternating_forest_imp_spec vset_invar vset_to_set odds abstract_forest forest_invar
     roots extend_forest_even_unclassified empty_forest K vset_empty get_path evens lst
     forest_assn forest_is_it forest_it_init it_has_next it_next
     forest_empty_imp forest_clear_imp forest_add_root_imp forest_extend_imp
     evens_memb_imp odds_memb_imp get_path_imp"
  by (intro alternating_forest_imp_spec.intro alternating_forest_imp_spec_axioms.intro
            satisified vit.set_order_axioms
            forest_fixed_univ_set_iterate_imp[of Evens, unfolded forest_part.case]
            forest_fixed_univ_set_iterate_imp[of Odds, unfolded forest_part.case]
            forest_empty_imp_rule forest_clear_imp_rule forest_empty_cong forest_add_root_imp_rule
            satisfied_simple_extension_precond_same[THEN iffD1, THEN forest_extend_imp_rule]
            evens_memb_imp_rule odds_memb_imp_rule get_path_imp_rule)

end

end
