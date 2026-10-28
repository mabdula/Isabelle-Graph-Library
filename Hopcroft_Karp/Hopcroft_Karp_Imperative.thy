theory Hopcroft_Karp_Imperative
  imports Hopcroft_Karp_Builders_Imperative Hopcroft_Karp_Top_Loop_Imperative
begin

section \<open>The Imperative Hopcroft-Karp Algorithm\<close>

text \<open>The imperative top loop (@{locale Hopcroft_Karp_Loop_Imperative}) with the imperative phase
  of @{locale Hopcroft_Karp_Phase_Builders_Imperative} as its phase. The matching is represented by
  its mate function, as in the functional algorithm, and the augmentation along a path is
  implemented imperatively, mirroring @{const Matching_Augmentation_Specs.augment_impl}: the
  vertices of the first path of the store of paths are taken pairwise, and the mates of both
  vertices of a pair are updated. The primitive operations are the empty mate function and its
  update, and the operations which read the store of paths.\<close>

subsection \<open>The augmentation along a path\<close>

locale Hopcroft_Karp_Augment_Imperative_spec =
  fixes mate_update_imp :: "'mi \<Rightarrow> 'v::heap \<Rightarrow> 'v \<Rightarrow> 'mi Heap"
    and path_is_empty_imp :: "'ips \<Rightarrow> bool Heap"
    and path_pop_imp :: "'ips \<Rightarrow> ('v labelled_vtx \<times> 'ips) Heap"
    and paths_drop_imp :: "'ips \<Rightarrow> 'ips Heap"
begin

partial_function (heap) augment_path_imp :: "'mi \<Rightarrow> 'ips \<Rightarrow> ('mi \<times> 'ips) Heap" where
  "augment_path_imp Mi Psi =
     do { e \<leftarrow> path_is_empty_imp Psi;
          if e then return (Mi, Psi)
          else do { (u, Psi1) \<leftarrow> path_pop_imp Psi;
                    e' \<leftarrow> path_is_empty_imp Psi1;
                    if e' then return (Mi, Psi1)
                    else do { (v, Psi2) \<leftarrow> path_pop_imp Psi1;
                              Mi1 \<leftarrow> mate_update_imp Mi (vtx u) (vtx v);
                              Mi2 \<leftarrow> mate_update_imp Mi1 (vtx v) (vtx u);
                              augment_path_imp Mi2 Psi2 } } }"

definition "augment_first_imp Mi Psi =
  do { (Mi', Psi') \<leftarrow> augment_path_imp Mi Psi;
       Psi'' \<leftarrow> paths_drop_imp Psi';
       return (Mi', Psi'') }"

end

subsection \<open>The algorithm\<close>

locale Hopcroft_Karp_Imperative =
  Hopcroft_Karp_Phase_Builders_Imperative where lookup = lookup and c_lookup = c_lookup
    and mate_lookup = mate_lookup and lookup_dist = lookup_dist and mate_lookup_imp = mate_lookup_imp
    and g_add_edge_imp = g_add_edge_imp and c_add_edge_imp = c_add_edge_imp
    and src_insert_imp = src_insert_imp and vis_isin_imp = vis_isin_imp
    and dist_lookup_imp = dist_lookup_imp and paths_snoc_imp = paths_snoc_imp
    and set_insert_imp = set_insert_imp and stack_push_imp = stack_push_imp
    and stack_abstract = stack_abstract and dist_lookup = dist_lookup +
  Hopcroft_Karp_Augment_Imperative_spec where mate_update_imp = mate_update_imp
    and path_pop_imp = path_pop_imp
  for lookup :: "'adjmap \<Rightarrow> 'v::heap \<Rightarrow> 'vset option"
  and c_lookup :: "'cadjmap \<Rightarrow> 'v labelled_vtx \<Rightarrow> 'cvset option"
  and mate_lookup :: "'mate \<Rightarrow> 'v \<Rightarrow> 'v option"
  and lookup_dist :: "'dmap \<Rightarrow> 'v labelled_vtx \<Rightarrow> enat option"
  and mate_lookup_imp :: "'mi \<Rightarrow> 'v \<Rightarrow> 'v option Heap"
  and g_add_edge_imp :: "'imp_G \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'imp_G Heap"
  and c_add_edge_imp :: "'gi \<Rightarrow> 'v labelled_vtx \<Rightarrow> 'v labelled_vtx \<Rightarrow> 'gi Heap"
  and src_insert_imp :: "'v \<Rightarrow> 'imp_src \<Rightarrow> 'imp_src Heap"
  and vis_isin_imp :: "'imp_vis \<Rightarrow> 'v \<Rightarrow> bool Heap"
  and dist_lookup_imp :: "'imp_dist \<Rightarrow> 'v labelled_vtx \<Rightarrow> nat Heap"
  and paths_snoc_imp :: "'ips \<Rightarrow> 'v labelled_vtx \<Rightarrow> 'ips Heap"
  and set_insert_imp :: "'v labelled_vtx \<Rightarrow> 'si \<Rightarrow> unit Heap"
  and stack_push_imp :: "'stki \<Rightarrow> 'v labelled_vtx \<Rightarrow> unit Heap"
  and stack_abstract :: "'s \<Rightarrow> 'v labelled_vtx list"
  and dist_lookup :: "'dist \<Rightarrow> 'v labelled_vtx \<Rightarrow> nat"
  and mate_update_imp :: "'mi \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'mi Heap"
  and path_pop_imp :: "'ips \<Rightarrow> ('v labelled_vtx \<times> 'ips) Heap" +
  fixes mate_empty_imp :: "'mi Heap"
    and paths_is_empty_imp :: "'ips \<Rightarrow> bool Heap"
  assumes mate_empty_rule: "<emp> mate_empty_imp <mate_assn mate_empty>"
    and mate_update_rule:
      "\<And>M Mi u v. \<lbrakk>u \<in> univ; v \<in> univ\<rbrakk> \<Longrightarrow>
       <mate_assn M Mi> mate_update_imp Mi u v <mate_assn (mate_update u v M)>"
    and paths_is_empty_rule:
      "\<And>ps Psi. <paths_assn ps Psi> paths_is_empty_imp Psi <\<lambda>r. paths_assn ps Psi * \<up>(r \<longleftrightarrow> ps = [])>"
    and path_is_empty_rule:
      "\<And>q ps Psi. <paths_assn (q # ps) Psi> path_is_empty_imp Psi
                  <\<lambda>r. paths_assn (q # ps) Psi * \<up>(r \<longleftrightarrow> q = [])>"
    and path_pop_rule:
      "\<And>w q ps Psi. <paths_assn ((w # q) # ps) Psi> path_pop_imp Psi
                    <\<lambda>(w', Psi'). paths_assn (q # ps) Psi' * \<up>(w' = w)>"
    and paths_drop_rule: "\<And>q ps Psi. <paths_assn (q # ps) Psi> paths_drop_imp Psi <paths_assn ps>"
begin

sublocale loop: Hopcroft_Karp_Loop_Imperative_spec
  where empty_matching_imp = mate_empty_imp and phase_imp = "phase_imp.hopcroft_karp_phase_imp Ei Vi"
    and paths_is_empty_imp = paths_is_empty_imp and augment_first_imp = augment_first_imp
  for Ei Vi .

text \<open>The imperative Hopcroft-Karp algorithm, for the edges and the vertices given as arrays.\<close>

definition "hopcroft_karp_imp Ei Vi = loop.Hopcroft_Karp_Loop_run_imp Ei Vi"

subsubsection \<open>The augmentation along a path\<close>

lemma path_pop_rule':
  "<paths_assn ((w # q) # ps) Psi> path_pop_imp Psi <\<lambda>r. paths_assn (q # ps) (snd r) * \<up>(fst r = w)>"
  using path_pop_rule[of w q ps Psi]
  by (simp add: case_prod_beta')

lemma augment_path_imp_rule:
  "set (map vtx q) \<subseteq> univ \<Longrightarrow>
   <mate_assn M Mi * paths_assn (q # ps) Psi> augment_path_imp Mi Psi
   <\<lambda>(Mi', Psi'). mate_assn (mate_augment M (map vtx q)) Mi' * paths_assn ([] # ps) Psi'>"
proof(induction q arbitrary: M Mi Psi rule: induct_list012, goal_cases)
  case (1 M Mi Psi)
  thus ?case
    by (subst augment_path_imp.simps) (sep_auto heap: path_is_empty_rule)
next
  case (2 x M Mi Psi)
  thus ?case
    by (subst augment_path_imp.simps) (sep_auto heap: path_is_empty_rule path_pop_rule')
next
  case (3 x y zs M Mi Psi)
  thus ?case
    by (subst augment_path_imp.simps)
       (sep_auto heap: path_is_empty_rule path_pop_rule' mate_update_rule 3(1) simp: Let_def)
qed

lemma augment_first_imp_rule:
  "set (map vtx q) \<subseteq> univ \<Longrightarrow>
   <mate_assn M Mi * paths_assn (q # ps) Psi> augment_first_imp Mi Psi
   <\<lambda>(Mi', Psi'). mate_assn (mate_augment M (map vtx q)) Mi' * paths_assn ps Psi'>"
  by (sep_auto heap: augment_path_imp_rule paths_drop_rule simp: augment_first_imp_def)

subsubsection \<open>Correctness\<close>

text \<open>For an input graph which satisfies @{const Hopcroft_Karp_Input.Hopcroft_Karp_axiom}, given by
  its edges and its vertices within the universe, and a stack capacity of at least twice the
  number of vertices.\<close>

context
  fixes Gin vs edges and Ei :: "('v \<times> 'v) array" and Vi :: "'v array"
  assumes axiom: "hk_input.Hopcroft_Karp_axiom Gin vs"
    and edges: "set edges = G.digraph_abs Gin"
    and input_univ: "dVs (G.digraph_abs Gin) \<subseteq> univ"
    and capacity: "2 * length vs \<le> cap"
begin

lemma input_bipartite: obtains X Y where "bipartite (hk_input.ugraph_abs Gin) X Y"
  using axiom
  unfolding hk_input.Hopcroft_Karp_axiom_def
  by blast

lemma augmenting_path_univ:
  assumes "graph_augmenting_path (hk_input.ugraph_abs Gin) M p"
  shows "set p \<subseteq> univ"
proof-
  obtain X Y where bip: "bipartite (hk_input.ugraph_abs Gin) X Y"
    by (rule input_bipartite)
  have "set p \<subseteq> Vs (hk_input.ugraph_abs Gin)"
    using assms
    by (auto intro: mem_path_Vs)
  thus ?thesis
    using Vs_ugraph_abs[OF axiom bip edges] input_props(5)[OF axiom bip edges] input_univ
    by simp
qed

interpretation hk_loop: Hopcroft_Karp_Loop_Imperative
  where lookup = lookup and G = Gin and vertex_list = vs and empty_matching = mate_empty
    and augment = mate_augment and matching_invar = "mate_invar (hk_input.ugraph_abs Gin)"
    and matching_abstract = mate_matching and phase = "hopcroft_karp_phase edges vs"
    and empty_matching_imp = mate_empty_imp
    and phase_imp = "phase_imp.hopcroft_karp_phase_imp Ei Vi"
    and paths_is_empty_imp = paths_is_empty_imp and augment_first_imp = augment_first_imp
    and matching_assn = mate_assn
    and paths_assn = "\<lambda>ps Psi. \<exists>\<^sub>Aqs. paths_assn qs Psi * \<up>(map (map vtx) qs = ps)"
    and input_assn = "Ei \<mapsto>\<^sub>a edges * Vi \<mapsto>\<^sub>a vs"
proof(unfold_locales, goal_cases)
  case (1 M)
  thus ?case
    by (rule mate_invarD(4))
next
  case 2
  show ?case
    using mate_empty_props by auto
next
  case 3
  show ?case
    using mate_empty_props by auto
next
  case (4 M p)
  thus ?case
    using mate_augmentation_correct by auto
next
  case (5 M p)
  thus ?case
    using mate_augmentation_correct by auto
next
  case (6 M p)
  obtain X Y where bip: "bipartite (hk_input.ugraph_abs Gin) X Y"
    by (rule input_bipartite)
  show ?case
    using 6(2,3)
    by (rule phase_sound[OF axiom bip edges])
next
  case (7 M)
  obtain X Y where bip: "bipartite (hk_input.ugraph_abs Gin) X Y"
    by (rule input_bipartite)
  show ?case
    using 7(2)
    by (rule phase_disjoint[OF axiom bip edges])
next
  case (8 M)
  obtain X Y where bip: "bipartite (hk_input.ugraph_abs Gin) X Y"
    by (rule input_bipartite)
  show ?case
    using 8(2,3)
    by (rule phase_complete[OF axiom bip edges])
next
  case 9
  show ?case
    by (rule axiom)
next
  case 10
  show ?case
    by (rule mate_empty_rule)
next
  case (11 M Mi)
  obtain X Y where bip: "bipartite (hk_input.ugraph_abs Gin) X Y"
    by (rule input_bipartite)
  show ?case
    by (sep_auto heap: phase_imp.hopcroft_karp_phase_imp_rule[OF axiom bip edges input_univ capacity 11])
next
  case (12 ps Psi)
  show ?case
    by (sep_auto heap: paths_is_empty_rule)
next
  case (13 M Mi p ps Psi)
  have "set p \<subseteq> univ"
    using 13(2)
    by (rule augmenting_path_univ)
  thus ?case
    by (sep_auto heap: augment_first_imp_rule simp: map_eq_Cons_conv)
qed

text \<open>The imperative algorithm computes the matching and the number of phases of the functional
  algorithm @{const Hopcroft_Karp_Loop.Hopcroft_Karp_Loop_run_impl}.\<close>

theorem hopcroft_karp_imp_refine:
  "<Ei \<mapsto>\<^sub>a edges * Vi \<mapsto>\<^sub>a vs> hopcroft_karp_imp Ei Vi
   <\<lambda>si. Ei \<mapsto>\<^sub>a edges * Vi \<mapsto>\<^sub>a vs *
         mate_assn (current_matching hk_loop.Hopcroft_Karp_Loop_run_impl) (i_matching si) *
         \<up>(i_phases si = phases hk_loop.Hopcroft_Karp_Loop_run_impl)>"
  unfolding hopcroft_karp_imp_def hk_loop.Hopcroft_Karp_Loop_run_impl_def
            hk_loop.Hopcroft_Karp_Loop_impl_to_Hopcroft_Karp_Loop
  by (rule hk_loop.Hopcroft_Karp_Loop_run_imp_rule)

text \<open>The imperative algorithm computes a maximum cardinality matching of the input graph.\<close>

theorem hopcroft_karp_imp_correct:
  "<Ei \<mapsto>\<^sub>a edges * Vi \<mapsto>\<^sub>a vs> hopcroft_karp_imp Ei Vi
   <\<lambda>si. \<exists>\<^sub>AM. Ei \<mapsto>\<^sub>a edges * Vi \<mapsto>\<^sub>a vs * mate_assn M (i_matching si) *
              \<up>(mate_invar (hk_input.ugraph_abs Gin) M \<and>
                 max_card_matching (hk_input.ugraph_abs Gin) (mate_matching M))>"
  unfolding hopcroft_karp_imp_def
  by (rule hk_loop.Hopcroft_Karp_Loop_run_imp_correct)

end

end

end
