theory BFS_Instantiation
  imports BFS_Refinement Data_Structures.Imp_Bool_Set Directed_Set_Graphs.CSR_Edge_Input
begin

section \<open>An Instantiation of the Imperative BFS\<close>

text \<open>The locale @{locale BFS_lists_instance} is instantiated with purely imperative data
      structures of fixed size, allocated once:

        \<^item> the visited set is a Boolean array over the vertices \<open>{..<n}\<close>
          (@{theory Data_Structures.Imp_Bool_Set}),
        \<^item> distances are an array over the vertices, parents a parent array
          (@{theory Graph_Algorithms_Dev.Parent_Array}),
        \<^item> the frontier is an array with a fill pointer and a buffer array of the same size, and
        \<^item> the graph is in compressed sparse row (CSR) form, built from the arrays of tails and
          heads by the buildup @{const csr_build_heads} of
          @{theory Directed_Set_Graphs.CSR_Edge_Input}: an array of heads grouped by their tails,
          together with the array of the starts of the groups. The neighbours of a vertex are
          folded over by @{const csr_fold_imp}.\<close>


section \<open>The Code\<close>

text \<open>The global interpretations of the code locales only fix operations and have no
      assumptions. The graph handle is the iterator over the neighbours itself: the code takes an
      arbitrary iterator \<open>Nb\<close>, e.g.\ one that skips some edges of a larger graph.\<close>

type_synonym bfs_nbs_iterator =
  "nat \<Rightarrow> (nat \<Rightarrow> nat array \<times> nat \<Rightarrow> (nat array \<times> nat) Heap) \<Rightarrow> nat array \<times> nat \<Rightarrow>
   (nat array \<times> nat) Heap"

global_interpretation bfs_sub_code: BFS_subprocedures_lists_code bool_array_set_isin_imp
    bool_array_set_insert_imp parent_array_extend_imp "\<lambda>Nb :: bfs_nbs_iterator. Nb"
  defines bfs_inner_loop = bfs_sub_code.inner_loop
    and bfs_outer_loop = bfs_sub_code.outer_loop
    and bfs_src_to_cf = bfs_sub_code.imp_src_to_cf
    and bfs_cf_is_empty = bfs_sub_code.imp_cf_is_empty
    and bfs_set_srcs_visited = bfs_sub_code.set_srcs_visited
    and bfs_set_dists = bfs_sub_code.set_all_dists_in_front_imp
    and bfs_round = bfs_sub_code.next_frontier_current_parents_imp
  done

global_interpretation bfs_code: BFS_Imperative_spec bfs_src_to_cf bfs_set_srcs_visited
    "bfs_round Nb" bfs_cf_is_empty "\<lambda>v Vi. bool_array_set_isin_imp Vi v" bfs_set_dists
    par_init_imp
  for Nb :: bfs_nbs_iterator
  defines bfs_loop = bfs_code.BFS_par_imp
    and bfs_init = bfs_code.initial_state_imp
    and bfs_check_reachable = bfs_code.check_reachable
    and bfs_visited_dists_parents = bfs_code.visited_dists_parents_imp
  done

declare bfs_code.BFS_par_imp.simps[code] parent_array_get_path_imp.simps[code]

text \<open>Path reconstruction on the parent array: the path from a vertex back to a source is
      written into the first cells of the array @{term Ra}.\<close>

definition "bfs_path Pa Ra v = parent_array_get_path_imp Pa Ra 0 v"

text \<open>The BFS on a CSR folds over the neighbours by @{const csr_fold_imp}. The iterator is fixed
      at code generation time by code equations, so the generated code calls the fold directly.\<close>

definition "bfs_csr_inner_loop Gi = bfs_inner_loop (csr_fold_imp Gi)"

definition "bfs_csr_outer_loop Gi = bfs_outer_loop (csr_fold_imp Gi)"

definition "bfs_csr_round Gi = bfs_round (csr_fold_imp Gi)"

definition "bfs_csr_loop Gi = bfs_loop (csr_fold_imp Gi)"

definition "bfs_csr_visited_dists_parents Gi = bfs_visited_dists_parents (csr_fold_imp Gi)"

lemmas bfs_csr_inner_loop_code[code] =
  bfs_sub_code.inner_loop.simps[of "csr_fold_imp Gi" for Gi, folded bfs_csr_inner_loop_def]

lemmas bfs_csr_outer_loop_code[code] =
  bfs_sub_code.outer_loop.simps[of "csr_fold_imp Gi" for Gi,
    folded bfs_csr_outer_loop_def bfs_csr_inner_loop_def]

lemmas bfs_csr_round_code[code] =
  bfs_sub_code.next_frontier_current_parents_imp.simps[of "csr_fold_imp Gi" for Gi,
    folded bfs_csr_round_def bfs_csr_outer_loop_def]

lemmas bfs_csr_loop_code[code] =
  bfs_code.BFS_par_imp.simps[of "csr_fold_imp Gi" for Gi, folded bfs_csr_loop_def bfs_csr_round_def]

lemmas bfs_csr_visited_dists_parents_code[code] =
  bfs_code.visited_dists_parents_imp_def[of "csr_fold_imp Gi" for Gi,
    folded bfs_csr_visited_dists_parents_def bfs_csr_loop_def]

text \<open>The final program takes the number of vertices, the arrays of tails and heads and the array
      of distinct sources. It builds the CSR, allocates all other data structures, copies the
      sources into the first frontier array and runs the BFS. The distance and the parent array are
      initialised with the identity. It returns the visited set, the distances and the parents.\<close>

definition bfs_csr_run :: "nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow>
                            (bool array \<times> nat array \<times> nat array) Heap" where
  "bfs_csr_run n Fa Ta Sa = do {
     Gi \<leftarrow> csr_build_heads n (Fa, Ta) 0;
     k \<leftarrow> Array.len Sa;
     Fr \<leftarrow> Array.new (Suc n) 0;
     copy_prefix_imp k Sa Fr 0;
     Bf \<leftarrow> Array.new (Suc n) 0;
     Vi \<leftarrow> Array.new n False;
     Da \<leftarrow> Array.make n id;
     Pa \<leftarrow> Array.make n id;
     bfs_csr_visited_dists_parents Gi Vi (Fr, k, Bf) Da Pa }"

export_code bfs_csr_run bfs_path checking SML_imp


section \<open>Correctness for an Arbitrary Iterator\<close>

text \<open>The BFS on preallocated arrays with an arbitrary iterator. The visited set and the parent
      array are kept at fixed handles, so that the arrays can be reused by repeated searches.\<close>

lemma len_intro: "length l = m \<Longrightarrow> a \<mapsto>\<^sub>a l \<Longrightarrow>\<^sub>A len_assn m a"
  unfolding len_assn_def by (rule ent_ex_postI[where x = l]) simp

lemma pull_len:
  assumes "\<And> l. length l = m \<Longrightarrow> <a \<mapsto>\<^sub>a l * Fm> c <Q>"
  shows "<len_assn m a * Fm> c <Q>"
  unfolding len_assn_def
  by (sep_auto heap: assms)

text \<open>The graph is a map @{term G} of the vertices below @{term n} to their neighbour lists, with
      a finite domain. The iterator @{term nbs} on a handle @{term Gh} folds over the neighbours of
      a vertex in the order of its list; the assertion @{term ga} holds the data of the iterator.\<close>

locale bfs_iterator_arrays =
  fixes n :: nat
    and G :: "nat \<Rightarrow> nat list option"
    and nbs :: "'gh \<Rightarrow> bfs_nbs_iterator"
    and ga :: "'gh \<Rightarrow> assn"
  assumes G_bound: "dVs {(u, v). v \<in> set (case G u of None \<Rightarrow> [] | Some vs \<Rightarrow> vs)} \<subseteq> {..<n}"
    and G_finite: "finite (dom G)"
    and nbs_rule: "\<lbrakk>u < n; \<And> acc acci x. x \<in> set (case G u of None \<Rightarrow> [] | Some vs \<Rightarrow> vs) \<Longrightarrow>
               <A acc acci> fi x acci <\<lambda> r. A (f x acc) r>\<rbrakk> \<Longrightarrow>
         <ga Gh * (A :: nat list \<times> nat list \<times> (nat \<Rightarrow> nat option) \<Rightarrow> nat array \<times> nat \<Rightarrow> assn) acc acci>
            nbs Gh u fi acci
         <\<lambda> r. ga Gh * A (foldl (\<lambda> acc x. f x acc) acc (case G u of None \<Rightarrow> [] | Some vs \<Rightarrow> vs)) r>"
begin

text \<open>The edges of the graph.\<close>

abbreviation "nbs_edges \<equiv> {(u, v). v \<in> set (case G u of None \<Rightarrow> [] | Some vs \<Rightarrow> vs)}"

lemma nbs_fold_imp:
  "indexed_set_fold_imp (\<lambda>G'. G' = G) (\<lambda>G u. set (case G u of None \<Rightarrow> [] | Some vs \<Rightarrow> vs))
     {..<n} (\<lambda>G u f (acc :: nat list \<times> nat list \<times> (nat \<Rightarrow> nat option)).
                foldl (\<lambda>acc x. f x acc) acc (case G u of None \<Rightarrow> [] | Some vs \<Rightarrow> vs))
     (\<lambda>_ Nb. ga Gh * \<up>(Nb = nbs Gh)) (\<lambda>Nb :: bfs_nbs_iterator. Nb)"
proof (unfold_locales, goal_cases)
  case (1 C i)
  show ?case by (intro exI[of _ "case C i of None \<Rightarrow> [] | Some vs \<Rightarrow> vs"]) simp
next
  case (2 C i acc_assn fi f Ci acc acci)
  have r: "<ga Gh * acc_assn acc acci> nbs Gh i fi acci
           <\<lambda>r. ga Gh * acc_assn (foldl (\<lambda>acc x. f x acc) acc (case C i of None \<Rightarrow> [] | Some vs \<Rightarrow> vs)) r>"
    unfolding 2(1) by (rule nbs_rule) (use 2(2) in simp, rule 2(3), simp only: 2(1))
  show ?case
    by (sep_auto heap: r)
qed

text \<open>The subprocedures of the BFS with the iterator on the handle @{term Gh}, the visited set at
      the handle @{term Vh} and the parent array at the handle @{term Pa}.\<close>

interpretation sub: BFS_subprocedures_lists where vis_isin_imp = bool_array_set_isin_imp
  and vis_insert_imp = bool_array_set_insert_imp and nbs_fold_imp = "\<lambda>Nb :: bfs_nbs_iterator. Nb"
  and par_extend_imp = parent_array_extend_imp and par_U = "{..<n}"
  and par_abstract = parent_array.pa_graph and par_extend = parent_array.pa_extend
  and par_invar = "parent_array.pa_invar n" and par_roots = parent_array.pa_roots
  and par_assn = "\<lambda>p pi. parent_array.pa_parent_assn n p pi * \<up>(pi = Pa)"
  and U = "{..<n}" and vis_invar = "\<lambda>X. X \<subseteq> {..<n}" and vis_abstract = id
  and vis_empty = "{}" and vis_insert = insert and vis_delete = "\<lambda>x X. X - {x}"
  and vis_isin = "\<lambda>X x. x \<in> X" and vis_assn = "\<lambda>X a. bool_array_set_assn n X a * \<up>(a = Vh)"
  and vis_delete_imp = bool_array_set_delete_imp
  and nbs_invar = "\<lambda>G'. G' = G" and K = "{..<n}"
  and nbs_fold = "\<lambda>G u f acc. foldl (\<lambda>acc x. f x acc) acc (case G u of None \<Rightarrow> [] | Some vs \<Rightarrow> vs)"
  and graph_assn = "\<lambda>_ Nb. ga Gh * \<up>(Nb = nbs Gh)" for Vh Gh Pa
  by (intro BFS_subprocedures_lists.intro bool_array_set_at nbs_fold_imp parent_array_at(1)
            BFS_subprocedures_lists_axioms.intro)
     simp_all

lemma Vs_G: "BFS_subprocedures_lists.Vs G = dVs nbs_edges"
  by (simp only: sub.Vs_def dVs_def sub.verts_rw ex_simps)

lemma card_Vs: "card (BFS_subprocedures_lists.Vs G) \<le> n"
  unfolding Vs_G using card_mono[OF finite_lessThan G_bound] by (simp only: card_lessThan)

lemmas imp_dist_assn_char = sub.imp_dist_assn_char

text \<open>The distance and the parent array keep their lengths.\<close>

lemma dist_len: "BFS_subprocedures_lists.imp_dist_assn n Da G d di \<Longrightarrow>\<^sub>A len_assn n Da"
  unfolding imp_dist_assn_char len_assn_def by sep_auto

lemma par_len: "parent_array.pa_parent_assn n p Pa \<Longrightarrow>\<^sub>A len_assn n Pa"
  unfolding parent_array.pa_parent_assn_def len_assn_def by sep_auto

text \<open>The BFS of @{locale BFS_lists_instance} on these subprocedures.\<close>

interpretation inst: BFS_lists_instance where vis_isin_imp = bool_array_set_isin_imp
  and vis_insert_imp = bool_array_set_insert_imp and nbs_fold_imp = "\<lambda>Nb :: bfs_nbs_iterator. Nb"
  and U = "{..<n}" and vis_invar = "\<lambda>X. X \<subseteq> {..<n}" and vis_abstract = id
  and vis_empty = "{}" and vis_insert = insert and vis_delete = "\<lambda>x X. X - {x}"
  and vis_isin = "\<lambda>X x. x \<in> X" and vis_assn = "\<lambda>X a. bool_array_set_assn n X a * \<up>(a = Vh)"
  and vis_delete_imp = bool_array_set_delete_imp
  and nbs_invar = "\<lambda>G'. G' = G" and K = "{..<n}"
  and nbs_fold = "\<lambda>G u f acc. foldl (\<lambda>acc x. f x acc) acc (case G u of None \<Rightarrow> [] | Some vs \<Rightarrow> vs)"
  and graph_assn = "\<lambda>_ Nb. ga Gh * \<up>(Nb = nbs Gh)"
  and G = G and Gi = "nbs Gh" and srcs = "rev ss"
  and N = n and par_assn = "\<lambda>p pi. parent_array.pa_parent_assn n p pi * \<up>(pi = Pa)"
  and Fr = Fr and Bf = Bf and Da = Da for Vh Gh Fr Bf Da Pa ss
  by (intro BFS_lists_instance.intro sub.BFS_subprocedures_lists_axioms parent_array_at(2)
            BFS_lists_instance_axioms.intro parent_array_at(3))
     (simp_all only: Vs_G G_bound simp_thms)

lemma code_eqs[simp]:
  "inst.imp_bfs.visited_dists_parents_imp Gh = bfs_visited_dists_parents (nbs Gh)"
  by (simp add: bfs_visited_dists_parents_def bfs_src_to_cf_def bfs_set_srcs_visited_def
                bfs_round_def bfs_cf_is_empty_def bfs_set_dists_def)

lemma digraph_abs_G[simp]: "sub.Graph.digraph_abs G = nbs_edges"
  unfolding sub.Graph.digraph_abs_def sub.Graph.neighbourhood_def by (rule refl)

text \<open>The functional BFS on the graph, with the parents in a parent array below @{term n}.\<close>

lemma distance_parents:
  "\<exists> exp_tree nfc dist_invar parent_abstract parent_invar par_U par_roots.
     BFS_3.BFS_distance_parents (\<lambda> x. None) (\<lambda> x G. fun_upd G x None) Cons (\<lambda> xs x. x \<in> set xs) set hd
       (\<lambda> x N G. fun_upd G x (Some N)) (\<lambda> G. True) [] (\<lambda> x xs. filter (\<lambda> y. x \<noteq> y) xs) (\<lambda> _. True)
       append (\<lambda> xs ys. filter (\<lambda> y. y \<in> set ys) xs) (\<lambda> xs ys. filter (\<lambda> y. y \<notin> set ys) xs)
       G exp_tree nfc distinct id (\<lambda> d x. d x) dist_invar (\<lambda> G x. G x)
       (\<lambda> d S n. \<lambda> y. if y \<in> set S then n else d y) parent_abstract parent_invar par_U
       (parent_array.pa_get_path n) par_roots parent_array.pa_init
       (BFS_subprocedures_lists.next_frontier_current_parents parent_array.pa_extend G)"
  using inst.imp_bfs.BFS_distance_parents_axioms unfolding fun_upd_def by blast

text \<open>The graphs and vertex sets of the functional BFS are maps to lists and lists.\<close>

lemmas graph_specs = sub.Graph.Pair_Graph_Specs_axioms
  and set_specs = sub.set_ops.Set2_axioms

text \<open>The searches from a list of sources: distinct, nonempty and in the graph. The sources are
      the first cells of the frontier array, so the list of the BFS is their reverse.\<close>

definition "bfs_sources ss \<longleftrightarrow> distinct ss \<and> ss \<noteq> [] \<and> set ss \<subseteq> dVs nbs_edges"

context
  fixes ss
  assumes b: "bfs_sources ss"
begin

lemma srcs_length: "length ss \<le> n"
proof -
  have "distinct ss" "set ss \<subseteq> {..<n}"
    using b G_bound unfolding bfs_sources_def by blast+
  from card_mono[OF finite_lessThan this(2)] show ?thesis
    by (simp only: card_lessThan distinct_card[OF \<open>distinct ss\<close>])
qed

lemma BFS_axiom: "inst.imp_bfs.BFS_axiom ss"
proof-
  have nb: "Pair_Graph.neighbourhood nbs_edges u = set (case G u of None \<Rightarrow> [] | Some vs \<Rightarrow> vs)" for u
    unfolding Pair_Graph.neighbourhood_def by (rule set_eqI) (simp only: mem_Collect_eq case_prod_conv)
  have s: "distinct ss \<and> ss \<noteq> [] \<and> set ss \<subseteq> dVs nbs_edges"
    using b unfolding bfs_sources_def .
  show ?thesis
    unfolding inst.imp_bfs.BFS_axiom_def digraph_abs_G sub.Graph.graph_inv_def
              sub.Graph.finite_graph_def sub.Graph.finite_vsets_def set_rev distinct_rev
              set_empty dom_def[symmetric] nb
    by (intro conjI allI impI TrueI finite_set G_finite conjunct1[OF s] conjunct1[OF conjunct2[OF s]]
              conjunct2[OF conjunct2[OF s]])
qed

definition "fin = inst.imp_bfs.BFS_par_impl (inst.imp_bfs.initial_par_state ss)"

text \<open>The final state of the functional BFS: the visited vertices are those reachable from the
      sources, with their distances; the parents of the visited non-sources lie on shortest
      paths; and the parent map yields a shortest path to every visited vertex.\<close>

lemmas fin_correct = inst.imp_bfs.BFS_par_correct[OF BFS_axiom fin_def, unfolded digraph_abs_G set_rev]

lemmas fin_path_length = inst.imp_bfs.get_path_length[OF BFS_axiom fin_def, unfolded digraph_abs_G set_rev]

lemma cf_len: "sub.imp_cf_assn (Suc n) Fr Bf G cf cfi \<Longrightarrow>\<^sub>A len_assn (Suc n) Fr * len_assn (Suc n) Bf"
  apply (cases cfi)
  apply (simp only: sub.imp_cf_assn.simps doubleton_eq_iff)
  apply (intro ent_ex_preI)
  apply (unfold ent_pure_pre_iff)
  apply (intro impI)
  apply (elim conjE disjE)
  apply (hypsubst)
  apply (rule ent_star_mono; rule len_intro; assumption)
  apply (hypsubst)
  apply (subst mult.commute)
  by (rule ent_star_mono; rule len_intro; assumption)

lemma par_intro: "len_assn n Pa \<Longrightarrow>\<^sub>A parent_array.pa_parent_assn n Map.empty Pa * \<up>(Pa = Pa)"
  unfolding len_assn_def parent_array.pa_parent_assn_def by sep_auto

text \<open>The BFS on the arrays allocated by the caller: the visited array @{term Vi}, the frontier
      array @{term Fr} whose first cells hold the sources, the buffer @{term Bf}, the distance
      array @{term Da} initialised with the identity, and the parent array @{term Pa}. Afterwards,
      the visited array, the distances and the parents are those of the final state @{const fin};
      the frontier and the buffer keep their lengths and can be reused.\<close>

lemma bfs_rule[bfs_heap_rules]:
  assumes "length fl = Suc n" "take (length ss) fl = ss" "length bl = Suc n"
  shows "<bool_array_set_assn n {} Vi * Fr \<mapsto>\<^sub>a fl * Bf \<mapsto>\<^sub>a bl * Da \<mapsto>\<^sub>a map id [0..<n] *
          len_assn n Pa * ga Gh>
           bfs_visited_dists_parents (nbs Gh) Vi (Fr, length ss, Bf) Da Pa
         <\<lambda> r. ga Gh * bool_array_set_assn n (set (BFS_dist_state.visited fin)) Vi *
            sub.imp_dist_assn n Da G (BFS_dist_state.dists fin) Da *
            parent_array.pa_parent_assn n (BFS_par_state.parent fin) Pa *
            len_assn (Suc n) Fr * len_assn (Suc n) Bf * \<up>(r = (Vi, Da, Pa))>"
proof-
  have sV: "set ss \<subseteq> BFS_subprocedures_lists.Vs G"
    using b unfolding bfs_sources_def Vs_G by (elim conjE)
  note ls = srcs_length
  have ids: "\<forall>i \<in> BFS_subprocedures_lists.Vs G.
      i < length (map id [0..<n]) \<and> id i = map id [0..<n] ! i"
    using G_bound by (auto simp only: Vs_G id_def map_ident length_upt diff_zero
        nth_upt add_0 subset_iff lessThan_iff)
  have v: "bool_array_set_assn n {} Vi \<Longrightarrow>\<^sub>A sub.is_visited_set Vi (BFS_subprocedures_lists.Vs G) (set []) Vi"
    unfolding sub.is_visited_set_def
    by (rule ent_ex_postI[where x = "{}"]) sep_auto
  have s: "Fr \<mapsto>\<^sub>a fl * Bf \<mapsto>\<^sub>a bl \<Longrightarrow>\<^sub>A sub.imp_src_assn (Suc n) Fr Bf G (rev ss) (Fr, length ss, Bf)"
    by (rule sub.imp_src_assn_intro) (use assms card_Vs ls sV in simp_all)
  have pre: "bool_array_set_assn n {} Vi * Fr \<mapsto>\<^sub>a fl * Bf \<mapsto>\<^sub>a bl * Da \<mapsto>\<^sub>a map id [0..<n] *
             len_assn n Pa * ga Gh
             \<Longrightarrow>\<^sub>A sub.is_visited_set Vi (BFS_subprocedures_lists.Vs G) (set []) Vi *
             sub.imp_src_assn (Suc n) Fr Bf G (rev ss) (Fr, length ss, Bf) *
             sub.imp_dist_assn n Da G id Da *
             (parent_array.pa_parent_assn n Map.empty Pa * \<up>(Pa = Pa)) * (ga Gh * \<up>(nbs Gh = nbs Gh))"
    by (rule ent_trans[OF _ ent_star_mono[OF ent_star_mono[OF ent_star_mono[OF ent_star_mono[OF v s]
           sub.imp_dist_assn_intro[OF ids] ] par_intro] ent_refl]])
       (simp_all add: mult_ac)
  have c: "(\<exists>\<^sub>A cf cfi. sub.imp_cf_assn (Suc n) Fr Bf G cf cfi)
           \<Longrightarrow>\<^sub>A len_assn (Suc n) Fr * len_assn (Suc n) Bf"
    by (intro ent_ex_preI) (rule cf_len)
  have post: "ga Gh * \<up>(nbs Gh = nbs Gh) * sub.is_visited_set Vi (BFS_subprocedures_lists.Vs G) (set V) visi *
              sub.imp_dist_assn n Da G d di * (parent_array.pa_parent_assn n p pari * \<up>(pari = Pa)) *
              (\<exists>\<^sub>A cf cfi. sub.imp_cf_assn (Suc n) Fr Bf G cf cfi)
              \<Longrightarrow>\<^sub>A ga Gh * bool_array_set_assn n (set V) Vi * sub.imp_dist_assn n Da G d Da *
              parent_array.pa_parent_assn n p Pa * len_assn (Suc n) Fr * len_assn (Suc n) Bf *
              \<up>((visi, di, pari) = (Vi, Da, Pa))"
    for V visi d di p pari
    unfolding sub.is_visited_set_def sub.imp_dist_assn_char
    by (rule ent_trans[OF ent_star_mono[OF ent_refl c]]) sep_auto
  note r = inst.imp_bfs.visited_dists_parents_imp_frontier_rule[OF BFS_axiom, folded fin_def,
             unfolded code_eqs, where Gh = Gh and Vh = Vi and Pa = Pa and Fr = Fr and Bf = Bf and Da = Da]
  show ?thesis
    by (rule ht_cons_prec[OF pre _ r]) (simp only: split_paired_all prod.case, rule post)
qed

text \<open>The path from the sources to a visited vertex @{term t}, reversed, is written into the
      first cells of an array with room for the vertices of the graph.\<close>

lemma path_rule[bfs_heap_rules]:
  assumes "t \<in> set (BFS_dist_state.visited fin)" "card (dVs nbs_edges) \<le> length rl"
  shows "<parent_array.pa_parent_assn n (BFS_par_state.parent fin) Pa * Ra \<mapsto>\<^sub>a rl>
           bfs_path Pa Ra t
         <\<lambda>k. parent_array.pa_parent_assn n (BFS_par_state.parent fin) Pa *
              Ra \<mapsto>\<^sub>a (parent_array.pa_get_path n (BFS_par_state.parent fin) t @
                      drop (length (parent_array.pa_get_path n (BFS_par_state.parent fin) t)) rl) *
              \<up>(k = length (parent_array.pa_get_path n (BFS_par_state.parent fin) t) \<and>
                 (\<exists>u \<in> set ss.
                    vwalk_bet nbs_edges u (rev (parent_array.pa_get_path n (BFS_par_state.parent fin) t)) t \<and>
                    length (parent_array.pa_get_path n (BFS_par_state.parent fin) t) - 1 =
                      distance_set nbs_edges (set ss) t))>"
proof-
  have card0: "0 + card (dVs (sub.Graph.digraph_abs G)) \<le> length rl"
    using assms(2) unfolding digraph_abs_G add_0 .
  note r = inst.imp_bfs.get_path_imp_correct[OF BFS_axiom fin_def assms(1) card0,
             where pari = Pa and Pa = Pa, unfolded digraph_abs_G set_rev]
  show ?thesis
    unfolding bfs_path_def
    by (rule ht_cons_prec[OF _ _ r])
       (simp_all only: take_0 append.simps(1) add_0 simp_thms(6) pure_true mult_1_right ent_refl)
qed

end

end

text \<open>Every graph below @{term n} with a finite domain is an instance, e.g.\ with an iterator that
      is never run; so the functional facts, e.g.\ @{thm [source] bfs_iterator_arrays.distance_parents},
      hold for it.\<close>

lemma bfs_iterator_arrays_graph:
  assumes "dVs {(u, v). v \<in> set (case G u of None \<Rightarrow> [] | Some vs \<Rightarrow> vs)} \<subseteq> {..<n}" "finite (dom G)"
  shows "bfs_iterator_arrays n G (\<lambda>_ _ _ acc. return acc) (\<lambda>_ :: unit. false)"
  by (rule bfs_iterator_arrays.intro[OF assms]) (simp only: star_false_left ht_false)

section \<open>Correctness\<close>

text \<open>The input: the number of vertices \<open>n\<close>, the lists \<open>fs\<close> and \<open>ts\<close> of tails and heads of
      the edges, with endpoints below \<open>n\<close>, and the distinct list of sources \<open>ss\<close>, which are
      vertices of the graph.\<close>

locale bfs_csr_arrays =
  fixes n :: nat and fs :: "nat list" and ts :: "nat list" and ss :: "nat list"
  assumes ts_length: "length ts = length fs"
    and fs_bound: "i < length fs \<Longrightarrow> fs ! i < n" and ts_bound: "i < length fs \<Longrightarrow> ts ! i < n"
    and srcs_distinct: "distinct ss" and srcs_nonempty: "ss \<noteq> []"
    and srcs_in_graph: "set ss \<subseteq> dVs (set (zip fs ts))"
begin

text \<open>The graph described by the edges, and the set of sources.\<close>

definition \<E> :: "(nat \<times> nat) set" where
  "\<E> = set (zip fs ts)"

definition \<S> :: "nat set" where
  "\<S> = set ss"

text \<open>The CSR: the buildup runs over the edges of the input arrays, with the tails as keys and
      the heads as stored values. The graph of the BFS is the map of the vertices to their blocks.\<close>

sublocale ei: csr_edge_input n fs ts "e_src fs" src_imp
  by unfold_locales
     (use ts_length src_imp_rule[of _ fs ts] in \<open>auto simp: in_set_conv_nth fs_bound ts_bound\<close>)

abbreviation nbs_map :: "nat \<Rightarrow> nat list option" where
  "nbs_map \<equiv> ei.heads.csr_map"

lemma nbs_edge[simp]: "v \<in> set (case nbs_map u of None \<Rightarrow> [] | Some vs \<Rightarrow> vs) \<longleftrightarrow> (u, v) \<in> \<E>"
proof (cases "u < n")
  case True
  have "set (ei.heads.csr_list u) =
        e_tgt fs ts ` (!) ei.inp.E_spec ` {ei.inp.B_spec ! u..<ei.inp.B_spec ! Suc u}"
    unfolding ei.heads.csr_list_set[of u undefined] ei.heads.csr_abstract_eq image_image
    using ei.B_spec_bound[OF True] by auto
  then show ?thesis
    unfolding ei.block_key[OF True]
    using True by (auto simp: ei.heads.csr_map_def \<E>_def set_zip ts_length)
next
  case False
  then show ?thesis
    using fs_bound by (fastforce simp: ei.heads.csr_map_def \<E>_def set_zip ts_length)
qed

lemma E_bound: "dVs \<E> \<subseteq> {..<n}"
  by (auto simp: dVs_def \<E>_def set_zip ts_length fs_bound ts_bound)

lemma edges_E[simp]: "{(u, v). v \<in> set (case nbs_map u of None \<Rightarrow> [] | Some vs \<Rightarrow> vs)} = \<E>"
  unfolding nbs_edge by (rule set_eqI) (simp only: mem_Collect_eq case_prod_beta prod.collapse)

text \<open>The neighbours of a vertex are folded over by @{const csr_fold_imp} in the order of its
      block.\<close>

lemma nbs_rule[bfs_heap_rules]:
  assumes "u < n"
    and "\<And>acc acci x. x \<in> set (case nbs_map u of None \<Rightarrow> [] | Some vs \<Rightarrow> vs) \<Longrightarrow>
           <A acc acci> fi x acci <\<lambda>r. A (f x acc) r>"
  shows "<ei.heads.csr_blocks_assn (\<lambda>v. ei.inp.B_spec ! v) Gh * A acc acci> csr_fold_imp Gh u fi acci
         <\<lambda>r. ei.heads.csr_blocks_assn (\<lambda>v. ei.inp.B_spec ! v) Gh *
              A (foldl (\<lambda>acc x. f x acc) acc (case nbs_map u of None \<Rightarrow> [] | Some vs \<Rightarrow> vs)) r>"
proof -
  have l: "(case nbs_map u of None \<Rightarrow> [] | Some vs \<Rightarrow> vs) = ei.heads.csr_list u"
    using assms(1) by (simp only: ei.heads.csr_map_def if_True option.case)
  show ?thesis
    unfolding l
    by (rule ei.heads.csr_fold_imp_refine[where c = "\<lambda>v. ei.inp.B_spec ! v",
               unfolded ei.heads.csr_fold_def, OF lessThan_iff[THEN iffD2, OF assms(1)]])
       (rule assms(2), unfold l ei.heads.csr_list_set[symmetric])
qed

lemma finite_dom: "finite (dom nbs_map)"
  by (rule finite_subset[where B = "{..<n}"]) (auto simp: ei.heads.csr_map_def split: if_splits)

interpretation it: bfs_iterator_arrays n nbs_map csr_fold_imp
  "ei.heads.csr_blocks_assn (\<lambda>v. ei.inp.B_spec ! v)"
  by (intro bfs_iterator_arrays.intro finite_dom nbs_rule) (unfold edges_E, rule E_bound)

lemmas Vs_G = it.Vs_G[unfolded edges_E]

lemma srcs: "it.bfs_sources ss"
  unfolding it.bfs_sources_def edges_E \<E>_def by (intro conjI srcs_distinct srcs_nonempty srcs_in_graph)

subsection \<open>The result of the BFS\<close>

named_theorems bfs_array_intros "Correctness of the arrays returned by BFS"

text \<open>The arrays returned are correct if, for every vertex of the graph @{term \<E>}, the
      visited array says whether it is reachable from a source, the distance array holds its
      distance from the sources if it is reachable, and the parent array holds, for every reachable
      vertex that is not a source, a reachable vertex from which an edge leads to it and whose
      distance is one smaller.\<close>

definition bfs_arrays :: "bool list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "bfs_arrays vs ds ps \<longleftrightarrow> (\<forall>x \<in> dVs \<E>.
     x < length vs \<and> x < length ds \<and> x < length ps \<and>
     (vs ! x \<longleftrightarrow> (\<exists>u \<in> \<S>. \<exists>q. vwalk_bet \<E> u q x)) \<and>
     (vs ! x \<longrightarrow> enat (ds ! x) = distance_set \<E> \<S> x) \<and>
     ((vs ! x \<and> x \<notin> \<S>) \<longrightarrow>
        vs ! (ps ! x) \<and> (ps ! x, x) \<in> \<E> \<and> distance_set \<E> \<S> x = distance_set \<E> \<S> (ps ! x) + 1))"

lemma bfs_arrays_intro[bfs_array_intros]:
  assumes "\<forall>u \<in> dVs \<E>. u < length l \<and> (l ! u \<longleftrightarrow> u \<in> set vis)"
    and "\<forall>i \<in> dVs \<E>. i < length dl \<and> d i = dl ! i"
    and "\<forall>i \<in> dVs \<E>. i < length pl \<and> p i = pl ! i"
    and "\<forall>x. x \<in> set vis \<longleftrightarrow> (\<exists>u \<in> \<S>. \<exists>q. vwalk_bet \<E> u q x)"
    and "\<forall>x \<in> set vis. enat (d x) = distance_set \<E> \<S> x"
    and "\<forall>x \<in> set vis - \<S>. p x \<in> set vis \<and> (p x, x) \<in> \<E> \<and>
               distance_set \<E> \<S> x = distance_set \<E> \<S> (p x) + 1"
  shows "bfs_arrays l dl pl"
proof (unfold bfs_arrays_def, intro ballI)
  fix x assume x: "x \<in> dVs \<E>"
  note at = bspec[OF assms(1) x] bspec[OF assms(2) x] bspec[OF assms(3) x]
  have parent: "l ! (pl ! x) \<and> (pl ! x, x) \<in> \<E> \<and>
      distance_set \<E> \<S> x = distance_set \<E> \<S> (pl ! x) + 1"
    if "l ! x" "x \<notin> \<S>"
  proof -
    have step: "p x \<in> set vis" "(p x, x) \<in> \<E>"
      "distance_set \<E> \<S> x = distance_set \<E> \<S> (p x) + 1"
      using assms(6) at(1) that by blast+
    show ?thesis
      unfolding conjunct2[OF at(3), symmetric]
      using step bspec[OF assms(1) dVsI(1)[OF step(2)]] by blast
  qed
  have "enat (dl ! x) = distance_set \<E> \<S> x" if "l ! x"
    unfolding conjunct2[OF at(2), symmetric]
    using assms(5) at(1) that by blast
  then show "x < length l \<and> x < length dl \<and> x < length pl \<and>
    (l ! x \<longleftrightarrow> (\<exists>u \<in> \<S>. \<exists>q. vwalk_bet \<E> u q x)) \<and>
    (l ! x \<longrightarrow> enat (dl ! x) = distance_set \<E> \<S> x) \<and>
    ((l ! x \<and> x \<notin> \<S>) \<longrightarrow> l ! (pl ! x) \<and> (pl ! x, x) \<in> \<E> \<and>
      distance_set \<E> \<S> x = distance_set \<E> \<S> (pl ! x) + 1)"
    using at assms(4) parent by blast
qed

text \<open>For the parent array, it suffices that every reachable vertex that is not a source has a
      parent in the parent map and that all its parents have these properties.\<close>

lemma bfs_arrays_intro_par[bfs_array_intros]:
  assumes "\<forall>u \<in> dVs \<E>. u < length l \<and> (l ! u \<longleftrightarrow> u \<in> set vis)"
    and "\<forall>i \<in> dVs \<E>. i < length dl \<and> d i = dl ! i"
    and "length pl = n" and "\<forall>v u. p v = Some u \<longrightarrow> pl ! v = u"
    and "\<forall>x. x \<in> set vis \<longleftrightarrow> (\<exists>u \<in> \<S>. \<exists>q. vwalk_bet \<E> u q x)"
    and "\<forall>x \<in> set vis. enat (d x) = distance_set \<E> \<S> x"
    and "\<forall>x \<in> set vis - \<S>. (\<exists>u. (x, u) \<in> parent_array.pa_graph p) \<and>
               (\<forall>u. (x, u) \<in> parent_array.pa_graph p \<longrightarrow> u \<in> set vis \<and> (u, x) \<in> \<E> \<and>
                  distance_set \<E> \<S> x = distance_set \<E> \<S> u + 1)"
  shows "bfs_arrays l dl pl"
proof (rule bfs_arrays_intro[OF assms(1,2) _ assms(5,6), where p = "\<lambda>i. pl ! i"])
  show "\<forall>i \<in> dVs \<E>. i < length pl \<and> pl ! i = pl ! i"
    using E_bound assms(3) by auto
  show "\<forall>x \<in> set vis - \<S>. pl ! x \<in> set vis \<and> (pl ! x, x) \<in> \<E> \<and>
    distance_set \<E> \<S> x = distance_set \<E> \<S> (pl ! x) + 1"
  proof
    fix x assume "x \<in> set vis - \<S>"
    show "pl ! x \<in> set vis \<and> (pl ! x, x) \<in> \<E> \<and>
      distance_set \<E> \<S> x = distance_set \<E> \<S> (pl ! x) + 1"
      using bspec[OF assms(7) \<open>x \<in> set vis - \<S>\<close>] assms(4)
      by (auto simp: parent_array.pa_graph_def)
  qed
qed

lemma arrays_ent:
  assumes "\<And>l dl pl. \<lbrakk>pv l; pd dl; pp pl\<rbrakk> \<Longrightarrow> res l dl pl"
  shows "F * (\<exists>\<^sub>A l. Vi \<mapsto>\<^sub>a l * \<up>(pv l)) * (\<exists>\<^sub>A dl. Da \<mapsto>\<^sub>a dl * \<up>(pd dl)) *
         (\<exists>\<^sub>A pl. Pa \<mapsto>\<^sub>a pl * \<up>(pp pl)) * F' \<Longrightarrow>\<^sub>A
         \<exists>\<^sub>A vs ds ps. Vi \<mapsto>\<^sub>a vs * Da \<mapsto>\<^sub>a ds * Pa \<mapsto>\<^sub>a ps * \<up>(res vs ds ps) * true"
  using assms by sep_auto

text \<open>The visited set as the array of its characteristic list.\<close>

lemma visited_ent:
  "bool_array_set_assn n S Vi \<Longrightarrow>\<^sub>A
   \<exists>\<^sub>A l. Vi \<mapsto>\<^sub>a l * \<up>(\<forall>u \<in> dVs \<E>. u < length l \<and> (l ! u \<longleftrightarrow> u \<in> S))"
  unfolding bool_array_set_assn_def
  using E_bound by sep_auto

lemma bfs_arrays_ent:
  assumes "\<forall>x. x \<in> set vis \<longleftrightarrow> (\<exists>u \<in> \<S>. \<exists>q. vwalk_bet \<E> u q x)"
    and "\<forall>x \<in> set vis. enat (d x) = distance_set \<E> \<S> x"
    and "\<forall>x \<in> set vis - \<S>. (\<exists>u. (x, u) \<in> parent_array.pa_graph p) \<and>
           (\<forall>u. (x, u) \<in> parent_array.pa_graph p \<longrightarrow> u \<in> set vis \<and> (u, x) \<in> \<E> \<and>
              distance_set \<E> \<S> x = distance_set \<E> \<S> u + 1)"
  shows "F * bool_array_set_assn n (set vis) Vi *
         BFS_subprocedures_lists.imp_dist_assn n Dh nbs_map d Da * parent_array.pa_parent_assn n p Pa * F'
         \<Longrightarrow>\<^sub>A
         \<exists>\<^sub>A vs ds ps. Vi \<mapsto>\<^sub>a vs * Da \<mapsto>\<^sub>a ds * Pa \<mapsto>\<^sub>a ps * \<up>(bfs_arrays vs ds ps) * true"
  unfolding it.imp_dist_assn_char parent_array.pa_parent_assn_def Vs_G
  by (rule ent_trans[OF ent_star_mono[OF ent_star_mono[OF ent_star_mono[OF ent_star_mono[OF ent_refl visited_ent]
                                                         ent_refl] ent_refl] ent_refl]],
      rule arrays_ent, rule bfs_arrays_intro_par[OF _ _ _ _ assms],
      (assumption | erule conjunct1 | erule conjunct2)+)

lemma bfs_csr_build_rule[bfs_heap_rules]:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts> csr_build_heads n (Fa, Ta) 0
   <\<lambda>Gi. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * ei.heads.csr_blocks_assn (\<lambda>v. ei.inp.B_spec ! v) Gi>"
  by (rule ht_cons_post[OF ei.csr_build_heads_rule[of Fa Ta, unfolded csr_build_heads]])
     (sep_auto simp: ei.heads.csr_blocks_assn_def split: prod.splits)

text \<open>The allocations of @{const bfs_csr_run} establish the precondition of the BFS on the
      instance.\<close>

lemma bfs_csr_run_rule[bfs_heap_rules]:
  assumes "\<And>Gi Vi Fr Bf Da Pa fl bl. \<lbrakk>length fl = Suc n; take (length ss) fl = ss; length bl = Suc n\<rbrakk> \<Longrightarrow>
     <bool_array_set_assn n {} Vi * Fr \<mapsto>\<^sub>a fl * Bf \<mapsto>\<^sub>a bl * Da \<mapsto>\<^sub>a map id [0..<n] * len_assn n Pa *
      ei.heads.csr_blocks_assn (\<lambda>v. ei.inp.B_spec ! v) Gi>
       bfs_csr_visited_dists_parents Gi Vi (Fr, length ss, Bf) Da Pa <Q Gi Vi Fr Bf Da Pa>"
  shows "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Sa \<mapsto>\<^sub>a ss> bfs_csr_run n Fa Ta Sa
         <\<lambda>r. (\<exists>\<^sub>A Gi Vi Fr Bf Da Pa. Q Gi Vi Fr Bf Da Pa r) * (Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Sa \<mapsto>\<^sub>a ss) * true>"
proof-
  let ?FL = "take (length ss) ss @ drop (length ss) (replicate (Suc n) (0::nat))"
  let ?I = "Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Sa \<mapsto>\<^sub>a ss"
  note ls = it.srcs_length[OF srcs]
  have lenF: "length ?FL = Suc n" "take (length ss) ?FL = ss"
    using ls by simp_all
  have main:
    "<(bool_array_set_assn n {} Vi * Fr \<mapsto>\<^sub>a ?FL * Bf \<mapsto>\<^sub>a replicate (Suc n) (0::nat) *
       Da \<mapsto>\<^sub>a map id [0..<n] * Pa \<mapsto>\<^sub>a map id [0..<n] *
       ei.heads.csr_blocks_assn (\<lambda>v. ei.inp.B_spec ! v) Gi) * ?I>
       bfs_csr_visited_dists_parents Gi Vi (Fr, length ss, Bf) Da Pa
     <\<lambda>r. (\<exists>\<^sub>A Gi Vi Fr Bf Da Pa. Q Gi Vi Fr Bf Da Pa r) * ?I * true>" for Gi Vi Fr Bf Da Pa
    by (rule ht_cons[OF ent_star_mono[OF ent_star_mono[OF ent_star_mono[OF ent_refl
                          len_intro[OF length_map[of id "[0..<n]", unfolded length_upt minus_nat.diff_0]]]
                          ent_refl] ent_refl] _
                     ht_frame[OF assms[OF lenF length_replicate], where R = ?I]])
       sep_auto
  show ?thesis
    unfolding bfs_csr_run_def
    using ls by (sep_auto heap: bfs_csr_build_rule copy_prefix_imp_rule bool_array_set_assn_new main)
qed

text \<open>The final correctness theorem: the program returns a visited, a distance and a parent
      array with these properties.\<close>

lemmas fin_correct = it.fin_correct[OF srcs, unfolded edges_E, folded \<S>_def]

theorem bfs_csr_run_correct[bfs_heap_rules]:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Sa \<mapsto>\<^sub>a ss> bfs_csr_run n Fa Ta Sa
   <\<lambda>(Vi, Da, Pa). \<exists>\<^sub>A vs ds ps. Vi \<mapsto>\<^sub>a vs * Da \<mapsto>\<^sub>a ds * Pa \<mapsto>\<^sub>a ps * \<up>(bfs_arrays vs ds ps) * true>"
  by (rule ht_cons_post[OF bfs_csr_run_rule[
        OF it.bfs_rule[OF srcs, folded bfs_csr_visited_dists_parents_def]]], assumption+,
      simp only: split_paired_all prod.case,
      rule ent_true_drop(1), rule ent_true_drop(1), intro ent_ex_preI,
      unfold ent_pure_pre_iff prod.inject, intro impI, elim conjE, hypsubst,
      rule ent_true_drop(2), unfold mult.assoc,
      rule bfs_arrays_ent[unfolded mult.assoc])
     (intro allI ballI; rule fin_correct; assumption?)+

text \<open>Path reconstruction: after the BFS, @{const bfs_path} writes a shortest path from the
      sources to any reachable vertex @{term v}, reversed, into the first cells of an array with
      at least @{term n} cells and returns its length.\<close>

lemma run_then_path:
  assumes "<P> m <\<lambda>r. (\<exists>\<^sub>A g1 g2 g3 g4 g5 g6. Q g1 g2 g3 g4 g5 g6 r) * F * true>"
    and "\<And>g1 g2 g3 g4 g5 g6 a b d. <Q g1 g2 g3 g4 g5 g6 (a, b, d) * Ra \<mapsto>\<^sub>a r> m' b d
           <\<lambda>k. \<exists>\<^sub>A ps. Ra \<mapsto>\<^sub>a ps * \<up>(q k ps) * true>"
  shows "<P * Ra \<mapsto>\<^sub>a r> do { (a, b, d) \<leftarrow> m; m' b d } <\<lambda>k. \<exists>\<^sub>A ps. Ra \<mapsto>\<^sub>a ps * \<up>(q k ps) * true>"
  by (sep_auto heap: assms(1,2))

theorem bfs_csr_path_correct[bfs_heap_rules]:
  assumes "\<exists>u \<in> \<S>. \<exists>q. vwalk_bet \<E> u q v" and "n \<le> length r"
  shows "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Sa \<mapsto>\<^sub>a ss * Ra \<mapsto>\<^sub>a r>
           do { (Vi, Da, Pa) \<leftarrow> bfs_csr_run n Fa Ta Sa; bfs_path Pa Ra v }
         <\<lambda>k. \<exists>\<^sub>A ps. Ra \<mapsto>\<^sub>a ps * \<up>(length ps = length r \<and>
              (\<exists>u \<in> \<S>. vwalk_bet \<E> u (rev (take k ps)) v \<and> enat (k - 1) = distance_set \<E> \<S> v)) * true>"
proof-
  have "v \<in> set (BFS_dist_state.visited (it.fin ss))"
    using assms(1) fin_correct(1) by blast
  have "card (dVs it.nbs_edges) \<le> length r"
    unfolding edges_E
    by (rule order.trans[OF card_mono[OF finite_lessThan E_bound, unfolded card_lessThan] assms(2)])
  note path = it.path_rule[OF srcs
      \<open>v \<in> set (BFS_dist_state.visited (it.fin ss))\<close>
      \<open>card (dVs it.nbs_edges) \<le> length r\<close>, unfolded edges_E, folded \<S>_def]
  have "length (parent_array.pa_get_path n (BFS_par_state.parent (it.fin ss)) v) \<le> length r"
    using it.fin_path_length[OF srcs \<open>v \<in> set (BFS_dist_state.visited (it.fin ss))\<close>]
      \<open>card (dVs it.nbs_edges) \<le> length r\<close> by linarith
  show ?thesis
    by (rule run_then_path[OF bfs_csr_run_rule[
          OF it.bfs_rule[OF srcs, folded bfs_csr_visited_dists_parents_def]]])
       (use \<open>length (parent_array.pa_get_path n (BFS_par_state.parent (it.fin ss)) v) \<le> length r\<close>
         in \<open>sep_auto heap: path\<close>)
qed

end



section \<open>Running the Code\<close>

text \<open>A test harness. \<open>bfs_query\<close> asks the arrays for a vertex \<open>v\<close>: if it is visited, it
      returns its distance and writes its path, reversed, into the array \<open>Ra\<close> the caller provides,
      together with the path length; otherwise it returns @{const None}. The \<open>code\<close> antiquotation
      compiles both into the running ML session; applying a @{typ "'a Heap"} computation to
      \<open>()\<close> runs it.\<close>

definition bfs_query :: "bool array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow>
                         (nat \<times> nat) option Heap" where
  "bfs_query Vi Da Pa Ra v = do {
     b \<leftarrow> Array.nth Vi v;
     if b then do {
       d \<leftarrow> Array.nth Da v;
       k \<leftarrow> bfs_path Pa Ra v;
       return (Some (d, k)) }
     else return None }"

text \<open>A graph with the sources 0 and 5, given by the arrays of tails and heads. A path is read
      from the first \<open>k\<close> entries of the path array and reversed, so it is printed from its source to
      the vertex. The path array is allocated once and reused for every query. Vertex 6 is
      unreachable: its query returns @{const None}.\<close>

ML_val \<open>
  let
    val nat = @{code nat_of_integer}
    val i = @{code integer_of_nat}
    val n = 7
    val es = [(0, 1), (0, 2), (1, 2), (2, 3), (1, 3), (5, 4), (4, 3), (3, 4), (6, 0)]
    val fa = Array.fromList (map (fn (u, _) => nat u) es)
    val ta = Array.fromList (map (fn (_, v) => nat v) es)
    val sa = Array.fromList (map nat [0, 5])
    val (vi, (da, pa)) = @{code bfs_csr_run} (nat n) fa ta sa ()
    val ra = Array.array (n, nat 0)
    fun query v =
      (case @{code bfs_query} vi da pa ra (nat v) () of
         NONE => (v, NONE)
       | SOME (d, k) => (v, SOME (i d, rev (List.tabulate (i k, fn j => i (Array.sub (ra, j)))))))
  in
    map query [0, 1, 2, 3, 4, 5, 6]
  end
\<close>

end
