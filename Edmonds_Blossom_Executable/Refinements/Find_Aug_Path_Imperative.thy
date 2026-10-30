theory Find_Aug_Path_Imperative
  imports
    Graph_Quotient_Lifting_Imperative
    Blossom_Matching_Specs_Imp
    Blossom_Executable.Find_Aug_Path
    Data_Structures.Bounded_Stack_Specs_Imp
    Imperative.Array_Folds
begin

provenance ai

section \<open>Imperative refinement of the search by shrinking blossoms\<close>

text \<open>The imperative program mirrors @{const Find_Aug_Path.Find_Aug_Path_impl}. The current graph
  and the current matching are heap objects, the current vertex list is an array, and the result
  of the search procedure is an imperative path or blossom (@{type match_blossom_res_imp}). A
  contraction builds a new graph from the contracted edges, a new vertex array, and a copy of the
  matching that is contracted in place. The previous graph and matching are pushed, together with
  the cycle and the new vertex, onto an imperative bounded stack (@{locale bounded_stack_imp}), from
  which the lifting pops them again.

  The search procedure, the operations on graphs and the creation of a vertex are parameters; their
  Hoare triples, stated against the functional operations, are the assumptions of the refinement
  locale.\<close>

subsection \<open>Membership in an array\<close>

definition \<^marker>\<open>provenance ai_human\<close> "mem_imp Ct x =
  do { n \<leftarrow> Array.len Ct;
       i \<leftarrow> first_pos_imp (\<lambda>y. return (y = x)) Ct n 0;
       return (i < n) }"

lemma mem_imp_rule: "<Ct \<mapsto>\<^sub>a C> mem_imp Ct x <\<lambda>r. Ct \<mapsto>\<^sub>a C * \<up>(r \<longleftrightarrow> x \<in> set C)>"
  unfolding mem_imp_def
  by (sep_auto heap: first_pos_imp_eq_rule simp: first_pos_member)

definition \<^marker>\<open>provenance ai_human\<close> "quot_vertex_imp Ct u x =
  do { b \<leftarrow> mem_imp Ct x; return (if b then u else x) }"

lemma quot_vertex_imp_rule:
  "<Ct \<mapsto>\<^sub>a C> quot_vertex_imp Ct u x <\<lambda>r. Ct \<mapsto>\<^sub>a C * \<up>(r = quotient_vertex C u x)>"
  unfolding quot_vertex_imp_def
  by (sep_auto heap: mem_imp_rule simp: quotient_vertex_def)

subsection \<open>Contracting a vertex array\<close>

text \<open>The vertices outside the cycle are counted and then copied, after the new vertex, into a
  new array.\<close>

partial_function \<^marker>\<open>provenance ai_human\<close> (heap) count_outside_imp ::
  "'a::heap array \<Rightarrow> 'a array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "count_outside_imp Vi Ct n i k =
     (if i < n then do { x \<leftarrow> Array.nth Vi i;
                         b \<leftarrow> mem_imp Ct x;
                         count_outside_imp Vi Ct n (Suc i) (if b then k else Suc k) }
      else return k)"

partial_function \<^marker>\<open>provenance ai_human\<close> (heap) copy_outside_imp ::
  "'a::heap array \<Rightarrow> 'a array \<Rightarrow> 'a array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "copy_outside_imp Vi Ct D n i j =
     (if i < n then do { x \<leftarrow> Array.nth Vi i;
                         b \<leftarrow> mem_imp Ct x;
                         if b then copy_outside_imp Vi Ct D n (Suc i) j
                         else do { _ \<leftarrow> Array.upd j x D;
                                   copy_outside_imp Vi Ct D n (Suc i) (Suc j) } }
      else return ())"

definition \<^marker>\<open>provenance ai_human\<close> "contract_vertices_imp Vi Ct u =
  do { n \<leftarrow> Array.len Vi;
       k \<leftarrow> count_outside_imp Vi Ct n 0 0;
       D \<leftarrow> Array.new (Suc k) u;
       copy_outside_imp Vi Ct D n 0 1;
       return D }"

abbreviation "outside C xs \<equiv> filter (\<lambda>v. v \<notin> set C) xs"

lemma count_outside_imp_rule:
  "i \<le> length vs \<Longrightarrow>
   <Vi \<mapsto>\<^sub>a vs * Ct \<mapsto>\<^sub>a C> count_outside_imp Vi Ct (length vs) i k
   <\<lambda>r. Vi \<mapsto>\<^sub>a vs * Ct \<mapsto>\<^sub>a C * \<up>(r = k + length (outside C (drop i vs)))>"
proof(induction "length vs - i" arbitrary: i k rule: less_induct)
  case less
  show ?case
  proof(cases "i < length vs")
    case True
    have d: "drop i vs = vs ! i # drop (Suc i) vs"
      using True by (simp add: Cons_nth_drop_Suc)
    have IH: "<Vi \<mapsto>\<^sub>a vs * Ct \<mapsto>\<^sub>a C> count_outside_imp Vi Ct (length vs) (Suc i) k'
              <\<lambda>r. Vi \<mapsto>\<^sub>a vs * Ct \<mapsto>\<^sub>a C * \<up>(r = k' + length (outside C (drop (Suc i) vs)))>"
      for k'
      using True by (intro less.hyps) auto
    show ?thesis
      using True
      by (subst count_outside_imp.simps) (sep_auto heap: mem_imp_rule IH simp: d)
  next
    case False
    thus ?thesis
      using less.prems by (subst count_outside_imp.simps) sep_auto
  qed
qed

lemma copy_outside_imp_rule:
  "\<lbrakk>i \<le> length vs; j + length (outside C (drop i vs)) \<le> length d\<rbrakk> \<Longrightarrow>
   <Vi \<mapsto>\<^sub>a vs * Ct \<mapsto>\<^sub>a C * D \<mapsto>\<^sub>a d> copy_outside_imp Vi Ct D (length vs) i j
   <\<lambda>_. Vi \<mapsto>\<^sub>a vs * Ct \<mapsto>\<^sub>a C * D \<mapsto>\<^sub>a put_list d j (outside C (drop i vs))>"
proof(induction "length vs - i" arbitrary: i j d rule: less_induct)
  case less
  show ?case
  proof(cases "i < length vs")
    case True
    have d: "drop i vs = vs ! i # drop (Suc i) vs"
      using True by (simp add: Cons_nth_drop_Suc)
    have IH: "j' + length (outside C (drop (Suc i) vs)) \<le> length d' \<Longrightarrow>
              <Vi \<mapsto>\<^sub>a vs * Ct \<mapsto>\<^sub>a C * D \<mapsto>\<^sub>a d'> copy_outside_imp Vi Ct D (length vs) (Suc i) j'
              <\<lambda>_. Vi \<mapsto>\<^sub>a vs * Ct \<mapsto>\<^sub>a C * D \<mapsto>\<^sub>a put_list d' j' (outside C (drop (Suc i) vs))>"
      for j' d'
      using True by (intro less.hyps) auto
    show ?thesis
      using True less.prems
      by (subst copy_outside_imp.simps) (sep_auto heap: mem_imp_rule IH simp: d)
  next
    case False
    thus ?thesis
      using less.prems by (subst copy_outside_imp.simps) sep_auto
  qed
qed

lemma contract_vertices_imp_rule:
  "<Vi \<mapsto>\<^sub>a vs * Ct \<mapsto>\<^sub>a C> contract_vertices_imp Vi Ct u
   <\<lambda>D. Vi \<mapsto>\<^sub>a vs * Ct \<mapsto>\<^sub>a C * D \<mapsto>\<^sub>a (u # outside C vs)>"
proof-
  have "put_list (replicate (Suc (length (outside C vs))) u) 1 (outside C vs) = u # outside C vs"
    by (simp add: put_list_eq)
  thus ?thesis
    unfolding contract_vertices_imp_def
    by (sep_auto heap: count_outside_imp_rule copy_outside_imp_rule)
qed

text \<open>Copying an array, which may be empty.\<close>

definition \<^marker>\<open>provenance ai_human\<close> "copy_array_imp A =
  do { n \<leftarrow> Array.len A;
       if n = 0 then Array.of_list [] else prefix_imp A n }"

lemma copy_array_imp_rule: "<A \<mapsto>\<^sub>a xs> copy_array_imp A <\<lambda>B. A \<mapsto>\<^sub>a xs * B \<mapsto>\<^sub>a xs>"
  unfolding copy_array_imp_def
  by (sep_auto heap: prefix_imp_rule)

subsection \<open>The program\<close>

record \<^marker>\<open>provenance ai_human\<close> ('gi, 'mi, 'v, 'ci) Find_Aug_Path_state_imp =
  i_graph :: 'gi
  i_vertices :: "'v array"
  i_matching :: 'mi
  i_contractions :: 'ci
  i_result :: "'v array match_blossom_res_imp option"

locale \<^marker>\<open>provenance ai_human\<close> Find_Aug_Path_Imperative_spec =
  fixes blos_search_imp ::
      "'gi::heap \<Rightarrow> 'mi::heap \<Rightarrow> 'v::heap array \<Rightarrow> 'v array match_blossom_res_imp option Heap"
    and create_vert_imp :: "'v array \<Rightarrow> 'v Heap"
    and g_empty_imp :: "'gi Heap"
    and g_add_edge_imp :: "'gi \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'gi Heap"
    and neighbours_imp :: "'gi \<Rightarrow> 'v \<Rightarrow> 'v array Heap"
    and g_isin_imp :: "'gi \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool Heap"
    and lookup_partner_imp :: "'mi \<Rightarrow> 'v \<Rightarrow> 'v option Heap"
    and copy_matching_imp :: "'mi \<Rightarrow> 'mi Heap"
    and contract_path_imp :: "'mi \<Rightarrow> 'v array \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and stack_empty_imp :: "'ci Heap"
    and stack_push_imp :: "'ci \<Rightarrow> ('gi \<times> 'mi \<times> 'v array \<times> 'v) \<Rightarrow> unit Heap"
    and stack_pop_imp :: "'ci \<Rightarrow> unit Heap"
    and stack_top_imp :: "'ci \<Rightarrow> ('gi \<times> 'mi \<times> 'v array \<times> 'v) Heap"
    and stack_is_empty_imp :: "'ci \<Rightarrow> bool Heap"
begin

subsubsection \<open>Contraction\<close>

text \<open>The contracted graph is built from the edges of the graph, each of whose endpoints is
  replaced by the new vertex if it lies on the cycle, leaving out loops.\<close>

partial_function \<^marker>\<open>provenance ai_human\<close> (heap) contract_nbs_imp ::
  "'v array \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'gi \<Rightarrow> 'gi Heap" where
  "contract_nbs_imp Ct u a A m j Hi =
     (if j < m then do { w \<leftarrow> Array.nth A j;
                         b \<leftarrow> quot_vertex_imp Ct u w;
                         Hi' \<leftarrow> (if a \<noteq> b then g_add_edge_imp Hi a b else return Hi);
                         contract_nbs_imp Ct u a A m (Suc j) Hi' }
      else return Hi)"

partial_function \<^marker>\<open>provenance ai_human\<close> (heap) contract_edges_imp ::
  "'gi \<Rightarrow> 'v array \<Rightarrow> 'v \<Rightarrow> 'v array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'gi \<Rightarrow> 'gi Heap" where
  "contract_edges_imp Gi Ct u Vi n i Hi =
     (if i < n then do { v \<leftarrow> Array.nth Vi i;
                         A \<leftarrow> neighbours_imp Gi v;
                         m \<leftarrow> Array.len A;
                         a \<leftarrow> quot_vertex_imp Ct u v;
                         Hi' \<leftarrow> contract_nbs_imp Ct u a A m 0 Hi;
                         contract_edges_imp Gi Ct u Vi n (Suc i) Hi' }
      else return Hi)"

definition \<^marker>\<open>provenance ai_human\<close> "contract_graph_imp Gi Vi Ct u =
  do { n \<leftarrow> Array.len Vi;
       Hi \<leftarrow> g_empty_imp;
       contract_edges_imp Gi Ct u Vi n 0 Hi }"

text \<open>The matching is copied, and the copy is contracted along the cycle without its last
  vertex, which is its first one.\<close>

definition \<^marker>\<open>provenance ai_human\<close> "contract_matching_imp Mi Ct u =
  do { Mi' \<leftarrow> copy_matching_imp Mi;
       n \<leftarrow> Array.len Ct;
       Bt \<leftarrow> prefix_imp Ct (n - 1);
       contract_path_imp Mi' Bt u;
       return Mi' }"

subsubsection \<open>The loop\<close>

partial_function \<^marker>\<open>provenance ai_human\<close> (heap) Find_Aug_Path_imp ::
  "('gi, 'mi, 'v, 'ci) Find_Aug_Path_state_imp \<Rightarrow> ('gi, 'mi, 'v, 'ci) Find_Aug_Path_state_imp Heap"
  where
  "Find_Aug_Path_imp s =
     (case i_result s of
        Some (Blossom_imp St Ct) \<Rightarrow>
          do { u \<leftarrow> create_vert_imp (i_vertices s);
               Gi' \<leftarrow> contract_graph_imp (i_graph s) (i_vertices s) Ct u;
               Vi' \<leftarrow> contract_vertices_imp (i_vertices s) Ct u;
               Mi' \<leftarrow> contract_matching_imp (i_matching s) Ct u;
               stack_push_imp (i_contractions s) (i_graph s, i_matching s, Ct, u);
               r \<leftarrow> blos_search_imp Gi' Mi' Vi';
               Find_Aug_Path_imp
                 (s\<lparr>i_graph := Gi', i_vertices := Vi', i_matching := Mi', i_result := r\<rparr>) }
      | _ \<Rightarrow> return s)"

subsubsection \<open>Lifting and the result\<close>

partial_function \<^marker>\<open>provenance ai_human\<close> (heap) lift_path_imp :: "'ci \<Rightarrow> 'v array \<Rightarrow> 'v array Heap" where
  "lift_path_imp Si Pt =
     do { e \<leftarrow> stack_is_empty_imp Si;
          if e then return Pt
          else do { (Ei, Ni, Ct, u) \<leftarrow> stack_top_imp Si;
                    stack_pop_imp Si;
                    Pt' \<leftarrow> refine_imp (g_isin_imp Ei) (lookup_partner_imp Ni) u Ct Pt;
                    lift_path_imp Si Pt' } }"

definition \<^marker>\<open>provenance ai_human\<close> "initial_state_imp Gi Mi Vi =
  do { Wi \<leftarrow> copy_array_imp Vi;
       Si \<leftarrow> stack_empty_imp;
       r \<leftarrow> blos_search_imp Gi Mi Wi;
       return \<lparr>i_graph = Gi, i_vertices = Wi, i_matching = Mi, i_contractions = Si,
               i_result = r\<rparr> }"

definition \<^marker>\<open>provenance ai_human\<close> "augmenting_path_imp s =
  (case i_result s of
     Some (Path_imp Pt) \<Rightarrow> do { Pt' \<leftarrow> lift_path_imp (i_contractions s) Pt; return (Some Pt') }
   | _ \<Rightarrow> return None)"

definition \<^marker>\<open>provenance ai_human\<close> "Find_Aug_Path_run_imp Gi Mi Vi =
  do { s \<leftarrow> initial_state_imp Gi Mi Vi;
       s' \<leftarrow> Find_Aug_Path_imp s;
       augmenting_path_imp s' }"

end

section \<open>Correctness of the imperative search\<close>

text \<open>An optional path is represented by an optional array.\<close>

definition \<^marker>\<open>provenance ai_human\<close> "path_opt_assn P r =
  (case P of
     None \<Rightarrow> \<up>(r = None)
   | Some p \<Rightarrow> (case r of None \<Rightarrow> false | Some Pt \<Rightarrow> Pt \<mapsto>\<^sub>a p))"

locale \<^marker>\<open>provenance ai_human\<close> Find_Aug_Path_Imperative =
  Find_Aug_Path where lookup = lookup and mate_empty = mate_empty +
  Find_Aug_Path_Imperative_spec where blos_search_imp = blos_search_imp
    and lookup_partner_imp = lookup_partner_imp and copy_matching_imp = copy_matching_imp
    and contract_path_imp = contract_path_imp and stack_push_imp = stack_push_imp +
  stk: bounded_stack_imp where stack_abstract = stack_abstract
    and stack_push_imp = stack_push_imp +
  mt: blossom_matching_imp where K = K and empty_matching = mate_empty
    and matching_invar = matching_invar_abs and lookup_partner = mate_lookup
    and get_partner = mate_partner and augment = mate_augment and matching_abstract = matching_abs
    and contract_path = mate_contract and expand_path_at_matched = mate_expand
    and add_alternatingly = mate_add_alternatingly and lookup_partner_imp = lookup_partner_imp
    and copy_matching_imp = copy_matching_imp and contract_path_imp = contract_path_imp
    and path_assn = "\<lambda>p Pt. Pt \<mapsto>\<^sub>a p"
  for lookup :: "'adjmap \<Rightarrow> 'v::heap \<Rightarrow> 'vset option"
    and mate_empty :: 'mate
    and blos_search_imp ::
      "'gi::heap \<Rightarrow> 'mi::heap \<Rightarrow> 'v array \<Rightarrow> 'v array match_blossom_res_imp option Heap"
    and lookup_partner_imp :: "'mi \<Rightarrow> 'v \<Rightarrow> 'v option Heap"
    and copy_matching_imp :: "'mi \<Rightarrow> 'mi Heap"
    and contract_path_imp :: "'mi \<Rightarrow> 'v array \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and stack_push_imp :: "'ci \<Rightarrow> ('gi \<times> 'mi \<times> 'v array \<times> 'v) \<Rightarrow> unit Heap"
    and stack_abstract :: "'s \<Rightarrow> ('gi \<times> 'mi \<times> 'v array \<times> 'v) list" +
  fixes graph_assn :: "'adjmap \<Rightarrow> 'gi \<Rightarrow> assn"
    and max_vertices :: nat
  assumes blos_search_imp_rule:
      "\<And>H ws N Gi Mi Wi. \<lbrakk>graph_input H ws; matching_invar H N; length ws \<le> max_vertices\<rbrakk> \<Longrightarrow>
       <graph_assn H Gi * matching_assn N Mi * Wi \<mapsto>\<^sub>a ws> blos_search_imp Gi Mi Wi
       <\<lambda>r. graph_assn H Gi * matching_assn N Mi * Wi \<mapsto>\<^sub>a ws *
            match_blossom_opt_assn (blos_search H ws N) r * true>"
    and create_vert_imp_rule:
      "\<And>ws Wi. set ws \<subset> K \<Longrightarrow>
       <Wi \<mapsto>\<^sub>a ws> create_vert_imp Wi <\<lambda>u. Wi \<mapsto>\<^sub>a ws * \<up>(u = create_vert ws)>"
    and g_empty_rule: "<emp> g_empty_imp <\<lambda>Hi. graph_assn empty Hi>"
    and g_add_edge_rule:
      "\<And>H Hi a b. <graph_assn H Hi> g_add_edge_imp Hi a b
                  <\<lambda>Hi'. graph_assn (Graph.add_edge H a b) Hi'>"
    and neighbours_rule:
      "\<And>H Gi v. \<lbrakk>Graph.graph_inv H; v \<in> K\<rbrakk> \<Longrightarrow>
       <graph_assn H Gi> neighbours_imp Gi v <\<lambda>A. graph_assn H Gi * A \<mapsto>\<^sub>a neighbour_list H v>"
    and g_isin_rule:
      "\<And>H Gi v w. \<lbrakk>Graph.graph_inv H; v \<in> K; w \<in> K\<rbrakk> \<Longrightarrow>
       <graph_assn H Gi> g_isin_imp Gi v w
       <\<lambda>r. graph_assn H Gi * \<up>(r = isin (Graph.neighbourhood H v) w)>"
    and Find_Aug_Path_axiom: Find_Aug_Path_axiom
    and max_vertices: "length vs \<le> max_vertices"
    and capacity: "length vs \<le> cap"
begin

lemma graph_input_G': "graph_input G vs"
  and matching_invar_M': "matching_invar G M"
  and vs_strict': "set vs \<subset> K"
  using Find_Aug_Path_axiom unfolding Find_Aug_Path_axiom_def by blast+

subsection \<open>Building the contracted graph\<close>

definition "contract_nbs_step C u a H w =
  (let b = quotient_vertex C u w in if a \<noteq> b then Graph.add_edge H a b else H)"

definition "contract_edges_step E C u H v =
  foldl (contract_nbs_step C u (quotient_vertex C u v)) H (neighbour_list E v)"

lemma contract_graph_foldl:
  "contract_graph E ws C u = foldl (contract_edges_step E C u) empty ws"
proof-
  have inner: "foldl (\<lambda>G (a, b). Graph.add_edge G a b) H
      (filter (\<lambda>(a, b). a \<noteq> b) (map (\<lambda>(a, b). (quotient_vertex C u a, quotient_vertex C u b))
        (map (Pair v) ns))) =
      foldl (contract_nbs_step C u (quotient_vertex C u v)) H ns" for H v ns
    by (induction ns arbitrary: H) (auto simp: contract_nbs_step_def Let_def)
  have "foldl (\<lambda>G (a, b). Graph.add_edge G a b) H
      (filter (\<lambda>(a, b). a \<noteq> b) (map (\<lambda>(a, b). (quotient_vertex C u a, quotient_vertex C u b))
        (adjacency_edges E ws))) = foldl (contract_edges_step E C u) H ws" for H
    by (induction ws arbitrary: H)
       (simp_all add: adjacency_edges_def inner contract_edges_step_def del: map_map)
  thus ?thesis
    by (simp add: contract_graph_def Graph.from_list_def quotient_edges_def)
qed

lemma contract_nbs_imp_rule:
  "j \<le> length ns \<Longrightarrow>
   <A \<mapsto>\<^sub>a ns * Ct \<mapsto>\<^sub>a C * graph_assn H Hi> contract_nbs_imp Ct u a A (length ns) j Hi
   <\<lambda>Hi'. A \<mapsto>\<^sub>a ns * Ct \<mapsto>\<^sub>a C * graph_assn (foldl (contract_nbs_step C u a) H (drop j ns)) Hi'>"
proof(induction "length ns - j" arbitrary: j H Hi rule: less_induct)
  case less
  show ?case
  proof(cases "j < length ns")
    case True
    have d: "drop j ns = ns ! j # drop (Suc j) ns"
      using True by (simp add: Cons_nth_drop_Suc)
    have IH: "<A \<mapsto>\<^sub>a ns * Ct \<mapsto>\<^sub>a C * graph_assn H' Hi'> contract_nbs_imp Ct u a A (length ns) (Suc j) Hi'
              <\<lambda>Hi''. A \<mapsto>\<^sub>a ns * Ct \<mapsto>\<^sub>a C *
                      graph_assn (foldl (contract_nbs_step C u a) H' (drop (Suc j) ns)) Hi''>"
      for H' Hi'
      using True by (intro less.hyps) auto
    show ?thesis
      using True
      by (subst contract_nbs_imp.simps)
         (sep_auto heap: quot_vertex_imp_rule g_add_edge_rule IH simp: d contract_nbs_step_def)
  next
    case False
    thus ?thesis
      using less.prems by (subst contract_nbs_imp.simps) sep_auto
  qed
qed

lemma contract_edges_imp_rule:
  assumes "Graph.graph_inv E" "set ws \<subseteq> K"
  shows "i \<le> length ws \<Longrightarrow>
   <graph_assn E Gi * Ct \<mapsto>\<^sub>a C * Vi \<mapsto>\<^sub>a ws * graph_assn H Hi>
     contract_edges_imp Gi Ct u Vi (length ws) i Hi
   <\<lambda>Hi'. graph_assn E Gi * Ct \<mapsto>\<^sub>a C * Vi \<mapsto>\<^sub>a ws *
          graph_assn (foldl (contract_edges_step E C u) H (drop i ws)) Hi' * true>"
proof(induction "length ws - i" arbitrary: i H Hi rule: less_induct)
  case less
  show ?case
  proof(cases "i < length ws")
    case True
    have d: "drop i ws = ws ! i # drop (Suc i) ws"
      using True by (simp add: Cons_nth_drop_Suc)
    have vK: "ws ! i \<in> K"
      using True assms(2) by (auto intro: nth_mem)
    have IH: "<graph_assn E Gi * Ct \<mapsto>\<^sub>a C * Vi \<mapsto>\<^sub>a ws * graph_assn H' Hi'>
                contract_edges_imp Gi Ct u Vi (length ws) (Suc i) Hi'
              <\<lambda>Hi''. graph_assn E Gi * Ct \<mapsto>\<^sub>a C * Vi \<mapsto>\<^sub>a ws *
                      graph_assn (foldl (contract_edges_step E C u) H' (drop (Suc i) ws)) Hi'' *
                      true>"
      for H' Hi'
      using True by (intro less.hyps) auto
    note NB = neighbours_rule[OF assms(1) vK]
    note CN = contract_nbs_imp_rule[where j = 0 and ns = "neighbour_list E (ws ! i)", simplified]
    show ?thesis
      using True
      by (subst contract_edges_imp.simps)
         (sep_auto heap: NB quot_vertex_imp_rule CN IH simp: d contract_edges_step_def)
  next
    case False
    thus ?thesis
      using less.prems by (subst contract_edges_imp.simps) sep_auto
  qed
qed

lemma contract_graph_imp_rule:
  assumes "graph_input E ws"
  shows "<graph_assn E Gi * Ct \<mapsto>\<^sub>a C * Vi \<mapsto>\<^sub>a ws> contract_graph_imp Gi Vi Ct u
         <\<lambda>Hi. graph_assn E Gi * Ct \<mapsto>\<^sub>a C * Vi \<mapsto>\<^sub>a ws * graph_assn (contract_graph E ws C u) Hi *
               true>"
  using contract_edges_imp_rule[OF graph_inputD(1,7)[OF assms], where i = 0]
  by (sep_auto heap: g_empty_rule simp: contract_graph_imp_def contract_graph_foldl)

subsection \<open>Contracting the matching and the vertex array\<close>

context
  fixes E N C u ws stem
  assumes contraction:
    "graph_input E ws" "matching_invar E N" "blossom (ugraph_abs E) (matching_abs N) stem C"
    "u \<notin> set ws - set C" "u \<in> K"
begin

lemmas facts = contraction_facts[OF contraction]

lemma contract_path_precond_here:
  "Mate.contract_path_precond (ugraph_abs E) N (butlast C) u
     (\<lambda>x. if x \<in> set (butlast C) then u else x)"
proof-
  have cycle: "odd_cycle C"
    by (rule match_blossomD(3)[OF blossomD(2)[OF contraction(3)]])
  have path: "alt_path (matching_abs N) (butlast C)"
    by (rule alt_path_split_off_last[OF match_blossom_alt_cycle[OF blossomD(2)[OF contraction(3)]]])
  have cycle_props: "set (butlast C) = set C"
    "odd (length (butlast C))" "distinct (butlast C)"
    by (cases C rule: list_cases_hd_and_last;
        insert odd_cycleD[OF cycle] odd_cycle_even_verts[OF cycle]
          match_blossomD(2)[OF blossomD(2)[OF contraction(3)]]; auto)+
  have in_univ: "set (butlast C) \<subseteq> K"
    using cycle_props(1) facts(2) graph_inputD(7)[OF contraction(1)]
      Vs_ugraph_abs_subset_vs[OF contraction(1)] by blast
  have fresh: "u \<notin> Vs (matching_abs N) - set (butlast C)"
    using facts(6,9) Vs_subset cycle_props(1) by blast
  show ?thesis
    by (rule Mate.contract_path_precondI[
          OF facts(7) path cycle_props(2,3) fresh refl in_univ facts(11)])
qed

lemma contract_matching_imp_rule:
  "<matching_assn N Mi * Ct \<mapsto>\<^sub>a C> contract_matching_imp Mi Ct u
   <\<lambda>Mi'. matching_assn N Mi * Ct \<mapsto>\<^sub>a C * matching_assn (contract_matching N C u) Mi' * true>"
proof-
  have inv: "matching_invar_abs (ugraph_abs E) N"
    by (rule facts(7))
  have CP: "<matching_assn N Mi' * Bt \<mapsto>\<^sub>a take (n - Suc 0) C> contract_path_imp Mi' Bt u
            <\<lambda>_. matching_assn (mate_contract N (butlast C) u) Mi' * Bt \<mapsto>\<^sub>a take (n - Suc 0) C>"
    if "n = length C" for n Mi' Bt
  proof-
    have bl: "take (n - Suc 0) C = butlast C"
      using that by (metis butlast_conv_take One_nat_def)
    show ?thesis
      unfolding bl by (rule mt.contract_path_rule[OF contract_path_precond_here])
  qed
  show ?thesis
    using facts(3)
    by (sep_auto heap: mt.copy_matching_rule[OF inv] prefix_imp_rule CP
        simp: contract_matching_imp_def contract_matching_def)
qed

end

subsection \<open>Further invariants of the functional search\<close>

text \<open>Every contraction on the stack contracts the graph and the matching of the entry below it,
  or the input at the bottom, to those of the entry above it, or the current ones at the top.
  The lifting relies on this to know that it lifts an augmenting path through every contraction.\<close>

fun chain :: "('adjmap \<times> 'mate \<times> 'v list \<times> 'v) list \<Rightarrow> 'adjmap \<Rightarrow> 'mate \<Rightarrow> bool" where
  "chain [] H N \<longleftrightarrow> H = G \<and> N = M"
| "chain ((E, N', C, u) # cs) H N \<longleftrightarrow>
     (\<exists>ws stem. graph_input E ws \<and> matching_invar E N' \<and>
        blossom (ugraph_abs E) (matching_abs N') stem C \<and> u \<notin> set ws - set C \<and> u \<in> K \<and>
        H = contract_graph E ws C u \<and> N = contract_matching N' C u \<and> chain cs E N')"

text \<open>A contraction does not lengthen the vertex list and reduces the number of distinct vertices.
  Hence the vertex list stays within the bound of the search procedure, and the number of
  contractions on the stack stays below the capacity of the stack.\<close>

definition "invar_size state \<longleftrightarrow>
  length (search_vertices state) \<le> length vs \<and>
  length (contractions state) + card (set (search_vertices state)) \<le> card (set vs)"

definition "invars state \<longleftrightarrow>
  invar_1 state \<and> invar_search state \<and>
  chain (contractions state) (search_graph state) (search_matching state) \<and> invar_size state"

lemma contract_vertices_size:
  assumes "graph_input E ws" "blossom (ugraph_abs E) (matching_abs N) stem C"
  shows "length (contract_vertices ws C u) \<le> length ws"
    "card (set (contract_vertices ws C u)) < card (set ws)"
proof-
  have C: "set C \<subseteq> set ws"
    using subset_path_Vs[OF path_suff[OF blossomD(1)[OF assms(2)]]]
      Vs_ugraph_abs_subset_vs[OF assms(1)] by blast
  have two: "2 \<le> card (set C)"
    by (rule blossom_cycle_longer_2[OF blossomD(2)[OF assms(2)]])
  hence "C \<noteq> []"
    by auto
  hence "hd C \<in> set ws" "hd C \<in> set C"
    using C by auto
  hence "length (outside C ws) < length ws"
    by (intro length_filter_less) auto
  thus "length (contract_vertices ws C u) \<le> length ws"
    by (simp add: contract_vertices_def)
  have eqs: "set (contract_vertices ws C u) = Set.insert u (set ws - set C)"
    by (auto simp: contract_vertices_def)
  have "card (Set.insert u (set ws - set C)) \<le> Suc (card (set ws - set C))"
    by (simp add: card_insert_if)
  hence "card (set (contract_vertices ws C u)) \<le> Suc (card (set ws - set C))"
    by (simp only: eqs)
  moreover have "card (set ws - set C) = card (set ws) - card (set C)"
    using C by (simp add: card_Diff_subset)
  moreover have "card (set C) \<le> card (set ws)"
    using C by (simp add: card_mono)
  ultimately show "card (set (contract_vertices ws C u)) < card (set ws)"
    using two by linarith
qed

lemma invars_initial: "invars initial_state"
  using initial_state_props(1,2)[OF Find_Aug_Path_axiom]
  by (simp add: invars_def invar_size_def initial_state_def)

lemma invars_upd1:
  assumes "Find_Aug_Path_call_1_conds state" "invars state"
  shows "invars (Find_Aug_Path_upd1 state)"
proof-
  have I: "invar_1 state" "invar_search state"
    "chain (contractions state) (search_graph state) (search_matching state)" "invar_size state"
    using assms(2) by (simp_all add: invars_def)
  obtain stem C where result: "search_result state = Some (Blossom stem C)"
    and contract:
    "graph_input (search_graph state) (search_vertices state)"
    "matching_invar (search_graph state) (search_matching state)"
    "blossom (ugraph_abs (search_graph state)) (matching_abs (search_matching state)) stem C"
    "create_vert (search_vertices state) \<notin> set (search_vertices state) - set C"
    "create_vert (search_vertices state) \<in> K"
    by (rule call_1_facts[OF Find_Aug_Path_axiom assms(1) I(1,2)])
  note upd = upd1_fields[OF Find_Aug_Path_axiom result]
  note sz = contract_vertices_size[OF contract(1,3), of "create_vert (search_vertices state)"]
  have "chain (contractions (Find_Aug_Path_upd1 state)) (search_graph (Find_Aug_Path_upd1 state))
      (search_matching (Find_Aug_Path_upd1 state))"
    using contract I(3) by (auto simp: upd)
  moreover have "invar_size (Find_Aug_Path_upd1 state)"
    using I(4) sz by (auto simp: invar_size_def upd)
  ultimately show ?thesis
    using invar_1_holds_1[OF Find_Aug_Path_axiom assms(1) I(1,2)]
      invar_search_holds_1[OF Find_Aug_Path_axiom assms(1) I(2)]
    by (simp add: invars_def)
qed

lemma contractions_less_cap:
  assumes "Find_Aug_Path_call_1_conds state" "invars state"
  shows "length (contractions state) < cap"
proof-
  have I: "invar_1 state" "invar_search state" "invar_size state"
    using assms(2) by (simp_all add: invars_def)
  obtain stem C where
    "graph_input (search_graph state) (search_vertices state)"
    "blossom (ugraph_abs (search_graph state)) (matching_abs (search_matching state)) stem C"
    by (rule call_1_facts[OF Find_Aug_Path_axiom assms(1) I(1,2)])
  hence "card (set (contract_vertices (search_vertices state) C undefined)) <
      card (set (search_vertices state))"
    by (rule contract_vertices_size(2))
  hence "0 < card (set (search_vertices state))"
    by linarith
  moreover have "card (set vs) \<le> length vs"
    by (rule card_length)
  ultimately show ?thesis
    using I(3) capacity by (simp add: invar_size_def)
qed

subsection \<open>The stack of contractions\<close>

definition "contr_stack_assn xs Si =
  (\<exists>\<^sub>A S. stack_assn S Si * \<up>(stack_invar S \<and> stack_abstract S = xs))"

lemma contr_stack_empty_rule:
  "<emp> stack_empty_imp <contr_stack_assn []>"
  unfolding contr_stack_assn_def
  by (sep_auto heap: stk.stack_empty_rule simp: stk.stack_empty)

lemma contr_stack_push_rule:
  "length xs < cap \<Longrightarrow>
   <contr_stack_assn xs Si> stack_push_imp Si x <\<lambda>_. contr_stack_assn (x # xs) Si>"
  unfolding contr_stack_assn_def
  by (sep_auto heap: stk.stack_push_rule simp: stk.stack_push)

lemma contr_stack_pop_rule:
  "xs \<noteq> [] \<Longrightarrow> <contr_stack_assn xs Si> stack_pop_imp Si <\<lambda>_. contr_stack_assn (tl xs) Si>"
  unfolding contr_stack_assn_def
  by (sep_auto heap: stk.stack_pop_rule simp: stk.stack_pop)

lemma contr_stack_top_rule:
  "xs \<noteq> [] \<Longrightarrow>
   <contr_stack_assn xs Si> stack_top_imp Si <\<lambda>r. contr_stack_assn xs Si * \<up>(r = hd xs)>"
  unfolding contr_stack_assn_def
  by (sep_auto heap: stk.stack_top_rule simp: stk.stack_top)

lemma contr_stack_is_empty_rule:
  "<contr_stack_assn xs Si> stack_is_empty_imp Si
   <\<lambda>r. contr_stack_assn xs Si * \<up>(r \<longleftrightarrow> xs = [])>"
  unfolding contr_stack_assn_def
  by (sep_auto heap: stk.stack_is_empty_rule simp: stk.stack_is_empty)

text \<open>The entries of the stack own the graphs, matchings and cycles of the recorded contractions.
  The graph and the matching of the bottom entry are those of the input.\<close>

fun entries_assn ::
  "('adjmap \<times> 'mate \<times> 'v list \<times> 'v) list \<Rightarrow> ('gi \<times> 'mi \<times> 'v array \<times> 'v) list \<Rightarrow> assn" where
  "entries_assn [] [] = emp"
| "entries_assn ((E, N, C, u) # cs) ((Ei, Ni, Ct, u') # hs) =
     graph_assn E Ei * matching_assn N Ni * Ct \<mapsto>\<^sub>a C * \<up>(u' = u) * entries_assn cs hs"
| "entries_assn _ _ = false"

fun bottom :: "('gi \<times> 'mi \<times> 'v array \<times> 'v) list \<Rightarrow> 'gi \<Rightarrow> 'mi \<Rightarrow> 'gi \<times> 'mi" where
  "bottom [] Hi Ni = (Hi, Ni)"
| "bottom ((Ei, Ni', _, _) # hs) _ _ = bottom hs Ei Ni'"

subsection \<open>The loop\<close>

definition "pre_assn Gi Mi s si hs =
  contr_stack_assn hs (i_contractions si) * entries_assn (contractions s) hs *
  graph_assn (search_graph s) (i_graph si) * i_vertices si \<mapsto>\<^sub>a search_vertices s *
  matching_assn (search_matching s) (i_matching si) *
  match_blossom_opt_assn (search_result s) (i_result si) *
  \<up>(bottom hs (i_graph si) (i_matching si) = (Gi, Mi) \<and> length hs = length (contractions s) \<and>
    invars s)"

definition "state_assn Gi Mi s si = (\<exists>\<^sub>A hs. pre_assn Gi Mi s si hs)"

lemma Find_Aug_Path_impl_upd1:
  "search_result s = Some (Blossom stem C) \<Longrightarrow>
   Find_Aug_Path_impl s = Find_Aug_Path_impl (Find_Aug_Path_upd1 s)"
  by (subst Find_Aug_Path_impl.simps) (simp add: Find_Aug_Path_upd1_def Let_def)

lemma Find_Aug_Path_impl_ret:
  "\<nexists>stem C. search_result s = Some (Blossom stem C) \<Longrightarrow> Find_Aug_Path_impl s = s"
  by (subst Find_Aug_Path_impl.simps) (auto split: option.splits match_blossom_res.splits)

lemma \<^marker>\<open>provenance ai_human\<close> Find_Aug_Path_imp_refine:
  "<pre_assn Gi Mi s si hs> Find_Aug_Path_imp si
   <\<lambda>si'. state_assn Gi Mi (Find_Aug_Path_impl s) si' * true>"
proof \<^marker>\<open>provenance ai\<close> (induction arbitrary: s si hs rule: Find_Aug_Path_imp.fixp_induct)
  case 1
  then show ?case
    by auto
next
  case 2
  then show ?case
    by simp
next
  case (3 f s si hs)
  show ?case
    unfolding pre_assn_def[of _ _ s si hs] mult.assoc[symmetric]
  proof(rule ht_extract_pre_pure(1), goal_cases)
    case 1
    hence B: "bottom hs (i_graph si) (i_matching si) = (Gi, Mi)"
      and L: "length hs = length (contractions s)" and I: "invars s"
      by blast+
    show ?case
    proof(cases "\<exists>stem C. search_result s = Some (Blossom stem C)")
      case False
      have F: "Find_Aug_Path_impl s = s"
        by (rule Find_Aug_Path_impl_ret[OF False])
      show ?thesis
      proof(cases "\<exists>St Ct. i_result si = Some (Blossom_imp St Ct)")
        case True
        hence "match_blossom_opt_assn (search_result s) (i_result si) = false"
          using False
          by (auto simp: match_blossom_opt_assn_def match_blossom_res_assn_def
              split: option.splits match_blossom_res.splits)
        thus ?thesis
          by simp
      next
        case not_blossom: False
        show ?thesis
          using B L I not_blossom
          by (sep_auto simp: F state_assn_def pre_assn_def
              split: option.splits match_blossom_res_imp.splits)
      qed
    next
      case True
      then obtain stem C where res: "search_result s = Some (Blossom stem C)"
        by blast
      show ?thesis
      proof(cases "\<exists>St Ct. i_result si = Some (Blossom_imp St Ct)")
        case False
        hence "match_blossom_opt_assn (search_result s) (i_result si) = false"
          using res
          by (auto simp: match_blossom_opt_assn_def match_blossom_res_assn_def
              split: option.splits match_blossom_res_imp.splits)
        thus ?thesis
          by simp
      next
        case True
        then obtain St Ct where ires: "i_result si = Some (Blossom_imp St Ct)"
          by blast
        have call: "Find_Aug_Path_call_1_conds s"
          using res by (simp add: Find_Aug_Path_call_1_conds_def)
        have I': "invar_1 s" "invar_search s"
          using I by (simp_all add: invars_def)
        obtain stem' C' where res': "search_result s = Some (Blossom stem' C')"
          and contract:
          "graph_input (search_graph s) (search_vertices s)"
          "matching_invar (search_graph s) (search_matching s)"
          "blossom (ugraph_abs (search_graph s)) (matching_abs (search_matching s)) stem' C'"
          "create_vert (search_vertices s) \<notin> set (search_vertices s) - set C'"
          "create_vert (search_vertices s) \<in> K"
          by (rule call_1_facts[OF Find_Aug_Path_axiom call I'])
        have sc: "stem' = stem" "C' = C"
          using res res' by simp_all
        note contract = contract[unfolded sc]
        have strict: "set (search_vertices s) \<subset> K"
          using I' by (simp add: invar_1_def)
        have cap: "length hs < cap"
          using contractions_less_cap[OF call I] L by simp
        define s' where "s' = Find_Aug_Path_upd1 s"
        note upd = upd1_fields[OF Find_Aug_Path_axiom res, folded s'_def]
        have I'': "invars s'"
          unfolding s'_def by (rule invars_upd1[OF call I])
        have inp': "graph_input (search_graph s') (search_vertices s')"
          "matching_invar (search_graph s') (search_matching s')"
          "length (search_vertices s') \<le> max_vertices"
          using I'' max_vertices
          by (auto simp: invars_def invar_1_def invar_size_def)
        have F: "Find_Aug_Path_impl s = Find_Aug_Path_impl s'"
          unfolding s'_def by (rule Find_Aug_Path_impl_upd1[OF res])
        have mbo: "match_blossom_opt_assn (search_result s) (Some (Blossom_imp St Ct)) =
            St \<mapsto>\<^sub>a stem * Ct \<mapsto>\<^sub>a C"
          by (simp add: res match_blossom_opt_assn_def match_blossom_res_assn_def)
        note BS = blos_search_imp_rule[OF inp'[unfolded upd(1-3)]]
        note CG = contract_graph_imp_rule[OF contract(1)]
        note CM = contract_matching_imp_rule[OF contract]
        have IH: "<contr_stack_assn ((i_graph si, i_matching si, Ct, create_vert (search_vertices s))
                      # hs) (i_contractions si) *
                    entries_assn (contractions s) hs *
                    graph_assn (search_graph s) (i_graph si) *
                    matching_assn (search_matching s) (i_matching si) *
                    Ct \<mapsto>\<^sub>a C *
                    graph_assn (search_graph s') Gi' * Vi' \<mapsto>\<^sub>a search_vertices s' *
                    matching_assn (search_matching s') Mi' *
                    match_blossom_opt_assn (search_result s') r>
                    f (si\<lparr>i_graph := Gi', i_vertices := Vi', i_matching := Mi', i_result := r\<rparr>)
                  <\<lambda>si'. state_assn Gi Mi (Find_Aug_Path_impl s) si' * true>"
          for Gi' Vi' Mi' r
          using 3[of s' "si\<lparr>i_graph := Gi', i_vertices := Vi', i_matching := Mi', i_result := r\<rparr>"
              "(i_graph si, i_matching si, Ct, create_vert (search_vertices s)) # hs"]
            B L I''
          unfolding F
          by (simp add: pre_assn_def upd(4) mult.assoc mult.left_commute)
        show ?thesis
          using cap
          by (sep_auto heap: create_vert_imp_rule[OF strict] CG contract_vertices_imp_rule CM
              contr_stack_push_rule BS[unfolded contract_vertices_def]
              IH[unfolded upd(5), unfolded upd(1-3) contract_vertices_def]
              simp: ires mbo)
      qed
    qed
  qed
qed

subsection \<open>Lifting\<close>

lemma aug_path_in_univ:
  assumes "graph_input H ws" "graph_augmenting_path (ugraph_abs H) (matching_abs N) p"
  shows "set p \<subseteq> K"
proof-
  have "2 \<le> length p"
    using assms(2) by (simp add: matching_augmenting_path_def)
  hence "set p \<subseteq> Vs (ugraph_abs H)"
    using assms(2) by (intro subset_path_Vs) auto
  thus ?thesis
    using Vs_ugraph_abs_subset_vs[OF assms(1)] graph_inputD(7)[OF assms(1)] by blast
qed

text \<open>The lifting pops every entry from the stack, but leaves the graphs, matchings and cycles of
  the entries in place.\<close>

lemma lift_path_imp_rule:
  "\<lbrakk>chain cs H N; graph_input H ws; graph_augmenting_path (ugraph_abs H) (matching_abs N) p\<rbrakk> \<Longrightarrow>
   <contr_stack_assn hs Si * entries_assn cs hs * Pt \<mapsto>\<^sub>a p> lift_path_imp Si Pt
   <\<lambda>Pt'. contr_stack_assn [] Si * entries_assn cs hs * Pt' \<mapsto>\<^sub>a lift_path cs p * true>"
proof(induction cs arbitrary: hs H N ws p Pt)
  case Nil
  show ?case
  proof(cases hs)
    case Nil
    thus ?thesis
      by (subst lift_path_imp.simps) (sep_auto heap: contr_stack_is_empty_rule)
  next
    case Cons
    thus ?thesis
      by simp
  qed
next
  case (Cons e cs)
  obtain E N' C u where e: "e = (E, N', C, u)"
    by (cases e)
  show ?case
  proof(cases hs)
    case Nil
    thus ?thesis
      by (simp add: e)
  next
    case (Cons h hs')
    obtain Ei Ni Ct u' where h: "h = (Ei, Ni, Ct, u')"
      by (cases h)
    show ?thesis
    proof(cases "u' = u")
      case False
      thus ?thesis
        by (simp add: Cons h e)
    next
      case True
      obtain ws' stem where c: "graph_input E ws'" "matching_invar E N'"
        "blossom (ugraph_abs E) (matching_abs N') stem C" "u \<notin> set ws' - set C" "u \<in> K"
        and H: "H = contract_graph E ws' C u" and N: "N = contract_matching N' C u"
        and ch: "chain cs E N'"
        using Cons.prems(1) by (auto simp: e)
      note facts' = contraction_facts[OF c]
      have p': "graph_augmenting_path (ugraph_abs E) (matching_abs N')
          (refine (\<lambda>v. isin (Graph.neighbourhood E v)) (mate_lookup N') u C p)"
        by (rule refine_correct[OF c]) (use Cons.prems(3) in \<open>simp add: H N\<close>)
      have pK: "set p \<subseteq> K"
        by (rule aug_path_in_univ[OF Cons.prems(2,3)])
      have CK: "set C \<subseteq> K"
        using facts'(2) Vs_ugraph_abs_subset_vs[OF c(1)] graph_inputD(7)[OF c(1)] by blast
      have two: "u \<in> set p \<Longrightarrow> 2 \<le> length p"
        using Cons.prems(3) by (simp add: matching_augmenting_path_def)
      have adj: "adj_ok (graph_assn E Ei * matching_assn N' Ni) (g_isin_imp Ei)
          (\<lambda>v. isin (Graph.neighbourhood E v)) K"
        unfolding adj_ok_def using graph_inputD(1)[OF c(1)] by (sep_auto heap: g_isin_rule)
      have mate: "mate_ok (graph_assn E Ei * matching_assn N' Ni) (lookup_partner_imp Ni)
          (mate_lookup N') K"
        unfolding mate_ok_def using facts'(7) by (sep_auto heap: mt.lookup_partner_rule)
      note RF = refine_imp_rule[OF facts'(3) two pK CK adj mate]
      note IH = Cons.IH[OF ch c(1) p', of hs']
      show ?thesis
        by (subst lift_path_imp.simps)
           (sep_auto heap: contr_stack_is_empty_rule contr_stack_top_rule contr_stack_pop_rule RF IH
            simp: Cons h e True)
    qed
  qed
qed

text \<open>The graph and the matching of the input are recovered from the bottom entry of the stack,
  or from the current state if the stack is empty.\<close>

lemma extract_input:
  "\<lbrakk>chain cs H N; bottom hs Hi Ni = (Gi, Mi)\<rbrakk> \<Longrightarrow>
   entries_assn cs hs * graph_assn H Hi * matching_assn N Ni \<Longrightarrow>\<^sub>A
   graph_assn G Gi * matching_assn M Mi * true"
proof(induction cs arbitrary: hs H N Hi Ni)
  case Nil
  thus ?case
    by (cases hs) (sep_auto+)
next
  case (Cons e cs)
  obtain E N' C u where e: "e = (E, N', C, u)"
    by (cases e)
  show ?case
  proof(cases hs)
    case Nil
    thus ?thesis
      by (simp add: e)
  next
    case (Cons h hs')
    obtain Ei Ni' Ct u' where h: "h = (Ei, Ni', Ct, u')"
      by (cases h)
    have ch: "chain cs E N'"
      using Cons.prems(1) by (auto simp: e)
    have IH: "entries_assn cs hs' * graph_assn E Ei * matching_assn N' Ni' \<Longrightarrow>\<^sub>A
        graph_assn G Gi * matching_assn M Mi * true"
      using Cons.prems(2) by (intro Cons.IH[OF ch]) (simp add: Cons h)
    have "entries_assn (e # cs) hs * graph_assn H Hi * matching_assn N Ni \<Longrightarrow>\<^sub>A
        (entries_assn cs hs' * graph_assn E Ei * matching_assn N' Ni') * true"
      by (sep_auto simp: Cons h e)
    also have "\<dots> \<Longrightarrow>\<^sub>A (graph_assn G Gi * matching_assn M Mi * true) * true"
      by (rule ent_star_mono[OF IH ent_refl])
    finally show ?thesis
      by (simp add: mult.assoc)
  qed
qed

subsection \<open>The result\<close>

lemma augmenting_path_imp_pre:
  "<pre_assn Gi Mi s si hs> augmenting_path_imp si
   <\<lambda>r. graph_assn G Gi * matching_assn M Mi * path_opt_assn (augmenting_path s) r * true>"
  unfolding pre_assn_def mult.assoc[symmetric]
proof(rule ht_extract_pre_pure(1), goal_cases)
  case 1
  hence B: "bottom hs (i_graph si) (i_matching si) = (Gi, Mi)" and I: "invars s"
    by blast+
  have ch: "chain (contractions s) (search_graph s) (search_matching s)"
    and I1: "graph_input (search_graph s) (search_vertices s)"
      "matching_invar (search_graph s) (search_matching s)"
    and IS: "invar_search s"
    using I by (simp_all add: invars_def invar_1_def)
  note EX = extract_input[OF ch B]
  text \<open>The assertion of the result is established first, without giving up the input.\<close>
  have raw: "<contr_stack_assn hs (i_contractions si) * entries_assn (contractions s) hs *
              graph_assn (search_graph s) (i_graph si) * i_vertices si \<mapsto>\<^sub>a search_vertices s *
              matching_assn (search_matching s) (i_matching si) *
              match_blossom_opt_assn (search_result s) (i_result si)>
             augmenting_path_imp si
             <\<lambda>r. (entries_assn (contractions s) hs * graph_assn (search_graph s) (i_graph si) *
                   matching_assn (search_matching s) (i_matching si)) *
                  (path_opt_assn (augmenting_path s) r * true)>"
  proof(cases "\<exists>p. search_result s = Some (Path p)")
    case True
    then obtain p where res: "search_result s = Some (Path p)"
      by blast
    show ?thesis
    proof(cases "\<exists>Pt. i_result si = Some (Path_imp Pt)")
      case False
      hence "match_blossom_opt_assn (search_result s) (i_result si) = false"
        using res
        by (auto simp: match_blossom_opt_assn_def match_blossom_res_assn_def
            split: option.splits match_blossom_res_imp.splits)
      thus ?thesis
        by simp
    next
      case True
      then obtain Pt where ires: "i_result si = Some (Path_imp Pt)"
        by blast
      have aug: "graph_augmenting_path (ugraph_abs (search_graph s)) (matching_abs (search_matching s)) p"
        using blos_search(1)[OF I1] IS res by (simp add: invar_search_def)
      have mbo: "match_blossom_opt_assn (Some (Path p)) (Some (Path_imp Pt)) = Pt \<mapsto>\<^sub>a p"
        by (simp add: match_blossom_opt_assn_def match_blossom_res_assn_def)
      show ?thesis
        by (sep_auto heap: lift_path_imp_rule[OF ch I1(1) aug]
            simp: augmenting_path_imp_def augmenting_path_def ires mbo res path_opt_assn_def)
    qed
  next
    case False
    have ap: "augmenting_path s = None"
      using False by (auto simp: augmenting_path_def split: option.splits match_blossom_res.splits)
    show ?thesis
    proof(cases "\<exists>Pt. i_result si = Some (Path_imp Pt)")
      case True
      hence "match_blossom_opt_assn (search_result s) (i_result si) = false"
        using False
        by (auto simp: match_blossom_opt_assn_def match_blossom_res_assn_def
            split: option.splits match_blossom_res.splits)
      thus ?thesis
        by simp
    next
      case not_path: False
      show ?thesis
        using not_path
        by (sep_auto simp: augmenting_path_imp_def ap path_opt_assn_def
            split: option.splits match_blossom_res_imp.splits)
    qed
  qed
  show ?case
    by (rule ht_cons_post[OF raw], rule ent_trans[OF ent_star_mono[OF EX ent_refl]]) sep_auto
qed

lemma augmenting_path_imp_rule:
  "<state_assn Gi Mi s si> augmenting_path_imp si
   <\<lambda>r. graph_assn G Gi * matching_assn M Mi * path_opt_assn (augmenting_path s) r * true>"
  unfolding state_assn_def
  by (sep_auto heap: augmenting_path_imp_pre)

subsection \<open>The whole search\<close>

lemma initial_state_imp_rule:
  "<graph_assn G Gi * matching_assn M Mi * Vi \<mapsto>\<^sub>a vs> initial_state_imp Gi Mi Vi
   <\<lambda>si. Vi \<mapsto>\<^sub>a vs * pre_assn Gi Mi initial_state si [] * true>"
  using invars_initial
  by (sep_auto heap: copy_array_imp_rule contr_stack_empty_rule
      blos_search_imp_rule[OF graph_input_G' matching_invar_M' max_vertices]
      simp: initial_state_imp_def pre_assn_def initial_state_def)

theorem \<^marker>\<open>provenance ai_human\<close> Find_Aug_Path_run_imp_rule:
  "<graph_assn G Gi * matching_assn M Mi * Vi \<mapsto>\<^sub>a vs> Find_Aug_Path_run_imp Gi Mi Vi
   <\<lambda>r. graph_assn G Gi * matching_assn M Mi * Vi \<mapsto>\<^sub>a vs *
        path_opt_assn Find_Aug_Path_run_impl r * true>"
  unfolding \<^marker>\<open>provenance ai\<close> Find_Aug_Path_run_imp_def Find_Aug_Path_run_impl_def
  by \<^marker>\<open>provenance ai\<close> (sep_auto heap: initial_state_imp_rule Find_Aug_Path_imp_refine augmenting_path_imp_rule)

theorem \<^marker>\<open>provenance ai_human\<close> Find_Aug_Path_run_imp_correct:
  "<graph_assn G Gi * matching_assn M Mi * Vi \<mapsto>\<^sub>a vs> Find_Aug_Path_run_imp Gi Mi Vi
   <\<lambda>r. \<exists>\<^sub>A P. graph_assn G Gi * matching_assn M Mi * Vi \<mapsto>\<^sub>a vs * path_opt_assn P r *
        \<up>((\<forall>q. P = Some q \<longrightarrow> graph_augmenting_path (ugraph_abs G) (matching_abs M) q) \<and>
          ((\<exists>p. graph_augmenting_path (ugraph_abs G) (matching_abs M) p) \<longrightarrow> P \<noteq> None)) *
        true>"
  using \<^marker>\<open>provenance ai\<close> Find_Aug_Path_run_impl_correct[OF Find_Aug_Path_axiom]
  by \<^marker>\<open>provenance ai\<close> (sep_auto heap: Find_Aug_Path_run_imp_rule)

end

end
