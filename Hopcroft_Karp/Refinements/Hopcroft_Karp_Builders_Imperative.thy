theory Hopcroft_Karp_Builders_Imperative
  imports Hopcroft_Karp_Phase_Imperative Imperative.Array_Folds
begin

section \<open>Imperative Builders of the Phase\<close>

text \<open>The builders of the phase, implemented imperatively. As in the functional phase, the
  edges and the vertices are lists, here stored in arrays, and every builder is a fold over one
  of them. The folds use only primitive operations, which correspond to the operations assumed
  by the functional phase: the lookup of a mate, the empty graph and the insertion of an edge,
  the empty set and the insertion into the sets of sources, the membership test in the visited
  sets, the lookup of a distance, the operations on the sets of copies and on the stack, and the
  extension of the store of paths. The graph and set representations remain abstract.\<close>

subsection \<open>The builders as folds\<close>

text \<open>The functional builders, written as the folds which the imperative builders perform.\<close>

context Hopcroft_Karp_Phase
begin

lemma free_sources_foldr:
  "foldr (\<lambda>v (b, S). if mate_get m v = nil then (False, insert v S) else (b, S)) vs
     (True, vset_empty) = (free_vertices vs m = [], free_vertex_set vs m)"
  by (induction vs) (auto simp: free_vertices_def free_vertex_set_def split: prod.splits)

lemma alt_graphs_foldl:
  "foldl (\<lambda>(M, U) (u, v). if mate_get m u = v then (G.add_edge M u v, U)
                          else (M, G.add_edge U u v)) (M0, U0) es =
   (foldl (\<lambda>G (u, v). G.add_edge G u v) M0 (filter (\<lambda>(u, v). mate_get m u = v) es),
    foldl (\<lambda>G (u, v). G.add_edge G u v) U0 (filter (\<lambda>(u, v). mate_get m u \<noteq> v) es))"
  by (induction es arbitrary: M0 U0) auto

lemma alt_graphs_from_list:
  "foldl (\<lambda>(M, U) (u, v). if mate_get m u = v then (G.add_edge M u v, U)
                          else (M, G.add_edge U u v)) (empty, empty) es =
   (G.from_list (matched_edges es m), G.from_list (unmatched_edges es m))"
  by (simp add: alt_graphs_foldl G.from_list_def matched_edges_def unmatched_edges_def)

definition "copy_edge m VE VO (d :: 'v labelled_vtx \<Rightarrow> nat) =
  (\<lambda>(u, v). if mate_get m u = v
           then (if u \<in> VO \<and> v \<in> VE \<and> d (Vtx Even v) = d (Vtx Odd u) + 1
                 then [(Vtx Even v, Vtx Odd u)] else [])
           else (if u \<in> VE \<and> v \<in> VO \<and> d (Vtx Odd v) = d (Vtx Even u) + 1
                 then [(Vtx Odd v, Vtx Even u)] else []))"

lemma copies_edges_dist_concat:
  "copies_edges_dist es m VE VO d = concat (map (copy_edge m VE VO d) es)"
  by (simp add: copies_edges_dist_def copy_edge_def)

definition "add_copies GC xs =
  foldl (\<lambda>(G, C) (x, y). (CGraph.add_edge G x y, Set.insert y (Set.insert x C))) GC xs"

lemma add_copies_eq:
  "add_copies (G, C) xs = (foldl (\<lambda>G (x, y). CGraph.add_edge G x y) G xs, C \<union> dVs (set xs))"
  by (induction xs arbitrary: G C) (auto simp: add_copies_def dVs_eq)

lemma copies_foldl:
  "foldl (\<lambda>GC e. add_copies GC (copy_edge m VE VO d e)) (c_empty, {}) es =
   (CGraph.from_list (copies_edges_dist es m VE VO d), dVs (set (copies_edges_dist es m VE VO d)))"
proof-
  have "foldl (\<lambda>GC e. add_copies GC (copy_edge m VE VO d e)) GC es =
          add_copies GC (concat (map (copy_edge m VE VO d) es))" for GC
    by (induction es arbitrary: GC) (simp_all add: add_copies_def)
  thus ?thesis
    by (simp add: add_copies_eq CGraph.from_list_def copies_edges_dist_concat)
qed

definition "root_cond m VO t \<longleftrightarrow> mate_get m t = nil \<and> t \<in> VO"

definition "min_step m VO (d :: 'v labelled_vtx \<Rightarrow> nat) k t =
  (if root_cond m VO t
   then Some (case k of None \<Rightarrow> d (Vtx Odd t) | Some k' \<Rightarrow> min (d (Vtx Odd t)) k')
   else k)"

lemma min_step_Some:
  "foldl (min_step m VO d) (Some a) xs =
     Some (fold min (map (\<lambda>t. d (Vtx Odd t)) (filter (root_cond m VO) xs)) a)"
  by (induction xs arbitrary: a) (auto simp: min_step_def)

lemma min_step_None:
  "foldl (min_step m VO d) None xs =
     (case filter (root_cond m VO) xs of [] \<Rightarrow> None
      | t # ts \<Rightarrow> Some (fold min (map (\<lambda>t. d (Vtx Odd t)) ts) (d (Vtx Odd t))))"
  by (induction xs) (simp_all add: min_step_def[where k = None] min_step_Some)

definition "push_step m VO (d :: 'v labelled_vtx \<Rightarrow> nat) k t S =
  (if root_cond m VO t \<and> Some (d (Vtx Odd t)) = k then Vtx Odd t # S else S)"

lemma push_step_foldr:
  "foldr (push_step m VO d k) xs [] =
     map (Vtx Odd) (filter (\<lambda>t. root_cond m VO t \<and> Some (d (Vtx Odd t)) = k) xs)"
  by (induction xs) (simp_all add: push_step_def)

lemma push_step_length: "length (foldr (push_step m VO d k) xs []) \<le> length xs"
  by (simp add: push_step_foldr)

lemma filter_root_cond: "filter (root_cond m VO) vs = filter (\<lambda>t. t \<in> VO) (free_vertices vs m)"
  unfolding free_vertices_def filter_filter
  by (rule filter_cong) (simp_all add: root_cond_def)

lemma phase_roots_folds:
  "foldr (push_step m VO d (foldl (min_step m VO d) None vs)) vs [] = phase_roots_dist vs m VO d"
proof-
  have F: "filter (\<lambda>t. root_cond m VO t \<and> Some (d (Vtx Odd t)) = k) vs =
             filter (\<lambda>t. Some (d (Vtx Odd t)) = k) (filter (root_cond m VO) vs)" for k
    by simp
  show ?thesis
    unfolding push_step_foldr min_step_None F
    by (cases "filter (root_cond m VO) vs")
       (simp_all add: phase_roots_dist_def filter_root_cond[symmetric] Let_def)
qed

definition "block_copy C x A = (if x \<in> C then Set.insert x A else A)"

lemma block_copies_Cons:
  "A \<union> {w \<in> C. vtx w \<in> vtx ` set (x # p)} =
     block_copy C (Vtx Odd (vtx x)) (block_copy C (Vtx Even (vtx x)) A) \<union>
     {w \<in> C. vtx w \<in> vtx ` set p}"
proof(intro set_eqI iffI)
  fix w
  assume "w \<in> A \<union> {w \<in> C. vtx w \<in> vtx ` set (x # p)}"
  moreover obtain q y where "w = Vtx q y"
    by (cases w)
  ultimately show "w \<in> block_copy C (Vtx Odd (vtx x)) (block_copy C (Vtx Even (vtx x)) A) \<union>
                         {w \<in> C. vtx w \<in> vtx ` set p}"
    by (cases q) (auto simp: block_copy_def)
qed (auto simp: block_copy_def split: if_splits)

end

subsection \<open>The program\<close>

text \<open>The primitive operations. The edges and the vertices are given as arrays.\<close>

locale Hopcroft_Karp_Builders_Imperative_spec =
  fixes nil :: "'v::heap"
    and mate_get_imp :: "'mi \<Rightarrow> 'v \<Rightarrow> 'v Heap"
    and g_empty_imp :: "'imp_G Heap"
    and g_add_edge_imp :: "'imp_G \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'imp_G Heap"
    and c_empty_imp :: "'gi Heap"
    and c_add_edge_imp :: "'gi \<Rightarrow> 'v labelled_vtx \<Rightarrow> 'v labelled_vtx \<Rightarrow> 'gi Heap"
    and src_empty_imp :: "'imp_src Heap"
    and src_insert_imp :: "'v \<Rightarrow> 'imp_src \<Rightarrow> 'imp_src Heap"
    and vis_isin_imp :: "'imp_vis \<Rightarrow> 'v \<Rightarrow> bool Heap"
    and dist_lookup_imp :: "'imp_dist \<Rightarrow> 'v labelled_vtx \<Rightarrow> nat Heap"
    and set_empty_imp :: "'si Heap"
    and set_insert_imp :: "'v labelled_vtx \<Rightarrow> 'si \<Rightarrow> unit Heap"
    and set_isin_imp :: "'si \<Rightarrow> 'v labelled_vtx \<Rightarrow> bool Heap"
    and stack_empty_imp :: "'stki Heap"
    and stack_is_empty_imp :: "'stki \<Rightarrow> bool Heap"
    and stack_top_imp :: "'stki \<Rightarrow> 'v labelled_vtx Heap"
    and stack_push_imp :: "'stki \<Rightarrow> 'v labelled_vtx \<Rightarrow> unit Heap"
    and stack_pop_imp :: "'stki \<Rightarrow> unit Heap"
    and paths_new_imp :: "'ips \<Rightarrow> 'ips Heap"
    and paths_snoc_imp :: "'ips \<Rightarrow> 'v labelled_vtx \<Rightarrow> 'ips Heap"
begin

text \<open>The sources: a right fold over the vertices, mirroring @{term "foldr insert"} over the free
  vertices. The flag records whether there is no free vertex.\<close>

definition "free_sources_step Mi =
  (\<lambda>v (b, S). do { mv \<leftarrow> mate_get_imp Mi v;
                  if mv = nil then do { S' \<leftarrow> src_insert_imp v S; return (False, S') }
                  else return (b, S) })"

definition "free_sources_imp (Vi :: 'v array) Mi =
  do { n \<leftarrow> Array.len Vi;
       S \<leftarrow> src_empty_imp;
       array_foldr Vi n (free_sources_step Mi) (True, S) }"

text \<open>The matching and the non-matching graph: a left fold over the edges, mirroring
  @{const Pair_Graph_Specs.from_list} of the filtered edges.\<close>

definition "alt_graphs_step Mi =
  (\<lambda>(u, v) (M, U). do { mu \<leftarrow> mate_get_imp Mi u;
                        if mu = v then do { M' \<leftarrow> g_add_edge_imp M u v; return (M', U) }
                        else do { U' \<leftarrow> g_add_edge_imp U u v; return (M, U') } })"

definition "alt_graphs_imp (Ei :: ('v \<times> 'v) array) Mi =
  do { n \<leftarrow> Array.len Ei;
       M \<leftarrow> g_empty_imp;
       U \<leftarrow> g_empty_imp;
       array_foldl Ei 0 n (alt_graphs_step Mi) (M, U) }"

text \<open>The graph of copies and the set of its vertices: a left fold over the edges, mirroring
  @{const Hopcroft_Karp_Phase.copies_edges_dist} and @{const Pair_Graph_Specs.from_list}.\<close>

definition "add_copy_imp Gi CVi x y =
  do { set_insert_imp x CVi;
       set_insert_imp y CVi;
       c_add_edge_imp Gi x y }"

definition "copies_step Mi VEi VOi Di =
  (\<lambda>(u, v) (Gi, CVi).
     do { mu \<leftarrow> mate_get_imp Mi u;
          if mu = v
          then do { a \<leftarrow> vis_isin_imp VOi u;
                    b \<leftarrow> vis_isin_imp VEi v;
                    du \<leftarrow> dist_lookup_imp Di (Vtx Odd u);
                    dv \<leftarrow> dist_lookup_imp Di (Vtx Even v);
                    if a \<and> b \<and> dv = du + 1
                    then do { Gi' \<leftarrow> add_copy_imp Gi CVi (Vtx Even v) (Vtx Odd u); return (Gi', CVi) }
                    else return (Gi, CVi) }
          else do { a \<leftarrow> vis_isin_imp VEi u;
                    b \<leftarrow> vis_isin_imp VOi v;
                    du \<leftarrow> dist_lookup_imp Di (Vtx Even u);
                    dv \<leftarrow> dist_lookup_imp Di (Vtx Odd v);
                    if a \<and> b \<and> dv = du + 1
                    then do { Gi' \<leftarrow> add_copy_imp Gi CVi (Vtx Odd v) (Vtx Even u); return (Gi', CVi) }
                    else return (Gi, CVi) } })"

definition "copies_graph_imp (Ei :: ('v \<times> 'v) array) Mi VEi VOi Di =
  do { n \<leftarrow> Array.len Ei;
       Gi \<leftarrow> c_empty_imp;
       CVi \<leftarrow> set_empty_imp;
       array_foldl Ei 0 n (copies_step Mi VEi VOi Di) (Gi, CVi) }"

text \<open>The roots: a left fold over the vertices computes the minimal level of the free vertices
  with an odd copy, and a right fold pushes the odd copies of those of minimal level.\<close>

definition "root_cond_imp Mi VOi t =
  do { mt \<leftarrow> mate_get_imp Mi t;
       a \<leftarrow> vis_isin_imp VOi t;
       return (mt = nil \<and> a) }"

definition "min_level_step Mi VOi Di =
  (\<lambda>t k. do { c \<leftarrow> root_cond_imp Mi VOi t;
              if c then do { dt \<leftarrow> dist_lookup_imp Di (Vtx Odd t);
                             return (Some (case k of None \<Rightarrow> dt | Some k' \<Rightarrow> min dt k')) }
              else return k })"

definition "push_roots_step Mi VOi Di k =
  (\<lambda>t Ri. do { c \<leftarrow> root_cond_imp Mi VOi t;
               if c then do { dt \<leftarrow> dist_lookup_imp Di (Vtx Odd t);
                              if Some dt = k then do { stack_push_imp Ri (Vtx Odd t); return Ri }
                              else return Ri }
               else return Ri })"

definition "phase_roots_imp (Vi :: 'v array) Mi VOi Di =
  do { n \<leftarrow> Array.len Vi;
       k \<leftarrow> array_foldl Vi 0 n (min_level_step Mi VOi Di) None;
       Ri \<leftarrow> stack_empty_imp;
       array_foldr Vi n (push_roots_step Mi VOi Di k) Ri }"

text \<open>The test whether a copy has level 0.\<close>

definition "level_zero_imp Di w =
  do { d \<leftarrow> dist_lookup_imp Di w;
       return (d = 0) }"

text \<open>The commitment of a found path: the path is popped from the stack and appended to a new
  path of the store, and the copies of its vertices which are vertices of the graph of copies are
  avoided, mirroring @{const Hopcroft_Karp_Phase.blocked_copies}.\<close>

definition "block_copy_imp CVi Ai x =
  do { b \<leftarrow> set_isin_imp CVi x;
       if b then set_insert_imp x Ai else return () }"

partial_function (heap) commit_loop :: "'si \<Rightarrow> 'stki \<Rightarrow> 'si \<Rightarrow> 'ips \<Rightarrow> ('si \<times> 'ips) Heap" where
  "commit_loop CVi Si Ai Psi =
     do { e \<leftarrow> stack_is_empty_imp Si;
          if e then return (Ai, Psi)
          else do { w \<leftarrow> stack_top_imp Si;
                    stack_pop_imp Si;
                    block_copy_imp CVi Ai (Vtx Even (vtx w));
                    block_copy_imp CVi Ai (Vtx Odd (vtx w));
                    Psi' \<leftarrow> paths_snoc_imp Psi w;
                    commit_loop CVi Si Ai Psi' } }"

definition "commit_path_imp CVi Si Ai Psi =
  do { Psi' \<leftarrow> paths_new_imp Psi;
       commit_loop CVi Si Ai Psi' }"

end

subsection \<open>Correctness\<close>

text \<open>The primitive operations meet the specifications of the corresponding functional
  operations, for vertices within the universe @{term univ} and copies within its preimage under
  @{const vtx}.\<close>

locale Hopcroft_Karp_Builders_Imperative =
  Hopcroft_Karp_Phase where K = univ and lookup = lookup and c_lookup = c_lookup and mate_get = mate_get
    and lookup_dist = lookup_dist +
  Hopcroft_Karp_Builders_Imperative_spec where mate_get_imp = mate_get_imp
    and g_add_edge_imp = g_add_edge_imp and c_add_edge_imp = c_add_edge_imp
    and src_insert_imp = src_insert_imp and vis_isin_imp = vis_isin_imp
    and dist_lookup_imp = dist_lookup_imp and paths_snoc_imp = paths_snoc_imp
    and set_insert_imp = set_insert_imp and stack_push_imp = stack_push_imp +
  stk: bounded_stack_imp where stack_abstract = stack_abstract and stack_push_imp = stack_push_imp +
  cset: fixed_univ_set_basic_imp where U = "vtx -` univ"
    and fixed_univ_set_invar = "\<lambda>S. S \<subseteq> vtx -` univ"
    and fixed_univ_set_abstract = id and fixed_univ_set_empty = "{}"
    and fixed_univ_set_insert = Set.insert and fixed_univ_set_delete = "\<lambda>x S. S - {x}"
    and fixed_univ_set_isin = "\<lambda>S x. x \<in> S" and fixed_univ_set_assn = set_assn
    and fixed_univ_set_insert_imp = set_insert_imp and fixed_univ_set_isin_imp = set_isin_imp
  for lookup :: "'adjmap \<Rightarrow> 'v::heap \<Rightarrow> 'vset option"
  and c_lookup :: "'cadjmap \<Rightarrow> 'v labelled_vtx \<Rightarrow> 'cvset option"
  and mate_get :: "'mate \<Rightarrow> 'v \<Rightarrow> 'v"
  and lookup_dist :: "'dmap \<Rightarrow> 'v labelled_vtx \<Rightarrow> enat option"
  and mate_get_imp :: "'mi \<Rightarrow> 'v \<Rightarrow> 'v Heap"
  and g_add_edge_imp :: "'imp_G \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'imp_G Heap"
  and c_add_edge_imp :: "'gi \<Rightarrow> 'v labelled_vtx \<Rightarrow> 'v labelled_vtx \<Rightarrow> 'gi Heap"
  and src_insert_imp :: "'v \<Rightarrow> 'imp_src \<Rightarrow> 'imp_src Heap"
  and vis_isin_imp :: "'imp_vis \<Rightarrow> 'v \<Rightarrow> bool Heap"
  and dist_lookup_imp :: "'imp_dist \<Rightarrow> 'v labelled_vtx \<Rightarrow> nat Heap"
  and paths_snoc_imp :: "'ips \<Rightarrow> 'v labelled_vtx \<Rightarrow> 'ips Heap"
  and set_insert_imp :: "'v labelled_vtx \<Rightarrow> 'si \<Rightarrow> unit Heap"
  and stack_push_imp :: "'stki \<Rightarrow> 'v labelled_vtx \<Rightarrow> unit Heap"
  and stack_abstract :: "'s \<Rightarrow> 'v labelled_vtx list"
  and univ :: "'v set"
  and set_assn :: "'v labelled_vtx set \<Rightarrow> 'si \<Rightarrow> assn" +
  fixes dist_lookup :: "'dist \<Rightarrow> 'v labelled_vtx \<Rightarrow> nat"
    and mate_assn :: "'mate \<Rightarrow> 'mi \<Rightarrow> assn"
    and graph_assn :: "'adjmap \<Rightarrow> 'imp_G \<Rightarrow> assn"
    and cgraph_assn :: "'cadjmap \<Rightarrow> 'gi \<Rightarrow> assn"
    and imp_src_assn :: "'vset \<Rightarrow> 'imp_src \<Rightarrow> assn"
    and imp_vis_assn :: "'vset \<Rightarrow> 'imp_vis \<Rightarrow> assn"
    and imp_dist_assn :: "'dist \<Rightarrow> 'imp_dist \<Rightarrow> assn"
    and paths_assn :: "'v labelled_vtx list list \<Rightarrow> 'ips \<Rightarrow> assn"
  assumes mate_get_rule:
    "\<And>m Mi v. <mate_assn m Mi> mate_get_imp Mi v <\<lambda>r. mate_assn m Mi * \<up>(r = mate_get m v)>"
  and g_empty_rule: "<emp> g_empty_imp <graph_assn empty>"
  and g_add_edge_rule:
    "\<And>H Hi u v. \<lbrakk>u \<in> univ; v \<in> univ\<rbrakk> \<Longrightarrow>
     <graph_assn H Hi> g_add_edge_imp Hi u v <graph_assn (G.add_edge H u v)>"
  and c_empty_rule: "<emp> c_empty_imp <cgraph_assn c_empty>"
  and c_add_edge_rule:
    "\<And>H Hi x y. \<lbrakk>x \<in> vtx -` univ; y \<in> vtx -` univ\<rbrakk> \<Longrightarrow>
     <cgraph_assn H Hi> c_add_edge_imp Hi x y <cgraph_assn (CGraph.add_edge H x y)>"
  and src_empty_rule: "<emp> src_empty_imp <imp_src_assn vset_empty>"
  and src_insert_rule:
    "\<And>S Si v. v \<in> univ \<Longrightarrow> <imp_src_assn S Si> src_insert_imp v Si <imp_src_assn (insert v S)>"
  and vis_isin_rule:
    "\<And>V Vi v. \<lbrakk>vset_inv V; v \<in> univ\<rbrakk> \<Longrightarrow>
     <imp_vis_assn V Vi> vis_isin_imp Vi v <\<lambda>r. imp_vis_assn V Vi * \<up>(r \<longleftrightarrow> v \<in> t_set V)>"
  and dist_lookup_rule:
    "\<And>D Di w. vtx w \<in> univ \<Longrightarrow>
     <imp_dist_assn D Di> dist_lookup_imp Di w <\<lambda>r. imp_dist_assn D Di * \<up>(r = dist_lookup D w)>"
  and set_empty_rule: "<emp> set_empty_imp <set_assn {}>"
  and paths_new_rule: "\<And>ps Psi. <paths_assn ps Psi> paths_new_imp Psi <paths_assn ([] # ps)>"
  and paths_snoc_rule:
    "\<And>q ps Psi w. <paths_assn (q # ps) Psi> paths_snoc_imp Psi w <paths_assn ((q @ [w]) # ps)>"
begin

subsubsection \<open>The stack\<close>

definition "stk_assn xs Si = (\<exists>\<^sub>A S. stack_assn S Si * \<up>(stack_invar S \<and> stack_abstract S = xs))"

lemma stk_empty_rule: "<emp> stack_empty_imp <stk_assn []>"
  unfolding stk_assn_def
  by (sep_auto heap: stk.stack_empty_rule simp: stk.stack_empty)

lemma stk_is_empty_rule:
  "<stk_assn xs Si> stack_is_empty_imp Si <\<lambda>r. stk_assn xs Si * \<up>(r \<longleftrightarrow> xs = [])>"
  unfolding stk_assn_def
  by (sep_auto heap: stk.stack_is_empty_rule simp: stk.stack_is_empty)

lemma stk_top_rule:
  "xs \<noteq> [] \<Longrightarrow> <stk_assn xs Si> stack_top_imp Si <\<lambda>r. stk_assn xs Si * \<up>(r = hd xs)>"
  unfolding stk_assn_def
  by (sep_auto heap: stk.stack_top_rule simp: stk.stack_top)

lemma stk_push_rule:
  "length xs < cap \<Longrightarrow> <stk_assn xs Si> stack_push_imp Si x <\<lambda>_. stk_assn (x # xs) Si>"
  unfolding stk_assn_def
  by (sep_auto heap: stk.stack_push_rule simp: stk.stack_push)

lemma stk_pop_rule:
  "xs \<noteq> [] \<Longrightarrow> <stk_assn xs Si> stack_pop_imp Si <\<lambda>_. stk_assn (tl xs) Si>"
  unfolding stk_assn_def
  by (sep_auto heap: stk.stack_pop_rule simp: stk.stack_pop)

subsubsection \<open>The sources\<close>

lemma free_sources_step_rule:
  assumes "v \<in> univ"
  shows "<(case acc of (b, S) \<Rightarrow> \<lambda>(bi, Si). imp_src_assn S Si * \<up>(bi = b)) acci * mate_assn m Mi>
           free_sources_step Mi v acci
         <\<lambda>r. (case (\<lambda>(b, S). if mate_get m v = nil then (False, insert v S) else (b, S)) acc of
                (b, S) \<Rightarrow> \<lambda>(bi, Si). imp_src_assn S Si * \<up>(bi = b)) r * mate_assn m Mi>"
  using assms
  by (cases acc; cases acci)
     (sep_auto heap: mate_get_rule src_insert_rule simp: free_sources_step_def)

lemma free_sources_imp_rule:
  assumes "set vs \<subseteq> univ"
  shows "<Vi \<mapsto>\<^sub>a vs * mate_assn m Mi> free_sources_imp Vi Mi
         <\<lambda>(b, Fi). Vi \<mapsto>\<^sub>a vs * mate_assn m Mi * imp_src_assn (free_vertex_set vs m) Fi *
                   \<up>(b \<longleftrightarrow> free_vertices vs m = [])>"
proof-
  note fold = array_foldr_all_rule[where acc_assn = "\<lambda>(b, S) (bi, Si). imp_src_assn S Si * \<up>(bi = b)"
    and f = "\<lambda>v (b, S). if mate_get m v = nil then (False, insert v S) else (b, S)"
    and F = "mate_assn m Mi" and fi = "free_sources_step Mi" and xs = vs and arr = Vi,
    OF free_sources_step_rule, OF subsetD[OF assms]]
  have R: "<Vi \<mapsto>\<^sub>a vs * imp_src_assn vset_empty S * mate_assn m Mi>
             array_foldr Vi (length vs) (free_sources_step Mi) (True, S)
           <\<lambda>r. Vi \<mapsto>\<^sub>a vs * (case r of (b, Fi) \<Rightarrow> imp_src_assn (free_vertex_set vs m) Fi *
                       \<up>(b \<longleftrightarrow> free_vertices vs m = [])) * mate_assn m Mi>" for S
    using fold[of "(True, vset_empty)" "(True, S)"]
    unfolding free_sources_foldr
    by simp
  show ?thesis
    unfolding free_sources_imp_def
    by (sep_auto heap: src_empty_rule R)
qed

subsubsection \<open>The matching and the non-matching graph\<close>

lemma alt_graphs_step_rule:
  assumes "e \<in> univ \<times> univ"
  shows "<(case acc of (M, U) \<Rightarrow> \<lambda>(Mgi, Ugi). graph_assn M Mgi * graph_assn U Ugi) acci *
          mate_assn m Mi>
           alt_graphs_step Mi e acci
         <\<lambda>r. (case (\<lambda>(M, U) (u, v). if mate_get m u = v then (G.add_edge M u v, U)
                                     else (M, G.add_edge U u v)) acc e of
                (M, U) \<Rightarrow> \<lambda>(Mgi, Ugi). graph_assn M Mgi * graph_assn U Ugi) r * mate_assn m Mi>"
  using assms
  by (cases e; cases acc; cases acci)
     (sep_auto heap: mate_get_rule g_add_edge_rule simp: alt_graphs_step_def)

lemma alt_graphs_imp_rule:
  assumes "set edges \<subseteq> univ \<times> univ"
  shows "<Ei \<mapsto>\<^sub>a edges * mate_assn m Mi> alt_graphs_imp Ei Mi
         <\<lambda>(Mgi, Ugi). Ei \<mapsto>\<^sub>a edges * mate_assn m Mi *
                       graph_assn (G.from_list (matched_edges edges m)) Mgi *
                       graph_assn (G.from_list (unmatched_edges edges m)) Ugi>"
proof-
  note fold = array_foldl_all_rule[where
      acc_assn = "\<lambda>(M, U) (Mgi, Ugi). graph_assn M Mgi * graph_assn U Ugi"
    and f = "\<lambda>(M, U) (u, v). if mate_get m u = v then (G.add_edge M u v, U)
                            else (M, G.add_edge U u v)"
    and F = "mate_assn m Mi" and fi = "alt_graphs_step Mi" and xs = edges and arr = Ei,
    OF alt_graphs_step_rule, OF subsetD[OF assms]]
  have R: "<Ei \<mapsto>\<^sub>a edges * (graph_assn empty M * graph_assn empty U) * mate_assn m Mi>
             array_foldl Ei 0 (length edges) (alt_graphs_step Mi) (M, U)
           <\<lambda>r. Ei \<mapsto>\<^sub>a edges *
                (case r of (Mgi, Ugi) \<Rightarrow> graph_assn (G.from_list (matched_edges edges m)) Mgi *
                                        graph_assn (G.from_list (unmatched_edges edges m)) Ugi) *
                mate_assn m Mi>" for M U
    using fold[of "(empty, empty)" "(M, U)"]
    unfolding alt_graphs_from_list
    by simp
  show ?thesis
    unfolding alt_graphs_imp_def
    by (sep_auto heap: g_empty_rule R)
qed

subsubsection \<open>The graph of copies\<close>

lemma copies_step_rule:
  assumes "e \<in> univ \<times> univ" "vset_inv VE" "vset_inv VO"
  shows "<(case acc of (H, C) \<Rightarrow> \<lambda>(Gi, CVi). cgraph_assn H Gi * set_assn C CVi * \<up>(C \<subseteq> vtx -` univ))
            acci *
          (mate_assn m Mi * imp_vis_assn VE VEi * imp_vis_assn VO VOi * imp_dist_assn D Di)>
           copies_step Mi VEi VOi Di e acci
         <\<lambda>r. (case add_copies acc (copy_edge m (t_set VE) (t_set VO) (dist_lookup D) e) of
                (H, C) \<Rightarrow> \<lambda>(Gi, CVi). cgraph_assn H Gi * set_assn C CVi * \<up>(C \<subseteq> vtx -` univ)) r *
              (mate_assn m Mi * imp_vis_assn VE VEi * imp_vis_assn VO VOi * imp_dist_assn D Di)>"
  using assms (*takes long*)
  by (cases e; cases acc; cases acci)
     (sep_auto heap: mate_get_rule vis_isin_rule dist_lookup_rule cset.fixed_univ_set_insert_rule
                     c_add_edge_rule
               simp: copies_step_def add_copy_imp_def copy_edge_def add_copies_def)

lemma copies_graph_imp_rule:
  assumes "set edges \<subseteq> univ \<times> univ" "vset_inv VE" "vset_inv VO"
  shows "<Ei \<mapsto>\<^sub>a edges * mate_assn m Mi * imp_vis_assn VE VEi * imp_vis_assn VO VOi *
          imp_dist_assn D Di>
           copies_graph_imp Ei Mi VEi VOi Di
         <\<lambda>(Gi, CVi). Ei \<mapsto>\<^sub>a edges * mate_assn m Mi * imp_vis_assn VE VEi * imp_vis_assn VO VOi *
           imp_dist_assn D Di *
           cgraph_assn (CGraph.from_list (copies_edges_dist edges m (t_set VE) (t_set VO) (dist_lookup D)))
             Gi *
           set_assn (dVs (set (copies_edges_dist edges m (t_set VE) (t_set VO) (dist_lookup D)))) CVi>"
proof-
  note fold = array_foldl_all_rule[where
      acc_assn = "\<lambda>(H, C) (Gi, CVi). cgraph_assn H Gi * set_assn C CVi * \<up>(C \<subseteq> vtx -` univ)"
    and f = "\<lambda>GC e. add_copies GC (copy_edge m (t_set VE) (t_set VO) (dist_lookup D) e)"
    and F = "mate_assn m Mi * imp_vis_assn VE VEi * imp_vis_assn VO VOi * imp_dist_assn D Di"
    and fi = "copies_step Mi VEi VOi Di" and xs = edges and arr = Ei,
    OF copies_step_rule, OF subsetD[OF assms(1)] assms(2,3)]
  have R: "<Ei \<mapsto>\<^sub>a edges * (cgraph_assn c_empty Gi * set_assn {} CVi) *
            (mate_assn m Mi * imp_vis_assn VE VEi * imp_vis_assn VO VOi * imp_dist_assn D Di)>
             array_foldl Ei 0 (length edges) (copies_step Mi VEi VOi Di) (Gi, CVi)
           <\<lambda>r. Ei \<mapsto>\<^sub>a edges *
                (case r of (Gi, CVi) \<Rightarrow>
                   cgraph_assn (CGraph.from_list (copies_edges_dist edges m (t_set VE) (t_set VO)
                                                    (dist_lookup D))) Gi *
                   set_assn (dVs (set (copies_edges_dist edges m (t_set VE) (t_set VO) (dist_lookup D))))
                     CVi * true) *
                (mate_assn m Mi * imp_vis_assn VE VEi * imp_vis_assn VO VOi * imp_dist_assn D Di)>"
    for Gi CVi
    using fold[of "(c_empty, {})" "(Gi, CVi)"]
    unfolding copies_foldl
    by (sep_auto simp: case_prod_beta')
  show ?thesis
    unfolding copies_graph_imp_def
    by (sep_auto heap: c_empty_rule set_empty_rule R)
qed

subsubsection \<open>The roots\<close>

lemma root_cond_imp_rule:
  assumes "vset_inv VO" "t \<in> univ"
  shows "<mate_assn m Mi * imp_vis_assn VO VOi> root_cond_imp Mi VOi t
         <\<lambda>r. mate_assn m Mi * imp_vis_assn VO VOi * \<up>(r \<longleftrightarrow> root_cond m (t_set VO) t)>"
  using assms
  by (sep_auto heap: mate_get_rule vis_isin_rule simp: root_cond_imp_def root_cond_def)

lemma min_level_step_rule:
  assumes "vset_inv VO" "t \<in> univ"
  shows "<\<up>(ki = k) * (mate_assn m Mi * imp_vis_assn VO VOi * imp_dist_assn D Di)>
           min_level_step Mi VOi Di t ki
         <\<lambda>r. \<up>(r = min_step m (t_set VO) (dist_lookup D) k t) *
              (mate_assn m Mi * imp_vis_assn VO VOi * imp_dist_assn D Di)>"
  using assms
  by (sep_auto heap: root_cond_imp_rule dist_lookup_rule simp: min_level_step_def min_step_def)

lemma push_roots_step_rule:
  assumes "vset_inv VO" "t \<in> univ" "length S < cap"
  shows "<stk_assn S Ri * (mate_assn m Mi * imp_vis_assn VO VOi * imp_dist_assn D Di)>
           push_roots_step Mi VOi Di k t Ri
         <\<lambda>r. stk_assn (push_step m (t_set VO) (dist_lookup D) k t S) r *
              (mate_assn m Mi * imp_vis_assn VO VOi * imp_dist_assn D Di)>"
  using assms
  by (sep_auto heap: root_cond_imp_rule dist_lookup_rule stk_push_rule
               simp: push_roots_step_def push_step_def)

lemma phase_roots_imp_rule:
  assumes "set vs \<subseteq> univ" "length vs \<le> cap" "vset_inv VO"
  shows "<Vi \<mapsto>\<^sub>a vs * mate_assn m Mi * imp_vis_assn VO VOi * imp_dist_assn D Di>
           phase_roots_imp Vi Mi VOi Di
         <\<lambda>Ri. Vi \<mapsto>\<^sub>a vs * mate_assn m Mi * imp_vis_assn VO VOi * imp_dist_assn D Di *
               stk_assn (phase_roots_dist vs m (t_set VO) (dist_lookup D)) Ri>"
proof-
  let ?F = "mate_assn m Mi * imp_vis_assn VO VOi * imp_dist_assn D Di"
  note fold1 = array_foldl_all_rule[where acc_assn = "\<lambda>k ki. \<up>(ki = k)"
    and f = "min_step m (t_set VO) (dist_lookup D)" and F = ?F and fi = "min_level_step Mi VOi Di"
    and xs = vs and arr = Vi, OF min_level_step_rule, OF assms(3) subsetD[OF assms(1)]]
  have R1: "<Vi \<mapsto>\<^sub>a vs * ?F> array_foldl Vi 0 (length vs) (min_level_step Mi VOi Di) None
            <\<lambda>r. Vi \<mapsto>\<^sub>a vs * \<up>(r = foldl (min_step m (t_set VO) (dist_lookup D)) None vs) * ?F>"
    using fold1[of None None]
    by simp
  have step: "<stk_assn (foldr (push_step m (t_set VO) (dist_lookup D) k)
                           (drop (Suc j) (take (length vs) vs)) []) Ri * ?F>
                push_roots_step Mi VOi Di k (vs ! j) Ri
              <\<lambda>r. stk_assn (push_step m (t_set VO) (dist_lookup D) k (vs ! j)
                        (foldr (push_step m (t_set VO) (dist_lookup D) k)
                           (drop (Suc j) (take (length vs) vs)) [])) r * ?F>"
    if "j < length vs" for j Ri k
  proof(rule push_roots_step_rule[OF assms(3)])
    show "vs ! j \<in> univ"
      using that assms(1) by auto
    have "length (foldr (push_step m (t_set VO) (dist_lookup D) k)
                    (drop (Suc j) (take (length vs) vs)) []) \<le> length vs - Suc j"
      using push_step_length[of m "t_set VO" "dist_lookup D" k "drop (Suc j) (take (length vs) vs)"]
      by simp
    thus "length (foldr (push_step m (t_set VO) (dist_lookup D) k)
                    (drop (Suc j) (take (length vs) vs)) []) < cap"
      using that assms(2) by linarith
  qed
  have R2: "<Vi \<mapsto>\<^sub>a vs * stk_assn [] Ri * ?F> array_foldr Vi (length vs) (push_roots_step Mi VOi Di k) Ri
            <\<lambda>r. Vi \<mapsto>\<^sub>a vs * stk_assn (foldr (push_step m (t_set VO) (dist_lookup D) k) vs []) r * ?F>"
    for k Ri
    using array_foldr_rule[where acc_assn = stk_assn and f = "push_step m (t_set VO) (dist_lookup D) k"
                            and acc = "[]" and F = ?F and fi = "push_roots_step Mi VOi Di k"
                            and xs = vs and n = "length vs" and arr = Vi, OF le_refl step]
    by simp
  show ?thesis
    unfolding phase_roots_imp_def
    by (sep_auto heap: R1 stk_empty_rule R2 simp: phase_roots_folds)
qed

subsubsection \<open>The test of the level\<close>

lemma level_zero_imp_rule:
  "vtx w \<in> univ \<Longrightarrow>
   <imp_dist_assn D Di> level_zero_imp Di w <\<lambda>r. imp_dist_assn D Di * \<up>(r \<longleftrightarrow> dist_lookup D w = 0)>"
  by (sep_auto heap: dist_lookup_rule simp: level_zero_imp_def)

subsubsection \<open>The commitment of a path\<close>

lemma block_copy_imp_rule:
  assumes "C \<subseteq> vtx -` univ" "A \<subseteq> vtx -` univ" "x \<in> vtx -` univ"
  shows "<set_assn C Ci * set_assn A Ai> block_copy_imp Ci Ai x
         <\<lambda>_. set_assn C Ci * set_assn (block_copy C x A) Ai>"
  using assms
  by (sep_auto heap: cset.fixed_univ_set_isin_rule cset.fixed_univ_set_insert_rule
               simp: block_copy_imp_def block_copy_def)

lemma block_copy_subset: "\<lbrakk>A \<subseteq> S; x \<in> S\<rbrakk> \<Longrightarrow> block_copy C x A \<subseteq> S"
  by (simp add: block_copy_def)

lemma commit_loop_rule:
  assumes "C \<subseteq> vtx -` univ" "A \<subseteq> vtx -` univ" "set p \<subseteq> vtx -` univ"
  shows "<set_assn C Ci * stk_assn p Si * set_assn A Ai * paths_assn (q # ps) Psi>
           commit_loop Ci Si Ai Psi
         <\<lambda>(Ai', Psi'). set_assn C Ci * stk_assn [] Si *
                        set_assn (A \<union> {w \<in> C. vtx w \<in> vtx ` set p}) Ai' *
                        paths_assn ((q @ p) # ps) Psi'>"
  using assms(2,3)
proof(induction p arbitrary: A q Psi)
  case Nil
  thus ?case
    by (subst commit_loop.simps) (sep_auto heap: stk_is_empty_rule)
next
  case (Cons x p)
  have sub: "block_copy C (Vtx Odd (vtx x)) (block_copy C (Vtx Even (vtx x)) A) \<subseteq> vtx -` univ"
    using Cons.prems by (auto simp: block_copy_def)
  note IH = Cons.IH[OF sub, of "q @ [x]", unfolded block_copies_Cons[symmetric] append_assoc]
  show ?case
    using Cons.prems assms(1)
    by (subst commit_loop.simps)
       (sep_auto heap: stk_is_empty_rule stk_top_rule stk_pop_rule block_copy_imp_rule paths_snoc_rule IH
                 simp: block_copy_subset)
qed

lemma commit_path_imp_rule:
  assumes "C \<subseteq> vtx -` univ" "A \<subseteq> vtx -` univ" "set p \<subseteq> vtx -` univ"
  shows "<set_assn C Ci * stk_assn p Si * set_assn A Ai * paths_assn ps Psi>
           commit_path_imp Ci Si Ai Psi
         <\<lambda>(Ai', Psi'). set_assn C Ci * stk_assn [] Si *
                        set_assn (A \<union> {w \<in> C. vtx w \<in> vtx ` set p}) Ai' * paths_assn (p # ps) Psi'>"
  using assms
  by (sep_auto heap: paths_new_rule commit_loop_rule[where q = "[]"] simp: commit_path_imp_def)

end

subsection \<open>The phase with the imperative builders\<close>

text \<open>With the remaining operations of @{locale Hopcroft_Karp_Phase_Imperative}, i.e.\ those of the
  BFS and of the incremental DFS and the allocations, the imperative builders instantiate
  @{locale Hopcroft_Karp_Phase_Imperative}, with the edges and the vertices given as arrays. The
  imperative phase computes the paths of the functional phase
  (@{text hopcroft_karp_phase_imp_rule} below).\<close>

locale Hopcroft_Karp_Phase_Builders_Imperative =
  Hopcroft_Karp_Builders_Imperative where lookup = lookup and c_lookup = c_lookup
    and mate_get = mate_get and lookup_dist = lookup_dist and mate_get_imp = mate_get_imp
    and g_add_edge_imp = g_add_edge_imp and c_add_edge_imp = c_add_edge_imp
    and src_insert_imp = src_insert_imp and vis_isin_imp = vis_isin_imp
    and dist_lookup_imp = dist_lookup_imp and paths_snoc_imp = paths_snoc_imp
    and set_insert_imp = set_insert_imp and stack_push_imp = stack_push_imp
    and stack_abstract = stack_abstract and dist_lookup = dist_lookup
  for lookup :: "'adjmap \<Rightarrow> 'v::heap \<Rightarrow> 'vset option"
  and c_lookup :: "'cadjmap \<Rightarrow> 'v labelled_vtx \<Rightarrow> 'cvset option"
  and mate_get :: "'mate \<Rightarrow> 'v \<Rightarrow> 'v"
  and lookup_dist :: "'dmap \<Rightarrow> 'v labelled_vtx \<Rightarrow> enat option"
  and mate_get_imp :: "'mi \<Rightarrow> 'v \<Rightarrow> 'v Heap"
  and g_add_edge_imp :: "'imp_G \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'imp_G Heap"
  and c_add_edge_imp :: "'gi \<Rightarrow> 'v labelled_vtx \<Rightarrow> 'v labelled_vtx \<Rightarrow> 'gi Heap"
  and src_insert_imp :: "'v \<Rightarrow> 'imp_src \<Rightarrow> 'imp_src Heap"
  and vis_isin_imp :: "'imp_vis \<Rightarrow> 'v \<Rightarrow> bool Heap"
  and dist_lookup_imp :: "'imp_dist \<Rightarrow> 'v labelled_vtx \<Rightarrow> nat Heap"
  and paths_snoc_imp :: "'ips \<Rightarrow> 'v labelled_vtx \<Rightarrow> 'ips Heap"
  and set_insert_imp :: "'v labelled_vtx \<Rightarrow> 'si \<Rightarrow> unit Heap"
  and stack_push_imp :: "'stki \<Rightarrow> 'v labelled_vtx \<Rightarrow> unit Heap"
  and stack_abstract :: "'s \<Rightarrow> 'v labelled_vtx list"
  and dist_lookup :: "'dist \<Rightarrow> 'v labelled_vtx \<Rightarrow> nat" +
  fixes next_frontier_and_visited :: "'adjmap \<Rightarrow> 'vset \<Rightarrow> 'vset \<Rightarrow> 'vset \<times> 'vset"
    and set_all_dists :: "'dist \<Rightarrow> parity \<Rightarrow> 'vset \<Rightarrow> nat \<Rightarrow> 'dist"
    and dist_invar :: "'dist \<Rightarrow> 'v labelled_vtx set \<Rightarrow> bool"
    and some_dist :: 'dist
    and imp_cf_assn :: "'vset \<Rightarrow> 'imp_cf \<Rightarrow> assn"
    and vis_empty_imp :: "'imp_vis Heap"
    and dist_init_imp :: "'imp_dist Heap"
    and paths_empty_imp :: "'ips Heap"
    and imp_cf_is_empty :: "'imp_cf \<Rightarrow> bool Heap"
    and next_frontier_and_visited_imp :: "'imp_G \<Rightarrow> 'imp_cf \<Rightarrow> 'imp_vis \<Rightarrow> ('imp_cf \<times> 'imp_vis) Heap"
    and set_all_dists_imp :: "'imp_dist \<Rightarrow> parity \<Rightarrow> 'imp_cf \<Rightarrow> nat \<Rightarrow> 'imp_dist Heap"
    and imp_src_to_cf :: "'imp_src \<Rightarrow> 'imp_cf Heap"
    and set_srcs_visited :: "'imp_vis \<Rightarrow> 'imp_src \<Rightarrow> 'imp_vis Heap"
    and sel_unseen_imp :: "'gi \<Rightarrow> 'v labelled_vtx \<Rightarrow> 'si \<Rightarrow> 'v labelled_vtx option Heap"
    and seen_init_imp :: "'si \<Rightarrow> 'si \<Rightarrow> 'si \<Rightarrow> unit Heap"
  assumes next_frontier_and_visited:
    "\<And>H F V F' V'. \<lbrakk>vset_inv F; vset_inv V; G.graph_inv H; G.digraph_abs H \<subseteq> univ \<times> univ;
        t_set F \<subseteq> univ; t_set V \<subseteq> univ; next_frontier_and_visited H F V = (F', V')\<rbrakk>
       \<Longrightarrow> vset_inv F'"
    "\<And>H F V F' V'. \<lbrakk>vset_inv F; vset_inv V; G.graph_inv H; G.digraph_abs H \<subseteq> univ \<times> univ;
        t_set F \<subseteq> univ; t_set V \<subseteq> univ; next_frontier_and_visited H F V = (F', V')\<rbrakk>
       \<Longrightarrow> t_set F' = next_frontier (G.digraph_abs H) (t_set F) (t_set V)"
    "\<And>H F V F' V'. \<lbrakk>vset_inv F; vset_inv V; G.graph_inv H; G.digraph_abs H \<subseteq> univ \<times> univ;
        t_set F \<subseteq> univ; t_set V \<subseteq> univ; next_frontier_and_visited H F V = (F', V')\<rbrakk>
       \<Longrightarrow> vset_inv V'"
    "\<And>H F V F' V'. \<lbrakk>vset_inv F; vset_inv V; G.graph_inv H; G.digraph_abs H \<subseteq> univ \<times> univ;
        t_set F \<subseteq> univ; t_set V \<subseteq> univ; next_frontier_and_visited H F V = (F', V')\<rbrakk>
       \<Longrightarrow> t_set V' = t_set V \<union> t_set F'"
  and set_all_dists:
    "\<And>d S p F n. \<lbrakk>vset_inv F; t_set F \<subseteq> univ; dist_invar d S\<rbrakk>
       \<Longrightarrow> dist_invar (set_all_dists d p F n) (S \<union> Vtx p ` t_set F)"
    "\<And>d S p F n x. \<lbrakk>vset_inv F; t_set F \<subseteq> univ; dist_invar d S; x \<in> t_set F\<rbrakk>
       \<Longrightarrow> dist_lookup (set_all_dists d p F n) (Vtx p x) = n"
    "\<And>d S p F n w. \<lbrakk>vset_inv F; t_set F \<subseteq> univ; dist_invar d S; w \<in> S - Vtx p ` t_set F\<rbrakk>
       \<Longrightarrow> dist_lookup (set_all_dists d p F n) w = dist_lookup d w"
  and some_dist: "dist_invar some_dist {}"
  and vset_empty_unique: "\<And>V. \<lbrakk>vset_inv V; t_set V = {}\<rbrakk> \<Longrightarrow> V = vset_empty"
  and imp_cf_is_empty_rule:
    "\<And>S Si. <imp_cf_assn S Si> imp_cf_is_empty Si <\<lambda>b. imp_cf_assn S Si * \<up>(b \<longleftrightarrow> S = vset_empty)>"
  and next_frontier_and_visited_imp_rule:
    "\<And>H Hi F Fi V Vi. \<lbrakk>vset_inv F; vset_inv V; G.graph_inv H; G.digraph_abs H \<subseteq> univ \<times> univ;
        t_set F \<subseteq> univ; t_set V \<subseteq> univ\<rbrakk> \<Longrightarrow>
     <imp_cf_assn F Fi * imp_vis_assn V Vi * graph_assn H Hi>
       next_frontier_and_visited_imp Hi Fi Vi
     <\<lambda>(Fi', Vi'). imp_cf_assn (fst (next_frontier_and_visited H F V)) Fi' *
                   imp_vis_assn (snd (next_frontier_and_visited H F V)) Vi' * graph_assn H Hi>"
  and set_all_dists_imp_rule:
    "\<And>d di p F Fi n. \<lbrakk>vset_inv F; t_set F \<subseteq> univ\<rbrakk> \<Longrightarrow>
     <imp_dist_assn d di * imp_cf_assn F Fi> set_all_dists_imp di p Fi n
     <\<lambda>r. imp_dist_assn (set_all_dists d p F n) r * imp_cf_assn F Fi>"
  and imp_src_to_cf_rule: "\<And>S Si. <imp_src_assn S Si> imp_src_to_cf Si <\<lambda>r. imp_cf_assn S r>"
  and set_srcs_visited_rule:
    "\<And>S Si Vi. <imp_src_assn S Si * imp_vis_assn vset_empty Vi> set_srcs_visited Vi Si
               <\<lambda>r. imp_vis_assn S r * imp_src_assn S Si>"
  and sel_unseen_rule:
    "\<And>CG Gi v S Si Sf. \<lbrakk>CGraph.graph_inv CG; dVs (CGraph.digraph_abs CG) \<subseteq> vtx -` univ;
        c_vset_inv Sf; c_t_set Sf = S; S \<subseteq> vtx -` univ; v \<in> vtx -` univ\<rbrakk> \<Longrightarrow>
     <cgraph_assn CG Gi * set_assn S Si> sel_unseen_imp Gi v Si
     <\<lambda>r. cgraph_assn CG Gi * set_assn S Si *
          \<up>(r = (if c_diff (CGraph.neighbourhood CG v) Sf \<noteq> c_vset_empty
                 then Some (c_sel (c_diff (CGraph.neighbourhood CG v) Sf)) else None))>"
  and seen_init_rule:
    "\<And>A Ai V Vi S SNi. \<lbrakk>A \<subseteq> vtx -` univ; V \<subseteq> vtx -` univ; S \<subseteq> vtx -` univ\<rbrakk> \<Longrightarrow>
     <set_assn A Ai * set_assn V Vi * set_assn S SNi> seen_init_imp SNi Ai Vi
     <\<lambda>_. set_assn A Ai * set_assn V Vi * set_assn (A \<union> V) SNi>"
  and vis_empty_rule: "<emp> vis_empty_imp <imp_vis_assn vset_empty>"
  and dist_init_rule: "<emp> dist_init_imp <imp_dist_assn some_dist>"
  and paths_empty_rule: "<emp> paths_empty_imp <paths_assn []>"
begin

sublocale phase_imp: Hopcroft_Karp_Phase_Imperative
  where free_sources_imp = free_sources_imp and alt_graphs_imp = alt_graphs_imp
    and copies_graph_imp = copies_graph_imp and phase_roots_imp = phase_roots_imp
    and level_zero_imp = level_zero_imp and commit_path_imp = commit_path_imp
    and edges_assn = "\<lambda>es Ei. Ei \<mapsto>\<^sub>a es" and verts_assn = "\<lambda>vs Vi. Vi \<mapsto>\<^sub>a vs"
proof unfold_locales
qed (rule next_frontier_and_visited set_all_dists some_dist vset_empty_unique imp_cf_is_empty_rule
          next_frontier_and_visited_imp_rule set_all_dists_imp_rule imp_src_to_cf_rule
          set_srcs_visited_rule sel_unseen_rule seen_init_rule free_sources_imp_rule
          alt_graphs_imp_rule vis_empty_rule dist_init_rule copies_graph_imp_rule
          phase_roots_imp_rule[unfolded stk_assn_def] level_zero_imp_rule
          commit_path_imp_rule[unfolded stk_assn_def] set_empty_rule paths_empty_rule;
     assumption)+

text \<open>The imperative phase with the imperative builders computes the paths of the functional
  phase.\<close>

lemmas hopcroft_karp_phase_imp_rule = phase_imp.hopcroft_karp_phase_imp_rule

end

end
