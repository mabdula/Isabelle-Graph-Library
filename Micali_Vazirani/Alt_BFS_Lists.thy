theory Alt_BFS_Lists
  imports Alt_BFS_Dist
begin

section \<open>The Distance BFS on Neighbour Lists\<close>

text \<open>An instance of the alternating BFS and of the distance BFS for vertices that are natural
      numbers: graphs map a vertex to the list of its neighbours, vertex sets are lists, and the
      distance maps are functions. This is the functional model of the imperative implementation
      on arrays. The operations of the original BFS, which are only needed in the proofs, are
      defined directly by their specifications.\<close>

definition "nbs (H::nat \<Rightarrow> nat list option) u = (case H u of None \<Rightarrow> [] | Some vs \<Rightarrow> vs)"

definition "expand_tree_l H (T::nat \<Rightarrow> nat list option) F V =
  (\<lambda>u. if u \<in> set F then Some (nbs T u @ filter (\<lambda>v. v \<notin> set V) (nbs H u)) else T u)"

definition "next_frontier_l H F V = filter (\<lambda>v. v \<notin> set V) (concat (map (nbs H) F))"

definition "upd_dists_l p H (D::nat labelled_vtx \<Rightarrow> enat option) F V =
  (\<lambda>w. if label w = p \<and> vtx w \<notin> set V \<and> (\<exists>u \<in> set F. vtx w \<in> set (nbs H u))
       then Some (the (D (Vtx (other_parity p) (hd (filter (\<lambda>u. vtx w \<in> set (nbs H u)) F)))) + 1)
       else D w)"

definition "init_dists_l srcs = (\<lambda>w. if label w = Even \<and> vtx w \<in> set srcs then Some 0 else None)"

text \<open>The new frontier and visited set: the old frontier is traversed from its last element,
      the new vertices are prepended.\<close>

definition "next_frontier_and_visited_l H F V =
  foldl (\<lambda>(nf, vis) u.
     foldl (\<lambda>(nf, vis) y. if y \<notin> set vis then (y # nf, y # vis) else (nf, vis)) (nf, vis) (nbs H u))
   ([], V) (rev F)"

definition "set_all_dists_l (d::nat labelled_vtx \<Rightarrow> nat) p F n =
  (\<lambda>w. if label w = p \<and> vtx w \<in> set F then n else d w)"

lemma inner_fold_nfv:
  "foldl (\<lambda>(nf, vis) y. if y \<notin> set vis then (y # nf, y # vis) else (nf, vis)) (nf, vis) ys
     = (nf', vis') \<Longrightarrow>
   set nf' = set nf \<union> (set ys - set vis) \<and> set vis' = set vis \<union> set ys"
proof(induction ys arbitrary: nf vis)
  case (Cons y ys)
  show ?case
  proof(cases "y \<in> set vis")
    case True
    thus ?thesis
      using Cons.IH[of nf vis] Cons.prems by auto
  next
    case False
    thus ?thesis
      using Cons.IH[of "y # nf" "y # vis"] Cons.prems by auto
  qed
qed simp

lemma outer_fold_nfv:
  "foldl (\<lambda>(nf, vis) u.
     foldl (\<lambda>(nf, vis) y. if y \<notin> set vis then (y # nf, y # vis) else (nf, vis)) (nf, vis) (nbs H u))
     (nf, vis) us = (nf', vis') \<Longrightarrow>
   set nf' = set nf \<union> (\<Union>u \<in> set us. set (nbs H u) - set vis) \<and>
   set vis' = set vis \<union> (\<Union>u \<in> set us. set (nbs H u))"
proof(induction us arbitrary: nf vis)
  case (Cons u us)
  obtain nf1 vis1 where eq:
    "foldl (\<lambda>(nf, vis) y. if y \<notin> set vis then (y # nf, y # vis) else (nf, vis)) (nf, vis) (nbs H u)
       = (nf1, vis1)"
    by (rule prod.exhaust)
  note one = inner_fold_nfv[OF eq]
  have "foldl (\<lambda>(nf, vis) u.
     foldl (\<lambda>(nf, vis) y. if y \<notin> set vis then (y # nf, y # vis) else (nf, vis)) (nf, vis) (nbs H u))
     (nf1, vis1) us = (nf', vis')"
    using Cons.prems unfolding foldl_Cons prod.case eq .
  note two = Cons.IH[OF this]
  show ?case
    using one two by auto
qed simp

lemma next_frontier_and_visited_l_correct:
  assumes "next_frontier_and_visited_l H F V = (F', V')"
  shows "set F' = next_frontier {(u, v). v \<in> set (nbs H u)} (set F) (set V)"
        "set V' = set V \<union> set F'"
  using outer_fold_nfv[OF assms[unfolded next_frontier_and_visited_l_def]]
  by (auto simp: next_frontier_def Pair_Graph.neighbourhood_def)

lemma lists_read_only:
  "Pair_Graph_Specs_Read_Only Cons (\<lambda>xs x. x \<in> set xs) set hd [] (\<lambda>x xs. filter (\<lambda>y. y \<noteq> x) xs)
     (\<lambda>_. True)"
  by unfold_locales auto

lemma digraph_abs_lists:
  "Pair_Graph_Specs_Read_Only.digraph_abs (\<lambda>xs x. x \<in> set xs) [] (\<lambda>M. M) H = {(u, v). v \<in> set (nbs H u)}"
  by (auto simp: Pair_Graph_Specs_Read_Only.digraph_abs_def[OF lists_read_only]
                 Pair_Graph_Specs_Read_Only.neighbourhood_def[OF lists_read_only] nbs_def
           split: option.splits)

lemma graph_inv_lists:
  "Pair_Graph_Specs_Read_Only.graph_inv (\<lambda>_::nat list. True) (\<lambda>M. M) (\<lambda>_. True) (H::nat \<Rightarrow> nat list option)"
  by (rule Pair_Graph_Specs_Read_Only.graph_invI[OF lists_read_only]) simp_all

lemma upd_dists_l_new:
  assumes "v \<in> next_frontier {(u, v). v \<in> set (nbs H u)} (set F) (set V)"
  shows "\<exists>u \<in> set F. v \<in> set (nbs H u) \<and> v \<notin> set V \<and>
           upd_dists_l p H D F V (Vtx p v) = Some (the (D (Vtx (other_parity p) u)) + 1)"
proof-
  have ne: "filter (\<lambda>u. v \<in> set (nbs H u)) F \<noteq> []" and vV: "v \<notin> set V"
    using assms by (auto simp: next_frontier_def Pair_Graph.neighbourhood_def filter_empty_conv)
  define u where "u = hd (filter (\<lambda>u. v \<in> set (nbs H u)) F)"
  have "u \<in> set F" "v \<in> set (nbs H u)"
    using hd_in_set[OF ne] by (auto simp: u_def)
  thus ?thesis
    using vV by (auto simp: upd_dists_l_def u_def[symmetric])
qed

lemma upd_dists_l_old:
  "w \<notin> Vtx p ` next_frontier {(u, v). v \<in> set (nbs H u)} (set F) (set V) \<Longrightarrow>
   upd_dists_l p H D F V w = D w"
  by (cases w) (auto simp: upd_dists_l_def next_frontier_def Pair_Graph.neighbourhood_def)

lemma set_all_dists_l_old: "w \<notin> Vtx p ` set F \<Longrightarrow> set_all_dists_l d p F n w = d w"
  by (cases w) (auto simp: set_all_dists_l_def)

lemma set_all_dists_l_new: "x \<in> set F \<Longrightarrow> set_all_dists_l d p F n (Vtx p x) = n"
  by (simp add: set_all_dists_l_def)

locale Alt_BFS_lists =
  fixes matchingG unmatchingG :: "nat \<Rightarrow> nat list option" and srcsL :: "nat list"
begin

sublocale alt: Alt_BFS_distance
  where empty = "\<lambda>_. None" and delete = "\<lambda>x M. M(x := None)" and lookup_neighb = "\<lambda>M x. M x"
    and insert = Cons and isin = "\<lambda>xs x. x \<in> set xs" and t_set = set and sel = hd
    and update = "\<lambda>x z M. M(x \<mapsto> z)" and adjmap_inv = "\<lambda>_. True"
    and vset_empty = Nil and vset_delete = "\<lambda>x xs. filter (\<lambda>y. y \<noteq> x) xs" and vset_inv = "\<lambda>_. True"
    and union = append and inter = "\<lambda>xs ys. filter (\<lambda>y. y \<in> set ys) xs"
    and diff = "\<lambda>xs ys. filter (\<lambda>y. y \<notin> set ys) xs"
    and lookup_dist = "\<lambda>m k. m k" and empty_dist = Map.empty and update_dist = "\<lambda>k v m. m(k \<mapsto> v)"
    and delete_dist = "\<lambda>k m. m(k := None)" and invar_dist = "\<lambda>_. True"
    and srcs = srcsL and matching = matchingG and unmatching = unmatchingG
    and expand_tree = expand_tree_l and next_frontier_impl = next_frontier_l
    and upd_dists = upd_dists_l and init_dists = "init_dists_l srcsL"
    and next_frontier_and_visited = next_frontier_and_visited_l and set_all_dists = set_all_dists_l
    and dist_lookup = "\<lambda>d w. d w" and dist_invar = "\<lambda>_ _. True" and some_dist = "\<lambda>_. 0"
  apply unfold_locales
  using next_frontier_and_visited_l_correct upd_dists_l_new upd_dists_l_old
        set_all_dists_l_old set_all_dists_l_new (*takes long*)
  by (auto simp: init_dists_l_def digraph_abs_lists graph_inv_lists
                 expand_tree_l_def new_edges_def next_frontier_def next_frontier_l_def
                 Pair_Graph.neighbourhood_def nbs_def
           split: option.splits if_splits)
end

end