theory Path_Search_Shortcut
  imports
    Neighbourhood_Best_Scan
    Hungarian_Method_Top_Loop
    Directed_Set_Graphs.More_Arith
begin

section \<open>A Rematching Shortcut before the Path Search\<close>

text \<open>Before a full path search, augmenting row reduction in the style of Jonker and Volgenant is
      tried. For a free left vertex @{term l}, a neighbour @{term r1} of smallest reduced cost
      @{term u1} and the smallest reduced cost @{term u2} of the other neighbours are computed. If
      @{term r1} is free, then raising the potential of @{term l} to @{term u1} makes
      @{term "[l, r1]"} a tight augmenting path. Otherwise, @{term l} takes @{term r1} from its
      partner @{term lq}: the potential of @{term l} becomes @{term u2} and that of @{term r1} drops
      by @{term "u2 - u1"}. The potential stays feasible, the matching keeps its size, and the chain
      continues at the now free vertex @{term lq}, at most @{term cap} times.

      The free left vertices are tried in the order @{term left_order}. The search context
      consists of the left vertices still to be tried and the cursors; both are kept from one
      call to the next. If no chain succeeds, the full path search @{term fallback} is run on the
      changed matching and potential, with the cursors, and the left vertices start over.
      The combination @{term path_search_sc} tries the shortcut only if its first argument holds.

      The matching is seen only through @{term buddy_get} and @{term rematch}, the potential only
      through @{term potential_get} and @{term potential_upd}.\<close>

locale path_search_shortcut_spec =
  hungarian_loop_spec potential_abstract init_potential potential_invar empty_matching
    matching_invar augment matching_abstract edge_costs card_L card_R
    "\<lambda>ctx M \<pi>. case fallback (snd ctx) M \<pi> of (r, M', \<pi>', C') \<Rightarrow> (r, M', \<pi>', (fst ctx, C'))"
    "(left_order, rnb_init)" G +
  nb_best_scan_spec rnb_current rnb_has rnb_move rnb_reset
  for potential_abstract :: "'potential \<Rightarrow> 'v \<Rightarrow> real"
    and init_potential potential_invar empty_matching matching_invar augment
    and matching_abstract :: "'matching \<Rightarrow> 'v set set"
    and edge_costs card_L card_R
    and fallback :: "'g \<Rightarrow> 'matching \<Rightarrow> 'potential \<Rightarrow>
                     'v path_search_result \<times> 'matching \<times> 'potential \<times> 'g"
    and left_order :: "'v list" and rnb_init :: 'g and G
    and rnb_current :: "'g \<Rightarrow> 'v \<Rightarrow> 'v" and rnb_has rnb_move rnb_reset +
  fixes nil :: 'v
    and buddy_get :: "'matching \<Rightarrow> 'v \<Rightarrow> 'v"
    and rematch :: "'matching \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'matching"
    and potential_get :: "'potential \<Rightarrow> 'v \<Rightarrow> real"
    and potential_upd :: "'potential \<Rightarrow> 'v \<Rightarrow> real \<Rightarrow> 'potential"
    and edge_costs_code :: "'v \<Rightarrow> 'v \<Rightarrow> real"
    and cap :: nat
begin
definition "free M v = (buddy_get M v = nil)"

definition "red \<pi> l r = edge_costs_code l r - potential_get \<pi> r"

text \<open>The potential change of a successful scan of @{term l} whose best neighbour @{term r1} is
      better by @{term d} than the runner-up: @{term l} gets @{term v} and @{term r1} is lowered by
      @{term d}.\<close>

definition "pot_shift \<pi> l v r1 d = potential_upd (potential_upd \<pi> l v) r1 (potential_get \<pi> r1 - d)"

text \<open>A chain from the free left vertex @{term l}, at most @{term k} rematches long. The cursors are
      threaded through the scans. If the best neighbour is free and there is a runner-up, it is
      lowered as in Jonker-Volgenant.\<close>

fun chain :: "nat \<Rightarrow> 'matching \<Rightarrow> 'potential \<Rightarrow> 'g \<Rightarrow> 'v \<Rightarrow>
              'g \<times> 'matching \<times> 'potential \<times> 'v list option" where
  "chain k M \<pi> C l =
     (case best_two (red \<pi>) (free M) l C of
        (C', None, _) \<Rightarrow> (C', M, \<pi>, None)
      | (C', Some (u1, r1), s) \<Rightarrow>
          if free M r1 then
            (case s of
               None \<Rightarrow> (C', M, potential_upd \<pi> l u1, Some [l, r1])
             | Some (u2, _) \<Rightarrow> (C', M, pot_shift \<pi> l u2 r1 (u2 - u1), Some [l, r1]))
          else (case s of
                  None \<Rightarrow> (C', M, \<pi>, None)
                | Some (u2, _) \<Rightarrow>
                    (case k of
                       0 \<Rightarrow> (C', M, \<pi>, None)
                     | Suc k' \<Rightarrow>
                         chain k' (rematch M l r1) (pot_shift \<pi> l u2 r1 (u2 - u1))
                           C' (buddy_get M r1))))"

declare chain.simps[simp del]

definition "sc_row s l =
  (case s of (C, M, \<pi>) \<Rightarrow>
     if free M l then (case chain cap M \<pi> C l of (C', M', \<pi>', r) \<Rightarrow> ((C', M', \<pi>'), r))
     else (s, None))"

text \<open>The loop over the left vertices still to be tried. It stops at the first successful chain
      and returns the vertices after its start.\<close>

fun sc_loop where
  "sc_loop s [] = (s, None, [])"
| "sc_loop s (l # xs) =
     (case sc_row s l of (s', None) \<Rightarrow> sc_loop s' xs | (s', Some p) \<Rightarrow> (s', Some (l, p), xs))"

definition "sc_try b s xs = (if b then sc_loop s xs else (s, None, xs))"

definition "path_search_sc b ctx M \<pi> =
  (case ctx of (xs, C) \<Rightarrow>
    (case sc_try b (C, M, \<pi>) xs of
       ((C', M', \<pi>'), Some (l, p), xs') \<Rightarrow> (Next_Iteration p, M', \<pi>', (xs', C'))
     | ((C', M', \<pi>'), None, _) \<Rightarrow>
         (case fallback C' M' \<pi>' of (r, M'', \<pi>'', C'') \<Rightarrow> (r, M'', \<pi>'', (left_order, C'')))))"

lemmas [code] = free_def red_def pot_shift_def chain.simps sc_row_def sc_loop.simps sc_try_def
  path_search_sc_def

end

text \<open>Replacing an element by a new one keeps the cardinality; for a rematch.\<close>

lemma card_swap:
  assumes "y \<in> A" "x \<notin> A"
  shows "card (A - {y} \<union> {x}) = card A"
proof(cases "finite A")
  case True
  have "card (A - {y} \<union> {x}) = Suc (card (A - {y}))" using True assms(2) by simp
  from this card_Suc_Diff1[OF True assms(1)] show ?thesis by (rule trans)
qed simp
locale path_search_shortcut =
  path_search_shortcut_spec +
  nb_best_scan rnb_current rnb_has rnb_move rnb_reset rnb_invar rnb_abstract rnb_iterated
    rnb_remaining K +
  potential_map: fixed_univ_map K potential_invar potential_upd potential_get
  for rnb_invar rnb_abstract rnb_iterated rnb_remaining K +
  fixes L R
  assumes G: "bipartite G L R" "set left_order = L" "L \<subseteq> K" "Vs G \<subseteq> K"
    and rnb_init: "rnb_invar rnb_init"
      "\<And>l. l \<in> L \<Longrightarrow> rnb_abstract rnb_init l = {r. {l, r} \<in> G}"
      "\<And>l. l \<in> L \<Longrightarrow> finite (rnb_abstract rnb_init l)"
    and edge_costs_code: "\<And>l r. \<lbrakk>{l, r} \<in> G; l \<in> L\<rbrakk> \<Longrightarrow> edge_costs_code l r = edge_costs {l, r}"
    and buddy: "\<And>M v. matching_invar M \<Longrightarrow>
                  buddy_get M v = nil \<longleftrightarrow> v \<notin> Vs (matching_abstract M)"
      "\<And>M v. \<lbrakk>matching_invar M; buddy_get M v \<noteq> nil\<rbrakk> \<Longrightarrow>
                  {buddy_get M v, v} \<in> matching_abstract M"
    and matching_graph: "\<And>M. matching_invar M \<Longrightarrow> graph_matching G (matching_abstract M)"
    and rematch: "\<And>M lq l r. \<lbrakk>matching_invar M; {lq, r} \<in> matching_abstract M;
                     l \<notin> Vs (matching_abstract M); {l, r} \<in> G\<rbrakk> \<Longrightarrow>
                     matching_invar (rematch M l r)"
      "\<And>M lq l r. \<lbrakk>matching_invar M; {lq, r} \<in> matching_abstract M;
                     l \<notin> Vs (matching_abstract M); {l, r} \<in> G\<rbrakk> \<Longrightarrow>
                     matching_abstract (rematch M l r) =
                       matching_abstract M - {{lq, r}} \<union> {{l, r}}"
    and potential: "\<And>\<pi>. potential_abstract \<pi> = potential_get \<pi>"
    and fallback: "\<And>C M \<pi> r M' \<pi>' C'. \<lbrakk>path_search_precond M \<pi>; rnb_invar C;
                     rnb_abstract C = rnb_abstract rnb_init; fallback C M \<pi> = (r, M', \<pi>', C')\<rbrakk> \<Longrightarrow>
                     good_search L R M (r, M', \<pi>') \<and> rnb_invar C' \<and>
                     rnb_abstract C' = rnb_abstract rnb_init"
begin

text \<open>The context of the search: left vertices and valid cursors.\<close>

definition "sc_ctx_invar ctx =
  (case ctx of (xs, C) \<Rightarrow>
     set xs \<subseteq> L \<and> rnb_invar C \<and> rnb_abstract C = rnb_abstract rnb_init)"

lemma nb_not_L: "\<lbrakk>l \<in> L; {l, r} \<in> G\<rbrakk> \<Longrightarrow> r \<notin> L"
  using bipartite_edgeD(1)[OF _ G(1)] by blast

lemma cost: "\<lbrakk>l \<in> L; {l, r} \<in> G\<rbrakk> \<Longrightarrow> red \<pi> l r = edge_costs {l, r} - potential_abstract \<pi> r"
  using edge_costs_code by (simp add: red_def potential)


text \<open>Matched edges that avoid the changed vertices stay tight.\<close>

lemma tight_keep:
  assumes "S \<subseteq> tight_subgraph G edge_costs p" "\<And>e x. \<lbrakk>e \<in> S; x \<in> e\<rbrakk> \<Longrightarrow> p' x = p x"
  shows "S \<subseteq> tight_subgraph G edge_costs p'"
proof
  fix e assume e: "e \<in> S"
  then obtain u v where uv: "e = {u, v}" "{u, v} \<in> G" "edge_costs {u, v} = p u + p v"
    using assms(1) by (auto elim!: in_tight_subgraphE)
  have "p' u = p u" "p' v = p v" using assms(2)[OF e] uv(1) by auto
  thus "e \<in> tight_subgraph G edge_costs p'" using uv by (intro in_tight_subgraphI) auto
qed

text \<open>A change of the potential at a left vertex @{term l} that is feasible on the edges of
      @{term l}, and that does not increase the potential elsewhere, keeps it feasible.\<close>

lemma feasible_after_row:
  assumes "feasible_min_perfect_dual G edge_costs p"
      and "\<And>y. {l, y} \<in> G \<Longrightarrow> p' l + p' y \<le> edge_costs {l, y}"
      and "\<And>x. x \<noteq> l \<Longrightarrow> p' x \<le> p x"
  shows "feasible_min_perfect_dual G edge_costs p'"
proof(rule feasible_min_perfect_dualI)
  fix e u v assume e: "e \<in> G" "e = {u, v}"
  show "p' u + p' v \<le> edge_costs e"
  proof(cases "u = l")
    case True
    thus ?thesis using assms(2)[of v] e by simp
  next
    case False
    show ?thesis
    proof(cases "v = l")
      case True
      have e': "e = {l, u}" using e(2) True by blast
      have "p' l + p' u \<le> edge_costs e" using assms(2)[of u] e(1) e' by simp
      thus ?thesis using True by (simp add: add.commute)
    next
      case False
      thus ?thesis
        using feasible_min_perfect_dualD[OF assms(1) e] assms(3)[of u] assms(3)[of v] \<open>u \<noteq> l\<close>
        by simp
    qed
  qed
qed

lemma precond_of_good:
  "\<lbrakk>path_search_precond M \<pi>; good_search_result M \<pi>' p\<rbrakk> \<Longrightarrow> path_search_precond M \<pi>'"
  by (simp add: path_search_precond_def good_search_result_def)

lemma pot_shift:
  assumes "potential_invar \<pi>" "l \<in> K" "r1 \<in> K"
  shows "potential_invar (pot_shift \<pi> l v r1 d)"
        "potential_abstract (pot_shift \<pi> l v r1 d) =
           (potential_abstract \<pi>)(l := v, r1 := potential_abstract \<pi> r1 - d)"
proof-
  have inv1: "potential_invar (potential_upd \<pi> l v)"
    by (rule potential_map.fixed_univ_map_upd_invar[OF assms(1,2)])
  show "potential_invar (pot_shift \<pi> l v r1 d)"
    unfolding pot_shift_def by (rule potential_map.fixed_univ_map_upd_invar[OF inv1 assms(3)])
  show "potential_abstract (pot_shift \<pi> l v r1 d) =
          (potential_abstract \<pi>)(l := v, r1 := potential_abstract \<pi> r1 - d)"
    using potential_map.fixed_univ_map_upd[OF inv1 assms(3)]
          potential_map.fixed_univ_map_upd[OF assms(1,2)]
    by (simp add: pot_shift_def potential)
qed

text \<open>The end of a chain: the best neighbour @{term r1} is free. The potential of @{term l} becomes
      some @{term v} below the reduced costs of the other arcs of @{term l}, and @{term r1} is
      lowered by @{term "v - u1"}, which keeps @{term "{l, r1}"} tight.\<close>

lemma success_step:
  assumes pre: "path_search_precond M \<pi>" and l: "l \<in> L" "l \<notin> Vs (matching_abstract M)"
      and r1: "{l, r1} \<in> G" "r1 \<notin> Vs (matching_abstract M)"
      and u1: "u1 = red \<pi> l r1"
      and v: "u1 \<le> v" "\<And>r. \<lbrakk>{l, r} \<in> G; r \<noteq> r1\<rbrakk> \<Longrightarrow> v \<le> red \<pi> l r"
      and \<pi>': "potential_invar \<pi>'"
        "potential_abstract \<pi>' =
           (potential_abstract \<pi>)(l := v, r1 := potential_abstract \<pi> r1 - (v - u1))"
  shows "good_search_result M \<pi>' [l, r1]"
proof-
  note P = path_search_precondD[OF pre]
  have other: "\<And>r. {l, r} \<in> G \<Longrightarrow> r \<noteq> l" using nb_not_L[OF l(1)] l(1) by blast
  have lr1: "l \<noteq> r1" using other[OF r1(1)] by simp
  let ?p = "potential_abstract \<pi>" and ?p' = "potential_abstract \<pi>'"
  note pa = \<pi>'(2)
  show ?thesis
  proof(rule good_search_resultI)
    show "potential_invar \<pi>'" by (rule \<pi>'(1))
    show "matching_abstract M \<subseteq> tight_subgraph G edge_costs ?p'"
      by (rule tight_keep[OF P(4)]) (use l(2) r1(2) in \<open>auto simp: pa Vs_def\<close>)
    show "feasible_min_perfect_dual G edge_costs ?p'"
    proof(rule feasible_after_row[OF P(5)])
      fix y assume y: "{l, y} \<in> G"
      show "?p' l + ?p' y \<le> edge_costs {l, y}"
      proof(cases "y = r1")
        case True
        thus ?thesis using cost[OF l(1) y] u1 lr1 by (simp add: pa algebra_simps)
      next
        case False
        thus ?thesis using cost[OF l(1) y] v(2)[OF y False] other[OF y] lr1 by (simp add: pa)
      qed
    next
      fix x assume "x \<noteq> l"
      thus "?p' x \<le> ?p x" using v(1) by (simp add: pa)
    qed
    have "?p' l + ?p' r1 = edge_costs {l, r1}"
      using cost[OF l(1) r1(1)] u1 lr1 by (simp add: pa algebra_simps)
    hence "{l, r1} \<in> tight_subgraph G edge_costs ?p'"
      by (intro in_tight_subgraphI[OF refl r1(1)]) simp
    thus "set (edges_of_path [l, r1]) \<subseteq> tight_subgraph G edge_costs ?p'" by simp
    have nM: "{l, r1} \<notin> matching_abstract M" using l(2) by (auto simp: Vs_def)
    have jV: "r1 \<in> Vs G" using r1(1) by (auto simp: Vs_def)
    have pth: "path G [l, r1]" using r1(1) jV by (auto intro: path.intros)
    have aug: "matching_augmenting_path (matching_abstract M) [l, r1]"
      using nM l(2) r1(2) by (auto intro!: matching_augmenting_pathI alt_list.intros)
    show "graph_augmenting_path G (matching_abstract M) [l, r1]"
      using pth aug other[OF r1(1)] by auto
  qed
qed

text \<open>A link of a chain: @{term l} takes the matched best neighbour @{term r1} from @{term lq}
      ("WHY IT IS ALLOWED" in the pseudocode).\<close>

lemma rematch_step:
  assumes pre: "path_search_precond M \<pi>" and l: "l \<in> L" "l \<notin> Vs (matching_abstract M)"
      and r1: "{l, r1} \<in> G" "{lq, r1} \<in> matching_abstract M"
      and r2: "{l, r2} \<in> G" "r2 \<noteq> r1"
      and u1: "u1 = red \<pi> l r1" "\<And>r. {l, r} \<in> G \<Longrightarrow> u1 \<le> red \<pi> l r"
      and u2: "u2 = red \<pi> l r2" "\<And>r. \<lbrakk>{l, r} \<in> G; r \<noteq> r1\<rbrakk> \<Longrightarrow> u2 \<le> red \<pi> l r"
      and \<pi>': "\<pi>' = pot_shift \<pi> l u2 r1 (u2 - u1)"
  shows "path_search_precond (rematch M l r1) \<pi>'"
        "card (matching_abstract (rematch M l r1)) = card (matching_abstract M)"
        "lq \<in> L" "lq \<notin> Vs (matching_abstract (rematch M l r1))"
proof-
  note P = path_search_precondD[OF pre]
  have lK: "l \<in> K" using l(1) G(3) by auto
  have r1K: "r1 \<in> K" using edges_are_Vs_2[OF r1(1)] G(4) by auto
  have r1L: "r1 \<notin> L" by (rule nb_not_L[OF l(1) r1(1)])
  have lr1: "l \<noteq> r1" using l(1) r1L by auto
  have lqG: "{lq, r1} \<in> G" using r1(2) P(3) by auto
  have r1R: "r1 \<in> R" using bipartite_edgeD(1)[OF r1(1) G(1) l(1)] by simp
  show lqL: "lq \<in> L" using bipartite_edgeD(4)[OF lqG G(1) r1R] by simp
  have lql: "lq \<noteq> l" using l(2) r1(2) by (auto simp: Vs_def)
  have lqr1: "lq \<noteq> r1" using lqL r1L by auto
  have mt: "matching (matching_abstract M)" using P(3) by simp
  have others: "l \<notin> e \<and> r1 \<notin> e \<and> lq \<notin> e"
    if e: "e \<in> matching_abstract M" "e \<noteq> {lq, r1}" for e
  proof-
    have "l \<notin> e" using l(2) e(1) by (auto simp: Vs_def)
    moreover have "r1 \<notin> e" using matching_unique_match[OF mt _ _ e(1) r1(2), of r1] e(2) by blast
    moreover have "lq \<notin> e" using matching_unique_match[OF mt _ _ e(1) r1(2), of lq] e(2) by blast
    ultimately show ?thesis by blast
  qed
  have RM: "matching_invar (rematch M l r1)"
           "matching_abstract (rematch M l r1) = matching_abstract M - {{lq, r1}} \<union> {{l, r1}}"
    using rematch[OF P(1) r1(2) l(2) r1(1)] by auto
  let ?p = "potential_abstract \<pi>" and ?p' = "potential_abstract \<pi>'"
  have inv': "potential_invar \<pi>'" and pa: "?p' = ?p(l := u2, r1 := ?p r1 - (u2 - u1))"
    unfolding \<pi>' by (rule pot_shift[OF P(2) lK r1K])+
  have u12: "u1 \<le> u2" using u1(2)[OF r2(1)] u2(1) by simp
  have keep: "?p' x = ?p x" if "e \<in> matching_abstract M - {{lq, r1}}" "x \<in> e" for e x
    using others[of e] that by (auto simp: pa)
  have tight_old: "matching_abstract M - {{lq, r1}} \<subseteq> tight_subgraph G edge_costs ?p'"
    by (rule tight_keep[OF subset_trans[OF Diff_subset P(4)] keep])
  have "?p' l + ?p' r1 = edge_costs {l, r1}"
    using cost[OF l(1) r1(1)] u1(1) lr1 by (simp add: pa algebra_simps)
  hence tight_new: "{l, r1} \<in> tight_subgraph G edge_costs ?p'"
    by (intro in_tight_subgraphI[OF refl r1(1)]) simp
  have tight: "matching_abstract (rematch M l r1) \<subseteq> tight_subgraph G edge_costs ?p'"
    using tight_old tight_new by (simp add: RM(2))
  have feas: "feasible_min_perfect_dual G edge_costs ?p'"
  proof(rule feasible_after_row[OF P(5)])
    fix y assume y: "{l, y} \<in> G"
    have yl: "y \<noteq> l" using nb_not_L[OF l(1) y] l(1) by auto
    show "?p' l + ?p' y \<le> edge_costs {l, y}"
    proof(cases "y = r1")
      case True
      thus ?thesis using cost[OF l(1) y] u1(1) lr1 by (simp add: pa algebra_simps)
    next
      case False
      thus ?thesis using cost[OF l(1) y] u2(2)[OF y False] lr1 yl by (simp add: pa)
    qed
  next
    fix x assume "x \<noteq> l"
    thus "?p' x \<le> ?p x" using u12 by (simp add: pa)
  qed
  show "path_search_precond (rematch M l r1) \<pi>'"
    using RM(1) inv' tight matching_graph[OF RM(1)] feas by (intro path_search_precondI) auto
  have nin: "{l, r1} \<notin> matching_abstract M" using l(2) by (auto simp: Vs_def)
  show "card (matching_abstract (rematch M l r1)) = card (matching_abstract M)"
    using card_swap[OF r1(2)] nin by (simp add: RM(2))
  show "lq \<notin> Vs (matching_abstract (rematch M l r1))"
  proof
    assume "lq \<in> Vs (matching_abstract (rematch M l r1))"
    then obtain e where e: "e \<in> matching_abstract (rematch M l r1)" "lq \<in> e" by (auto simp: Vs_def)
    thus False using others[of e] lql lqr1 by (auto simp: RM(2))
  qed
qed

text \<open>A chain keeps the precondition of the path search, the size of the matching and the
      collection of the neighbourhoods. A path that it finds is a tight augmenting path.\<close>

lemma chain_valid:
  assumes "path_search_precond M \<pi>" "rnb_invar C" "rnb_abstract C = rnb_abstract rnb_init"
          "l \<in> L" "l \<notin> Vs (matching_abstract M)" "chain k M \<pi> C l = (C', M', \<pi>', res)"
  shows "path_search_precond M' \<pi>' \<and> card (matching_abstract M') = card (matching_abstract M) \<and>
         rnb_invar C' \<and> rnb_abstract C' = rnb_abstract rnb_init \<and>
         (\<forall>p. res = Some p \<longrightarrow> good_search_result M' \<pi>' p)"
  using assms
proof(induction k arbitrary: M \<pi> C l C' M' \<pi>' res rule: less_induct)
  case (less k)
  note pre = less.prems(1) and l = less.prems(4,5)
  note P = path_search_precondD[OF pre]
  have lK: "l \<in> K" using l(1) G(3) by auto
  have N: "rnb_abstract C l = {r. {l, r} \<in> G}" using rnb_init(2)[OF l(1)] less.prems(3) by simp
  have fin: "finite (rnb_abstract C l)" using rnb_init(3)[OF l(1)] less.prems(3) by simp
  obtain C1 b s where bt: "best_two (red \<pi>) (free M) l C = (C1, b, s)" by (metis prod_cases3)
  note B = best_two_props[OF less.prems(2) lK fin bt]
  have C1: "rnb_invar C1" "rnb_abstract C1 = rnb_abstract rnb_init"
    using B(1,2) less.prems(3) by simp_all
  note ch = less.prems(6)[unfolded chain.simps[of k M \<pi> C l] bt]
  show ?case
  proof(cases b)
    case None
    thus ?thesis using ch C1 pre by auto
  next
    case (Some q)
    note bS = Some
    obtain u1 r1 where q: "q = (u1, r1)" by (cases q) auto
    have b1: "r1 \<in> rnb_abstract C l" "u1 = red \<pi> l r1" "\<forall>r\<in>rnb_abstract C l. u1 \<le> red \<pi> l r"
      using B(4)[OF bS[unfolded q]] by auto
    have r1G: "{l, r1} \<in> G" using b1(1) N by simp
    have u1min: "\<And>r. {l, r} \<in> G \<Longrightarrow> u1 \<le> red \<pi> l r" using b1(3) N by simp
    have r1f: "r1 \<notin> Vs (matching_abstract M)" if "free M r1"
      using that buddy(1)[OF P(1)] by (simp add: free_def)
    have r1K: "r1 \<in> K" using edges_are_Vs_2[OF r1G] G(4) by auto
    have lr1: "l \<noteq> r1" using nb_not_L[OF l(1) r1G] l(1) by auto
    show ?thesis
    proof(cases s)
      case None
      note sN = None
      show ?thesis
      proof(cases "free M r1")
        case True
        have eq: "C' = C1" "M' = M" "\<pi>' = potential_upd \<pi> l u1" "res = Some [l, r1]"
          using ch True by (simp_all add: bS q sN)
        have pa: "potential_abstract (potential_upd \<pi> l u1) =
                    (potential_abstract \<pi>)(l := u1, r1 := potential_abstract \<pi> r1 - (u1 - u1))"
          using potential_map.fixed_univ_map_upd[OF P(2) lK] lr1 by (auto simp: potential)
        have gs: "good_search_result M (potential_upd \<pi> l u1) [l, r1]"
          by (rule success_step[OF pre l r1G r1f[OF True] b1(2) order_refl _
                     potential_map.fixed_univ_map_upd_invar[OF P(2) lK] pa])
             (rule u1min)
        show ?thesis using eq C1 gs precond_of_good[OF pre gs] by simp
      next
        case False
        thus ?thesis using ch C1 pre by (auto simp: bS q sN)
      qed
    next
      case (Some q2)
      note sS = Some
      obtain u2 r2 where q2: "q2 = (u2, r2)" by (cases q2) auto
      have b2: "r2 \<in> rnb_abstract C l - {r1}" "u2 = red \<pi> l r2"
               "\<forall>r\<in>rnb_abstract C l - {r1}. u2 \<le> red \<pi> l r"
        using B(6)[OF bS[unfolded q] sS[unfolded q2]] by auto
      have r2G: "{l, r2} \<in> G" "r2 \<noteq> r1" using b2(1) N by auto
      have u2min: "\<And>r. \<lbrakk>{l, r} \<in> G; r \<noteq> r1\<rbrakk> \<Longrightarrow> u2 \<le> red \<pi> l r" using b2(3) N by simp
      have u12: "u1 \<le> u2" using u1min[OF r2G(1)] b2(2) by simp
      define \<pi>2 where "\<pi>2 = pot_shift \<pi> l u2 r1 (u2 - u1)"
      show ?thesis
      proof(cases "free M r1")
        case True
        have eq: "C' = C1" "M' = M" "\<pi>' = \<pi>2" "res = Some [l, r1]"
          using ch True by (simp_all add: bS q sS q2 \<pi>2_def)
        have gs: "good_search_result M \<pi>2 [l, r1]"
          unfolding \<pi>2_def
          by (rule success_step[OF pre l r1G r1f[OF True] b1(2) u12 u2min
                     pot_shift[OF P(2) lK r1K]])
        show ?thesis using eq C1 gs precond_of_good[OF pre gs] by simp
      next
        case False
        have lqe: "{buddy_get M r1, r1} \<in> matching_abstract M"
          using buddy(2)[OF P(1)] False by (simp add: free_def)
        show ?thesis
        proof(cases k)
          case 0
          thus ?thesis using ch False C1 pre by (auto simp: bS q sS q2)
        next
          case (Suc k')
          note st = rematch_step[OF pre l r1G lqe r2G b1(2) u1min b2(2) u2min \<pi>2_def]
          have rec: "chain k' (rematch M l r1) \<pi>2 C1 (buddy_get M r1) = (C', M', \<pi>', res)"
            using ch False by (simp add: bS q sS q2 Suc \<pi>2_def)
          have IH: "path_search_precond M' \<pi>' \<and>
                    card (matching_abstract M') = card (matching_abstract (rematch M l r1)) \<and>
                    rnb_invar C' \<and> rnb_abstract C' = rnb_abstract rnb_init \<and>
                    (\<forall>p. res = Some p \<longrightarrow> good_search_result M' \<pi>' p)"
            by (rule less.IH[OF _ st(1) C1 st(3,4) rec]) (simp add: Suc)
          thus ?thesis using st(2) by simp
        qed
      qed
    qed
  qed
qed

text \<open>The invariant of the loop over the left vertices, for the initial matching @{term M0}.\<close>

definition "sc_inv M0 s res =
  (case s of (C, M, \<pi>) \<Rightarrow>
     path_search_precond M \<pi> \<and> card (matching_abstract M) = card (matching_abstract M0) \<and>
     rnb_invar C \<and> rnb_abstract C = rnb_abstract rnb_init \<and>
     (case res of None \<Rightarrow> True | Some (l, p) \<Rightarrow> l \<in> L \<and> good_search_result M \<pi> p))"

lemma sc_row_valid:
  assumes "l \<in> L" "sc_inv M0 s None" "sc_row s l = (s1, r)"
  shows "sc_inv M0 s1 (map_option (Pair l) r)"
proof-
  obtain C M \<pi> where s: "s = (C, M, \<pi>)" by (metis prod_cases3)
  have I: "path_search_precond M \<pi>" "card (matching_abstract M) = card (matching_abstract M0)"
          "rnb_invar C" "rnb_abstract C = rnb_abstract rnb_init"
    using assms(2) by (simp_all add: sc_inv_def s)
  show ?thesis
  proof(cases "free M l")
    case True
    have lf: "l \<notin> Vs (matching_abstract M)"
      using True buddy(1)[OF path_search_precondD(1)[OF I(1)]] by (simp add: free_def)
    obtain C1 M1 \<pi>1 r1 where ch: "chain cap M \<pi> C l = (C1, M1, \<pi>1, r1)" by (metis prod_cases4)
    have eq: "s1 = (C1, M1, \<pi>1)" "r = r1"
      using assms(3) True by (simp_all add: s sc_row_def ch)
    show ?thesis
      using chain_valid[OF I(1,3,4) assms(1) lf ch] I(2) assms(1)
      by (auto simp: sc_inv_def eq split: option.splits)
  next
    case False
    have eq: "s1 = s" "r = None" using assms(3) False by (simp_all add: s sc_row_def)
    show ?thesis using assms(2) by (simp add: eq)
  qed
qed

lemma sc_loop_valid:
  assumes "set xs \<subseteq> L" "sc_inv M0 s None" "sc_loop s xs = (s', res, xs')"
  shows "sc_inv M0 s' res" "set xs' \<subseteq> set xs"
proof-
  have "sc_inv M0 s' res \<and> set xs' \<subseteq> set xs"
    using assms
  proof(induction xs arbitrary: s)
    case Nil
    thus ?case by simp
  next
    case (Cons l xs)
    obtain s1 r where row: "sc_row s l = (s1, r)" by fastforce
    have I1: "sc_inv M0 s1 (map_option (Pair l) r)"
      using sc_row_valid[OF _ Cons.prems(2) row] Cons.prems(1) by simp
    show ?case
    proof(cases r)
      case None
      have "sc_loop s1 xs = (s', res, xs')" using Cons.prems(3) by (simp add: row None)
      thus ?thesis using Cons.IH[of s1] Cons.prems(1) I1 None by auto
    next
      case (Some p)
      have "s' = s1" "res = Some (l, p)" "xs' = xs" using Cons.prems(3) by (simp_all add: row Some)
      thus ?thesis using I1 Some by auto
    qed
  qed
  thus "sc_inv M0 s' res" "set xs' \<subseteq> set xs" by simp_all
qed

lemma good_search_card:
  "\<lbrakk>good_search L R M1 res; card (matching_abstract M1) = card (matching_abstract M)\<rbrakk>
   \<Longrightarrow> good_search L R M res"
  by (auto simp: good_search_def split: prod.splits)

text \<open>The combination satisfies the contract of the path search of @{locale hungarian_loop},
      with @{const sc_ctx_invar} as the invariant of the context.\<close>

theorem path_search_sc_correct:
  assumes "path_search_precond M \<pi>" "sc_ctx_invar ctx"
    "path_search_sc b ctx M \<pi> = (r, M', \<pi>', ctx')"
  shows "good_search L R M (r, M', \<pi>')" "sc_ctx_invar ctx'"
proof-
  obtain xs C where ctx: "ctx = (xs, C)" by fastforce
  have C: "set xs \<subseteq> L" "rnb_invar C" "rnb_abstract C = rnb_abstract rnb_init"
    using assms(2) by (simp_all add: sc_ctx_invar_def ctx)
  have I0: "sc_inv M (C, M, \<pi>) None" using assms(1) C(2,3) by (simp add: sc_inv_def)
  obtain C1 M1 \<pi>1 res xs1 where st: "sc_try b (C, M, \<pi>) xs = ((C1, M1, \<pi>1), res, xs1)"
    by (metis prod_cases3)
  have I: "sc_inv M (C1, M1, \<pi>1) res" "set xs1 \<subseteq> L"
  proof-
    have "sc_inv M (C1, M1, \<pi>1) res \<and> set xs1 \<subseteq> L"
    proof(cases b)
      case True
      thus ?thesis using sc_loop_valid[OF C(1) I0] C(1) st by (fastforce simp: sc_try_def)
    next
      case False
      thus ?thesis using I0 C(1) st by (simp add: sc_try_def)
    qed
    thus "sc_inv M (C1, M1, \<pi>1) res" "set xs1 \<subseteq> L" by simp_all
  qed
  have I': "path_search_precond M1 \<pi>1" "card (matching_abstract M1) = card (matching_abstract M)"
           "rnb_invar C1" "rnb_abstract C1 = rnb_abstract rnb_init"
    using I(1) by (simp_all add: sc_inv_def)
  have "good_search L R M (r, M', \<pi>') \<and> sc_ctx_invar ctx'"
  proof(cases res)
    case None
    obtain C2 where fb: "fallback C1 M1 \<pi>1 = (r, M', \<pi>', C2)" "ctx' = (left_order, C2)"
      using assms(3) by (auto simp: path_search_sc_def ctx st None split: prod.splits)
    have F: "good_search L R M1 (r, M', \<pi>')" "rnb_invar C2" "rnb_abstract C2 = rnb_abstract rnb_init"
      using fallback[OF I'(1,3,4) fb(1)] by simp_all
    show ?thesis
      using good_search_card[OF F(1) I'(2)] F(2,3) G(2) by (simp add: sc_ctx_invar_def fb(2))
  next
    case (Some a)
    then obtain l p where a: "res = Some (l, p)" by (cases a) auto
    have eq: "r = Next_Iteration p" "M' = M1" "\<pi>' = \<pi>1" "ctx' = (xs1, C1)"
      using assms(3) by (simp_all add: path_search_sc_def ctx st a)
    show ?thesis using I by (simp add: good_search_def sc_inv_def sc_ctx_invar_def eq a)
  qed
  thus "good_search L R M (r, M', \<pi>')" "sc_ctx_invar ctx'" by simp_all
qed

end

end