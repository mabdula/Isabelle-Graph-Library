theory Path_Search_Shortcut
  imports
    Neighbourhood_Best_Scan
    Hungarian_Method_Top_Loop
    Data_Structures.More_Arith
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
  using bipartite_edgeD(1)[OF _ G(1)]
  by blast

lemma cost: "\<lbrakk>l \<in> L; {l, r} \<in> G\<rbrakk> \<Longrightarrow> red \<pi> l r = edge_costs {l, r} - potential_abstract \<pi> r"
  using edge_costs_code
  by (simp add: red_def potential)

lemma free_unmatched: "\<lbrakk>path_search_precond M \<pi>; free M r\<rbrakk> \<Longrightarrow> r \<notin> Vs (matching_abstract M)"
  using buddy(1) path_search_precondD(1)
  by (auto simp: free_def)

lemma not_free_matched: "\<lbrakk>path_search_precond M \<pi>; \<not> free M r\<rbrakk> \<Longrightarrow> {buddy_get M r, r} \<in> matching_abstract M"
  using buddy(2) path_search_precondD(1)
  by (auto simp: free_def)

text \<open>Matched edges that avoid the changed vertices stay tight.\<close>

lemma tight_keep:
  "\<lbrakk>S \<subseteq> tight_subgraph G edge_costs p; \<And>e x. \<lbrakk>e \<in> S; x \<in> e\<rbrakk> \<Longrightarrow> p' x = p x\<rbrakk>
     \<Longrightarrow> S \<subseteq> tight_subgraph G edge_costs p'"
  by (auto 4 4 elim!: in_tight_subgraphE intro!: in_tight_subgraphI[OF refl])

text \<open>A change of the potential at a left vertex @{term l} that is feasible on the edges of
      @{term l}, and that does not increase the potential elsewhere, keeps it feasible.\<close>

lemma feasible_after_row:
  assumes "feasible_min_perfect_dual G edge_costs p"
      and "\<And>y. {l, y} \<in> G \<Longrightarrow> p' l + p' y \<le> edge_costs {l, y}"
      and "\<And>x. x \<noteq> l \<Longrightarrow> p' x \<le> p x"
  shows "feasible_min_perfect_dual G edge_costs p'"
proof(rule feasible_min_perfect_dualI)
  fix e u v
  assume "e \<in> G" "e = {u, v}"
  thus "p' u + p' v \<le> edge_costs e"
    using assms(2)[of u] assms(2)[of v] feasible_min_perfect_dualD[OF assms(1), of e u v] assms(3)[of u] assms(3)[of v]
    by (cases "u = l"; cases "v = l"; auto simp: insert_commute add.commute)
qed

lemma precond_of_good:
  "\<lbrakk>path_search_precond M \<pi>; good_search_result M \<pi>' p\<rbrakk> \<Longrightarrow> path_search_precond M \<pi>'"
  by (simp add: path_search_precond_def good_search_result_def)

lemma pot_shift:
  assumes "potential_invar \<pi>" "l \<in> K" "r1 \<in> K"
  shows "potential_invar (pot_shift \<pi> l v r1 d)"
        "potential_abstract (pot_shift \<pi> l v r1 d) =
           (potential_abstract \<pi>)(l := v, r1 := potential_abstract \<pi> r1 - d)"
  using assms
  by (simp_all add: pot_shift_def potential potential_map.fixed_univ_map_upd potential_map.fixed_univ_map_upd_invar)

text \<open>Row changes of the potential in the style of Jonker-Volgenant: @{term l} gets @{term v} and its
      best neighbour @{term r1} is lowered by @{term "v - u1"}.\<close>

lemma row_shift_feasible:
  assumes "feasible_min_perfect_dual G edge_costs (potential_abstract \<pi>)" "l \<in> L" "{l, r1} \<in> G"
          "u1 = red \<pi> l r1" "u1 \<le> v" "\<And>r. \<lbrakk>{l, r} \<in> G; r \<noteq> r1\<rbrakk> \<Longrightarrow> v \<le> red \<pi> l r"
  shows "feasible_min_perfect_dual G edge_costs
           ((potential_abstract \<pi>)(l := v, r1 := potential_abstract \<pi> r1 - (v - u1)))"
  using assms(2-) nb_not_L[of l] cost[of l]
  by (intro feasible_after_row[OF assms(1)]; auto simp: algebra_simps)

lemma row_shift_tight:
  "\<lbrakk>l \<in> L; {l, r1} \<in> G; u1 = red \<pi> l r1\<rbrakk>
     \<Longrightarrow> {l, r1} \<in> tight_subgraph G edge_costs
           ((potential_abstract \<pi>)(l := v, r1 := potential_abstract \<pi> r1 - (v - u1)))"
  using cost[of l r1 \<pi>] nb_not_L[of l r1]
  by (auto intro!: in_tight_subgraphI[OF refl] simp: algebra_simps)

lemma augmenting_edge: "\<lbrakk>l \<in> L; {l, r1} \<in> G; l \<notin> Vs M; r1 \<notin> Vs M\<rbrakk> \<Longrightarrow> graph_augmenting_path G M [l, r1]"
  using nb_not_L[of l r1]
  by (auto intro!: matching_augmenting_pathI alt_list.intros path.intros simp: Vs_def)

text \<open>The end of a chain: the best neighbour @{term r1} is free. The potential of @{term l} becomes
      some @{term v} below the reduced costs of the other arcs of @{term l}, and @{term r1} is
      lowered by @{term "v - u1"}, which keeps @{term "{l, r1}"} tight.\<close>

lemma success_step:
  assumes "path_search_precond M \<pi>" "l \<in> L" "l \<notin> Vs (matching_abstract M)"
      "{l, r1} \<in> G" "r1 \<notin> Vs (matching_abstract M)" "u1 = red \<pi> l r1"
      "u1 \<le> v" "\<And>r. \<lbrakk>{l, r} \<in> G; r \<noteq> r1\<rbrakk> \<Longrightarrow> v \<le> red \<pi> l r" "potential_invar \<pi>'"
      "potential_abstract \<pi>' =
         (potential_abstract \<pi>)(l := v, r1 := potential_abstract \<pi> r1 - (v - u1))"
  shows "good_search_result M \<pi>' [l, r1]"
proof-
  note P = path_search_precondD[OF assms(1)]
  have "matching_abstract M \<subseteq> tight_subgraph G edge_costs (potential_abstract \<pi>')"
    using assms(3,5,10)
    by (auto intro!: tight_keep[OF P(4)] simp: Vs_def)
  thus ?thesis
    using assms(9,10) row_shift_feasible[OF P(5) assms(2,4,6-8)] row_shift_tight[OF assms(2,4,6)]
          augmenting_edge[OF assms(2,4,3,5)]
    by (auto intro!: good_search_resultI)
qed

text \<open>A link of a chain: @{term l} takes the matched best neighbour @{term r1} from @{term lq}
      ("WHY IT IS ALLOWED" in the pseudocode).\<close>

lemma rematch_others:
  "\<lbrakk>graph_matching G M; {lq, r1} \<in> M; l \<notin> Vs M; e \<in> M; e \<noteq> {lq, r1}\<rbrakk> \<Longrightarrow> l \<notin> e \<and> r1 \<notin> e \<and> lq \<notin> e"
  using matching_unique_match[of M r1 e "{lq, r1}"] matching_unique_match[of M lq e "{lq, r1}"]
  by (auto simp: Vs_def)

lemma rematch_keep:
  "\<lbrakk>M \<subseteq> tight_subgraph G edge_costs p; graph_matching G M; {lq, r1} \<in> M; l \<notin> Vs M\<rbrakk>
     \<Longrightarrow> M - {{lq, r1}} \<subseteq> tight_subgraph G edge_costs (p(l := v, r1 := w))"
  by ((rule tight_keep[where p = p], blast); use rematch_others[of M lq r1 l] in auto)

lemma rematch_tight:
  "\<lbrakk>M \<subseteq> tight_subgraph G edge_costs p; graph_matching G M; {lq, r1} \<in> M; l \<notin> Vs M;
    {l, r1} \<in> tight_subgraph G edge_costs (p(l := v, r1 := w))\<rbrakk>
     \<Longrightarrow> M - {{lq, r1}} \<union> {{l, r1}} \<subseteq> tight_subgraph G edge_costs (p(l := v, r1 := w))"
  using rematch_keep[of M p lq r1 l v w]
  by simp

lemma rematch_partner:
  "\<lbrakk>graph_matching G M; l \<in> L; l \<notin> Vs M; {l, r1} \<in> G; {lq, r1} \<in> M\<rbrakk> \<Longrightarrow> lq \<in> L \<and> lq \<noteq> l \<and> lq \<noteq> r1"
  using bipartite_edgeD(1)[of l r1 G L R] bipartite_edgeD(4)[of lq r1 G L R] G(1)
  by (auto simp: Vs_def)

lemma rematch_step:
  assumes "path_search_precond M \<pi>" "l \<in> L" "l \<notin> Vs (matching_abstract M)"
      "{l, r1} \<in> G" "{lq, r1} \<in> matching_abstract M"
      "{l, r2} \<in> G" "r2 \<noteq> r1"
      "u1 = red \<pi> l r1" "\<And>r. {l, r} \<in> G \<Longrightarrow> u1 \<le> red \<pi> l r"
      "u2 = red \<pi> l r2" "\<And>r. \<lbrakk>{l, r} \<in> G; r \<noteq> r1\<rbrakk> \<Longrightarrow> u2 \<le> red \<pi> l r"
      "\<pi>' = pot_shift \<pi> l u2 r1 (u2 - u1)"
  shows "path_search_precond (rematch M l r1) \<pi>'"
        "card (matching_abstract (rematch M l r1)) = card (matching_abstract M)"
        "lq \<in> L" "lq \<notin> Vs (matching_abstract (rematch M l r1))"
proof-
  note P = path_search_precondD[OF assms(1)]
  note R = rematch[OF P(1) assms(5,3,4)]
  have "potential_invar \<pi>'"
      "potential_abstract \<pi>' = (potential_abstract \<pi>)(l := u2, r1 := potential_abstract \<pi> r1 - (u2 - u1))"
    using pot_shift[OF P(2), of l r1 u2 "u2 - u1"] assms(2,4,12) G(3,4) edges_are_Vs_2[of l r1 G]
    by auto
  moreover have "u1 \<le> u2"
    using assms(6,9,10)
    by simp
  ultimately show "path_search_precond (rematch M l r1) \<pi>'"
    using R matching_graph rematch_tight[OF P(4,3) assms(5,3) row_shift_tight[OF assms(2,4,8), of u2]]
          row_shift_feasible[OF P(5) assms(2,4,8) _ assms(11)]
    by (auto intro!: path_search_precondI)
  show "lq \<in> L" "card (matching_abstract (rematch M l r1)) = card (matching_abstract M)"
      "lq \<notin> Vs (matching_abstract (rematch M l r1))"
    using rematch_partner[OF P(3) assms(2-5)] R(2) card_swap[OF assms(5), of "{l, r1}"]
          rematch_others[OF P(3) assms(5,3)] assms(3)
    by (auto simp: Vs_def)
qed

lemma best_two_chain_props:
  assumes "rnb_invar C" "rnb_abstract C = rnb_abstract rnb_init" "l \<in> L"
          "best_two (red \<pi>) (free M) l C = (C1, b, s)"
  shows "rnb_invar C1" "rnb_abstract C1 = rnb_abstract rnb_init"
        "b = Some (u1, r1) \<Longrightarrow> {l, r1} \<in> G \<and> u1 = red \<pi> l r1 \<and> (\<forall>r. {l, r} \<in> G \<longrightarrow> u1 \<le> red \<pi> l r)"
        "\<lbrakk>b = Some (u1, r1); s = Some (u2, r2)\<rbrakk> \<Longrightarrow>
           {l, r2} \<in> G \<and> r2 \<noteq> r1 \<and> u2 = red \<pi> l r2 \<and> (\<forall>r. {l, r} \<in> G \<and> r \<noteq> r1 \<longrightarrow> u2 \<le> red \<pi> l r)"
proof-
  note I = rnb_init(2,3)[OF assms(3)]
  note B = best_two_props[OF assms(1) subsetD[OF G(3) assms(3)] I(2)[folded assms(2)] assms(4)]
  show "rnb_invar C1" "rnb_abstract C1 = rnb_abstract rnb_init"
    using B(1,2) assms(2)
    by simp_all
  show "b = Some (u1, r1) \<Longrightarrow> {l, r1} \<in> G \<and> u1 = red \<pi> l r1 \<and> (\<forall>r. {l, r} \<in> G \<longrightarrow> u1 \<le> red \<pi> l r)"
    using B(4)[where x = u1 and j = r1] I(1) assms(2)
    by auto
  show "\<lbrakk>b = Some (u1, r1); s = Some (u2, r2)\<rbrakk> \<Longrightarrow>
          {l, r2} \<in> G \<and> r2 \<noteq> r1 \<and> u2 = red \<pi> l r2 \<and> (\<forall>r. {l, r} \<in> G \<and> r \<noteq> r1 \<longrightarrow> u2 \<le> red \<pi> l r)"
    using B(6)[where x = u1 and j = r1 and y = u2 and i = r2] I(1) assms(2)
    by auto
qed

lemma chain_found:
  "\<lbrakk>path_search_precond M \<pi>; l \<in> L; l \<notin> Vs (matching_abstract M); {l, r1} \<in> G; free M r1;
    u1 = red \<pi> l r1; u1 \<le> v; \<forall>r. {l, r} \<in> G \<and> r \<noteq> r1 \<longrightarrow> v \<le> red \<pi> l r; potential_invar \<pi>';
    potential_abstract \<pi>' = (potential_abstract \<pi>)(l := v, r1 := potential_abstract \<pi> r1 - (v - u1))\<rbrakk>
     \<Longrightarrow> path_search_precond M \<pi>' \<and> good_search_result M \<pi>' [l, r1]"
  using success_step[of M \<pi> l r1 u1 v \<pi>'] precond_of_good[of M \<pi> \<pi>' "[l, r1]"] free_unmatched[of M \<pi> r1]
  by auto

lemma chain_found_none:
  "\<lbrakk>path_search_precond M \<pi>; l \<in> L; l \<notin> Vs (matching_abstract M); {l, r1} \<in> G; free M r1;
    u1 = red \<pi> l r1; \<forall>r. {l, r} \<in> G \<longrightarrow> u1 \<le> red \<pi> l r\<rbrakk>
     \<Longrightarrow> path_search_precond M (potential_upd \<pi> l u1) \<and> good_search_result M (potential_upd \<pi> l u1) [l, r1]"
  using potential_map.fixed_univ_map_upd[of \<pi> l] potential_map.fixed_univ_map_upd_invar[of \<pi> l] nb_not_L[of l r1]
        path_search_precondD(2)[of M \<pi>] subsetD[OF G(3)]
  by (intro chain_found[where v = u1]; auto simp: potential fun_eq_iff)

lemma chain_found_some:
  "\<lbrakk>path_search_precond M \<pi>; l \<in> L; l \<notin> Vs (matching_abstract M); {l, r1} \<in> G; free M r1;
    u1 = red \<pi> l r1; \<forall>r. {l, r} \<in> G \<longrightarrow> u1 \<le> red \<pi> l r;
    {l, r2} \<in> G \<and> r2 \<noteq> r1 \<and> u2 = red \<pi> l r2 \<and> (\<forall>r. {l, r} \<in> G \<and> r \<noteq> r1 \<longrightarrow> u2 \<le> red \<pi> l r)\<rbrakk>
     \<Longrightarrow> path_search_precond M (pot_shift \<pi> l u2 r1 (u2 - u1)) \<and>
         good_search_result M (pot_shift \<pi> l u2 r1 (u2 - u1)) [l, r1]"
  using chain_found[of M \<pi> l r1 u1 u2 "pot_shift \<pi> l u2 r1 (u2 - u1)"] pot_shift[of \<pi> l r1 u2 "u2 - u1"]
        path_search_precondD(2)[of M \<pi>] G(3,4) edges_are_Vs_2[of l r1 G]
  by auto

lemma chain_rematch:
  "\<lbrakk>path_search_precond M \<pi>; l \<in> L; l \<notin> Vs (matching_abstract M); {l, r1} \<in> G; \<not> free M r1;
    u1 = red \<pi> l r1; \<forall>r. {l, r} \<in> G \<longrightarrow> u1 \<le> red \<pi> l r;
    {l, r2} \<in> G \<and> r2 \<noteq> r1 \<and> u2 = red \<pi> l r2 \<and> (\<forall>r. {l, r} \<in> G \<and> r \<noteq> r1 \<longrightarrow> u2 \<le> red \<pi> l r)\<rbrakk>
     \<Longrightarrow> path_search_precond (rematch M l r1) (pot_shift \<pi> l u2 r1 (u2 - u1)) \<and>
         card (matching_abstract (rematch M l r1)) = card (matching_abstract M) \<and>
         buddy_get M r1 \<in> L \<and> buddy_get M r1 \<notin> Vs (matching_abstract (rematch M l r1))"
  using rematch_step[of M \<pi> l r1 "buddy_get M r1" r2 u1 u2 "pot_shift \<pi> l u2 r1 (u2 - u1)"]
        not_free_matched[of M \<pi> r1]
  by auto

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
  obtain C1 b s where "best_two (red \<pi>) (free M) l C = (C1, b, s)"
    by (cases "best_two (red \<pi>) (free M) l C"; auto)
  note B = best_two_chain_props[OF less.prems(2-4) this]
  note ch = less.prems(6)[unfolded chain.simps[of k M \<pi> C l] \<open>best_two (red \<pi>) (free M) l C = (C1, b, s)\<close>]
  show ?case
  proof(cases b)
    case None
    thus ?thesis
      using ch B(1,2) less.prems(1)
      by simp
  next
    case (Some q)
    then obtain u1 r1 where "b = Some (u1, r1)"
      by fastforce
    hence "{l, r1} \<in> G \<and> u1 = red \<pi> l r1 \<and> (\<forall>r. {l, r} \<in> G \<longrightarrow> u1 \<le> red \<pi> l r)"
      by (rule B(3))
    show ?thesis
    proof(cases s)
      case None
      thus ?thesis
        using ch \<open>b = Some (u1, r1)\<close> \<open>{l, r1} \<in> G \<and> u1 = red \<pi> l r1 \<and> (\<forall>r. {l, r} \<in> G \<longrightarrow> u1 \<le> red \<pi> l r)\<close>
              B(1,2) chain_found_none[of M \<pi> l r1 u1] less.prems(1,4,5)
        by (cases "free M r1"; auto)
    next
      case (Some q2)
      then obtain u2 r2 where "s = Some (u2, r2)"
        by fastforce
      hence "{l, r2} \<in> G \<and> r2 \<noteq> r1 \<and> u2 = red \<pi> l r2 \<and> (\<forall>r. {l, r} \<in> G \<and> r \<noteq> r1 \<longrightarrow> u2 \<le> red \<pi> l r)"
        using B(4) \<open>b = Some (u1, r1)\<close>
        by blast
      show ?thesis
      proof(cases "free M r1")
        case True
        thus ?thesis
          using ch \<open>b = Some (u1, r1)\<close> \<open>s = Some (u2, r2)\<close> B(1,2) less.prems(1,4,5)
                \<open>{l, r1} \<in> G \<and> u1 = red \<pi> l r1 \<and> (\<forall>r. {l, r} \<in> G \<longrightarrow> u1 \<le> red \<pi> l r)\<close>
                chain_found_some[of M \<pi> l r1 u1 r2 u2] \<open>{l, r2} \<in> G \<and> r2 \<noteq> r1 \<and> u2 = red \<pi> l r2 \<and> _\<close>
          by auto
      next
        case False
        show ?thesis
        proof(cases k)
          case 0
          thus ?thesis
            using ch False \<open>b = Some (u1, r1)\<close> \<open>s = Some (u2, r2)\<close> B(1,2) less.prems(1)
            by simp
        next
          case (Suc k')
          hence "chain k' (rematch M l r1) (pot_shift \<pi> l u2 r1 (u2 - u1)) C1 (buddy_get M r1) = (C', M', \<pi>', res)"
            using ch False \<open>b = Some (u1, r1)\<close> \<open>s = Some (u2, r2)\<close>
            by simp
          moreover have "path_search_precond (rematch M l r1) (pot_shift \<pi> l u2 r1 (u2 - u1)) \<and>
              card (matching_abstract (rematch M l r1)) = card (matching_abstract M) \<and>
              buddy_get M r1 \<in> L \<and> buddy_get M r1 \<notin> Vs (matching_abstract (rematch M l r1))"
            using chain_rematch[of M \<pi> l r1 u1 r2 u2] False less.prems(1,4,5)
                  \<open>{l, r1} \<in> G \<and> u1 = red \<pi> l r1 \<and> (\<forall>r. {l, r} \<in> G \<longrightarrow> u1 \<le> red \<pi> l r)\<close>
                  \<open>{l, r2} \<in> G \<and> r2 \<noteq> r1 \<and> u2 = red \<pi> l r2 \<and> _\<close>
            by auto
          ultimately show ?thesis
            using less.IH[of k' "rematch M l r1" "pot_shift \<pi> l u2 r1 (u2 - u1)" C1 "buddy_get M r1" C' M' \<pi>' res]
                  B(1,2) \<open>k = Suc k'\<close>
            by auto
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
  "\<lbrakk>l \<in> L; sc_inv M0 (C, M, \<pi>) None; sc_row (C, M, \<pi>) l = (s1, r)\<rbrakk> \<Longrightarrow> sc_inv M0 s1 (map_option (Pair l) r)"
  using chain_valid[of M \<pi> C l cap] free_unmatched[of M \<pi> l]
  by (auto simp: sc_inv_def sc_row_def split: if_splits prod.splits option.splits)

lemma sc_loop_valid:
  "\<lbrakk>set xs \<subseteq> L; sc_inv M0 s None; sc_loop s xs = (s', res, xs')\<rbrakk> \<Longrightarrow> sc_inv M0 s' res \<and> set xs' \<subseteq> set xs"
proof(induction xs arbitrary: s)
  case (Cons l xs)
  obtain s1 r where "sc_row s l = (s1, r)"
    by fastforce
  moreover hence "sc_inv M0 s1 (map_option (Pair l) r)"
    using sc_row_valid[of l M0] Cons.prems(1,2)
    by (cases s rule: prod_cases3) auto
  ultimately show ?case
    using Cons.prems(1,3) Cons.IH[of s1]
    by (cases r; auto)
qed simp

lemma good_search_card:
  "\<lbrakk>good_search L R M1 res; card (matching_abstract M1) = card (matching_abstract M)\<rbrakk>
   \<Longrightarrow> good_search L R M res"
  by (auto simp: good_search_def split: prod.splits)

lemma sc_try_valid:
  "\<lbrakk>set xs \<subseteq> L; sc_inv M (C, M, \<pi>) None; sc_try b (C, M, \<pi>) xs = (s1, res, xs1)\<rbrakk> \<Longrightarrow> sc_inv M s1 res \<and> set xs1 \<subseteq> L"
  using sc_loop_valid[of xs M "(C, M, \<pi>)"]
  by (auto simp: sc_try_def split: if_splits)
text \<open>The combination satisfies the contract of the path search of @{locale hungarian_loop},
      with @{const sc_ctx_invar} as the invariant of the context.\<close>

lemma path_search_sc_correct:
  assumes "path_search_precond M \<pi>" "sc_ctx_invar ctx"
    "path_search_sc b ctx M \<pi> = (r, M', \<pi>', ctx')"
  shows "good_search L R M (r, M', \<pi>')" "sc_ctx_invar ctx'"
proof-
  obtain xs C where "ctx = (xs, C)"
    by fastforce
  obtain C1 M1 \<pi>1 res xs1 where "sc_try b (C, M, \<pi>) xs = ((C1, M1, \<pi>1), res, xs1)"
    by (cases "sc_try b (C, M, \<pi>) xs"; auto)
  have "set xs \<subseteq> L" "sc_inv M (C, M, \<pi>) None"
    using assms(1,2) \<open>ctx = (xs, C)\<close>
    by (simp_all add: sc_ctx_invar_def sc_inv_def)
  hence "path_search_precond M1 \<pi>1" "card (matching_abstract M1) = card (matching_abstract M)"
        "rnb_invar C1" "rnb_abstract C1 = rnb_abstract rnb_init" "set xs1 \<subseteq> L"
        "res = Some (l, p) \<Longrightarrow> l \<in> L \<and> good_search_result M1 \<pi>1 p" for l p
    using sc_try_valid[of xs M C \<pi> b "(C1, M1, \<pi>1)" res xs1] \<open>sc_try b (C, M, \<pi>) xs = ((C1, M1, \<pi>1), res, xs1)\<close>
    by (auto simp: sc_inv_def)
  have "good_search L R M (r, M', \<pi>') \<and> sc_ctx_invar ctx'"
  proof(cases res)
    case None
    then obtain C2 where "fallback C1 M1 \<pi>1 = (r, M', \<pi>', C2)" "ctx' = (left_order, C2)"
      using assms(3) \<open>ctx = (xs, C)\<close> \<open>sc_try b (C, M, \<pi>) xs = ((C1, M1, \<pi>1), res, xs1)\<close>
      by (auto simp: path_search_sc_def split: prod.splits)
    with fallback[OF \<open>path_search_precond M1 \<pi>1\<close> \<open>rnb_invar C1\<close> \<open>rnb_abstract C1 = rnb_abstract rnb_init\<close>]
         good_search_card[of M1 "(r, M', \<pi>')" M] \<open>card (matching_abstract M1) = card (matching_abstract M)\<close> G(2)
    show ?thesis
      by (auto simp: sc_ctx_invar_def)
  next
    case (Some a)
    thus ?thesis
      using assms(3) \<open>ctx = (xs, C)\<close> \<open>sc_try b (C, M, \<pi>) xs = ((C1, M1, \<pi>1), res, xs1)\<close>
            \<open>path_search_precond M1 \<pi>1\<close> \<open>card (matching_abstract M1) = card (matching_abstract M)\<close>
            \<open>rnb_invar C1\<close> \<open>rnb_abstract C1 = rnb_abstract rnb_init\<close> \<open>set xs1 \<subseteq> L\<close>
            \<open>\<And>l p. res = Some (l, p) \<Longrightarrow> l \<in> L \<and> good_search_result M1 \<pi>1 p\<close>
      by (auto simp: path_search_sc_def good_search_def sc_ctx_invar_def split: prod.splits)
  qed
  thus "good_search L R M (r, M', \<pi>')" "sc_ctx_invar ctx'"
    by simp_all
qed

end

end