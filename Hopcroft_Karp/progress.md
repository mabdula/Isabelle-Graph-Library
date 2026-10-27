# Hopcroft-Karp progress log

## Setup (2026-10-11, orchestrator)
- Project copy /media/llms/Isabelle-Graph-Library-Hopcroft-Karp (branch hopcroft-karp from dacfcfc + working-tree copies, see plan "Project copy").
- Isabelle home /media/llms/isabelle-home-hk; Micali_Vazirani heap built there (EXIT 0, 7:38).
- jEdit/I/Q: port 8767, token hk, logic Micali_Vazirani; bridge ./mcp.py pins port+token.

## Hopcroft_Karp Gate 1
Status: GATE 1 GREEN (beta-0 .. beta-4). PIDE: 0 errors, 0 sorry, is_processed; batch build exit 0 (Hopcroft_Karp, 12s). ASCII grep count 0. Snapshot backups/Hopcroft_Karp.thy.gate1-green.

beta-0 recon:
- Import merge Top_Loop + Basic_Matching.Berge loads with no duplicate-name errors and no ambiguity warnings.
- `matching` :: 'adjmap (BFS parameter); `Matching.matching` :: 'a set set => bool; `G` :: ('ver*'ver) set. As planned.
- No qualifier needed for any name in the recon list (induct_vwalk_bet, path.induct, edges_of_path.induct, alt_list_step/empty, alt_vwalk_bet_append_2/3, distance_set_0, bipartite_*, mem_path_Vs, vs_member, edges_are_Vs(_2), dVs_eq, dVsI, in_dVsE, dVs_subset, vwalk_bet_in_dVs/_in_vertices, hd_of_vwalk_bet'/'', last_of_vwalk_bet, aug_paths_are_even, matching_augmenting_path_def, distinct_map, path_edges_subset) except alt_dist.alt_vwalk_bet_subset and alt_dist.alt_dist_set_inf (locale prefix, as planned).
- Vwalk.vwalk_bet is displayed as dpath_bet. induct_vwalk_bet has P over (E p a b); the plan's `induction rule: induct_vwalk_bet` with case names path1/path2 worked as written.
- In the axiom context, copies_dagE, copies_lev_decrease, copies_reach_zero, altd_set_witness, valid_alt_BFS_DAG_props all show leading `BFS_axiom ==>` premise (so [OF BFS_axiom_hk ...] citation is right).
- Premise forms of the new lemmas: all four BFS_axiom lemmas take `BFS_axiom` (exported), copies_walk_alt_walk / copies_dag_cases / copies_dag_vtx_dVs are axiom-free.

Gate 1 lemmas (all passed REPL first try, all plan text verbatim modulo ASCII transcription; no repairs needed, no sledgehammer needed):
vwalk_bet_level_distinct (global), BFS.copies_dag_cases, BFS.copies_dag_vtx_dVs, BFS.copies_walk_alt_walk, BFS.copies_lev_zero, BFS.copies_walk_from_odd, BFS.VisO_copies_dVs.
Deviations: plan comments (beta-N goes here) replaced by the lemmas; the "Gate 2 adds..." comment at the beta-4 slot was consumed (re-add in Gate 2 if wanted); the `\<comment>` explanatory notes inside proofs were dropped. iq.iq temporarily imported for REPL, removed again.
Tooling notes: write_file needs `command` (str_replace/insert/line), not whole-content; shell heredocs with {...} braces get refused by the worktree guard (use dict() in scripts).

## Interim read-only graph theory (2026-10-11, orchestrator)
- Copied Hopcroft_Karp/Pair_Graph_Specs_Read_Only.thy from the Graph ADT copy (md5 eb614a94..., 166 lines, ASCII, no sorry/smt/metis); added to Hopcroft_Karp/ROOT before Hopcroft_Karp. Delete at integration (HK-D9).

## Gate 1 verified by orchestrator (2026-10-11)
- PIDE 0 errors (is_processed), statements identical to plan (8 lemmas), comment-aware scan 0 sorry/oops/metis/smt/apply/iq.iq, ASCII 0, batch build exit 0.

## Hopcroft_Karp Gate 2
Status: GATE 2 GREEN (gamma-0 .. gamma-6). PIDE: 0 errors, 0 warnings-as-errors (3 benign warnings, 2 pre-existing), is_processed, running 0, unprocessed 0; get_sorry_positions 0; ASCII grep count 0; batch build `isabelle build -d . Hopcroft_Karp` finished (11s). Snapshot backups/Hopcroft_Karp.thy.gate2-green. iq.iq import removed again.

Placement: gamma-0 (alt_list_edges_of_vwalk_path, alt_list_edges_of_path_vwalk) in section "Generic walk lemmas" before `context BFS`; gamma-1..6 in a nested instance context at the END of the BFS_axiom context (after VisO_copies_dVs), closed by `end -- matching instance`.
Lemmas: G_char, dVs_G_Vs, vwalk_G_path, path_vwalk_G, alt_walk_alt_path, alt_path_alt_list, aug_path_alt_walk, copies_walk_side, copies_walk_distinct_vtx, copies_walk_augmenting, aug_path_copies_start, aug_path_iff_free_odd_copy, BFS_aug_path_iff, BFS_copies_walk_augmenting.
Repairs (plan text otherwise verbatim modulo ASCII; no sledgehammer needed, both repairs are in non-search closers):
1. alt_list_edges_of_vwalk_path, step `ih`: plan `by (rule 3(1)[OF h(2) 3(4) 3(3)])` raised "OF: multiple unifiers" (higher-order, P/Q schematic). Replaced by `by (rule 3(1)[OF h(2)]) (fact 3(4), fact 3(3))`.
2. copies_walk_augmenting, `len2`: plan `using l0 ev by presburger` fails (simp preprocess turns `length (rev (map vtx q)) \<noteq> 0` into `q \<noteq> []`, so presburger sees a non-arithmetic premise). Replaced by a local helper `have gen: "\<And>n::nat. n \<noteq> 0 \<Longrightarrow> even n \<Longrightarrow> 2 \<le> n" by presburger` and `have len2: ... by (rule gen[OF l0 ev])`.
REPL lesson: repl_init_from_source with a pattern anchors AFTER the matched command; anchoring at `end <comment BFS_axiom context>` lands OUTSIDE the context (BFS_axiom_hk then reads `BFS_axiom ==> BFS_axiom`). Anchor on the last `by` of VisO_copies_dVs and step `qed` first.
Tooling lesson: after earlier inserts, line numbers from the on-disk file are stale vs the jEdit buffer; use read_file mode Line on the buffer before `insert` (one mis-insert was undone with str_replace of the whole inserted text).

## Gate 2 verified by orchestrator (2026-10-11)
- PIDE 0 errors (is_processed), 24 lemma statements + instance-context assumptions identical to plan, comment-aware scan 0 sorry/oops/metis/smt/apply/iq.iq, ASCII 0, batch build exit 0. HK-M1 (oracle) COMPLETE.
- Accepted closer repairs: OF with two higher-order premises -> rule + (fact, fact); presburger after simp-normalised premises -> local arithmetic helper.

## Hopcroft_Karp Gate 3
Status: GATE 3 GREEN (delta-0 .. delta-6), new theory Hopcroft_Karp/HK_Top_Loop.thy (315 lines, imports only Basic_Matching.Berge). PIDE: 0 errors, 0 warnings, running 0, unprocessed 0, is_processed; get_sorry_positions 0; ASCII grep count 0; batch `isabelle build -d . Hopcroft_Karp` finished (11s). ROOT theories: Pair_Graph_Specs_Read_Only HK_Top_Loop Hopcroft_Karp. Snapshot backups/HK_Top_Loop.thy.gate3-green. iq.iq import removed again, REPLs removed.
All plan text verbatim modulo ASCII, every step REPL-gated step by step. One repair, in aug_path_disjoint_preserved (delta-1): the plan closers `using VsM' qh disj hd_in_set[OF qne] hd_in_set[OF pne] last_in_set[OF pne] by blast` for qh' and ql' timed out in the REPL (10s cap). Sledgehammer not used (non-arithmetic trivial set-membership goal); decomposed instead: local facts hq/lq/hp/lp (by rule hd_in_set/last_in_set), four disequalities a,b,c,d (`using disj .. by (intro notI) (auto)`, 0.01s each), then qh' / ql' by `unfolding VsM' using .. by simp`. Statement unchanged. No other deviations (the `end -- hk_loop_spec` comment dropped; skeleton comment lines dropped).

## Gate 3 verified by orchestrator (2026-10-11)
- PIDE 0 errors (is_processed), all statements/definitions/locale assumptions identical to plan, scan 0 sorry/oops/metis/smt/apply/iq.iq, ASCII 0, batch build exit 0. HK-M2 (abstract loop) COMPLETE.
- Accepted repair: delta-1 qh/ql blast closers exceeded the REPL cap; replaced by explicit membership facts + simp.

## Hopcroft_Karp Gate 4
Status: GATE 4 GREEN (eps-0 .. eps-5), new theory Hopcroft_Karp/HK_Search.thy (imports only Micali_Vazirani.IDFS). PIDE: 0 errors, 0 warnings, running 0, unprocessed 0, is_processed; get_sorry_positions 0; ASCII grep count 0; batch `isabelle build -d . Hopcroft_Karp` finished (12s). ROOT theories: Pair_Graph_Specs_Read_Only HK_Top_Loop HK_Search Hopcroft_Karp. Snapshot backups/HK_Search.thy.gate4-green. iq.iq import removed again, REPL hk4 removed.
eps-0 recon: every IDFS_* fact (sound_1/2/3/6/7/8, vis_works_1/3/4, closed_None, complete_w, dVs_bound) carries the six premises in plan order (dpath (rev p), distinct p, vset_inv avoid, vset_inv vis, avoid subset dVs, vis subset dVs) then the IDFS_impl call; sound_6 has an extra trailing `p <> []`; IDFS_complete_w concludes `set p - t_set avoid <= t_set vis'` (as used). vwalk1: `v : dVs G ==> dpath G [v]`. set_ops.set_union/invar_union take two vset_inv premises. No change to the A bundle.
Deviations: one repair, root_call 4th conjunct (r : t_set vis'): plan closer `using IDFS_complete_w[...] that(2) by simp` leaves `{r} - avoid <= vis' ==> r notin avoid ==> r : vis'` unsolved; replaced by explicit h (IDFS_complete_w), m (r : set [r] - t_set avoid by simp), `by (rule subsetD[OF h m])`. Not sledgehammered (trivial membership, decomposed instead). Everything else verbatim modulo ASCII and dropped comment lines.

## Gate 4 verified by orchestrator (2026-10-11)
- PIDE 0 errors (is_processed), all statements identical to plan, scan 0 sorry/oops/metis/smt/apply/iq.iq, ASCII 0, batch build exit 0. HK-M3 (search) COMPLETE.
- Accepted repair: root_call conjunct 4 closer replaced by subsetD on IDFS_complete_w.

## Hopcroft_Karp Gate 5
Status: STOPPED AT zeta-0 (plan stop condition hit: the alt_bfs.* HK-M1 lemmas are NOT available under that name). Nothing of zeta-1..6 written. HK_Phase.thy = import skeleton only (imports as in zeta-0, no iq.iq, ASCII 0); ROOT now lists HK_Phase after Hopcroft_Karp; batch isabelle build -d . Hopcroft_Karp exit 0 (17s): the import merge (Hopcroft_Karp, HK_Top_Loop, HK_Search, Pair_Graph_Specs_Read_Only, Alt_BFS_Example, DDFS_Example, Matching_Augmentation_Executable) loads in PIDE and in batch.

zeta-0 recon record (REPL anchored after begin of HK_Phase, 2026-10-11):
(a) merge loads, no clashes (PIDE 0 errors; batch exit 0).
(b) term results:
- alt_bfs_impl takes matching, unmatching, state (adjmap type is ((a * (a*color) tree) * color) tree); returns a state.
- alt_bfs_initial_state takes the srcs tree, returns a BFS_state.
- alt_bfs.BFS_axiom takes: a itself, srcs, matching, unmatching (theorem form: Alt_BFS.BFS.BFS_axiom isin t_set M.invar Leaf vset_inv lookup ?srcs ?matching ?unmatching). The plan order (alt_bfs.BFS_axiom Mt Ut S) is WRONG; correct is srcs matching unmatching, plus leading itself argument.
- alt_bfs.valid_alt_BFS_DAG_impl takes: srcs matching unmatching T dists VisE VisO.
- alt_bfs.copies_dag, alt_bfs.copies_lev: UNDEFINED constants (Top_Loop locale constants, shown as BFS.copies_dag isin vset_empty lookup_neighb matching unmatching dG and BFS.copies_lev isin t_set vset_empty lookup_neighb srcs matching unmatching w).
- IDFS_witness.IDFS_impl argument order: insert isin sel vset_empty union diff lookup G P avoid p vis. EXACTLY the plan hk_phase order (vset_insert isin sel vset_empty vset_union vset_diff lookup CG P ...). No change needed.
- idfs.Graph.from_list and G.from_list: (a*a) list to adjmap. vset_of_list_rbt: a list to (a*color) tree; vset_of_list_rbt_def: vset_of_list_rbt is DFS_avoid.vset_of_list vset_insert vset_empty (foldr vset_insert xs vset_empty).
- parents = BFS_2.BFS_state.parents (works on Alt_BFS.BFS_state); distances, visited_odd, visited_even are Alt_BFS record fields.
(c) thm results:
- AVAILABLE as alt_bfs.*: BFS_valid_DAG_impl (premise BFS_axiom for ?srcs ?matching ?unmatching; conclusion about alt_bfs.BFS ... (alt_bfs_initial_state ?srcs)), BFS_impl_same (premise alt_bfs.BFS_dom), initial_state_props (13 facts, last is BFS_dom), BFS_axiom_def.
- NOT AVAILABLE as alt_bfs.*: copies_walk_augmenting, aug_path_iff_free_odd_copy, copies_reach_zero, valid_DAG_layered, copies_lev_by_lookup, copies_dag_dVs, VisO_copies_dVs (all Undefined fact). Reason: they were added to locale BFS in Top_Loop/Hopcroft_Karp, which do not import Alt_BFS_Example, so the alt_bfs registration never receives them; merging theories does not re-propagate.
- They ARE available as locale facts BFS.name with leading premise the locale predicate Alt_BFS.BFS ?empty ... ?init_dists (thm BFS.copies_walk_augmenting, BFS.VisO_copies_dVs, BFS.BFS_aug_path_iff all exist). The predicate fact EXISTS: alt_bfs.BFS_axioms, i.e. Alt_BFS.BFS vset_empty RBT_Map.delete vset_insert isin t_set sel update M.invar Leaf vset_delete vset_inv vset_union vset_inter vset_diff lookup lookup vset_empty update RBT_Map.delete M.invar ?srcs expand_tree BFS_Example.next_frontier upd_dists_exec (init_dists_exec ?srcs). So BFS.copies_walk_augmenting[OF alt_bfs.BFS_axioms bfs_axiom ...] is a possible citation form (NOT yet tested in a proof; not used).
- G.from_list_correct (5 facts: G.graph_inv, idfs.Graph.finite_graph, idfs.Graph.finite_vsets, G.digraph_abs (G.from_list es) = set es, has_neighb_set); idfs.Graph.from_list_correct same shape with idfs.Graph.*.
- idfs.vset_of_list_aux does NOT exist (idfs interprets DFS_avoid; the lemma lives in DFS_avoid_thms). Usable instead: ddfs_diamond.vset_of_list_aux (graph independent): vset_inv (foldr vset_insert xs vset_empty) and t_set (...) = set xs.
- Other probed names: matching_augmentation_spec.symmetric_buddiesD (premise symmetric_buddies lookup M; conclusion lookup M u = Some v iff lookup M v = Some u) exists; the primed M-def lemma exists, equal to the set of pairs x y with lookup M x = Some y; invar_matchingD gives 5 facts (buddy_invar, symmetric_buddies, no_self_loop_buddy, graph_matching G (M M), finite (M M)); idfs.Graph.vset.set.invar_insert exists; Set2.invar_insert and idfs.vset.set.invar_insert do not.
(d) syntactic equality checks: alt_bfs.Graph.c is not a constant name (Alt_BFS.BFS Graph is Pair_Graph_Specs.* at the BFS parameters; BFS_axiom_def unfolds to G.digraph_abs, G.graph_inv, idfs.Graph.finite_graph, idfs.Graph.finite_vsets, so the alt-BFS side is the G.* vocabulary). Between G and idfs.Graph: finite_graph and finite_vsets are rfl-equal; digraph_abs, graph_inv, neighbourhood are NOT (G uses M.invar and Leaf; idfs.Graph uses adj_inv and vset_empty; idfs.Graph.neighbourhood is neighbourhood_idfs; G.neighbourhood displays as alt_bfs.unmatching_neighbourhood). Bridge lemmas needed (adj_inv and vset_empty unfolding, as in DDFS_Example eq/gi steps).
(e) IDFS_witness.IDFS_impl_def DOES carry a locale premise: the full predicate IDFS_witness ?empty ... ?G ?lev, then IDFS_impl insert isin sel vset_empty union diff lookup G P avoid p vis = (let st = DFS_avoid.avoid_final_state_impl insert isin sel vset_empty union diff lookup G (IDFS_stack0 isin avoid vis p) vis avoid P in (ret st, visited st)). For Gate 6, a code equation for hk_phase cannot use it as a global lemma (the premise mentions the run-time graph CG); a hk_phase variant calling IDFS_stack0 and avoid_impl_rbt directly (axiom-free, cf. avoid_impl_rbt_code in DDFS_Example) would be needed.

### Gate 5 result (after orchestrator amendment zeta-A)
Status: GATE 5 GREEN (zeta-0 .. zeta-6), new theory Hopcroft_Karp/HK_Phase.thy (814 lines). PIDE: 0 errors, running 0, unprocessed 0, is_processed, 11 benign warnings (partially applied constant in interpretation notes); get_sorry_positions 0; comment-aware scan 0 sorry/oops/metis/smt/apply/meson/iq.iq; ASCII grep count 0; batch isabelle build -d . Hopcroft_Karp exit 0 (20s). ROOT: Pair_Graph_Specs_Read_Only HK_Top_Loop HK_Search Hopcroft_Karp HK_Phase. Snapshots backups/HK_Phase.thy.zeta4, .zeta5, .gate5-green. iq.iq removed, REPL hk5 removed.
Final theorems (thm): hk_input Gin vs X Y ==> mate_invar (UG_of Gin) m ==> P : set (hk_phase (hk_edges Gin vs) vs m) ==> graph_augmenting_path (UG_of Gin) (mate_matching m) P; ... ==> sorted_wrt (%P Q. set P Int set Q = {}) (hk_phase ...); ... ==> EX P. graph_augmenting_path ... P ==> hk_phase ... ~= [].
Deviations (all logged with reason):
1. hkbfs interpretation: global_interpretation (not interpretation; matches Alt_BFS_Example form, for ... clause) with empty_dist = Leaf instead of RBT_Set.empty, proved by using alt_bfs.BFS_axioms by (simp add: RBT_Set.empty_def). Reason: a registration identical to alt_bfs is merged into it and receives no facts (tested: hkbfs with identical clauses gave no hkbfs.* facts at all). BFS_impl/initial_state are definitional constants alt_bfs_impl/alt_bfs_initial_state (unfold alt_bfs_impl_def to match hkbfs.BFS_impl); valid_alt_BFS_DAG(_impl), BFS, BFS_dom, BFS_axiom are rfl-equal to the alt_bfs ones.
2. bfs_axiom statement written as Alt_BFS.BFS.BFS_axiom isin Tree2.set_tree M.invar Leaf vset_inv lookup S Mt Ut (argument order srcs matching unmatching; no itself argument needed in this form).
3. valid_alt_BFS_DAG_impl order srcs matching unmatching T dists VisE VisO; st_valid/st_valid' use hkbfs.*; st_eq (new helper) = alt_bfs.BFS_impl_same[OF initial_state_props(13)[OF bfs_axiom]].
4. zeta-1: mate_Map_axioms new helper (plan used Map_axioms_as_needed from Hungarian); mate_matching_eq := mate.\<M>_def' alias (the folded fact is already stated with mate_matching, so unfolding mate_matching_def first, as in the plan, breaks it); mate_invarD(2) cited for symmetric_buddies (mate_invarD is the 5-fact list); mate.symmetric_buddiesD exists.
5. zeta-2: unchanged (RO interpretation with vset_delete = RBT.delete as in the plan; five RO_* bridge lemmas pass by ext + simp).
6. zeta-3: hk_phase uses nested lets instead of the semicolon let (identical term; the I/R REPL splits commands at the semicolon) and Alt_BFS.BFS_state.parents (plain parents resolves to BFS_2.BFS_state.parents with the wrong record type); step argument hk_idfs CG (...) with global hk_stack0/hk_idfs (zeta-A item 5). hk_idfs_eq proved by intro ext + simp with hk_idfs_def hk_stack0_def W.IDFS_impl_def W.IDFS_stack0_def avoid_impl_rbt_def (0.08s).
7. Global helpers added: fold_min_mem (stated with Set.insert, because insert resolves to the RBT insert), layered_dgraph_cong, vset_of_list_rbt_props (induction via idfs.Graph.vset.set.invar_insert/set_insert, unfolding idfs.vset_of_list_def; DFS_avoid.vset_of_list_def carries a locale premise and does not unfold).
8. zeta-4: Vs_UG plan closer (by auto simp: ... dVs_eq) failed; replaced by two explicit inclusions (vs_member, UG_of_def, dVsI, in_dVsE, symmetry inp_parts(4)). Others verbatim. UG_graph_invar blast passed.
9. zeta-5: M_sub by auto (graph_matching is an abbreviation, no _def). Mt_abs/Ut_abs written from the outline via set equality (G.from_list_correct(4), mate_matching_iff, UG_edge_iff, hk_edges_set). S_props via local induction on foldr insert_rbt (for xs). bfs_axiom: finite neighbourhoods via local fin_nb (snd image), srcs subset dVs via edge at free vertex, disjointness from Mt_abs/Ut_abs. T_sub via valid_alt_BFS_DAG_props(3). New helpers T_graph_inv, isin_T (set.set_isin), cl_mem (concat/map membership), CG_abs by two inclusions (the first attempt with consider/blast timed out in the REPL; replaced by explicit cx2 disjunction, obtain by elim exE conjE, and show by intro exI conjI), S_free, VO_inv, dVs_CG. CG_level by hkbfs.copies_lev_by_lookup. CG_layered by hkbfs.valid_DAG_layered + layered_dgraph_cong. interpretation W: IDFS_witness established inside the m-context exactly as in DDFS_Example (3 cases: G.Pair_Graph_Specs_axioms, RBT.Set2_axioms, CG_layered) - no obstacle. roots_props/roots_dVs/roots_nonempty (assumes ... shows form, same theorem)/blk_props proved as outlined (roots_nonempty by define fs/L/k + fold_min_mem).
10. zeta-6: local interpretation W does not survive the m-context, so the three proofs are split into aux lemmas inside the m-context (phase_unfold, DS_facts, phase_sound_aux, phase_disjoint_aux, phase_complete_aux) and the three theorems outside (free_list = [] case analysis). Statements of hk_phase_sound/_disjoint/_complete unchanged. phase_complete: W.disjoint_search_nonempty needs [where P = ...] (multiple unifiers otherwise).
Mate wording: no new identifier contains buddy.
Sledgehammer: not needed (no step required discovery; every failed closer was a decomposable membership/obtain goal, repaired by decomposition per the rules).
Gate 6 notes: (i) IDFS_witness.IDFS_impl_def has the locale premise; hk_phase already uses hk_idfs, with hk_idfs_eq available only inside the m-context (local interpretation W) - Gate 6 needs code equations only for hk_idfs/hk_stack0 (plain defs over avoid_impl_rbt, which has code equations). (ii) Code concerns to test with export_code/value: RO.neighbourhood (hk_edges) - the interpretation RO emits a Partially applied constant Lookup2.lookup warning for the [code] equation inherited from the read-only locale, so add [code] RO_neighbourhood (RO.neighbourhood = G.neighbourhood) or an explicit equation; idfs.Graph.from_list/add_edge and G.from_list have only the locale-def equations (idfs.Graph.from_list_def etc.), check they are declared [code] (DDFS_Example has no [code] for idfs.Graph.from_list); hk_level uses the_enat; hk_roots uses fold min; hk_blk uses vset_of_list_rbt (code equation vset_of_list_rbt_code exists). (iii) The abbreviations es/Mt/Ut/S/st/T/cl/CG/lv are printed as local.* abbreviations outside the contexts (display only). (iv) hkbfs is a global_interpretation registered with empty_dist = Leaf: its Graph.* constants are not syntactically the G.* ones in display, but G.digraph_abs equality is by rfl.

## Gate 5 verified by orchestrator (2026-10-11)
- PIDE 0 errors (is_processed), hk_phase_sound/disjoint/complete + hk_input/UG_of/hk_edges statements identical to plan; zeta-3 definitions identical except the approved zeta-A changes (hk_idfs step, nested lets, Alt_BFS.BFS_state.parents qualifier); scan 0 sorry/oops/metis/smt/meson/apply/iq.iq, ASCII 0, batch build exit 0.
- Accepted deviation: hkbfs is a global_interpretation with empty_dist = Leaf (an identical registration to alt_bfs is merged and gets no facts).

## Hopcroft_Karp Gate 6
Status: GATE 6 GREEN (eta-1 .. eta-3), new theory Hopcroft_Karp/HK_Example.thy (163 lines, imports only HK_Phase). PIDE: 0 errors, 2 benign warnings (Introduced fixed type variable 'b in xs__), running 0, unprocessed 0, is_processed; get_sorry_positions 0; ASCII grep count 0; scan 0 sorry/oops/metis/smt/apply/iq.iq/buddy; batch "isabelle build -d . Hopcroft_Karp" exit 0 (19s); export_code hopcroft_karp in SML module_name HK succeeds. ROOT: ... HK_Phase HK_Example. Snapshot backups/HK_Example.thy.gate6-green. iq.iq removed, REPL hk6 removed. HK_Phase.thy and all other Gate 1-5 files untouched.

Code equations (the only plumbing needed; the inherited equations are unusable because RO, G and idfs.Graph are plain interpretations, so their constants are partial applications of locale constants, e.g. pair_graph_specs_read_only.neighbourhood Leaf lookup; declaring "lemmas [code] = RO.neighbourhood_def" gives "Partially applied constant Lookup2.lookup"):
- value of hk_edges demo_G demo_vs first failed with "No code equations for pair_graph_specs_read_only.neighbourhood, Pair_Graph_Specs.from_list".
- Fix: global constants nb_rbt, add_edge_rbt, from_list_rbt, add_edge_idfs, from_list_idfs with their own definitions (copied from the locale equations at the RBT operations), plus [code_unfold] lemmas RO.neighbourhood = nb_rbt, G.neighbourhood = nb_rbt, G.add_edge = add_edge_rbt, G.from_list = from_list_rbt, idfs.Graph.add_edge = add_edge_idfs, idfs.Graph.from_list = from_list_idfs (each by ext + unfolding the interpretation definitions). No change to HK_Phase.thy was needed.
- hk_exec.hk_loop_impl / augment_list: the lemmas [code] of the locale hk_loop_defs transfer through the global_interpretation; no extra code equation. hk_idfs/hk_stack0/avoid_impl_rbt/vset_of_list_rbt/mate_augment: executable as they are.
- The global_interpretation hk_exec ... defines ... done is accepted exactly as planned.
Sledgehammer: not needed (no failed closer; the only repair was a missing-code-equation problem).

Value outputs (computed in the REPL before the file was written; the same commands are in the theory):
1. hk_edges demo_G demo_vs = [(0, 3), (0, 4), (1, 3), (1, 5), (2, 4), (3, 0), (3, 1), (4, 0), (4, 2), (5, 1)]
   Expected by hand: neighbours of u in RBT in-order are sorted, so for vs = [0..5]: 0:[3,4], 1:[3,5], 2:[4], 3:[0,1], 4:[0,2], 5:[1], concatenated: AGREES.
2. hk_phase (hk_edges demo_G demo_vs) demo_vs Leaf = [[4, 0], [3, 1]]
   Hand simulation (empty matching): srcs = all six vertices (Even copies, level 0); every vertex has a neighbour, so all six Odd copies are at level 1; the parents graph T contains all 10 edges; copies edges (Odd v -> Even u for each edge (u,v), inserted in es order) give N(O0) = (E3,E4) with root E3, N(O1) = (E3,E5), N(O2) = (E4), N(O3) = (E0,E1), N(O4) = (E0,E2), N(O5) = (E1); order on copies: Even < Odd, then the vertex. Roots = [O0, ..., O5] (all level 1). Root O0: seen = (O0); sel of (N(O0) - seen) is the ROOT of the tree returned by diff_rbt (join-based, it re-roots): diff of B(E3, R(E4)) with B(O0) splits at O0 and gives B(R(E3), E4, Leaf), root E4 (computed by hand through split/join/join2), so sel = E4; E4 satisfies P (level 0) -> path [E4, O0], read off [4,0]. blk = copies E0,O0,E4,O4. Root O1: seen = avoid + O1 = B(B(E0), E4, B(R(O0), O1, R(O4))) (union computed by hand); diff N(O1) seen = B(E3, R(E5)) after join2, root E3 -> path [E3, O1], read off [3,1]; blk adds E1,O1,E3,O3. Root O2: N(O2) = (E4) is avoided -> backtrack, None. Roots O3, O4 are in avoid (hk_stack0 drops them, empty stack) -> None. Root O5: N(O5) = (E1) avoided -> None. Expected [[4,0],[3,1]]: AGREES (the tie-break E4 versus E3 at the first root is decided by diff_rbt re-rooting, not by insertion order).
3. Tree2.inorder (hopcroft_karp demo_G demo_vs) = [(0, 3), (1, 5), (2, 4), (3, 0), (4, 2), (5, 1)]
   Expected: after phase 1 the matching is 4-0, 3-1; free = 2, 5; the only augmenting path is 2-4-0-3-1-5, giving 2-4, 0-3, 1-5, the unique perfect matching of the demo graph (2-4 and 1-5 are forced, then 0-3). Mate map: 6 entries, symmetric: AGREES. (Phase 2 reasoned at the level of the unique augmenting path, not traced through the tree structures.)

Proofs: all closers passed the REPL cap on the first try (<0.6s each); eta-2 text verbatim except:
- DEVIATION in hopcroft_karp_correct: the plan name hk.hk_loop_impl does not exist (the constant displays as hk_loop_defs.hk_loop_impl mate_augment (hk_phase (hk_edges Gin vs) vs)); the helper fact eq is stated with that term. Theorem statement unchanged; closer is simp with hopcroft_karp_def hk_loop_exec_def.
- demo_input split into one lemma per conjunct (demo_abs, demo_inv, demo_fin, demo_sym, demo_loop, demo_vs_dVs, demo_bip).
- Placement: code-equation section before the loop; value commands before the demo proofs.
thm hopcroft_karp_correct: hk_input ?Gin ?vs ?X ?Y ==> mate_invar (UG_of ?Gin) (hopcroft_karp ?Gin ?vs); hk_input ?Gin ?vs ?X ?Y ==> max_card_matching (UG_of ?Gin) (mate_matching (hopcroft_karp ?Gin ?vs)).
thm demo_max: max_card_matching (UG_of demo_G) (mate_matching (hopcroft_karp demo_G demo_vs)).
Mate wording: no new identifier contains buddy.

## Gate 6 verified by orchestrator (2026-10-11)
- PIDE 0 errors (is_processed); hopcroft_karp_correct and demo_max statements as planned; hopcroft_karp definition as planned; HK_Phase.thy unchanged since gate5-green (md5); scan 0 sorry/oops/metis/smt/apply/iq.iq/buddy; ASCII 0; full session batch build exit 0; export_code in file.
- Demo independently re-traced: phase 1 on the empty matching returns [[4,0],[3,1]] (two disjoint shortest paths of length 1); phase 2 the unique length-5 path 2-4-0-3-1-5; final mate function = perfect matching {0,3},{1,5},{2,4}.
- Accepted deviations: executable copies of RO/G/idfs.Graph neighbourhood/add_edge/from_list with [code_unfold] bridges; demo_input split per conjunct.
- CAMPAIGN STATUS: Gates 1-6 GREEN. Not done: HK-M5 (O(sqrt V) phase bound), integration of the read-only split (HK-D9), commit (user decision).

## Restyle R0 (orchestrator, 2026-10-11)

User: "go ahead with R0"; read-only locales to be capitalised (Pair_Graph_Specs_Read_Only,
Pair_Graph_U_Specs_Read_Only); the Graph ADT session has ended, so the rename is done here in R0-0.

- R0-1 snapshots: Hopcroft_Karp/backups/restyle-R0/ (six HK theories + ROOT).
- R0-2 baseline: batch build of Hopcroft_Karp exit 0; demo values via PIDE:
  edges [(0,3),(0,4),(1,3),(1,5),(2,4),(3,0),(3,1),(4,0),(4,2),(5,1)], phase 1 [[4,0],[3,1]],
  final mate map [(0,3),(1,5),(2,4),(3,0),(4,2),(5,1)].
- R0-3 baseline measurements reproduce the HK column of stats.txt
  (tmp/r0_stats.txt, tmp/r0_locale_struct.txt).
- R0-0 integration:
  - pre-images backed up to Hopcroft_Karp/backups/integration/*.orig (+ HK theories, ROOT);
  - Graph_ADT_Split.patch (md5 837a51f7...) dry run clean, applied with `patch -p1` (exit 0);
  - renamed pair_graph_specs_read_only -> Pair_Graph_Specs_Read_Only (20 occurrences) and
    pair_graph_u_specs_read_only -> Pair_Graph_U_Specs_Read_Only (4) in the six patched files;
  - subsumption confirmed by inspection: G in Pair_Graph_RBT has the same read-only
    operations as RO, so RO.* -> G.* and the five RO_* bridges are removed (HK edits via I/Q);
  - own jEdit (pid 2177071) shut down before patching (no modified buffers);
  - isabelle-home-hk etc/settings: ISABELLE_TOOL_JAVA_OPTIONS -Xmx16g.
  - NOTE: one read-only `tools/list` request was sent to port 8765 (another campaign's jEdit) by
    mistake while ours was down; no authentication, no edits.
- R0-0 HK side (via I/Q): HK_Phase (import of the interim theory, RO interpretation and five
  RO_* bridges removed, RO. -> G.) and HK_Example (RO_nb_code_unfold removed,
  G_nb_code_unfold proved directly, RO_* unfoldings dropped, RO. -> G.) written with
  write_file and saved; disk == reviewed contents, ASCII. Interim theory deleted (copy in
  backups/integration/), ROOT entry removed. Micali_Vazirani heap rebuilt in isabelle-home-hk
  (7.5 min); jEdit relaunched (pid 2345497, port 8767). PIDE: HK_Example and HK_Phase 0 errors;
  demo values unchanged.
- R0-4..6 checks (scratch theory Hopcroft_Karp/R0_Scratch.thy, not in ROOT; delete when jEdit
  next closes):
  - free: current_matching, phases, roots, avoided, explored, paths, ugraph_abs,
    Hopcroft_Karp*, Disjoint_Paths_Search*, adjacency_edges, matched_edges, free_vertices,
    copies_edges, copy_level, phase_roots, blocked_copies, IDFS_impl_rbt, bfs_sources; top-level
    fact names matching, augment, phase, search_step undefined (free);
  - initial_state, call_1_measure exist only as locale-qualified constants (as in DFS/BFS);
  - Pair_Graph_Specs_Read_Only parameters: insert isin t_set sel vset_empty vset_delete
    vset_inv lookup adjmap_inv;
  - global_interpretation ... for x y defines c = ...: c is abstracted only over the for-variables
    that occur (test: r0c :: nat => nat);
  - Graph.layered_graph_input is available under a Graph: Pair_Graph_Specs parent (DDFS imported).
- R0-0 verification: full library build `isabelle build -D . -j 3` (isabelle-home-hk) exit 0,
  31 min; all sessions incl. Hungarian_Method, Use_Orlins_Algorithm, Spanning_Trees,
  Micali_Vazirani, Hopcroft_Karp. Disk: 5.9 GB free afterwards.
- Renamed patch saved: Hopcroft_Karp/backups/integration/Graph_ADT_Split_capitalised.patch
  (775 lines, md5 fed53843071eef91af9f8a8fd7a6e2fa); re-applied to copies of the dacfcfc
  pre-images it reproduces the six verified files byte for byte.
- R0 DONE. Next: R1 (Hopcroft_Karp_Top_Loop), on the user's go-ahead.

## Restyle Gate R1 (coder)

Phase A (paste only, no repairs). Pasted: new theory Hopcroft_Karp/Hopcroft_Karp_Top_Loop.thy (candidate verbatim; jEdit buffer re-encodes symbols, disk copy now holds unicode), HK_Phase.thy import changed to Hopcroft_Karp_Top_Loop, HK_Example.thy replaced by candidate (disk == candidate).
Result: Hopcroft_Karp_Top_Loop: 12 errors + 4 commands stuck running (lines 26, 28, 37 diverging auto/fastforce; line 147 knock-on). HK_Phase and HK_Example: not processable (blocked on the unfinished import; 0 errors, 2022 / 224 commands unprocessed).
Causes: (1) locale Hopcroft_Karp_Loop header: fresh type variable for matching_abstract (needs `where lookup = lookup for lookup :: ...` header; tested in scratch: variant LB typechecks); (2) closers at lines 26/28/37 time out in REPL. R1_Scratch.thy (neutral scratch, reset to stub, not in ROOT) used for REPL probes.

Phase B (coder). Applied Fix 1 (locale header with where lookup = lookup / for lookup) and the replacement proof of augmenting_path_disjoint_preserved. Result: header OK, lemma OK after one extra repair (3a): the membership step hd p/last p/hd q/last q (by auto simp: matching_augmenting_path_def) diverged; replaced by a proof- block with p <> [] and q <> [] via (intro notI) (simp add: matching_augmenting_path_def), then (simp_all add: hd_in_set last_in_set); REPL-gated, 0.03s; final ultimately step 0.4s. Sledgehammer not used (non-arithmetic trivial list facts; decomposition in REPL instead).
First-time failures (3b, not repaired): Hopcroft_Karp_Top_Loop line 132 (impl_same, Let_def loops, 667s+ running), lines 218, 228, 240, 243, 305, 307, 337 (errors), 282, 325, 341 (non-terminating). Top_Loop: 7 errors + 4 non-terminating; HK_Phase, HK_Example: blocked (unprocessed), 0 errors reported. Scratch_R1.thy used for REPL probes (reset to stub, saved, ASCII). All three theory files ASCII on disk.

Phase C (coder). Applied all 11 phaseC items to Hopcroft_Karp_Top_Loop.thy. Two needed fallbacks: (a) foldl_augment_props Cons case: the plan's first step (auto dest: matching(1) graph_matching_finite) left finite (matching_abstract M); replaced by gm: graph_matching ... (rule matching(1)), then finite/matching via (auto intro: graph_matching_finite), and the card step uses new_matching_plus_one[of "matching_abstract M" p] with (auto simp: augment(2)); (b) call_1_terminates closing step: auto left a nat goal needing 0 < length (phase ?M); fixed with using length_greater_0_conv[of "phase ?M", THEN iffD2], (auto ... simp del: length_greater_0_conv; presburger). REPL-gated, no sledgehammer needed.
Status: Top_Loop 0 errors, running 0, unprocessed 0 (6.4s). HK_Phase 0 errors, running 0, unprocessed 0 (12.8s). HK_Example 9 errors (root: the two global interpretations hk_exec line 80 and hk line 103 closers; rest cascade). Not repaired (first-time). All three files ASCII, 0 sorry; Scratch_R1.thy reset to stub.

Phase D (coder). Applied sections 1-3 of phaseD_fixes.md to HK_Example.thy, section 4 for hopcroft_karp_correct. Two repairs beyond the files: matching_contract closer (auto split graph_matching) -> using mate_invarD mate_empty_props by simp_all (REPL-gated); phase_contract_complete (hk_phase_complete carries a hk_input G vs X Y premise, so the exists-premise must be opened) -> proof- with assume/obtain X Y/ (rule hk_phase_complete) (use mi ex in simp_all add: ugraph_abs_rbt_UG_of). Section 4 text worked unchanged.
Final: Top_Loop, HK_Phase, HK_Example all 0 errors, running 0, unprocessed 0; no sorry; ASCII on disk; Scratch_R1.thy reset to stub. Values: hk_edges demo = [(0,3),(0,4),(1,3),(1,5),(2,4),(3,0),(3,1),(4,0),(4,2),(5,1)]; hk_phase demo Leaf = [[4,0],[3,1]]; inorder hopcroft_karp demo = [(0,3),(1,5),(2,4),(3,0),(4,2),(5,1)]. export_code to SML succeeded.

## Restyle Gate R1 (orchestrator verification, 2026-10-11)

GREEN. Hopcroft_Karp_Top_Loop (new; HK_Top_Loop removed from ROOT and disk, copy in
backups/restyle-R0/), plus the R1 consumer patch of HK_Example and the import of HK_Phase.
- Process: one-shot (tmp/coder/R1/) -> coder Phase A report (locale type-variable link, three
  divergent calls) -> orchestrator fixes (Phase B) -> 11 first-time failures reported ->
  orchestrator one iteration (Phase C; 9 of 11 passed as written; coder fallback repaired the
  termination arithmetic (presburger) and the foldl Cons case) -> HK_Example closers reported
  -> orchestrator iteration (Phase D: contract lemmas in clause shape + simp closers, as in
  BFS_Example; coder fallback repaired matching_contract (simp_all) and
  phase_contract_complete (obtain X Y first)).
- Lessons: (1) `locale L = P + fixes ...` does not link 'v of P; use `P where lookup = lookup
  for lookup :: ...`. (2) A return update that is the identity makes `_holds_ret_1` an
  identity intro rule; `intro!: invar_holds_intros` then loops: use `intro:` in the loop and
  termination lemmas. (3) `graph_augmenting_path` is an abbreviation (conjunction): auto splits
  goals before rules apply; use contract lemmas as conditional simp rules or `dest:`.
  (4) Goals of an interpretation proof contain the raw locale terms; fold the `defines`
  constants with `<c>_def[symmetric]`. (5) A theory created through I/Q open_file is saved in
  unicode: create new theories on disk first (ASCII) and open them.
- Checks: PIDE 0 errors / 0 running / 0 unprocessed on Hopcroft_Karp_Top_Loop, HK_Phase,
  HK_Example; batch build exit 0 (twice, after the layout fixes); no sorry/metis/smt/meson;
  `apply` only in the DFS/BFS templates (induct x2, loop lemma x2, final lemma, global
  interpretation); no brace blocks; ASCII. Statements as in the one-shot plus
  `finite_ugraph_abs` (orchestrator, Phase C). Demo values unchanged; export_code succeeds.
- Layout fixes by the orchestrator via I/Q: line 1 indentation, five `by` moved to their own
  line, one over-indented `by`.
- Measurements (style_stats, Hopcroft_Karp_Top_Loop): 30 lemmas; single by 66.7%; median
  proof length 2; labelled facts 0.07/lemma; [OF] 0.30/lemma; named assumptions 0; attribute
  53.3%; by/using opening a line 100%/100%; record 1; function (domintros) 1 + impl; 1
  invariant family complete (props, intro, 2 branches, holds); locale_struct: three locales,
  no interpretation.
- Snapshot: backups/restyle-R1/. Scratch_R1.thy (stub, not in ROOT) to be deleted at the next
  jEdit restart.

## Restyle Gate R2 (coder)
- Phase A: Disjoint_Paths_Search.thy opened unchanged (identical to the one-shot); HK_Search.thy
  replaced by the candidate (disk equals candidate, ASCII).
- Disjoint_Paths_Search: NOT processable as pasted. Non-terminating commands: impl_same,
  invar_explored_closed_props, invar_within_graph_holds_upd1/upd2, invar_paths_sound_holds_upd1,
  invar_paths_disjoint_holds_upd1, invar_explored_closed_holds_upd2, correct_3_ret_1. Failing:
  domintros (case order swapped), Disjoint_Paths_Search_axiom_props, invar_blocked_avoided_holds_upd2,
  initial_state_props; invar_1_holds fails on lemma order (needs within_graph upd lemmas).
  HK_Search / HK_Phase / HK_Example: unprocessed (blocked behind the import).
- Diagnosis in the scratch theory (Hopcroft_Karp/Scratch_R2.thy, now reset to a stub): a fully
  clean variant (0 errors, 0 running) with REPL-verified replacements, saved as
  /home/llm/.claude/jobs/1269a04e/tmp/coder/R2/Disjoint_Paths_Search_probe_clean.txt and the diff
  probe_fixes.diff. Nothing of this was written to Disjoint_Paths_Search.thy.
- Phase B (approved): probe_fixes applied to Disjoint_Paths_Search.thy as a whole-buffer write (disk equals
  R2/DPS_final_expected.thy = probe_clean with theory name Disjoint_Paths_Search and no iq.iq; ASCII).
  Status: Disjoint_Paths_Search 0 errors / 0 running / 0 unprocessed (3 warnings), no sorry;
  HK_Search 0/0/0 (304 finished); HK_Phase 0/0/0 (10 warnings); HK_Example 0/0/0 (4 warnings).
  Demo values unchanged: [(0,3),(0,4),(1,3),(1,5),(2,4),(3,0),(3,1),(4,0),(4,2),(5,1)];
  [[4,0],[3,1]]; [(0,3),(1,5),(2,4),(3,0),(4,2),(5,1)]; export_code hopcroft_karp in SML succeeds.
  Scratch_R2.thy is a stub; no REPLs open.

## Restyle Gate R2 (orchestrator verification, 2026-10-11)

GREEN. Disjoint_Paths_Search (new; generic search loop, contract of the search step as
assumptions of the definitions locale), plus HK_Search importing it (its two generic walk
lemmas moved).
- Process: one-shot -> coder Phase A (12 failures; the coder isolated each in a scratch copy and
  REPL-verified a replacement) -> orchestrator reviewed and accepted them as its one iteration
  (proof-only changes, invar_1_holds moved after the invar_within_graph family) -> applied.
  Orchestrator tidy-up via I/Q: redundant `subsetD` removed from three dest lists (duplicate-rule
  warnings), two blank-line glitches. 0 warnings remain.
- Lessons: `someI_ex` needs an explicit predicate (`someI[of "..."]`); with goal_cases the
  domintros cases come in the order of the function's patterns (None before Some); the
  `_holds` lemma of an invariant must come after the families it relies on; `fastforce` loops
  more readily than `auto` + one `blast dest:` step.
- Checks: PIDE 0 errors / 0 warnings / fully processed for Disjoint_Paths_Search, HK_Search,
  HK_Phase, HK_Example (coder; Disjoint_Paths_Search re-checked by the orchestrator after the
  tidy-up); batch build exit 0; no sorry/metis/smt/meson; `apply` only in the DFS/BFS templates
  (induct, 9 loop lemmas, 3 final lemmas); ASCII; statements as in the one-shot. Demo values
  unchanged, export_code succeeds.
- Measurements (style_stats, Disjoint_Paths_Search): 70 lemmas; single by 77.1%; median 2;
  labelled 0.10/lemma; [OF] 0.37/lemma; named assumptions 0; attribute 78.6%; by/using opening a
  line 100%/100%; 7 invariant families, all complete (props, intro, 3 branches, holds);
  locale_struct: two locales, no interpretation; imports Pair_Graph_Specs, Set2_Addons, DDFS (D2).
- Snapshot: backups/restyle-R2/.

## Restyle Gate R3 (coder)

Phase A. Alt_BFS_Bipartite.thy pasted unchanged (equals R3/Alt_BFS_Bipartite.thy); HK_Phase.thy patched with the
four R3 edits (import, bipartite_matching_input_phase, two [OF ...] lists), saved. No theory imports Hopcroft_Karp
any more (old Hopcroft_Karp.thy only on disk, not in ROOT).
- Alt_BFS_Bipartite as pasted: NOT processable. Root failures (PIDE + REPL): line 84 (case 1 of
  copies_walk_alt_walk, auto/alt_vwalk_bet_append_3 cannot guess p1/p2); line 125-127 (copies_lev_zero, third
  moreover: x in dVs G lost); line 150-151 (copies_walk_from_odd, final auto); line 161 (VisO_copies_dVs, fastforce
  non-terminating, 1500 s+); 222 (G_eq_undirected_edges, auto needs subset_iff); 233 (vwalk_G_iff_path dir 1, G
  rewritten inside dVs); 240 (fastforce, loops; auto works); 265/268 (augmenting_path_alt_walk, auto);
  271 (auto loops); 310 (copies_walk_label_side final auto loops); 329 (blast loops; auto works);
  391 (fastforce loops); 433 (blast loops); 56 (force, 20-25 s, REPL timeout).
  Lines 88, 91, 92, 97, 130, 133, 144-154 and the rest are cascades.
- HK_Phase, HK_Example: blocked (unprocessed) behind the hanging import.
- Scratch diagnosis: Scratch_R3.thy (copy of the theory + iq.iq) repaired step by step with REPL-verified
  replacements: fully clean (0 errors, 0 running, 0 unprocessed, 2 warnings, ~30 s, dominated by line 56 force).
  Candidate saved: R3/Alt_BFS_Bipartite_candidate.thy (ASCII, no iq.iq), diff R3/Alt_BFS_Bipartite_fixes.diff.
  Consumer check with copies Scratch_R3P (HK_Phase importing Scratch_R3) and Scratch_R3E (HK_Example): both 0 errors
  (HK_Phase 10 warnings, HK_Example 4 warnings) -> bundle lemma / argument order of the patch is correct.
- Scratch_R3, Scratch_R3P, Scratch_R3E reset to stubs; no REPLs left open.

Phase B (orchestrator approved). Candidate (R3/Alt_BFS_Bipartite_candidate.thy) written whole into the buffer, then
three DFS/BFS-style replacements from R3/phaseB_fixes.md, each REPL-gated in a Scratch_R3 copy first:
copies_dag_vtx_dVs (auto simp: dVs_eq elim!: copies_dag_cases intro: rev_image_eqI, 0.5 s),
augmenting_path_alt_walk (moreover/ultimately version, ~2.4 s), copies_walk_augmenting (~2.6 s): all three stuck.
Removed dVsI / dVsI(1) from the two intro lists in Alt_BFS_Bipartite (lines 205, 245): duplicate-rule warnings gone, proofs pass.
Final: Alt_BFS_Bipartite 0 errors / 0 warnings / 0 running / 0 unprocessed (8 s); HK_Phase 0 errors / 10 warnings (all
pre-existing; two are duplicate dVsI intros at lines 215, 239, not touched); HK_Example 0 errors / 4 warnings.
Demo values unchanged: [(0,3),(0,4),(1,3),(1,5),(2,4),(3,0),(3,1),(4,0),(4,2),(5,1)]; [[4,0],[3,1]];
[(0,3),(1,5),(2,4),(3,0),(4,2),(5,1)]; export_code hopcroft_karp in SML ok. ASCII, no sorry/smt/metis.
Scratch_R3/R3P/R3E are stubs; no REPLs open. Snapshot: backups/restyle-R3/.

## Restyle Gate R3 (orchestrator verification, 2026-10-11)

GREEN. Alt_BFS_Bipartite (from Hopcroft_Karp.thy, which is removed; copy in
backups/restyle-R0/), plus the HK_Phase consumer patch (bundle lemma
bipartite_matching_input_phase, two [OF] lists shortened).
- Process: one-shot -> coder Phase A (13 failures, each isolated in a scratch copy with a
  REPL-verified repair) -> orchestrator iteration: candidate accepted as base, three proofs
  replaced by DFS/BFS-style versions (copies_dag_vtx_dVs single call instead of a 20 s force;
  augmenting_path_alt_walk and copies_walk_augmenting as moreover/ultimately chains) - all three
  stuck. dVsI removed from two intro lists (duplicate-rule warnings).
- Checks: PIDE 0 errors on Alt_BFS_Bipartite (0 warnings), HK_Phase, HK_Example; batch build
  exit 0; no sorry/metis/smt/meson/apply; ASCII; statements identical to the one-shot; demo
  values unchanged, export_code succeeds; nothing imports the old theory.
- Measurements (Alt_BFS_Bipartite vs old Hopcroft_Karp.thy): 23 lemmas (24); single by 47.8%
  (16.7%); median proof length 9 (15); labelled 0.57/lemma (3.50); [OF] 2.09/lemma (3.00);
  named assumptions 0 (0.96); by/using opening a line 100%/100% (13.5%/38.3%). Below the DFS/BFS
  targets: a purely mathematical theory without loop machinery; [OF] mostly from
  `valid_alt_BFS_DAG_props[OF \<open>BFS_axiom\<close> ...]` notes. Group-level figures at R6.
- Snapshot: backups/restyle-R3/.

## Restyle Gate R4 (coder)

Phase A. Both one-shot files opened (open_file), unchanged on disk. Hopcroft_Karp_Subprocedures never finishes in the
buffer: line 69 (mate_Vs_iff, fastforce) diverges (60+ s, running 1, unprocessed 649, errors 0 reported); Hopcroft_Karp_Example
imports it and cannot be processed. The real files were NOT edited (Phase A). The runaway command in the Subprocedures
buffer is still spinning; it needs a buffer edit (Phase B) to stop.
Diagnosis in Scratch_R4.thy (copy with iq.iq, failing steps replaced one after another by REPL-verified candidates) and
Scratch_R4E.thy (Example importing Scratch_R4). 27 Subprocedures failures + 3 Example failures, all with REPL-verified
candidates. With all candidates applied: Scratch_R4 0 errors / 0 running / 0 unprocessed (14 s total, slowest step
sorted_wrt_mono_rel ... force, 4.6 s); Scratch_R4E 0 errors / 0 running / 0 unprocessed, demo values [[3,1],[4,0]],
mate map [(0,3),(1,5),(2,4),(3,0),(4,2),(5,1)], export_code ok, hopcroft_karp_correct_1/2 print as required.
Candidates (ASCII, no sorry/metis/smt, no iq.iq): R4c/Hopcroft_Karp_Subprocedures_candidate.thy,
R4c/Hopcroft_Karp_Example_candidate.thy, diffs R4c/Subprocedures_fixes.diff, R4c/Example_fixes.diff (under
/home/llm/.claude/jobs/1269a04e/tmp/coder/). Statement-level changes inside the candidate: (a) phase_search defines two more
constants (code equations), (b) three lemmas phase_search_correct_1/2/3, (c) hopcroft_karp_phase_unfold and the
phase_paths_* proofs state the search run as phase_search.Disjoint_Paths_Search blocked copies_graph (...) (...initial_state copy_roots).
Scratch_R4/Scratch_R4E are stubs; no REPLs open.

## Restyle Gate R4 (coder, Phase B)

Both Phase A candidates written whole into the real buffers (this stopped the runaway line-69 command): Subprocedures and
Example each 0 errors. Then B1-B5, each gated in a Scratch_R4 copy (B3 and B5 also in the REPL), written to the real buffer
after each success:
- B1 merged lemma search_step (inside the layered context, IDFS_impl_rbt_props and outer search_step removed): stuck, all
  seven shows as given; `thm search_step` prints layered_graph_input first, then the five premises, then the call.
- B2 `qed (fact search_step)+` in phase_search: stuck (primary).
- B3 phase_search_proofs: primary (auto with simp: Disjoint_Paths_Search_axiom_def ...) failed in the REPL (auto leaves
  `x : set (phase_roots ...) ==> x : dVs (set (copies_edges ...))`, from_list_correct(4) rewrites first); alternative stuck
  (`using phase_search.Disjoint_Paths_Search_axioms copies_graph_layered copy_roots_in_graph blocked_copies_props(1,2)
  by (auto intro!: Disjoint_Paths_Search_thms.intro Disjoint_Paths_Search_thms_axioms.intro simp: ...Disjoint_Paths_Search_axiom_def)`).
  Fact name phase_search.Disjoint_Paths_Search_axioms exists.
- B4 search_state abbreviation and its three uses: stuck.
- B5 one-step ending of phase_complete: stuck (blast 0.02 s in the REPL).
Final: Subprocedures 0 errors / 13 warnings / 0 running / 0 unprocessed (about 13 s, slowest step sorted_wrt_mono_rel ... force
3.6 s); Example 0 errors / 4 warnings. Demo: edges as before, first phase [[3,1],[4,0]], mate map
[(0,3),(1,5),(2,4),(3,0),(4,2),(5,1)]; export_code ok. ASCII, no sorry/metis/smt/meson; the only apply is the template
`apply unfold_locales` in Example. Backups: tmp/coder/R4b_backup/. Scratch_R4/R4E stubs; no REPLs open.

## Restyle Gate R4 (orchestrator verification, 2026-10-12)

GREEN. Hopcroft_Karp_Subprocedures (from HK_Phase + HK_Search) and Hopcroft_Karp_Example (from
HK_Example); HK_Phase/HK_Search/HK_Example deleted (copies in backups/restyle-R4-pre/ and
backups/restyle-R0/).
- Process: one-shot -> coder Phase A (27 + 3 failures, each repaired in a scratch copy with a
  REPL-verified step) -> orchestrator iteration (R4c/phaseB_fixes.md), all five stuck:
  B1 IDFS_impl_rbt_props and search_step merged into one contract-form lemma inside the layered
  context (its export is the contract clause verbatim); B2 phase_search interpretation cases 3-9
  as `qed (fact search_step)+`; B3 phase_search_proofs reuses phase_search.Disjoint_Paths_Search_axioms
  (alternative form; the primary left a goal because from_list_correct(4) rewrites first);
  B4 abbreviation search_state; B5 phase_complete ends in one step.
- Orchestrator clean-up (no-op edits, all through I/Q): simp-set entries reported as duplicate
  removed (Subprocedures 11 commands, Example 2, Top_Loop 2); from_list code-unfold lemmas in
  Example as `unfolding ...[abs_def] by ...` (removes two fixed-type-variable warnings).
- Statement-level changes (approved): phase_search defines disjoint_paths_search_impl_rbt,
  disjoint_paths_search_initial_state, disjoint_paths_search_rbt (code equations); lemmas
  phase_search_correct_1/2/3; hopcroft_karp_phase_unfold states the run as `paths search_state`;
  hopcroft_karp_correct_1/2 folded in four comma-separated steps. Contract lemmas matching, augment,
  phase_sound/disjoint/complete unchanged.
- Checks: PIDE 0 errors on all five theories, fully processed; warnings: Top_Loop 3 and
  Subprocedures 1 'Ambiguous input' (library notation clash: \<oplus> is both Matching.symmetric_diff
  and Vertex_Walk.vwalk_join), Subprocedures 1 code-equation notice on the phase_bfs
  re-interpretation (partially applied union_rbt); all others 0. Batch build
  `isabelle build -d . Hopcroft_Karp` exit 0 (26 s). No sorry/metis/smt/meson; only apply is the
  template `apply unfold_locales` in Example; ASCII. Demo: adjacency_edges 10 pairs; phase 1
  [[3,1],[4,0]]; final mate map [(0,3),(1,5),(2,4),(3,0),(4,2),(5,1)]; export_code ok;
  hopcroft_karp_correct_1: hopcroft_karp_axiom_rbt G vs ==> max_card_matching (ugraph_abs_rbt G)
  (mate_matching (current_matching (hopcroft_karp_run_impl G vs))).
- Measurements (SUB = Subprocedures, EX = Example, OLD = HK_Phase+HK_Search+HK_Example):
  lemmas 50 / 9 / 71; single by 64.0% / 100% / 50.7%; median proof length 2 / 1 / 4;
  labelled 0.00 / 0.00 / 1.30 per lemma; [OF] 1.00 / 0.11 / 1.39 per lemma; mean isar proof
  14.8 / - / 17.8 lines. SUB meets the DFS/BFS targets except [OF] (target <= 0.6).
- Snapshot: backups/restyle-R4/ (five theories + ROOT).

## Restyle Gate R5 (orchestrator verification, 2026-10-12)

GREEN, no further edits. Hopcroft_Karp_Example was written in R5 form in the R4 one-shot and
polished at the R4 gate (from_list code-unfold lemmas as single unfolding/by proofs; duplicate
simp entries removed). Plan R5 items: code bridges with single-by proofs; composition by one
global_interpretation hopcroft_karp ... defines (apply unfold_locales, BFS_Example form); rule-7
context with interpretation hopcroft_karp_proofs and lemmas hopcroft_karp_correct_1/2 [folded ...];
demo_bipartite (2 lines), demo_axiom, demo_max = hopcroft_karp_correct_1[OF demo_axiom]; export_code.
Gate R5: statements match plan section 0.1 (premise hopcroft_karp_axiom_rbt G vs; max_card_matching
resp. mate_invar of current_matching (hopcroft_karp_run_impl G vs)); export_code ok; demo values as
R4; locale_struct: one global interpretation with defines (as BFS_Example) plus the rule-7 local
interpretation in an assumes-context. PIDE 0 errors / 0 warnings; batch build exit 0 (the R4 gate
build). Metrics: 9 lemmas, 100% single by, median 1, [OF] 0.11. Snapshot: backups/restyle-R4/
(identical files).

## Restyle R6 close-out (orchestrator, 2026-10-12)

DONE. Restyle campaign R0-R6 complete.
- Group measurement (style_stats.py; NEW = the five restyled theories, OLD = the five
  pre-restyle theories of backups/restyle-R0): lemmas 182 (108); single by 69.2% (38.0%);
  median proof length 2 (8); labelled 0.12 (2.29); [OF] 0.74 (2.10); named assumptions 0.00
  (0.51); elim!/intro! 0.30 (0.00); by/using opening a line 100%/100% (17%/35%);
  proof - / proof ( 0/0 (41/52); attributes 45.6% (6.5%); named-theorem bundles 14 (0);
  invariant families 1 + 7 (0). Missed targets: [OF] <= 0.6, elim!/intro! >= 0.8,
  attributes >= 60%; reasons in Hopcroft_Karp_Restyle_Plan.md section 0 (concentrated in
  Alt_BFS_Bipartite and Subprocedures). Full output: backups/restyle-R6/r6_stats.txt,
  r6_pertheory.txt, r4r5_locale_struct.txt.
- One whitespace fix through I/Q: Disjoint_Paths_Search `proof (cases ...)` -> `proof(cases ...)`.
- Coordination: no RO.* references and no interim read-only theory remain (R0-0
  integration confirmed). For integration: layered_dgraph / layered_graph_input (DDFS.thy)
  and layered_dgraph_cong (Subprocedures) belong in the graph library (D2).
- Editor backups Hopcroft_Karp/*.thy~ removed. Scratch_R1..R4E stubs remain (open in jEdit;
  delete after a jEdit restart).
- Hopcroft_Karp_Plan.md status block and the memory file updated.
- Final checks: PIDE 0 errors on all five theories (warnings: Top_Loop 3 and Subprocedures 1
  'Ambiguous input' from the library notation clash of \<oplus>, Subprocedures 1 code-equation
  notice; others 0); batch build `isabelle build -d . Hopcroft_Karp` exit 0 (25 s).
- Snapshot: backups/restyle-R6/ (five theories, ROOT, both plans, measurement outputs).
- Open: D2 (DDFS import in Disjoint_Paths_Search); optional polishing of Alt_BFS_Bipartite;
  commit (user decision).

## D2 removed: DFS/DDFS split (orchestrator, 2026-10-12)

User: "it should not import ddfs. split dfs". Way (i) of plan D2, in the HK copy (MV theories
edited by user decision; text moved verbatim, no proof changed; all theory edits via I/Q, new
theories written to disk in ASCII first).
- New Micali_Vazirani/Layered_Digraph.thy (imports Vwalk, Pair_Graph_Specs): dpath, dpath_bet,
  layered_dgraph (+ I/finite/level/base/D/E/no_self_loop), Pair_Graph_Specs.layered_graph_input
  (+ I/D/E), moved from DDFS.thy. DDFS, IDFS, MV Top_Loop import it.
- IDFS.thy imports DFS_Avoid Layered_Digraph; locale DDFS_layered and sublocale
  DDFS_layered <= DDFS (old IDFS.thy 505-746) moved to the start of DDFS_Interpretation.thy.
- New Micali_Vazirani/IDFS_Example.thy (imports IDFS, Pair_Graph_RBT): global_interpretation
  idfs: DFS_avoid (find_idfs, av_found_rbt, neighbourhood_idfs, avoid_impl_rbt,
  avoid_initial_rbt, vset_of_list_rbt) and its code lemmas, moved from DDFS_Example, which now
  imports it. Subsumption: idfs registers the shared Pair_Graph_Specs instance first, so
  ddfs_diamond.Graph.* is undefined: the four unused defines neighbourhood/add_edge/
  delete_edge/from_list_diamond dropped; ddfs_diamond_code folds neighbourhood_idfs_def (as
  ddfs_chain_code). DDFS_Example demos unchanged (([0,1,3],[0,2]), ([3],[3]), ([2,3],[2]),
  Some [0,2,3], Some [0,1,3], Some [0,1,2,3]); export_code ok.
- MV ROOT: + Layered_Digraph, + IDFS_Example.
- HK: Disjoint_Paths_Search imports Micali_Vazirani.Layered_Digraph; Subprocedures imports
  Micali_Vazirani.IDFS_Example (DDFS_Example and IDFS dropped). Import closure: no HK theory,
  nor IDFS, IDFS_Example, DFS_Avoid, MV Top_Loop, reaches DDFS.
- Checks: `isabelle build -d . Hopcroft_Karp` exit 0 (Micali_Vazirani rebuilt 53 s,
  Hopcroft_Karp 25 s); only Hopcroft_Karp depends on Micali_Vazirani. jEdit restarted on the new
  heap (pid changed; port 8767, token hk): all five HK theories 0 errors, warnings as before;
  HK demo unchanged; ASCII.
- Integration patch (MV checkout, patch -p1): backups/integration/DFS_DDFS_split.patch
  (md5 2d667dfe...), dry run clean on /media/llms/Isabelle-Graph-Library-Micali-Vazirani.
- Snapshots: backups/dfs-split-pre/ (before), backups/dfs-split/ (after).
- Housekeeping: Scratch_R1..R4E stubs and jEdit autosaves (#HK_*.thy#, identical to backups)
  deleted; Micali_Vazirani/*.thy~ removed.
