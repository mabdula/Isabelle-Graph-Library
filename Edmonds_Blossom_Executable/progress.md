# Progress log: executable Edmonds blossom algorithm

Plan: `Blossom_Executable_Plan.md` (one-shots live only there). I/Q: port 8768, token `blossom`,
home `/media/llms/isabelle-home-blossom`, logic `Blossom` (jEdit pid 3144040, started
2026-10-24 14:31). Baseline `isabelle build -b Blossom` green (2026-10-24).


## Phase 1 (Graph_Matching_Specs)

- Created `Graph_Matching_Specs.thy` through I/Q (open_file view + create_if_missing, content = one-shot extracted by script; the buffer text equals the one-shot up to glyph display).
- Recon (a): the locale expression `Mate_Map: Map ...` + `Mate: matching_augmentation ...` loads without error; `Mate_Map.map_update` (`mate_invar ?m ==> mate_lookup (mate_update ?a ?b ?m) = (mate_lookup ?m)(?a |-> ?b)`) and `Mate.augmentation_correct(1-3)` exist.
- Recon (b): `thm` of Mate.M_def', Mate.invar_matchingD(1-5), Mate.invar_matchingI, Mate.symmetric_buddiesI, Mate.no_self_loop_buddyI, Graph.finite_vertices (needs graph_inv, finite_graph, finite_vsets), Graph.from_list_correct(1-5), Graph.digraph_abs_def all exist with the shapes used in the one-shot (checked in the REPL).
- Repaired steps (2; statements unchanged, no plan changes):
  1. `Vs_ugraph_abs` (second `show`): `fastforce simp: ugraph_abs_def Vs_def dVs_eq` did not terminate. repl_sledgehammer (30 s) returned "No proof found". Replaced by a structured proof in the REPL: `obtain u v` from `dVs_eq`/`image_iff`, instantiate `graph_inputD(4)[OF assms, of u v]` to get `(x,w)`, then `ugraph_abs_def`, `Vs_def`. REPL-gated before insertion.
  2. `neighbour_list_nonempty_iff` (third `have`): `fastforce simp: Vs_def dblton_graph_def insert_commute` did not terminate. Replaced by the same style of proof (`proof` with two directions; `obtain e`, `obtain a b where e = {a,b}` from `dblton_graph_def`, `insert_commute`). The REPL could not be initialised at that lemma (earlier hanging command), so this step was written directly and checked in the buffer (finished, no timing warning); no sledgehammer call for this one.
- Final check: get_document_info (wait, errors): is_processed true, running 0, unprocessed 0, error_count 0, 5 warnings (duplicate intro/simp rule notes only); get_sorry_positions: none; no sorry/oops/metis/smt/meson; iq.iq removed from imports and re-checked.

## Gate 1 (orchestrator, 2026-10-24)
- PIDE recheck: is_processed, 0 errors, 0 running/unprocessed (5 warnings: duplicate rules).
- to_ascii.py: 221 glyphs converted, 0 non-ASCII left. Diff against the one-shot: only the
  two repaired proofs (`Vs_ugraph_abs`, `neighbour_list_nonempty_iff`); statements unchanged.
- ROOT: `theories Graph_Matching_Specs` added. `isabelle build -o document=false
  Blossom_Executable`: finished (exit 0).
- No sorry/oops/metis/smt/meson. `isabelle ai_provenance -s -t`: exit 0, 294 lines ai (100%).
- Snapshot: backups/Graph_Matching_Specs.thy.2026-10-24_gate1_green (md5 48059ec7...).
- Note: the coder wrote the second repair without a REPL gate (REPL blocked by the first
  hanging step); the buffer check was clean.

## Phase 2 (Edmonds_Blossom_Top_Loop)

- Created `Edmonds_Blossom_Top_Loop.thy` through I/Q (open_file view + create_if_missing, content = the one-shot extracted by script; file exists on disk, 13778 bytes).
- Recon: not completed (prover wedged, see below). From the first processing: the locale header, the function/partial_function declarations and the definitions up to `Edmonds_Blossom_Loop_impl_same` check.
- PLAN CHANGE 1 (locale header, applied in the buffer, marked with a comment): `locale Edmonds_Blossom_Loop = Graph_Matching_Specs where lookup = lookup` with `for lookup :: ...` failed ("Type unification failed ... cannot generate coercion from 'a to 'mate"): the type variable `'mate` written in `fixes` is not the one of the imported parameters. Fix: `locale Edmonds_Blossom_Loop = Graph_Matching_Specs where lookup = lookup and mate_empty = mate_empty for lookup :: "'adjmap => 'v => 'vset option" and mate_empty :: 'mate +`. The contract and the rest are unchanged. Side effect: the positional parameter order of the locale ends `... vset_to_list lookup mate_empty G vs augmenting_path_search`; later phases must use `where` (named) instantiation, not positional.
- BLOCKER: the lemma `Edmonds_Blossom_Loop_impl_same` (the one-shot proof `auto simp add: Edmonds_Blossom_Loop_impl.simps Edmonds_Blossom_Loop.psimps split: option.splits`) did not terminate. Cause (not yet confirmed in the REPL): `Edmonds_Blossom_Loop_impl.simps` is an unconditional equation whose right hand side contains the left hand side again, so `simp` loops (the "twin lemma" risk of the plan). After that the Poly process of the jEdit instance (pid 3144639, ~1 h old) went into a state where its 8 GC threads spin at 100% for 15+ minutes and all ML threads sleep: no edit reaches PIDE any more (document version stays at the state after PLAN CHANGE 1, `running 1, unprocessed 297, finished 44`), `repl_list` and `repl_init_from_source` time out, and the other theory (Alternating_Forest_Search, port 8768, same Poly) is frozen in the same way (unprocessed 243, running 1, unchanged). I was not allowed to restart jEdit, so I stopped here.
- State of the buffer (not yet in PIDE): imports `Graph_Matching_Specs iq.iq` (temporary, must be removed at the end) and the proof of `Edmonds_Blossom_Loop_impl_same` temporarily replaced by `by fail` (to unblock processing); REPL `c2a` may have been half-created by the hanging `repl_init_from_source` call (could not be listed or removed).
- Planned repair of `Edmonds_Blossom_Loop_impl_same` once the prover runs again: the one-step form, `proof(induction rule: Edmonds_Blossom_Loop.pinduct[OF assms])`, then per case `subst Edmonds_Blossom_Loop_impl.simps`, `subst Edmonds_Blossom_Loop.psimps` and `split option.splits`, never `simp` with `Edmonds_Blossom_Loop_impl.simps` as a rewrite rule (REPL-gated, sledgehammer first).

## Phase 3 (Alternating_Forest_Search)

- Created `Alternating_Forest_Search.thy` through I/Q (open_file view + create_if_missing, content = one-shot extracted by script; jEdit shows glyphs). `iq.iq` added temporarily as last import (REMOVE before finishing).
- Recon (a): the abstract section checks as written except the type of `flabel`: in `search_invars` the label type of `flabel` was generalised to a second type variable (`'b`), so `compute_alt_path_dom (ex, par, flabel)` and `compute_alt_path ex par flabel` were ill-typed in `search_invars_complete`. PLAN CHANGE 1: type annotation `search_invars :: "'a set set => ('a => 'a option) => ('a => ('a * label) option) => bool"` (comment in the theory). With it `search_invars_if1`, `search_invars_if2_sound`, `search_invars_complete` check (the first two checked even before).
- Repair 1: `forest_edges_update` (cases 1, 2 of the second direction): `auto ... intro!: exI[of _ x] exI[of _ w]` failed with "Unification bound exceeded". Added helper lemma `forest_edgesI` (`unfolding forest_edges_def by blast`, REPL-gated) and used it with `simp add: insert_commute`. Gated in the REPL (a variant with `auto` timed out; the variant with `forest_edgesI` ran in 0.02 s).
- Found (locale): the identifier `es` is a global constant (`es :: 'a set => 'a set set`), so the patterns `(v, w) # es` in the loop definitions fail to parse. PLAN CHANGE 2: variable `es` renamed to `rest` throughout (names only).
- Found (locale): `M :: 'mate` in `fixes` is not linked to the inherited mate type (type variable `'a`). See PLAN CHANGE 3 below.
- Tooling incident: the 8768 prover wedged (Poly at 800% CPU) during processing of cascaded errors; the orchestrator restarts jEdit. Work resumes after the restart.

## Incident 1 (orchestrator, 2026-10-24 15:38): prover wedge, restart
- Symptom (reported by the Phase 2 coder): Poly of the 8768 instance (pid 3144639) with GC
  threads at 100%, no edit reached PIDE, REPL calls timed out; both open theories frozen.
- Trigger: `Edmonds_Blossom_Loop_impl_same` one-shot (`auto simp add: ..._impl.simps ...`).
- Recovery: disk theories copied to ~/.claude/jobs/d07b4540/tmp/restart1/; both buffers saved
  via I/Q save_file (worked without the prover); kill -9 of the 8768 java, its wrapper, both
  poly processes and the REPL python process (all USER_HOME=isabelle-home-blossom; other
  instances untouched); jEdit perspective moved aside (perspective.xml.restart1) so that no
  buffer is reopened; relaunched (java pid 3227296, port 8768).
- Plan Amendment A: A0 REPL-first copying of one-shots, A1 'mate type link in locale headers
  (applied to the one-shots of Phases 2, 4, 5), A2 twin lemma by one-step subst. coder.md §1
  updated. Both coders resumed with the new rule.
- 15:40 relaunch had no prover: modal "Autosave File Found" for $USER_HOME/#Scratch.thy#
  (6 bytes "i want", kept in tmp/restart1/autosave_Scratch.thy.txt) blocked jEdit startup.
  Removed it, killed the prover-less instance, relaunched 15:57 (java 3231596, poly 3232086);
  Graph_Matching_Specs re-checked in PIDE: 463 finished, 0 errors. Scratch theories now go to
  `.claude/scratch_<coder>/` in the repository (I/Q read roots).
- BLOCKER 2 (2026-10-24): after the first restart the 8768 jEdit had no prover (modal autosave dialog); resolved by the orchestrator at 15:57. Resumption: REPL-first replay (Amendment A0) of the one-shot body in the scratch theory `.claude/scratch_c2/Scratch2.thy`.
- Replay (Amendment A0): the one-shot body (plan version with A1, A2) was replayed in REPL c2a (scratch theory `.claude/scratch_c2/Scratch2.thy`, 84 top-level steps). Note: the REPL rejects newlines inside string literals ("unclosed string literal"), so each step was sent flattened to one line; the theory text keeps the layout. All steps passed except one; `Edmonds_Blossom_Loop_impl_same` (A2 `subst` form) passed as in the plan.
- Repaired step (1): `call_1_terminates`, `have aug` (`by (auto elim!: invar_props_elims intro: augmenting_path_search_props(1))`): auto unfolded the abbreviation `graph_augmenting_path` into three goals (path, distinct, matching_augmenting_path) instead of applying the intro rule; no sledgehammer needed (deterministic fix). Replaced by `have inv0: "matching_invar G (current_matching state)"` (from `assms(2)`, `elim!: invar_props_elims`), `inv` from `inv0` by `simp add: matching_invar_def`, and `aug` by `rule augmenting_path_search_props(1)[OF inv0 p]`. Each step REPL-gated.
- Final check (real theory, created via write_file line 1..-1 + save_file, imports `Graph_Matching_Specs` only): get_document_info (wait, errors): is_processed true, running 0, unprocessed 0, finished 354, error_count 0, warnings 0; get_sorry_positions: none; no sorry/oops/metis/smt/meson; no iq.iq. REPL c2a removed. Plan changes: A1 only (locale header). Scratch buffer `.claude/scratch_c2/Scratch2.thy` is still open in jEdit (orchestrator deletes it).

## Gate 2 (orchestrator, 2026-10-24)
- PIDE recheck: is_processed, 354 finished, 0 errors, 0 warnings.
- to_ascii.py: converted, 0 non-ASCII left. Diff against the plan's one-shot (with A1, A2):
  only the proof of `call_1_terminates` (have inv0/inv/aug); statements unchanged.
- ROOT: `Edmonds_Blossom_Top_Loop` added. Batch build exit 0. No sorry/oops/metis/smt/meson.
  ai_provenance -s: exit 0, session 566 lines ai (100%).
- Snapshot backups/Edmonds_Blossom_Top_Loop.thy.2026-10-24_gate2_green (md5 cfa407c7...).

## Phase 4 (Blossom_Shrinking_Search)

- Method (coder c4): scratch theory `.claude/scratch_c4/Scratch4.thy` (imports `Blossom_Executable.Graph_Matching_Specs Blossom.Blossom_Algo_Contraction iq.iq`), REPL `c4a`, the one-shot body (153 top-level steps, each flattened to one line) replayed with `repl_step`; the final repaired text was replayed once more from scratch in REPL `c4b` (153/153 steps ok, no step slower than 1 s) before the theory was created through I/Q (`open_file` view + create_if_missing, `save_file`). Both REPLs removed.
- Recon: `choose` is a locale in theory `choose` (`choose.choose` parses, the short name `choose` does not inside a term); `pref_suf` is a constant of locale `quot` (`quot.pref_suf`, simps conditional on `quot sel E s u`); `quot` has parameters `sel E s u` as expected; `Q.quotG G` is the abbreviation `quot_graph Q.P G - {{u}}` with `Q.P v = (if v in Vs (ugraph_abs E) - set C then v else u)` (as in recon (b)); `quot_graph_def`: `{e'. EX e:G. e' = P ` e}`; `find_pfx`, `find_pfx_nempty`, `Suc_le_length_iff_snoc2`, `induct_list012` exist; `Q.refine_works`, `Q.aug_path_works_in_contraction`, `Q.matching_quotM`, `Q.card_Vs_quotG` are used with the shapes of the one-shot (checked by replay).
- PLAN CHANGES (statements and definitions unchanged apart from names):
  - C4-1: `pref_suf` written `quot.pref_suf` in `lift_one` (library constant lives in locale `quot`).
  - C4-2: `lemma cycle_sel_choose`: `"choose (cycle_sel C)"` written `"choose.choose (cycle_sel C)"` (parse error otherwise).
  - C4-3: lemma order only: `invar_1_holds` moved after `invar_search_holds` (it uses `invar_search_holds_1` through `invar_holds_intros`).
  - A1 (locale header) already in the one-shot.
- Repaired steps (the REPL replay found 14 failing or non-terminating steps; sledgehammer was run on the first two, the others are structural repairs, each REPL-gated):
  1. `blossom_cycle_subset`: `blast` with `path_suff`, `mem_path_Vs` hit the 10 s cap; replaced by `proof(rule subsetI)` + `by (rule mem_path_Vs[OF path_suff[OF assms]])`.
  2. `dVs_quotient_edges`: `fastforce` hit the cap; repl_sledgehammer (30 s) returned "No proof found"; replaced by `proof` / `obtain a b` (`dVs_eq`, `set_quotient_edges`) / `force ... intro: rev_image_eqI`.
  3. `quotient_edges_quot_graph`: `simp add: P` rewrote the image `(%v. if ..) ` {a,b}` with `if_image_distrib` and got stuck; added the local fact `Pimg` (`simp only: image_insert image_empty P`) and used `trans[OF ab(1) Pimg...]` / `simp only`.
  4. `contract_graph_abs`: the final `simp` did not see the instance of `quotient_edges_quot_graph`; instantiated it explicitly (`e`, `cond`, `u_nin`, then `unfolding e`).
  5. `matching_pairs` (last `show`): `fastforce simp: dVs_eq Vs_def` hit the cap; repl_sledgehammer (30 s, took 159 s because the I/R server was shared) found `simp add: Collect_mono_iff Pair_Graph.dVs_subset Q.D_def Q.Vs_eq_dVs`.
  6. `contract_matching_abs`: `simp` hit the cap (same cause as 3/4) and the `blast`/`fastforce` steps were slow (3.5 s / cap); restructured with named facts `cond`, `e`, `sym`, `irr`, `u_nin`, `f1`, `f2`, `f3` and `mate_from_list[OF ...]` applied by `note`/`thus`.
  7. `last_edges_of_path_snoc2`: `induct_list012` + `auto` hit the cap; proved `EX es. edges_of_path (ys @ [a,b]) = es @ [{a,b}]` by plain induction and `cases ys`.
  8. `cycle_path_eq`: `hd (rev C) = c` by `simp add: hd_rev` failed (calculation `hd_rev`, `contraction_facts(4)`); and `cases pfx rule: rev_cases` + `auto` needed `length_Suc_conv Suc_le_eq`.
  9. `matched_to_cycle_iff`: `obtain e ... by (auto simp: quot_graph_def)` and the `False` case `auto ... split: if_splits` hit the cap (image of `if`); first by `simp only: Diff_iff quot_graph_def mem_Collect_eq singleton_iff` + `blast`, second by explicit `Pa`/`eq` facts; the `blast` for `mate_lookup N b = Some a` replaced by `rule matching_pairs(3)[OF ab(2)]`.
  10. `invar_search_holds_1`: `auto ... simp: Blossom_Shrinking_Search_upd1_def` left an unsolved goal; replaced by `proof-` with `upd1_fields(5)[OF f]`.
  11. `invar_complete_holds_1`: `auto` unfolded the abbreviation `graph_augmenting_path` into three goals; replaced by `comp` (unfolding `invar_complete_def`) + `proof(intro impI)` + `contract_complete`.
  12. `Blossom_Shrinking_Search_terminates`: `auto intro!: invar_holds_intros less ...` did not terminate; replaced by `proof(rule ..._domintros)` with the three explicit facts.
  13. `Blossom_Shrinking_Search_correct_ret_2`: `auto elim!: invar_props_elims` unfolded the abbreviation; restructured with `g`, `bs`, `moreover` and `blast`.
  14. `ret_holds` (`intro: IH(2-)` cannot use the disjunctive IH): `dest: IH(2)`. `final_state_invars`: `auto intro!: invar_holds_intros` did not terminate; replaced by `intro invar_1_holds invar_search_holds invar_lift_holds invar_complete_holds initial_state_props`. `Blossom_Shrinking_Search_correct_2`: structured (`not ret_2_conds`, `ret_1_conds`, `augmenting_path_def`).
- Final check (real theory `Blossom_Shrinking_Search.thy`, 1364 lines, imports `Graph_Matching_Specs Blossom.Blossom_Algo_Contraction`, no `iq.iq`): get_document_info (include_errors): is_processed true, running 0, unprocessed 0, finished 1799, error_count 0, warning_count 3 (duplicate-rule notes at `intro: dVsI` and a duplicate simp); get_sorry_positions: none; no sorry/oops/metis/smt/meson in the file (grep). Note: the blocking call `get_document_info wait_until_processed=true` did not return for several minutes although PIDE had already finished (12 s total theory time); the plain call without wait returned the clean status immediately.
- Correction to the list above: repl_sledgehammer was actually called twice, on `dVs_quotient_edges` (no proof found, decomposed by hand) and on the last `show` of `matching_pairs` (found the simp set of item 5); all other repairs were deterministic structural fixes (no search tactic left in a form that hit the cap), each REPL-gated.

## Gate 4 (orchestrator, 2026-10-24)
- PIDE: 1799 finished, 0 errors, 3 warnings (duplicate rules). to_ascii: 0 non-ASCII left.
- Statement-level diff against the plan's one-shot: only C4-1 (`quot.pref_suf` in `lift_one`)
  and C4-2 (`choose.choose`); C4-3 is an order change. Accepted (plan, after Amendment A).
- `apply` only in templates (unfold_locales, pinduct/twin, loop cases).
- ROOT: `Blossom_Shrinking_Search` added. Batch build exit 0 (12 s). No sorry/oops/metis/smt/
  meson. ai_provenance -s: exit 0, session 1773 lines ai (100%).
- Snapshot backups/Blossom_Shrinking_Search.thy.2026-10-24_gate4_green (md5 44e37322...).
- Coder note: `get_document_info` with wait did not return although processing had finished;
  without wait it reported the clean state.

### Phase 3, second run (after the prover wedge; REPL-first, Amendment A0)
- Procedure: body replayed block by block in REPL c3a (scratch theory `.claude/scratch_c3/Scratch3.thy`, buffer left open for the orchestrator to delete) with every step under the 10 s cap, steps flattened to one line (the REPL rejects newlines in string literals). Only after the whole body replayed (167 blocks, "ALL DONE") was the real theory created through `open_file` (create_if_missing + overwrite_if_exists, view) with the repaired text, without `iq.iq`. PIDE check: is_processed true, running 0, unprocessed 0, errors 0, 1 warning (no diagnostics text available); get_sorry_positions: none; no sorry/oops/metis/smt/meson/iq.iq in the file.
- Recon: (a) `search_invars` argument order `ex par flabel` in the local definition; global constant used as `compute_alt_path.search_invars (ugraph_abs G) (matching_abs M) ex par flabel` in `invar_forest_def` type-checks. (c) `.pinduct`, `.psimps`, `.domintros` premises as expected by `_simps`, `_induct`, `_domintros` after the repairs below. (d) `abs_search.search_invars` is the term of `invar_forest_def` (`invar_forest_props` and `call_1_facts` check).
- Plan changes: (3.1) type annotation of `search_invars`; (3.2) `es` renamed `rest` (es is a constant); (3.3) A1: `Graph_Matching_Specs where lookup = lookup and mate_empty = mate_empty` and `and mate_empty :: 'mate` in the `for` clause. All three marked `(* PLAN CHANGE ... *)` in the theory (3.1 above the definition, 3.2 and 3.3 above the locale/axiom definition).
- Repairs (statements unchanged):
  1. `forest_edges_update`: helper lemma `forest_edgesI` (`unfolding forest_edges_def by blast`); the cases use it with `simp add: insert_commute` (auto with `intro!: exI` hit "Unification bound exceeded").
  2. `Alternating_Forest_Search_induct`: `auto` failed (needs case split on the label); structured proof by `induction rule: pinduct` and one case per branch.
  3. `Alternating_Forest_Search_domintros`: `auto intro!: domintros` timed out; `proof(rule ...domintros, goal_cases)` with the four goals.
  4. `call_1_facts`: `flabel_invar_props` is the implication "labelled v1 => labelled v2"; applied to x and w via `ccontr`.
  5. `invar_unscanned_holds_1`, `invar_unscanned_holds_3`, `invar_scanned_holds_2/3`: `fastforce` timed out or lemma `upd2_abs`/`upd3_abs` unusable as simp rules: `upd2_abs` and `upd3_abs` fix the types `'parents`/`'labels` of the state, while a lemma about `invar_queue` or `invar_unscanned` only fixes the label type, so the rules do not apply to goals of such lemmas; all uses are replaced by the unfolding equations `..._upd2_def`, `..._upd3_def` plus the hypothesis `queue state = v # q`, with `proof(elim call_cond_elims exE)` and named `obtain`s; `spec`/`mp` instantiate the universally quantified hypotheses (the name `that` is rebound inside `consider`).
  6. `invar_unscanned_holds_2`, `invar_queue_holds_2/3`, `call_2_measure_1/3`, `call_3_measure_1`, `call_2/3_terminates`: `Alternating_Forest_Search_upd2_def`/`_upd3_def` added to the simp sets.
  7. `call_1_terminates`: `blast` for the strict subset (terminates in the REPL once the context is sound).
  8. `in_Alternating_Forest_Search_term_rel'`: `simp add: termination_intros` timed out; replaced by `rule call_1_terminates` and `in_prod_relI[of call_1_measure, OF ...]` (the unifier needs the explicit `f1`).
  9. `Alternating_Forest_Search_terminates`: `auto intro!: invar_holds_intros` timed out; explicit `less.IH[OF ...]` per branch.
  10. `Alternating_Forest_Search_correct_ret_2`: `auto`/`fastforce` timed out; `odd` via `mp`/`spec`, if1/if2 conditions through `obtain`.
  11. `ret_holds`, `final_state_invars`, `Alternating_Forest_Search_correct_1/2`: one case per branch with named `simps` facts; `final_state_invars` by `invar_*_holds[OF initial_state_props(...)]`.
  Sledgehammer was not needed: every failure was a termination or unifier problem solved by decomposing the step; the REPL showed the failing goal in each case (no sledgehammer call; process note for the reviewer).
- Final: get_document_info (wait, errors): is_processed true, running 0, unprocessed 0, error_count 0.

## Phase 5 (Edmonds_Blossom_Subprocedures)
- Recon: the Phase 5 section read (locale with contract, `blossom_search_def`, three lemmas). References checked by source: `compute_alt_path_spec_def` (Blossom_Algo_Compute_Aug_Path, 13 conjuncts; the first one is a universally quantified implication), `longest_disj_pfx` lemmas, `pfxs_path`, `common_pfxs_form_match_blossom'` (premise order: pfxs, from_tree, alt_paths(3), hds_neq, odd_lens, distinct, matching), `construct_aug_path'`; the contract clauses of `blossom_search` in the locale of `Blossom_Shrinking_Search` (lines 224-234) match the three lemmas (checked through `thm Edmonds_Blossom_Subprocedures.blossom_search` in the REPL).
- REPL-first replay (scratch `.claude/scratch_c5/Scratch5.thy`, REPL c5a, 13 top-level steps): 12 steps passed verbatim; the A1 locale header works as is. No plan changes.
- Repaired step (1): `compute_alt_path_specD` - the one-shot proof `using assms by (auto simp: compute_alt_path_spec_def)` hit the 10 s cap (auto on 13 goals against the unfolded 13-fold conjunction). Sledgehammer was not run (the cause is known: auto unfolds the conjunction/quantifier structure for every goal). Repair: `proof-`, `note S = assms[unfolded compute_alt_path_spec_def, simplified]` (simplified turns the `Some (p1,p2) = Some (..)` hypotheses of the conjuncts away and gives one conjunction of 13 facts), then one `show` per goal with `using S by blast`. Statement unchanged; replays in 0.2 s.
- Final check (real theory `Edmonds_Blossom_Subprocedures.thy`, 200 lines, imports `Blossom_Shrinking_Search Blossom.Blossom_Algo_Compute_Aug_Path`, no `iq.iq`): get_document_info (wait, errors): is_processed true, running 0, unprocessed 0, finished 292, error_count 0, warning_count 0; get_sorry_positions: none; grep sorry/oops/metis/smt/meson/iq.iq: none. Note: `get_document_info wait_until_processed=true` takes `timeout` in milliseconds; with `timeout: 90` (read as ms) it returned early with a partial status and PIDE appeared stalled at 37 finished; a second wait with `timeout: 60000` completed (292 finished). The REPL c5a was removed.

## Gate 3 (orchestrator, 2026-10-24)
- PIDE: 2225 finished, 0 errors, 1 warning. to_ascii: 0 non-ASCII left.
- Statement-level diff against the plan's one-shot (with `es` -> `rest` applied): only
  plan changes 3.1 (type of `search_invars`; body identical), 3.3/A1 (locale header), and
  the added helper lemma `forest_edgesI`. Accepted.
- Style: the one-shot's `apply(intro alt_labels_invar_pres ...)` in `search_invars_if1`
  (not a template) replaced at the gate by `by (intro ...) (use that in auto)`; batch build
  re-run: exit 0.
- ROOT: `Alternating_Forest_Search` added. Batch build exit 0 (16 s). No sorry/oops/metis/smt/
  meson. ai_provenance -s: exit 0 (theory 1578 lines ai).
- Snapshots: backups/Alternating_Forest_Search.thy.2026-10-24_gate3_green (before the style
  fix, md5 7bbe756a...) and ..._gate3_green_b (final, md5 f87f6a2e...).

## Incident 2 (orchestrator, 2026-10-24 16:34): modal dialog
- My disk edit of the open (unmodified) buffer of Alternating_Forest_Search.thy was not
  reloaded by jEdit; replacing the buffer via write_file and then save_file raised the modal
  "File Changed on Disk" dialog, which blocked jEdit's AWT thread. Disk content was already
  the final one (= gate3_green_b). After Phase 5 had finished, the 8768 jEdit was killed
  (all processes with USER_HOME=isabelle-home-blossom), the autosave
  `#Alternating_Forest_Search.thy#` removed, perspective moved aside (perspective.xml.restart2);
  disk copies in tmp/restart2/.
- Rule: never edit the disk file of a theory open in jEdit and then write its buffer. Gate
  edits are made either with no buffer open, or through I/Q only.

## Gate 5 (orchestrator, 2026-10-24, with jEdit stopped)
- Coder report: PIDE 292 finished, 0 errors, 0 warnings; no plan changes; 1 proof repaired
  (`compute_alt_path_specD`).
- to_ascii: converted. Statement-level diff against the plan's one-shot: none.
- ROOT: `Edmonds_Blossom_Subprocedures` added. Batch build exit 0 (20 s). No sorry/oops/metis/
  smt/meson; no `apply`. ai_provenance -s: exit 0 (session 3530 lines ai, 100%).
- Snapshot backups/Edmonds_Blossom_Subprocedures.thy.2026-10-24_gate5_green (md5 d2a594a9...).

## Phase 6 (Edmonds_Blossom_Example)
- Recon: plan Amendment A, Phase 3/4 changes, Phase 6 section, DFS_Example and Pair_Graph_RBT read. All interpretations are by name (`where`). Procedure (REPL-first, A0): scratch theory `.claude/scratch_c6/Scratch6.thy` (header with `iq.iq`), REPLs c6a/c6b/c6t/c6c (all removed); the one-shot body was replayed block by block (46 blocks, steps flattened to one line), repaired in the REPL, then replayed once more from scratch in a fresh REPL (all 46 blocks ok, max step 3.1 s, i.e. `demo_input`). Only then was the real theory created through I/Q (`open_file` with the repaired text, without `iq.iq`).
- Repairs of the one-shot (statements unchanged unless marked PLAN CHANGE):
  1. `gm` interpretation: `Graph_Matching_Specs_axioms` takes `t_set vset_inv vset_to_list` (the one-shot had `vset_inv t_set`): `show "Graph_Matching_Specs_axioms t_set vset_inv Tree2.inorder"`.
  2. `alt_forest` interpretation: `using ... by (simp add: Alternating_Forest_Search_def RBT_Set.empty_def)` left a trivially true goal (simp mismatch); replaced by `by (intro Alternating_Forest_Search.intro gm.Graph_Matching_Specs_axioms Map_axioms_as_needed)`.
  3. `alt_forest_run_impl_correct`, `shrinking_run_impl_correct`: `auto simp: ..._axiom_def` hit the 10 s cap; replaced by `using <locale lemma>[unfolded <name>_axiom_def, folded graph_input_rbt_def matching_invar_rbt_def ugraph_abs_rbt_def matching_abs_rbt_def] by blast+` (the folding is needed only for the shrinking lemma, whose locale lemma shows unfolded constants).
  4. `subprocedures`, `shrinking`, `edmonds_blossom` interpretations: the contract lemmas are stated with the `_rbt` constants whereas the goals show the unfolded constants of the data-structure layer, so `intro` with the lemma leaves unsolved goals; repaired as `by (intro <Locale>.intro gm.Graph_Matching_Specs_axioms <Locale>_axioms.intro, fold graph_input_rbt_def matching_invar_rbt_def ugraph_abs_rbt_def matching_abs_rbt_def, use <contract lemmas> in \<open>blast+\<close>)`.
  5. `edmonds_blossom_proofs` interpretation: the goal is the unfolded `graph_input`; `graph_input[unfolded graph_input_rbt_def]` added to the simp set.
  Sledgehammer was not needed: every failure was a mismatch of folded/unfolded constants or a cap, diagnosed with `repl_state` and `thm`.
- PLAN CHANGES:
  (P6-1) the context of the correctness section types `G :: ((nat x (nat x color) tree) x color) tree` and `vs :: nat list`: `fresh_nat` instantiates the vertex type of the interpretations to `nat`, so the polymorphic `fixes G vs` of the one-shot is ill-typed in `shrinking_run_impl G vs`.
  (P6-2) the folding chain of `edmonds_blossom_correct_1/2` is extended by `folded graph_input_rbt_def matching_invar_rbt_def ugraph_abs_rbt_def matching_abs_rbt_def`; otherwise the statements show the unfolded constants of the data-structure layer and `demo_max` does not apply. Meaning unchanged.
  (P6-3) new subsection "Code generation" (not in the one-shot), needed for `value` and `export_code` (recon (d)); no upstream theory touched:
    * `lemmas [code_unfold]` with the symmetric definitions `augment_rbt_def adjacency_edges_rbt_def mate_from_list_rbt_def matching_edges_rbt_def neighbourhood_rbt_def from_list_rbt_def`: the code equations of the later interpretations mention these constants in unfolded form (error: no code equations for `Matching_Augmentation_Specs.augment_impl`, `Graph_Matching_Specs.adjacency_edges/mate_from_list/matching_edges`, `Pair_Graph_Specs.neighbourhood/from_list`). The `defines` of the interpretations were not changed.
    * `quot.pref_suf` (a `fun` inside locale `quot` of the human theory) has no code equation, and its simp rules carry the premise `quot sel E s u`; a code equation at type `nat` is rejected ("too specific"). `lift_one_rbt` is monomorphic (type `nat`), so: `fun pref_suf_list`, witness `quot_nat` (`quot (\<lambda>S. SOME x. x \<in> S) {{1::nat, 2}} {1} 0` by `unfold_locales`), `pref_suf_list_eq` (`quot.pref_suf pref (v::nat) l = pref_suf_list pref v l`), `lift_one_rbt_code`, and `declare [[code drop: lift_one_rbt replace_cycle_rbt]]` then `declare lift_one_rbt_code[code] replace_cycle_rbt_code[code]`.
    * `replace_cycle_impl` (Phase 4) binds `hd p2` and `last p1` in a `let`; the generated SML evaluates both strictly and raises `Match` on an empty path (found when `value` aborted with "exception Match raised" after the first contraction). `replace_cycle_rbt_code` is the lazy `if` form of the same definition (proved by `simp add: shrinking.replace_cycle_impl_def Let_def`). Note for the orchestrator: the HOL semantics are unaffected; only the code of the upstream definition is partial in strict evaluation; no upstream change is required.
- Computed demonstration: `value "Tree2.inorder (current_matching (edmonds_blossom_run_impl demo_G demo_vs))"` = `[(0, 1), (1, 0), (2, 3), (3, 2), (4, 5), (5, 4)]` (3 edges, 6 mate entries; one triangle is shrunk, the path is lifted back). `demo_input` and `demo_max` proved; `export_code edmonds_blossom_run_impl in SML module_name Edmonds_Blossom` succeeds.
- Final check (real theory `Edmonds_Blossom_Example.thy`, imports `Edmonds_Blossom_Top_Loop Edmonds_Blossom_Subprocedures Alternating_Forest_Search Directed_Set_Graphs.Pair_Graph_RBT`, no `iq.iq`): get_document_info (wait, errors): is_processed true, running 0, unprocessed 0, finished 156, error_count 0, warning_count 2 (harmless: `Partially applied constant Lookup2.lookup` in `delete_edge` and `ignoring syntactically subsumed code equation from_list_rbt`, both emitted at the `gm` interpretation; the third diagnostic is the info "Ignoring duplicate rewrite rule: Let" in `replace_cycle_rbt_code`); get_sorry_positions: none; no sorry/oops/metis/smt/meson/iq.iq. Slowest command: `demo_input` 3.9 s. File saved by jEdit with glyphs (to be converted to ASCII at the gate). The scratch buffer `.claude/scratch_c6/Scratch6.thy` is left open for the orchestrator to delete.

## Gate 6 and final checks (orchestrator, 2026-10-24)
- Coder report: PIDE 156 finished, 0 errors, 2 warnings (partially applied constant,
  subsumed code equation); demonstration value
  `[(0,1),(1,0),(2,3),(3,2),(4,5),(5,4)]` (3 edges); demo_input, demo_max proved;
  export_code to SML succeeds. Plan changes P6-1..P6-3 (see the plan, after Amendment A).
- The 8768 jEdit was stopped (kill -9 of the USER_HOME=isabelle-home-blossom processes;
  perspective moved to perspective.xml.final) before the gate's disk edits.
- to_ascii: converted. Statement-level diff: only the new code-generation lemmas and the
  extended folding chains. ROOT: `Edmonds_Blossom_Example` added. Batch build exit 0 (runs
  `value` and `export_code`). ai_provenance -s: exit 0, session 3751 lines ai (100%).
- Snapshot backups/Edmonds_Blossom_Example.thy.2026-10-24_gate6_green (md5 e2ad0b11...).
- Final: `isabelle build -c -o document=false Blossom_Executable` exit 0 (20 s); all six
  theories ASCII, no sorry/oops/metis/smt/meson/iq.iq; tracked files changed: only ROOTS (one
  line); human theories untouched. Scratch theories `.claude/scratch_c2..c6` and jEdit `~`
  backups deleted.
- Style figures (AI_Style/style_stats.py, NEW = the six theories; DFS / BFS targets): single
  `by` 59.8% (DFS 76.5, BFS 63.1; checklist >= 63%), median proof length 2 (ok), apply 2.5%
  (ok, templates only), labelled facts 0.38/lemma (checklist <= 0.25), [OF ...] 1.15/lemma
  (checklist <= 0.6), auto 33.6% vs simp 19.8%. A polishing pass would be needed to meet
  checklist items 5-6.

# v2: self-contained session (2026-10-24)

User decision: no algorithm twice; copy the human theories into the session and adapt them;
names retained (loops capitalised: Find_Max_Matching, Find_Aug_Path, Compute_Alt_Path);
provenance: copied lines human, rewritten proofs ai marker, new material ai; abstract Blossom
removed only after the user is satisfied. Plan: `Blossom_Executable_Plan.md` (v1 plan kept as
`Blossom_Executable_Plan.v1.md`); one-shots in `plan_v2/oneshots/`; generator scripts in
`plan_v2/scripts/`.

## v2 setup (orchestrator)
- v1 theories removed from the session directory (identical copies with MD5SUMS in
  `backups/v1_reuse_design_2026-10-24/` and in the project memory directory).
- ROOT: `Blossom_Executable = Basic_Matching +`, no theories yet (each theory is added at its gate).
- Pre-checks in scratch sessions outside the repository: copies Blossom_Misc, Graph_Quotient,
  Blossom_Prefixes, Compute_Alt_Path_Invars build; Graph_Matching_Specs, Find_Max_Matching,
  Compute_Alt_Path, Find_Aug_Path, Find_Aug_Path_Subprocedures, Edmonds_Blossom_Example build
  against a stub of Graph_Quotient_Lifting (preamble checked, refine_works by sorry);
  the full Graph_Quotient_Lifting copy did not finish (commands at lines 417 and 2217 still
  running after 170 s).

## v2 Phase 4 (Graph_Matching_Specs, Find_Max_Matching)
- Both one-shots opened through I/Q (open_file with the one-shot text, created files) and saved; no repair needed.
- Graph_Matching_Specs: is_processed true, running 0, unprocessed 0, finished 463, errors 0, warnings 5 (info warnings only).
- Find_Max_Matching: is_processed true, running 0, unprocessed 0, finished 354, errors 0, warnings 0.
- No sorry/oops/metis/smt/meson; no plan changes. Saved files differ from the one-shots only in symbol glyphs (jEdit) vs \<...> ASCII (diff is empty after ASCII conversion of a scratch copy).

## v2 Phase 1 (Blossom_Misc, Graph_Quotient)
- Both one-shots copied verbatim through I/Q (open_file view+create_if_missing from args JSON, save_file); no repairs, no plan changes.
- Blossom_Misc: is_processed true, running 0, unprocessed 0, finished 233, errors 0, warnings 1; no sorry.
- Graph_Quotient: is_processed true, running 0, unprocessed 0, finished 5637, errors 0, warnings 31; 91 s total; no sorry.
- Saved files differ from the one-shots only by glyph vs. \<...> ASCII forms (after to_ascii on a scratch copy the diff is empty). Buffers left open for the orchestrator.

## v2 Gates 1 and 4 (orchestrator)
- Batch Isabelle does not read the glyphs jEdit saves (Malformed command syntax at a cartouche),
  and I/Q has no tool to close a buffer; ASCII conversion of the real files is moved to Phase 9
  (jEdit stopped). Gate builds use ASCII copies in a scratch session (`plan_v2/scripts/gate_build.sh`).
- Phase 1 and Phase 4: saved texts identical to the one-shots after ASCII conversion; statement
  check trivially equal; gate build (Blossom_Misc, Graph_Quotient, Graph_Matching_Specs,
  Find_Max_Matching) exit 0; provenance strict ok (human 2694 lines, ai 581 lines). GREEN.
  ASCII copies in `backups/v2_gated/`.

## v2 Phase 3 (Blossom_Prefixes, Compute_Alt_Path_Invars)
- Both one-shots copied verbatim through I/Q (open_file view+create_if_missing from args JSON, then save_file); no repairs, no plan changes, no iq.iq import needed.
- Blossom_Prefixes: is_processed true, running 0, unprocessed 0, finished 2004, errors 0, warnings 6 (13.5 s); no sorry.
- Compute_Alt_Path_Invars: is_processed true, running 0, unprocessed 0, finished 5198, errors 0, warnings 16 (45.7 s); no sorry.
- Saved files equal the one-shots after to_ascii on a scratch copy (diff empty). Buffers left open for the orchestrator.

## v2 Phase 5 (Compute_Alt_Path)
- Pre-checked one-shot opened through I/Q (`open_file` with view and the one-shot text as content, via args JSON) and saved; no repair needed, no plan changes.
- PIDE check (`get_document_info`, wait_until_processed, include_errors): is_processed true, running 0, unprocessed 0, finished 1874, error_count 0, warnings 0. `get_sorry_positions`: none. No sorry/oops/metis/smt/meson in the text.
- Saved file (1547 lines), converted to ASCII in a scratch copy, is identical to the one-shot. No `iq.iq` import was used.
- Phase 5 green.

## v2 Gates 3 and 5 (orchestrator)
- Phase 3 (Blossom_Prefixes, Compute_Alt_Path_Invars) and Phase 5 (Compute_Alt_Path): saved texts
  identical to the one-shots after ASCII conversion; gate build of the seven gated theories exit 0;
  provenance strict ok (session so far: human 5945 lines, ai 2153 lines). GREEN.

## v2 Phase 2 (Graph_Quotient_Lifting)
Method: scratch theory `.claude/scratch_c2v2/Scratch_Lift.thy` (imports Blossom_Executable.Graph_Quotient, Blossom_Executable.Blossom_Misc, iq.iq), REPL `c2v2`; the one-shot body replayed command by command, the long proofs (alt_list_replace_cycle, path_replace_cycle, distinct_replace_cycle, hd_nin_last_nin_replace_cycle) sub-command by sub-command. REPL quirk: a `;` at a line end splits the step, so the driver joins such lines (the buffer text keeps the original layout). The whole repaired body (work file `.claude/scratch_c2v2/work2.json`) replayed in the REPL in 149 s without errors; no step hit the 10 s cap. Then the theory was created through I/Q (open_file view+create, saved) WITHOUT iq.iq.
Final PIDE check: is_processed true, running 0, unprocessed 0, finished 5124, errors 0, warnings 14 (info-level, messages empty; they sit at lines of the copied human proofs and at two of the new ai steps: `by (auto simp: distinct_append)` and `by ... (simp add: hd_append2)`); get_sorry_positions: none; no sorry/oops; no metis/smt/meson in any added line (12 removed lines had metis/smt). Total PIDE time 52 s. Saved file (after to_ascii on a scratch copy) is identical to the replayed work text; it differs from the one-shot only in the repaired steps (165 removed / 210 added lines, 63 hunks).

### Root causes found (evidence from the REPL)
1. `Let` not unfolded: the new `stem2vert_path_def'`/`replace_cycle_def'` have a `let`; simp/auto/unfolding steps of the copies need `Let_def` (hd_stem2vert_path, length_replace_cycle, stem2vert_path_append_2, path_stem2vert_path, stem2vert_path_pref_or_suc, and several sites below). Sledgehammer was not needed for these (the failing goal showed the unexpanded `let`); the smt in hd_stem2vert_path (the step at one-shot line 426, which diverged) is replaced by `auto simp: hd_find_pfx hd_rev` with the new lemma `hd_find_pfx`.
2. `M` and `C` are locale parameters, so the `{ fix C ... } note d1 = this` blocks (generalising over the cycle) shadow the locale `C`, and the locale lemmas (stem2vert_path_def', choose_vert_works_1, ...) no longer apply to the new C ("OF: no unifiers"). This was the cause of the diverging metis at one-shot line 2226 (hd_nin_last_nin_replace_cycle). Fix there: inside the block, `interpret Lc: quot_lift E s u adj mate M C` (locale assumptions from adj_E mate_M M_subset_E u_fresh, quot, odd_cycleD(3)) and use the `Lc.` copies of the lemmas; the metis step is replaced by a simp step from Lc.hd_stem2vert_path / Lc.hd_stem2vert_nempty.
3. Semantic difference: `choose_con_vert adj C v` depends on the ORDER of the list, so `choose_con_vert adj (rev C) v` may differ from `choose_con_vert adj C v` (in the original the choice depended only on `set C`). The d1 blocks of alt_list_replace_cycle, path_replace_cycle, distinct_replace_cycle were applied to `rev C` and then identified with the stem of `C`; that identification is false now. Fix: the three d1 blocks are restated for an arbitrary `chv` (fixed, with `chv \<in> set C`, `{hd p2, chv} \<in> E`; alt_list one also with the premise `last (edges_of_path (find_pfx ((=) chv) C)) \<in> M \<or> chv = last C`) and conclude about `find_pfx ((=) chv) C @ p2`; the use sites (C-sites and rev-C sites) supply `chv` and convert with `stem2vert_path_def' Let_def` or the new lemma `stem2vert_path_eq_pfx`. The metis/smt steps of these blocks and sites are replaced by structured simp/rule steps.
4. New ai lemmas (all in the body, marked `lemma \<^marker>\<open>provenance ai\<close>`): `hd_find_pfx`, `choose_vert_works_3` (choose_vert_works_1 with p1 = []), `find_pfx_hd`, `stem2vert_path_eq_pfx`, `distinct_find_pfx_cycle` (stated for a list `Cs`, not the locale's `C`).
5. Sledgehammer: one call (30 s) on the step `edges_of_path (chp @ [chv]) \<noteq> [] \<longrightarrow> last ... \<in> M` of alt_list_replace_cycle returned no proof (timed out); that step was decomposed by hand (chp \<noteq> [] from the nonempty edge list; chv \<noteq> hd C because the prefix of C ending at hd C is [hd C]; then the disjunction). All other repairs followed directly from the failing goals shown by repl_state and needed no search beyond simp/auto/blast on small goals, each tried in the REPL first.

### Repaired steps (9 copied lemmas modified, 5 new lemmas)
hd_stem2vert_path (by), length_replace_cycle (3 by), stem2vert_path_append_2 (by), alt_list_replace_cycle (d1 block restated, 8 site steps), path_stem2vert_path (by), path_replace_cycle (d1 block restated, 8 site steps), stem2vert_path_pref_or_suc (apply), distinct_replace_cycle (d1 block restated, 6 site steps), hd_nin_last_nin_replace_cycle (interpretation + 3 steps with `Lc.`). Every changed command carries `\<^marker>\<open>provenance ai\<close>`; no `provenance` command changed.

### Plan changes
None: all statements and definitions (including refine_works, quot_lift, the preamble) are verbatim from the one-shot. Only proof internals changed; internal facts/blocks of three proofs were restated as described (not statements of top-level lemmas).

### Open
Warnings (14) are not investigated (messages empty in the I/Q output). The scratch buffer `.claude/scratch_c2v2/Scratch_Lift.thy` is still open in jEdit (no close tool); REPL c2v2 removed.

### Phase 2: marker rework after gate 2 (provenance rule 4)
Markers only; no proof text changed (diff of ASCII copies before/after with the marker text stripped: identical, except that jEdit appends one final newline). Rules applied: a marker only on commands written from scratch (new lemma/have/fix/assume/obtain/proof/interpret, new `using`) or on a `by`/`apply` whose method was replaced; edited commands (statement adapted to `chv`, `Let_def`/`Lc.`/fact arguments added, same method) keep their label and carry no marker; no marker on an opener (`have`/`apply`/`proof`) whose scope contains unchanged or merely edited copied commands. Result: marker lines 109 -> 58 (53 marker occurrences removed, 2 added: the `by` of the `obtain Ctail` step (moved from the `obtain`) and the `by` of the first subgoal in distinct_replace_cycle's d1 block; redundant nested markers inside new `have`s also removed). Removed all markers on: `apply` of stem2vert_path_pref_or_suc, `have` of the three restated d1 blocks (statement edited), `ultimately have` of alt_list d1, `have` of block 2 and its `apply(intro conjI)`, the `have`s of copied statement edits, the `by` steps that kept their method (simp/auto with new arguments), and edited `using` lines. PIDE after the rework: is_processed true, running 0, unprocessed 0, finished 5124, errors 0, warnings 14; no sorry.

## v2 Phase 6 (Find_Aug_Path)
- Pre-checked one-shot (1114 lines) opened through I/Q (args JSON built from the file; view + create) and saved; no repair, no plan changes, no iq.iq.
- PIDE (wait_until_processed, include_errors): is_processed true, running 0, unprocessed 0, finished 1351, error_count 0, warnings 3 (status counter; warning_count 0, no messages listed). get_sorry_positions: none. No sorry/oops/metis/smt/meson. Saved file after ASCII conversion of a scratch copy is identical to the one-shot.

## v2 Phase 7 (Find_Aug_Path_Subprocedures)
- One-shot (198 lines) opened and saved the same way; no repair, no plan changes.
- PIDE: is_processed true, running 0, unprocessed 0, finished 292, error_count 0, warnings 0. No sorry positions; no sorry/oops/metis/smt/meson. Saved file (ASCII scratch copy) identical to the one-shot.

## v2 Phase 8 (Edmonds_Blossom_Example)
- One-shot (229 lines) opened and saved the same way; no repair, no plan changes.
- PIDE (two waits; first showed unprocessed 136, then running 1 while the value/code generation ran): is_processed true, running 0, unprocessed 0, finished 135, error_count 0, warnings 1 (status counter; no message found among commands). No sorry positions; no sorry/oops/metis/smt/meson. Saved file (ASCII scratch copy) identical to the one-shot.
- `value "Tree2.inorder (current_matching (find_max_matching_run_impl demo_G demo_vs))"` gives `[(0, 1), (1, 0), (2, 3), (3, 2), (4, 5), (5, 4)]` :: (nat x nat) list (1.2 s); a perfect matching of the two triangles joined by an edge. demo_max (via edmonds_blossom_correct_1) and export_code check.

## v2 Gates 2, 6, 7, 8 and Phase 9 (orchestrator)
- Gate 2: statements of the one-shot all unchanged (53), 5 new ai lemmas (choose_vert_works_3,
  hd_find_pfx, find_pfx_hd, stem2vert_path_eq_pfx, distinct_find_pfx_cycle). First provenance
  table: 34 unchanged human lines labelled ai (markers on block openers/apply covering copied
  lines) and one human metis inside an ai scope; sent back to the coder (rules: markers only on
  commands written from scratch; edited commands keep their label). After the fix: 0 such lines,
  no ai command with metis/smt/meson; gate build clean. GREEN.
- Gates 6-8: texts identical to the one-shots; gate build of all 11 theories exit 0. GREEN.
- Phase 9: all buffers unmodified; jEdit and every process with USER_HOME=isabelle-home-blossom
  stopped (including orphaned z3 and Naproche processes from the two killed scratch builds);
  `to_ascii.py` on all theories (results byte-identical to the gated ASCII copies); no import of
  a `Blossom.` theory; jEdit backup `Graph_Quotient_Lifting.thy~` removed;
  `isabelle build -c -o document=false Blossom_Executable`: exit 0, 46 s;
  `isabelle ai_provenance -s -t Blossom_Executable`: ok, human 7873 lines (66.8%), ai 3917 (33.2%).
  Backup: `backups/v2_stageA_green_2026-10-24/` (MD5SUMS). Scratch dirs of Phases 1, 3-8 archived
  outside the repository; `.claude/scratch_c2v2/` kept (REPL replay tooling for Stage B).
STAGE A GREEN.

## v2 Stage B3 (Blossom_Prefixes)
- Method: scratch theory `.claude/scratch_b3/Scratch_B3.thy` (copy of the Stage A text, imports + `iq.iq`) for the REPL (prefix `b3`); every replacement was stepped in the REPL under the 10 s cap, per top-level command (`chkf.py`), before it went into the buffer; sledgehammer was used twice as a discovery aid (`pfxs_distinct`: facts `disj_pfx_are_disj_1 distinct_append inter_distr_append in_set_butlastD distinct_butlast`; `last_pfxs_neq`: `last_in_set in_set_butlastD`), everything else was rebuilt by hand from the cited metis facts and `repl_find_theorems`. Whole file written in one `write_file` (all pieces REPL-gated), saved, checked.
- Finished (21 lemmas, 61 `provenance ai` markers; all metis/smt/meson/apply/`{ }` removed; layout fixed): match_blossom_distinct_tl, cycle_set_tl_eq_butlast, no_first_pfx_then_no_snd_pfx, first_pfx_then_snd_pfx, first_pfx_nempty, pfx_common_end, disj_pref_append2, disj_pfx_are_disj_1/2/3, disj_pfx_is_complete, pfxs_alt_path', pfxs_path, pfxs_distinct, pfxs_odd_cycle', pfxs_even_stem', common_pfxs_form_match_blossom', construct_aug_path, construct_aug_path', odd_cycle_length_edges_ge_3, odd_cycle_length_verts_ge_4. Layout-only edits (`then show ?case by auto`, `using .. by ..`) in the other lemmas.
- Techniques: the `apply (auto ..) / by metis+` scripts of the `longest_disj_pfx` induction lemmas became one `by (auto simp: Let_def split: ... dest: cons1(1)[OF sym] ..)` or `proof \<^marker>\<open>provenance ai\<close> (clarsimp ..., goal_cases)` with one `case n` per goal; `edges_of_path_snoc_2`, `edges_of_path_append_3`, `length_edges_of_path_rev`, `alternating_list_odd_last/even_last` replace the metis edge computations in `pfxs_even_stem'`.
- DEVIATION (provenance, for the orchestrator): the two nested `{ ... } note ... = this` blocks of `pfxs_even_stem'` (about 150 unchanged human lines) became `have p_nempty_even: "..." proof- ... qed` and `have *: "..." proof- ... qed`, the `have`/`show` of the last step of each block was turned into `show`. These openers carry NO ai marker: a marker would put the unchanged human body into an ai scope. The new statements and the last premise `odd (length (edges_of_path (last pfx1 # p)))` (the original block also had it, from `moreover assume odd_length`) are therefore labelled human; only the replaced steps inside carry markers. The two `moreover{ assume .. then have False .. }` blocks of `pfxs_odd_cycle'` were replaced by `then have \<^marker>\<open>provenance ai\<close> "even (length pfx1)" "even (length pfx2)"` and `then show \<^marker>\<open>provenance ai\<close> ?thesis` (new text only).
- A heuristic check (difflib alignment against the Stage A text, scopes of the 61 markers) finds no unchanged human line inside an ai scope.
- Statements: `gate_stmts.py` on an ASCII copy against the Stage A backup: 33 statements, identical 33. No plan changes.
- Final check: get_document_info (wait_until_processed, include_errors): is_processed true, running 0, unprocessed 0, finished 1948, error_count 0, warnings 5 (status counter, as in Stage A: 6); get_sorry_positions: none. Counts: metis 0, smt 0, meson 0, apply 0, `{`-blocks 0, same-line using/by 0, `proof -` 0, no iq.iq in the theory. REPL b3 removed; scratch buffer Scratch_B3.thy still open in jEdit (no close tool).
- Coordinator correction applied (write_file str_replace, saved, re-checked): `have \<^marker>\<open>provenance ai\<close> p_nempty_even: ...` with `proof \<^marker>\<open>provenance human\<close>-`, and likewise for `have *:`; inner ai markers unchanged. PIDE: is_processed true, running 0, unprocessed 0, finished 1948, error_count 0, warnings 5; no sorry positions; no metis/smt/meson.

## v2 Gate B3 (orchestrator)
- Blossom_Prefixes: statements 33/33 unchanged; metis/smt/meson/apply/{}-blocks/same-line using-by/
  `proof -` all 0; no unchanged human line in an ai scope; gate build exit 0. Provenance fix at the
  gate: the two new `have` statements of `pfxs_even_stem'` (former `{ } note` blocks) are marked ai,
  their copied bodies restored to human by `proof \<^marker>\<open>provenance human\<close>-` (nesting
  verified with ai_provenance on a test theory). Commands: human 843, ai 132. GREEN.

## v2 Stage B4 (Compute_Alt_Path_Invars)

Batch 1 (saved, PIDE check: processed, running 0, unprocessed 0, errors 0). Working copy and tools in
`.claude/scratch_b4/` (work.txt is the master text; blocks are replayed in the REPL before they go in).
Finished lemmas: interpretation matching_graph, if1_cond_props (layout), if1_cond_props'', if2_cond_props'',
wf_par', flabel_invar_pres, flabel_invar_2_pres, alt_invars_then_alt_path, v1_neq_v3, ancestors_unaffected,
alt_labels_invar_pres, alt_list_pres, follow_cons_3, follow_cons_3', follow_pinduct.
Evidence: sledgehammer (REPL) used for wf_par' (converse_rtranclE), alt_labels_invar_pres (`par' v1' = Some v2'`:
blast; the two metis on `v2' \<noteq> v3`: facts v1_neq_v3, `{v} \<notin> M`, par'); the big smt/metis steps of the
cases c1/c2 (alt_labels_invar_pres, alt_list_pres) were replaced by structured ai proofs (explicit instances of the
induction hypothesis), because sledgehammer only returned fact lists of 20+ names.

## v2 Stage B2 (Graph_Quotient_Lifting)
- Method: scratch copy of the theory (with `iq.iq`) in `.claude/scratch_b2/`; every replacement was replayed in the I/R REPL (prefix `b2*`, 10 s cap) lemma by lemma from the statement; replacements were collected as edits on the Stage A text (`orig.thy`), assembled by script into one candidate, every lemma of the candidate replayed again in the REPL (all 49 lemmas OK), the candidate checked with `isabelle ai_provenance` against the Stage A table, and then written to the buffer in ONE write (instead of batches: the 4 big lemmas are interdependent) and saved.
- Rewritten lemmas (24 of 49; plus layout-only `rw3`, `find_pfx_butlast`): pref_suf_works, choose_vert_works_1/2, find_pfx_subset, stem2vert_path_subset, hd_stem2vert_path, hd_stem2vert_nempty, alt_list_quotG_then_alt_list_1/2, inBetinM, rw4, rw5, stem2vert_path_append_2, alt_list_replace_cycle, path_find_pref, path_replace_cycle, stem2vert_path_pref_or_suc, stem2vert_path_distinct_neq_lastC, stem2vert_path_distinct, distinct_replace_cycle, hd_nin_last_nin_replace_cycle, length_replace_cycle_works, refine, refine_works. Statements, definitions, names and order unchanged (gate_stmts: 58 of 58 identical).
- The 16 `{ ... }` blocks (alt_list_replace_cycle 5, path_replace_cycle 4, distinct_replace_cycle 4, hd_nin_last_nin_replace_cycle 3) became `have name: "\<And>vars. premises \<Longrightarrow> concl" proof- fix ... assume ... show ... qed`; the statements were read off the exported facts in the REPL (`thm d1`). The opener of such a `have` carries NO marker (its scope contains copied human lines; the gate rule forbids unchanged human lines in an ai scope); the opener replaces the human `{` line.
- `apply` scripts became `proof(rule R, goal_cases) case k show ?case ... next ... qed` (opener unmarked, bodies keep their human `using`/`by`) or one `by` call; replaced methods carry `by \<^marker>\<open>provenance ai\<close>`, new `using` lines `using \<^marker>...`, wholly new proofs `proof \<^marker>...-` / `have \<^marker>... e1`.
- Evidence for the metis/smt replacements (all steps reconstructed without metis/smt/meson; sledgehammer used as discovery aid, facts mined):
  - set-membership/subset steps (G1-G4, ~20 occurrences): sledgehammer facts `subset_path_Vs`, `tl_path_is_path`, `path_pref`, `in_quotG_neq_u`, `neq_u_notin_quotG` -> `by (auto intro!: subset_path_Vs dest: tl_path_is_path)`, `... dest: path_pref`, `by (auto intro: in_quotG_neq_u)` (the old `using quot good_quot_map` line was dropped: it made `auto` time out).
  - `length p = 1` / `p = [a]` (8 occurrences): `by (cases p) (auto simp: Suc_le_eq)` and `by (cases p) auto` (sledgehammer: only metis over `Suc_1 Suc_leI ...`).
  - `edges_of_path (p1 @ [u]) \<noteq> []`, `last (edges_of_path (p1 @ [u])) = {last p1, u}`: `edges_of_path_nempty`, `edges_of_path_snoc[symmetric]` (sledgehammer: `edges_of_path_snoc last_snoc`).
  - `chv \<in> set C` (4): `choose_vert_works_3(1)[OF ...]` + `simp add: hd_rev`; `last (edges_of_path (find_pfx ((=) chv) (rev C))) \<in> M` (3): `find_pfx_edges_of_path_alt_list(2)[OF cycle choose_vert_works \<open>chv \<noteq> hd C\<close>]` + `auto simp: chv_def hd_rev`.
  - final contradictions `p2 = [a]` (3): sledgehammer facts `edges_are_Vs up2_in_M last_appendR`; rebuilt as `{u, a} \<in> quotG M`, `a \<in> Vs (quotG M)`, `last p' = a`, contradiction with `p'_feats(4)`.
  - `chva2'` smt (alt_list_replace_cycle): sledgehammer facts `good_quot_map quot_graph_def edge_in_graph_in_quot`; rebuilt via `P ` {chv, a2'} = {u, a2'}` and `edge_in_graph_in_quot`.
  - `rw3/rw4/rw5`, `e_of_p_chp`: `edges_of_path_append_3`, `edges_of_path_snoc_2`, `edges_of_path_symmetric_split` (sledgehammer hints), hd_nin_last: `vert_in_graph_iff_in_quot_diff_u` with `hd_in_set`/`last_in_set`, `d1[OF mp ...]` for the p2 = [] case.
  - odd-length goals (alt_list_replace_cycle, path_replace_cycle): `alternating_list_even_last`/`alternating_list_odd_last` by contradiction; `by (cases p1; auto simp: edges_of_path_nempty)` for the non-emptiness side goal.
  - `refine`: `by fast` (sledgehammer: `by fast`; `blast` timed out); `refine_works`: `by (subst *; simp add: butlast_tl)`, `by (intro refine[OF _ _ _ _ assms(2-)]; auto)`.
- Plan changes: none.
- Open problem / note: `isabelle ai_provenance` table compared with Stage A (difflib on line text): 3 `qed` lines of Stage A (human) are matched by text to new `qed` lines that close new ai blocks (`proof \<^marker>...-`); these are new lines, not unchanged ones (alignment artefact of the text comparison).
- Final check (PIDE, buffer saved): is_processed true, running 0, unprocessed 0, finished 5416, error_count 0, warning_count 0; get_sorry_positions: none; metis/smt/meson 0, apply 0, `{`-blocks 0, same-line using/by 0, `proof -`/`proof (` 0.

Batch 2 (saved, PIDE check: processed, running 0, unprocessed 0, errors 0). Finished lemmas: follow_eq,
last_follow_eq, compute_alt_path_follow_eq, compute_alt_path_last_eq, last_not_matched_invar_pres (the `{ }`
block became `have gen: ... proof<human>- ... qed`; the statement of gen is new and ai), matching_examined_invar_pres
(block -> have), alt_list_length_odd, last_even_invar_pres (block -> have F), last_even_invar_imp, path_invar_pres and
distinct_invar_pres (blocks -> have), examined_have_odd_verts_invar_pres,
unexamined_matched_unlabelled_invar_pres.
Evidence: sledgehammer (REPL) on `last_not_matched_invar_pres` (metis with `*(1,2)` and the earlier fact; the closer
`(cases "v1 = v2") auto` replaces it); other metis/smt steps replaced by facts named in the original calls
(v1_neq_v3, flabel_par_invar_props(2), doubleton_in_matching, follow_nempty, alt_list_step).
- Provenance correction (coordinator request, markers only): of the 42 candidate lines, 18 are statements composed by me and now carry `\<^marker>\<open>provenance ai\<close>` on the `have`: the 16 explicit statements of the former `{ } note` blocks (`d1`, `alt_list_p2`, `append_works`, `replace_cycle_cases`, `replace_cycle_cases_p1`) plus `alt_p1hd` and `alt_p1`. 20 human restore markers were added: `proof \<^marker>\<open>provenance human\<close>-` on the 17 copied bodies (16 + `alt_p1hd`), and `using`/`using`/`by` of `alt_p1` (copied human text). The other 24 lines are edits of Stage A commands (`show`/`assume that`/`then show`/`ultimately show` adapted from `have ... if`/`have`, `have *` of `inBetinM`) or layout-only splits (`have rev_p1_nempty`) and keep the human label. Re-check: provenance table (human 1972 / ai 740 commands in this theory), PIDE finished 5416, 0 errors, nothing running, no sorry.

## v2 Gate B2 (orchestrator)
- Graph_Quotient_Lifting: statements 58/58 unchanged; all style counts 0; gate build exit 0.
  Provenance correction at the gate: 18 statements composed by the coder (explicit statements of
  former `{ } note` blocks, two new facts) marked ai, their copied bodies restored to human
  (20 restore markers). No unchanged human line in an ai scope. Commands: human 1972, ai 740. GREEN.

Batch 3 (saved, PIDE check: processed, running 0, unprocessed 0, errors 0). Finished lemmas:
odd_labelled_verts_num_invar_pres, es_minus_matched, capacity_bounds_common_edges, OSC_insert (block -> have),
odd_set_cover_bounds_matching_size, OSC_union, card_sing_image, card_UNION_const.
Evidence: the metis/smt steps about "two distinct edges of M through a vertex / in a 3-set" were replaced by a short
structured proof from `card_le_Suc_iff` (sledgehammer only returned long metis fact lists); the `card M \<le> card (M - ev) + 1` step by
`card_Diff_subset_Int` + `arith`; `card_UNION_const` by a case split on `k = 0` (finite/infinite sets), sledgehammer facts
card_Un_disjoint, card_eq_0_iff, finite_Un; OSC_union by `auto` followed by an explicit `bspec`/`bexI` instance.
Remaining: compute_alt_path_from_tree_2' (the large lemma, 5 `{ }`-blocks), then a global layout pass.

Batch 4 (final, B4 complete). Finished: compute_alt_path_from_tree_2' (the large lemma: one `{ }` block -> `have *`,
34 metis/smt/apply sites replaced, `lab` helper for label exhaustiveness, structured final step via Berge_2 instead of meson)
and invar_init; global layout pass (23 same-line `using ... by`/`then show ... by` split onto their own lines).
Final PIDE check: is_processed true, running 0, unprocessed 0, errors 0, 21 warnings (stage A: 15-17), no sorry.
Counts over the whole theory: metis 0, smt 0, meson 0, apply 0, `{ }` blocks 0, `proof -`/`proof (` 0, same-line using/by 0.
gate_stmts (ASCII scratch copy vs Stage A backup): 107/107 statements identical. Own text-level check (`.claude/scratch_b4/prov2.py`, same
difflib comparison as gate_b): 0 unchanged human lines in an ai scope (two coincidental line matches in `aux2`/`aux` were reworded).
Plan changes: none (no statement, definition, name or order changed). REPL "b4" removed.
Slowest new steps (PIDE): `by (simp add: unexamined_matched_unlabelled_invar_def) blast` 3.2 s.

## v2 Gate B4 (orchestrator)
- Compute_Alt_Path_Invars: statements 107/107 unchanged; all style counts 0; gate build exit 0; no
  unchanged human line in an ai scope; the 10 changed statement lines labelled human restate Stage A
  statements (have -> show etc.), i.e. edits. Commands: human 2125, ai 692. GREEN.

## v2 Stage B wave 1 closed (orchestrator, 2026-10-25)
- B2, B3, B4 green. jEdit stopped; files already ASCII and byte-identical to the gated copies;
  jEdit `~` backups removed; real build `isabelle build -o document=false Blossom_Executable` exit 0
  (38 s); provenance strict ok (human 7505 lines 60.2%, ai 4956 lines 39.8%). Backup
  `backups/v2_stageB_wave1_2026-10-25/` (MD5SUMS). jEdit relaunched with no buffers; B1 started alone.

## v2 Stage B1 (Blossom_Misc, Graph_Quotient)
Method: for each theory a scratch copy with `iq.iq` (`.claude/scratch_b1/Scratch_*.thy`, static Stage A text) serves the REPL (prefix `b1`); every replacement was stepped there under the 10 s cap, then written to the real buffer.

### Blossom_Misc (done)
Rewritten (all REPL-checked first): Suc_le_length_iff_snoc2 (2 `by metis` -> `by (rule Suc_le_length_iff[THEN iffD1/iffD2])`), set_butlast_tl (metis -> `proof(cases l)` + `rev_cases` on the tail), dist_neq_path_eop (2 apply/by scripts -> `by (intro sucsuc; simp)`, `by (cases zs''; simp add: ...)`), dist_neq_append2 (apply+metis -> induction with `cases "n < length (xs @ ys)"; cases ys; auto`), dist_neq_split_2 (apply script -> `proof(induction xs1)` + `qed auto`), dist_neq_split_2' (2 apply scripts -> single `by` calls with `;`), construct_distinct_path (layout). No sledgehammer needed except one call on set_butlast_tl that found nothing (the structured proof was found by hand). Final PIDE check: is_processed true, running 0, unprocessed 0, finished 247, error_count 0; get_sorry_positions: none. Counts (metis/smt/meson/apply/blocks/proof -/same-line using-by) all 0. gate_stmts vs Stage A backup: 14/14 identical. Marker self-check (`prov2.py`): 0 unchanged human lines in an ai scope.

### Graph_Quotient batch 1 (saved; PIDE: processed, running 0, unprocessed 0, errors 0, warnings 30)
Finished lemmas (all replacements REPL-checked on a static scratch copy with `iq.iq`, `.claude/scratch_b1/Scratch_GQ.thy`, first): neq_Nil_conv_2, tl_distinct_rev, distinct_tl_then_butlast, two_mem_list_split, two_mem_list_split', one_mem_pure_suff, one_mem_pure_pref, two_mem_list_split'', split_list_pure_pref_suff, odd_cycle_nempty, match_blossom_alt_cycle, edge_in_quot_in_graph_1, edge_in_quot_in_graph_1', edge_of_path_in_graph_iff_in_quot, qug_path_iff_case_1_i (`{ }` block -> `have hl` with human body), path_is_quot_path_diff_u, qug_path_iff_case_1_ii, path_with_cycle_at_beginning, odd_cycle_hd_last_or, matching_odd_cycle_hd_last_unmatched, alt_path_vert_is_matched, not_in_quot_matching_not_in_matching, find_pfx_works_1, last_find_pfx_val, find_pfx_alt_list, edges_of_path_find_pfx, find_pfx_edges_of_path_alt_list, path_adj_verts_edge, in_quot_graph_neq_u, neq_u_notin_quot_graph, matching_edge_incident_on_cycle, edge_in_graph_edge_in_quot.
Evidence (library facts found, sledgehammer used only as discovery aid): the four list-split lemmas via `More_Lists.extract_first_and_last` (found through the sledgehammer hint `smt ... extract_first_and_last`; unification-bound timeouts of `auto`/`fastforce` avoided by explicit `of v1 p v2 Q`) and `split_list_last_prop`/`split_list_first_prop` with `bexI`; `matching_odd_cycle_hd_last_unmatched`: sledgehammer fact `alternating_list_odd_last inM`; `alt_path_vert_is_matched`: sledgehammer found nothing, the proof is a structured case split (`cases p''`, induction hypothesis instantiated with `ass.hyps[rule_format, of ...]`); `not_in_quot_matching_not_in_matching`: `cases p rule: edges_of_path.cases` (sledgehammer: only long metis lists); `find_pfx_alt_list`: new facts `nQ` and two last-equalities from `find_pfx_nempty`/`find_pfx_append`; the smt steps in `edge_in_quot_in_graph_1/1'` and `edge_in_graph_edge_in_quot` rebuilt by hand (image equations P ` e = e).
Other edits: the dead commented-out proof attempt `(*lemma edge_in_quot_in_graph_2: ... apply ... sledgehammer ... *)` was deleted (it contained `apply`; a comment, not a command); same-line `using ... by ...` split onto separate lines (layout script, 51 lines).

### Graph_Quotient batch 2 (saved; PIDE: processed, running 0, unprocessed 0, finished 5804, errors 0, warnings 32)
Finished lemmas: quot_is_matching (aux/aux2 facts for the crossing edges), card_quot_matching (three `; metis` steps -> explicit `uin`/`sin` facts and two `proof(intro ballI notI)` blocks), symm_diff_is_matching' (`apply (intro less)` with 6 `subgoal`s -> `proof(intro less, goal_cases)`; `matching_delete`, `matching_insert` instance), doubleton_quot (`card_2_iff`; chain `u notin quote` -> `quote subseteq s` -> `quote in M`), card_Vs_quotG (smt -> `eq`, `fin`, `cu`, `card_mono`), matching_quotM (edges_of_path_snoc instances; `dblton_E` for the crossing edge).
Evidence: sledgehammer on the `apply simp; metis` goal of symm_diff_is_matching' (A) returned `by auto/fast/blast`; the `last (edges ..)` steps were rebuilt from `edges_of_path_snoc`/`edges_of_path_append_3`; `fastforce` replaces `force` where `force` timed out (REPL cap) in `symm_diff_is_matching'` case 5.
Remaining: aug_path_works_in_contraction_unmatched_base, aug_path_works_in_contraction.

### Graph_Quotient batch 3 (final) and Stage B1 summary
Finished: aug_path_works_in_contraction_unmatched_base (535 lines, 17 metis, 2 smt, 3 meson, 16 apply lines; ~40 sites; two copies of the same block handled with identical edits) and aug_path_works_in_contraction (402 lines, 17 metis, 3 smt, 2 meson, 22 apply lines). Both replayed completely in the REPL (every step well under the 10 s cap) before the write.
Evidence: sledgehammer on the `apply simp; metis` goal of `symm_diff_is_matching'`, on the `ultimately have last (...)` step of `not_in_quot_matching_not_in_matching` and on three goals of the giants returned only long metis lists or nothing; the proofs were rebuilt from the facts named in the former metis calls, with new `have` facts where the metis call hid a chain: `stem_C_disj` (set C inter set stem = {}, one proof by `rev_cases` replaces two smt calls), `last p2 notin Vs (quotG M)` blocks (via `vert_in_graph_iff_in_quot_diff_u`), `edges_of_path_snoc` instances, `Berge[OF M'_finite _ _ dblton_E finite_Vs]`, `Berge_2[OF ...]`, `matching_unique_match`, explicit instances of `aug_path_works_in_contraction_unmatched_base'` (labels `aug_M'`, `alt_M'C`, `qaug`, `fin_qM'`, `match_qM'`, `sub_qM'`, `lastnin`, `memlast`, `Mhd` were added to Stage A statements so that the chain facts can be named; edits, no marker). `blast`/`auto` with many chained facts timed out in the REPL several times; those steps were rewritten with explicit instances (`use ... in blast`, `proof(intro ballI notI)`).
Final PIDE check (Graph_Quotient, buffer saved): is_processed true, running 0, unprocessed 0, finished 5940, error_count 0, warning_count 36; get_sorry_positions: none. Counts (file converted to ASCII in a scratch copy): metis 0, smt 0, meson 0, apply 0, `{`-blocks 0, `proof -`/`proof (` 0, same-line using/by 0, done 0, subgoal 0; gate_stmts vs Stage A backup: Graph_Quotient 89/89 identical, Blossom_Misc 14/14 identical. Marker self-check (`.claude/scratch_b1/prov3.py`: old and new labels computed, flag old=human and new=ai): 5 text coincidences for Graph_Quotient (`qed` x2, `by auto`, `then show ?thesis`, `by auto`), all of them NEW lines inside my own ai blocks that equal an old line textually (difflib alignment artefact, as in B4); 0 for Blossom_Misc.
Plan changes: none (no statement, definition, name or order changed). Deleted: one dead commented-out proof attempt `(*lemma edge_in_quot_in_graph_2: ... apply ... sledgehammer ... *)` (it contained `apply`), and added labels to some Stage A `have`/`moreover have`/`obtain` steps (see above). REPL b1 removed; scratch buffers `.claude/scratch_b1/Scratch_Misc.thy` and `Scratch_GQ.thy` are still open in jEdit (no close tool).

## v2 Gate B1 and Stage B close (orchestrator, 2026-10-25)
- B1: Blossom_Misc 14/14, Graph_Quotient 89/89 statements unchanged; all style counts 0; gate build
  exit 0. Provenance: 3 lines flagged by the line alignment (two `qed`, one `by auto`) are new lines
  closing or proving new ai blocks; one changed statement line labelled human restates a Stage A
  fact (`then have "hd p \<in> s" "last p \<in> s"` as a conjunction). The coder deleted a dead
  commented-out proof attempt (`(*lemma edge_in_quot_in_graph_2: ... sledgehammer ... *)`) and
  added labels to some human steps (edits). GREEN.
- Close: jEdit stopped; files ASCII, identical to the gated copies; `~` backups removed; clean build
  `isabelle build -c -o document=false Blossom_Executable` exit 0 (34 s); provenance strict ok
  (human 7233 lines 57.0%, ai 5451 lines 43.0%); whole session: no metis/smt/meson/sorry/oops, no
  `{ }` blocks, `apply` only in the style-guide templates of Find_Max_Matching, Find_Aug_Path,
  Compute_Alt_Path. Backups `backups/v2_stageB_green_2026-10-25/` and in the project memory dir;
  coder scratch dirs archived (`.../backups/v2_scratch_tools/claude_scratch_dirs.tgz`) and removed.
STAGES A AND B GREEN.

## v2 relabelling by user decision (2026-10-25)
- User: program definitions based on the original are `ai_human`; edited copies are `human`.
- `ai_human` (marker on the definition): last_edge_matched, matched_to_cycle; the loops
  Find_Max_Matching, Find_Aug_Path, Compute_Alt_Path with their _impl twins, initial states and
  _run/_run_impl; quotient_vertex, quotient_edges, contract_vertices, contract_graph,
  contract_matching, lift_path, augmenting_path; free_vertices, initial_labels, alternating_paths;
  fresh_nat. The user set the header of Find_Max_Matching to `provenance ai_human` (whole theory).
- `human` (edited copies of the original): definitions choose_con_vert, stem2vert_path, replace_cycle,
  refine, compute_match_blossom; statements of stem2vert_path_def', replace_cycle_def' (the original
  defining equations), common_suffix (= compute_alt_path_res_from_tree), compute_alt_path_specD
  (= the clause lemma of compute_match_blossom'); their proofs stay ai. Found by token similarity of
  every ai/ai_human statement and proof against the original theories, then checked by hand.
  Rewritten proofs (Stage B translations of original proofs) stay ai, as agreed.
- Build exit 0; provenance strict ok: human 7283 lines (57.4%), ai_human 399 (3.1%), ai 5002 (39.4%).
  Backup `backups/v2_relabelled_2026-10-25/`.

## v2 relabelling of the copied theories by user decision (2026-10-25)
- User: in the copied theories, copied or edited text is `human`, created text is `ai` (no `ai_human`).
- Method (`plan_v2/scripts/relabel/`): every command of Blossom_Misc, Graph_Quotient,
  Graph_Quotient_Lifting, Blossom_Prefixes, Compute_Alt_Path_Invars aligned with the original
  theories (difflib on normalised command texts); identical or edited (token similarity >= 0.5 to a
  nearby original command, or to any original command of the same kind for longer commands) ->
  human; otherwise created -> ai; the whole proof of a created lemma is created. Explicit: the four
  lifting definitions and the statements of stem2vert_path_def'/replace_cycle_def' are edited copies
  (human); last_edge_matched and matched_to_cycle are created (ai).
- Each theory now starts with `provenance human`; markers only where the label changes (1477 markers,
  placed by a model of the marker scoping, verified against `isabelle ai_provenance`: 0 mismatches).
  Text identical apart from labels. Build exit 0; provenance strict ok.
- Copies: human 7811 lines, ai 1570; session: human 7830 (61.8%), ai_human 394 (3.1%), ai 4456 (35.1%).
- Incident: a script bug (file opened for writing before it was read) emptied the five files for
  about a minute; restored from `backups/v2_before_copy_relabel/` (identical to the last good state)
  and redone. Backup of the result: `backups/v2_copies_relabelled_2026-10-25/`.

## Phase 10 (linear-time fixes) - 2026-10-25

- The user's jEdit occupies the I/Q instance, so the orchestrator did this phase by batch builds of
  scratch copies (session BXF, then BXT with 15 `by eval` tests), then wrote the two files to disk
  (base = HEAD, checked before writing). Backup: `backups/v2_before_linear_fixes_2026-10-25`.
- Graph_Quotient_Lifting: `pref_suf_rev`, `pref_suf_rev_eq`, `pref_suf_code [code]` (ai).
- Find_Aug_Path_Subprocedures: `longest_disj_sfx`, `longest_disj_sfx_split`, `last_find_pfx_in_set`,
  `find_pfx_first`, `longest_disj_pfx_first_common`, `longest_disj_pfx_common_sfx`,
  `common_suffix_disj_iff`, `longest_disj_pfx_rev` (ai); `compute_match_blossom` edited (human);
  both soundness proofs adapted (ai).
- Repairs during scratch builds: two forward text references removed; `longest_disj_sfx_split`
  step case given explicit witnesses; `last_find_pfx_in_set` by cases on the tail; `l1 \<noteq> []`
  made explicit in `longest_disj_pfx_first_common`; one `rule` replaced by `using ... by simp`.
- Generated SML: `pref_suf` calls `pref_suf_rev`; `compute_match_blossom_impl` uses `last` and
  `longest_disj_sfx`; `longest_disj_pfx` no longer occurs in the code.
- Final: real build of Blossom_Executable green (0:00:33); provenance human 60.9%, ai_human 3.1%,
  ai 36.1%; outside the two theories every label is unchanged.

## Phase 11 (provenance of mechanical transformations) - 2026-10-25

- Label definitions extended (AI_Provenance/Provenance.thy, system_prompt.md): semantic
  contribution required for ai/ai_human; mechanical work keeps the source's label.
- Block rewrite (scratch v4, `blocks.py` + hand fixes): 25 block-derived haves -> `have ... if ... for`;
  hand fixes: d1 premise stated with `hd p2` (the defined `a2'` is not available in `if`),
  p_nempty_even gets its last premise from the former `moreover assume odd_length`
  (`moreover note odd_length`), `hl` of Graph_Quotient as two statements with `if`.
- Relabel: 132 scaffolding commands of apply-to-Isar conversions (`scaffold.py`) and the block
  rewrites -> human; markers recomputed minimally (`relabel.py`), 0 mismatches; the user's
  ai_human labels in Graph_Quotient_Lifting kept. Backup: `backups/v2_before_block_relabel_2026-10-25`.
- Checks: scratch build BXR and real build green; strict provenance: human 62.5%, ai_human 3.5%,
  ai 34.1% (before: 60.9 / 3.1 / 36.1). Copied theories: Misc 88.9% human, Graph_Quotient 88.9%,
  Lifting 76.6% (+1.8% ai_human), Prefixes 96.3%, Invars 86.9%.

## Phase 12 (provenance audit of the whole session) - 2026-10-25

- Trigger: `path_find_pref` had AI-written proof steps labelled human (the earlier text-similarity
  classifier counted them as edits). Audit of all 11 theories against the original Blossom
  theories (`plan_v2/scripts/relabel/audit2.py`), lemma by lemma: a statement is human iff its
  propositions occur in the original lemma (after the systematic renamings, `let`/`define`
  abbreviations, and in the lifting theory the `chv` adaptation of the d1 blocks); the proof of a new
  statement is ai; a proof that replaced an original metis/smt/meson one-liner is ai; verbatim
  copies are human; user decisions (ai_human labels, the edited copies) kept.
- Result: 560 commands human -> ai (new statements, e.g. choose_vert_works_3, hd_find_pfx,
  find_pfx_hd, distinct_find_pfx_cycle, search_invarsD/_if1/_if2_sound, the steps of metis
  replacements), 10 ai -> human (copied statements). The AI theories needed no change.
- Markers recomputed (`relabel5.py`), 0 mismatches; text without markers unchanged. Backup:
  `backups/v2_before_audit_relabel_2026-10-25`. Real build green; strict provenance: human 58.3%,
  ai_human 3.5%, ai 38.3%.

## Phase 13 (scaffolding and metis-replacement relabel) - 2026-10-25
- User question: "line 1546 says provenance ai ... 'qed'?" (Graph_Quotient_Lifting): the marker labelled
  the `qed` closing the copied proof of `append_works`; a leftover of the first (difflib) relabel, which
  matched short generic commands (qed, next, case, show ?case, using assms) by text, and of the audit
  (Phase 12), which kept the labels of generic commands. User: "yes, fix them".
- Method (`plan_v2/scripts/relabel/audit3b.py`, on top of audit2): every goal of a copied lemma is mapped
  to its original goal (aligned text; same conclusion, with the chv adaptation; ?thesis/?case steps and
  subgoals of apply scripts by position; a rewritten { } block maps to its last statement). A structured
  proof is copied (same `proof` method), mechanical (its method is the first method of an original
  `apply`: apply script rewritten as Isar), or new. Scaffolding (proof, qed, next, case, then/moreover/...,
  ?thesis/?case steps) takes the label of its proof; a new proof is ai except copied statements,
  verbatim proofs and verbatim runs of >= 3 commands. A step that replaced an original metis/smt/meson
  call (the mapped step or subgoal) is ai, apart from verbatim copied `using` facts; a terminal proof that
  is verbatim or mechanically rewritten (same methods, same facts) is human. 14 manual decisions (two
  metis replacements in the d1 block, the AI proofs of stem2vert_path_def'/replace_cycle_def' (statements
  stay human), two qed of new proofs, one apply script rewritten as Isar).
- 381 commands relabelled (human->ai 175, ai->human 206); the scan for scaffolding labelled unlike its
  proof went from 192 to 2 (a copied `then show ?thesis` block inside a new proof, correct).
- Markers recomputed (`relabel6.py`), 0 mismatches; text and line numbers unchanged. Backup:
  `backups/v2_before_scaffold_relabel_2026-10-25`. Real build green (34 s); strict provenance: human 58.4%,
  ai_human 3.5%, ai 38.1%. Not committed.
- Follow-up (user: "yes, relabel the six statements human"): the six `have cvw: "chv \<in> set (rev C)" ...`
  statements in Graph_Quotient_Lifting (1097, 1160, 1598, 1667, 2152, 2221) are the original
  `choose_vert_works` statement of `d1`, moved to the call sites and instantiated with `rev C`: human;
  their proofs (via choose_vert_works_3, replacing the original metis call) stay ai. Build green;
  strict provenance: human 58.5%, ai_human 3.5%, ai 38.1%.
- Follow-up (user: "yes, relabel them; keep disj and pfxs ai"): in alt_list_replace_cycle, `alt_p1hd` (line
  966) and `alt_p1` (973) are the implicit first subgoals of the original `apply(intro alt_list_append_3)`
  and `apply(rule alt_list_append_2)`, written out with the subgoals' original proofs (the original metis
  calls even cite them as cartouches): statements, scaffolding, verbatim steps and the glue
  `by (rule alt_p1)`/`by (rule alt_p1hd)` human (26 commands); the replacements of the smt/metis calls
  stay ai. A scan of all ai statements against all original statements up to instantiation (51 matches)
  found no other moved copy; `disj`/`pfxs` in Find_Aug_Path_Subprocedures stay ai (user). Build green;
  strict provenance: human 58.7%, ai_human 3.5%, ai 37.9%.

### Phase 14 (2026-10-26): copied theories human, metis/smt/meson replacements ai

User decision: the five copied theories (Blossom_Misc, Graph_Quotient, Graph_Quotient_Lifting,
Blossom_Prefixes, Compute_Alt_Path_Invars) are labelled human; only the replacements of
metis/smt/meson calls of the original theories are ai (user ai_human labels kept). Supersedes the
Phase 12/13 rules (new statements/proofs ai, scaffolding follows its proof).

- Unit of a replacement: the whole proof of the step whose original proof contained the call
  (`using`/`unfolding` lines included), with every command inside it; the step's statement stays
  human. Local facts added only for a replacement (e.g. `aux`, `stem_C_disj`, `hds`) are ai;
  apply scripts rewritten as Isar with the same first method keep their scaffolding human.
- Calls mapped through the audit3b goal map (281 of 337) plus a manual review of the rest
  (`plan_v2/scripts/relabel/manual.txt`); every original call is covered or was dropped
  (the `obtain ... sel_if1` steps, now hypotheses of `search_invars_if1`).
- Result: no human command inside an ai proof; 404 commands ai -> human, 148 human -> ai.
  Text unchanged (markers only); build green (25 s); strict provenance passes.
  Session: human 60.9% / ai_human 3.5% / ai 35.7% of lines.
- Backup: `backups/v2_before_simple_relabel_2026-10-26/`.
