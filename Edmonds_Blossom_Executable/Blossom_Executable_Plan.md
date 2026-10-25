# Plan v2: a self-contained executable Edmonds blossom algorithm

> **STATUS (2026-10-25, 02:50): STAGES A AND B GREEN.** Self-contained session
> `Blossom_Executable` (parent `Basic_Matching`, no theory of `Blossom` imported) builds from
> scratch (`isabelle build -c -o document=false Blossom_Executable`, exit 0, 34 s; includes `value`
> and `export_code`); 11 theories, 13730 lines, ASCII. No `metis`/`smt`/`meson`/`sorry`/`{ }`
> blocks anywhere; `apply` only in the style-guide templates of the ai loop theories. Provenance
> strict ok: human 7233 lines (57.0%), ai 5451 lines (43.0%). Backup
> `backups/v2_stageB_green_2026-10-25/` (MD5SUMS). Pending user decisions: the Stage B scope
> (section 6b) and the removal of the abstract session `Blossom`.

## 1. Goal and user decisions (2026-10-24)

- "Reduce redundancy, i.e. the same algorithm should not be done twice: once abstract and
  another executable." The session `Blossom_Executable` becomes **self-contained**: it does not
  import the session `Blossom`. The human theories it needs are **copied** into it, and their
  proofs are modified "to deal with the new constants and fit the standard style".
- Provenance: copied lines keep the label `human`; a proof that is rewritten gets an `ai`
  marker on its `proof`/`apply`/`by` (rule 3); new material is `ai`.
- "When you make the copy, functions should retain their names." The loops take the original
  names, capitalised: `Find_Max_Matching`, `Find_Aug_Path`, `Compute_Alt_Path`. The lifting
  functions keep `choose_con_vert`, `stem2vert_path`, `replace_cycle`, `refine`; the blossom
  procedure keeps `compute_match_blossom`; the subprocedure parameters keep `aug_path_search`,
  `blos_search`, `create_vert`, `compute_alt_path`.
- "The abstract blossom version should be removed, after everything is done and I am
  satisfied." Until then `Edmonds_Blossom_Algorithm/` and its `ROOTS` line stay untouched.
- "Backup the executable version, write a plan, and execute it in the usual way" (one-shots in
  the plan, coders copy and repair, orchestrator gates and reports per phase).

## 2. Design

### 2.1 The session

`session Blossom_Executable = Basic_Matching +`, sessions `AI_Provenance Data_Structures
Directed_Set_Graphs Undirected_Set_Graphs Graph_Algorithms_Dev`, `document = false`. Theories in
dependency order (the ROOT lists a theory only after its gate):

| # | Theory | Origin | Labels | Imports |
|---|---|---|---|---|
| 1 | `Blossom_Misc` | verbatim copy of `Blossom_Misc` | human | `Undirected_Set_Graphs.Paths` |
| 2 | `Graph_Quotient` | copy of `Graph_Quotient` lines 1-1069 and 3308-5022, without the choice function | human (+ ai proofs) | `Undirected_Set_Graphs.Pair_Graph_Berge_Adaptor`, `Undirected_Set_Graphs.Undirected_Set_Graphs`, `Basic_Matching.Berge` |
| 3 | `Graph_Quotient_Lifting` | executable lifting functions (new) + copy of `Graph_Quotient` lines 1070-3307 | ai preamble, human body | `Graph_Quotient Blossom_Misc` |
| 4 | `Blossom_Prefixes` | copy of `Blossom_Algo_Contraction` (result datatype, lines 340-375, 528-1436) and of `compute_alt_path_spec` (`Blossom_Algo_Compute_Aug_Path` lines 13-39) | human | `Graph_Quotient Blossom_Misc` |
| 5 | `Compute_Alt_Path_Invars` | copy of `Blossom_Algo_Search` without the abstract function + the v1 state-level lemmas | human body, ai tail | `Graph_Algorithms_Dev.Parent_Map Blossom_Prefixes` |
| 6 | `Graph_Matching_Specs` | v1 green theory, unchanged | ai | as v1 |
| 7 | `Find_Max_Matching` | v1 `Edmonds_Blossom_Top_Loop`, renamed | ai | `Graph_Matching_Specs` |
| 8 | `Compute_Alt_Path` | v1 `Alternating_Forest_Search`, renamed, abstract part moved to 5 | ai | `Graph_Matching_Specs Compute_Alt_Path_Invars` |
| 9 | `Find_Aug_Path` | v1 `Blossom_Shrinking_Search`, renamed, lifting by `refine` | ai | `Graph_Matching_Specs Graph_Quotient_Lifting Blossom_Prefixes` |
| 10 | `Find_Aug_Path_Subprocedures` | v1 `Edmonds_Blossom_Subprocedures`, renamed (`compute_match_blossom`) | ai | `Find_Aug_Path` |
| 11 | `Edmonds_Blossom_Example` | v1 example, renamed, without code overrides | ai | `Find_Max_Matching Find_Aug_Path_Subprocedures Compute_Alt_Path Directed_Set_Graphs.Pair_Graph_RBT` |

### 2.2 No algorithm twice

Not copied, because the executable loops replace them: the abstract `find_max_matching`
(`Blossom_Algo_Main_Loop`), `find_aug_path` and its soundness/completeness proofs
(`Blossom_Algo_Contraction` lines 13-338, 376-522), the abstract `compute_alt_path` function and
its induction proofs (`Blossom_Algo_Search`: the function, `compute_alt_path_dom`,
`compute_alt_path_from_tree_1`, `compute_alt_path_from_tree_2`, the `_sound`/`_complete` lemmas,
the `compute_alt_path_use` locale), and the abstract `compute_match_blossom` with its
interpretation proofs (`Blossom_Algo_Compute_Aug_Path` lines 41-374). The theory `choose` is not
needed any more. Copied are only mathematics: graph quotients, the lifting of augmenting paths,
blossom prefixes, the invariants of the alternating-forest search and their preservation.

### 2.3 Changes made in the copies (all by script, `plan_v2/scripts/`)

- `Graph_Quotient`: locale `quot = graph_abs E + fixes s u assumes good_quot_map` (the parent
  `pre_quot = choose sel + ...` and the parameter `sel` removed); `rev_P`, `sel'`,
  `rev_map_works_1/2`, `rev_map_map`, `quot_alt_path_iff_alt_path` removed (they exist only for
  `sel`); `path_is_quot_path`/`path_is_quot_path'` now conclude `path E p` (ai proofs); five
  general lemmas of the lifting part (`in_quot_graph_neq_u`, `Vs_quotG_subset_Vs_quot_graph`,
  `in_quotG_neq_u`, `neq_u_notin_quot_graph`, `neq_u_notin_quotG`) moved before line 3308 into a
  `context quot`, because the contraction part uses them. Batch-checked: builds.
- `Graph_Quotient_Lifting`: see 2.4. Not yet checked (Phase 2 does it).
- `Blossom_Prefixes`: verbatim pieces; import `Blossom_Misc` added (for `set_butlast_tl`,
  `numeral_4_eq_4`). Batch-checked: builds.
- `Compute_Alt_Path_Invars`: locale `compute_alt_path = match G M` (the parent `choose sel`
  removed); the abstract function and the lemmas about it dropped (2.2);
  `compute_alt_path_from_tree_2'` restated at a state: its premise
  `compute_alt_path ex par flabel = None` is replaced by `\<not> if1_cond flabel ex` and
  `\<not> if2_cond flabel`, and its proof is the base case of the original induction. The v1 lemmas
  `search_invars`, `search_invars_init`, `search_invars_if1`, `search_invars_if2_sound`,
  `search_invars_complete` (v1 `Alternating_Forest_Search` lines 21-222) are appended as an ai
  section. Batch-checked: builds.

### 2.4 The lifting functions

Global, executable functions, parameterised by an adjacency test `adj` and a mate function
`mate`, with the original names (ai):
`choose_con_vert adj C v` (first vertex of the list `C` adjacent to `v`), `stem2vert_path adj mate
C v`, `replace_cycle adj mate C p1 p2` (lazy `if`, no `let`), `refine adj mate u C p`, the
helpers `last_edge_matched`, `matched_to_cycle`, and the human function `pref_suf` moved out of
the locale (so it has code equations).

```
locale quot_lift = quot E s u for E :: "'a set set" and s u +
  fixes adj :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and mate :: "'a \<Rightarrow> 'a option" and M :: "'a set set"
    and C :: "'a list"
  assumes adj_E: "\<And>v w. adj v w \<longleftrightarrow> {v, w} \<in> E"
      and mate_M: "\<And>v w. mate v = Some w \<longleftrightarrow> {v, w} \<in> M"
      and M_subset_E: "M \<subseteq> E" and s_cycle: "s = Vs E - set C"
      and u_fresh: "u \<notin> Vs E" and hd_last_cycle: "hd C = last C"
```

In this locale the functions satisfy the defining equations of the originals
(`stem2vert_path_def'`, `replace_cycle_def'`, ai, batch-checked). The copied body (original
lines 1070-3307, `context quot` -> `context quot_lift`) therefore uses `stem2vert_path_def'` and
`replace_cycle_def'` where the original used the definitions; `choose_con_vert (set C)` became
`choose_con_vert adj C`, `stem2vert_path C M` -> `stem2vert_path adj mate C`,
`replace_cycle C M` -> `replace_cycle adj mate C`, `refine C M` -> `refine adj mate u C`; the two
uses of `sel` (in `choose_vert_works_1/2`) are replaced by `choose_con_vert_props` (ai). `M` and
`C` are now parameters of the locale; their free occurrences in the statements refer to them.
The final theorem keeps its statement:

```
theorem refine_works:
  assumes cycle: "blossom E M stem C" and
    quot_aug_path: "graph_augmenting_path (quotG E) (quotG M) p'" and
    matching: "matching M" "M \<subseteq> E" and
    quot: "s = (Vs E) - set C"
  shows "graph_augmenting_path E M (refine adj mate u C p')"
```

`Find_Aug_Path` interprets `quot_lift (ugraph_abs E) (Vs (ugraph_abs E) - set C) u
(\<lambda>v. isin (Graph.neighbourhood E v)) (mate_lookup N) (matching_abs N) C` (lemma
`quot_lift_here`) and uses `refine_works` directly (`refine_correct`). This removes v1's choice
function `cycle_sel`, the bridge lemmas `cycle_path_eq`, `replace_cycle_eq`, `lift_one_eq`, and
the code overrides of the v1 example (`pref_suf_list`, `lift_one_rbt_code`,
`replace_cycle_rbt_code`).

### 2.5 Pre-check of the one-shots (orchestrator, scratch sessions outside the repository)

- Copies 1, 2, 4, 5: batch build clean.
- 6-11 against a stub of 3 (its ai preamble, checked, plus `refine_works` by `sorry`,
  `quick_and_dirty`): batch build clean, including `value` and `export_code` in the example.
- 3 (full): the batch build did not finish within 20 minutes; two commands were still running
  after 170 s: line 426 of the one-shot file (`by (smt find_pfx.elims hd_rev list.sel(1))` in `hd_stem2vert_path`)
  and line 2226 (a `metis` in `hd_nin_last_nin_replace_cycle`, the step
  `hd (stem2vert_path adj mate C (hd p2) @ p2) = hd C`). Errors in the rest of the body are
  unknown. Phase 2 is the only phase expected to need real repair work.

### 2.6 Naming (settled)

Loops: locale, function, record (`<Name>_state`), `_impl`, `_run`, `_run_impl`, `_axiom`,
`_call_i_conds`, ... as in v1 with the new names. Subprocedure locale (as `BFS_subprocedures`):
`Find_Aug_Path_subprocedures`, constant `compute_match_blossom`, lemmas
`compute_match_blossom_sound_path`, `compute_match_blossom_sound_blossom`,
`compute_match_blossom_complete`, `lemmas compute_match_blossom = ...`. Example interpretations
(lower-case names): `gm`, `compute_alt_path`, `find_aug_path_subprocedures`, `find_aug_path`,
`find_max_matching`, `find_max_matching_proofs`; defined constants `compute_alt_path_run_impl`,
`compute_match_blossom_impl`, `find_aug_path_run_impl`, `find_max_matching_run_impl`, ...;
final lemmas `edmonds_blossom_correct_1/2` (names kept from v1).

## 3. Settled decisions carried over from v1 (Amendment A of the v1 plan)

- A0 REPL-first: an UNCHECKED one-shot is replayed in the REPL before it enters a jEdit buffer.
  Exempt: one-shots marked "pre-checked" in their phase (their batch build is clean, so no
  command diverges); they may be opened in jEdit directly.
- A1: `Graph_Matching_Specs where lookup = lookup and mate_empty = mate_empty` with
  `mate_empty :: 'mate` in the `for` clause. Already in the one-shots.
- A2: twin lemmas unfold `<loop>_impl.simps` once with `subst`. Already in the one-shots.
- The variable `es` is avoided (it is a constant of `Compute_Alt_Path_Invars`); v1 uses `rest`.

## 4. Coder protocol (v2)

The coder follows `.claude/agents/coder.md`, with these v2 rules:
1. The one-shot of a theory is `plan_v2/oneshots/<Theory>.thy.oneshot`. Copy it VERBATIM (do not
   read it into your context in full; generate the I/Q args JSON from the file with a short
   Python call and send it with `.claude/iq/iq_call.py open_file <args.json>`).
2. Scratch theories import session theories by qualified name, e.g.
   `imports Blossom_Executable.Graph_Quotient Blossom_Executable.Blossom_Misc iq.iq`.
3. **Human material.** Do not restyle human proofs in Stage A. A human proof that checks stays
   as it is, even with `metis`/`smt`/`apply`. A human proof step that fails is repaired; the
   repaired step gets `\<^marker>\<open>provenance ai\<close>` directly after its keyword (`by`, `apply`,
   `proof`, or `have`/`show` for an inserted step with its sub-proof), and it must not use
   `metis`, `smt` or `meson`. Never change a `provenance` command and never relabel a line.
   A human statement may change only as a PLAN CHANGE (minimal, with the reason).
4. **ai material** follows coder.md section 5 in full (no `metis`/`smt`/`meson`, `apply` only
   in templates).
5. Theory files are written only through I/Q; ROOT, ROOTS, the plan and the one-shot files are
   the orchestrator's.

## 5. Gates (orchestrator, per phase)

1. Coder report and progress.md read; PIDE result 0 errors, nothing running, no `sorry`.
2. The jEdit buffer of the theory is closed or jEdit is stopped before any disk edit.
3. Statement check: every lemma/definition statement equals the one-shot's, except reported
   PLAN CHANGEs (script diff); for copies, the one-shot's statements equal the originals up to
   the substitutions of 2.3/2.4.
4. No `sorry`/`oops`; no `metis`/`smt`/`meson` in ai-labelled commands.
5. The theory is added to ROOT; gate build clean: `plan_v2/scripts/gate_build.sh` builds ASCII
   copies of the ROOT's theories as a scratch session `BXG` (batch Isabelle does not read
   jEdit's glyphs, and I/Q cannot close a buffer, so the real files are converted to ASCII only
   in Phase 9 with jEdit stopped; then `isabelle build Blossom_Executable` runs on them).
6. `isabelle ai_provenance -s -t` on the gate session passes.
7. Backup of the gated theory in `backups/`; state recorded here and in progress.md.

## 6. Phases

Stage A makes the session self-contained and green. Stage B restyles the copied proofs.

| Phase | Theories | One-shot state | Depends on | Coder work expected |
|---|---|---|---|---|
| 1 | `Blossom_Misc`, `Graph_Quotient` | pre-checked | - | land and check |
| 2 | `Graph_Quotient_Lifting` | NOT checked; preamble checked | 1 | repair the copied body (REPL-first) |
| 3 | `Blossom_Prefixes`, `Compute_Alt_Path_Invars` | pre-checked | 1 | land and check |
| 4 | `Graph_Matching_Specs`, `Find_Max_Matching` | pre-checked | - | land and check |
| 5 | `Compute_Alt_Path` | pre-checked | 3, 4 | land and check |
| 6 | `Find_Aug_Path` | pre-checked against the stub of 2 | 2, 3, 4 | land and check |
| 7 | `Find_Aug_Path_Subprocedures` | pre-checked against the stub of 2 | 6 | land and check |
| 8 | `Edmonds_Blossom_Example` | pre-checked against the stub of 2 | 5, 7 | land and check (value, export_code) |
| 9 | (orchestrator) | - | 1-8 | clean session build, provenance, ROOT/ROOTS, report |
| B1-B4 | restyle `Graph_Quotient` (+`Blossom_Misc`), `Graph_Quotient_Lifting`, `Blossom_Prefixes`, `Compute_Alt_Path_Invars` | - | Stage A | replace `metis`/`smt`/`meson`, non-template `apply`, `{ }` blocks; statements unchanged; rewritten proofs get the ai marker |

### Phase 2 (`Graph_Quotient_Lifting`): instructions

- Scratch theory: `imports Blossom_Executable.Graph_Quotient Blossom_Executable.Blossom_Misc iq.iq`.
  Replay the one-shot body in the REPL top-level command by top-level command. The preamble (up to
  the first `end`, i.e. the definitions, `pref_suf`, `quot_lift` and its five lemmas) is
  checked; replay it as is.
- Expected trouble: proofs that unfold `stem2vert_path_def'`/`replace_cycle_def'` and then use
  `metis`/`smt` with facts about the old shape, in particular one-shot lines 426 and 2226 (2.5). Useful
  facts of the preamble: `choose_con_vert_props`, `last_edge_matched_iff`,
  `matched_to_cycle_iff`, `stem2vert_path_def'`, `replace_cycle_def'`, the locale assumptions
  `adj_E mate_M M_subset_E s_cycle u_fresh hd_last_cycle`.
- The statements of the copied lemmas are authoritative. If a copied lemma is false in the new
  setting (e.g. a lemma stated for an arbitrary list that now only holds for the locale's `C`),
  make the minimal PLAN CHANGE and report it; `refine_works` must keep its statement, since
  `Find_Aug_Path` uses it.

### Phases 1, 3-8: instructions

The one-shots are pre-checked: open the theory through I/Q with the one-shot as content, save,
check (coder.md section 3). Repair only what fails in PIDE (should be nothing; report anything).

## 6b. Stage B: restyling the copied human theories

**Scope (orchestrator decision, to be confirmed by the user at the end).** The copies are brought
to the project rules (style guide 5.6) and the layout rules (5.5): no `metis`, `smt`, `meson`;
no `apply` (the copies contain none of the 5.6 templates); no `{ ... }` blocks; `using`/`by` on
their own lines; `proof-`/`proof(` without a space. A proof that is rewritten follows 5.1-5.3
(one automatic call where possible, otherwise a short structured proof). A human proof that
already satisfies 5.5 and 5.6 is left as it is, even if it has labelled steps or `[OF]`
chains: rewriting those as well would replace most of the human text by ai text.

**Invariant.** Statements, definitions, lemma names and their order stay exactly as in Stage A
(gate: `gate_stmts.py` against `backups/v2_stageA_green_2026-10-24/<Theory>.thy`).

**Provenance.**
- A proof step whose method is replaced gets the marker on that command
  (`by \<^marker>\<open>provenance ai\<close> (auto ...)`).
- An `apply` script or a `{ }` block replaced by a structured proof gets the marker on the new
  opener (`proof \<^marker>\<open>provenance ai\<close>(induction ...)`, `have \<^marker>\<open>provenance ai\<close> ...`);
  its scope is then entirely new text.
- Layout-only edits (moving `using`/`by` to their own line, `proof -` -> `proof-`) are edits:
  no marker, the label stays human.
- The gate checks that no unchanged human line lies in an ai scope.

**Protocol.**
- jEdit is restarted with no buffers open before each wave. The coder opens only its theory.
- For each lemma to restyle, the coder initialises the REPL at the lemma in the open theory
  (`repl_init_from_source`), finds and checks the new proof there (sledgehammer only as a
  discovery aid; never keep metis/smt/meson), and collects the replacements.
- The replacements go into the buffer in batches of about 10-15 lemmas (`write_file`
  str_replace, or a full-buffer replacement computed by a script from the current buffer text),
  followed by save and a PIDE check.
- After each batch the coder appends to progress.md the lemmas it has finished, so that a
  successor can resume. If its context runs short, the coder finishes the current batch, saves,
  checks, and reports "partial" with the next lemma.
- `.claude/scratch_c2v2/` holds the Phase 2 coder's REPL tools (persistent I/Q client `iqc.py`,
  `fine.py` to split long proofs into REPL steps, `replay_all.py`); they may be reused.

**Waves.**
- Wave 1: B2 `Graph_Quotient_Lifting` and B3 `Blossom_Prefixes`, in parallel (they are
  independent of each other).
- Gate, with jEdit stopped: ASCII conversion, real build, provenance; then a restart.
- Wave 2: B1 `Blossom_Misc` + `Graph_Quotient`, and B4 `Compute_Alt_Path_Invars` (its human
  part), in parallel. B1 writes its buffer rarely, because each write makes PIDE re-check the
  open B4 theory.
- Gate.

**Gate B (per theory).**
- Statements unchanged.
- Zero `metis`/`smt`/`meson`/`apply`/`{`-blocks/`proof -`.
- No `using`/`by` after the statement or `have` on the same line.
- No unchanged human line in an ai scope.
- Gate build clean, provenance strict ok.

## 7. Risks known in advance

- Phase 2 may take long: 2446 lines, 90 `metis`, 9 `smt` in the human body.
- One jEdit instance (port 8768) serves all coders; heavy theories (`Graph_Quotient` 90 s,
  `Compute_Alt_Path_Invars` 50 s of batch time) slow down PIDE. At most two coders at a time.
- PIDE runs with logic `Blossom` (heap of the abstract session, for its ancestors): no theory of
  `Blossom_Executable` may import a theory of `Blossom`; the gate's batch build (parent
  `Basic_Matching`) checks this.

## 8. Baseline facts

- Isabelle2025-2, `USER_HOME=/media/llms/isabelle-home-blossom`, jEdit/I/Q port 8768, token
  `blossom`, bridge `.claude/iq/mcp.py`/`iq_call.py`.
- Sizes of the one-shots: Blossom_Misc 135, Graph_Quotient 2780, Graph_Quotient_Lifting 2445,
  Blossom_Prefixes 988, Compute_Alt_Path_Invars 2702, Graph_Matching_Specs 341,
  Find_Max_Matching 337, Compute_Alt_Path 1547, Find_Aug_Path 1114,
  Find_Aug_Path_Subprocedures 198, Edmonds_Blossom_Example 229 lines.
- Proof debt of the copies (Stage B): metis/smt/meson/apply-lines = Blossom_Misc 4/0/0/9,
  Graph_Quotient 85/16/10/77, Graph_Quotient_Lifting 90/9/0/63, Blossom_Prefixes 52/2/2/27,
  Compute_Alt_Path_Invars 54/17/3/86.

## Phase status

| Phase | State |
|---|---|
| 1 | **green** 2026-10-24 (PIDE: Blossom_Misc 233 / Graph_Quotient 5637 commands, 0 errors; text identical to the one-shots; gate build of ASCII copies clean; provenance strict ok: Graph_Quotient 99.4% human, 0.6% ai) |
| 2 | **green** 2026-10-24 (PIDE 5124 commands, 0 errors; no plan changes; 9 copied proofs repaired, 5 ai helper lemmas; all 53 one-shot statements unchanged; markers corrected at the gate so that no unchanged human line is labelled ai; no ai metis/smt/meson; gate build clean; 82.2% human) |
| 3 | **green** 2026-10-24 (PIDE: Blossom_Prefixes 2004 / Compute_Alt_Path_Invars 5198 commands, 0 errors; texts identical to the one-shots; gate build clean; provenance strict ok: Compute_Alt_Path_Invars 92.6% human, 7.4% ai) |
| 4 | **green** 2026-10-24 (PIDE: Graph_Matching_Specs 463 / Find_Max_Matching 354 commands, 0 errors; text identical to the one-shots; gate build clean; provenance strict ok, 100% ai) |
| 5 | **green** 2026-10-24 (PIDE 1874 commands, 0 errors; text identical to the one-shot; gate build clean; provenance strict ok, 100% ai) |
| 6 | **green** 2026-10-24 (PIDE 1351 commands, 0 errors; text identical to the one-shot; gate build clean; 100% ai) |
| 7 | **green** 2026-10-24 (PIDE 292 commands, 0 errors; text identical to the one-shot; gate build clean; 100% ai) |
| 8 | **green** 2026-10-24 (PIDE 135 commands; value: perfect matching [(0,1),(1,0),(2,3),(3,2),(4,5),(5,4)], 0 errors; text identical to the one-shot; gate build clean; 100% ai) |
| 9 | **green** 2026-10-24 (jEdit stopped; real files converted to ASCII, byte-identical to the gated copies; clean build exit 0; provenance strict ok; backup `backups/v2_stageA_green_2026-10-24/` with MD5SUMS) |
| B3 | **green** 2026-10-25 (PIDE 1948 commands, 0 errors; 33/33 statements unchanged; metis/smt/meson/apply/blocks/same-line using-by/`proof -` all 0; 21 proofs rewritten; no unchanged human line in an ai scope; human 843 / ai 132 commands) |
| B2 | **green** 2026-10-25 (PIDE 5416 commands, 0 errors, 0 warnings; 58/58 statements unchanged; all counts 0; 24 proofs rewritten; composed statements of former `{ }` blocks marked ai with human-restored copied bodies; no unchanged human line in an ai scope; human 1972 / ai 740 commands) |
| B4 | **green** 2026-10-25 (PIDE 0 errors; 107/107 statements unchanged; all counts 0; 36 lemmas + 1 interpretation rewritten; 7 `{ }` blocks as ai statements with human-restored bodies; no unchanged human line in an ai scope; human 2125 / ai 692 commands) |
| B1 | **green** 2026-10-25 (Blossom_Misc PIDE 247 / Graph_Quotient 5940 commands, 0 errors; 14/14 and 89/89 statements unchanged; all counts 0; 6 + 40 proofs rewritten; the 3 diff flags are new `qed`/`by auto` lines inside new ai blocks (alignment artefacts); one dead commented-out proof attempt removed from Graph_Quotient) |
| B close | **green** 2026-10-25 (jEdit stopped; ASCII; clean build exit 0, 34 s; provenance strict ok; human 57.0% / ai 43.0% of lines) |
