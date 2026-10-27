# Plan: an executable Edmonds blossom algorithm (phased, with one-shot proofs)

> **STATUS (2026-10-24): ALL SIX PHASES GREEN.** Session `Blossom_Executable` builds from scratch
> (`isabelle build -c -o document=false Blossom_Executable`, exit 0); 3751 lines, 100% `ai`; no
> sorry/metis/smt/meson; ASCII. Final theorems `edmonds_blossom_correct_1/2` in
> `Edmonds_Blossom_Example`; demonstration and SML export work. Not done: commit (user decision),
> optional style polishing (see Gate 6 in progress.md). Approach approved by the user on
> 2026-10-24 ("ok, continue"). Every theory below is a one-shot: written in full, never
> checked by Isabelle. The one-shots live **only in this file**. The session directory holds
> only theories that check. The coder copies a phase's one-shot into the real theory and
> repairs it there. Per-phase state: see "Phase status" below and `progress.md`.

## Phase status

| Phase | Theory | State |
|---|---|---|
| 1 | `Graph_Matching_Specs` | **green** 2026-10-24 (gate: PIDE 0 errors, ASCII, ROOT, batch build, provenance 100% ai; no plan changes; 2 proofs repaired) |
| 2 | `Edmonds_Blossom_Top_Loop` | **green** 2026-10-24 (gate: PIDE 0 errors, ASCII, ROOT, batch build, provenance 100% ai; plan changes A1, A2; 1 proof repaired) |
| 3 | `Alternating_Forest_Search` | **green** 2026-10-24 (gate: PIDE 2225 commands 0 errors, ASCII, ROOT, batch build, provenance 100% ai; plan changes 3.1-3.3; helper lemma `forest_edgesI`; proofs repaired, one non-template `apply` of the one-shot removed at the gate) |
| 4 | `Blossom_Shrinking_Search` | **green** 2026-10-24 (gate: PIDE 1799 commands 0 errors, ASCII, ROOT, batch build, provenance 100% ai; plan changes A1, C4-1..C4-3; 14 proofs repaired) |
| 5 | `Edmonds_Blossom_Subprocedures` | **green** 2026-10-24 (gate: PIDE 292 commands 0 errors, ASCII, ROOT, batch build, provenance 100% ai; no plan changes; 1 proof repaired) |
| 6 | `Edmonds_Blossom_Example` | **green** 2026-10-24 (gate: PIDE 156 commands 0 errors, ASCII, ROOT, batch build incl. `value` and `export_code`, provenance 100% ai; plan changes P6-1..P6-3) |

Dependencies: 2, 3 and 4 need 1; 5 needs 4; 6 needs all. Phases 2 and 3 are independent of
each other.

## Amendment A (2026-10-24, after the first prover wedge; orchestrator)

**Incident.** During Phases 2 and 3 the prover of the 8768 instance wedged (all GC threads
spinning, no edit reached PIDE). Trigger: the one-shot proof of `Edmonds_Blossom_Loop_impl_same`
used `simp` with the unfolding equation `Edmonds_Blossom_Loop_impl.simps`, which loops and
makes terms grow. PIDE has no timeout, so one diverging tactic in a freshly copied one-shot
stops the whole instance (both theories). The orchestrator saved both buffers through I/Q,
killed only the 8768 processes and relaunched it without restoring buffers. The first relaunch
started no prover: jEdit's modal "Autosave File Found" dialog for its default scratch buffer
(`$USER_HOME/#Scratch.thy#`) blocked the startup. Restart recipe: save buffers via I/Q, kill -9
the processes with `USER_HOME=/media/llms/isabelle-home-blossom`, remove `#*#` autosave files in
that home and in the session directory, move `jedit/perspective.xml` aside, relaunch, and check
that a `poly` process with that `USER_HOME` exists.

**A0 - REPL-first copying (new coder rule).** A one-shot is copied first into the **REPL**, not
into a jEdit buffer: create a scratch theory that contains only the theory header of the phase
(same imports, plus `iq.iq` last) in `.claude/scratch_<coder>/` of the repository (I/Q only reads
inside the repository; `.claude/` is untracked and outside every session directory; the
orchestrator deletes these directories at the end), open it, `repl_init_from_source` at its `begin`, then feed the one-shot body to
the REPL with `repl_step`, one top-level command (with its proof) at a time. Every step then
runs under the REPL cap (about 10 s). Repair in the REPL. Only when the whole body replays
without errors, create the real theory file through I/Q with the repaired text (without
`iq.iq`) and check it in PIDE. The real theory file never contains an unchecked search tactic.

**A1 - the type variable of the mate function.** In a locale importing
`Graph_Matching_Specs where lookup = lookup`, a type `'mate` written in `fixes` is not the type
of the inherited `mate_*` parameters ("cannot generate coercion from 'a to 'mate"). Fix (found
by the Phase 2 coder): `Graph_Matching_Specs where lookup = lookup and mate_empty = mate_empty`
with `and mate_empty :: 'mate` in the `for` clause. Applied to the one-shots of Phases 2, 4, 5;
the Phase 3 coder applies it to its theory. Consequence: the positional parameter order of these
locales changes; instantiate them only by name (`where`), as Phase 6 does.

**A2 - twin lemmas.** Never `simp`/`auto` with `<loop>_impl.simps`; unfold it once with `subst`.
Applied to the Phase 2 one-shot; the one-shots of Phases 3 and 4 already use `subst`.

**Phase 3 plan changes found by its coder (to be confirmed at Gate 3).** (3.1) type annotation
`search_invars :: "'a set set \<Rightarrow> ('a \<Rightarrow> 'a option) \<Rightarrow> ('a \<Rightarrow> ('a \<times> label) option) \<Rightarrow> bool"`
(otherwise the label type is generalised and `compute_alt_path ex par flabel` is ill-typed);
(3.2) the variable `es` is renamed `rest` (`es` is a constant of `Blossom_Algo_Search`);
(3.3) A1.

**Phase 4 plan changes (accepted at Gate 4).** (C4-1) `lift_one` uses `quot.pref_suf` (the
function is defined inside locale `quot`); (C4-2) `cycle_sel_choose` states
`choose.choose (cycle_sel C)` (the locale predicate's short name does not parse in a term);
(C4-3) `invar_1_holds` moved after `invar_search_holds` (its proof uses
`invar_search_holds_1`). Statements otherwise unchanged (checked by a statement-level diff).

**Phase 6 plan changes (accepted at Gate 6).** (P6-1) the final context fixes natural-number
vertices (`fresh_nat` fixes the vertex type); (P6-2) the folding chains of
`edmonds_blossom_correct_1/2` also fold the data-structure constants; (P6-3) a subsection "Code
generation": `[code_unfold]` bridges for the constants of `gm`; `quot.pref_suf` has no code
equation (a function inside locale `quot`), replaced for the code of `lift_one_rbt` by
`pref_suf_list` (proved equal via an inhabitant `quot_nat` of the locale);
`replace_cycle_impl` binds `hd p2` and `last p1` in a `let`, which strict SML evaluates on empty
paths (exception `Match` after the first contraction), so its code equation is replaced by the
proved lazy form `replace_cycle_rbt_code`. Both code equations are proved lemmas.
Possible follow-up (not done): state `replace_cycle_impl` lazily and give `lift_one` an
executable prefix function in `Blossom_Shrinking_Search`, which would make these code
overrides unnecessary.

---

## Goal and approach

**Goal.** A verified executable version of Edmonds' blossom algorithm, as a functional program:
for every input graph satisfying the input conditions, the program returns a matching of
maximum cardinality. Code is exported to SML.

**Approach: reuse the existing correctness proofs.** The session `Blossom`
(`Edmonds_Blossom_Algorithm/`, about 10,000 lines, labelled `human`) proves the algorithm
correct on HOL sets, with an abstract choice function `sel` and an abstract fresh-vertex
function `create_vert`. It has four layers, each specified by a contract that the layer above
assumes:

```
find_max_matching (Main_Loop)        assumes aug_path_search: sound and complete
  find_aug_path (Contraction)        assumes blos_search: Path p is augmenting,
                                       Blossom stem C is a blossom, complete
    compute_match_blossom (Compute_Aug_Path)  assumes compute_alt_path_spec, complete
      compute_alt_path (Search)      proves compute_alt_path_spec and completeness
```

The executable development has one layer per abstract layer, in the form of the DFS/BFS
theories (`AI_Style/Library_Style_Guide.md`). The final theorem of each executable layer is the
contract that the abstract theory assumes of that layer, stated over the abstraction of the data
structures. The proofs discharge these contracts with the existing theorems; the mathematics is
not proved again. No human theory is changed. New lemmas about the abstract locales are added in
the new theories (`context compute_alt_path begin ... end`) and labelled `ai`.

| Theory (session `Blossom_Executable`) | Abstract layer | How correctness is obtained |
|---|---|---|
| `Graph_Matching_Specs` | (data structures) | Adjacency map (`Pair_Graph_Specs`, both orientations of each edge) plus a vertex list; mate function (`Matching_Augmentation_Specs`, a `Map`); an operation listing the elements of a vertex set. Abstraction `ugraph_abs`, input conditions `graph_input`, matching invariant `matching_invar`. |
| `Edmonds_Blossom_Top_Loop` | `find_max_matching` | Loop over a record holding the mate function; parameter `augmenting_path_search` with its contract. Maximum cardinality by Berge's lemma. Shape of the verified Hopcroft-Karp top loop. |
| `Alternating_Forest_Search` | `compute_alt_path` | Worklist loop: queue of even vertices, edges still to scan, parent map, label map. Every growth step is an `if1` step of the abstract search, so its invariants and their preservation lemmas carry over. Soundness at an edge between two even vertices: a lemma extracted from the returning case of `compute_alt_path_from_tree_1`. Completeness: at the final state neither `if1` nor `if2` applies, so the abstract function returns `None` there, and `compute_alt_path_from_tree_2'` applies. |
| `Blossom_Shrinking_Search` | `find_aug_path` | Tail-recursive loop: current contracted graph, vertex list and matching, a stack of contractions, and the stored search result. Contraction maps the cycle to a fresh vertex in the edge list and rebuilds the data structures; its abstraction is `quot.quotG`. Lifting through one blossom is proved **equal** to `quot.refine` for a choice function built from the cycle (`cycle_sel`), so `refine_works` and `aug_path_works_in_contraction` give correctness. |
| `Edmonds_Blossom_Subprocedures` | `compute_match_blossom` | Implements the shrinking search's `blossom_search` from the forest search's two paths: disjoint gives an augmenting path, otherwise `longest_disj_pfx` gives a blossom. Proof from the global lemmas `construct_aug_path'`, `common_pfxs_form_match_blossom'`, `pfxs_path`. |
| `Edmonds_Blossom_Example` | (composition) | Red-black trees; global interpretations in the order forest search, sub-procedures, shrinking search, top loop; final theorem re-exported with `[folded ...]`; demonstration; `export_code`. |

**Layering (style guide section 3.6).** Algorithm theories import specifications and mathematics only.
A sub-procedure is a parameter of the definitions locale and its contract is `assumes` of that
locale, each clause with its input conditions as premises. Composition happens only in the
example theory. The forest search and the shrinking search are algorithms with their own
theories (like DFS); their final lemmas have the form of the contract clauses of the layer that
uses them.

## Settled design decisions

- **EB-D1 Reuse, do not re-prove.** Abstract lemmas are used as they are. Where a needed fact
  is buried inside an existing proof, it is restated in a new theory with an adapted proof
  (`search_invars_if2_sound`, `blossom_cycle_props`). Human theories are not edited.
- **EB-D2 Choices.** The abstract algorithm chooses with `sel`; the executable one chooses by
  list order. We never prove equality with an abstract *function* that makes choices. The search
  is related to the abstract search step by step (each growth step is an `if1` step). The
  lifting is equal to `quot.refine` for the choice function `cycle_sel C`, which picks the first
  element of the cycle list. The abstract search locale is interpreted with the choice function
  `\<lambda>S. SOME x. x \<in> S`, which is never executed.
- **EB-D3 Examined edges are not stored.** The abstract search keeps the set `ex` of examined
  edges. In the executable search it is the set of forest edges, `forest_edges (parent map)`,
  which is the same set (the abstract step adds exactly the two new forest edges).
- **EB-D4 Search order.** The executable search returns as soon as an edge between two even
  vertices is scanned, possibly before the forest is complete. This is sound: the abstract
  soundness argument at an `if2` edge needs only the invariants, not that `if1` is impossible.
- **EB-D5 Contraction through edge lists.** A contraction maps the vertices of the cycle to the
  fresh vertex in the edge list of the graph (and of the matching), drops loops, and rebuilds
  the adjacency map (`Graph.from_list`) and the mate function (`mate_from_list`). The vertex
  list becomes `u # filter (\<lambda>v. v \<notin> set C) vs`. The vertex list may contain
  vertices without edges; it only has to contain all vertices with edges.
- **EB-D6 Loops are tail-recursive.** `find_aug_path` is not tail-recursive (it lifts after the
  recursive call). The executable version keeps the contractions on a stack and lifts the final
  path through the stack (`lift_path`).
- **EB-D7 Results are read off the final state.** The forest search reads its answer from the
  first unscanned edge of the final state (`alternating_paths`); the shrinking search stores the
  result of the last search in the state (`search_result`) and reads off the lifted path
  (`augmenting_path`). Both returning branches leave the state unchanged.
- **EB-D8 Efficiency.** Correct, not asymptotically optimal: the search restarts after every
  contraction (as the abstract algorithm does) and every contraction costs O(m log n); overall
  about O(n^2 m log n). The O(n^3) and O(sqrt(n) m) variants are out of scope.
- **EB-D9 Names.** Algorithm name `Edmonds_Blossom`; the definitions locales are
  `Edmonds_Blossom_Loop`, `Alternating_Forest_Search`, `Blossom_Shrinking_Search`,
  `Edmonds_Blossom_Subprocedures`. Proofs: `Edmonds_Blossom_Loop_thms` (DFS form, a locale);
  the forest search and the shrinking search prove inside the definitions locale in
  `context assumes <name>_axiom` (BFS form), so that their final lemmas carry the input
  conditions as premises and discharge the contract clauses of the layer above directly.
  Record fields are distinct across the three records (`current_matching`; `queue`, `unscanned`,
  `forest_parents`, `forest_labels`; `search_graph`, `search_vertices`, `search_matching`,
  `contractions`, `search_result`).
- **EB-D10 Terminology.** Academic English. A matching is represented by its *mate function*.
  New identifiers use `mate`. The library's mate-function locale is cited by its name, and its
  lemma names are cited as they are, but they are never used for new identifiers or in prose.
  The mate map is additionally registered as `Mate_Map: Map ...` so that the map lemmas are
  available as `Mate_Map.*`.
- **EB-D11 Data structures through ADTs.** Graph: `Pair_Graph_Specs` (qualifier `Graph`). Mate
  function: `Map` + `matching_augmentation` (qualifiers `Mate_Map`, `Mate`). Parent map and
  label map in the forest search: `Map` (qualifiers `Parent`, `Label`). Listing a vertex set:
  parameter `vset_to_list` with `vset_inv N \<Longrightarrow> set (vset_to_list N) = t_set N` (instance:
  `Tree2.inorder`), as `fold_vset` in `BFS_Subprocedures`.

## Project setup (done 2026-10-24)

- **Repository:** `/media/llms/Isabelle-Graph-Library-Blossom-Executable`, branch `main` (HEAD
  `bee8c9d`). Nothing is committed (user decision pending).
- **Session:** `Blossom_Executable = Blossom +`, directory `Edmonds_Blossom_Executable/`, listed
  in the top-level `ROOTS`. Its `ROOT` lists only theories that have passed their gate; the
  orchestrator adds a theory to `ROOT` at its gate. Options `[document = false, timeout = 3600]`.
- **Isabelle home:** every build and jEdit run uses `USER_HOME=/media/llms/isabelle-home-blossom`.
  It holds copies of the distribution heaps from the Hopcroft-Karp home and its own library
  heaps; the repository is registered there as a component (so `isabelle ai_provenance` works).
  Never build into `~/.isabelle` (shared with the Micali-Vazirani checkout, whose sources
  differ).
- **jEdit/I/Q instance:** logic `Blossom`, **port 8768, token `blossom`**, launched from the
  repository root with
  `USER_HOME=/media/llms/isabelle-home-blossom IQ_AUTH_TOKEN=blossom DISPLAY=:1 XAUTHORITY=/home/llm/.Xauthority nohup /media/llms/Isabelle2025-2/bin/isabelle jedit -l Blossom -d /media/llms/AutoCorrode/iq/ -d . &`.
  Other instances belong to other campaigns (8765 `graph-adt`, 8766 `ddfs`, 8767 `hk`): never
  touch, never kill. The shell exports `IQ_AUTH_TOKEN=gemini-1`, which belongs to another
  campaign.
- **Bridge scripts** (port and token pinned): `.claude/iq/mcp.py TOOL 'JSON'`;
  `.claude/iq/iq_call.py TOOL ARGS.json [WAIT]` for large arguments (whole-theory
  `write_file`); `.claude/iq/to_ascii.py FILE.thy` converts glyphs to `\<name>` (orchestrator
  only, at gates).
- **Baseline:** `USER_HOME=/media/llms/isabelle-home-blossom isabelle build -b Blossom` passed
  (2026-10-24, 6 min). Disk: about 4 GB free; check `df -h /media/llms` before large builds.
- **Logs:** `Edmonds_Blossom_Executable/progress.md` (one section per phase);
  snapshots `Edmonds_Blossom_Executable/backups/<theory>.thy.<date>_<tag>` (append-only; only
  label a snapshot green with a verification behind it).

## Coder protocol

The coder agent is `.claude/agents/coder.md` (adapted for this repository). For every phase:

1. **Copy the one-shot** - into the REPL first (Amendment A0), then into the theory file. Create the theory file named in the phase section, in
   `Edmonds_Blossom_Executable/`, with the one-shot text of that section **verbatim and whole**,
   through the I/Q MCP (`open_file` with `view: true` and the content, then `save_file`). The
   one-shot already starts with `provenance ai` after `begin`.
2. **Repair, do not redesign.** The lemma **statements and definitions are authoritative**;
   the proofs are candidates. Repair broken proofs with the REPL and sledgehammer, as
   `coder.md` prescribes (mine sledgehammer's facts; never keep `metis`/`smt`/`meson`).
   Auxiliary lemmas may be added (they are `ai` like the rest of the theory). Proofs may be
   restructured freely.
3. **Report back instead of changing the plan.** If a statement or definition is wrong (false,
   unprovable from the available facts, ill-typed, or a name or argument order of the library
   differs from the plan), make the **minimal** change that keeps the intent, mark it with a
   comment `(* PLAN CHANGE: ... *)`, and record it in `progress.md` and in the final report
   under "Plan changes". If the intent itself cannot be kept, stop and report the failing goal.
4. **Style.** Follow `AI_Style/Library_Style_Guide.md`: `using`/`by` on their own lines,
   `proof-`/`proof(` without a space, no `{ ... }` blocks, `apply` only in the templates of the
   style guide section 5.6 (loop induction, `_induct`, twin lemma, `unfold_locales` in
   interpretations), no labelled fact for every small step.
5. **Provenance.** Everything written in these theories is `ai`
   (`AI_Provenance/system_prompt.md`). Do not write other labels.
6. **Done** when `get_document_info` (wait, errors) reports the theory processed with 0 errors,
   and `get_sorry_positions` reports none, and the theory contains no `sorry`, `oops`, `metis`,
   `smt`, `meson`.
7. **Log** in `progress.md` under `## Phase N` (Bash append only): steps repaired with the
   sledgehammer facts mined, plan changes, open problems.

**Orchestrator gate** (after the coder reports done): PIDE recheck; `to_ascii.py` on the
theory; add the theory to `ROOT`;
`USER_HOME=/media/llms/isabelle-home-blossom isabelle build -o document=false Blossom_Executable`
(exit 0); grep for `sorry|oops|metis|smt|meson`; `isabelle ai_provenance -s Blossom_Executable`
with the same `USER_HOME`; statements compared with this plan (plan changes reviewed); snapshot
to `backups/`; update "Phase status".

## Baseline facts (names used by the one-shots; the coder verifies them in recon)

- Matching ADT (`Basic_Matching/Matching_Augmentation_Executable.thy`): locale
  `Matching_Augmentation_Specs` (Map qualifier inside it: see the theory), proof locale
  `matching_augmentation`; `augment_impl`, `\<M>`, `\<M>_def'`, `invar_matching`
  (`invar_matchingI`, `invar_matchingD(1-5)`), `augmentation_correct(1-3)`,
  `empty_matching_props`, `symmetric_buddiesI/D`, `no_self_loop_buddyI/E`.
- Graph ADT (`Pair_Graph_Specs`): `digraph_abs_def`, `neighbourhood`, `are_connected_abs`,
  `finite_vertices`, `from_list`, `from_list_correct(1-5)`, `neighbourhood_invars'`.
- Undirected graphs: `Vs_def`, `dblton_graph_def`, `graph_invar` (abbreviation),
  `neighbourhood_def` (`{u. {u, v} \<in> G}`), `graph_abs` locale, `construct_path`.
- Matching: `matching_def`, `matching_augmenting_path_def`, `graph_augmenting_path`
  (abbreviation), `alt_path`, `nin_M_alt_path`, `Berge`, `max_card_matching_def`.
- Search (`Blossom_Algo_Search`, locale `compute_alt_path G M sel`): `if1_def`, `if1_cond_def`,
  `if2_def`, `if2_cond_def`, `if1_props`, `v1_neq_v2_neq_v3`, `invar_init`,
  `compute_alt_path_dom`, `compute_alt_path.psimps`, the 17 invariants and their `_pres`
  lemmas, `alt_invars_then_alt_path`, `last_even_invar_imp`, `flabel_invar_props`,
  `flabel_invar_2_props`, `distinct_invar_props`, `path_invar_props`,
  `compute_alt_path_from_tree_2'`; datatype `label = Odd | Even`.
- Parent maps (`Graph_Algorithms_Dev.Parent_Map`): `parent_spec`, `parent_def`,
  `parent.follow_hd`, `parent.from_tree`, `parent.follow_impl_is_follow`, the global
  `follow_impl` and `follow_impl_def`.
- Contraction (`Blossom_Algo_Contraction`, `Graph_Quotient`): datatype `match_blossom_res`
  (`Path`, `Blossom`); `match_blossom_def`, `match_blossomD`, `blossomD`, `odd_cycleD`,
  `odd_cycle_nempty`, `match_blossom_distinct_tl`, `quot_graph_def`; locale `quot sel E s u`
  with `quotG`, `choose_con_vert_def`, `stem2vert_path_def`, `replace_cycle_def`,
  `refine_def`, `refine_works`, `aug_path_works_in_contraction`, `matching_quotM`,
  `card_Vs_quotG`; `find_pfx`, `find_pfx_nempty`, `pref_suf`, `longest_disj_pfx` and the lemmas
  `first_pfx_then_snd_pfx`, `disj_pfx_is_complete`, `disj_pref_append1/2`, `first_pfx_nempty`,
  `snd_pfx_nempty`, `pfx_common_end`, `pfxs_path`, `common_pfxs_form_match_blossom'`,
  `construct_aug_path'`; `compute_alt_path_spec_def` (`Blossom_Algo_Compute_Aug_Path`);
  `Suc_le_length_iff_snoc2` (`Blossom_Misc`).
- Note: `blossom_cycle_longer_2` and `blossom_diff` lie inside locale `find_aug_path` and are
  therefore not used; `blossom_cycle_props` restates what is needed.

## Risks known in advance

- **Locale constants in global form.** `invar_forest_def` uses
  `compute_alt_path.search_invars (ugraph_abs G) (matching_abs M) ex par flabel`. Check the
  argument order with `term compute_alt_path.search_invars` (the global constant takes the
  locale parameters that occur in the definition, here `G M`).
- **Function package with `case`.** The `pinduct`, `psimps` and `domintros` of loops whose
  body is a nested `case` have many premises; `_simps`, `_induct`, `_domintros` may need
  `split: list.splits prod.splits option.splits label.splits` or `match_blossom_res.splits`.
- **The twin lemma.** If `auto` with `_impl.simps` loops, use the one-step `subst` form
  (as in `Parent_Map.follow_dom_impl_same_loop`).
- **Interpretation of the quotient locale.** `quot` is `pre_quot sel E + fixes s u + assumes`;
  `unfold_locales` produces the choice axiom, `graph_invar E` (possibly split), `u \<notin> s`,
  `s \<subset> Vs E`.
- **Code generation (phase 6).** Every locale constant reachable from the exported code must be
  in the `defines` of a global interpretation (as in `DFS_Example`, which avoids the plain
  interpretation `G` of `Pair_Graph_RBT` by using `map_empty` and `adj_inv`). The second and
  later global interpretations reuse the names of the first (`gm`) for shared constants.

---
## Phase 1: the data-structure layer (`Graph_Matching_Specs.thy`)

**Goal.** The locale `Graph_Matching_Specs` (graph ADT + mate-function ADT + `vset_to_list`),
the abstraction `ugraph_abs`, the input conditions `graph_input`, `matching_invar`, the
operations `neighbour_list`, `adjacency_edges`, `matching_edges`, `mate_from_list`, and their
lemmas.

**Recon (record in progress.md first).** (a) The locale expression loads: in particular
`Mate_Map: Map ...` followed by `Mate: matching_augmentation ...` with the same parameters (the
second registration's inner map interpretation is subsumed by the first; check that
`Mate_Map.map_update` and `Mate.augmentation_correct` both exist). (b) `thm Mate.\<M>_def'
Mate.invar_matchingD Mate.invar_matchingI Mate.symmetric_buddiesI Mate.no_self_loop_buddyI
Graph.finite_vertices Graph.from_list_correct Graph.digraph_abs_def`.

**Frozen statements.** All lemma statements of the one-shot. Used later:
`graph_inputD`, `graph_inputI`, `in_ugraph_abs_iff`, `isin_neighbourhood_iff`,
`ugraph_abs_graph_invar`, `Vs_ugraph_abs`, `Vs_ugraph_abs_subset_vs`, `neighbour_list`,
`neighbour_list_ugraph_abs`, `neighbour_list_nonempty_iff`, `adjacency_edges`,
`matching_abs_iff`, `Vs_matching_abs_iff`, `matching_invar_props`, `matching_invar_mate_edge`,
`matching_edges`, `mate_from_list`, `from_list_graph_input`, `ugraph_abs_from_list`.

**One-shot theory** (copy verbatim into `Edmonds_Blossom_Executable/Graph_Matching_Specs.thy`):

```isabelle
theory Graph_Matching_Specs
  imports Directed_Set_Graphs.Pair_Graph_Specs Basic_Matching.Matching_Augmentation_Executable
begin

provenance ai

section \<open>Graphs and matchings for the executable blossom algorithm\<close>

text \<open>An undirected graph is represented by an adjacency map that stores both orientations of
  every edge. A matching is represented by its mate function, which maps every matched vertex to
  its partner. The locale below combines the two data structures with an operation that lists the
  elements of a vertex set, which is needed to scan the neighbours of a vertex and to enumerate
  the edges of a graph.\<close>

locale Graph_Matching_Specs =
  Graph: Pair_Graph_Specs where lookup = lookup +
  Mate_Map: Map mate_empty mate_update mate_delete mate_lookup mate_invar +
  Mate: matching_augmentation mate_empty mate_update mate_delete mate_lookup mate_invar
  for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option"
  and mate_empty :: 'mate
  and mate_update :: "'v \<Rightarrow> 'v \<Rightarrow> 'mate \<Rightarrow> 'mate"
  and mate_delete :: "'v \<Rightarrow> 'mate \<Rightarrow> 'mate"
  and mate_lookup :: "'mate \<Rightarrow> 'v \<Rightarrow> 'v option"
  and mate_invar :: "'mate \<Rightarrow> bool" +
  fixes vset_to_list :: "'vset \<Rightarrow> 'v list"
  assumes vset_to_list: "\<And>N. vset_inv N \<Longrightarrow> set (vset_to_list N) = t_set N"
begin

subsection \<open>Abstraction and input conditions\<close>

definition "ugraph_abs G = {{u, v} | u v. (u, v) \<in> Graph.digraph_abs G}"

text \<open>The conditions on a graph and its vertex list. The list may contain vertices without
  edges; it is used to enumerate the vertices.\<close>

definition "graph_input G vs \<longleftrightarrow>
   Graph.graph_inv G \<and> Graph.finite_graph G \<and> Graph.finite_vsets G \<and>
   (\<forall>u v. (u, v) \<in> Graph.digraph_abs G \<longrightarrow> (v, u) \<in> Graph.digraph_abs G) \<and>
   (\<forall>u. (u, u) \<notin> Graph.digraph_abs G) \<and>
   dVs (Graph.digraph_abs G) \<subseteq> set vs"

abbreviation "matching_abs \<equiv> Mate.\<M>"

definition "matching_invar G M = Mate.invar_matching (ugraph_abs G) M"

subsection \<open>Operations\<close>

definition "neighbour_list G v = vset_to_list (Graph.neighbourhood G v)"

definition "adjacency_edges G vs = concat (map (\<lambda>v. map (Pair v) (neighbour_list G v)) vs)"

definition "matching_edges M vs =
   concat (map (\<lambda>v. case mate_lookup M v of Some w \<Rightarrow> [(v, w)] | None \<Rightarrow> []) vs)"

definition "mate_from_list ps = foldl (\<lambda>m (a, b). mate_update a b m) mate_empty ps"

lemmas [code] = neighbour_list_def adjacency_edges_def matching_edges_def mate_from_list_def

subsection \<open>Properties of the input conditions\<close>

lemma graph_inputD:
  "graph_input G vs \<Longrightarrow> Graph.graph_inv G"
  "graph_input G vs \<Longrightarrow> Graph.finite_graph G"
  "graph_input G vs \<Longrightarrow> Graph.finite_vsets G"
  "\<lbrakk>graph_input G vs; (u, v) \<in> Graph.digraph_abs G\<rbrakk> \<Longrightarrow> (v, u) \<in> Graph.digraph_abs G"
  "graph_input G vs \<Longrightarrow> (u, u) \<notin> Graph.digraph_abs G"
  "graph_input G vs \<Longrightarrow> dVs (Graph.digraph_abs G) \<subseteq> set vs"
  by (auto simp: graph_input_def)

lemma graph_inputI:
  "\<lbrakk>Graph.graph_inv G; Graph.finite_graph G; Graph.finite_vsets G;
    \<And>u v. (u, v) \<in> Graph.digraph_abs G \<Longrightarrow> (v, u) \<in> Graph.digraph_abs G;
    \<And>u. (u, u) \<notin> Graph.digraph_abs G; dVs (Graph.digraph_abs G) \<subseteq> set vs\<rbrakk>
   \<Longrightarrow> graph_input G vs"
  by (auto simp: graph_input_def)

lemma in_ugraph_abs_iff:
  "graph_input G vs \<Longrightarrow> {u, v} \<in> ugraph_abs G \<longleftrightarrow> (u, v) \<in> Graph.digraph_abs G"
  by (auto simp: ugraph_abs_def doubleton_eq_iff dest: graph_inputD(4))

lemma isin_neighbourhood_iff:
  "isin (Graph.neighbourhood G v) w \<longleftrightarrow> (v, w) \<in> Graph.digraph_abs G"
  by (simp add: Graph.digraph_abs_def)

lemma Vs_ugraph_abs_subset:
  "Vs (ugraph_abs G) \<subseteq> dVs (Graph.digraph_abs G)"
  by (auto simp: ugraph_abs_def Vs_def intro: dVsI)

lemma ugraph_abs_graph_invar:
  assumes "graph_input G vs"
  shows "graph_invar (ugraph_abs G)"
proof
  show "dblton_graph (ugraph_abs G)"
    using graph_inputD(5)[OF assms]
    by (fastforce simp: dblton_graph_def ugraph_abs_def)
  have "finite (dVs (Graph.digraph_abs G))"
    using graph_inputD(1-3)[OF assms]
    by (rule Graph.finite_vertices)
  thus "finite (Vs (ugraph_abs G))"
    using Vs_ugraph_abs_subset
    by (rule finite_subset[rotated])
qed

lemma Vs_ugraph_abs:
  assumes "graph_input G vs"
  shows "Vs (ugraph_abs G) = dVs (Graph.digraph_abs G)"
proof
  show "Vs (ugraph_abs G) \<subseteq> dVs (Graph.digraph_abs G)"
    by (rule Vs_ugraph_abs_subset)
  show "dVs (Graph.digraph_abs G) \<subseteq> Vs (ugraph_abs G)"
    using graph_inputD(4)[OF assms]
    by (fastforce simp: ugraph_abs_def Vs_def dVs_eq)
qed

lemma Vs_ugraph_abs_subset_vs:
  "graph_input G vs \<Longrightarrow> Vs (ugraph_abs G) \<subseteq> set vs"
  using Vs_ugraph_abs_subset graph_inputD(6)
  by blast

subsection \<open>Properties of the operations\<close>

lemma neighbour_list:
  assumes "graph_input G vs"
  shows "set (neighbour_list G v) = {w. (v, w) \<in> Graph.digraph_abs G}"
proof-
  have "Graph.graph_inv G"
    using assms
    by (rule graph_inputD(1))
  thus ?thesis
    by (auto simp: neighbour_list_def vset_to_list)
qed

lemma neighbour_list_ugraph_abs:
  assumes "graph_input G vs"
  shows "w \<in> set (neighbour_list G v) \<longleftrightarrow> {v, w} \<in> ugraph_abs G"
  by (simp add: neighbour_list[OF assms] in_ugraph_abs_iff[OF assms])

lemma neighbour_list_nonempty_iff:
  assumes "graph_input G vs"
  shows "neighbour_list G v \<noteq> [] \<longleftrightarrow> v \<in> Vs (ugraph_abs G)"
proof-
  have "neighbour_list G v \<noteq> [] \<longleftrightarrow> (\<exists>w. w \<in> set (neighbour_list G v))"
    by (cases "neighbour_list G v") auto
  also have "\<dots> \<longleftrightarrow> (\<exists>w. {v, w} \<in> ugraph_abs G)"
    by (simp add: neighbour_list_ugraph_abs[OF assms])
  also have "\<dots> \<longleftrightarrow> v \<in> Vs (ugraph_abs G)"
    using ugraph_abs_graph_invar[OF assms]
    by (fastforce simp: Vs_def dblton_graph_def insert_commute)
  finally show ?thesis .
qed

lemma adjacency_edges:
  assumes "graph_input G vs"
  shows "set (adjacency_edges G vs) = Graph.digraph_abs G"
proof-
  have "set (adjacency_edges G vs) = {(v, w). v \<in> set vs \<and> (v, w) \<in> Graph.digraph_abs G}"
    by (auto simp: adjacency_edges_def neighbour_list[OF assms])
  moreover have "v \<in> set vs" if "(v, w) \<in> Graph.digraph_abs G" for v w
    using that graph_inputD(6)[OF assms]
    by (auto intro: dVsI)
  ultimately show ?thesis
    by auto
qed

subsection \<open>The mate function\<close>

lemma matching_abs_iff:
  "Mate.invar_matching E M \<Longrightarrow> {u, v} \<in> matching_abs M \<longleftrightarrow> mate_lookup M u = Some v"
  by (auto simp: Mate.\<M>_def' doubleton_eq_iff dest: Mate.invar_matchingD(2) Mate.symmetric_buddiesD)

lemma Vs_matching_abs_iff:
  "Mate.invar_matching E M \<Longrightarrow> v \<in> Vs (matching_abs M) \<longleftrightarrow> mate_lookup M v \<noteq> None"
  by (auto simp: Vs_def Mate.\<M>_def' dest: Mate.invar_matchingD(2) Mate.symmetric_buddiesD)

lemma matching_invar_props:
  assumes "matching_invar G M"
  shows "mate_invar M" "matching (matching_abs M)" "matching_abs M \<subseteq> ugraph_abs G"
        "finite (matching_abs M)"
  using assms
  by (auto simp: matching_invar_def dest: Mate.invar_matchingD)

lemma matching_invar_mate_edge:
  assumes "graph_input G vs" "matching_invar G M" "mate_lookup M u = Some v"
  shows "{u, v} \<in> matching_abs M" "{u, v} \<in> ugraph_abs G" "(u, v) \<in> Graph.digraph_abs G"
proof-
  show "{u, v} \<in> matching_abs M"
    using assms(2,3)
    by (simp add: matching_invar_def matching_abs_iff)
  thus "{u, v} \<in> ugraph_abs G"
    using matching_invar_props(3)[OF assms(2)]
    by blast
  thus "(u, v) \<in> Graph.digraph_abs G"
    by (simp add: in_ugraph_abs_iff[OF assms(1)])
qed

lemma matching_edges:
  assumes "graph_input G vs" "matching_invar G M"
  shows "set (matching_edges M vs) = {(u, v). mate_lookup M u = Some v}"
proof-
  have "u \<in> set vs" if "mate_lookup M u = Some v" for u v
    using matching_invar_mate_edge(3)[OF assms that] graph_inputD(6)[OF assms(1)]
    by (auto intro: dVsI)
  thus ?thesis
    by (force simp: matching_edges_def split: option.splits)
qed

lemma mate_foldl_update:
  assumes "mate_invar m" "\<And>a b b'. \<lbrakk>(a, b) \<in> set ps; (a, b') \<in> set ps\<rbrakk> \<Longrightarrow> b = b'"
  shows "mate_invar (foldl (\<lambda>m (a, b). mate_update a b m) m ps) \<and>
         (\<forall>a b. mate_lookup (foldl (\<lambda>m (a, b). mate_update a b m) m ps) a = Some b \<longleftrightarrow>
                (a, b) \<in> set ps \<or> ((\<forall>b'. (a, b') \<notin> set ps) \<and> mate_lookup m a = Some b))"
  using assms
proof(induction ps arbitrary: m)
  case Nil
  then show ?case
    by simp
next
  case (Cons p ps)
  obtain a0 b0 where p: "p = (a0, b0)"
    by (cases p)
  have inv: "mate_invar (mate_update a0 b0 m)"
    using Cons.prems(1)
    by (rule Mate_Map.invar_update)
  have func: "\<And>a b b'. \<lbrakk>(a, b) \<in> set ps; (a, b') \<in> set ps\<rbrakk> \<Longrightarrow> b = b'"
    using Cons.prems(2)
    by auto
  have IH: "mate_invar (foldl (\<lambda>m (a, b). mate_update a b m) (mate_update a0 b0 m) ps) \<and>
            (\<forall>a b. mate_lookup (foldl (\<lambda>m (a, b). mate_update a b m) (mate_update a0 b0 m) ps) a = Some b
                   \<longleftrightarrow> (a, b) \<in> set ps \<or>
                       ((\<forall>b'. (a, b') \<notin> set ps) \<and> mate_lookup (mate_update a0 b0 m) a = Some b))"
    using Cons.IH[OF inv func] .
  have upd: "mate_lookup (mate_update a0 b0 m) a = (if a = a0 then Some b0 else mate_lookup m a)" for a
    using Cons.prems(1)
    by (simp add: Mate_Map.map_update)
  have "(a0, b) \<in> set ps \<Longrightarrow> b = b0" for b
    using Cons.prems(2)[of a0 b b0]
    by (simp add: p)
  thus ?case
    using IH
    by (auto simp: p upd)
qed

lemma matching_set_functional:
  assumes "matching {{a, b} | a b. (a, b) \<in> set ps}" "\<And>a. (a, a) \<notin> set ps"
          "(a, b) \<in> set ps" "(a, b') \<in> set ps"
  shows "b = b'"
proof(rule ccontr)
  assume "b \<noteq> b'"
  hence "{a, b} \<noteq> {a, b'}"
    by (auto simp: doubleton_eq_iff)
  moreover have "{a, b} \<in> {{a, b} | a b. (a, b) \<in> set ps}" "{a, b'} \<in> {{a, b} | a b. (a, b) \<in> set ps}"
    using assms(3,4)
    by blast+
  ultimately have "{a, b} \<inter> {a, b'} = {}"
    using assms(1)
    by (auto simp: matching_def)
  thus False
    by blast
qed

lemma mate_from_list:
  assumes "graph_input G vs"
    and "\<And>a b. (a, b) \<in> set ps \<Longrightarrow> (b, a) \<in> set ps"
    and "\<And>a. (a, a) \<notin> set ps"
    and "matching {{a, b} | a b. (a, b) \<in> set ps}"
    and "\<And>a b. (a, b) \<in> set ps \<Longrightarrow> (a, b) \<in> Graph.digraph_abs G"
  shows "matching_invar G (mate_from_list ps)"
        "matching_abs (mate_from_list ps) = {{a, b} | a b. (a, b) \<in> set ps}"
proof-
  have func: "\<And>a b b'. \<lbrakk>(a, b) \<in> set ps; (a, b') \<in> set ps\<rbrakk> \<Longrightarrow> b = b'"
    using matching_set_functional[OF assms(4,3)]
    by blast
  have fold: "mate_invar (mate_from_list ps)"
    "\<And>a b. mate_lookup (mate_from_list ps) a = Some b \<longleftrightarrow> (a, b) \<in> set ps"
    using mate_foldl_update[OF Mate_Map.invar_empty func]
    by (auto simp: mate_from_list_def Mate_Map.map_empty)
  show abs: "matching_abs (mate_from_list ps) = {{a, b} | a b. (a, b) \<in> set ps}"
    by (simp add: Mate.\<M>_def' fold(2))
  have "Mate.symmetric_buddies (mate_from_list ps)"
    using assms(2)
    by (auto intro!: Mate.symmetric_buddiesI simp: fold(2))
  moreover have "Mate.no_self_loop_buddy (mate_from_list ps)"
    using assms(3)
    by (auto intro!: Mate.no_self_loop_buddyI simp: fold(2))
  moreover have "matching_abs (mate_from_list ps) \<subseteq> ugraph_abs G"
    using assms(5)
    by (auto simp: abs ugraph_abs_def)
  moreover have "finite (matching_abs (mate_from_list ps))"
  proof-
    have "{{a, b} | a b. (a, b) \<in> set ps} = (\<lambda>(a, b). {a, b}) ` set ps"
      by auto
    thus ?thesis
      by (simp add: abs)
  qed
  ultimately show "matching_invar G (mate_from_list ps)"
    using fold(1) assms(4)
    by (auto intro!: Mate.invar_matchingI simp: matching_invar_def abs)
qed

subsection \<open>Graphs built from edge lists\<close>

lemma from_list_graph_input:
  assumes "\<And>a b. (a, b) \<in> set xs \<Longrightarrow> (b, a) \<in> set xs" "\<And>a. (a, a) \<notin> set xs"
          "dVs (set xs) \<subseteq> set vs"
  shows "graph_input (Graph.from_list xs) vs"
  using assms
  by (auto intro!: graph_inputI simp: Graph.from_list_correct)

lemma ugraph_abs_from_list:
  "ugraph_abs (Graph.from_list xs) = {{a, b} | a b. (a, b) \<in> set xs}"
  by (simp add: ugraph_abs_def Graph.from_list_correct)

end

end
```

---

## Phase 2: the top loop (`Edmonds_Blossom_Top_Loop.thy`)

**Goal.** `Edmonds_Blossom_Loop_correct_1`: the final matching has maximum cardinality;
`Edmonds_Blossom_Loop_correct_2`: it satisfies `matching_invar`; and
`Edmonds_Blossom_Loop_impl_to_Edmonds_Blossom_Loop`.

**Recon.** `thm Mate.augmentation_correct Mate.empty_matching_props Berge max_card_matching_def`;
the form of `Edmonds_Blossom_Loop.pinduct` and `.domintros` (the `case` gives a premise
`augmenting_path_search (current_matching state) = Some p`).

**Frozen statements.** The locale `Edmonds_Blossom_Loop` (its contract), the definitions, and
the statements of `Edmonds_Blossom_Loop_correct_1/2`, `Edmonds_Blossom_Loop_impl_to_...`,
`initial_state_props`.

**One-shot theory** (copy verbatim into `Edmonds_Blossom_Executable/Edmonds_Blossom_Top_Loop.thy`):

```isabelle
theory Edmonds_Blossom_Top_Loop
  imports Graph_Matching_Specs
begin

provenance ai

section \<open>The top loop of Edmonds' blossom algorithm\<close>

text \<open>The top loop starts from the empty matching and augments the current matching along an
  augmenting path for as long as the search procedure finds one. When the search reports that no
  augmenting path exists, the matching has maximum cardinality by Berge's lemma. The search
  procedure is a parameter, specified by its soundness and its completeness.\<close>

subsection \<open>The program state\<close>

record 'mate Edmonds_Blossom_Loop_state =
  current_matching :: 'mate

subsection \<open>Setup for automation\<close>

named_theorems call_cond_elims
named_theorems call_cond_intros
named_theorems ret_holds_intros
named_theorems invar_props_intros
named_theorems invar_props_elims
named_theorems invar_holds_intros
named_theorems state_rel_intros
named_theorems state_rel_holds_intros

subsection \<open>The loop\<close>

(* PLAN CHANGE A1 (2026-10-24): mate_empty is instantiated by name and typed in the for
   clause, so that the type variable 'mate below is that of the mate-function ADT. *)
locale Edmonds_Blossom_Loop = Graph_Matching_Specs where lookup = lookup and mate_empty = mate_empty
  for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option" and mate_empty :: 'mate +
  fixes G :: 'adjmap and vs :: "'v list"
    and augmenting_path_search :: "'mate \<Rightarrow> 'v list option"
  assumes augmenting_path_search:
    "\<And>M p. \<lbrakk>graph_input G vs; matching_invar G M; augmenting_path_search M = Some p\<rbrakk>
       \<Longrightarrow> graph_augmenting_path (ugraph_abs G) (matching_abs M) p"
    "\<And>M. \<lbrakk>graph_input G vs; matching_invar G M;
           \<exists>p. graph_augmenting_path (ugraph_abs G) (matching_abs M) p\<rbrakk>
       \<Longrightarrow> augmenting_path_search M \<noteq> None"
begin

definition "Edmonds_Blossom_Loop_axiom = graph_input G vs"

function (domintros) Edmonds_Blossom_Loop ::
  "'mate Edmonds_Blossom_Loop_state \<Rightarrow> 'mate Edmonds_Blossom_Loop_state" where
  "Edmonds_Blossom_Loop state =
     (case augmenting_path_search (current_matching state) of
        Some p \<Rightarrow>
          Edmonds_Blossom_Loop
            (state \<lparr>current_matching := Mate.augment_impl (current_matching state) p\<rparr>)
      | None \<Rightarrow> state)"
  by pat_completeness auto

partial_function (tailrec) Edmonds_Blossom_Loop_impl ::
  "'mate Edmonds_Blossom_Loop_state \<Rightarrow> 'mate Edmonds_Blossom_Loop_state" where
  "Edmonds_Blossom_Loop_impl state =
     (case augmenting_path_search (current_matching state) of
        Some p \<Rightarrow>
          Edmonds_Blossom_Loop_impl
            (state \<lparr>current_matching := Mate.augment_impl (current_matching state) p\<rparr>)
      | None \<Rightarrow> state)"

lemma Edmonds_Blossom_Loop_impl_same:
  assumes "Edmonds_Blossom_Loop_dom state"
  shows "Edmonds_Blossom_Loop_impl state = Edmonds_Blossom_Loop state"
proof(induction rule: Edmonds_Blossom_Loop.pinduct[OF assms])
  \<comment> \<open>PLAN CHANGE A2: never rewrite with the unfolding equation of the twin; one step only.\<close>
  case (1 state)
  show ?case
    by (subst Edmonds_Blossom_Loop_impl.simps, subst Edmonds_Blossom_Loop.psimps[OF 1(1)])
       (auto split: option.splits intro: 1(2))
qed

definition "initial_state = \<lparr>current_matching = mate_empty\<rparr>"

definition "Edmonds_Blossom_Loop_run = Edmonds_Blossom_Loop initial_state"

definition "Edmonds_Blossom_Loop_run_impl = Edmonds_Blossom_Loop_impl initial_state"

lemmas [code] = Edmonds_Blossom_Loop_impl.simps initial_state_def Edmonds_Blossom_Loop_run_impl_def

definition "Edmonds_Blossom_Loop_call_1_conds state =
  (\<exists>p. augmenting_path_search (current_matching state) = Some p)"

definition "Edmonds_Blossom_Loop_upd1 state =
  state \<lparr>current_matching :=
           Mate.augment_impl (current_matching state)
             (the (augmenting_path_search (current_matching state)))\<rparr>"

definition "Edmonds_Blossom_Loop_ret_1_conds state =
  (augmenting_path_search (current_matching state) = None)"

abbreviation "Edmonds_Blossom_Loop_ret1 state \<equiv> state"

definition "invar_current_matching state = matching_invar G (current_matching state)"

definition "call_1_measure state =
  card (ugraph_abs G) - card (matching_abs (current_matching state))"

definition "Edmonds_Blossom_Loop_term_rel' = call_1_measure <*mlex*> {}"

lemma Edmonds_Blossom_Loop_call_1_conds[call_cond_elims]:
  "Edmonds_Blossom_Loop_call_1_conds state \<Longrightarrow>
   ((\<exists>p. augmenting_path_search (current_matching state) = Some p) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: Edmonds_Blossom_Loop_call_1_conds_def)

lemma Edmonds_Blossom_Loop_call_1_condsI[call_cond_intros]:
  "augmenting_path_search (current_matching state) = Some p \<Longrightarrow>
   Edmonds_Blossom_Loop_call_1_conds state"
  by (auto simp: Edmonds_Blossom_Loop_call_1_conds_def)

lemma Edmonds_Blossom_Loop_ret_1_conds[call_cond_elims]:
  "Edmonds_Blossom_Loop_ret_1_conds state \<Longrightarrow>
   (augmenting_path_search (current_matching state) = None \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: Edmonds_Blossom_Loop_ret_1_conds_def)

lemma Edmonds_Blossom_Loop_ret_1_condsI[call_cond_intros]:
  "augmenting_path_search (current_matching state) = None \<Longrightarrow>
   Edmonds_Blossom_Loop_ret_1_conds state"
  by (auto simp: Edmonds_Blossom_Loop_ret_1_conds_def)

lemma Edmonds_Blossom_Loop_cases:
  assumes "Edmonds_Blossom_Loop_call_1_conds state \<Longrightarrow> P"
          "Edmonds_Blossom_Loop_ret_1_conds state \<Longrightarrow> P"
  shows "P"
  using assms
  by (cases "augmenting_path_search (current_matching state)")
     (auto simp: Edmonds_Blossom_Loop_call_1_conds_def Edmonds_Blossom_Loop_ret_1_conds_def)

lemma Edmonds_Blossom_Loop_simps:
  assumes "Edmonds_Blossom_Loop_dom state"
  shows "Edmonds_Blossom_Loop_call_1_conds state \<Longrightarrow>
           Edmonds_Blossom_Loop state = Edmonds_Blossom_Loop (Edmonds_Blossom_Loop_upd1 state)"
        "Edmonds_Blossom_Loop_ret_1_conds state \<Longrightarrow>
           Edmonds_Blossom_Loop state = Edmonds_Blossom_Loop_ret1 state"
  by (auto simp: Edmonds_Blossom_Loop.psimps[OF assms] Edmonds_Blossom_Loop_upd1_def
                 Edmonds_Blossom_Loop_call_1_conds_def Edmonds_Blossom_Loop_ret_1_conds_def)

lemma Edmonds_Blossom_Loop_induct:
  assumes "Edmonds_Blossom_Loop_dom state"
  assumes "\<And>state. \<lbrakk>Edmonds_Blossom_Loop_dom state;
                     Edmonds_Blossom_Loop_call_1_conds state \<Longrightarrow>
                       P (Edmonds_Blossom_Loop_upd1 state)\<rbrakk>
                    \<Longrightarrow> P state"
  shows "P state"
  apply(rule Edmonds_Blossom_Loop.pinduct[OF assms(1)])
  apply(rule assms(2))
  by (auto simp: Edmonds_Blossom_Loop_call_1_conds_def Edmonds_Blossom_Loop_upd1_def)

lemma Edmonds_Blossom_Loop_domintros:
  assumes "Edmonds_Blossom_Loop_call_1_conds state \<Longrightarrow>
             Edmonds_Blossom_Loop_dom (Edmonds_Blossom_Loop_upd1 state)"
  shows "Edmonds_Blossom_Loop_dom state"
  using assms
  by (auto intro: Edmonds_Blossom_Loop.domintros
           simp: Edmonds_Blossom_Loop_call_1_conds_def Edmonds_Blossom_Loop_upd1_def)

end

subsection \<open>Locale for the proofs\<close>

locale Edmonds_Blossom_Loop_thms = Edmonds_Blossom_Loop +
  assumes Edmonds_Blossom_Loop_axiom: Edmonds_Blossom_Loop_axiom
begin

lemma graph_input_G[simp]: "graph_input G vs"
  using Edmonds_Blossom_Loop_axiom
  by (simp add: Edmonds_Blossom_Loop_axiom_def)

lemma ugraph_abs_G[simp]: "graph_invar (ugraph_abs G)"
  by (rule ugraph_abs_graph_invar[OF graph_input_G])

lemma finite_ugraph_abs_G[simp]: "finite (ugraph_abs G)"
  using ugraph_abs_G
  by (simp add: finite_Vs_then_finite)

lemmas augmenting_path_search_props = augmenting_path_search[OF graph_input_G]

subsection \<open>The invariant\<close>

lemma invar_current_matching_props[invar_props_elims]:
  "invar_current_matching state \<Longrightarrow> (matching_invar G (current_matching state) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_current_matching_def)

lemma invar_current_matching_intro[invar_props_intros]:
  "matching_invar G (current_matching state) \<Longrightarrow> invar_current_matching state"
  by (auto simp: invar_current_matching_def)

lemma invar_current_matching_holds_1[invar_holds_intros]:
  "\<lbrakk>Edmonds_Blossom_Loop_call_1_conds state; invar_current_matching state\<rbrakk>
   \<Longrightarrow> invar_current_matching (Edmonds_Blossom_Loop_upd1 state)"
proof(elim call_cond_elims invar_props_elims exE)
  fix p
  assume inv: "matching_invar G (current_matching state)"
     and p: "augmenting_path_search (current_matching state) = Some p"
  hence "graph_augmenting_path (ugraph_abs G) (matching_abs (current_matching state)) p"
    by (intro augmenting_path_search_props(1))
  thus ?thesis
    using inv p
    by (auto intro!: invar_props_intros Mate.augmentation_correct(1)
               simp: Edmonds_Blossom_Loop_upd1_def matching_invar_def)
qed

lemma invar_current_matching_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>Edmonds_Blossom_Loop_ret_1_conds state; invar_current_matching state\<rbrakk>
   \<Longrightarrow> invar_current_matching (Edmonds_Blossom_Loop_ret1 state)"
  by auto

lemma invar_current_matching_holds[invar_holds_intros]:
  assumes "Edmonds_Blossom_Loop_dom state" "invar_current_matching state"
  shows "invar_current_matching (Edmonds_Blossom_Loop state)"
  using assms(2)
proof(induction rule: Edmonds_Blossom_Loop_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    apply(rule Edmonds_Blossom_Loop_cases[where state = state])
    by (auto intro: IH(2-) invar_holds_intros simp: Edmonds_Blossom_Loop_simps[OF IH(1)])
qed

subsection \<open>Termination\<close>

named_theorems termination_intros

lemma call_1_terminates[termination_intros]:
  assumes "Edmonds_Blossom_Loop_call_1_conds state" "invar_current_matching state"
  shows "(Edmonds_Blossom_Loop_upd1 state, state) \<in> call_1_measure <*mlex*> r"
proof-
  obtain p where p: "augmenting_path_search (current_matching state) = Some p"
    using assms(1)
    by (auto elim!: call_cond_elims)
  have inv: "Mate.invar_matching (ugraph_abs G) (current_matching state)"
    using assms(2)
    by (auto elim!: invar_props_elims simp: matching_invar_def)
  have aug: "graph_augmenting_path (ugraph_abs G) (matching_abs (current_matching state)) p"
    using assms(2) p
    by (auto elim!: invar_props_elims intro: augmenting_path_search_props(1))
  have less: "card (matching_abs (current_matching state))
                < card (matching_abs (Mate.augment_impl (current_matching state) p))"
    by (rule Mate.augmentation_correct(3)[OF inv aug])
  have "matching_abs (Mate.augment_impl (current_matching state) p) \<subseteq> ugraph_abs G"
    using Mate.augmentation_correct(1)[OF inv aug]
    by (auto dest: Mate.invar_matchingD(4))
  hence "card (matching_abs (Mate.augment_impl (current_matching state) p)) \<le> card (ugraph_abs G)"
    by (intro card_mono) simp_all
  hence "call_1_measure (Edmonds_Blossom_Loop_upd1 state) < call_1_measure state"
    using less p
    by (simp add: call_1_measure_def Edmonds_Blossom_Loop_upd1_def)
  thus ?thesis
    by (rule mlex_less)
qed

lemma wf_term_rel: "wf Edmonds_Blossom_Loop_term_rel'"
  by (auto simp: wf_mlex Edmonds_Blossom_Loop_term_rel'_def)

lemma in_Edmonds_Blossom_Loop_term_rel'[termination_intros]:
  "\<lbrakk>Edmonds_Blossom_Loop_call_1_conds state; invar_current_matching state\<rbrakk> \<Longrightarrow>
     (Edmonds_Blossom_Loop_upd1 state, state) \<in> Edmonds_Blossom_Loop_term_rel'"
  by (simp add: Edmonds_Blossom_Loop_term_rel'_def termination_intros)

lemma Edmonds_Blossom_Loop_terminates[termination_intros]:
  assumes "invar_current_matching state"
  shows "Edmonds_Blossom_Loop_dom state"
  using wf_term_rel assms
proof(induction rule: wf_induct_rule)
  case (less x)
  show ?case
    by (rule Edmonds_Blossom_Loop_domintros)
       (auto intro: invar_holds_intros less in_Edmonds_Blossom_Loop_term_rel')
qed

subsection \<open>Correctness\<close>

lemma Edmonds_Blossom_Loop_correct_ret_1:
  "\<lbrakk>invar_current_matching state; Edmonds_Blossom_Loop_ret_1_conds state\<rbrakk>
   \<Longrightarrow> max_card_matching (ugraph_abs G) (matching_abs (current_matching state))"
proof(elim invar_props_elims call_cond_elims)
  assume inv: "matching_invar G (current_matching state)"
     and none: "augmenting_path_search (current_matching state) = None"
  hence "\<nexists>p. graph_augmenting_path (ugraph_abs G) (matching_abs (current_matching state)) p"
    using augmenting_path_search_props(2)
    by blast
  moreover have "matching (matching_abs (current_matching state))"
                "matching_abs (current_matching state) \<subseteq> ugraph_abs G"
                "finite (matching_abs (current_matching state))"
    using matching_invar_props[OF inv]
    by simp_all
  ultimately show ?thesis
    using Berge[of "matching_abs (current_matching state)" "ugraph_abs G"] ugraph_abs_G
    by (auto simp: max_card_matching_def not_le)
qed

lemma ret1_holds[ret_holds_intros]:
  assumes "Edmonds_Blossom_Loop_dom state"
  shows "Edmonds_Blossom_Loop_ret_1_conds (Edmonds_Blossom_Loop state)"
proof(induction rule: Edmonds_Blossom_Loop_induct[OF assms])
  case IH: (1 state)
  show ?case
    apply(rule Edmonds_Blossom_Loop_cases[where state = state])
    by (auto intro!: IH(2-) simp: Edmonds_Blossom_Loop_simps[OF IH(1)])
qed

subsection \<open>The initial state\<close>

lemma initial_state_props[invar_holds_intros, termination_intros]:
  "invar_current_matching initial_state" "Edmonds_Blossom_Loop_dom initial_state"
proof-
  show "invar_current_matching initial_state"
    using Mate.empty_matching_props(1)[of "ugraph_abs G"]
    by (auto intro!: invar_props_intros simp: initial_state_def matching_invar_def)
  thus "Edmonds_Blossom_Loop_dom initial_state"
    by (rule Edmonds_Blossom_Loop_terminates)
qed

lemma Edmonds_Blossom_Loop_impl_to_Edmonds_Blossom_Loop:
  "Edmonds_Blossom_Loop_impl initial_state = Edmonds_Blossom_Loop initial_state"
  by (auto intro!: Edmonds_Blossom_Loop_impl_same initial_state_props)

subsection \<open>Final correctness\<close>

lemma Edmonds_Blossom_Loop_correct_1:
  "max_card_matching (ugraph_abs G)
     (matching_abs (current_matching (Edmonds_Blossom_Loop initial_state)))"
  apply(intro Edmonds_Blossom_Loop_correct_ret_1[where state = "Edmonds_Blossom_Loop initial_state"])
  by(auto intro: invar_holds_intros ret_holds_intros)

lemma Edmonds_Blossom_Loop_correct_2:
  "matching_invar G (current_matching (Edmonds_Blossom_Loop initial_state))"
  using invar_current_matching_holds[OF initial_state_props(2,1)]
  by (auto elim!: invar_props_elims)

end

end
```

---

## Phase 3: the alternating forest search (`Alternating_Forest_Search.thy`)

**Goal.** `Alternating_Forest_Search_run_impl_correct`: under
`Alternating_Forest_Search_axiom`, the result satisfies `compute_alt_path_spec` and is not
`None` when an augmenting path exists. These are the contract clauses of
`Edmonds_Blossom_Subprocedures`.

**Recon.** (a) `term compute_alt_path.search_invars` after the `context compute_alt_path`
block: the argument order of the global constant (expected `G M ex par flabel`); adjust
`invar_forest_def` if it differs. (b) `thm compute_alt_path.invar_init
compute_alt_path.compute_alt_path_dom compute_alt_path.compute_alt_path_from_tree_2'
parent.follow_impl_is_follow follow_impl_def parent_def`. (c) The premises of
`Alternating_Forest_Search.pinduct`, `.psimps`, `.domintros`.
(d) That `abs_search.search_invars` (inside the axiom context) is the same term as the one in
`invar_forest_def`.

**Suggested order of repair.** The abstract section (`search_invars*`) first; then the loop
boilerplate (`_cases`, `_simps`, `_induct`, `_domintros`, twin lemma); then `call_1_facts`,
`call_2_odd`; then the invariant families; then termination; then correctness.

**Frozen statements.** The locale, the record, the loop, all definitions, `search_invars_if1`,
`search_invars_if2_sound`, `search_invars_complete`, the invariant definitions, and
`Alternating_Forest_Search_correct_1/2`, `..._run_impl_correct`. If an invariant turns out to
be too weak for a preservation lemma, strengthening it is a plan change (report it).

**One-shot theory** (copy verbatim into `Edmonds_Blossom_Executable/Alternating_Forest_Search.thy`):

```isabelle
theory Alternating_Forest_Search
  imports Graph_Matching_Specs Blossom.Blossom_Algo_Search
begin

provenance ai

section \<open>The alternating forest search of Edmonds' blossom algorithm\<close>

text \<open>The search grows an alternating forest rooted at the free vertices. Every vertex of the
  forest carries a label: the root of its tree and its parity (even or odd). The search keeps a
  queue of even vertices whose neighbours remain to be scanned, and the list of edges, from the
  even vertex currently being scanned, that remain to be examined. An edge to an unlabelled
  vertex grows the forest by that vertex and its mate; an edge between two even vertices ends the
  search with the two paths from its endpoints to their roots. If every even vertex has been
  scanned, no augmenting path exists.

  The correctness proof reuses the invariants of the abstract search
  @{const compute_alt_path.compute_alt_path}: every growth step of the executable search is a
  step of the abstract search.\<close>

subsection \<open>The abstract search, one state at a time\<close>

context compute_alt_path
begin

definition search_invars where
  "search_invars ex par flabel \<longleftrightarrow>
     (\<forall>v r lab. flabel v = Some (r, lab) \<longrightarrow> alt_labels_invar flabel r (parent_spec.follow par v)) \<and>
     (\<forall>v r. flabel v = Some (r, Even) \<longrightarrow>
        alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd))
                 (parent_spec.follow par v)) \<and>
     parent_spec par \<and> flabel_invar flabel \<and> flabel_par_invar par flabel \<and>
     last_not_matched_invar par flabel \<and> matching_examined_invar flabel ex \<and>
     last_even_invar par flabel \<and> distinct_invar par \<and> path_invar par \<and>
     flabel_invar_2 flabel \<and>
     examined_have_odd_verts_invar ex flabel \<and> unexamined_matched_unlabelled_invar ex flabel \<and>
     finite_odds_invar flabel \<and> odd_labelled_verts_num_invar ex flabel \<and>
     ulabelled_verts_matched_invar ex flabel \<and> odd_then_matched_examined_invar ex flabel \<and>
     finite ex \<and> ex \<subseteq> G"

lemma search_invarsD:
  assumes "search_invars ex par flabel"
  shows "\<And>v r lab. flabel v = Some (r, lab) \<Longrightarrow> alt_labels_invar flabel r (parent_spec.follow par v)"
        "\<And>v r. flabel v = Some (r, Even) \<Longrightarrow>
           alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd))
                    (parent_spec.follow par v)"
        "parent_spec par" "flabel_invar flabel" "flabel_par_invar par flabel"
        "last_not_matched_invar par flabel" "matching_examined_invar flabel ex"
        "last_even_invar par flabel" "distinct_invar par" "path_invar par" "flabel_invar_2 flabel"
        "examined_have_odd_verts_invar ex flabel" "unexamined_matched_unlabelled_invar ex flabel"
        "finite_odds_invar flabel" "odd_labelled_verts_num_invar ex flabel"
        "ulabelled_verts_matched_invar ex flabel" "odd_then_matched_examined_invar ex flabel"
        "finite ex" "ex \<subseteq> G"
  using assms
  by (auto simp: search_invars_def)

lemma search_invars_init:
  "search_invars {} (\<lambda>v. None) (\<lambda>v. if v \<in> Vs G \<and> v \<notin> Vs M then Some (v, Even) else None)"
  using invar_init[where flabel = "\<lambda>v. if v \<in> Vs G \<and> v \<notin> Vs M then Some (v, Even) else None"
                     and ex = "{}" and par = "\<lambda>v. None"]
  by (simp add: search_invars_def)

text \<open>A growth step preserves the invariants. The individual steps are those of the proofs
  of @{thm [source] compute_alt_path_from_tree_1} and @{thm [source] compute_alt_path_from_tree_2'}.\<close>

lemma search_invars_if1:
  assumes invars: "search_invars ex par flabel" and ass: "if1 flabel ex v1 v2 v3 r"
  shows "search_invars (insert {v2, v3} (insert {v1, v2} ex)) (par(v2 \<mapsto> v1, v3 \<mapsto> v2))
           (flabel(v2 \<mapsto> (r, Odd), v3 \<mapsto> (r, Even)))"
proof-
  note I = search_invarsD[OF invars]
  let ?par' = "par(v2 \<mapsto> v1, v3 \<mapsto> v2)"
  let ?flabel' = "flabel(v2 \<mapsto> (r, Odd), v3 \<mapsto> (r, Even))"
  let ?ex' = "insert {v2, v3} (insert {v1, v2} ex)"
  have "parent_spec ?par'"
    using parent_spec_pres(1)[OF I(3,4,5) ass] .
  moreover have "flabel_invar ?flabel'"
    using flabel_invar_pres[OF I(4) ass, of Odd _ Even] .
  moreover have "flabel_par_invar ?par' ?flabel'"
    using flabel_par_invar_pres(1)[OF I(5) ass] .
  moreover have "alt_labels_invar ?flabel' r' (parent_spec.follow ?par' v)"
    if "?flabel' v = Some (r', lab)" for v r' lab
    apply(intro alt_labels_invar_pres[OF ass I(1,2,3,4,5)])
    using that
    by auto
  moreover have "alt_list (\<lambda>v. ?flabel' v = Some (r', Even)) (\<lambda>v. ?flabel' v = Some (r', Odd))
                   (parent_spec.follow ?par' v)"
    if "?flabel' v = Some (r', Even)" for v r'
    using alt_list_pres[OF ass I(2,3,4,5)] that
    by auto
  moreover have "last_not_matched_invar ?par' ?flabel'"
    by (intro last_not_matched_invar_pres(2)[OF ass I(3,4,5,6)])
  moreover have "matching_examined_invar ?flabel' ?ex'"
    using matching_examined_invar_pres[OF I(4,7) ass] .
  moreover have "last_even_invar ?par' ?flabel'"
    using last_even_invar_pres[OF I(3,4,5,8) ass] .
  moreover have "distinct_invar ?par'"
    using distinct_invar_pres[OF I(3,4,5,2,9) ass] .
  moreover have "path_invar ?par'"
    using path_invar_pres[OF I(3,4,5,10) ass] .
  moreover have "flabel_invar_2 ?flabel'"
    by (intro flabel_invar_2_pres[OF _ ass] I(11))
  moreover have "examined_have_odd_verts_invar ?ex' ?flabel'"
    using examined_have_odd_verts_invar_pres(1)[OF I(4,12) ass] .
  moreover have "unexamined_matched_unlabelled_invar ?ex' ?flabel'"
    using unexamined_matched_unlabelled_invar_pres(1)[OF I(4,13) ass] .
  moreover have "finite_odds_invar ?flabel'"
    by (intro finite_odds_invar_pres[where ex = ex and ?v1.0 = v1] I ass)
  moreover have "odd_labelled_verts_num_invar ?ex' ?flabel'"
    by (intro odd_labelled_verts_num_invar_pres[where ex = ex and ?v1.0 = v1] I ass)
  moreover have "ulabelled_verts_matched_invar ?ex' ?flabel'"
    by (intro ulabelled_verts_matched_invar_pres[where ex = ex and ?v1.0 = v1] I ass)
  moreover have "odd_then_matched_examined_invar ?ex' ?flabel'"
    by (intro odd_then_matched_examined_invar_pres[where ex = ex and ?v1.0 = v1] I ass)
  moreover have "finite ?ex'"
    using I(18)
    by simp
  moreover have "?ex' \<subseteq> G"
    using I(19) if1_props(1,4)[OF ass] matching(2)
    by auto
  ultimately show ?thesis
    by (simp add: search_invars_def)
qed

text \<open>An edge between two even vertices yields two paths with the properties required by
  @{const compute_alt_path_spec}. The argument is the returning case of the proof of
  @{thm [source] compute_alt_path_from_tree_1}.\<close>

lemma search_invars_if2_sound:
  assumes invars: "search_invars ex par flabel" and if2: "if2 flabel v1 v2 r s"
  shows "compute_alt_path_spec G M (Some (parent_spec.follow par v1, parent_spec.follow par v2))"
proof-
  note I = search_invarsD[OF invars]
  define p1 where "p1 = parent_spec.follow par v1"
  define p2 where "p2 = parent_spec.follow par v2"
  have s: "flabel v1 = Some (r, Even)" "flabel v2 = Some (s, Even)" "{v1, v2} \<in> G"
    using if2
    by (auto simp: if2_def)
  have prt: "parent par"
    using I(3)
    by (simp add: parent_def)
  have hds: "hd p1 = v1" "hd p2 = v2"
    by (simp_all add: p1_def p2_def parent.follow_hd[OF prt])
  have from_tree:
    "\<And>pref1 x post1 pref2 post2. \<lbrakk>p1 = pref1 @ x # post1; p2 = pref2 @ x # post2\<rbrakk> \<Longrightarrow> post1 = post2"
    using parent.from_tree[OF prt]
    by (fastforce simp: p1_def p2_def)
  have lasts: "last p1 \<notin> Vs M" "last p2 \<notin> Vs M"
    using I(6) s(1,2)
    by (auto simp: last_not_matched_invar_def p1_def p2_def)
  have nM: "{v1, v2} \<notin> M"
    by (rule flabel_invar_2_props[OF I(11) s(1,2)])
  have alt1: "alt_path M (hd p1 # p2)"
  proof-
    have "alt_path (-M) p2"
      unfolding p2_def
      by (rule alt_invars_then_alt_path[OF I(3) I(2)[OF s(2)] I(1)[OF s(2)]])
    moreover have "{hd p1, hd p2} \<notin> M"
      using nM
      by (simp add: hds)
    ultimately show ?thesis
      by (rule nin_M_alt_path[rotated])
  qed
  have alt2: "alt_path M (hd p2 # p1)"
  proof-
    have "alt_path (-M) p1"
      unfolding p1_def
      by (rule alt_invars_then_alt_path[OF I(3) I(2)[OF s(1)] I(1)[OF s(1)]])
    moreover have "{hd p2, hd p1} \<notin> M"
      using nM
      by (simp add: hds insert_commute)
    ultimately show ?thesis
      by (rule nin_M_alt_path[rotated])
  qed
  have "v1 \<noteq> v2"
    using graph s(3)
    by (auto elim: dblton_graphE simp: doubleton_eq_iff)
  hence hds_neq: "hd p1 \<noteq> hd p2"
    by (simp add: hds)
  have odds: "odd (length p1)" "odd (length p2)"
    using last_even_invar_imp[OF I(3) I(2)[OF s(1)] I(8) s(1)]
          last_even_invar_imp[OF I(3) I(2)[OF s(2)] I(8) s(2)]
    by (simp_all add: p1_def p2_def)
  have dists: "distinct p1" "distinct p2"
    by (simp_all add: p1_def p2_def distinct_invar_props[OF I(9)])
  have "v1 \<in> Vs G" "v2 \<in> Vs G"
    using s(3)
    by (auto simp: Vs_def)
  hence paths: "path G p1" "path G p2"
    by (simp_all add: p1_def p2_def path_invar_props[OF I(10)])
  have edge: "{hd p1, hd p2} \<in> G"
    using s(3)
    by (simp add: hds)
  have "compute_alt_path_spec G M (Some (p1, p2))"
    unfolding compute_alt_path_spec_def
    using from_tree alt1 alt2 lasts hds_neq odds dists paths edge
    by auto
  thus ?thesis
    by (simp add: p1_def p2_def)
qed

text \<open>If no growth step applies and no edge joins two even vertices, there is no augmenting
  path. This is the theorem @{thm [source] compute_alt_path_from_tree_2'}, applied at a state at
  which the abstract search returns immediately.\<close>

lemma search_invars_complete:
  assumes invars: "search_invars ex par flabel"
      and no_if1: "\<not> if1_cond flabel ex" and no_if2: "\<not> if2_cond flabel"
  shows "\<nexists>p. matching_augmenting_path M p \<and> path G p \<and> distinct p"
proof-
  note I = search_invarsD[OF invars]
  have dom: "compute_alt_path_dom (ex, par, flabel)"
    by (rule compute_alt_path_dom[OF I(18,19)])
  have "compute_alt_path ex par flabel = None"
    using no_if1 no_if2
    by (simp add: compute_alt_path.psimps[OF dom] Let_def)
  thus ?thesis
    by (rule compute_alt_path_from_tree_2'[OF I(4,12,13,14,15,16,17) _ I(18,19)])
qed

end

subsection \<open>Edges of a forest given by parent pointers\<close>

definition "forest_edges par = {{a, b} | a b. par a = Some b}"

lemma forest_edges_empty[simp]: "forest_edges (\<lambda>v. None) = {}"
  by (simp add: forest_edges_def)

lemma forest_edges_update:
  assumes "par w = None" "par x = None" "w \<noteq> x"
  shows "forest_edges (par(w \<mapsto> v, x \<mapsto> w)) = insert {w, x} (insert {v, w} (forest_edges par))"
proof(intro equalityI subsetI)
  fix e
  assume "e \<in> forest_edges (par(w \<mapsto> v, x \<mapsto> w))"
  then obtain a b where e: "e = {a, b}" "(par(w \<mapsto> v, x \<mapsto> w)) a = Some b"
    by (auto simp: forest_edges_def)
  show "e \<in> insert {w, x} (insert {v, w} (forest_edges par))"
  proof(cases "a = x")
    case True
    then show ?thesis
      using e
      by (auto simp: insert_commute)
  next
    case False
    show ?thesis
    proof(cases "a = w")
      case True
      then show ?thesis
        using e \<open>a \<noteq> x\<close>
        by (auto simp: insert_commute)
    next
      case False
      then show ?thesis
        using e \<open>a \<noteq> x\<close>
        by (auto simp: forest_edges_def)
    qed
  qed
next
  fix e
  assume "e \<in> insert {w, x} (insert {v, w} (forest_edges par))"
  then consider "e = {w, x}" | "e = {v, w}" | "e \<in> forest_edges par"
    by blast
  then show "e \<in> forest_edges (par(w \<mapsto> v, x \<mapsto> w))"
  proof cases
    case 1
    then show ?thesis
      by (auto simp: forest_edges_def insert_commute intro!: exI[of _ x] exI[of _ w])
  next
    case 2
    then show ?thesis
      using assms(3)
      by (auto simp: forest_edges_def insert_commute intro!: exI[of _ w] exI[of _ v])
  next
    case 3
    then obtain a b where ab: "e = {a, b}" "par a = Some b"
      by (auto simp: forest_edges_def)
    moreover have "a \<noteq> w" "a \<noteq> x"
      using ab(2) assms(1,2)
      by auto
    ultimately show ?thesis
      by (auto simp: forest_edges_def)
  qed
qed

subsection \<open>The program state\<close>

record ('v, 'parents, 'labels) Alternating_Forest_Search_state =
  queue :: "'v list"
  unscanned :: "('v \<times> 'v) list"
  forest_parents :: 'parents
  forest_labels :: 'labels

subsection \<open>Setup for automation\<close>

named_theorems call_cond_elims
named_theorems call_cond_intros
named_theorems ret_holds_intros
named_theorems invar_props_intros
named_theorems invar_props_elims
named_theorems invar_holds_intros
named_theorems state_rel_intros
named_theorems state_rel_holds_intros

subsection \<open>The loop\<close>

locale Alternating_Forest_Search =
  Graph_Matching_Specs where lookup = lookup +
  Parent: Map parent_empty parent_update parent_delete parent_lookup parent_invar +
  Label: Map label_empty label_update label_delete label_lookup label_invar
  for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option"
  and parent_empty :: 'parents
  and parent_update :: "'v \<Rightarrow> 'v \<Rightarrow> 'parents \<Rightarrow> 'parents"
  and parent_delete :: "'v \<Rightarrow> 'parents \<Rightarrow> 'parents"
  and parent_lookup :: "'parents \<Rightarrow> 'v \<Rightarrow> 'v option"
  and parent_invar :: "'parents \<Rightarrow> bool"
  and label_empty :: 'labels
  and label_update :: "'v \<Rightarrow> 'v \<times> label \<Rightarrow> 'labels \<Rightarrow> 'labels"
  and label_delete :: "'v \<Rightarrow> 'labels \<Rightarrow> 'labels"
  and label_lookup :: "'labels \<Rightarrow> 'v \<Rightarrow> ('v \<times> label) option"
  and label_invar :: "'labels \<Rightarrow> bool" +
  fixes G :: 'adjmap and vs :: "'v list" and M :: 'mate
begin

definition "Alternating_Forest_Search_axiom \<longleftrightarrow> graph_input G vs \<and> matching_invar G M"

abbreviation "abs_parents state \<equiv> parent_lookup (forest_parents state)"
abbreviation "abs_labels state \<equiv> label_lookup (forest_labels state)"
abbreviation "abs_examined state \<equiv> forest_edges (abs_parents state)"

function (domintros) Alternating_Forest_Search ::
  "('v, 'parents, 'labels) Alternating_Forest_Search_state \<Rightarrow>
   ('v, 'parents, 'labels) Alternating_Forest_Search_state" where
  "Alternating_Forest_Search state =
     (case unscanned state of
        (v, w) # es \<Rightarrow>
          (case label_lookup (forest_labels state) w of
             None \<Rightarrow>
               (case mate_lookup M w of
                  Some x \<Rightarrow>
                    (let r = fst (the (label_lookup (forest_labels state) v)) in
                     Alternating_Forest_Search
                       (state \<lparr>queue := x # queue state, unscanned := es,
                               forest_parents :=
                                 parent_update x w (parent_update w v (forest_parents state)),
                               forest_labels :=
                                 label_update x (r, Even)
                                   (label_update w (r, Odd) (forest_labels state))\<rparr>))
                | None \<Rightarrow> Alternating_Forest_Search (state \<lparr>unscanned := es\<rparr>))
           | Some (r, Even) \<Rightarrow> state
           | Some (r, Odd) \<Rightarrow> Alternating_Forest_Search (state \<lparr>unscanned := es\<rparr>))
      | [] \<Rightarrow>
          (case queue state of
             v # q \<Rightarrow>
               Alternating_Forest_Search
                 (state \<lparr>queue := q, unscanned := map (Pair v) (neighbour_list G v)\<rparr>)
           | [] \<Rightarrow> state))"
  by pat_completeness auto

partial_function (tailrec) Alternating_Forest_Search_impl ::
  "('v, 'parents, 'labels) Alternating_Forest_Search_state \<Rightarrow>
   ('v, 'parents, 'labels) Alternating_Forest_Search_state" where
  "Alternating_Forest_Search_impl state =
     (case unscanned state of
        (v, w) # es \<Rightarrow>
          (case label_lookup (forest_labels state) w of
             None \<Rightarrow>
               (case mate_lookup M w of
                  Some x \<Rightarrow>
                    (let r = fst (the (label_lookup (forest_labels state) v)) in
                     Alternating_Forest_Search_impl
                       (state \<lparr>queue := x # queue state, unscanned := es,
                               forest_parents :=
                                 parent_update x w (parent_update w v (forest_parents state)),
                               forest_labels :=
                                 label_update x (r, Even)
                                   (label_update w (r, Odd) (forest_labels state))\<rparr>))
                | None \<Rightarrow> Alternating_Forest_Search_impl (state \<lparr>unscanned := es\<rparr>))
           | Some (r, Even) \<Rightarrow> state
           | Some (r, Odd) \<Rightarrow> Alternating_Forest_Search_impl (state \<lparr>unscanned := es\<rparr>))
      | [] \<Rightarrow>
          (case queue state of
             v # q \<Rightarrow>
               Alternating_Forest_Search_impl
                 (state \<lparr>queue := q, unscanned := map (Pair v) (neighbour_list G v)\<rparr>)
           | [] \<Rightarrow> state))"

lemma Alternating_Forest_Search_impl_same:
  assumes "Alternating_Forest_Search_dom state"
  shows "Alternating_Forest_Search_impl state = Alternating_Forest_Search state"
  apply(induction rule: Alternating_Forest_Search.pinduct[OF assms])
  apply(subst Alternating_Forest_Search_impl.simps)
  by (auto simp: Alternating_Forest_Search.psimps Let_def
          split: list.splits prod.splits option.splits label.splits)

definition "free_vertices = filter (\<lambda>v. neighbour_list G v \<noteq> [] \<and> mate_lookup M v = None) vs"

definition "initial_labels =
  foldr (\<lambda>v l. label_update v (v, Even) l) free_vertices label_empty"

definition "initial_state =
  \<lparr>queue = free_vertices, unscanned = [], forest_parents = parent_empty,
   forest_labels = initial_labels\<rparr>"

text \<open>The answer is read off the final state: if the search stopped at an edge between two even
  vertices, the two paths from its endpoints to their roots.\<close>

definition "alternating_paths state =
  (case unscanned state of
     (v, w) # _ \<Rightarrow> Some (follow_impl (parent_lookup (forest_parents state)) v,
                         follow_impl (parent_lookup (forest_parents state)) w)
   | [] \<Rightarrow> None)"

definition "Alternating_Forest_Search_run = alternating_paths (Alternating_Forest_Search initial_state)"

definition "Alternating_Forest_Search_run_impl =
  alternating_paths (Alternating_Forest_Search_impl initial_state)"

lemmas [code] = Alternating_Forest_Search_impl.simps free_vertices_def initial_labels_def
  initial_state_def alternating_paths_def Alternating_Forest_Search_run_impl_def

definition "Alternating_Forest_Search_call_1_conds state =
  (\<exists>v w es x. unscanned state = (v, w) # es \<and> label_lookup (forest_labels state) w = None \<and>
              mate_lookup M w = Some x)"

definition "Alternating_Forest_Search_upd1 state =
  (case unscanned state of
     (v, w) # es \<Rightarrow>
       (let x = the (mate_lookup M w); r = fst (the (label_lookup (forest_labels state) v)) in
        state \<lparr>queue := x # queue state, unscanned := es,
               forest_parents := parent_update x w (parent_update w v (forest_parents state)),
               forest_labels :=
                 label_update x (r, Even) (label_update w (r, Odd) (forest_labels state))\<rparr>)
   | [] \<Rightarrow> state)"

definition "Alternating_Forest_Search_call_2_conds state =
  (\<exists>v w es. unscanned state = (v, w) # es \<and>
            (\<forall>r. label_lookup (forest_labels state) w \<noteq> Some (r, Even)) \<and>
            (label_lookup (forest_labels state) w = None \<longrightarrow> mate_lookup M w = None))"

definition "Alternating_Forest_Search_upd2 state = state \<lparr>unscanned := tl (unscanned state)\<rparr>"

definition "Alternating_Forest_Search_call_3_conds state =
  (\<exists>v q. unscanned state = [] \<and> queue state = v # q)"

definition "Alternating_Forest_Search_upd3 state =
  (case queue state of
     v # q \<Rightarrow> state \<lparr>queue := q, unscanned := map (Pair v) (neighbour_list G v)\<rparr>
   | [] \<Rightarrow> state)"

definition "Alternating_Forest_Search_ret_1_conds state =
  (\<exists>v w es r. unscanned state = (v, w) # es \<and> label_lookup (forest_labels state) w = Some (r, Even))"

abbreviation "Alternating_Forest_Search_ret1 state \<equiv> state"

definition "Alternating_Forest_Search_ret_2_conds state =
  (unscanned state = [] \<and> queue state = [])"

abbreviation "Alternating_Forest_Search_ret2 state \<equiv> state"

definition "invar_1 state \<longleftrightarrow>
  parent_invar (forest_parents state) \<and> label_invar (forest_labels state)"

definition "invar_forest state \<longleftrightarrow>
  compute_alt_path.search_invars (ugraph_abs G) (matching_abs M)
    (abs_examined state) (abs_parents state) (abs_labels state)"

definition "invar_unscanned state \<longleftrightarrow>
  (\<forall>v w. (v, w) \<in> set (unscanned state) \<longrightarrow>
     {v, w} \<in> ugraph_abs G \<and> (\<exists>r. label_lookup (forest_labels state) v = Some (r, Even)))"

definition "invar_queue state \<longleftrightarrow>
  (\<forall>v \<in> set (queue state). \<exists>r. label_lookup (forest_labels state) v = Some (r, Even))"

definition "invar_scanned state \<longleftrightarrow>
  (\<forall>v r. label_lookup (forest_labels state) v = Some (r, Even) \<longrightarrow>
     v \<in> set (queue state) \<or>
     (\<forall>w. {v, w} \<in> ugraph_abs G \<longrightarrow>
        (v, w) \<in> set (unscanned state) \<or>
        (\<exists>r'. label_lookup (forest_labels state) w = Some (r', Odd))))"

definition "call_1_measure state =
  card {v \<in> Vs (ugraph_abs G). label_lookup (forest_labels state) v = None}"

definition "call_2_measure state = length (unscanned state)"

definition "call_3_measure state = length (queue state)"

definition "Alternating_Forest_Search_term_rel' =
  call_1_measure <*mlex*> call_3_measure <*mlex*> call_2_measure <*mlex*> {}"

lemma Alternating_Forest_Search_call_1_conds[call_cond_elims]:
  "Alternating_Forest_Search_call_1_conds state \<Longrightarrow>
   (\<lbrakk>\<exists>v w es x. unscanned state = (v, w) # es \<and> label_lookup (forest_labels state) w = None \<and>
                mate_lookup M w = Some x\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: Alternating_Forest_Search_call_1_conds_def)

lemma Alternating_Forest_Search_call_1_condsI[call_cond_intros]:
  "\<lbrakk>unscanned state = (v, w) # es; label_lookup (forest_labels state) w = None;
    mate_lookup M w = Some x\<rbrakk> \<Longrightarrow> Alternating_Forest_Search_call_1_conds state"
  by (auto simp: Alternating_Forest_Search_call_1_conds_def)

lemma Alternating_Forest_Search_call_2_conds[call_cond_elims]:
  "Alternating_Forest_Search_call_2_conds state \<Longrightarrow>
   (\<lbrakk>\<exists>v w es. unscanned state = (v, w) # es \<and>
              (\<forall>r. label_lookup (forest_labels state) w \<noteq> Some (r, Even)) \<and>
              (label_lookup (forest_labels state) w = None \<longrightarrow> mate_lookup M w = None)\<rbrakk> \<Longrightarrow> P)
   \<Longrightarrow> P"
  by (auto simp: Alternating_Forest_Search_call_2_conds_def)

lemma Alternating_Forest_Search_call_2_condsI[call_cond_intros]:
  "\<lbrakk>unscanned state = (v, w) # es; \<forall>r. label_lookup (forest_labels state) w \<noteq> Some (r, Even);
    label_lookup (forest_labels state) w = None \<longrightarrow> mate_lookup M w = None\<rbrakk>
   \<Longrightarrow> Alternating_Forest_Search_call_2_conds state"
  by (auto simp: Alternating_Forest_Search_call_2_conds_def)

lemma Alternating_Forest_Search_call_3_conds[call_cond_elims]:
  "Alternating_Forest_Search_call_3_conds state \<Longrightarrow>
   (\<lbrakk>unscanned state = []; \<exists>v q. queue state = v # q\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: Alternating_Forest_Search_call_3_conds_def)

lemma Alternating_Forest_Search_call_3_condsI[call_cond_intros]:
  "\<lbrakk>unscanned state = []; queue state = v # q\<rbrakk> \<Longrightarrow> Alternating_Forest_Search_call_3_conds state"
  by (auto simp: Alternating_Forest_Search_call_3_conds_def)

lemma Alternating_Forest_Search_ret_1_conds[call_cond_elims]:
  "Alternating_Forest_Search_ret_1_conds state \<Longrightarrow>
   (\<lbrakk>\<exists>v w es r. unscanned state = (v, w) # es \<and>
                label_lookup (forest_labels state) w = Some (r, Even)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: Alternating_Forest_Search_ret_1_conds_def)

lemma Alternating_Forest_Search_ret_1_condsI[call_cond_intros]:
  "\<lbrakk>unscanned state = (v, w) # es; label_lookup (forest_labels state) w = Some (r, Even)\<rbrakk>
   \<Longrightarrow> Alternating_Forest_Search_ret_1_conds state"
  by (auto simp: Alternating_Forest_Search_ret_1_conds_def)

lemma Alternating_Forest_Search_ret_2_conds[call_cond_elims]:
  "Alternating_Forest_Search_ret_2_conds state \<Longrightarrow>
   (\<lbrakk>unscanned state = []; queue state = []\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: Alternating_Forest_Search_ret_2_conds_def)

lemma Alternating_Forest_Search_ret_2_condsI[call_cond_intros]:
  "\<lbrakk>unscanned state = []; queue state = []\<rbrakk> \<Longrightarrow> Alternating_Forest_Search_ret_2_conds state"
  by (auto simp: Alternating_Forest_Search_ret_2_conds_def)

lemma Alternating_Forest_Search_cases:
  assumes "Alternating_Forest_Search_call_1_conds state \<Longrightarrow> P"
          "Alternating_Forest_Search_call_2_conds state \<Longrightarrow> P"
          "Alternating_Forest_Search_call_3_conds state \<Longrightarrow> P"
          "Alternating_Forest_Search_ret_1_conds state \<Longrightarrow> P"
          "Alternating_Forest_Search_ret_2_conds state \<Longrightarrow> P"
  shows "P"
proof(cases "unscanned state")
  case Nil
  then show ?thesis
    using assms(3,5)
    by (cases "queue state")
       (auto simp: Alternating_Forest_Search_call_3_conds_def
                   Alternating_Forest_Search_ret_2_conds_def)
next
  case (Cons e es)
  obtain v w where e: "e = (v, w)"
    by (cases e)
  show ?thesis
  proof(cases "label_lookup (forest_labels state) w")
    case None
    then show ?thesis
      using assms(1,2) Cons e
      by (cases "mate_lookup M w")
         (auto simp: Alternating_Forest_Search_call_1_conds_def
                     Alternating_Forest_Search_call_2_conds_def)
  next
    case (Some rl)
    obtain r l where rl: "rl = (r, l)"
      by (cases rl)
    show ?thesis
      using assms(2,4) Cons e Some rl
      by (cases l)
         (auto simp: Alternating_Forest_Search_call_2_conds_def
                     Alternating_Forest_Search_ret_1_conds_def)
  qed
qed

lemma Alternating_Forest_Search_simps:
  assumes "Alternating_Forest_Search_dom state"
  shows "Alternating_Forest_Search_call_1_conds state \<Longrightarrow>
           Alternating_Forest_Search state =
             Alternating_Forest_Search (Alternating_Forest_Search_upd1 state)"
        "Alternating_Forest_Search_call_2_conds state \<Longrightarrow>
           Alternating_Forest_Search state =
             Alternating_Forest_Search (Alternating_Forest_Search_upd2 state)"
        "Alternating_Forest_Search_call_3_conds state \<Longrightarrow>
           Alternating_Forest_Search state =
             Alternating_Forest_Search (Alternating_Forest_Search_upd3 state)"
        "Alternating_Forest_Search_ret_1_conds state \<Longrightarrow>
           Alternating_Forest_Search state = Alternating_Forest_Search_ret1 state"
        "Alternating_Forest_Search_ret_2_conds state \<Longrightarrow>
           Alternating_Forest_Search state = Alternating_Forest_Search_ret2 state"
  by (auto simp: Alternating_Forest_Search.psimps[OF assms] Let_def
                 Alternating_Forest_Search_call_1_conds_def Alternating_Forest_Search_upd1_def
                 Alternating_Forest_Search_call_2_conds_def Alternating_Forest_Search_upd2_def
                 Alternating_Forest_Search_call_3_conds_def Alternating_Forest_Search_upd3_def
                 Alternating_Forest_Search_ret_1_conds_def Alternating_Forest_Search_ret_2_conds_def
          split: option.splits label.splits)

lemma Alternating_Forest_Search_induct:
  assumes "Alternating_Forest_Search_dom state"
  assumes "\<And>state. \<lbrakk>Alternating_Forest_Search_dom state;
                     Alternating_Forest_Search_call_1_conds state \<Longrightarrow>
                       P (Alternating_Forest_Search_upd1 state);
                     Alternating_Forest_Search_call_2_conds state \<Longrightarrow>
                       P (Alternating_Forest_Search_upd2 state);
                     Alternating_Forest_Search_call_3_conds state \<Longrightarrow>
                       P (Alternating_Forest_Search_upd3 state)\<rbrakk>
                    \<Longrightarrow> P state"
  shows "P state"
  apply(rule Alternating_Forest_Search.pinduct[OF assms(1)])
  apply(rule assms(2))
  by (auto simp: Let_def
                 Alternating_Forest_Search_call_1_conds_def Alternating_Forest_Search_upd1_def
                 Alternating_Forest_Search_call_2_conds_def Alternating_Forest_Search_upd2_def
                 Alternating_Forest_Search_call_3_conds_def Alternating_Forest_Search_upd3_def)

lemma Alternating_Forest_Search_domintros:
  assumes "Alternating_Forest_Search_call_1_conds state \<Longrightarrow>
             Alternating_Forest_Search_dom (Alternating_Forest_Search_upd1 state)"
          "Alternating_Forest_Search_call_2_conds state \<Longrightarrow>
             Alternating_Forest_Search_dom (Alternating_Forest_Search_upd2 state)"
          "Alternating_Forest_Search_call_3_conds state \<Longrightarrow>
             Alternating_Forest_Search_dom (Alternating_Forest_Search_upd3 state)"
  shows "Alternating_Forest_Search_dom state"
  using assms
  by (auto intro!: Alternating_Forest_Search.domintros
             simp: Let_def
                   Alternating_Forest_Search_call_1_conds_def Alternating_Forest_Search_upd1_def
                   Alternating_Forest_Search_call_2_conds_def Alternating_Forest_Search_upd2_def
                   Alternating_Forest_Search_call_3_conds_def Alternating_Forest_Search_upd3_def)

subsection \<open>Data-structure facts\<close>

lemma upd1_abs:
  assumes "invar_1 state" "unscanned state = (v, w) # es" "mate_lookup M w = Some x"
          "label_lookup (forest_labels state) v = Some (r, Even)"
  shows "abs_parents (Alternating_Forest_Search_upd1 state) = (abs_parents state)(w \<mapsto> v, x \<mapsto> w)"
        "abs_labels (Alternating_Forest_Search_upd1 state) =
           (abs_labels state)(w \<mapsto> (r, Odd), x \<mapsto> (r, Even))"
        "queue (Alternating_Forest_Search_upd1 state) = x # queue state"
        "unscanned (Alternating_Forest_Search_upd1 state) = es"
        "invar_1 (Alternating_Forest_Search_upd1 state)"
  using assms
  by (auto simp: invar_1_def Alternating_Forest_Search_upd1_def Parent.map_update Label.map_update
                 Parent.invar_update Label.invar_update)

lemma upd2_abs[simp]:
  "abs_parents (Alternating_Forest_Search_upd2 state) = abs_parents state"
  "abs_labels (Alternating_Forest_Search_upd2 state) = abs_labels state"
  "queue (Alternating_Forest_Search_upd2 state) = queue state"
  "unscanned (Alternating_Forest_Search_upd2 state) = tl (unscanned state)"
  by (simp_all add: Alternating_Forest_Search_upd2_def)

lemma upd3_abs:
  assumes "queue state = v # q"
  shows "abs_parents (Alternating_Forest_Search_upd3 state) = abs_parents state"
        "abs_labels (Alternating_Forest_Search_upd3 state) = abs_labels state"
        "queue (Alternating_Forest_Search_upd3 state) = q"
        "unscanned (Alternating_Forest_Search_upd3 state) = map (Pair v) (neighbour_list G v)"
  using assms
  by (simp_all add: Alternating_Forest_Search_upd3_def)

lemma label_foldr:
  "label_invar (foldr (\<lambda>v l. label_update v (v, Even) l) xs label_empty) \<and>
   label_lookup (foldr (\<lambda>v l. label_update v (v, Even) l) xs label_empty) =
     (\<lambda>v. if v \<in> set xs then Some (v, Even) else None)"
  by (induction xs)
     (auto simp: Label.map_empty Label.invar_empty Label.map_update Label.invar_update fun_eq_iff)

lemma follow_impl_eq:
  assumes "parent_spec par"
  shows "follow_impl par = parent_spec.follow par"
proof-
  interpret par_here: parent par
    using assms
    by (simp add: parent_def)
  show ?thesis
    using par_here.follow_impl_is_follow[folded follow_impl_def] .
qed

subsection \<open>Proofs\<close>

context
  assumes Alternating_Forest_Search_axiom: Alternating_Forest_Search_axiom
begin

lemma graph_input_G[simp]: "graph_input G vs"
  and matching_invar_M[simp]: "matching_invar G M"
  using Alternating_Forest_Search_axiom
  by (simp_all add: Alternating_Forest_Search_axiom_def)

interpretation abs_search: compute_alt_path "ugraph_abs G" "matching_abs M" "\<lambda>S. SOME x. x \<in> S"
  apply unfold_locales
  using ugraph_abs_graph_invar[OF graph_input_G] matching_invar_props[OF matching_invar_M]
  by (auto intro: someI_ex)

lemma finite_Vs_G[simp]: "finite (Vs (ugraph_abs G))"
  using ugraph_abs_graph_invar[OF graph_input_G]
  by simp

lemma Vs_G_subset_vs: "Vs (ugraph_abs G) \<subseteq> set vs"
  by (rule Vs_ugraph_abs_subset_vs[OF graph_input_G])

lemma mate_lookup_iff: "mate_lookup M u = Some v \<longleftrightarrow> {u, v} \<in> matching_abs M"
  using matching_invar_M
  by (simp add: matching_invar_def matching_abs_iff)

lemma Vs_matching_iff: "u \<in> Vs (matching_abs M) \<longleftrightarrow> mate_lookup M u \<noteq> None"
  using matching_invar_M
  by (simp add: matching_invar_def Vs_matching_abs_iff)

lemma set_free_vertices:
  "set free_vertices = {v. v \<in> Vs (ugraph_abs G) \<and> v \<notin> Vs (matching_abs M)}"
  using Vs_G_subset_vs
  by (auto simp: free_vertices_def neighbour_list_nonempty_iff[OF graph_input_G] Vs_matching_iff)

lemma initial_labels:
  "label_invar initial_labels"
  "label_lookup initial_labels =
     (\<lambda>v. if v \<in> Vs (ugraph_abs G) \<and> v \<notin> Vs (matching_abs M) then Some (v, Even) else None)"
  using label_foldr[of free_vertices]
  by (auto simp: initial_labels_def set_free_vertices fun_eq_iff)

subsubsection \<open>Facts about the branches\<close>

lemma call_1_facts:
  assumes "Alternating_Forest_Search_call_1_conds state" "invar_forest state"
          "invar_unscanned state"
  obtains v w es x r where
    "unscanned state = (v, w) # es" "label_lookup (forest_labels state) w = None"
    "mate_lookup M w = Some x" "label_lookup (forest_labels state) v = Some (r, Even)"
    "{v, w} \<in> ugraph_abs G" "label_lookup (forest_labels state) x = None" "w \<noteq> x"
    "abs_search.if1 (abs_labels state) (abs_examined state) v w x r"
proof-
  obtain v w es x where vw: "unscanned state = (v, w) # es"
      "label_lookup (forest_labels state) w = None" "mate_lookup M w = Some x"
    using assms(1)
    by (auto elim!: call_cond_elims)
  obtain r where r: "label_lookup (forest_labels state) v = Some (r, Even)" "{v, w} \<in> ugraph_abs G"
    using assms(3) vw(1)
    by (auto simp: invar_unscanned_def)
  have I: "abs_search.search_invars (abs_examined state) (abs_parents state) (abs_labels state)"
    using assms(2)
    by (simp add: invar_forest_def)
  have wx: "{w, x} \<in> matching_abs M"
    using vw(3)
    by (simp add: mate_lookup_iff)
  have par_w: "abs_parents state w = None" "\<forall>v'. abs_parents state v' \<noteq> Some w"
    using abs_search.search_invarsD(5)[OF I] vw(2)
    by (auto simp: abs_search.flabel_par_invar_def)
  hence "{v, w} \<notin> abs_examined state"
    by (auto simp: forest_edges_def doubleton_eq_iff)
  hence if1: "abs_search.if1 (abs_labels state) (abs_examined state) v w x r"
    using r vw(2) wx
    by (simp add: abs_search.if1_def)
  have "label_lookup (forest_labels state) x = None"
    using abs_search.flabel_invar_props[OF abs_search.search_invarsD(4)[OF I] wx vw(2)] .
  moreover have "w \<noteq> x"
    using abs_search.v1_neq_v2_neq_v3(2)[OF if1] .
  ultimately show ?thesis
    using that vw r if1
    by blast
qed

lemma call_2_odd:
  assumes "Alternating_Forest_Search_call_2_conds state" "invar_forest state"
          "invar_unscanned state"
  obtains v w es r where "unscanned state = (v, w) # es"
    "label_lookup (forest_labels state) w = Some (r, Odd)"
proof-
  obtain v w es where vw: "unscanned state = (v, w) # es"
      "\<forall>r. label_lookup (forest_labels state) w \<noteq> Some (r, Even)"
      "label_lookup (forest_labels state) w = None \<longrightarrow> mate_lookup M w = None"
    using assms(1)
    by (auto elim!: call_cond_elims)
  have "{v, w} \<in> ugraph_abs G"
    using assms(3) vw(1)
    by (auto simp: invar_unscanned_def)
  hence w_in: "w \<in> Vs (ugraph_abs G)"
    by (auto simp: Vs_def)
  have I: "abs_search.search_invars (abs_examined state) (abs_parents state) (abs_labels state)"
    using assms(2)
    by (simp add: invar_forest_def)
  have "label_lookup (forest_labels state) w \<noteq> None"
  proof
    assume none: "label_lookup (forest_labels state) w = None"
    hence "\<exists>e \<in> matching_abs M - abs_examined state. w \<in> e"
      using abs_search.search_invarsD(16)[OF I] w_in
      by (auto simp: abs_search.ulabelled_verts_matched_invar_def)
    hence "w \<in> Vs (matching_abs M)"
      by (auto simp: Vs_def)
    thus False
      using vw(3) none
      by (simp add: Vs_matching_iff)
  qed
  then obtain r l where "label_lookup (forest_labels state) w = Some (r, l)"
    by auto
  moreover hence "l = Odd"
    using vw(2)
    by (cases l) auto
  ultimately show ?thesis
    using that vw(1)
    by blast
qed

subsubsection \<open>The representation invariant\<close>

lemma invar_1_props[invar_props_elims]:
  "invar_1 state \<Longrightarrow>
   (\<lbrakk>parent_invar (forest_parents state); label_invar (forest_labels state)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_1_def)

lemma invar_1_intro[invar_props_intros]:
  "\<lbrakk>parent_invar (forest_parents state); label_invar (forest_labels state)\<rbrakk> \<Longrightarrow> invar_1 state"
  by (auto simp: invar_1_def)

lemma invar_1_holds_1[invar_holds_intros]:
  assumes "Alternating_Forest_Search_call_1_conds state" "invar_1 state" "invar_forest state"
          "invar_unscanned state"
  shows "invar_1 (Alternating_Forest_Search_upd1 state)"
proof-
  obtain v w es x r where f:
    "unscanned state = (v, w) # es" "label_lookup (forest_labels state) w = None"
    "mate_lookup M w = Some x" "label_lookup (forest_labels state) v = Some (r, Even)"
    "{v, w} \<in> ugraph_abs G" "label_lookup (forest_labels state) x = None" "w \<noteq> x"
    "abs_search.if1 (abs_labels state) (abs_examined state) v w x r"
    by (rule call_1_facts[OF assms(1,3,4)])
  show ?thesis
    by (rule upd1_abs(5)[OF assms(2) f(1,3,4)])
qed

lemma invar_1_holds_2[invar_holds_intros]:
  "\<lbrakk>Alternating_Forest_Search_call_2_conds state; invar_1 state\<rbrakk>
   \<Longrightarrow> invar_1 (Alternating_Forest_Search_upd2 state)"
  by (auto simp: invar_1_def Alternating_Forest_Search_upd2_def)

lemma invar_1_holds_3[invar_holds_intros]:
  "\<lbrakk>Alternating_Forest_Search_call_3_conds state; invar_1 state\<rbrakk>
   \<Longrightarrow> invar_1 (Alternating_Forest_Search_upd3 state)"
  by (auto simp: invar_1_def Alternating_Forest_Search_upd3_def split: list.splits)

lemma invar_1_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>Alternating_Forest_Search_ret_1_conds state; invar_1 state\<rbrakk>
   \<Longrightarrow> invar_1 (Alternating_Forest_Search_ret1 state)"
  by auto

lemma invar_1_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>Alternating_Forest_Search_ret_2_conds state; invar_1 state\<rbrakk>
   \<Longrightarrow> invar_1 (Alternating_Forest_Search_ret2 state)"
  by auto

subsubsection \<open>The invariants of the abstract search\<close>

lemma invar_forest_props[invar_props_elims]:
  "invar_forest state \<Longrightarrow>
   (abs_search.search_invars (abs_examined state) (abs_parents state) (abs_labels state) \<Longrightarrow> P)
   \<Longrightarrow> P"
  by (auto simp: invar_forest_def)

lemma invar_forest_intro[invar_props_intros]:
  "abs_search.search_invars (abs_examined state) (abs_parents state) (abs_labels state)
   \<Longrightarrow> invar_forest state"
  by (auto simp: invar_forest_def)

lemma invar_forest_holds_1[invar_holds_intros]:
  assumes "Alternating_Forest_Search_call_1_conds state" "invar_1 state" "invar_forest state"
          "invar_unscanned state"
  shows "invar_forest (Alternating_Forest_Search_upd1 state)"
proof-
  obtain v w es x r where f:
    "unscanned state = (v, w) # es" "label_lookup (forest_labels state) w = None"
    "mate_lookup M w = Some x" "label_lookup (forest_labels state) v = Some (r, Even)"
    "{v, w} \<in> ugraph_abs G" "label_lookup (forest_labels state) x = None" "w \<noteq> x"
    "abs_search.if1 (abs_labels state) (abs_examined state) v w x r"
    by (rule call_1_facts[OF assms(1,3,4)])
  have I: "abs_search.search_invars (abs_examined state) (abs_parents state) (abs_labels state)"
    using assms(3)
    by (simp add: invar_forest_def)
  have none: "abs_parents state w = None" "abs_parents state x = None"
    using abs_search.search_invarsD(5)[OF I] f(2,6)
    by (auto simp: abs_search.flabel_par_invar_def)
  show ?thesis
    using abs_search.search_invars_if1[OF I f(8)] forest_edges_update[OF none f(7)]
    by (simp add: invar_forest_def upd1_abs[OF assms(2) f(1,3,4)])
qed

lemma invar_forest_holds_2[invar_holds_intros]:
  "\<lbrakk>Alternating_Forest_Search_call_2_conds state; invar_forest state\<rbrakk>
   \<Longrightarrow> invar_forest (Alternating_Forest_Search_upd2 state)"
  by (simp add: invar_forest_def)

lemma invar_forest_holds_3[invar_holds_intros]:
  "\<lbrakk>Alternating_Forest_Search_call_3_conds state; invar_forest state\<rbrakk>
   \<Longrightarrow> invar_forest (Alternating_Forest_Search_upd3 state)"
  by (auto elim!: call_cond_elims simp: invar_forest_def upd3_abs)

lemma invar_forest_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>Alternating_Forest_Search_ret_1_conds state; invar_forest state\<rbrakk>
   \<Longrightarrow> invar_forest (Alternating_Forest_Search_ret1 state)"
  by auto

lemma invar_forest_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>Alternating_Forest_Search_ret_2_conds state; invar_forest state\<rbrakk>
   \<Longrightarrow> invar_forest (Alternating_Forest_Search_ret2 state)"
  by auto

subsubsection \<open>The edges that remain to be examined\<close>

lemma invar_unscanned_props[invar_props_elims]:
  "invar_unscanned state \<Longrightarrow>
   ((\<forall>v w. (v, w) \<in> set (unscanned state) \<longrightarrow>
       {v, w} \<in> ugraph_abs G \<and> (\<exists>r. label_lookup (forest_labels state) v = Some (r, Even)))
    \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_unscanned_def)

lemma invar_unscanned_intro[invar_props_intros]:
  "(\<forall>v w. (v, w) \<in> set (unscanned state) \<longrightarrow>
      {v, w} \<in> ugraph_abs G \<and> (\<exists>r. label_lookup (forest_labels state) v = Some (r, Even)))
   \<Longrightarrow> invar_unscanned state"
  by (auto simp: invar_unscanned_def)

lemma invar_unscanned_holds_1[invar_holds_intros]:
  assumes "Alternating_Forest_Search_call_1_conds state" "invar_1 state" "invar_forest state"
          "invar_unscanned state"
  shows "invar_unscanned (Alternating_Forest_Search_upd1 state)"
proof-
  obtain v w es x r where f:
    "unscanned state = (v, w) # es" "label_lookup (forest_labels state) w = None"
    "mate_lookup M w = Some x" "label_lookup (forest_labels state) v = Some (r, Even)"
    "{v, w} \<in> ugraph_abs G" "label_lookup (forest_labels state) x = None" "w \<noteq> x"
    "abs_search.if1 (abs_labels state) (abs_examined state) v w x r"
    by (rule call_1_facts[OF assms(1,3,4)])
  show ?thesis
    using assms(4) f(1,2)
    by (fastforce simp: invar_unscanned_def upd1_abs[OF assms(2) f(1,3,4)])
qed

lemma invar_unscanned_holds_2[invar_holds_intros]:
  "\<lbrakk>Alternating_Forest_Search_call_2_conds state; invar_unscanned state\<rbrakk>
   \<Longrightarrow> invar_unscanned (Alternating_Forest_Search_upd2 state)"
  by (auto elim!: call_cond_elims simp: invar_unscanned_def)

lemma invar_unscanned_holds_3[invar_holds_intros]:
  "\<lbrakk>Alternating_Forest_Search_call_3_conds state; invar_queue state\<rbrakk>
   \<Longrightarrow> invar_unscanned (Alternating_Forest_Search_upd3 state)"
  by (auto elim!: call_cond_elims
           simp: invar_unscanned_def invar_queue_def upd3_abs
                 neighbour_list_ugraph_abs[OF graph_input_G])

lemma invar_unscanned_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>Alternating_Forest_Search_ret_1_conds state; invar_unscanned state\<rbrakk>
   \<Longrightarrow> invar_unscanned (Alternating_Forest_Search_ret1 state)"
  by auto

lemma invar_unscanned_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>Alternating_Forest_Search_ret_2_conds state; invar_unscanned state\<rbrakk>
   \<Longrightarrow> invar_unscanned (Alternating_Forest_Search_ret2 state)"
  by auto

subsubsection \<open>The queue holds even vertices\<close>

lemma invar_queue_props[invar_props_elims]:
  "invar_queue state \<Longrightarrow>
   ((\<forall>v \<in> set (queue state). \<exists>r. label_lookup (forest_labels state) v = Some (r, Even)) \<Longrightarrow> P)
   \<Longrightarrow> P"
  by (auto simp: invar_queue_def)

lemma invar_queue_intro[invar_props_intros]:
  "(\<forall>v \<in> set (queue state). \<exists>r. label_lookup (forest_labels state) v = Some (r, Even))
   \<Longrightarrow> invar_queue state"
  by (auto simp: invar_queue_def)

lemma invar_queue_holds_1[invar_holds_intros]:
  assumes "Alternating_Forest_Search_call_1_conds state" "invar_1 state" "invar_forest state"
          "invar_unscanned state" "invar_queue state"
  shows "invar_queue (Alternating_Forest_Search_upd1 state)"
proof-
  obtain v w es x r where f:
    "unscanned state = (v, w) # es" "label_lookup (forest_labels state) w = None"
    "mate_lookup M w = Some x" "label_lookup (forest_labels state) v = Some (r, Even)"
    "{v, w} \<in> ugraph_abs G" "label_lookup (forest_labels state) x = None" "w \<noteq> x"
    "abs_search.if1 (abs_labels state) (abs_examined state) v w x r"
    by (rule call_1_facts[OF assms(1,3,4)])
  show ?thesis
    using assms(5) f(2)
    by (fastforce simp: invar_queue_def upd1_abs[OF assms(2) f(1,3,4)])
qed

lemma invar_queue_holds_2[invar_holds_intros]:
  "\<lbrakk>Alternating_Forest_Search_call_2_conds state; invar_queue state\<rbrakk>
   \<Longrightarrow> invar_queue (Alternating_Forest_Search_upd2 state)"
  by (simp add: invar_queue_def)

lemma invar_queue_holds_3[invar_holds_intros]:
  "\<lbrakk>Alternating_Forest_Search_call_3_conds state; invar_queue state\<rbrakk>
   \<Longrightarrow> invar_queue (Alternating_Forest_Search_upd3 state)"
  by (auto elim!: call_cond_elims simp: invar_queue_def upd3_abs)

lemma invar_queue_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>Alternating_Forest_Search_ret_1_conds state; invar_queue state\<rbrakk>
   \<Longrightarrow> invar_queue (Alternating_Forest_Search_ret1 state)"
  by auto

lemma invar_queue_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>Alternating_Forest_Search_ret_2_conds state; invar_queue state\<rbrakk>
   \<Longrightarrow> invar_queue (Alternating_Forest_Search_ret2 state)"
  by auto

subsubsection \<open>Scanned even vertices have only odd neighbours\<close>

lemma invar_scanned_props[invar_props_elims]:
  "invar_scanned state \<Longrightarrow>
   ((\<forall>v r. label_lookup (forest_labels state) v = Some (r, Even) \<longrightarrow>
       v \<in> set (queue state) \<or>
       (\<forall>w. {v, w} \<in> ugraph_abs G \<longrightarrow>
          (v, w) \<in> set (unscanned state) \<or>
          (\<exists>r'. label_lookup (forest_labels state) w = Some (r', Odd)))) \<Longrightarrow> P)
   \<Longrightarrow> P"
  by (auto simp: invar_scanned_def)

lemma invar_scanned_intro[invar_props_intros]:
  "(\<forall>v r. label_lookup (forest_labels state) v = Some (r, Even) \<longrightarrow>
      v \<in> set (queue state) \<or>
      (\<forall>w. {v, w} \<in> ugraph_abs G \<longrightarrow>
         (v, w) \<in> set (unscanned state) \<or>
         (\<exists>r'. label_lookup (forest_labels state) w = Some (r', Odd))))
   \<Longrightarrow> invar_scanned state"
  by (auto simp: invar_scanned_def)

lemma invar_scanned_holds_1[invar_holds_intros]:
  assumes "Alternating_Forest_Search_call_1_conds state" "invar_1 state" "invar_forest state"
          "invar_unscanned state" "invar_scanned state"
  shows "invar_scanned (Alternating_Forest_Search_upd1 state)"
proof-
  obtain v w es x r where f:
    "unscanned state = (v, w) # es" "label_lookup (forest_labels state) w = None"
    "mate_lookup M w = Some x" "label_lookup (forest_labels state) v = Some (r, Even)"
    "{v, w} \<in> ugraph_abs G" "label_lookup (forest_labels state) x = None" "w \<noteq> x"
    "abs_search.if1 (abs_labels state) (abs_examined state) v w x r"
    by (rule call_1_facts[OF assms(1,3,4)])
  note upd = upd1_abs[OF assms(2) f(1,3,4)]
  show ?thesis
    unfolding invar_scanned_def
  proof(intro allI impI)
    fix y r'
    assume y: "label_lookup (forest_labels (Alternating_Forest_Search_upd1 state)) y = Some (r', Even)"
    show "y \<in> set (queue (Alternating_Forest_Search_upd1 state)) \<or>
          (\<forall>z. {y, z} \<in> ugraph_abs G \<longrightarrow>
             (y, z) \<in> set (unscanned (Alternating_Forest_Search_upd1 state)) \<or>
             (\<exists>r''. label_lookup (forest_labels (Alternating_Forest_Search_upd1 state)) z =
                     Some (r'', Odd)))"
    proof(cases "y = x")
      case True
      then show ?thesis
        by (simp add: upd)
    next
      case False
      hence "label_lookup (forest_labels state) y = Some (r', Even)"
        using y f(7)
        by (auto simp: upd split: if_splits)
      hence "y \<in> set (queue state) \<or>
             (\<forall>z. {y, z} \<in> ugraph_abs G \<longrightarrow> (y, z) \<in> set (unscanned state) \<or>
                (\<exists>r''. label_lookup (forest_labels state) z = Some (r'', Odd)))"
        using assms(5)
        by (auto simp: invar_scanned_def)
      thus ?thesis
      proof
        assume "y \<in> set (queue state)"
        thus ?thesis
          by (simp add: upd)
      next
        assume all: "\<forall>z. {y, z} \<in> ugraph_abs G \<longrightarrow> (y, z) \<in> set (unscanned state) \<or>
                         (\<exists>r''. label_lookup (forest_labels state) z = Some (r'', Odd))"
        have "(y, z) \<in> set es \<or>
              (\<exists>r''. label_lookup (forest_labels (Alternating_Forest_Search_upd1 state)) z =
                      Some (r'', Odd))"
          if "{y, z} \<in> ugraph_abs G" for z
        proof-
          consider "(y, z) = (v, w)" | "(y, z) \<in> set es"
            | "\<exists>r''. label_lookup (forest_labels state) z = Some (r'', Odd)"
            using all that f(1)
            by auto
          thus ?thesis
          proof cases
            case 1
            then show ?thesis
              using f(7)
              by (auto simp: upd)
          next
            case 2
            then show ?thesis
              by simp
          next
            case 3
            then obtain r'' where z: "label_lookup (forest_labels state) z = Some (r'', Odd)"
              by blast
            hence "z \<noteq> w" "z \<noteq> x"
              using f(2,6)
              by auto
            thus ?thesis
              using z
              by (auto simp: upd)
          qed
        qed
        thus ?thesis
          by (simp add: upd)
      qed
    qed
  qed
qed

lemma invar_scanned_holds_2[invar_holds_intros]:
  assumes "Alternating_Forest_Search_call_2_conds state" "invar_forest state"
          "invar_unscanned state" "invar_scanned state"
  shows "invar_scanned (Alternating_Forest_Search_upd2 state)"
proof-
  obtain v w es r where f: "unscanned state = (v, w) # es"
      "label_lookup (forest_labels state) w = Some (r, Odd)"
    by (rule call_2_odd[OF assms(1-3)])
  show ?thesis
    using assms(4) f
    by (fastforce simp: invar_scanned_def)
qed

lemma invar_scanned_holds_3[invar_holds_intros]:
  "\<lbrakk>Alternating_Forest_Search_call_3_conds state; invar_scanned state\<rbrakk>
   \<Longrightarrow> invar_scanned (Alternating_Forest_Search_upd3 state)"
  by (fastforce elim!: call_cond_elims
                 simp: invar_scanned_def upd3_abs neighbour_list_ugraph_abs[OF graph_input_G])

lemma invar_scanned_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>Alternating_Forest_Search_ret_1_conds state; invar_scanned state\<rbrakk>
   \<Longrightarrow> invar_scanned (Alternating_Forest_Search_ret1 state)"
  by auto

lemma invar_scanned_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>Alternating_Forest_Search_ret_2_conds state; invar_scanned state\<rbrakk>
   \<Longrightarrow> invar_scanned (Alternating_Forest_Search_ret2 state)"
  by auto

subsubsection \<open>The invariants hold for the whole loop\<close>

lemma invar_1_holds[invar_holds_intros]:
  assumes "Alternating_Forest_Search_dom state" "invar_1 state" "invar_forest state"
          "invar_unscanned state" "invar_queue state"
  shows "invar_1 (Alternating_Forest_Search state)"
  using assms(2-)
proof(induction rule: Alternating_Forest_Search_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    apply(rule Alternating_Forest_Search_cases[where state = state])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: Alternating_Forest_Search_simps[OF IH(1)])
qed

lemma invar_forest_holds[invar_holds_intros]:
  assumes "Alternating_Forest_Search_dom state" "invar_1 state" "invar_forest state"
          "invar_unscanned state" "invar_queue state"
  shows "invar_forest (Alternating_Forest_Search state)"
  using assms(2-)
proof(induction rule: Alternating_Forest_Search_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    apply(rule Alternating_Forest_Search_cases[where state = state])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: Alternating_Forest_Search_simps[OF IH(1)])
qed

lemma invar_unscanned_holds[invar_holds_intros]:
  assumes "Alternating_Forest_Search_dom state" "invar_1 state" "invar_forest state"
          "invar_unscanned state" "invar_queue state"
  shows "invar_unscanned (Alternating_Forest_Search state)"
  using assms(2-)
proof(induction rule: Alternating_Forest_Search_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    apply(rule Alternating_Forest_Search_cases[where state = state])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: Alternating_Forest_Search_simps[OF IH(1)])
qed

lemma invar_queue_holds[invar_holds_intros]:
  assumes "Alternating_Forest_Search_dom state" "invar_1 state" "invar_forest state"
          "invar_unscanned state" "invar_queue state"
  shows "invar_queue (Alternating_Forest_Search state)"
  using assms(2-)
proof(induction rule: Alternating_Forest_Search_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    apply(rule Alternating_Forest_Search_cases[where state = state])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: Alternating_Forest_Search_simps[OF IH(1)])
qed

lemma invar_scanned_holds[invar_holds_intros]:
  assumes "Alternating_Forest_Search_dom state" "invar_1 state" "invar_forest state"
          "invar_unscanned state" "invar_queue state" "invar_scanned state"
  shows "invar_scanned (Alternating_Forest_Search state)"
  using assms(2-)
proof(induction rule: Alternating_Forest_Search_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    apply(rule Alternating_Forest_Search_cases[where state = state])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: Alternating_Forest_Search_simps[OF IH(1)])
qed

subsubsection \<open>Termination\<close>

named_theorems termination_intros

declare termination_intros

lemma in_prod_relI[intro!,termination_intros]:
  "\<lbrakk>f1 a = f1 a'; (a, a') \<in> f2 <*mlex*> r\<rbrakk> \<Longrightarrow> (a,a') \<in> (f1 <*mlex*> f2 <*mlex*> r)"
   by (simp add: mlex_iff)+

definition "less_rel = {(x::nat, y::nat). x < y}"

lemma wf_less_rel[intro!]: "wf less_rel"
  by(auto simp: less_rel_def wf_less)

lemma call_1_terminates[termination_intros]:
  assumes "Alternating_Forest_Search_call_1_conds state" "invar_1 state" "invar_forest state"
          "invar_unscanned state"
  shows "(Alternating_Forest_Search_upd1 state, state) \<in> call_1_measure <*mlex*> r"
proof-
  obtain v w es x r' where f:
    "unscanned state = (v, w) # es" "label_lookup (forest_labels state) w = None"
    "mate_lookup M w = Some x" "label_lookup (forest_labels state) v = Some (r', Even)"
    "{v, w} \<in> ugraph_abs G" "label_lookup (forest_labels state) x = None" "w \<noteq> x"
    "abs_search.if1 (abs_labels state) (abs_examined state) v w x r'"
    by (rule call_1_facts[OF assms(1,3,4)])
  let ?U = "\<lambda>s. {v \<in> Vs (ugraph_abs G). label_lookup (forest_labels s) v = None}"
  have "w \<in> Vs (ugraph_abs G)"
    using f(5)
    by (auto simp: Vs_def)
  hence "w \<in> ?U state"
    using f(2)
    by simp
  moreover have "?U (Alternating_Forest_Search_upd1 state) \<subseteq> ?U state - {w}"
    by (auto simp: upd1_abs[OF assms(2) f(1,3,4)] split: if_splits)
  ultimately have "?U (Alternating_Forest_Search_upd1 state) \<subset> ?U state"
    by blast
  moreover have "finite (?U state)"
    by simp
  ultimately have "call_1_measure (Alternating_Forest_Search_upd1 state) < call_1_measure state"
    by (simp add: call_1_measure_def psubset_card_mono)
  thus ?thesis
    by (rule mlex_less)
qed

lemma call_2_measure_1[termination_intros]:
  "call_1_measure state = call_1_measure (Alternating_Forest_Search_upd2 state)"
  by (simp add: call_1_measure_def)

lemma call_2_measure_3[termination_intros]:
  "call_3_measure state = call_3_measure (Alternating_Forest_Search_upd2 state)"
  by (simp add: call_3_measure_def)

lemma call_2_terminates[termination_intros]:
  "Alternating_Forest_Search_call_2_conds state \<Longrightarrow>
     (Alternating_Forest_Search_upd2 state, state) \<in> call_2_measure <*mlex*> r"
  by (auto elim!: call_cond_elims intro!: mlex_less simp: call_2_measure_def)

lemma call_3_measure_1[termination_intros]:
  "Alternating_Forest_Search_call_3_conds state \<Longrightarrow>
     call_1_measure state = call_1_measure (Alternating_Forest_Search_upd3 state)"
  by (auto elim!: call_cond_elims simp: call_1_measure_def upd3_abs)

lemma call_3_terminates[termination_intros]:
  "Alternating_Forest_Search_call_3_conds state \<Longrightarrow>
     (Alternating_Forest_Search_upd3 state, state) \<in> call_3_measure <*mlex*> r"
  by (auto elim!: call_cond_elims intro!: mlex_less simp: call_3_measure_def upd3_abs)

lemma wf_term_rel: "wf Alternating_Forest_Search_term_rel'"
  by (auto simp: wf_mlex Alternating_Forest_Search_term_rel'_def)

lemma in_Alternating_Forest_Search_term_rel'[termination_intros]:
  "\<lbrakk>Alternating_Forest_Search_call_1_conds state; invar_1 state; invar_forest state;
    invar_unscanned state\<rbrakk> \<Longrightarrow>
     (Alternating_Forest_Search_upd1 state, state) \<in> Alternating_Forest_Search_term_rel'"
  "Alternating_Forest_Search_call_2_conds state \<Longrightarrow>
     (Alternating_Forest_Search_upd2 state, state) \<in> Alternating_Forest_Search_term_rel'"
  "Alternating_Forest_Search_call_3_conds state \<Longrightarrow>
     (Alternating_Forest_Search_upd3 state, state) \<in> Alternating_Forest_Search_term_rel'"
  by (simp add: Alternating_Forest_Search_term_rel'_def termination_intros)+

lemma Alternating_Forest_Search_terminates[termination_intros]:
  assumes "invar_1 state" "invar_forest state" "invar_unscanned state" "invar_queue state"
  shows "Alternating_Forest_Search_dom state"
  using wf_term_rel assms
proof(induction rule: wf_induct_rule)
  case (less x)
  show ?case
    by (rule Alternating_Forest_Search_domintros)
       (auto intro!: invar_holds_intros less in_Alternating_Forest_Search_term_rel')
qed

subsubsection \<open>Correctness\<close>

lemma Alternating_Forest_Search_correct_ret_1:
  assumes "invar_forest state" "invar_unscanned state" "Alternating_Forest_Search_ret_1_conds state"
  shows "compute_alt_path_spec (ugraph_abs G) (matching_abs M) (alternating_paths state)"
proof-
  obtain v w es r' where f: "unscanned state = (v, w) # es"
      "label_lookup (forest_labels state) w = Some (r', Even)"
    using assms(3)
    by (auto elim!: call_cond_elims)
  obtain r where r: "label_lookup (forest_labels state) v = Some (r, Even)" "{v, w} \<in> ugraph_abs G"
    using assms(2) f(1)
    by (auto simp: invar_unscanned_def)
  have I: "abs_search.search_invars (abs_examined state) (abs_parents state) (abs_labels state)"
    using assms(1)
    by (simp add: invar_forest_def)
  have "abs_search.if2 (abs_labels state) v w r r'"
    using f(2) r
    by (simp add: abs_search.if2_def)
  hence spec: "compute_alt_path_spec (ugraph_abs G) (matching_abs M)
                 (Some (parent_spec.follow (abs_parents state) v,
                        parent_spec.follow (abs_parents state) w))"
    by (rule abs_search.search_invars_if2_sound[OF I])
  have "follow_impl (abs_parents state) = parent_spec.follow (abs_parents state)"
    by (rule follow_impl_eq[OF abs_search.search_invarsD(3)[OF I]])
  thus ?thesis
    using spec f(1)
    by (simp add: alternating_paths_def)
qed

lemma Alternating_Forest_Search_correct_ret_2:
  assumes "invar_forest state" "invar_scanned state" "Alternating_Forest_Search_ret_2_conds state"
  shows "alternating_paths state = None"
        "\<nexists>p. graph_augmenting_path (ugraph_abs G) (matching_abs M) p"
proof-
  have nil: "unscanned state = []" "queue state = []"
    using assms(3)
    by (auto elim!: call_cond_elims)
  thus "alternating_paths state = None"
    by (simp add: alternating_paths_def)
  have I: "abs_search.search_invars (abs_examined state) (abs_parents state) (abs_labels state)"
    using assms(1)
    by (simp add: invar_forest_def)
  have odd: "\<exists>r'. abs_labels state w = Some (r', Odd)"
    if "abs_labels state v = Some (r, Even)" "{v, w} \<in> ugraph_abs G" for v w r
    using assms(2) that nil
    by (auto simp: invar_scanned_def)
  have "\<not> abs_search.if1_cond (abs_labels state) (abs_examined state)"
    using odd
    by (fastforce simp: abs_search.if1_cond_def)
  moreover have "\<not> abs_search.if2_cond (abs_labels state)"
    using odd
    by (fastforce simp: abs_search.if2_cond_def)
  ultimately have "\<nexists>p. matching_augmenting_path (matching_abs M) p \<and> path (ugraph_abs G) p \<and>
                       distinct p"
    by (rule abs_search.search_invars_complete[OF I])
  thus "\<nexists>p. graph_augmenting_path (ugraph_abs G) (matching_abs M) p"
    by blast
qed

lemma ret_holds[ret_holds_intros]:
  assumes "Alternating_Forest_Search_dom state"
  shows "Alternating_Forest_Search_ret_1_conds (Alternating_Forest_Search state) \<or>
         Alternating_Forest_Search_ret_2_conds (Alternating_Forest_Search state)"
proof(induction rule: Alternating_Forest_Search_induct[OF assms])
  case IH: (1 state)
  show ?case
    apply(rule Alternating_Forest_Search_cases[where state = state])
    by (auto intro: IH(2-) simp: Alternating_Forest_Search_simps[OF IH(1)])
qed

subsubsection \<open>The initial state\<close>

lemma initial_state_props[invar_holds_intros, termination_intros]:
  "invar_1 initial_state" "invar_forest initial_state" "invar_unscanned initial_state"
  "invar_queue initial_state" "invar_scanned initial_state"
  "Alternating_Forest_Search_dom initial_state"
proof-
  show inv1: "invar_1 initial_state"
    using initial_labels(1)
    by (auto intro!: invar_props_intros simp: initial_state_def Parent.invar_empty)
  show invf: "invar_forest initial_state"
    using abs_search.search_invars_init
    by (simp add: invar_forest_def initial_state_def initial_labels(2) Parent.map_empty)
  show invu: "invar_unscanned initial_state"
    by (simp add: invar_unscanned_def initial_state_def)
  show invq: "invar_queue initial_state"
    by (auto simp: invar_queue_def initial_state_def initial_labels(2) set_free_vertices)
  show "invar_scanned initial_state"
    by (auto simp: invar_scanned_def initial_state_def initial_labels(2) set_free_vertices
            split: if_splits)
  show "Alternating_Forest_Search_dom initial_state"
    by (rule Alternating_Forest_Search_terminates[OF inv1 invf invu invq])
qed

lemma Alternating_Forest_Search_impl_to_Alternating_Forest_Search:
  "Alternating_Forest_Search_impl initial_state = Alternating_Forest_Search initial_state"
  by (auto intro!: Alternating_Forest_Search_impl_same initial_state_props)

subsubsection \<open>Final correctness\<close>

lemma final_state_invars:
  "invar_forest (Alternating_Forest_Search initial_state)"
  "invar_unscanned (Alternating_Forest_Search initial_state)"
  "invar_scanned (Alternating_Forest_Search initial_state)"
  by (auto intro!: invar_holds_intros)

lemma Alternating_Forest_Search_correct_1:
  "compute_alt_path_spec (ugraph_abs G) (matching_abs M)
     (alternating_paths (Alternating_Forest_Search initial_state))"
  using ret_holds[OF initial_state_props(6)]
        Alternating_Forest_Search_correct_ret_1[OF final_state_invars(1,2)]
        Alternating_Forest_Search_correct_ret_2(1)[OF final_state_invars(1,3)]
  by (auto simp: compute_alt_path_spec_def)

lemma Alternating_Forest_Search_correct_2:
  assumes "\<exists>p. graph_augmenting_path (ugraph_abs G) (matching_abs M) p"
  shows "alternating_paths (Alternating_Forest_Search initial_state) \<noteq> None"
  using ret_holds[OF initial_state_props(6)] assms
        Alternating_Forest_Search_correct_ret_2(2)[OF final_state_invars(1,3)]
  by (auto elim!: call_cond_elims simp: alternating_paths_def)

lemma Alternating_Forest_Search_run_impl_correct:
  "compute_alt_path_spec (ugraph_abs G) (matching_abs M) Alternating_Forest_Search_run_impl"
  "\<exists>p. graph_augmenting_path (ugraph_abs G) (matching_abs M) p \<Longrightarrow>
     Alternating_Forest_Search_run_impl \<noteq> None"
  using Alternating_Forest_Search_correct_1 Alternating_Forest_Search_correct_2
  by (simp_all add: Alternating_Forest_Search_run_impl_def
                    Alternating_Forest_Search_impl_to_Alternating_Forest_Search)

end

end

end
```

---

## Phase 4: the search with blossom shrinking (`Blossom_Shrinking_Search.thy`)

**Goal.** `Blossom_Shrinking_Search_run_impl_correct`: under `Blossom_Shrinking_Search_axiom`,
a returned path is an augmenting path of the input, and a path is returned whenever an
augmenting path exists. These are the contract clauses of `Edmonds_Blossom_Loop`.

**Recon.** (a) `thm quot.refine_works quot.aug_path_works_in_contraction quot.matching_quotM
quot.card_Vs_quotG quot.refine_def quot.replace_cycle_def quot.stem2vert_path_def
quot.choose_con_vert_def` and the parameter order of `quot` (expected `sel E s u`).
(b) After `interpretation Q`, that `Q.quotG X` unfolds to
`quot_graph (\<lambda>v. if v \<in> Vs (ugraph_abs E) - set C then v else u) X - {{u}}`
(the form used by `quotient_edges_quot_graph`). (c) `thm Suc_le_length_iff_snoc2 find_pfx.simps
find_pfx_nempty induct_list012`.

**Key lemmas (frozen).** `quotient_edges_quot_graph`, `contract_graph_abs`,
`contract_graph_input`, `contract_matching_abs`, `contract_matching_invar`, `contract_card_Vs`,
`contract_complete`, `lift_one_eq`, `lift_one_correct`; the loop, the invariants and the final
lemmas.

**One-shot theory** (copy verbatim into `Edmonds_Blossom_Executable/Blossom_Shrinking_Search.thy`):

```isabelle
theory Blossom_Shrinking_Search
  imports Graph_Matching_Specs Blossom.Blossom_Algo_Contraction
begin

provenance ai

section \<open>Searching for an augmenting path by shrinking blossoms\<close>

text \<open>The search calls a procedure that returns an augmenting path, a blossom, or nothing. When
  it returns a blossom, the cycle of the blossom is contracted to a fresh vertex, in the graph
  and in the matching, and the search is repeated on the contracted graph. The contractions are
  recorded on a stack. When an augmenting path of the contracted graph is found, it is lifted
  through the recorded contractions, from the last one to the first, to an augmenting path of the
  input graph. A contraction preserves the existence of augmenting paths, so if the procedure
  returns nothing, the input graph has no augmenting path.

  The correctness of lifting and contracting is that of the abstract algorithm
  @{const find_aug_path.find_aug_path}: the lifting function below is equal to
  @{const quot.refine} for a suitable choice function.\<close>

subsection \<open>Facts about blossoms\<close>

lemma blossom_cycle_props:
  assumes "match_blossom M stem C"
  shows "C \<noteq> []" "hd C = last C" "2 \<le> card (set C)" "distinct (tl C)"
proof-
  show "C \<noteq> []"
    using odd_cycle_nempty[OF match_blossomD(3)[OF assms]] .
  show "hd C = last C"
    using odd_cycleD(3)[OF match_blossomD(3)[OF assms]] .
  show "distinct (tl C)"
    using match_blossom_distinct_tl[OF assms] .
  have len: "3 \<le> length C"
    using odd_cycleD(1)[OF match_blossomD(3)[OF assms]] .
  have "distinct (butlast C)"
    using match_blossomD(2)[OF assms]
    by simp
  hence "card (set (butlast C)) = length (butlast C)"
    by (rule distinct_card)
  moreover have "set (butlast C) \<subseteq> set C"
    by (rule in_set_butlastD[THEN subsetI])
  moreover have "2 \<le> length (butlast C)"
    using len
    by simp
  ultimately show "2 \<le> card (set C)"
    using card_mono[of "set C" "set (butlast C)"]
    by simp
qed

lemma blossom_cycle_subset:
  assumes "path E (stem @ C)"
  shows "set C \<subseteq> Vs E"
  using path_suff[OF assms] mem_path_Vs
  by blast

subsection \<open>A choice function for the lifting\<close>

text \<open>The abstract lifting chooses, among the vertices of the cycle adjacent to a given vertex,
  one with a choice function. The executable lifting takes the first such vertex in the list of
  the cycle. The following choice function makes the two agree.\<close>

definition "cycle_sel C S =
  (case find (\<lambda>x. x \<in> S) C of Some x \<Rightarrow> x | None \<Rightarrow> (if S = {} then hd C else (SOME x. x \<in> S)))"

lemma cycle_sel_choose: "choose (cycle_sel C)"
proof
  fix S :: "'a set"
  assume "finite S" "S \<noteq> {}"
  show "cycle_sel C S \<in> S"
  proof(cases "find (\<lambda>x. x \<in> S) C")
    case None
    then show ?thesis
      using \<open>S \<noteq> {}\<close>
      by (auto simp: cycle_sel_def intro: someI_ex)
  next
    case (Some x)
    then show ?thesis
      by (auto simp: cycle_sel_def dest: find_Some_iff[THEN iffD1])
  qed
qed

subsection \<open>Contracting an edge list\<close>

definition "quotient_vertex C u v = (if v \<in> set C then u else v)"

definition "quotient_edges C u es =
  filter (\<lambda>(a, b). a \<noteq> b) (map (\<lambda>(a, b). (quotient_vertex C u a, quotient_vertex C u b)) es)"

lemmas [code] = quotient_vertex_def quotient_edges_def

lemma set_quotient_edges:
  "set (quotient_edges C u es) =
     {(quotient_vertex C u a, quotient_vertex C u b) | a b.
        (a, b) \<in> set es \<and> quotient_vertex C u a \<noteq> quotient_vertex C u b}"
  by (auto simp: quotient_edges_def)

lemma quotient_edges_sym:
  "(\<And>a b. (a, b) \<in> set es \<Longrightarrow> (b, a) \<in> set es) \<Longrightarrow>
   (a, b) \<in> set (quotient_edges C u es) \<Longrightarrow> (b, a) \<in> set (quotient_edges C u es)"
  by (fastforce simp: set_quotient_edges)

lemma quotient_edges_irrefl: "(a, a) \<notin> set (quotient_edges C u es)"
  by (auto simp: set_quotient_edges)

lemma quotient_edges_mono:
  "set es \<subseteq> set es' \<Longrightarrow> set (quotient_edges C u es) \<subseteq> set (quotient_edges C u es')"
  by (auto simp: set_quotient_edges)

lemma dVs_quotient_edges:
  "dVs (set (quotient_edges C u es)) \<subseteq> insert u (dVs (set es) - set C)"
  by (fastforce simp: set_quotient_edges quotient_vertex_def dVs_eq split: if_splits)

lemma quotient_edges_quot_graph:
  assumes "set es = D" "\<And>a b. (a, b) \<in> D \<Longrightarrow> (b, a) \<in> D" "\<And>a. (a, a) \<notin> D"
          "\<And>v. v \<in> dVs D \<Longrightarrow> v \<in> s \<longleftrightarrow> v \<notin> set C" "u \<notin> s"
  shows "{{a, b} | a b. (a, b) \<in> set (quotient_edges C u es)} =
           quot_graph (\<lambda>v. if v \<in> s then v else u) {{a, b} | a b. (a, b) \<in> D} - {{u}}"
    (is "?L = ?R")
proof-
  let ?P = "\<lambda>v. if v \<in> s then v else u"
  have P: "?P v = quotient_vertex C u v" if "v \<in> dVs D" for v
    using assms(4)[OF that]
    by (simp add: quotient_vertex_def)
  show ?thesis
  proof(intro equalityI subsetI)
    fix e
    assume "e \<in> ?L"
    then obtain a b where ab: "e = {quotient_vertex C u a, quotient_vertex C u b}" "(a, b) \<in> D"
        "quotient_vertex C u a \<noteq> quotient_vertex C u b"
      using assms(1)
      by (auto simp: set_quotient_edges)
    have "a \<in> dVs D" "b \<in> dVs D"
      using ab(2)
      by (auto intro: dVsI)
    hence "e = ?P ` {a, b}"
      using ab(1)
      by (simp add: P)
    moreover have "{a, b} \<in> {{a, b} | a b. (a, b) \<in> D}"
      using ab(2)
      by blast
    moreover have "e \<noteq> {u}"
      using ab(1,3)
      by (auto simp: doubleton_eq_iff)
    ultimately show "e \<in> ?R"
      by (auto simp: quot_graph_def)
  next
    fix e
    assume "e \<in> ?R"
    then obtain a b where ab: "e = ?P ` {a, b}" "(a, b) \<in> D" "e \<noteq> {u}"
      by (auto simp: quot_graph_def)
    have ab_dVs: "a \<in> dVs D" "b \<in> dVs D"
      using ab(2)
      by (auto intro: dVsI)
    have neq: "quotient_vertex C u a \<noteq> quotient_vertex C u b"
    proof
      assume eq: "quotient_vertex C u a = quotient_vertex C u b"
      hence "e = {quotient_vertex C u a}"
        using ab(1) ab_dVs
        by (simp add: P)
      hence "quotient_vertex C u a \<noteq> u"
        using ab(3)
        by auto
      hence "a \<notin> set C" "b \<notin> set C"
        using eq
        by (auto simp: quotient_vertex_def split: if_splits)
      hence "a = b"
        using eq
        by (simp add: quotient_vertex_def)
      thus False
        using ab(2) assms(3)
        by simp
    qed
    have "e = {quotient_vertex C u a, quotient_vertex C u b}"
      using ab(1) ab_dVs
      by (simp add: P)
    thus "e \<in> ?L"
      using ab(2) neq assms(1)
      by (auto simp: set_quotient_edges)
  qed
qed

subsection \<open>The program state\<close>

record ('adjmap, 'mate, 'v) Blossom_Shrinking_Search_state =
  search_graph :: 'adjmap
  search_vertices :: "'v list"
  search_matching :: 'mate
  contractions :: "('adjmap \<times> 'mate \<times> 'v list \<times> 'v) list"
  search_result :: "'v match_blossom_res option"

subsection \<open>Setup for automation\<close>

named_theorems call_cond_elims
named_theorems call_cond_intros
named_theorems ret_holds_intros
named_theorems invar_props_intros
named_theorems invar_props_elims
named_theorems invar_holds_intros
named_theorems state_rel_intros
named_theorems state_rel_holds_intros

subsection \<open>The loop\<close>

(* PLAN CHANGE A1 (2026-10-24): mate_empty is instantiated by name and typed in the for
   clause, so that the type variable 'mate below is that of the mate-function ADT. *)
locale Blossom_Shrinking_Search = Graph_Matching_Specs where lookup = lookup and mate_empty = mate_empty
  for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option" and mate_empty :: 'mate +
  fixes G :: 'adjmap and vs :: "'v list" and M :: 'mate
    and blossom_search :: "'adjmap \<Rightarrow> 'v list \<Rightarrow> 'mate \<Rightarrow> 'v match_blossom_res option"
    and fresh_vertex :: "'v list \<Rightarrow> 'v"
  assumes blossom_search:
    "\<And>G' vs' M' p. \<lbrakk>graph_input G' vs'; matching_invar G' M'; blossom_search G' vs' M' = Some (Path p)\<rbrakk>
       \<Longrightarrow> graph_augmenting_path (ugraph_abs G') (matching_abs M') p"
    "\<And>G' vs' M' stem C. \<lbrakk>graph_input G' vs'; matching_invar G' M';
                         blossom_search G' vs' M' = Some (Blossom stem C)\<rbrakk>
       \<Longrightarrow> blossom (ugraph_abs G') (matching_abs M') stem C"
    "\<And>G' vs' M'. \<lbrakk>graph_input G' vs'; matching_invar G' M';
                  \<exists>p. graph_augmenting_path (ugraph_abs G') (matching_abs M') p\<rbrakk>
       \<Longrightarrow> blossom_search G' vs' M' \<noteq> None"
  and fresh_vertex: "\<And>vs'. fresh_vertex vs' \<notin> set vs'"
begin

definition "Blossom_Shrinking_Search_axiom \<longleftrightarrow> graph_input G vs \<and> matching_invar G M"

subsubsection \<open>Contraction\<close>

definition "contract_vertices vs' C u = u # filter (\<lambda>v. v \<notin> set C) vs'"

definition "contract_graph G' vs' C u = Graph.from_list (quotient_edges C u (adjacency_edges G' vs'))"

definition "contract_matching M' vs' C u = mate_from_list (quotient_edges C u (matching_edges M' vs'))"

subsubsection \<open>Lifting\<close>

definition "cycle_neighbour E C v =
  (case find (\<lambda>x. isin (Graph.neighbourhood E v) x) C of Some x \<Rightarrow> x | None \<Rightarrow> hd C)"

definition "last_edge_matched N xs =
  (case rev xs of b # a # _ \<Rightarrow> mate_lookup N a = Some b | _ \<Rightarrow> True)"

definition "cycle_path E N C v =
  (let w = cycle_neighbour E C v; pfx = find_pfx ((=) w) C in
   if last_edge_matched N pfx then pfx else find_pfx ((=) w) (rev C))"

definition "matched_to_cycle N C x =
  (x \<notin> set C \<and> (case mate_lookup N x of Some c \<Rightarrow> c \<in> set C | None \<Rightarrow> False))"

definition "replace_cycle_impl E N C p1 p2 =
  (let stem2p2 = cycle_path E N C (hd p2); p12stem = cycle_path E N C (last p1) in
   if p1 = [] then stem2p2 @ p2
   else if p2 = [] then p12stem @ rev p1
   else if \<not> matched_to_cycle N C (hd p2) then p1 @ stem2p2 @ p2
   else rev p2 @ p12stem @ rev p1)"

definition "lift_one E N C u p =
  (if u \<in> set p then replace_cycle_impl E N C (fst (pref_suf [] u p)) (snd (pref_suf [] u p))
   else p)"

fun lift_path where
  "lift_path [] p = p"
| "lift_path ((E, N, C, u) # cs) p = lift_path cs (lift_one E N C u p)"

lemmas [code] = contract_vertices_def contract_graph_def contract_matching_def cycle_neighbour_def
  last_edge_matched_def cycle_path_def matched_to_cycle_def replace_cycle_impl_def lift_one_def
  lift_path.simps

subsubsection \<open>One contraction\<close>

context
  fixes E N C u vs' stem
  assumes contraction:
    "graph_input E vs'" "matching_invar E N" "blossom (ugraph_abs E) (matching_abs N) stem C"
    "u \<notin> set vs'"
begin

lemma contraction_facts:
  "graph_invar (ugraph_abs E)" "set C \<subseteq> Vs (ugraph_abs E)" "C \<noteq> []" "hd C = last C"
  "2 \<le> card (set C)" "u \<notin> Vs (ugraph_abs E)" "Mate.invar_matching (ugraph_abs E) N"
  "matching (matching_abs N)" "matching_abs N \<subseteq> ugraph_abs E" "finite (matching_abs N)"
proof-
  show "graph_invar (ugraph_abs E)"
    by (rule ugraph_abs_graph_invar[OF contraction(1)])
  show "set C \<subseteq> Vs (ugraph_abs E)"
    by (rule blossom_cycle_subset[OF blossomD(1)[OF contraction(3)]])
  show "C \<noteq> []" "hd C = last C" "2 \<le> card (set C)"
    using blossom_cycle_props[OF blossomD(2)[OF contraction(3)]]
    by simp_all
  show "u \<notin> Vs (ugraph_abs E)"
    using contraction(4) Vs_ugraph_abs_subset_vs[OF contraction(1)]
    by blast
  show "Mate.invar_matching (ugraph_abs E) N"
    using contraction(2)
    by (simp add: matching_invar_def)
  show "matching (matching_abs N)" "matching_abs N \<subseteq> ugraph_abs E" "finite (matching_abs N)"
    using matching_invar_props[OF contraction(2)]
    by simp_all
qed

lemma quot_here: "quot (cycle_sel C) (ugraph_abs E) (Vs (ugraph_abs E) - set C) u"
  apply unfold_locales
  using choose.sel[OF cycle_sel_choose] contraction_facts(1,2,3,6)
  by (auto simp: neq_Nil_conv)

interpretation Q: quot "cycle_sel C" "ugraph_abs E" "Vs (ugraph_abs E) - set C" u
  by (rule quot_here)

lemma contract_graph_abs:
  "ugraph_abs (contract_graph E vs' C u) = Q.quotG (ugraph_abs E)"
proof-
  have "ugraph_abs E = {{a, b} | a b. (a, b) \<in> Graph.digraph_abs E}"
    by (simp add: ugraph_abs_def)
  moreover have "v \<in> Vs (ugraph_abs E) - set C \<longleftrightarrow> v \<notin> set C"
    if "v \<in> dVs (Graph.digraph_abs E)" for v
    using that Vs_ugraph_abs[OF contraction(1)]
    by simp
  ultimately show ?thesis
    using quotient_edges_quot_graph[OF adjacency_edges[OF contraction(1)]
                                       graph_inputD(4,5)[OF contraction(1)]]
          contraction_facts(6)
    by (simp add: contract_graph_def ugraph_abs_from_list)
qed

lemma contract_graph_input:
  "graph_input (contract_graph E vs' C u) (contract_vertices vs' C u)"
  unfolding contract_graph_def
proof(rule from_list_graph_input)
  have sym: "\<And>a b. (a, b) \<in> set (adjacency_edges E vs') \<Longrightarrow> (b, a) \<in> set (adjacency_edges E vs')"
    using graph_inputD(4)[OF contraction(1)]
    by (simp add: adjacency_edges[OF contraction(1)])
  show "\<And>a b. (a, b) \<in> set (quotient_edges C u (adjacency_edges E vs')) \<Longrightarrow>
              (b, a) \<in> set (quotient_edges C u (adjacency_edges E vs'))"
    using quotient_edges_sym[OF sym]
    by blast
  show "\<And>a. (a, a) \<notin> set (quotient_edges C u (adjacency_edges E vs'))"
    by (rule quotient_edges_irrefl)
  have "dVs (set (adjacency_edges E vs')) \<subseteq> set vs'"
    using adjacency_edges[OF contraction(1)] graph_inputD(6)[OF contraction(1)]
    by simp
  thus "dVs (set (quotient_edges C u (adjacency_edges E vs'))) \<subseteq> set (contract_vertices vs' C u)"
    using dVs_quotient_edges[of C u "adjacency_edges E vs'"]
    by (auto simp: contract_vertices_def)
qed

lemma matching_pairs:
  "set (matching_edges N vs') = {(a, b). mate_lookup N a = Some b}"
  "matching_abs N = {{a, b} | a b. (a, b) \<in> {(a, b). mate_lookup N a = Some b}}"
  "\<And>a b. mate_lookup N a = Some b \<Longrightarrow> mate_lookup N b = Some a"
  "\<And>a. mate_lookup N a \<noteq> Some a"
  "dVs {(a, b). mate_lookup N a = Some b} \<subseteq> Vs (ugraph_abs E)"
proof-
  show "set (matching_edges N vs') = {(a, b). mate_lookup N a = Some b}"
    by (rule matching_edges[OF contraction(1,2)])
  show "matching_abs N = {{a, b} | a b. (a, b) \<in> {(a, b). mate_lookup N a = Some b}}"
    by (simp add: Mate.\<M>_def')
  show "\<And>a b. mate_lookup N a = Some b \<Longrightarrow> mate_lookup N b = Some a"
    using Mate.invar_matchingD(2)[OF contraction_facts(7)]
    by (auto dest: Mate.symmetric_buddiesD)
  show "\<And>a. mate_lookup N a \<noteq> Some a"
    using Mate.invar_matchingD(3)[OF contraction_facts(7)]
    by (auto elim: Mate.no_self_loop_buddyE)
  show "dVs {(a, b). mate_lookup N a = Some b} \<subseteq> Vs (ugraph_abs E)"
    using matching_invar_mate_edge(2)[OF contraction(1,2)]
    by (fastforce simp: dVs_eq Vs_def)
qed

lemma contract_matching_abs:
  "matching_abs (contract_matching N vs' C u) = Q.quotG (matching_abs N)"
  and contract_matching_invar:
  "matching_invar (contract_graph E vs' C u) (contract_matching N vs' C u)"
proof-
  let ?D = "{(a, b). mate_lookup N a = Some b}"
  let ?ps = "quotient_edges C u (matching_edges N vs')"
  have quot: "{{a, b} | a b. (a, b) \<in> set ?ps} = Q.quotG (matching_abs N)"
  proof-
    have "v \<in> Vs (ugraph_abs E) - set C \<longleftrightarrow> v \<notin> set C" if "v \<in> dVs ?D" for v
      using that matching_pairs(5)
      by auto
    thus ?thesis
      using quotient_edges_quot_graph[OF matching_pairs(1), of "Vs (ugraph_abs E) - set C" C u]
            matching_pairs(3,4) contraction_facts(6)
      by (simp add: matching_pairs(2))
  qed
  have "matching (Q.quotG (matching_abs N))"
    by (rule Q.matching_quotM[OF blossomD(2)[OF contraction(3)] contraction_facts(8,9)]) simp
  moreover have "\<And>a b. (a, b) \<in> set ?ps \<Longrightarrow> (b, a) \<in> set ?ps"
    using quotient_edges_sym[of "matching_edges N vs'"] matching_pairs(1,3)
    by blast
  moreover have "\<And>a b. (a, b) \<in> set ?ps \<Longrightarrow>
                   (a, b) \<in> Graph.digraph_abs (contract_graph E vs' C u)"
  proof-
    have "set (matching_edges N vs') \<subseteq> set (adjacency_edges E vs')"
      using matching_pairs(1) adjacency_edges[OF contraction(1)]
            matching_invar_mate_edge(3)[OF contraction(1,2)]
      by auto
    thus "\<And>a b. (a, b) \<in> set ?ps \<Longrightarrow> (a, b) \<in> Graph.digraph_abs (contract_graph E vs' C u)"
      using quotient_edges_mono
      by (fastforce simp: contract_graph_def Graph.from_list_correct)
  qed
  ultimately have "matching_invar (contract_graph E vs' C u) (mate_from_list ?ps)"
                  "matching_abs (mate_from_list ?ps) = {{a, b} | a b. (a, b) \<in> set ?ps}"
    using mate_from_list[OF contract_graph_input, of ?ps] quotient_edges_irrefl quot
    by auto
  thus "matching_abs (contract_matching N vs' C u) = Q.quotG (matching_abs N)"
       "matching_invar (contract_graph E vs' C u) (contract_matching N vs' C u)"
    using quot
    by (simp_all add: contract_matching_def)
qed

lemma contract_card_Vs:
  "card (Vs (ugraph_abs (contract_graph E vs' C u))) < card (Vs (ugraph_abs E))"
proof-
  have "Vs (ugraph_abs E) - (Vs (ugraph_abs E) - set C) = set C"
    using contraction_facts(2)
    by blast
  hence "1 < card (Vs (ugraph_abs E) - (Vs (ugraph_abs E) - set C))"
    using contraction_facts(5)
    by simp
  thus ?thesis
    using Q.card_Vs_quotG contraction_facts(1)
    by (simp add: contract_graph_abs)
qed

lemma contract_complete:
  assumes "\<exists>p. graph_augmenting_path (ugraph_abs E) (matching_abs N) p"
  shows "\<exists>p. graph_augmenting_path (ugraph_abs (contract_graph E vs' C u))
                (matching_abs (contract_matching N vs' C u)) p"
proof-
  obtain p where p: "graph_augmenting_path (ugraph_abs E) (matching_abs N) p"
    using assms
    by blast
  have "\<exists>p'. graph_augmenting_path (Q.quotG (ugraph_abs E)) (Q.quotG (matching_abs N)) p'"
    by (rule Q.aug_path_works_in_contraction[OF contraction(3) p contraction_facts(8,9,10) refl
                                              contraction_facts(6)])
  thus ?thesis
    by (simp add: contract_graph_abs contract_matching_abs)
qed

lemma cycle_neighbour_eq:
  "cycle_neighbour E C v = cycle_sel C (set C \<inter> neighbourhood (ugraph_abs E) v)"
proof-
  have iff: "isin (Graph.neighbourhood E v) x \<longleftrightarrow> x \<in> neighbourhood (ugraph_abs E) v" for x
    using in_ugraph_abs_iff[OF contraction(1), of x v] graph_inputD(4)[OF contraction(1), of v x]
          graph_inputD(4)[OF contraction(1), of x v]
    by (auto simp: isin_neighbourhood_iff neighbourhood_def)
  have "find (\<lambda>x. isin (Graph.neighbourhood E v) x) C =
        find (\<lambda>x. x \<in> set C \<inter> neighbourhood (ugraph_abs E) v) C"
    by (rule find_cong) (auto simp: iff)
  moreover have "find (\<lambda>x. x \<in> set C \<inter> neighbourhood (ugraph_abs E) v) C = None \<Longrightarrow>
                 set C \<inter> neighbourhood (ugraph_abs E) v = {}"
    by (auto simp: find_None_iff)
  ultimately show ?thesis
    by (auto simp: cycle_neighbour_def cycle_sel_def split: option.splits)
qed

lemma choose_con_vert_eq:
  "Q.choose_con_vert (set C) v = cycle_neighbour E C v"
  by (simp add: Q.choose_con_vert_def cycle_neighbour_eq)

lemma last_edges_of_path_snoc2: "last (edges_of_path (ys @ [a, b])) = {a, b}"
  by (induction ys rule: induct_list012) auto

lemma last_edge_matched_iff:
  "2 \<le> length xs \<Longrightarrow> last_edge_matched N xs \<longleftrightarrow> last (edges_of_path xs) \<in> matching_abs N"
proof-
  assume len: "2 \<le> length xs"
  obtain ys a b where xs: "xs = ys @ [a, b]"
  proof-
    obtain b ys' where 1: "xs = ys' @ [b]" "Suc 0 \<le> length ys'"
      using Suc_le_length_iff_snoc2[of "Suc 0" xs] len
      by auto
    obtain a ys where "ys' = ys @ [a]"
      using Suc_le_length_iff_snoc2[of 0 ys'] 1(2)
      by auto
    thus ?thesis
      using that 1(1)
      by simp
  qed
  have "last (edges_of_path xs) = {a, b}"
    by (simp add: xs last_edges_of_path_snoc2)
  moreover have "last_edge_matched N xs \<longleftrightarrow> mate_lookup N a = Some b"
    by (simp add: last_edge_matched_def xs)
  ultimately show ?thesis
    by (simp add: matching_abs_iff[OF contraction_facts(7)])
qed

lemma cycle_path_eq:
  "cycle_path E N C v = Q.stem2vert_path C (matching_abs N) v"
proof-
  define w where "w = cycle_neighbour E C v"
  define pfx where "pfx = find_pfx ((=) w) C"
  have pfx_rev: "find_pfx ((=) w) (rev C) = pfx" if "length pfx < 2"
  proof-
    obtain c cs where C: "C = c # cs"
      using contraction_facts(3)
      by (cases C) auto
    have "cs \<noteq> []"
      using contraction_facts(5) C
      by auto
    hence "find_pfx ((=) w) cs \<noteq> []"
      by (rule find_pfx_nempty)
    hence wc: "w = c" "pfx = [c]"
      using that
      by (auto simp: pfx_def C split: if_splits)
    have "hd (rev C) = c"
      using contraction_facts(4) C
      by (simp add: hd_rev)
    then obtain ds where "rev C = c # ds"
      using C
      by (cases "rev C") auto
    thus ?thesis
      using wc
      by simp
  qed
  show ?thesis
  proof(cases "2 \<le> length pfx")
    case True
    then show ?thesis
      by (simp add: cycle_path_def Q.stem2vert_path_def choose_con_vert_eq Let_def
                    w_def[symmetric] pfx_def[symmetric] last_edge_matched_iff)
  next
    case False
    hence "last_edge_matched N pfx"
      by (cases pfx rule: rev_cases) (auto simp: last_edge_matched_def)
    then show ?thesis
      using pfx_rev False
      by (simp add: cycle_path_def Q.stem2vert_path_def choose_con_vert_eq Let_def
                    w_def[symmetric] pfx_def[symmetric])
  qed
qed

lemma matched_to_cycle_iff:
  "matched_to_cycle N C x \<longleftrightarrow> {u, x} \<in> Q.quotG (matching_abs N)"
proof
  assume m: "matched_to_cycle N C x"
  then obtain c where c: "x \<notin> set C" "mate_lookup N x = Some c" "c \<in> set C"
    by (auto simp: matched_to_cycle_def split: option.splits)
  have xc: "{x, c} \<in> matching_abs N"
    using c(2)
    by (simp add: matching_abs_iff[OF contraction_facts(7)])
  hence "x \<in> Vs (ugraph_abs E)"
    using contraction_facts(9)
    by (auto simp: Vs_def)
  hence "x \<noteq> u"
    using contraction_facts(6)
    by auto
  have "(\<lambda>v. if v \<in> Vs (ugraph_abs E) - set C then v else u) ` {x, c} = {x, u}"
    using c(1,3) \<open>x \<in> Vs (ugraph_abs E)\<close>
    by auto
  thus "{u, x} \<in> Q.quotG (matching_abs N)"
    using xc \<open>x \<noteq> u\<close>
    by (auto simp: quot_graph_def insert_commute doubleton_eq_iff intro!: bexI[of _ "{x, c}"])
next
  assume "{u, x} \<in> Q.quotG (matching_abs N)"
  then obtain e where e: "e \<in> matching_abs N"
      "{u, x} = (\<lambda>v. if v \<in> Vs (ugraph_abs E) - set C then v else u) ` e" "{u, x} \<noteq> {u}"
    by (auto simp: quot_graph_def)
  obtain a b where ab: "e = {a, b}" "mate_lookup N a = Some b"
    using e(1)
    by (auto simp: Mate.\<M>_def')
  have "a \<in> Vs (ugraph_abs E)" "b \<in> Vs (ugraph_abs E)"
    using e(1) ab(1) contraction_facts(9)
    by (auto simp: Vs_def)
  have "x \<noteq> u"
    using e(3)
    by auto
  show "matched_to_cycle N C x"
  proof(cases "a \<in> set C")
    case True
    hence "b \<notin> set C" "x = b"
      using e(2) ab(1) \<open>x \<noteq> u\<close> \<open>b \<in> Vs (ugraph_abs E)\<close>
      by (auto simp: doubleton_eq_iff split: if_splits)
    moreover have "mate_lookup N b = Some a"
      using ab(2) matching_pairs(3)
      by blast
    ultimately show ?thesis
      using True
      by (simp add: matched_to_cycle_def)
  next
    case False
    hence "b \<in> set C" "x = a"
      using e(2) ab(1) \<open>x \<noteq> u\<close> \<open>a \<in> Vs (ugraph_abs E)\<close> contraction_facts(6)
      by (auto simp: doubleton_eq_iff split: if_splits)
    thus ?thesis
      using False ab(2)
      by (simp add: matched_to_cycle_def)
  qed
qed

lemma replace_cycle_eq:
  "replace_cycle_impl E N C p1 p2 = Q.replace_cycle C (matching_abs N) p1 p2"
  by (simp add: replace_cycle_impl_def Q.replace_cycle_def cycle_path_eq matched_to_cycle_iff Let_def)

lemma lift_one_eq:
  "lift_one E N C u p = Q.refine C (matching_abs N) p"
  by (simp add: lift_one_def Q.refine_def replace_cycle_eq)

lemma lift_one_correct:
  assumes "graph_augmenting_path (ugraph_abs (contract_graph E vs' C u))
             (matching_abs (contract_matching N vs' C u)) p"
  shows "graph_augmenting_path (ugraph_abs E) (matching_abs N) (lift_one E N C u p)"
proof-
  have "graph_augmenting_path (Q.quotG (ugraph_abs E)) (Q.quotG (matching_abs N)) p"
    using assms
    by (simp add: contract_graph_abs contract_matching_abs)
  hence "graph_augmenting_path (ugraph_abs E) (matching_abs N) (Q.refine C (matching_abs N) p)"
    by (rule Q.refine_works[OF contraction(3) _ contraction_facts(8,9) refl])
  thus ?thesis
    by (simp add: lift_one_eq)
qed

end

subsubsection \<open>The loop\<close>

function (domintros) Blossom_Shrinking_Search ::
  "('adjmap, 'mate, 'v) Blossom_Shrinking_Search_state \<Rightarrow>
   ('adjmap, 'mate, 'v) Blossom_Shrinking_Search_state" where
  "Blossom_Shrinking_Search state =
     (case search_result state of
        Some (Blossom stem C) \<Rightarrow>
          (let u = fresh_vertex (search_vertices state);
               G' = contract_graph (search_graph state) (search_vertices state) C u;
               vs' = contract_vertices (search_vertices state) C u;
               M' = contract_matching (search_matching state) (search_vertices state) C u
           in Blossom_Shrinking_Search
                (state \<lparr>search_graph := G', search_vertices := vs', search_matching := M',
                        contractions := (search_graph state, search_matching state, C, u)
                                          # contractions state,
                        search_result := blossom_search G' vs' M'\<rparr>))
      | _ \<Rightarrow> state)"
  by pat_completeness auto

partial_function (tailrec) Blossom_Shrinking_Search_impl ::
  "('adjmap, 'mate, 'v) Blossom_Shrinking_Search_state \<Rightarrow>
   ('adjmap, 'mate, 'v) Blossom_Shrinking_Search_state" where
  "Blossom_Shrinking_Search_impl state =
     (case search_result state of
        Some (Blossom stem C) \<Rightarrow>
          (let u = fresh_vertex (search_vertices state);
               G' = contract_graph (search_graph state) (search_vertices state) C u;
               vs' = contract_vertices (search_vertices state) C u;
               M' = contract_matching (search_matching state) (search_vertices state) C u
           in Blossom_Shrinking_Search_impl
                (state \<lparr>search_graph := G', search_vertices := vs', search_matching := M',
                        contractions := (search_graph state, search_matching state, C, u)
                                          # contractions state,
                        search_result := blossom_search G' vs' M'\<rparr>))
      | _ \<Rightarrow> state)"

lemma Blossom_Shrinking_Search_impl_same:
  assumes "Blossom_Shrinking_Search_dom state"
  shows "Blossom_Shrinking_Search_impl state = Blossom_Shrinking_Search state"
  apply(induction rule: Blossom_Shrinking_Search.pinduct[OF assms])
  apply(subst Blossom_Shrinking_Search_impl.simps)
  by (auto simp: Blossom_Shrinking_Search.psimps Let_def
          split: option.splits match_blossom_res.splits)

definition "initial_state =
  \<lparr>search_graph = G, search_vertices = vs, search_matching = M, contractions = [],
   search_result = blossom_search G vs M\<rparr>"

text \<open>The answer is read off the final state.\<close>

definition "augmenting_path state =
  (case search_result state of
     Some (Path p) \<Rightarrow> Some (lift_path (contractions state) p)
   | _ \<Rightarrow> None)"

definition "Blossom_Shrinking_Search_run = augmenting_path (Blossom_Shrinking_Search initial_state)"

definition "Blossom_Shrinking_Search_run_impl =
  augmenting_path (Blossom_Shrinking_Search_impl initial_state)"

lemmas [code] = Blossom_Shrinking_Search_impl.simps initial_state_def augmenting_path_def
  Blossom_Shrinking_Search_run_impl_def

definition "Blossom_Shrinking_Search_call_1_conds state =
  (\<exists>stem C. search_result state = Some (Blossom stem C))"

definition "Blossom_Shrinking_Search_upd1 state =
  (case search_result state of
     Some (Blossom stem C) \<Rightarrow>
       (let u = fresh_vertex (search_vertices state);
            G' = contract_graph (search_graph state) (search_vertices state) C u;
            vs' = contract_vertices (search_vertices state) C u;
            M' = contract_matching (search_matching state) (search_vertices state) C u
        in state \<lparr>search_graph := G', search_vertices := vs', search_matching := M',
                  contractions := (search_graph state, search_matching state, C, u)
                                    # contractions state,
                  search_result := blossom_search G' vs' M'\<rparr>)
   | _ \<Rightarrow> state)"

definition "Blossom_Shrinking_Search_ret_1_conds state =
  (\<exists>p. search_result state = Some (Path p))"

abbreviation "Blossom_Shrinking_Search_ret1 state \<equiv> state"

definition "Blossom_Shrinking_Search_ret_2_conds state = (search_result state = None)"

abbreviation "Blossom_Shrinking_Search_ret2 state \<equiv> state"

definition "invar_1 state \<longleftrightarrow>
  graph_input (search_graph state) (search_vertices state) \<and>
  matching_invar (search_graph state) (search_matching state)"

definition "invar_search state \<longleftrightarrow>
  search_result state =
    blossom_search (search_graph state) (search_vertices state) (search_matching state)"

definition "invar_lift state \<longleftrightarrow>
  (\<forall>p. graph_augmenting_path (ugraph_abs (search_graph state)) (matching_abs (search_matching state)) p
       \<longrightarrow> graph_augmenting_path (ugraph_abs G) (matching_abs M) (lift_path (contractions state) p))"

definition "invar_complete state \<longleftrightarrow>
  ((\<exists>p. graph_augmenting_path (ugraph_abs G) (matching_abs M) p) \<longrightarrow>
   (\<exists>p. graph_augmenting_path (ugraph_abs (search_graph state))
          (matching_abs (search_matching state)) p))"

definition "call_1_measure state = card (Vs (ugraph_abs (search_graph state)))"

definition "Blossom_Shrinking_Search_term_rel' = call_1_measure <*mlex*> {}"

lemma Blossom_Shrinking_Search_call_1_conds[call_cond_elims]:
  "Blossom_Shrinking_Search_call_1_conds state \<Longrightarrow>
   ((\<exists>stem C. search_result state = Some (Blossom stem C)) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: Blossom_Shrinking_Search_call_1_conds_def)

lemma Blossom_Shrinking_Search_call_1_condsI[call_cond_intros]:
  "search_result state = Some (Blossom stem C) \<Longrightarrow> Blossom_Shrinking_Search_call_1_conds state"
  by (auto simp: Blossom_Shrinking_Search_call_1_conds_def)

lemma Blossom_Shrinking_Search_ret_1_conds[call_cond_elims]:
  "Blossom_Shrinking_Search_ret_1_conds state \<Longrightarrow>
   ((\<exists>p. search_result state = Some (Path p)) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: Blossom_Shrinking_Search_ret_1_conds_def)

lemma Blossom_Shrinking_Search_ret_1_condsI[call_cond_intros]:
  "search_result state = Some (Path p) \<Longrightarrow> Blossom_Shrinking_Search_ret_1_conds state"
  by (auto simp: Blossom_Shrinking_Search_ret_1_conds_def)

lemma Blossom_Shrinking_Search_ret_2_conds[call_cond_elims]:
  "Blossom_Shrinking_Search_ret_2_conds state \<Longrightarrow> (search_result state = None \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: Blossom_Shrinking_Search_ret_2_conds_def)

lemma Blossom_Shrinking_Search_ret_2_condsI[call_cond_intros]:
  "search_result state = None \<Longrightarrow> Blossom_Shrinking_Search_ret_2_conds state"
  by (auto simp: Blossom_Shrinking_Search_ret_2_conds_def)

lemma Blossom_Shrinking_Search_cases:
  assumes "Blossom_Shrinking_Search_call_1_conds state \<Longrightarrow> P"
          "Blossom_Shrinking_Search_ret_1_conds state \<Longrightarrow> P"
          "Blossom_Shrinking_Search_ret_2_conds state \<Longrightarrow> P"
  shows "P"
proof(cases "search_result state")
  case None
  then show ?thesis
    using assms(3)
    by (auto simp: Blossom_Shrinking_Search_ret_2_conds_def)
next
  case (Some res)
  then show ?thesis
    using assms(1,2)
    by (cases res)
       (auto simp: Blossom_Shrinking_Search_call_1_conds_def Blossom_Shrinking_Search_ret_1_conds_def)
qed

lemma Blossom_Shrinking_Search_simps:
  assumes "Blossom_Shrinking_Search_dom state"
  shows "Blossom_Shrinking_Search_call_1_conds state \<Longrightarrow>
           Blossom_Shrinking_Search state =
             Blossom_Shrinking_Search (Blossom_Shrinking_Search_upd1 state)"
        "Blossom_Shrinking_Search_ret_1_conds state \<Longrightarrow>
           Blossom_Shrinking_Search state = Blossom_Shrinking_Search_ret1 state"
        "Blossom_Shrinking_Search_ret_2_conds state \<Longrightarrow>
           Blossom_Shrinking_Search state = Blossom_Shrinking_Search_ret2 state"
  by (auto simp: Blossom_Shrinking_Search.psimps[OF assms] Let_def Blossom_Shrinking_Search_upd1_def
                 Blossom_Shrinking_Search_call_1_conds_def Blossom_Shrinking_Search_ret_1_conds_def
                 Blossom_Shrinking_Search_ret_2_conds_def)

lemma Blossom_Shrinking_Search_induct:
  assumes "Blossom_Shrinking_Search_dom state"
  assumes "\<And>state. \<lbrakk>Blossom_Shrinking_Search_dom state;
                     Blossom_Shrinking_Search_call_1_conds state \<Longrightarrow>
                       P (Blossom_Shrinking_Search_upd1 state)\<rbrakk>
                    \<Longrightarrow> P state"
  shows "P state"
  apply(rule Blossom_Shrinking_Search.pinduct[OF assms(1)])
  apply(rule assms(2))
  by (auto simp: Let_def Blossom_Shrinking_Search_call_1_conds_def Blossom_Shrinking_Search_upd1_def)

lemma Blossom_Shrinking_Search_domintros:
  assumes "Blossom_Shrinking_Search_call_1_conds state \<Longrightarrow>
             Blossom_Shrinking_Search_dom (Blossom_Shrinking_Search_upd1 state)"
  shows "Blossom_Shrinking_Search_dom state"
  using assms
  by (auto intro: Blossom_Shrinking_Search.domintros
           simp: Let_def Blossom_Shrinking_Search_call_1_conds_def Blossom_Shrinking_Search_upd1_def)

subsubsection \<open>Proofs\<close>

context
  assumes Blossom_Shrinking_Search_axiom: Blossom_Shrinking_Search_axiom
begin

lemma graph_input_G[simp]: "graph_input G vs"
  and matching_invar_M[simp]: "matching_invar G M"
  using Blossom_Shrinking_Search_axiom
  by (simp_all add: Blossom_Shrinking_Search_axiom_def)

lemma call_1_facts:
  assumes "Blossom_Shrinking_Search_call_1_conds state" "invar_1 state" "invar_search state"
  obtains stem C where
    "search_result state = Some (Blossom stem C)"
    "blossom (ugraph_abs (search_graph state)) (matching_abs (search_matching state)) stem C"
proof-
  obtain stem C where sc: "search_result state = Some (Blossom stem C)"
    using assms(1)
    by (auto elim!: call_cond_elims)
  have "blossom (ugraph_abs (search_graph state)) (matching_abs (search_matching state)) stem C"
    using blossom_search(2) assms(2,3) sc
    by (auto simp: invar_1_def invar_search_def)
  thus ?thesis
    using that sc
    by blast
qed

lemma upd1_fields:
  assumes "search_result state = Some (Blossom stem C)"
  shows "search_graph (Blossom_Shrinking_Search_upd1 state) =
           contract_graph (search_graph state) (search_vertices state) C
             (fresh_vertex (search_vertices state))"
        "search_vertices (Blossom_Shrinking_Search_upd1 state) =
           contract_vertices (search_vertices state) C (fresh_vertex (search_vertices state))"
        "search_matching (Blossom_Shrinking_Search_upd1 state) =
           contract_matching (search_matching state) (search_vertices state) C
             (fresh_vertex (search_vertices state))"
        "contractions (Blossom_Shrinking_Search_upd1 state) =
           (search_graph state, search_matching state, C, fresh_vertex (search_vertices state))
             # contractions state"
        "search_result (Blossom_Shrinking_Search_upd1 state) =
           blossom_search (search_graph (Blossom_Shrinking_Search_upd1 state))
             (search_vertices (Blossom_Shrinking_Search_upd1 state))
             (search_matching (Blossom_Shrinking_Search_upd1 state))"
  using assms
  by (simp_all add: Blossom_Shrinking_Search_upd1_def Let_def)

subsubsection \<open>The representation invariant\<close>

lemma invar_1_props[invar_props_elims]:
  "invar_1 state \<Longrightarrow>
   (\<lbrakk>graph_input (search_graph state) (search_vertices state);
     matching_invar (search_graph state) (search_matching state)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_1_def)

lemma invar_1_intro[invar_props_intros]:
  "\<lbrakk>graph_input (search_graph state) (search_vertices state);
    matching_invar (search_graph state) (search_matching state)\<rbrakk> \<Longrightarrow> invar_1 state"
  by (auto simp: invar_1_def)

lemma invar_1_holds_1[invar_holds_intros]:
  assumes "Blossom_Shrinking_Search_call_1_conds state" "invar_1 state" "invar_search state"
  shows "invar_1 (Blossom_Shrinking_Search_upd1 state)"
proof-
  obtain stem C where f:
    "search_result state = Some (Blossom stem C)"
    "blossom (ugraph_abs (search_graph state)) (matching_abs (search_matching state)) stem C"
    by (rule call_1_facts[OF assms])
  note upd = upd1_fields[OF f(1)]
  have fresh: "fresh_vertex (search_vertices state) \<notin> set (search_vertices state)"
    by (rule fresh_vertex)
  have g: "graph_input (search_graph state) (search_vertices state)"
          "matching_invar (search_graph state) (search_matching state)"
    using assms(2)
    by (auto elim!: invar_props_elims)
  show ?thesis
    using contract_graph_input[OF g f(2) fresh] contract_matching_invar[OF g f(2) fresh]
    by (auto intro!: invar_props_intros simp: upd)
qed

lemma invar_1_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>Blossom_Shrinking_Search_ret_1_conds state; invar_1 state\<rbrakk>
   \<Longrightarrow> invar_1 (Blossom_Shrinking_Search_ret1 state)"
  by auto

lemma invar_1_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>Blossom_Shrinking_Search_ret_2_conds state; invar_1 state\<rbrakk>
   \<Longrightarrow> invar_1 (Blossom_Shrinking_Search_ret2 state)"
  by auto

lemma invar_1_holds[invar_holds_intros]:
  assumes "Blossom_Shrinking_Search_dom state" "invar_1 state" "invar_search state"
  shows "invar_1 (Blossom_Shrinking_Search state)"
  using assms(2-)
proof(induction rule: Blossom_Shrinking_Search_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    apply(rule Blossom_Shrinking_Search_cases[where state = state])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: Blossom_Shrinking_Search_simps[OF IH(1)])
qed

subsubsection \<open>The stored search result\<close>

lemma invar_search_props[invar_props_elims]:
  "invar_search state \<Longrightarrow>
   (search_result state =
      blossom_search (search_graph state) (search_vertices state) (search_matching state) \<Longrightarrow> P)
   \<Longrightarrow> P"
  by (auto simp: invar_search_def)

lemma invar_search_intro[invar_props_intros]:
  "search_result state =
     blossom_search (search_graph state) (search_vertices state) (search_matching state)
   \<Longrightarrow> invar_search state"
  by (auto simp: invar_search_def)

lemma invar_search_holds_1[invar_holds_intros]:
  "\<lbrakk>Blossom_Shrinking_Search_call_1_conds state; invar_search state\<rbrakk>
   \<Longrightarrow> invar_search (Blossom_Shrinking_Search_upd1 state)"
  by (auto elim!: call_cond_elims
           simp: invar_search_def Blossom_Shrinking_Search_upd1_def Let_def)

lemma invar_search_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>Blossom_Shrinking_Search_ret_1_conds state; invar_search state\<rbrakk>
   \<Longrightarrow> invar_search (Blossom_Shrinking_Search_ret1 state)"
  by auto

lemma invar_search_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>Blossom_Shrinking_Search_ret_2_conds state; invar_search state\<rbrakk>
   \<Longrightarrow> invar_search (Blossom_Shrinking_Search_ret2 state)"
  by auto

lemma invar_search_holds[invar_holds_intros]:
  assumes "Blossom_Shrinking_Search_dom state" "invar_search state"
  shows "invar_search (Blossom_Shrinking_Search state)"
  using assms(2-)
proof(induction rule: Blossom_Shrinking_Search_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    apply(rule Blossom_Shrinking_Search_cases[where state = state])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: Blossom_Shrinking_Search_simps[OF IH(1)])
qed

subsubsection \<open>Lifting gives augmenting paths of the input\<close>

lemma invar_lift_props[invar_props_elims]:
  "invar_lift state \<Longrightarrow>
   ((\<forall>p. graph_augmenting_path (ugraph_abs (search_graph state)) (matching_abs (search_matching state)) p
         \<longrightarrow> graph_augmenting_path (ugraph_abs G) (matching_abs M) (lift_path (contractions state) p))
    \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_lift_def)

lemma invar_lift_intro[invar_props_intros]:
  "(\<forall>p. graph_augmenting_path (ugraph_abs (search_graph state)) (matching_abs (search_matching state)) p
        \<longrightarrow> graph_augmenting_path (ugraph_abs G) (matching_abs M) (lift_path (contractions state) p))
   \<Longrightarrow> invar_lift state"
  by (auto simp: invar_lift_def)

lemma invar_lift_holds_1[invar_holds_intros]:
  assumes "Blossom_Shrinking_Search_call_1_conds state" "invar_1 state" "invar_search state"
          "invar_lift state"
  shows "invar_lift (Blossom_Shrinking_Search_upd1 state)"
proof-
  obtain stem C where f:
    "search_result state = Some (Blossom stem C)"
    "blossom (ugraph_abs (search_graph state)) (matching_abs (search_matching state)) stem C"
    by (rule call_1_facts[OF assms(1-3)])
  note upd = upd1_fields[OF f(1)]
  have fresh: "fresh_vertex (search_vertices state) \<notin> set (search_vertices state)"
    by (rule fresh_vertex)
  have g: "graph_input (search_graph state) (search_vertices state)"
          "matching_invar (search_graph state) (search_matching state)"
    using assms(2)
    by (auto elim!: invar_props_elims)
  show ?thesis
    using lift_one_correct[OF g f(2) fresh] assms(4)
    by (auto intro!: invar_props_intros elim!: invar_props_elims simp: upd)
qed

lemma invar_lift_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>Blossom_Shrinking_Search_ret_1_conds state; invar_lift state\<rbrakk>
   \<Longrightarrow> invar_lift (Blossom_Shrinking_Search_ret1 state)"
  by auto

lemma invar_lift_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>Blossom_Shrinking_Search_ret_2_conds state; invar_lift state\<rbrakk>
   \<Longrightarrow> invar_lift (Blossom_Shrinking_Search_ret2 state)"
  by auto

lemma invar_lift_holds[invar_holds_intros]:
  assumes "Blossom_Shrinking_Search_dom state" "invar_1 state" "invar_search state"
          "invar_lift state"
  shows "invar_lift (Blossom_Shrinking_Search state)"
  using assms(2-)
proof(induction rule: Blossom_Shrinking_Search_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    apply(rule Blossom_Shrinking_Search_cases[where state = state])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: Blossom_Shrinking_Search_simps[OF IH(1)])
qed

subsubsection \<open>Contraction preserves the existence of augmenting paths\<close>

lemma invar_complete_props[invar_props_elims]:
  "invar_complete state \<Longrightarrow>
   (((\<exists>p. graph_augmenting_path (ugraph_abs G) (matching_abs M) p) \<longrightarrow>
     (\<exists>p. graph_augmenting_path (ugraph_abs (search_graph state))
            (matching_abs (search_matching state)) p)) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_complete_def)

lemma invar_complete_intro[invar_props_intros]:
  "((\<exists>p. graph_augmenting_path (ugraph_abs G) (matching_abs M) p) \<longrightarrow>
    (\<exists>p. graph_augmenting_path (ugraph_abs (search_graph state))
           (matching_abs (search_matching state)) p))
   \<Longrightarrow> invar_complete state"
  by (auto simp: invar_complete_def)

lemma invar_complete_holds_1[invar_holds_intros]:
  assumes "Blossom_Shrinking_Search_call_1_conds state" "invar_1 state" "invar_search state"
          "invar_complete state"
  shows "invar_complete (Blossom_Shrinking_Search_upd1 state)"
proof-
  obtain stem C where f:
    "search_result state = Some (Blossom stem C)"
    "blossom (ugraph_abs (search_graph state)) (matching_abs (search_matching state)) stem C"
    by (rule call_1_facts[OF assms(1-3)])
  note upd = upd1_fields[OF f(1)]
  have fresh: "fresh_vertex (search_vertices state) \<notin> set (search_vertices state)"
    by (rule fresh_vertex)
  have g: "graph_input (search_graph state) (search_vertices state)"
          "matching_invar (search_graph state) (search_matching state)"
    using assms(2)
    by (auto elim!: invar_props_elims)
  show ?thesis
    using contract_complete[OF g f(2) fresh] assms(4)
    by (auto intro!: invar_props_intros elim!: invar_props_elims simp: upd)
qed

lemma invar_complete_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>Blossom_Shrinking_Search_ret_1_conds state; invar_complete state\<rbrakk>
   \<Longrightarrow> invar_complete (Blossom_Shrinking_Search_ret1 state)"
  by auto

lemma invar_complete_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>Blossom_Shrinking_Search_ret_2_conds state; invar_complete state\<rbrakk>
   \<Longrightarrow> invar_complete (Blossom_Shrinking_Search_ret2 state)"
  by auto

lemma invar_complete_holds[invar_holds_intros]:
  assumes "Blossom_Shrinking_Search_dom state" "invar_1 state" "invar_search state"
          "invar_complete state"
  shows "invar_complete (Blossom_Shrinking_Search state)"
  using assms(2-)
proof(induction rule: Blossom_Shrinking_Search_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    apply(rule Blossom_Shrinking_Search_cases[where state = state])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: Blossom_Shrinking_Search_simps[OF IH(1)])
qed

subsubsection \<open>Termination\<close>

named_theorems termination_intros

lemma call_1_terminates[termination_intros]:
  assumes "Blossom_Shrinking_Search_call_1_conds state" "invar_1 state" "invar_search state"
  shows "(Blossom_Shrinking_Search_upd1 state, state) \<in> call_1_measure <*mlex*> r"
proof-
  obtain stem C where f:
    "search_result state = Some (Blossom stem C)"
    "blossom (ugraph_abs (search_graph state)) (matching_abs (search_matching state)) stem C"
    by (rule call_1_facts[OF assms])
  note upd = upd1_fields[OF f(1)]
  have fresh: "fresh_vertex (search_vertices state) \<notin> set (search_vertices state)"
    by (rule fresh_vertex)
  have g: "graph_input (search_graph state) (search_vertices state)"
          "matching_invar (search_graph state) (search_matching state)"
    using assms(2)
    by (auto elim!: invar_props_elims)
  show ?thesis
    using contract_card_Vs[OF g f(2) fresh]
    by (intro mlex_less) (simp add: call_1_measure_def upd)
qed

lemma wf_term_rel: "wf Blossom_Shrinking_Search_term_rel'"
  by (auto simp: wf_mlex Blossom_Shrinking_Search_term_rel'_def)

lemma in_Blossom_Shrinking_Search_term_rel'[termination_intros]:
  "\<lbrakk>Blossom_Shrinking_Search_call_1_conds state; invar_1 state; invar_search state\<rbrakk> \<Longrightarrow>
     (Blossom_Shrinking_Search_upd1 state, state) \<in> Blossom_Shrinking_Search_term_rel'"
  by (simp add: Blossom_Shrinking_Search_term_rel'_def termination_intros)

lemma Blossom_Shrinking_Search_terminates[termination_intros]:
  assumes "invar_1 state" "invar_search state"
  shows "Blossom_Shrinking_Search_dom state"
  using wf_term_rel assms
proof(induction rule: wf_induct_rule)
  case (less x)
  show ?case
    by (rule Blossom_Shrinking_Search_domintros)
       (auto intro!: invar_holds_intros less in_Blossom_Shrinking_Search_term_rel')
qed

subsubsection \<open>Correctness\<close>

lemma Blossom_Shrinking_Search_correct_ret_1:
  assumes "invar_1 state" "invar_search state" "invar_lift state"
          "Blossom_Shrinking_Search_ret_1_conds state" "augmenting_path state = Some q"
  shows "graph_augmenting_path (ugraph_abs G) (matching_abs M) q"
proof-
  obtain p where p: "search_result state = Some (Path p)"
    using assms(4)
    by (auto elim!: call_cond_elims)
  have "graph_augmenting_path (ugraph_abs (search_graph state)) (matching_abs (search_matching state)) p"
    using blossom_search(1) assms(1,2) p
    by (auto elim!: invar_props_elims)
  moreover have "q = lift_path (contractions state) p"
    using assms(5) p
    by (simp add: augmenting_path_def)
  ultimately show ?thesis
    using assms(3)
    by (auto elim!: invar_props_elims)
qed

lemma Blossom_Shrinking_Search_correct_ret_2:
  assumes "invar_1 state" "invar_search state" "invar_complete state"
          "Blossom_Shrinking_Search_ret_2_conds state"
  shows "augmenting_path state = None"
        "\<nexists>p. graph_augmenting_path (ugraph_abs G) (matching_abs M) p"
proof-
  have none: "search_result state = None"
    using assms(4)
    by (auto elim!: call_cond_elims)
  thus "augmenting_path state = None"
    by (simp add: augmenting_path_def)
  have "\<nexists>p. graph_augmenting_path (ugraph_abs (search_graph state))
               (matching_abs (search_matching state)) p"
    using blossom_search(3) assms(1,2) none
    by (auto elim!: invar_props_elims)
  thus "\<nexists>p. graph_augmenting_path (ugraph_abs G) (matching_abs M) p"
    using assms(3)
    by (auto elim!: invar_props_elims)
qed

lemma ret_holds[ret_holds_intros]:
  assumes "Blossom_Shrinking_Search_dom state"
  shows "Blossom_Shrinking_Search_ret_1_conds (Blossom_Shrinking_Search state) \<or>
         Blossom_Shrinking_Search_ret_2_conds (Blossom_Shrinking_Search state)"
proof(induction rule: Blossom_Shrinking_Search_induct[OF assms])
  case IH: (1 state)
  show ?case
    apply(rule Blossom_Shrinking_Search_cases[where state = state])
    by (auto intro: IH(2-) simp: Blossom_Shrinking_Search_simps[OF IH(1)])
qed

subsubsection \<open>The initial state\<close>

lemma initial_state_props[invar_holds_intros, termination_intros]:
  "invar_1 initial_state" "invar_search initial_state" "invar_lift initial_state"
  "invar_complete initial_state" "Blossom_Shrinking_Search_dom initial_state"
proof-
  show inv1: "invar_1 initial_state"
    by (auto intro!: invar_props_intros simp: initial_state_def)
  show invs: "invar_search initial_state"
    by (auto intro!: invar_props_intros simp: initial_state_def)
  show "invar_lift initial_state"
    by (auto intro!: invar_props_intros simp: initial_state_def)
  show "invar_complete initial_state"
    by (auto intro!: invar_props_intros simp: initial_state_def)
  show "Blossom_Shrinking_Search_dom initial_state"
    by (rule Blossom_Shrinking_Search_terminates[OF inv1 invs])
qed

lemma Blossom_Shrinking_Search_impl_to_Blossom_Shrinking_Search:
  "Blossom_Shrinking_Search_impl initial_state = Blossom_Shrinking_Search initial_state"
  by (auto intro!: Blossom_Shrinking_Search_impl_same initial_state_props)

subsubsection \<open>Final correctness\<close>

lemma final_state_invars:
  "invar_1 (Blossom_Shrinking_Search initial_state)"
  "invar_search (Blossom_Shrinking_Search initial_state)"
  "invar_lift (Blossom_Shrinking_Search initial_state)"
  "invar_complete (Blossom_Shrinking_Search initial_state)"
  by (auto intro!: invar_holds_intros)

lemma Blossom_Shrinking_Search_correct_1:
  assumes "augmenting_path (Blossom_Shrinking_Search initial_state) = Some q"
  shows "graph_augmenting_path (ugraph_abs G) (matching_abs M) q"
  using ret_holds[OF initial_state_props(5)] assms
        Blossom_Shrinking_Search_correct_ret_1[OF final_state_invars(1-3)]
        Blossom_Shrinking_Search_correct_ret_2(1)[OF final_state_invars(1,2,4)]
  by auto

lemma Blossom_Shrinking_Search_correct_2:
  assumes "\<exists>p. graph_augmenting_path (ugraph_abs G) (matching_abs M) p"
  shows "augmenting_path (Blossom_Shrinking_Search initial_state) \<noteq> None"
  using ret_holds[OF initial_state_props(5)] assms
        Blossom_Shrinking_Search_correct_ret_2(2)[OF final_state_invars(1,2,4)]
  by (auto elim!: call_cond_elims simp: augmenting_path_def)

lemma Blossom_Shrinking_Search_run_impl_correct:
  "Blossom_Shrinking_Search_run_impl = Some q \<Longrightarrow>
     graph_augmenting_path (ugraph_abs G) (matching_abs M) q"
  "\<exists>p. graph_augmenting_path (ugraph_abs G) (matching_abs M) p \<Longrightarrow>
     Blossom_Shrinking_Search_run_impl \<noteq> None"
  using Blossom_Shrinking_Search_correct_1 Blossom_Shrinking_Search_correct_2
  by (simp_all add: Blossom_Shrinking_Search_run_impl_def
                    Blossom_Shrinking_Search_impl_to_Blossom_Shrinking_Search)

end

end

end
```

---

## Phase 5: finding an augmenting path or a blossom (`Edmonds_Blossom_Subprocedures.thy`)

**Goal.** `blossom_search_path`, `blossom_search_blossom`, `blossom_search_complete`: exactly
the three contract clauses of `Blossom_Shrinking_Search` for `blossom_search`.

**Recon.** `thm construct_path construct_aug_path' common_pfxs_form_match_blossom' pfxs_path
disj_pfx_is_complete first_pfx_then_snd_pfx disj_pref_append1 disj_pref_append2
first_pfx_nempty snd_pfx_nempty pfx_common_end compute_alt_path_spec_def`.

**Frozen statements.** The locale (its contract), `blossom_search_def`, the three lemmas.

**One-shot theory** (copy verbatim into `Edmonds_Blossom_Executable/Edmonds_Blossom_Subprocedures.thy`):

```isabelle
theory Edmonds_Blossom_Subprocedures
  imports Blossom_Shrinking_Search Blossom.Blossom_Algo_Compute_Aug_Path
begin

provenance ai

section \<open>Finding an augmenting path or a blossom\<close>

text \<open>The alternating forest search returns two alternating paths, from the endpoints of an edge
  between two even vertices to the roots of their trees. If the two paths are vertex-disjoint,
  they form an augmenting path together with that edge. Otherwise they share a suffix, and their
  longest disjoint prefixes form a blossom with the remainder of either path as its stem. This is
  the procedure @{const compute_match_blossom'.compute_match_blossom}, without its special case
  for an edge between two free vertices: the forest search returns such an edge itself.\<close>

lemma compute_alt_path_specD:
  assumes "compute_alt_path_spec G M (Some (p1, p2))"
  shows "\<And>pref1 x post1 pref2 post2. \<lbrakk>p1 = pref1 @ x # post1; p2 = pref2 @ x # post2\<rbrakk>
           \<Longrightarrow> post1 = post2"
        "alt_path M (hd p1 # p2)" "alt_path M (hd p2 # p1)" "last p1 \<notin> Vs M" "last p2 \<notin> Vs M"
        "hd p1 \<noteq> hd p2" "odd (length p1)" "odd (length p2)" "distinct p1" "distinct p2"
        "path G p1" "path G p2" "{hd p1, hd p2} \<in> G"
  using assms
  by (auto simp: compute_alt_path_spec_def)

lemma common_suffix:
  assumes "compute_alt_path_spec G M (Some (p1, p2))"
          "(Some pfx1, Some pfx2) = longest_disj_pfx p1 p2"
  obtains p where "p1 = pfx1 @ p" "p2 = pfx2 @ p"
proof-
  obtain p1' p2' where pp: "p1 = pfx1 @ p1'" "p2 = pfx2 @ p2'"
    using disj_pref_append1[OF assms(2)] disj_pref_append2[OF assms(2)]
    by blast
  obtain ys1 y1 where s1: "pfx1 = ys1 @ [y1]"
    using first_pfx_nempty[OF assms(2)]
    by (cases pfx1 rule: rev_cases) auto
  obtain ys2 y2 where s2: "pfx2 = ys2 @ [y2]"
    using snd_pfx_nempty[OF assms(2)]
    by (cases pfx2 rule: rev_cases) auto
  have "y1 = y2"
    using pfx_common_end[OF assms(2)] s1 s2
    by simp
  hence "p1' = p2'"
    using compute_alt_path_specD(1)[OF assms(1), of ys1 y1 p1' ys2 p2'] pp s1 s2
    by simp
  thus ?thesis
    using that pp
    by blast
qed

(* PLAN CHANGE A1 (2026-10-24): mate_empty is instantiated by name and typed in the for
   clause, so that the type variable 'mate below is that of the mate-function ADT. *)
locale Edmonds_Blossom_Subprocedures = Graph_Matching_Specs where lookup = lookup and mate_empty = mate_empty
  for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option" and mate_empty :: 'mate +
  fixes alternating_forest_search ::
    "'adjmap \<Rightarrow> 'v list \<Rightarrow> 'mate \<Rightarrow> ('v list \<times> 'v list) option"
  assumes alternating_forest_search:
    "\<And>G vs M. \<lbrakk>graph_input G vs; matching_invar G M\<rbrakk>
       \<Longrightarrow> compute_alt_path_spec (ugraph_abs G) (matching_abs M) (alternating_forest_search G vs M)"
    "\<And>G vs M. \<lbrakk>graph_input G vs; matching_invar G M;
                \<exists>p. graph_augmenting_path (ugraph_abs G) (matching_abs M) p\<rbrakk>
       \<Longrightarrow> alternating_forest_search G vs M \<noteq> None"
begin

definition "blossom_search G vs M =
  (case alternating_forest_search G vs M of
     Some (p1, p2) \<Rightarrow>
       (if set p1 \<inter> set p2 = {} then Some (Path (rev p1 @ p2))
        else (case longest_disj_pfx p1 p2 of
                (pfx1, pfx2) \<Rightarrow>
                  Some (Blossom (rev (drop (length (the pfx1)) p1)) (rev (the pfx1) @ the pfx2))))
   | None \<Rightarrow> None)"

lemmas [code] = blossom_search_def

lemma blossom_search_path:
  assumes "graph_input G vs" "matching_invar G M" "blossom_search G vs M = Some (Path p)"
  shows "graph_augmenting_path (ugraph_abs G) (matching_abs M) p"
proof-
  obtain p1 p2 where res: "alternating_forest_search G vs M = Some (p1, p2)"
      "set p1 \<inter> set p2 = {}" "p = rev p1 @ p2"
    using assms(3)
    by (auto simp: blossom_search_def split: option.splits if_splits prod.splits)
  have spec: "compute_alt_path_spec (ugraph_abs G) (matching_abs M) (Some (p1, p2))"
    using alternating_forest_search(1)[OF assms(1,2)] res(1)
    by simp
  note S = compute_alt_path_specD[OF spec]
  have ne: "p1 \<noteq> []" "p2 \<noteq> []"
    using S(7,8)
    by auto
  have "path (ugraph_abs G) (rev p1 @ p2)"
    by (rule construct_path[OF S(11,12,13)])
  moreover have "distinct (rev p1 @ p2)"
    using S(9,10) res(2)
    by simp
  moreover have "matching_augmenting_path (matching_abs M) (rev p1 @ p2)"
    by (rule construct_aug_path'[OF res(2) ne S(3,2,4,5,7,8)])
  ultimately show ?thesis
    using res(3)
    by simp
qed

lemma blossom_search_blossom:
  assumes "graph_input G vs" "matching_invar G M" "blossom_search G vs M = Some (Blossom stem C)"
  shows "blossom (ugraph_abs G) (matching_abs M) stem C"
proof-
  obtain p1 p2 pfx1 pfx2 where res: "alternating_forest_search G vs M = Some (p1, p2)"
      "set p1 \<inter> set p2 \<noteq> {}" "longest_disj_pfx p1 p2 = (pfx1, pfx2)"
      "stem = rev (drop (length (the pfx1)) p1)" "C = rev (the pfx1) @ the pfx2"
    using assms(3)
    by (auto simp: blossom_search_def split: option.splits if_splits prod.splits)
  have spec: "compute_alt_path_spec (ugraph_abs G) (matching_abs M) (Some (p1, p2))"
    using alternating_forest_search(1)[OF assms(1,2)] res(1)
    by simp
  note S = compute_alt_path_specD[OF spec]
  have "pfx1 \<noteq> None"
  proof
    assume "pfx1 = None"
    hence "(None, pfx2) = longest_disj_pfx p1 p2"
      using res(3)
      by simp
    hence "set p1 \<inter> set p2 = {}"
      by (rule disj_pfx_is_complete)
    thus False
      using res(2)
      by simp
  qed
  then obtain q1 where q1: "pfx1 = Some q1"
    by blast
  then obtain q2 where q2: "pfx2 = Some q2"
    using first_pfx_then_snd_pfx[of q1 pfx2 p1 p2] res(3)
    by auto
  have pfxs: "(Some q1, Some q2) = longest_disj_pfx p1 p2"
    using res(3) q1 q2
    by simp
  obtain p where p: "p1 = q1 @ p" "p2 = q2 @ p"
    by (rule common_suffix[OF spec pfxs])
  have "path (ugraph_abs G) (rev (drop (length q1) p1) @ rev q1 @ q2)"
    by (rule pfxs_path[OF pfxs S(11,12,13)])
  moreover have "match_blossom (matching_abs M) (rev (drop (length q1) p1)) (rev q1 @ q2)"
    by (rule common_pfxs_form_match_blossom'[OF pfxs p S(3,2,4,6,7,8,9,10)
                                                matching_invar_props(2)[OF assms(2)]])
  ultimately show ?thesis
    using res(4,5) q1 q2
    by simp
qed

lemma blossom_search_complete:
  assumes "graph_input G vs" "matching_invar G M"
          "\<exists>p. graph_augmenting_path (ugraph_abs G) (matching_abs M) p"
  shows "blossom_search G vs M \<noteq> None"
  using alternating_forest_search(2)[OF assms]
  by (auto simp: blossom_search_def split: option.splits prod.splits)

lemmas blossom_search = blossom_search_path blossom_search_blossom blossom_search_complete

end

end
```

---

## Phase 6: the executable algorithm on red-black trees (`Edmonds_Blossom_Example.thy`)

**Goal.** Global interpretations of all layers with red-black trees; `edmonds_blossom_correct_1`
(maximum cardinality of the result of `edmonds_blossom_run_impl G vs` for every `G vs` with
`graph_input_rbt G vs`) and `edmonds_blossom_correct_2`; the demonstration (`value` gives a
matching of three edges; `demo_max` proved); `export_code` succeeds.

**Recon.** (a) The parameter names of `Pair_Graph_Specs` as used in `DFS_Example` (`empty`,
`delete`, `lookup`, `insert`, `isin`, `t_set`, `sel`, `update`, `adjmap_inv`, `vset_empty`,
`vset_delete`, `vset_inv`). (b) `Map_axioms_as_needed`, `G.Pair_Graph_Specs_axioms`,
`Tree2.set_inorder`. (c) After each global interpretation, which constants of the shared part
are named by the first interpretation (`gm`); the later `defines` must not redefine them.
(d) `value` and `export_code` succeed only if every reachable locale constant has code
equations: add missing constants to the `defines` clauses (and `lemmas [code]` in the locale
if needed).

**Frozen statements.** `edmonds_blossom_correct_1/2` (modulo the folding of constants),
`demo_max`.

**One-shot theory** (copy verbatim into `Edmonds_Blossom_Executable/Edmonds_Blossom_Example.thy`):

```isabelle
theory Edmonds_Blossom_Example
  imports Edmonds_Blossom_Top_Loop Edmonds_Blossom_Subprocedures Alternating_Forest_Search
          Directed_Set_Graphs.Pair_Graph_RBT
begin

provenance ai

section \<open>The executable blossom algorithm on red-black trees\<close>

text \<open>Graphs, mate functions, parent maps and label maps are red-black trees. Vertices are
  natural numbers; a fresh vertex is one more than the largest vertex of a list.\<close>

subsection \<open>Fresh vertices and vertex lists\<close>

definition "fresh_nat (vs :: nat list) = Suc (foldr max vs 0)"

lemma foldr_max_ge: "x \<in> set vs \<Longrightarrow> x \<le> foldr max vs (a :: nat)"
  by (induction vs) auto

lemma fresh_nat: "fresh_nat vs \<notin> set vs"
  using foldr_max_ge[of _ vs 0]
  by (fastforce simp: fresh_nat_def)

lemma vset_to_list_rbt: "vset_inv N \<Longrightarrow> set (Tree2.inorder N) = Tree2.set_tree N"
  by simp

subsection \<open>The data structures\<close>

global_interpretation gm: Graph_Matching_Specs
  where empty = map_empty and delete = RBT_Map.delete and lookup = lookup and insert = vset_insert
    and isin = isin and t_set = t_set and sel = sel and update = update and adjmap_inv = adj_inv
    and vset_empty = vset_empty and vset_delete = vset_delete and vset_inv = vset_inv
    and mate_empty = Leaf and mate_update = update and mate_delete = RBT_Map.delete
    and mate_lookup = lookup and mate_invar = M.invar
    and vset_to_list = Tree2.inorder
  defines ugraph_abs_rbt = gm.ugraph_abs
    and graph_input_rbt = gm.graph_input
    and matching_invar_rbt = gm.matching_invar
    and matching_abs_rbt = gm.Mate.\<M>
    and augment_rbt = gm.Mate.augment_impl
    and neighbourhood_rbt = gm.Graph.neighbourhood
    and add_edge_rbt = gm.Graph.add_edge
    and from_list_rbt = gm.Graph.from_list
    and neighbour_list_rbt = gm.neighbour_list
    and adjacency_edges_rbt = gm.adjacency_edges
    and matching_edges_rbt = gm.matching_edges
    and mate_from_list_rbt = gm.mate_from_list
proof(rule Graph_Matching_Specs.intro)
  show "Pair_Graph_Specs map_empty RBT_Map.delete lookup vset_insert isin t_set sel update adj_inv
          vset_empty vset_delete vset_inv"
    using G.Pair_Graph_Specs_axioms
    by (simp add: RBT_Set.empty_def adj_inv_def map_empty_def)
  show "Map Leaf update RBT_Map.delete lookup M.invar"
    using Map_axioms_as_needed
    by (simp add: RBT_Set.empty_def)
  thus "matching_augmentation Leaf update RBT_Map.delete lookup M.invar"
    by (simp add: matching_augmentation_def Matching_Augmentation_Specs_def)
  show "Graph_Matching_Specs_axioms vset_inv t_set Tree2.inorder"
    by (rule Graph_Matching_Specs_axioms.intro) simp
qed

subsection \<open>The alternating forest search\<close>

global_interpretation alt_forest: Alternating_Forest_Search
  where empty = map_empty and delete = RBT_Map.delete and lookup = lookup and insert = vset_insert
    and isin = isin and t_set = t_set and sel = sel and update = update and adjmap_inv = adj_inv
    and vset_empty = vset_empty and vset_delete = vset_delete and vset_inv = vset_inv
    and mate_empty = Leaf and mate_update = update and mate_delete = RBT_Map.delete
    and mate_lookup = lookup and mate_invar = M.invar and vset_to_list = Tree2.inorder
    and parent_empty = Leaf and parent_update = update and parent_delete = RBT_Map.delete
    and parent_lookup = lookup and parent_invar = M.invar
    and label_empty = Leaf and label_update = update and label_delete = RBT_Map.delete
    and label_lookup = lookup and label_invar = M.invar
    and G = G and vs = vs and M = N
  for G vs N
  defines alt_forest_impl = alt_forest.Alternating_Forest_Search_impl
    and alt_forest_free_vertices = alt_forest.free_vertices
    and alt_forest_initial_labels = alt_forest.initial_labels
    and alt_forest_initial_state = alt_forest.initial_state
    and alt_forest_paths = alt_forest.alternating_paths
    and alt_forest_run_impl = alt_forest.Alternating_Forest_Search_run_impl
  using gm.Graph_Matching_Specs_axioms Map_axioms_as_needed
  by (simp add: Alternating_Forest_Search_def RBT_Set.empty_def)

lemma alt_forest_run_impl_correct:
  "\<lbrakk>graph_input_rbt G vs; matching_invar_rbt G N\<rbrakk>
   \<Longrightarrow> compute_alt_path_spec (ugraph_abs_rbt G) (matching_abs_rbt N) (alt_forest_run_impl G vs N)"
  "\<lbrakk>graph_input_rbt G vs; matching_invar_rbt G N;
    \<exists>p. graph_augmenting_path (ugraph_abs_rbt G) (matching_abs_rbt N) p\<rbrakk>
   \<Longrightarrow> alt_forest_run_impl G vs N \<noteq> None"
  using alt_forest.Alternating_Forest_Search_run_impl_correct[of G vs N]
  by (auto simp: alt_forest.Alternating_Forest_Search_axiom_def)

subsection \<open>Finding an augmenting path or a blossom\<close>

global_interpretation subprocedures: Edmonds_Blossom_Subprocedures
  where empty = map_empty and delete = RBT_Map.delete and lookup = lookup and insert = vset_insert
    and isin = isin and t_set = t_set and sel = sel and update = update and adjmap_inv = adj_inv
    and vset_empty = vset_empty and vset_delete = vset_delete and vset_inv = vset_inv
    and mate_empty = Leaf and mate_update = update and mate_delete = RBT_Map.delete
    and mate_lookup = lookup and mate_invar = M.invar and vset_to_list = Tree2.inorder
    and alternating_forest_search = alt_forest_run_impl
  defines blossom_search_rbt = subprocedures.blossom_search
  by (intro Edmonds_Blossom_Subprocedures.intro gm.Graph_Matching_Specs_axioms
            Edmonds_Blossom_Subprocedures_axioms.intro alt_forest_run_impl_correct)

subsection \<open>Searching for an augmenting path by shrinking blossoms\<close>

global_interpretation shrinking: Blossom_Shrinking_Search
  where empty = map_empty and delete = RBT_Map.delete and lookup = lookup and insert = vset_insert
    and isin = isin and t_set = t_set and sel = sel and update = update and adjmap_inv = adj_inv
    and vset_empty = vset_empty and vset_delete = vset_delete and vset_inv = vset_inv
    and mate_empty = Leaf and mate_update = update and mate_delete = RBT_Map.delete
    and mate_lookup = lookup and mate_invar = M.invar and vset_to_list = Tree2.inorder
    and G = G and vs = vs and M = N
    and blossom_search = blossom_search_rbt and fresh_vertex = fresh_nat
  for G vs N
  defines shrinking_impl = shrinking.Blossom_Shrinking_Search_impl
    and shrinking_initial_state = shrinking.initial_state
    and shrinking_augmenting_path = shrinking.augmenting_path
    and shrinking_run_impl = shrinking.Blossom_Shrinking_Search_run_impl
    and contract_vertices_rbt = shrinking.contract_vertices
    and contract_graph_rbt = shrinking.contract_graph
    and contract_matching_rbt = shrinking.contract_matching
    and cycle_neighbour_rbt = shrinking.cycle_neighbour
    and last_edge_matched_rbt = shrinking.last_edge_matched
    and cycle_path_rbt = shrinking.cycle_path
    and matched_to_cycle_rbt = shrinking.matched_to_cycle
    and replace_cycle_rbt = shrinking.replace_cycle_impl
    and lift_one_rbt = shrinking.lift_one
    and lift_path_rbt = shrinking.lift_path
  by (intro Blossom_Shrinking_Search.intro gm.Graph_Matching_Specs_axioms
            Blossom_Shrinking_Search_axioms.intro subprocedures.blossom_search fresh_nat)

lemma shrinking_run_impl_correct:
  "\<lbrakk>graph_input_rbt G vs; matching_invar_rbt G N; shrinking_run_impl G vs N = Some p\<rbrakk>
   \<Longrightarrow> graph_augmenting_path (ugraph_abs_rbt G) (matching_abs_rbt N) p"
  "\<lbrakk>graph_input_rbt G vs; matching_invar_rbt G N;
    \<exists>p. graph_augmenting_path (ugraph_abs_rbt G) (matching_abs_rbt N) p\<rbrakk>
   \<Longrightarrow> shrinking_run_impl G vs N \<noteq> None"
  using shrinking.Blossom_Shrinking_Search_run_impl_correct[of G vs N]
  by (auto simp: shrinking.Blossom_Shrinking_Search_axiom_def)

subsection \<open>The algorithm\<close>

global_interpretation edmonds_blossom: Edmonds_Blossom_Loop
  where empty = map_empty and delete = RBT_Map.delete and lookup = lookup and insert = vset_insert
    and isin = isin and t_set = t_set and sel = sel and update = update and adjmap_inv = adj_inv
    and vset_empty = vset_empty and vset_delete = vset_delete and vset_inv = vset_inv
    and mate_empty = Leaf and mate_update = update and mate_delete = RBT_Map.delete
    and mate_lookup = lookup and mate_invar = M.invar and vset_to_list = Tree2.inorder
    and G = G and vs = vs and augmenting_path_search = "shrinking_run_impl G vs"
  for G vs
  defines edmonds_blossom_impl = edmonds_blossom.Edmonds_Blossom_Loop_impl
    and edmonds_blossom_initial_state = edmonds_blossom.initial_state
    and edmonds_blossom_run_impl = edmonds_blossom.Edmonds_Blossom_Loop_run_impl
  by (intro Edmonds_Blossom_Loop.intro gm.Graph_Matching_Specs_axioms
            Edmonds_Blossom_Loop_axioms.intro shrinking_run_impl_correct)

subsection \<open>Correctness of the executable algorithm\<close>

context
  fixes G vs
  assumes graph_input: "graph_input_rbt G vs"
begin

interpretation edmonds_blossom_proofs: Edmonds_Blossom_Loop_thms
  where empty = map_empty and delete = RBT_Map.delete and lookup = lookup and insert = vset_insert
    and isin = isin and t_set = t_set and sel = sel and update = update and adjmap_inv = adj_inv
    and vset_empty = vset_empty and vset_delete = vset_delete and vset_inv = vset_inv
    and mate_empty = Leaf and mate_update = update and mate_delete = RBT_Map.delete
    and mate_lookup = lookup and mate_invar = M.invar and vset_to_list = Tree2.inorder
    and G = G and vs = vs and augmenting_path_search = "shrinking_run_impl G vs"
  by (intro Edmonds_Blossom_Loop_thms.intro edmonds_blossom.Edmonds_Blossom_Loop_axioms
            Edmonds_Blossom_Loop_thms_axioms.intro)
     (simp add: edmonds_blossom.Edmonds_Blossom_Loop_axiom_def graph_input)

lemmas edmonds_blossom_correct_1 =
  edmonds_blossom_proofs.Edmonds_Blossom_Loop_correct_1[
    folded edmonds_blossom_proofs.Edmonds_Blossom_Loop_impl_to_Edmonds_Blossom_Loop,
    folded edmonds_blossom_impl_def edmonds_blossom_initial_state_def,
    folded edmonds_blossom.Edmonds_Blossom_Loop_run_impl_def]

lemmas edmonds_blossom_correct_2 =
  edmonds_blossom_proofs.Edmonds_Blossom_Loop_correct_2[
    folded edmonds_blossom_proofs.Edmonds_Blossom_Loop_impl_to_Edmonds_Blossom_Loop,
    folded edmonds_blossom_impl_def edmonds_blossom_initial_state_def,
    folded edmonds_blossom.Edmonds_Blossom_Loop_run_impl_def]

end

subsection \<open>Demonstration\<close>

text \<open>Two triangles joined by an edge. A maximum matching has three edges; finding it requires
  shrinking a triangle.\<close>

definition "demo_edges =
  [(0::nat, 1::nat), (1, 0), (1, 2), (2, 1), (2, 0), (0, 2), (2, 3), (3, 2),
   (3, 4), (4, 3), (4, 5), (5, 4), (5, 3), (3, 5)]"

definition "demo_G = from_list_rbt demo_edges"

definition "demo_vs = [0, 1, 2, 3, 4, 5::nat]"

value "Tree2.inorder (current_matching (edmonds_blossom_run_impl demo_G demo_vs))"

lemma demo_input: "graph_input_rbt demo_G demo_vs"
  unfolding demo_G_def
  by (rule gm.from_list_graph_input) (auto simp: demo_edges_def demo_vs_def dVs_eq)

lemma demo_max:
  "max_card_matching (ugraph_abs_rbt demo_G)
     (matching_abs_rbt (current_matching (edmonds_blossom_run_impl demo_G demo_vs)))"
  by (rule edmonds_blossom_correct_1[OF demo_input])

export_code edmonds_blossom_run_impl in SML module_name Edmonds_Blossom

end
```

---
