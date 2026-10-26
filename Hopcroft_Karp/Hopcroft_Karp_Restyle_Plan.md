# Plan: restyling the Hopcroft–Karp theories in the DFS/BFS style (version 2)

Drafted 2026-10-11. Status: **R0–R6 DONE (2026-10-12); D2 removed (2026-10-12).**
- The user has decided RD1–RD5 (§1).
- RD12 is decided: integrate the read-only split first, as R0-0.
- D2 is removed. User (2026-10-12): "it should not import ddfs. split dfs". Way (i) was
  carried out: the DFS side is split from DDFS (see D2 below).
- **R0 is DONE (2026-10-11; user: "go ahead with R0").** The read-only split is
  integrated, with both base locales capitalised (`Pair_Graph_Specs_Read_Only`,
  `Pair_Graph_U_Specs_Read_Only`; user ruling). The full library build passes, and
  the R0 checks are recorded in `progress.md` ("## Restyle R0"). R1 waits for the
  user's go-ahead; the coder has not been started.

Version 1 of this plan (`Hopcroft_Karp_Restyle_Plan.v1.md`) followed version 1
of the style guide, which allowed the Hungarian method's conventions. **Version
2 of the guide makes DFS and BFS the ground truth** (user decision,
2026-10-11): `DFS.thy`, `DFS_Example.thy`, `BFS_2.thy`,
`BFS_Subprocedures.thy`, `BFS_Example.thy`. Other library theories count only
where they do not contradict these five. This version follows guide v2
(`/media/llms/Isabelle-Graph-Library-Style/Library_Style_Guide.md`, cited as
"guide §n").

What changed from version 1 of this plan:

| Topic | Version 1 (withdrawn) | Version 2 (guide v2) |
|---|---|---|
| Locale names | `hopcroft_karp_loop_spec` / `hopcroft_karp_loop` (Hungarian) | `Hopcroft_Karp_Loop` / `Hopcroft_Karp_Loop_thms` (DFS); likewise for the search loop |
| Sub-procedure contracts | assumptions of the proofs locale (Hungarian) | assumptions of the definitions locale, each clause with the input conditions it needs as premises (BFS, guide §3.6 rule 2) |
| Input conditions | locale assumptions in the proofs locale | one definition `<name>_axiom`, assumed by the proofs locale |
| Termination | `less_induct` with `[OF _ refl]` (Hungarian) | measure definitions, `<loop>_term_rel'`, `call_1_terminates`, `wf_induct_rule` (DFS) |
| Final results | wrapper definition and a `theorem` (Hungarian) | `lemma`s `<loop>_correct_<k>` about `<loop> initial_state`, `<loop>_impl_to_<loop>`, `<loop>_run`, `<loop>_run_impl` (DFS) |
| Interpretations | spread over the phase and example theories | composition only in the example theory, except the recorded deviations of §1 (RD3) |

---

## 0. What must not change, and how success is measured

**Invariant across the whole campaign.**
1. The final result keeps its mathematical content. For every input
   adjacency map and vertex list satisfying the input conditions, the result
   satisfies `mate_invar` and is a maximum-cardinality matching of the
   undirected graph of the input. Only names and the form of the input
   condition may change. Today the result is `hopcroft_karp_correct(1,2)`.
   After R5 it is `hopcroft_karp_correct_1` (maximum cardinality) and
   `hopcroft_karp_correct_2` (representation invariant), re-exported by
   `[folded …]` in the example theory. The premise becomes
   `hopcroft_karp_axiom_rbt G vs` (RD4).
2. The algorithm stays executable. `export_code` succeeds, and the
   demonstration's final mate map is still
   `[(0,3),(1,5),(2,4),(3,0),(4,2),(5,1)]`.
3. Project rules:
   - no `sorry`, `smt`, `metis` or `meson`;
   - no `{ … }` blocks;
   - ASCII on disk;
   - theory edits only through I/Q;
   - `apply` only in the DFS/BFS templates of §3 (RD1).
4. HK-D9 rules for the read-only specification are unchanged. Instantiate it
   with named `where` only, use one bridge lemma per constant, never refer to
   the sublocale qualifier, and never import the interim theory together with
   the split library.
5. The Micali–Vazirani theories in the copy (`Alt_BFS`, `Top_Loop`, `DDFS`,
   `DFS_Avoid`, `IDFS`, `*_Example`) are not edited. Exception, by user decision
   (2026-10-12, D2): the DFS/DDFS split. Text was moved without change of proofs.
   For porting to the MV checkout: `backups/integration/DFS_DDFS_split.patch`.

**Measured acceptance (after R5)**, with `style_stats.py` and
`locale_struct.py`, against the DFS and BFS columns (guide §1, §7):

| Metric | HK now | Target (guide §7) | Measured after R6 (2026-10-12) |
|---|---|---|---|
| Lemmas closed by a single `by` | 38.0% | ≥ 63% | 69.2% |
| Median proof length | 8 | ≤ 2 | 2 |
| Labelled `have`/`show`/`obtain` per lemma | 2.29 | ≤ 0.25 | 0.12 |
| `[OF …]` per lemma | 2.10 | ≤ 0.6 | **0.74** (missed: Alt_BFS_Bipartite 2.09, Subprocedures 1.00) |
| Named assumptions per lemma | 0.51 | 0 | 0.00 |
| `elim!:` + `intro!:` per lemma | 0.00 | ≥ 0.8 | **0.30** (missed: loop theories 0.37 / 0.56; the three other theories have no rule bundles) |
| `by` / `using` opening a line | 17% / 35% | ≥ 95% | 100% / 100% |
| `proof -` / `proof (` with a space | 41 / 52 | 0 / 0 | 0 / 0 |
| Lemmas carrying an attribute | 6.5% | ≥ 60% | **45.6%** (missed: Alt_BFS_Bipartite 4.3%, Subprocedures 12.0%) |
| Loops as `function (domintros)` over one record, with an `_impl` twin | 0 of 2 | 2 of 2 | 2 of 2 |
| `invar_*` families (`_props`, `_intro`, one per branch, `_holds`) | 0 | 1 (top loop) + 7 (search) | 1 + 7 |
| Named theorems declared and used | none | in both loop theories | 14 bundles, both loop theories |
| Termination (guide §7 item 10) | `less_induct`, inline arithmetic | DFS form in both loops | DFS form in both loops |
| Final correctness (guide §7 item 11) | arbitrary state with premises; proved again in the example | three layers, `_impl_to_<loop>`, run definitions, `[folded …]` re-export | as targeted |
| Layering (guide §7 item 12, `locale_struct.py`) | interpretations in four theories | as §2, with the deviations of RD3 only | as targeted (D1: concrete interpretations in Subprocedures) |
| `hk_` prefixes, one- to three-letter global abbreviations | 15 | 0 | 0 |

**Reasons for the three missed targets (R6).** All three are concentrated in the
two theories without loop machinery. `Alt_BFS_Bipartite` is mathematics about
copies walks: its `[OF]` count comes from `valid_alt_BFS_DAG_props[OF ...]`
instantiations, and its lemmas are intermediate results with no natural
`[simp]`/`[intro]` role. `Hopcroft_Karp_Subprocedures` instantiates the
alternating BFS and the incremental DFS at concrete red-black-tree operations
(`[OF phase_bfs_axiom bfs_state_valid]` patterns). The loop theories
(`Hopcroft_Karp_Top_Loop`, `Disjoint_Paths_Search`) meet every target except
`elim!:`/`intro!:` density. A further polishing pass on `Alt_BFS_Bipartite`
(48 `[OF]`, median proof 9) is possible but not planned; it needs the user's
decision.

Per theory (lemmas; single `by`; median; labels; `[OF]`; attributes):
Top_Loop 30, 66.7%, 2, 0.07, 0.30, 53.3%; Disjoint_Paths_Search 70, 77.1%, 2,
0.10, 0.37, 78.6%; Alt_BFS_Bipartite 23, 47.8%, 9, 0.57, 2.09, 4.3%;
Subprocedures 50, 64.0%, 2, 0.00, 1.00, 12.0%; Example 9, 100%, 1, 0.00, 0.11,
55.6%.

The target for labelled facts is BFS's 0.21, rounded. It is the hardest one,
because the bipartite layer (R3) is mathematics with several genuine
intermediate steps; the gate reports it per theory.

---

## 1. Decisions

**Decided by the user (2026-10-11, relayed by the style session).** The user's
words: "1. use apply, as long as it is like dfs, etc 2. capitalise 3. use p2
4. existential fine, 5. yes."

- **RD1. `apply` exactly where DFS/BFS use it, in their form, and nowhere
  else** (guide §5.6). The templates are listed in §3 under "Coder
  instructions". Everywhere else the coder's rule against `apply` stands.
- **RD2. Capitalise** (guide §2.2 rule 4).
  - **Capitals:** everything whose name starts with the algorithm's name,
    following `DFS`, `DFS_state`, `DFS_impl`, `DFS_call_1_conds`,
    `DFS_axioms`:
    - locales `Hopcroft_Karp_Input`, `Hopcroft_Karp_Loop`,
      `Disjoint_Paths_Search`;
    - records `Hopcroft_Karp_Loop_state`, `Disjoint_Paths_Search_state`;
    - loop constants `Hopcroft_Karp_Loop`, `Hopcroft_Karp_Loop_impl`;
    - branch constants `Hopcroft_Karp_Loop_call_1_conds`,
      `Hopcroft_Karp_Loop_upd1`, …;
    - `Hopcroft_Karp_Loop_term_rel'`, `Hopcroft_Karp_Loop_run`;
    - input bundles `Hopcroft_Karp_axiom`, `Disjoint_Paths_Search_axiom`;
    - lemmas named after them (`Hopcroft_Karp_Loop_cases`,
      `Hopcroft_Karp_Loop_correct_1`, `in_Hopcroft_Karp_Loop_term_rel'`,
      `Hopcroft_Karp_Loop_impl_to_Hopcroft_Karp_Loop`, …).
  - **Lower case:**
    - role suffixes (`Hopcroft_Karp_Loop_thms`, as `DFS_thms`);
    - unprefixed names (`initial_state`, `invar_matching`, `call_1_measure`,
      `ugraph_abs`);
    - interpretation names (`hopcroft_karp`, `hopcroft_karp_input_rbt`,
      `phase_search`, as `dfs` in DFS_Example);
    - the executable and implementation constants (`hopcroft_karp_impl`,
      `ugraph_abs_rbt`, `hopcroft_karp_axiom_rbt`, `disjoint_paths_search_rbt`,
      `hopcroft_karp_phase`, as `dfs_impl`, `next_frontier`).
- **RD3. P2** (the phase as the concrete implementation in
  `Hopcroft_Karp_Subprocedures.thy`), with the deviations D1–D4 below.
  - **Why the pure form needs MV edits.** In guide v2 the phase would be an
    algorithm whose definitions locale fixes the alternating BFS and the
    search, with contracts, and every global interpretation would be in the
    example theory. But:
    - the alternating BFS exists executably only as `Alt_BFS_Example`'s
      global interpretation `alt_bfs`;
    - its facts are stated in the MV locale `Alt_BFS.BFS`, which has four
      further sub-procedures;
    - facts HK adds to that locale are not inherited by `alt_bfs` (ζ-A), so
      a re-interpretation (today `hkbfs`) is needed;
    - the incremental DFS's contract is proved in the MV locale
      `IDFS_witness`, which carries an assumption about its input graph.
  - **What P2 does.** The top loop and the search loop follow guide v2
    completely. `Hopcroft_Karp_Subprocedures.thy` implements the top loop's
    `matching`, `augment` and `phase` and the search loop's `search_step`.
    - It proves lemmas named and stated exactly as those contract clauses,
      for all inputs (guide §3.6 rule 4).
    - It holds the interpretations those implementations need.
    - `Hopcroft_Karp_Example.thy` holds the composition, the `[folded …]`
      re-export and the demonstration.
  - **Not chosen: P1**, an abstract phase locale over a copies-graph builder.
    The builder would still be concrete, so P1 would only move the deviation
    down one level. It remains possible later without touching R1–R3.
- **RD4. Existential bipartition.** The input bundle contains
  `\<exists>X Y. bipartite ugraph_abs X Y`. The `phase` clauses have the bundle
  `Hopcroft_Karp_axiom` as a premise, so they hold for all inputs. The final
  lemmas have the premise `hopcroft_karp_axiom_rbt G vs`. The demonstration
  proves it with the witnesses `{0,1,2}` and `{3,4,5}`.
- **RD5. One shared input locale, `Hopcroft_Karp_Input`.**
  - **Why it is needed.** An `assumes` clause cannot refer to a
    `definition` of its own locale. The HK input conditions (seven
    conjuncts, plus the undirected graph that occurs in eight clauses) are
    too long to repeat inline.
  - **What it holds:** the input graph, the vertex list, `ugraph_abs` and
    the bundle `Hopcroft_Karp_axiom`. The contract clauses cite the bundle.
  - **Precedent:** BFS_Subprocedures' shared parent `Pair_Graph_Sepcs_Set2`.
  - **Names.**
    - `ugraph_abs` is the library's own name for this set
      (`Pair_Graph_U_Specs.ugraph_abs`; today `UG_of`).
    - The bundles are singular `…_axiom` (BFS form), because Isabelle
      generates `<locale>_axioms` itself for a locale that has a parent and
      its own `assumes`.

- **RD12. Integrate the read-only split first, as step R0-0** (user,
  2026-10-11; option (a) below, after RD11).

**Decided 2026-10-12:** D2 is removed by way (i), the split of the DFS side from DDFS (see D2).

**Settled by the guide or by the earlier review** (no decision needed):

- RD6. The record field is `current_matching` (`matching` is a constant of
  Basic_Matching). The phase's sources are `bfs_sources` (`sources` is a
  constant of Pair_Graph). Both are accepted in guide v2 §2.3.
- RD7. The search loop accumulates paths by prepending. The demonstration's
  first phase then prints `[[3,1],[4,0]]` instead of `[[4,0],[3,1]]`; the
  final matching is unchanged.
- RD8. `Hopcroft_Karp.thy` becomes `Alt_BFS_Bipartite.thy`, and its six
  context assumptions become one bundle (v1 RD4, unchanged).
- RD9. The matching operations stay parameters (guide §6.1, last paragraph),
  with the Hungarian method's parameter names `empty_matching`,
  `matching_invar`, `augment` and `matching_abstract`. The constants
  `mate_augment`, `mate_matching` and `mate_invar` keep their names. Whether
  to use the Hungarian instance's constants instead is still the user's
  earlier, separate question.
- RD10. **Capitalised (user ruling, 2026-10-11): `Pair_Graph_Specs_Read_Only`
  and `Pair_Graph_U_Specs_Read_Only`.**
  - The Graph ADT session's split used lower-case names. That session had
    ended, so R0-0 applied its verified patch and renamed both locales in the
    six patched files (20 + 4 occurrences).
  - The base locale is part of `Directed_Set_Graphs.Pair_Graph_Specs`, and
    `Pair_Graph_Specs = Map + Pair_Graph_Specs_Read_Only`, with unchanged
    parameter order: `insert isin t_set sel vset_empty vset_delete vset_inv
    lookup adjmap_inv`.
  - The renamed patch against dacfcfc is
    `Hopcroft_Karp/backups/integration/Graph_ADT_Split_capitalised.patch`
    (775 lines, md5 fed53843071eef91af9f8a8fd7a6e2fa). It reproduces the
    verified files byte for byte.
- RD11. Nothing is committed (the user decides). Snapshots go to
  `Hopcroft_Karp/backups/restyle-R<n>/` at every gate.
- **RD12 (decided: (a), integrate first). When to integrate the read-only split.**
  - **The patch.** The Graph ADT session's patch is ready:
    `/media/llms/Isabelle-Graph-Library-Graph-ADT/Graph_ADT_Split.patch`,
    md5 837a51f78dea8ce448a0c32f6980eb08. The instructions are in
    `Graph_ADT_Integration_for_HK.md` beside it.
    - It changes six library theories: `Pair_Graph_Specs`,
      `Pair_Graph_U_Specs`, `DDFS_Example`, `WBP_Matching_Exec`,
      `Use_Orlins_Algorithm/Instantiation` and `Kruskal_Greedy`.
    - The full library build passes with it.
  - **HK-D9 condition.** It applies the patch "after HK is verified", and
    the six HK gates are green.
  - **(a) Recommended: integrate as step R0-0, before R1.** The restyle is
    then written once, against the final library:
    - no interim theory and no `RO.c = G.c` bridges;
    - the top loop imports `Directed_Set_Graphs.Pair_Graph_Specs`;
    - one prefix (`G.`) for every read-only name at red–black trees (see
      the subsumption note in R4-1).
  - **(b) Integrate after R6.** Every new interpretation of the restyle
    must then be revisited for subsumption, and the bridges renamed.
  - **Either way:** the six patched files are not edited during the
    restyle (none is an HK theory), so the patch still applies cleanly.

**Recorded deviations from guide v2** (all under P2):
- D1. `Hopcroft_Karp_Subprocedures.thy` works at the concrete operations and
  contains interpretations (RD3).
- D2. **REMOVED 2026-10-12** (user: "it should not import ddfs. split dfs"). Way (i)
  below, carried out in the HK copy (MV theories; text moved, no proof changed):
  - new `Micali_Vazirani/Layered_Digraph.thy` (imports `Vwalk`, `Pair_Graph_Specs`):
    `dpath`, `dpath_bet`, `layered_dgraph` + lemmas, `Pair_Graph_Specs.layered_graph_input`
    + lemmas, moved from DDFS.thy; DDFS, IDFS and MV `Top_Loop` import it;
  - `IDFS.thy` imports `DFS_Avoid Layered_Digraph`; its DDFS bridge (`locale DDFS_layered`,
    `sublocale DDFS_layered \<subseteq> DDFS`) moved to the start of `DDFS_Interpretation.thy`;
  - new `Micali_Vazirani/IDFS_Example.thy` (imports `IDFS`, `Pair_Graph_RBT`): the RBT
    interpretation `idfs: DFS_avoid` (`avoid_impl_rbt`, `vset_of_list_rbt`, code equations),
    moved from `DDFS_Example`, which imports it. Interpretation subsumption: `idfs` now
    registers the shared `Pair_Graph_Specs` instance first, so the four `ddfs_diamond.Graph.*`
    defines of `DDFS_Example` were dropped (unused) and its diamond code equation folds
    `neighbourhood_idfs_def`, as the chain one already did; demo values unchanged;
  - HK: `Disjoint_Paths_Search` imports `Micali_Vazirani.Layered_Digraph`;
    `Hopcroft_Karp_Subprocedures` imports `Micali_Vazirani.IDFS_Example` (no `DDFS_Example`).
    No HK theory reaches DDFS any more (transitively).
  - Integration: `backups/integration/DFS_DDFS_split.patch` (applies cleanly to the MV
    checkout, `patch -p1 --dry-run`, 2026-10-12). At integration the predicates belong in
    the graph library.

  The analysis before the decision:
  - **What it needs from DDFS.** Only the two predicates `layered_dgraph`
    (DDFS.thy:252) and `layered_graph_input` (DDFS.thy:300, in
    `context Pair_Graph_Specs`). The search step's contract has
    `Graph.layered_graph_input G lev` as its premise. That premise is exactly
    the assumption of `IDFS_witness`, so the implementation can interpret
    `IDFS_witness` and reuse its theorems.
  - **Why not import IDFS instead** (the user's question). IDFS *implements*
    the search step, and an algorithm theory must not import its
    implementation (guide §3.6 rule 3). Importing IDFS would not avoid DDFS
    either:
    - IDFS.thy itself `imports DFS_Avoid DDFS`;
    - `IDFS_witness` assumes `Graph.layered_graph_input`;
    - IDFS.thy:513 ff. (`DDFS_layered`, `sublocale DDFS_layered \<subseteq> DDFS`)
      needs DDFS.
  - **DDFS is loaded in any case.** `Hopcroft_Karp_Subprocedures` imports
    `IDFS` and `DDFS_Example` (for `avoid_impl_rbt`, DDFS_Example.thy:313),
    so the session loads DDFS regardless. D2 concerns only which theory the
    *generic* search loop depends on.
  - **Ways to remove D2:**
    - **(i) Move the predicates (MV edits).** Move the two predicates into a
      small theory or into the graph library (e.g. next to `Vwalk`). Move
      `DDFS_layered` and its sublocale into `DDFS_Interpretation.thy`, which
      already imports both. Move `avoid_impl_rbt` into an IDFS example theory.
      This is not checked for feasibility, and needs the user's approval
      because it edits MV theories.
    - **(ii) No MV edits.** Restate the search step's premise without the
      predicate:
      - inline, as its three conditions (levels decrease along edges, finite
        vertex set, every vertex reaches level 0) together with
        `graph_inv`/`finite_graph`/`finite_vsets`, in each of the seven
        clauses;
      - or as a local copy of the definition in `Disjoint_Paths_Search`,
        with a one-line equivalence lemma in `Hopcroft_Karp_Subprocedures`.

      The cost is a duplicated definition (or long clauses) until
      integration.
  - Until the user decides, D2 stays as it is. At integration the
    predicates belong in the graph library.
- D3. The input conditions are in a shared parent locale (RD5).
- D4. `Alt_BFS_Bipartite.thy` adds facts to the MV locale `Alt_BFS.BFS` from
  outside, as today.

**Interpretation subsumption** (Graph ADT session, 2026-10-11). Isabelle
registers a locale instance only once. When two interpretations in scope
share the read-only operations (`insert isin t_set sel vset_empty vset_delete
vset_inv lookup adjmap_inv`), the read-only constants and facts (`digraph_abs`,
`neighbourhood`, `graph_inv`, `are_connected_absI`, …) exist only under the
prefix registered first. Under the other prefix they are undefined. Facts of
the first registration carry its `defines` rewrites. Within one proof, use
one prefix.

---

## 2. Theories and phases

**Session `ROOT` after R5 (P2):**

| Theory | Imports | Contains | Kind |
|---|---|---|---|
| `Pair_Graph_Specs_Read_Only` | (unchanged, interim) | read-only adjacency-map specification | specification |
| `Hopcroft_Karp_Top_Loop` | `Basic_Matching.Berge`, `Pair_Graph_Specs_Read_Only` | `Hopcroft_Karp_Input`, `Hopcroft_Karp_Loop`, `Hopcroft_Karp_Loop_thms` | algorithm |
| `Disjoint_Paths_Search` | `Directed_Set_Graphs.Pair_Graph_Specs`, `Data_Structures.Set2_Addons`, `Micali_Vazirani.Layered_Digraph` (D2 removed) | `Disjoint_Paths_Search`, `Disjoint_Paths_Search_thms` | algorithm |
| `Alt_BFS_Bipartite` | `Micali_Vazirani.Top_Loop`, `Basic_Matching.Berge` | facts in locale `Alt_BFS.BFS` | mathematics (D4) |
| `Hopcroft_Karp_Subprocedures` | `Hopcroft_Karp_Top_Loop`, `Disjoint_Paths_Search`, `Alt_BFS_Bipartite`, `Micali_Vazirani.Alt_BFS_Example`, `Micali_Vazirani.IDFS_Example`, `Basic_Matching.Matching_Augmentation_Executable` | implementations of `matching`, `augment`, `phase` (and of the search step) | implementation (D1) |
| `Hopcroft_Karp_Example` | `Hopcroft_Karp_Subprocedures` | code bridges, `global_interpretation hopcroft_karp: Hopcroft_Karp_Loop`, `[folded …]` re-export, demonstration | example |

Dependencies point from the implementation to the caller: the
`_Subprocedures` theory imports both loops; neither loop imports it (guide
§3.6 rule 3).

| Phase | Theory (new ← old) | Depends on | Kind of change | Size now → expected |
|---|---|---|---|---|
| R0 | — | — | recon, baseline, backups, name checks | — |
| R1 | `Hopcroft_Karp_Top_Loop` ← `HK_Top_Loop` | — | input locale, definitions locale with contracts, proofs locale, machinery, DFS termination, final lemmas | 321 → ~330 |
| R2 | `Disjoint_Paths_Search` (new; replaces the loop of `HK_Search`) | — | record, contract of the step, 7 invariant families, DFS termination, final lemmas | 196 → ~520 |
| R3 | `Alt_BFS_Bipartite` ← `Hopcroft_Karp` | — | names, assumption bundle, proofs | 587 → ~420 |
| R4 | `Hopcroft_Karp_Subprocedures` ← `HK_Phase` + `HK_Search` | R1, R2, R3 | implementations with contract lemmas; phase on the new search loop; proofs | 1010 → ~650 |
| R5 | `Hopcroft_Karp_Example` ← `HK_Example` | R4 | composition, re-export, demonstration | 163 → ~120 |
| R6 | — | all | measurement, close-out, coordination | — |

**Keeping the session green.**
- R1 patches `HK_Example` in the same gate (§R1-6).
- R2 adds its theory alongside `HK_Search`. `HK_Search` imports it and drops
  its two generic walk lemmas, so no fact name is declared twice.
- R3 patches `HK_Phase` by name substitution only.
- R4 replaces `HK_Phase` and `HK_Search`, and patches `HK_Example` by name
  substitution.
- R5 restyles `HK_Example` into `Hopcroft_Karp_Example`.

---

## 3. Gate protocol (all phases)

As in `Hopcroft_Karp_Plan.md` § Coder protocol: I/Q on port 8767, token `hk`,
through the copy's `mcp.py`; `USER_HOME=/media/llms/isabelle-home-hk`; other
instances are never touched. The REPL gate applies to search closers, and
sledgehammer runs in the REPL on a broken step. The coder runs Sonnet at high
effort.

**Coder instructions: `apply` (RD1).** `.claude/agents/coder.md:176` ("No
`apply` scripts") is not edited. For this campaign it gives way in exactly
the following templates, written as DFS/BFS write them, and nowhere else.
Anywhere else, a failing step is repaired by the order in item 2 below,
never by an `apply` script.

| Template | Ground-truth source | Form |
|---|---|---|
| Induction per branch (`<loop>_induct`) | `DFS_induct`, `BFS_induct` | `apply(rule <loop>.pinduct[OF assms(1)])`, `apply(rule assms(2)[simplified <loop>_call_<i>_conds_def <loop>_upd<i>_def …])`, `by (auto simp: Let_def split: …)` |
| Invariant preserved by the loop (`invar_<x>_holds`), and `ret1_holds` | `invar_seen_stack_holds` | inside `case IH: (1 state)`: `apply(rule <loop>_cases[where state = state])`, then `by (auto intro!: IH(2-) invar_holds_intros simp: <loop>_simps[OF IH(1)])` |
| Final lemmas (`<loop>_correct_<k>`) | `BFS_correct_2` | `apply(intro <loop>_correct_<k>_ret_1[where state = "<loop> initial_state"])`, then `by(auto intro: invar_holds_intros ret_holds_intros)` |
| Global interpretations in the example and implementation theories | `BFS_Example` | `apply unfold_locales`, then `by (auto simp add: <impl>.<contract lemma> …)` |
| The executable twin on the initial state (`<loop>_impl_to_<loop>`), if the single `by` of R1-5 fails | `DFS_impl_to_DFS` | the `apply(induction rule: <loop>.pinduct[OF that])`, `apply(subst <loop>.psimps)`, `apply(subst <loop>_impl.simps)`, `by(auto …)` sequence of DFS |

Anything beyond these templates (more `apply` steps, `apply` inside other
lemmas) is a protocol violation, and the gate check rejects it.

1. **Statements first.** The orchestrator writes the statements and candidate
   proofs into this plan before the gate. The coder pastes them, then repairs
   only failing steps. Statements change only with the orchestrator's
   approval, recorded as an amendment.
2. **Repair order for a failing step.** Each fallback is tried only after the
   one before it fails.
   - First, the same single call with more of the bundles
     (`elim!: call_cond_elims invar_props_elims`, `intro!: invar_props_intros`,
     `simp: <branch>_def Let_def`).
   - Then `force`/`fastforce`/`blast` with the same modifiers.
   - Then sledgehammer in the REPL; a `metis` or `smt` answer is translated
     into `auto`, `force` or `blast` with the facts it names.
   - Last, a short structured proof in the form of guide §5.2: one `have` per
     mathematical step, chained with `hence`/`moreover`/`ultimately`, earlier
     facts cited as cartouches, no labels for book-keeping.
3. **Layout** (guide §5.5).
   - `using` and `by` start their own line, indented two spaces.
   - Write `proof-` and `proof(…)`, with no space.
   - Long method calls are split with one modifier per line.
4. **Gate checks** (orchestrator):
   - PIDE reports 0 errors on every session theory;
   - the batch build exits with 0;
   - the `tmp/verify_thy.py` scan finds no `sorry`, `metis`, `smt`, `meson` or
     `{`-blocks; `apply` appears only in the templates of §3 (RD1);
   - the files are pure ASCII;
   - the statements match the plan;
   - `style_stats.py` and `locale_struct.py` are run on the gate's theories,
     with the figures recorded in `progress.md` under "## Restyle Gate R<n>";
   - the theories are snapshotted to `backups/restyle-R<n>/`;
   - the demonstration still yields the final mate map of §0.

---

## R0. Recon, baseline, backups (orchestrator)

0. *(RD12 (a), decided.)* Integrate the read-only split, following
   `Graph_ADT_Integration_for_HK.md` step by step. Specifically:
   - close the six patched theories in jEdit;
   - `git apply --check`, then `git apply`;
   - delete `Pair_Graph_Specs_Read_Only.thy` and its `ROOT` entry, and
     import `Directed_Set_Graphs.Pair_Graph_Specs` instead;
   - rename `RO.…` to `G.…` where subsumption requires it, and delete the
     trivial bridges;
   - rebuild in `isabelle-home-hk`. For a full library build use
     `isabelle build -D . -j 3` (never `-d . -a`) with
     `ISABELLE_TOOL_JAVA_OPTIONS="-Djava.awt.headless=true -Xms512m -Xmx16g -Xss16m"`
     in `isabelle-home-hk`'s `etc/settings`.

   The gate is the same as today's Gate 6: the session builds, the
   demonstration values are unchanged, and `export_code` succeeds. Snapshot
   to `backups/integration/` first. In the theory skeletons below, read
   `Pair_Graph_Specs_Read_Only` as `Directed_Set_Graphs.Pair_Graph_Specs`.
1. Snapshot the six HK theories and `ROOT` to `backups/restyle-R0/`.
2. Check that the session is green: batch build, and `value` of the
   demonstration.
3. Run `style_stats.py` (it must reproduce the HK column of `stats.txt`) and
   `locale_struct.py` on the HK directory.
4. Check in the REPL (`term`, `find_consts`, `thm`) that these names are free
   where they will be declared:
   - the record fields `current_matching`, `phases`, `roots`, `avoided`,
     `explored`, `paths`;
   - the locale names, and the auto-generated predicates `<locale>_axioms` of
     every new locale (RD5);
   - the global names of §A;
   - the fact names `matching`, `augment`, `phase` and `search_step` at the
     top level of `Hopcroft_Karp_Subprocedures`. These are the contract-lemma
     names of R4 (guide §3.6 rule 4). Where one is already taken by an
     imported theory, R4 uses `<name>_rbt` for it instead.
5. Determine three facts about the existing locales and record them:
   - the parameter order of `pair_graph_specs_read_only`: `vset_empty
     vset_delete vset_inv insert isin t_set sel lookup adjmap_inv`, as in
     today's `RO` interpretation;
   - the parameter order of `Set2` as `IDFS_witness` instantiates it;
   - whether `global_interpretation … for x y defines c = t` abstracts `c`
     over all `for` variables or only over those occurring in `t`. Write a
     two-line test in the REPL.
6. Check whether `Graph.layered_graph_input` (DDFS.thy, in a `context
   Pair_Graph_Specs`) is available in a locale with a `Graph: Pair_Graph_Specs`
   parent, once `Micali_Vazirani.DDFS` is imported.

---

## R1. `Hopcroft_Karp_Top_Loop.thy` (from `HK_Top_Loop.thy`)

Templates: DFS.thy for layout, machinery, termination and final lemmas;
BFS_2.thy for sub-procedure contracts in the definitions locale.

### R1-1. Header, augmentation lemmas, state, automation

```
theory Hopcroft_Karp_Top_Loop
  imports "Basic_Matching.Berge" Pair_Graph_Specs_Read_Only
begin

section \<open>Top Loop of the Hopcroft-Karp Algorithm\<close>

subsection \<open>Augmenting along vertex-disjoint augmenting paths\<close>

lemma edges_of_path_disjoint:
  "\<lbrakk>e \<in> set (edges_of_path q); set p \<inter> set q = {}\<rbrakk> \<Longrightarrow> e \<notin> set (edges_of_path p)"
  using edges_of_path_Vs[of p] edges_of_path_Vs[of q]
  by (fastforce simp: Vs_def dest!: in_edges_of_path_split)

lemma augmenting_path_disjoint_preserved:
  "\<lbrakk>matching M; graph_augmenting_path G M p; graph_augmenting_path G M q; set p \<inter> set q = {}\<rbrakk>
   \<Longrightarrow> graph_augmenting_path G (M \<oplus> set (edges_of_path p)) q"
```
*Proof outline:* a structured proof of at most 10 lines, in four steps.
1. The edges of `q` have the same membership in `M` and in
   `M' = M ⊕ set (edges_of_path p)`, by `edges_of_path_disjoint` and
   `in_symmetric_diff_iff`.
2. Hence `q` alternates with respect to `M'`, by `alt_list_cong_1` and
   `alt_list_cong_2`.
3. `Vs M' = {hd p, last p} ∪ Vs M`, by `rematch_atl_path_Vs_change` and
   `aug_paths_are_even`.
4. The ends of `q` lie in `set q`, which is disjoint from `set p`, so they are
   free in `M'`.

The source is today's `aug_path_disjoint_preserved`, which has 25 labelled
steps. `augment_all` and its lemmas are deleted (see `foldl_augment_card`).

```
subsection \<open>The program state\<close>

record 'matching Hopcroft_Karp_Loop_state =
  current_matching :: 'matching
  phases :: nat

subsection \<open>Setup for automation\<close>

named_theorems call_cond_elims
named_theorems call_cond_intros
named_theorems ret_holds_intros
named_theorems invar_props_intros
named_theorems invar_props_elims
named_theorems invar_holds_intros
named_theorems state_rel_intros
named_theorems state_rel_holds_intros
```
These are the eight names of DFS; `termination_intros` is declared before the
termination subsection, as in DFS. If a bundle stays unused, the R1 gate
removes its declaration.

### R1-2. The input (RD4, RD5)

```
subsection \<open>The input\<close>

locale Hopcroft_Karp_Input =
  Graph: pair_graph_specs_read_only
    where vset_empty = vset_empty and vset_delete = vset_delete and vset_inv = vset_inv
      and insert = insert and isin = isin and t_set = t_set and sel = sel
      and lookup = lookup and adjmap_inv = adjmap_inv
  for vset_empty vset_delete vset_inv insert isin t_set sel
      and lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option" and adjmap_inv +
  fixes G :: 'adjmap and vertex_list :: "'v list"
begin

definition "ugraph_abs = {{u, v} | u v. (u, v) \<in> Graph.digraph_abs G}"

definition "Hopcroft_Karp_axiom =
  (Graph.graph_inv G \<and> Graph.finite_graph G \<and> Graph.finite_vsets G \<and>
   (\<forall>u v. (u, v) \<in> Graph.digraph_abs G \<longrightarrow> (v, u) \<in> Graph.digraph_abs G) \<and>
   (\<forall>u. (u, u) \<notin> Graph.digraph_abs G) \<and>
   set vertex_list = dVs (Graph.digraph_abs G) \<and>
   (\<exists>X Y. bipartite ugraph_abs X Y))"

end
```
This is today's `hk_input` with the sides made existential, and `UG_of` under
the library's name. The `where` list follows HK-D9 (named instantiation only).
The exact parameter names come from R0-5.

### R1-3. The definitions locale: sub-procedures with contracts, the loop

```
subsection \<open>The loop\<close>

locale Hopcroft_Karp_Loop = Hopcroft_Karp_Input +
  fixes empty_matching :: 'matching
    and augment :: "'matching \<Rightarrow> 'v list \<Rightarrow> 'matching"
    and matching_invar :: "'matching \<Rightarrow> bool"
    and matching_abstract :: "'matching \<Rightarrow> 'v set set"
    and phase :: "'matching \<Rightarrow> 'v list list"
  assumes matching:
      "\<And>M. matching_invar M \<Longrightarrow> graph_matching ugraph_abs (matching_abstract M)"
      "matching_invar empty_matching"
      "matching_abstract empty_matching = {}"
    and augment:
      "\<And>M p. \<lbrakk>matching_invar M; graph_augmenting_path ugraph_abs (matching_abstract M) p\<rbrakk>
         \<Longrightarrow> matching_invar (augment M p)"
      "\<And>M p. \<lbrakk>matching_invar M; graph_augmenting_path ugraph_abs (matching_abstract M) p\<rbrakk>
         \<Longrightarrow> matching_abstract (augment M p) = matching_abstract M \<oplus> set (edges_of_path p)"
    and phase:
      "\<And>M p. \<lbrakk>Hopcroft_Karp_axiom; matching_invar M; p \<in> set (phase M)\<rbrakk>
         \<Longrightarrow> graph_augmenting_path ugraph_abs (matching_abstract M) p"
      "\<And>M. \<lbrakk>Hopcroft_Karp_axiom; matching_invar M\<rbrakk>
         \<Longrightarrow> sorted_wrt (\<lambda>p q. set p \<inter> set q = {}) (phase M)"
      "\<And>M. \<lbrakk>Hopcroft_Karp_axiom; matching_invar M;
             \<exists>p. graph_augmenting_path ugraph_abs (matching_abstract M) p\<rbrakk>
         \<Longrightarrow> phase M \<noteq> []"
begin
```
The `matching` and `augment` clauses need no input premise: the mate
function satisfies them for every graph (today's `mate_invarD`,
`mate_empty_props`, `mate_augmentation_correct`). The `phase` clauses carry
the input bundle, as BFS's clauses carry `Graph.graph_inv G` (guide §3.6
rule 2). The phase is correct only for valid inputs.

```
function (domintros) Hopcroft_Karp_Loop ::
  "'matching Hopcroft_Karp_Loop_state \<Rightarrow> 'matching Hopcroft_Karp_Loop_state" where
  "Hopcroft_Karp_Loop state =
     (if phase (current_matching state) \<noteq> [] then
        let paths = phase (current_matching state) in
        Hopcroft_Karp_Loop
          (state \<lparr>current_matching := foldl augment (current_matching state) paths,
                  phases := Suc (phases state)\<rparr>)
      else state)"
  by pat_completeness auto

partial_function (tailrec) Hopcroft_Karp_Loop_impl ::
  "'matching Hopcroft_Karp_Loop_state \<Rightarrow> 'matching Hopcroft_Karp_Loop_state" where
  (same body, with Hopcroft_Karp_Loop_impl in the recursive call)

lemma Hopcroft_Karp_Loop_impl_same:
  assumes "Hopcroft_Karp_Loop_dom state"
  shows "Hopcroft_Karp_Loop_impl state = Hopcroft_Karp_Loop state"
  by(induction rule: Hopcroft_Karp_Loop.pinduct[OF assms])
    (auto simp add: Hopcroft_Karp_Loop_impl.simps Hopcroft_Karp_Loop.psimps Let_def)

definition "initial_state = \<lparr>current_matching = empty_matching, phases = 0\<rparr>"

definition "Hopcroft_Karp_Loop_run = Hopcroft_Karp_Loop initial_state"

definition "Hopcroft_Karp_Loop_run_impl = Hopcroft_Karp_Loop_impl initial_state"

lemmas [code] = Hopcroft_Karp_Loop_impl.simps initial_state_def Hopcroft_Karp_Loop_run_impl_def

definition "Hopcroft_Karp_Loop_call_1_conds state = (phase (current_matching state) \<noteq> [])"

definition "Hopcroft_Karp_Loop_upd1 state =
  (let paths = phase (current_matching state) in
   state \<lparr>current_matching := foldl augment (current_matching state) paths,
          phases := Suc (phases state)\<rparr>)"

definition "Hopcroft_Karp_Loop_ret_1_conds state = (phase (current_matching state) = [])"

abbreviation "Hopcroft_Karp_Loop_ret1 state \<equiv> state"

definition "invar_matching state = matching_invar (current_matching state)"

definition "call_1_measure state = card ugraph_abs - card (matching_abstract (current_matching state))"

definition "Hopcroft_Karp_Loop_term_rel' = call_1_measure <*mlex*> {}"
```
Then come the branch lemmas and the four standard lemmas (guide §3.3),
candidate text:
```
lemma Hopcroft_Karp_Loop_call_1_conds[call_cond_elims]:
  "Hopcroft_Karp_Loop_call_1_conds state \<Longrightarrow> (phase (current_matching state) \<noteq> [] \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: Hopcroft_Karp_Loop_call_1_conds_def)

lemma Hopcroft_Karp_Loop_call_1_condsI[call_cond_intros]:
  "phase (current_matching state) \<noteq> [] \<Longrightarrow> Hopcroft_Karp_Loop_call_1_conds state"
  by (auto simp: Hopcroft_Karp_Loop_call_1_conds_def)

(the same two for ret_1, with "= []")

lemma Hopcroft_Karp_Loop_cases:
  assumes "Hopcroft_Karp_Loop_call_1_conds state \<Longrightarrow> P"
          "Hopcroft_Karp_Loop_ret_1_conds state \<Longrightarrow> P"
  shows "P"
  using assms
  by (auto simp: Hopcroft_Karp_Loop_call_1_conds_def Hopcroft_Karp_Loop_ret_1_conds_def)

lemma Hopcroft_Karp_Loop_simps:
  assumes "Hopcroft_Karp_Loop_dom state"
  shows "Hopcroft_Karp_Loop_call_1_conds state \<Longrightarrow>
           Hopcroft_Karp_Loop state = Hopcroft_Karp_Loop (Hopcroft_Karp_Loop_upd1 state)"
        "Hopcroft_Karp_Loop_ret_1_conds state \<Longrightarrow> Hopcroft_Karp_Loop state = Hopcroft_Karp_Loop_ret1 state"
  by (auto simp: Hopcroft_Karp_Loop.psimps[OF assms] Let_def Hopcroft_Karp_Loop_upd1_def
                 Hopcroft_Karp_Loop_call_1_conds_def Hopcroft_Karp_Loop_ret_1_conds_def)

lemma Hopcroft_Karp_Loop_induct:
  assumes "Hopcroft_Karp_Loop_dom state"
          "\<And>state. \<lbrakk>Hopcroft_Karp_Loop_dom state;
                     Hopcroft_Karp_Loop_call_1_conds state \<Longrightarrow> P (Hopcroft_Karp_Loop_upd1 state)\<rbrakk>
                    \<Longrightarrow> P state"
  shows "P state"
  apply(rule Hopcroft_Karp_Loop.pinduct[OF assms(1)])
  apply(rule assms(2)[simplified Hopcroft_Karp_Loop_call_1_conds_def Hopcroft_Karp_Loop_upd1_def])
  by (auto simp: Let_def)

lemma Hopcroft_Karp_Loop_domintros:
  assumes "Hopcroft_Karp_Loop_call_1_conds state \<Longrightarrow>
             Hopcroft_Karp_Loop_dom (Hopcroft_Karp_Loop_upd1 state)"
  shows "Hopcroft_Karp_Loop_dom state"
  using assms
  by (auto intro: Hopcroft_Karp_Loop.domintros
           simp: Hopcroft_Karp_Loop_call_1_conds_def Hopcroft_Karp_Loop_upd1_def Let_def)

end
```

### R1-4. The proofs locale: invariant, termination

```
locale Hopcroft_Karp_Loop_thms = Hopcroft_Karp_Loop +
  assumes Hopcroft_Karp_axiom: Hopcroft_Karp_axiom
begin

lemma ugraph_abs_graph_invar[simp]: "graph_invar ugraph_abs"
```
*Proof:* single `by`, from `Hopcroft_Karp_axiom` (no loops, hence
`dblton_graph`; finiteness by `Graph.finite_vertices`). The source is today's
`UG_graph_invar`.

```
lemmas phase_props[simp] = phase[OF Hopcroft_Karp_axiom]

lemma graph_matching_finite: "graph_matching ugraph_abs M \<Longrightarrow> finite M"
  using ugraph_abs_graph_invar finite_Vs_then_finite
  by (auto intro: finite_subset)

lemma foldl_augment_invar:
  "\<lbrakk>matching_invar M; \<forall>p \<in> set ps. graph_augmenting_path ugraph_abs (matching_abstract M) p;
    sorted_wrt (\<lambda>p q. set p \<inter> set q = {}) ps\<rbrakk>
   \<Longrightarrow> matching_invar (foldl augment M ps)"
  and foldl_augment_card:
  "\<lbrakk>(same premises)\<rbrakk>
   \<Longrightarrow> card (matching_abstract (foldl augment M ps)) = card (matching_abstract M) + length ps"
```
*Proof:* one `induction ps arbitrary: M`.
- `Nil` is `simp`.
- `Cons` closes with one `auto` using `augment`,
  `augmenting_path_disjoint_preserved`, `new_matching_plus_one` and
  `graph_matching_finite`.
- If the two conclusions are awkward in one induction, prove the conjunction
  and split it with `lemmas … = …[THEN conjunct1/2]`.

```
definition "invar_matching state = matching_invar (current_matching state)"   (already in R1-3)

lemma invar_matching_props[invar_props_elims]:
  "invar_matching state \<Longrightarrow> (matching_invar (current_matching state) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_matching_def)

lemma invar_matching_intro[invar_props_intros]:
  "matching_invar (current_matching state) \<Longrightarrow> invar_matching state"
  by (auto simp: invar_matching_def)

lemma invar_matching_holds_upd1[invar_holds_intros]:
  "\<lbrakk>Hopcroft_Karp_Loop_call_1_conds state; invar_matching state\<rbrakk>
   \<Longrightarrow> invar_matching (Hopcroft_Karp_Loop_upd1 state)"
  by (auto elim!: invar_props_elims
          intro!: invar_props_intros foldl_augment_invar
            simp: Hopcroft_Karp_Loop_upd1_def Let_def)

lemma invar_matching_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>Hopcroft_Karp_Loop_ret_1_conds state; invar_matching state\<rbrakk>
   \<Longrightarrow> invar_matching (Hopcroft_Karp_Loop_ret1 state)"
  by auto

lemma invar_matching_holds[invar_holds_intros]:
  assumes "Hopcroft_Karp_Loop_dom state" "invar_matching state"
  shows "invar_matching (Hopcroft_Karp_Loop state)"
  using assms(2)
proof(induction rule: Hopcroft_Karp_Loop_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    apply(rule Hopcroft_Karp_Loop_cases[where state = state])
    by (auto intro!: IH(2-) invar_holds_intros simp: Hopcroft_Karp_Loop_simps[OF IH(1)])
qed
```

```
subsection \<open>Termination\<close>

named_theorems termination_intros

lemma call_1_terminates[termination_intros]:
  "\<lbrakk>Hopcroft_Karp_Loop_call_1_conds state; invar_matching state\<rbrakk> \<Longrightarrow>
     (Hopcroft_Karp_Loop_upd1 state, state) \<in> call_1_measure <*mlex*> r"
```
*Proof:* this lemma holds the cardinality arithmetic (guide §4.1, *HK*).
- The card after the update is the card before plus `length (phase …)`
  (`foldl_augment_card`), and `length (phase …) \<ge> 1`.
- The card after is at most `card ugraph_abs`: the new matching is a subset
  of `ugraph_abs` (`matching(1)`, `foldl_augment_invar`), which is finite.
- Candidate, split one modifier per line:
  `by (fastforce elim!: invar_props_elims call_cond_elims simp: call_1_measure_def Hopcroft_Karp_Loop_upd1_def Let_def foldl_augment_card intro!: mlex_less diff_less_mono2 card_mono)`.
- Fallback: a structured proof with two `have`s (the card equation and the
  bound), then `mlex_less` and `linarith`.

```
lemma wf_term_rel: "wf Hopcroft_Karp_Loop_term_rel'"
  by (auto simp: wf_mlex Hopcroft_Karp_Loop_term_rel'_def)

lemma in_Hopcroft_Karp_Loop_term_rel'[termination_intros]:
  "\<lbrakk>Hopcroft_Karp_Loop_call_1_conds state; invar_matching state\<rbrakk> \<Longrightarrow>
     (Hopcroft_Karp_Loop_upd1 state, state) \<in> Hopcroft_Karp_Loop_term_rel'"
  by (simp add: Hopcroft_Karp_Loop_term_rel'_def termination_intros)

lemma Hopcroft_Karp_Loop_terminates[termination_intros]:
  assumes "invar_matching state"
  shows "Hopcroft_Karp_Loop_dom state"
  using wf_term_rel assms
proof(induction rule: wf_induct_rule)
  case (less x)
  show ?case
    by (rule Hopcroft_Karp_Loop_domintros)
       (auto intro!: invar_holds_intros less in_Hopcroft_Karp_Loop_term_rel')
qed
```
DFS's helpers `in_prod_relI`, `less_rel` and `wf_less_rel` are copied only if
one of these proofs uses them.

### R1-5. Final correctness (guide §4.2)

```
subsection \<open>Correctness\<close>

lemma Hopcroft_Karp_Loop_correct_ret_1:
  "\<lbrakk>invar_matching state; Hopcroft_Karp_Loop_ret_1_conds state\<rbrakk>
   \<Longrightarrow> max_card_matching ugraph_abs (matching_abstract (current_matching state))"
```
*Proof:* the Berge argument, in at most 6 lines (guide §5.2).
- `phase_props(3)` and the branch condition: there is no augmenting path.
- Berge's theorem (`Berge`, `max_card_matching_def`, `graph_matching_finite`).

The source is the `ccontr` block of today's `hk_loop_correct`.

```
lemma ret1_holds[ret_holds_intros]:
  assumes "Hopcroft_Karp_Loop_dom state"
  shows "Hopcroft_Karp_Loop_ret_1_conds (Hopcroft_Karp_Loop state)"
proof(induction rule: Hopcroft_Karp_Loop_induct[OF assms])
  case IH: (1 state)
  show ?case
    apply(rule Hopcroft_Karp_Loop_cases[where state = state])
    by (auto intro!: IH(2-) simp: Hopcroft_Karp_Loop_simps[OF IH(1)])
qed
```
There is one returning branch and no result field. The return update is the
identity, so DFS's companion `DFS_ret_<i>` would read `P \<Longrightarrow> P` and is
omitted.

```
subsection \<open>The initial state\<close>

lemma initial_state_props[invar_holds_intros, termination_intros]:
  "invar_matching initial_state" "Hopcroft_Karp_Loop_dom initial_state"
  by (auto intro!: invar_props_intros Hopcroft_Karp_Loop_terminates matching(2)
            simp: initial_state_def)

lemma Hopcroft_Karp_Loop_correct_1:
  "max_card_matching ugraph_abs (matching_abstract (current_matching (Hopcroft_Karp_Loop initial_state)))"
  apply(intro Hopcroft_Karp_Loop_correct_ret_1[where state = "Hopcroft_Karp_Loop initial_state"])
  by(auto intro: invar_holds_intros ret_holds_intros)

lemma Hopcroft_Karp_Loop_correct_2:
  "matching_invar (current_matching (Hopcroft_Karp_Loop initial_state))"
  by (auto intro: invar_holds_intros elim!: invar_props_elims)

lemma Hopcroft_Karp_Loop_impl_to_Hopcroft_Karp_Loop:
  "Hopcroft_Karp_Loop_impl initial_state = Hopcroft_Karp_Loop initial_state"
  by (auto intro!: Hopcroft_Karp_Loop_impl_same initial_state_props)

end
end
```
The phase bound (HK-M5)
will later be another final lemma, about `phases (Hopcroft_Karp_Loop
initial_state)`, with its own invariant family.

### R1-6. Consumer patch in `HK_Example.thy` (same gate; R5 restyles the rest)

1. Interpret the input locale at red–black trees:
   ```
   global_interpretation hopcroft_karp_input_rbt: Hopcroft_Karp_Input
     where vset_empty = Leaf and vset_delete = RBT.delete and vset_inv = vset_inv
       and insert = insert_rbt and isin = isin and t_set = Tree2.set_tree and sel = sel
       and lookup = lookup and adjmap_inv = M.invar
     for G vertex_list
     defines ugraph_abs_rbt = hopcroft_karp_input_rbt.ugraph_abs
       and hopcroft_karp_axiom_rbt = hopcroft_karp_input_rbt.Hopcroft_Karp_axiom
   ```
   Its parent `Graph` is subsumed by the earlier `RO` (or, after integration,
   by `G`), so read-only names keep their `RO.` (`G.`) prefix (§1, after D4).
   Add two bridge lemmas, `ugraph_abs_rbt G = UG_of G` and
   `hopcroft_karp_axiom_rbt G vs \<longleftrightarrow> (\<exists>X Y. hk_input G vs X Y)`, each a single
   `by` from the definitions and the `RO_*` bridges.
2. Replace `hk_exec` with:
   ```
   global_interpretation hk_exec: Hopcroft_Karp_Loop
     where (the where list of step 1) and G = G and vertex_list = vertex_list
       and empty_matching = Leaf and augment = mate_augment
       and matching_invar = "mate_invar (ugraph_abs_rbt G)" and matching_abstract = mate_matching
       and phase = "hk_phase (hk_edges G vertex_list) vertex_list"
     for G vertex_list
     defines hk_loop_impl = hk_exec.Hopcroft_Karp_Loop_impl
       and hk_initial_state = hk_exec.initial_state
     (proof: unfold_locales, then one auto per clause group with mate_invarD, mate_empty_props,
      mate_augmentation_correct, hk_phase_sound/_disjoint/_complete and the two bridges)
   ```
3. `hopcroft_karp Gin vs` becomes
   `current_matching (hk_loop_impl Gin vs (hk_initial_state …))`.
   `hopcroft_karp_correct` keeps its statement until R5. It is proved inside
   the existing context by `interpretation hk_proofs: Hopcroft_Karp_Loop_thms`
   and `hk_proofs.Hopcroft_Karp_Loop_correct_1/2[folded hk_proofs.Hopcroft_Karp_Loop_impl_to_Hopcroft_Karp_Loop]`.
4. `HK_Phase.thy` imports `Hopcroft_Karp_Top_Loop` in place of `HK_Top_Loop`.
   `ROOT` is updated.

**Gate R1 checks.** These are the checks of §3, plus guide §7 items 1–4 and
10–12 for this theory:
- `locale_struct.py` shows `Hopcroft_Karp_Input`, `Hopcroft_Karp_Loop` and
  `Hopcroft_Karp_Loop_thms`, and no interpretation in this theory;
- no `.psimps` or `.pinduct` appears outside `_simps`, `_induct`,
  `_domintros` and `_impl_same`.

---

## R2. `Disjoint_Paths_Search.thy` (new)

Templates: DFS.thy for the machinery; BFS_2.thy for the step as a parameter
whose contract is an assumption of the definitions locale.

### R2-1. State and definitions locale

```
theory Disjoint_Paths_Search
  imports Directed_Set_Graphs.Pair_Graph_Specs Data_Structures.Set2_Addons Micali_Vazirani.DDFS
begin

section \<open>Searching for Vertex-Disjoint Paths\<close>

lemma vwalk_bet_closed: (moved from HK_Search; single call by induct_vwalk_bet and auto)
lemma found_vwalk_bet:  (moved from HK_Search)

subsection \<open>The program state\<close>

record ('v, 'vset) Disjoint_Paths_Search_state =
  roots :: "'v list"
  avoided :: 'vset
  explored :: 'vset
  paths :: "'v list list"

subsection \<open>Setup for automation\<close>

(the eight named_theorems of R1-1)

subsection \<open>The loop\<close>

locale Disjoint_Paths_Search =
  Graph: Pair_Graph_Specs where lookup = lookup +
  set_ops: Set2 vset_empty vset_delete _ t_set vset_inv insert
  for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option" +
  fixes G :: 'adjmap
    and target :: "'v \<Rightarrow> bool"
    and blocked :: "'v list \<Rightarrow> 'vset"
    and initial_roots :: "'v list"
    and search_step :: "'vset \<Rightarrow> 'v \<Rightarrow> 'vset \<Rightarrow> 'v list option \<times> 'vset"
  assumes search_step:
    "\<And>lev avoid r vis res vis'. \<lbrakk>Graph.layered_graph_input G lev; vset_inv avoid; vset_inv vis;
        t_set avoid \<subseteq> dVs (Graph.digraph_abs G); t_set vis \<subseteq> dVs (Graph.digraph_abs G);
        r \<in> dVs (Graph.digraph_abs G); search_step avoid r vis = (res, vis')\<rbrakk>
       \<Longrightarrow> vset_inv vis'"
    "(same premises) \<Longrightarrow> t_set vis' \<subseteq> dVs (Graph.digraph_abs G)"
    "(same premises) \<Longrightarrow> t_set vis \<subseteq> t_set vis'"
    "(same premises with res = None; r \<notin> t_set avoid) \<Longrightarrow> r \<in> t_set vis'"
    "(same premises with res = None; v \<in> t_set vis' - t_set vis; (v, w) \<in> Graph.digraph_abs G)
       \<Longrightarrow> w \<in> t_set avoid \<union> t_set vis'"
    "(same premises; v \<in> t_set vis' - t_set vis) \<Longrightarrow> \<not> target v"
    "(same premises with res = Some p) \<Longrightarrow>
       Vwalk.vwalk (Graph.digraph_abs G) (rev p) \<and> p \<noteq> [] \<and> distinct p \<and> target (hd p) \<and>
       last p = r \<and> set p \<inter> (t_set avoid \<union> t_set vis') = {}"
begin
```
- **Inputs.** The inputs are `G`, `target`, `blocked` and `initial_roots`.
  Their conditions form `Disjoint_Paths_Search_axiom` below.
- **The step is the only sub-procedure.** Its contract carries the
  layering premise `Graph.layered_graph_input G lev`, for some `lev`. That
  premise is exactly the assumption of `IDFS_witness`, so the implementation
  in R4 can interpret that locale.
- **`blocked` is an input, not a sub-procedure.** In the example it is a
  `for` variable, so its properties cannot be contract clauses; they are
  input conditions (contrast v1).
- The seven clauses are today's `root_call` conclusions, written out with
  their premises, as in BFS.

```
function (domintros) Disjoint_Paths_Search ::
  "('v, 'vset) Disjoint_Paths_Search_state \<Rightarrow> ('v, 'vset) Disjoint_Paths_Search_state" where
  "Disjoint_Paths_Search state =
     (case roots state of
        [] \<Rightarrow> state
      | r # rs \<Rightarrow>
          (case search_step (avoided state) r (explored state) of
             (Some p, explored') \<Rightarrow>
               Disjoint_Paths_Search
                 (state \<lparr>roots := rs, avoided := union (avoided state) (blocked p),
                         explored := explored', paths := p # paths state\<rparr>)
           | (None, explored') \<Rightarrow>
               Disjoint_Paths_Search (state \<lparr>roots := rs, explored := explored'\<rparr>)))"
  by pat_completeness auto

partial_function (tailrec) Disjoint_Paths_Search_impl :: (same type and body)
lemma Disjoint_Paths_Search_impl_same: (as in R1-3)

definition "Disjoint_Paths_Search_axiom =
  ((\<exists>lev. Graph.layered_graph_input G lev) \<and>
   set initial_roots \<subseteq> dVs (Graph.digraph_abs G) \<and>
   (\<forall>p. vset_inv (blocked p) \<and> t_set (blocked p) \<subseteq> dVs (Graph.digraph_abs G)))"

definition "initial_state =
  \<lparr>roots = initial_roots, avoided = vset_empty, explored = vset_empty, paths = []\<rparr>"
definition "Disjoint_Paths_Search_run = Disjoint_Paths_Search initial_state"
definition "Disjoint_Paths_Search_run_impl = Disjoint_Paths_Search_impl initial_state"
lemmas [code] = Disjoint_Paths_Search_impl.simps initial_state_def Disjoint_Paths_Search_run_impl_def
```

### R2-2. Branches, measure, the four standard lemmas

| Branch | Condition | Update or result |
|---|---|---|
| `call_1` (a path is found) | `roots state = r # rs` and `search_step (avoided state) r (explored state) = (Some p, explored')` | `upd1`: drop the root, add `blocked p` to `avoided`, set `explored := explored'`, prepend `p` |
| `call_2` (no path) | `roots state = r # rs` and the step returns `(None, explored')` | `upd2`: drop the root, set `explored := explored'` |
| `ret_1` (no root left) | `roots state = []` | `ret1 = state` (abbreviation) |

```
definition "Disjoint_Paths_Search_upd1 state =
  (let (path, explored') = search_step (avoided state) (hd (roots state)) (explored state);
       p = the path
   in state \<lparr>roots := tl (roots state), avoided := union (avoided state) (blocked p),
             explored := explored', paths := p # paths state\<rparr>)"

definition "Disjoint_Paths_Search_upd2 state =
  state \<lparr>roots := tl (roots state),
         explored := snd (search_step (avoided state) (hd (roots state)) (explored state))\<rparr>"

lemma Disjoint_Paths_Search_call_1_conds[call_cond_elims]:
  "Disjoint_Paths_Search_call_1_conds state \<Longrightarrow>
   (\<And>r rs p explored'. \<lbrakk>roots state = r # rs;
       search_step (avoided state) r (explored state) = (Some p, explored')\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: Disjoint_Paths_Search_call_1_conds_def split: list.splits option.splits prod.splits)
```
- The `_conds` definitions are copies of the body with `True`/`False` at the
  leaves, as in DFS. `call_2` and `ret_1` get the same pair of lemmas.
- `Disjoint_Paths_Search_cases`, `_simps`, `_induct` and `_domintros` follow
  DFS's three- and four-branch versions, with
  `split: list.splits option.splits prod.splits`.

Measure, in the definitions locale (guide §4.1). Both recursive branches drop
the head of `roots`, so they decrease the same quantity:
```
definition "call_1_measure state = length (roots state)"
definition "Disjoint_Paths_Search_term_rel' = call_1_measure <*mlex*> {}"
```

### R2-3. Invariants (definitions in the definitions locale)

```
definition "invar_1 state = (vset_inv (avoided state) \<and> vset_inv (explored state))"

definition "invar_within_graph state =
  (t_set (avoided state) \<subseteq> dVs (Graph.digraph_abs G) \<and> t_set (explored state) \<subseteq> dVs (Graph.digraph_abs G) \<and>
   set (roots state) \<subseteq> dVs (Graph.digraph_abs G))"

definition "invar_roots state = (set (roots state) \<subseteq> set initial_roots)"

definition "invar_paths_sound state =
  (\<forall>p \<in> set (paths state).
     Vwalk.vwalk (Graph.digraph_abs G) (rev p) \<and> p \<noteq> [] \<and> distinct p \<and> target (hd p) \<and>
     last p \<in> set initial_roots)"

definition "invar_blocked_avoided state =
  (\<forall>p \<in> set (paths state). t_set (blocked p) \<subseteq> t_set (avoided state))"

definition "invar_paths_disjoint state =
  sorted_wrt (\<lambda>q p. set q \<inter> t_set (blocked p) = {}) (paths state)"

definition "invar_explored_closed state =
  (paths state = [] \<longrightarrow>
     t_set (avoided state) = {} \<and>
     set initial_roots \<subseteq> set (roots state) \<union> t_set (explored state) \<and>
     (\<forall>v \<in> t_set (explored state). \<not> target v) \<and>
     (\<forall>v w. v \<in> t_set (explored state) \<longrightarrow> (v, w) \<in> Graph.digraph_abs G \<longrightarrow> w \<in> t_set (explored state)))"
```
How these map to the current development:
- `invar_1` and `invar_within_graph` replace `search_pre`.
- `invar_paths_sound` and `invar_paths_disjoint` are the two conjuncts of
  `disjoint_search_correct`.
- `invar_explored_closed` replaces `none_closed_reach` and
  `disjoint_search_nonempty`. It is stronger: completeness now holds for
  every root, not only the first.
- The `_props` form of `invar_explored_closed` takes `paths state = []` as a
  second premise and has flat conclusions. If `elim!` handles that premise
  badly, it is declared plain `elim`, as DFS declares
  `invar_visited_through_seen_props`.

### R2-4. Proofs locale

```
locale Disjoint_Paths_Search_thms = Disjoint_Paths_Search +
  assumes Disjoint_Paths_Search_axiom: Disjoint_Paths_Search_axiom
begin

context
  includes set_ops.automation2 and Graph.adjmap.automation and Graph.vset.set.automation
begin

lemma Disjoint_Paths_Search_axiom_props[simp, intro]:
  "Graph.layered_graph_input G (SOME lev. Graph.layered_graph_input G lev)"
  "set initial_roots \<subseteq> dVs (Graph.digraph_abs G)"
  "vset_inv (blocked p)" "t_set (blocked p) \<subseteq> dVs (Graph.digraph_abs G)"
  using Disjoint_Paths_Search_axiom
  by (auto simp: Disjoint_Paths_Search_axiom_def intro: someI_ex)
```
The `SOME` form lets the contract clauses be used with `simp`/`intro` without
naming a witness. If it is awkward, use `obtain lev where …` once in each
lemma that needs it.

**Family lemmas.** There are 7 invariants. Each gets `_props`, `_intro`,
`_holds_upd1`, `_holds_upd2`, `_holds_ret_1` and `_holds`: 42 lemmas, in the
form of guide §4.

| Invariant | Needs (for `upd1`, `upd2`) | Facts used |
|---|---|---|
| `invar_1` | `invar_within_graph` | `search_step(1)`, `set_ops.invar_union` |
| `invar_within_graph` | `invar_1` | `search_step(2)`, `set_ops.set_union` |
| `invar_roots` | — | `set (tl xs) \<subseteq> set xs` |
| `invar_paths_sound` | `invar_1`, `invar_within_graph`, `invar_roots` | `search_step(7)` |
| `invar_blocked_avoided` | `invar_1` | `set_ops.set_union` |
| `invar_paths_disjoint` | `invar_1`, `invar_within_graph`, `invar_blocked_avoided` | `search_step(7)`: the new path misses `avoided`, which contains every earlier `blocked q` |
| `invar_explored_closed` | `invar_1`, `invar_within_graph` | `upd1` vacuous (`paths \<noteq> []`); `upd2` by `search_step(1–6)` with `avoided = {}` |

Candidate for each branch lemma:
```
  by (auto elim!: call_cond_elims invar_props_elims intro!: invar_props_intros
            dest!: search_step
            simp: Disjoint_Paths_Search_upd1_def Let_def)
```
- **Exception: `invar_explored_closed_holds_upd2`.** This is the one
  mathematical case. Write a structured proof of at most 12 lines, with one
  step each for the root, the closure of the old explored set, the closure of
  the newly explored vertices, and "no target".
- Every `_holds` lemma is the three-line induction of R1-4, with
  `Disjoint_Paths_Search_cases`.

**Termination** (DFS form; no invariant needed, so `_terminates` has no
premise):
```
subsection \<open>Termination\<close>
named_theorems termination_intros

lemma call_1_terminates[termination_intros]:
  "Disjoint_Paths_Search_call_1_conds state \<Longrightarrow>
     (Disjoint_Paths_Search_upd1 state, state) \<in> call_1_measure <*mlex*> r"
  by (auto elim!: call_cond_elims intro!: mlex_less
            simp: call_1_measure_def Disjoint_Paths_Search_upd1_def)

lemma call_2_terminates[termination_intros]:
  "Disjoint_Paths_Search_call_2_conds state \<Longrightarrow>
     (Disjoint_Paths_Search_upd2 state, state) \<in> call_1_measure <*mlex*> r"
  (same proof with upd2)

lemma wf_term_rel: "wf Disjoint_Paths_Search_term_rel'"
  by (auto simp: wf_mlex Disjoint_Paths_Search_term_rel'_def)

lemma in_Disjoint_Paths_Search_term_rel'[termination_intros]:
  "Disjoint_Paths_Search_call_1_conds state \<Longrightarrow>
     (Disjoint_Paths_Search_upd1 state, state) \<in> Disjoint_Paths_Search_term_rel'"
  "Disjoint_Paths_Search_call_2_conds state \<Longrightarrow>
     (Disjoint_Paths_Search_upd2 state, state) \<in> Disjoint_Paths_Search_term_rel'"
  by (simp add: Disjoint_Paths_Search_term_rel'_def termination_intros)+

lemma Disjoint_Paths_Search_terminates[termination_intros]:
  "Disjoint_Paths_Search_dom state"
  using wf_term_rel
proof(induction rule: wf_induct_rule)
  case (less state)
  show ?case
    by (rule Disjoint_Paths_Search_domintros) (auto intro!: less in_Disjoint_Paths_Search_term_rel')
qed
```
Both branches decrease the same measure, so no "unchanged" lemma
(`call_2_measure_1`) is needed.

### R2-5. Final correctness (guide §4.2)

Layer 1, one lemma per property, in BFS naming:
```
lemma Disjoint_Paths_Search_correct_1_ret_1:
  "\<lbrakk>invar_paths_sound state; Disjoint_Paths_Search_ret_1_conds state; p \<in> set (paths state)\<rbrakk>
   \<Longrightarrow> Vwalk.vwalk (Graph.digraph_abs G) (rev p) \<and> p \<noteq> [] \<and> distinct p \<and> target (hd p) \<and>
       last p \<in> set initial_roots"
  by (auto elim!: invar_props_elims)

lemma Disjoint_Paths_Search_correct_2_ret_1:
  "\<lbrakk>invar_paths_disjoint state; Disjoint_Paths_Search_ret_1_conds state\<rbrakk>
   \<Longrightarrow> sorted_wrt (\<lambda>q p. set q \<inter> t_set (blocked p) = {}) (paths state)"
  by (auto elim!: invar_props_elims)

lemma Disjoint_Paths_Search_correct_3_ret_1:
  "\<lbrakk>invar_explored_closed state; Disjoint_Paths_Search_ret_1_conds state;
    r \<in> set initial_roots; Vwalk.vwalk_bet (Graph.digraph_abs G) r q z; target z\<rbrakk>
   \<Longrightarrow> paths state \<noteq> []"
  by (auto elim!: call_cond_elims invar_props_elims dest: vwalk_bet_closed)
```
Layer 2, `ret1_holds[ret_holds_intros]`: the three-line induction (R1-5).
Then `initial_state_props[invar_holds_intros, termination_intros]`, with the
seven invariants and `Disjoint_Paths_Search_dom initial_state`.

Layer 3, about `Disjoint_Paths_Search initial_state`, with no premise, two
lines each as in R1-5:
- `Disjoint_Paths_Search_correct_1`: every path is a walk to a target, from
  an initial root.
- `Disjoint_Paths_Search_correct_2`: the paths are pairwise disjoint from the
  blocked sets of the paths found before them.
- `Disjoint_Paths_Search_correct_3`: if a root reaches a target, a path is
  found.

The executable twin:
`Disjoint_Paths_Search_impl_to_Disjoint_Paths_Search: "Disjoint_Paths_Search_impl initial_state = Disjoint_Paths_Search initial_state"`.

From this gate on, `HK_Search` imports `Disjoint_Paths_Search` and loses its
copies of `vwalk_bet_closed` and `found_vwalk_bet`.

**Gate R2 checks.** These are the checks of §3, plus guide §7 items 1–4, 10
and 11, and item 12 (`locale_struct.py`: two locales; no interpretation; the
imports of R2-1).

---

## R3. `Alt_BFS_Bipartite.thy` (from `Hopcroft_Karp.thy`)

This is unchanged from v1 except for one alignment: the bundle's undirected
graph is a fixed variable `UG` here. It is instantiated with `ugraph_abs` in R4.
- **Theory name and header.** Rename the theory and update `ROOT` and the
  import of `HK_Phase`. Use subsections:
  - *Walk lemmas*;
  - *Edges of the copies graph*;
  - *Walks of the copies graph under the BFS axiom*;
  - *The bipartite matching instance*;
  - *Augmenting paths and walks of the copies graph*.
- **`BFS_axiom_hk` is deleted.** Its uses become the cartouche
  `\<open>BFS_axiom\<close>`.
- **Assumption bundle**, in locale `BFS`, before the axiom context:
  ```
  definition "bipartite_matching_input UG M X Y =
    (graph_invar UG \<and> M \<subseteq> UG \<and>
     Graph.digraph_abs matching = {(u, v). {u, v} \<in> M} \<and>
     Graph.digraph_abs unmatching = {(u, v). {u, v} \<in> UG - M} \<and>
     t_set srcs = Vs UG - Vs M \<and> bipartite UG X Y)"
  ```
  - The instance context becomes
    `context fixes UG M X Y assumes "bipartite_matching_input UG M X Y"`.
  - The bundle is unpacked once into
    `bipartite_matching_input_props[simp]` (six facts, by `auto simp: …_def`).
- **Renames** (§A):
  - `G_char` → `G_eq_undirected_edges`;
  - `vwalk_G_path` and `path_vwalk_G` → one lemma, `vwalk_G_iff_path`;
  - `aug_path_*` → `augmenting_path_*`;
  - `copies_walk_side` → `copies_walk_label_side`.

Proof targets, lemma by lemma:

| Lemma | Now (lines / labels) | Target |
|---|---|---|
| `vwalk_bet_level_distinct` | 35 / 6 | ≤ 8 lines: `induction rule: induct_vwalk_bet`, `auto` with `less_le_trans`, no `consider` |
| `alt_list_edges_of_vwalk_path` / `_path_vwalk` | 20 / 3, 30 / 6 | one `by (induction p arbitrary: … rule: edges_of_path.induct) (auto simp: alt_list_step alt_list_empty)` each |
| `copies_dag_vtx_dVs` | 14 / 1 | `by (force simp: dVs_eq copies_dag_def)` |
| `copies_walk_alt_walk` | 55 / 10 | keep the induction; one case per edge kind, ≤ 6 lines each, chained with `hence` |
| `copies_lev_zero` | 40 / 9 | ≤ 12 lines |
| `copies_walk_from_odd`, `VisO_copies_dVs` | 20 / 5, 25 / 8 | ≤ 8 lines each |
| `G_eq_undirected_edges`, `dVs_G_subset_Vs`, `vwalk_G_iff_path`, `alt_walk_alt_path`, `alt_path_imp_alt_list` | 4–25 each | single `by`, or `induction` + `auto` |
| `augmenting_path_alt_walk` | 23 / 11 | ≤ 6 lines |
| `copies_walk_label_side` | 35 / 8 | keep the induction; each edge kind by `bipartite_edgeD` in one call |
| `copies_walk_distinct_vtx` | 33 / 10 | ≤ 12 lines; the choice of side stays as one mathematical step |
| `copies_walk_augmenting` | 36 / 16 | ≤ 10 lines |
| `augmenting_path_copies_start`, `augmenting_path_iff_free_odd_copy` | 18 / 5, 26 / 6 | ≤ 6 lines each |

**Consumer patch.** `HK_Phase` changes its import. Lemma names change by
substitution. The positional fact lists become `[OF bfs_axiom <bundle fact>
st_valid' …]`, with a one-line `have` of the bundle.

---

## R4. `Hopcroft_Karp_Subprocedures.thy` (from `HK_Phase.thy`; `HK_Search` removed)

The implementation layer under P2 (RD3). Every lemma that discharges a
contract has the name and statement of that contract clause (guide §3.6
rule 4), stated at the concrete operations and for all inputs.

### R4-1. Layout

1. *Data structures at red–black trees.* This is the D1 deviation.
   - **Read-only names and subsumption** (§1, after D4).
     - `hopcroft_karp_input_rbt`'s parent `Graph` is the same read-only
       instance as `RO`, so only one of the two prefixes carries the
       read-only names.
     - *Before integration (RD12 (b)):* `RO` and its five bridges stay
       unchanged (HK-D9). `RO` is registered first, and every read-only name
       is written `RO.…`, never `hopcroft_karp_input_rbt.Graph.…`.
     - *After integration (RD12 (a)):* `G: Pair_Graph_Specs` from
       `Alt_BFS_Example` is registered first. `RO` and the bridges are
       deleted, and every read-only name is written `G.…`.
   - `global_interpretation hopcroft_karp_input_rbt: Hopcroft_Karp_Input`
     moves here from R1-6, with `ugraph_abs_rbt` and `hopcroft_karp_axiom_rbt`.
     It contributes only these two definitions.
   - The `mate` interpretation and its `lemmas` are unchanged. Its
     constants keep their names (RD9).
   - The re-interpretation of the alternating BFS is renamed `hkbfs` →
     `phase_bfs`, with its text block kept.
2. *The matching operations meet the top loop's contract.* Three lemmas named
   `matching`, `augment`, as the contract clauses, each a single `by` from
   `mate_invarD`, `mate_empty_props` and `mate_augmentation_correct`.
   `mate_matching_iff` and `mate_Vs_iff` become `by (auto …)` proofs and
   conditional `[simp]` rules.
3. *The search step meets the search loop's contract.*
   - `definition "IDFS_stack0_rbt avoid vis p = …"` (was `hk_stack0`) and
     `definition "IDFS_impl_rbt CG P avoid p vis = …"` (was `hk_idfs`).
   - In
     `context fixes CG lev assumes "idfs.Graph.layered_graph_input CG lev"`:
     an `interpretation idfs_witness: IDFS_witness` (today's `W`), recorded
     under D1.
   - Lemma `search_step`: the seven clauses of R2-1 for
     `\<lambda>avoid r vis. IDFS_impl_rbt CG P avoid [r] vis`. The proof uses one
     `note` with the `IDFS_*` theorems, then one `by` per conclusion. The
     source is today's `root_call` (30 lines, 14 labels).
4. *The executable search loop.*
   ```
   global_interpretation phase_search: Disjoint_Paths_Search
     where (the Set2 and graph operations of today's W interpretation)
       and G = CG and target = P and blocked = blk and initial_roots = rs
       and search_step = "\<lambda>avoid r vis. IDFS_impl_rbt CG P avoid [r] vis"
     for CG P blk rs
     defines disjoint_paths_search_rbt = phase_search.Disjoint_Paths_Search_run_impl
     apply unfold_locales
     by (auto simp add: search_step)
   ```
   This is the BFS_Example form. It sits here rather than in the example
   theory because the phase's definition calls it (D1).
5. *Executable builders and the phase* (global, renamed per §A):
   - `adjacency_edges`, `matched_edges`, `unmatched_edges`, `free_vertices`,
     `free_vertex_set`, `copies_edges`, `copy_level`, `phase_roots` and
     `blocked_copies`;
   - `hopcroft_karp_phase G vs m`, whose body is today's `hk_phase` with
     spelled-out `let` names. The search is called as
     `paths (disjoint_paths_search_rbt copies_graph (\<lambda>w. level w = 0) blk rs)`.
6. *Input lemmas.* Global, with plain `\<lbrakk>hopcroft_karp_axiom_rbt G vs\<rbrakk> \<Longrightarrow> …`
   statements, ≤ 4 lines each:
   - `adjacency_edges_set`
   - `ugraph_abs_rbt_edge_iff`
   - `Vs_ugraph_abs_rbt`
   - `hopcroft_karp_axiom_rbtE[elim]`, which unpacks the bundle with flat
     premises and obtains `X`, `Y`.
7. *The phase for a fixed matching.* Today's
   `context fixes m assumes mi fne`.
   - It becomes `context fixes G vs m assumes "hopcroft_karp_axiom_rbt G vs"
     "mate_invar (ugraph_abs_rbt G) m" "free_vertices vs m \<noteq> []"`.
   - The nine one-letter abbreviations become spelled-out local
     abbreviations: `edge_list`, `matching_graph`, `non_matching_graph`,
     `bfs_sources`, `bfs_state`, `bfs_dag`, `copies_edge_list`,
     `copies_graph`, `level`.
   - Then the lemmas of R4-2, and an
     `interpretation phase_search_proofs: Disjoint_Paths_Search_thms` of the
     executable search at this instance (D1). Its axiom is proved from
     `copies_graph_layered`, `copy_roots_in_graph` and `blocked_copies_props`.
8. *The phase meets the top loop's contract.* Lemma `phase`: the three
   clauses of R1-3 with `phase = hopcroft_karp_phase (adjacency_edges G vs) vs`,
   premises as in the contract.
   - The case `free_vertices vs m = []` is `simp`.
   - Otherwise the clause is the lemma of item 7.

### R4-2. Lemmas of the phase context: renames and targets

| Now | New | Target |
|---|---|---|
| `M_sub` | `mate_matching_subset` | single `by` |
| `Mt_abs`, `Ut_abs` (25 lines each) | `matching_graph_abs`, `non_matching_graph_abs` | single `by (auto simp: matched_edges_def G.from_list_correct adjacency_edges_set ugraph_abs_rbt_edge_iff …)` |
| `S_props`, `S_free` | `bfs_sources_props[simp]` | ≤ 3 lines; the `foldr insert_rbt` fact becomes a global one-line lemma `set_tree_foldr_insert_rbt` |
| `bfs_axiom` (55 lines) | `phase_bfs_axiom` | split into `[simp]` facts (finite neighbourhoods of `from_list` graphs; sources inside the non-matching graph; sources non-empty; the two graphs disjoint), then `by (auto simp: phase_bfs.BFS_axiom_def)` |
| `st_eq`, `st_valid`, `st_valid'` | `bfs_state_eq`, `bfs_state_valid_impl`, `bfs_state_valid` | single `by` each |
| `T_sub`, `T_graph_inv`, `isin_T` | `bfs_dag_subset`, `bfs_dag_graph_inv`, `isin_bfs_dag` | ≤ 4 lines each |
| `cl_mem`, `CG_abs` (65 lines) | `copies_edge_list_mem`, `copies_graph_abs` | ≤ 10 lines |
| `CG_level`, `CG_layered` | `copies_graph_level`, `copies_graph_layered` | ≤ 4 lines each |
| `roots_props`, `roots_dVs`, `roots_nonempty` | `copy_roots_free_odd`, `copy_roots_in_graph`, `copy_roots_nonempty` | ≤ 6 lines each |
| `dVs_CG`, `blk_props` | `dVs_copies_graph`, `blocked_copies_props` | ≤ 6 lines |
| `phase_unfold`, `DS_facts` | `hopcroft_karp_phase_unfold`; `DS_facts` deleted (replaced by `phase_search_proofs.Disjoint_Paths_Search_correct_1/2/3`) | single `by` |
| `phase_sound_aux`, `phase_disjoint_aux`, `phase_complete_aux` (28, 32, 42 lines) | `phase_paths_augmenting`, `phase_paths_disjoint`, `phase_paths_nonempty` | ≤ 10 lines each, with the bundle fact of R3 |
| `vset_of_list_rbt_props`, `fold_min_mem`, `layered_dgraph_cong` | unchanged names | single `by`; `layered_dgraph_cong` ≤ 8 lines |

`HK_Phase.thy` and `HK_Search.thy` are removed from `ROOT` (snapshots in
`backups/restyle-R4/`). `HK_Example` gets the name substitutions of §A.

**Gate R4 checks.** These are the checks of §3, plus:
- the demonstration's first phase is `[[3,1],[4,0]]` (RD7) and the final mate
  map is unchanged;
- `locale_struct.py` shows interpretations only in this theory and in the
  example, matching the D1 list exactly.

---

## R5. `Hopcroft_Karp_Example.thy` (from `HK_Example.thy`)

Layout per `BFS_Example`, plus the concrete correctness of guide §3.6 rule 7.

1. *Code equations.* The bridges are kept (`nb_rbt`, `add_edge_rbt`,
   `from_list_rbt`, `add_edge_idfs`, `from_list_idfs`, `[code_unfold]`), with
   single-`by` proofs.
2. *Composition* (guide §3.6 rule 5). The implementations are interpreted in
   R4; the top loop is interpreted here:
   ```
   global_interpretation hopcroft_karp: Hopcroft_Karp_Loop
     where (the where list of hopcroft_karp_input_rbt) and G = G and vertex_list = vertex_list
       and empty_matching = Leaf and augment = mate_augment
       and matching_invar = "mate_invar (ugraph_abs_rbt G)" and matching_abstract = mate_matching
       and phase = "hopcroft_karp_phase (adjacency_edges G vertex_list) vertex_list"
     for G vertex_list
     defines hopcroft_karp_impl = hopcroft_karp.Hopcroft_Karp_Loop_impl
       and hopcroft_karp_initial_state = hopcroft_karp.initial_state
       and hopcroft_karp_run_impl = hopcroft_karp.Hopcroft_Karp_Loop_run_impl
     apply unfold_locales
     by (auto simp add: matching augment phase)
   ```
   `matching`, `augment` and `phase` are the contract lemmas of R4.
3. *Concrete correctness* (guide §3.6 rule 7):
   ```
   context
     fixes G vertex_list
     assumes "hopcroft_karp_axiom_rbt G vertex_list"
   begin
   interpretation hopcroft_karp_proofs: Hopcroft_Karp_Loop_thms
     where (the where list of item 2)
     (proof: unfold_locales, citing the global interpretation's facts and the assumption)
   lemmas hopcroft_karp_correct_1 =
       hopcroft_karp_proofs.Hopcroft_Karp_Loop_correct_1[folded
         hopcroft_karp_proofs.Hopcroft_Karp_Loop_impl_to_Hopcroft_Karp_Loop
         hopcroft_karp_impl_def hopcroft_karp_initial_state_def]
     and hopcroft_karp_correct_2 = (the same for _correct_2)
   end
   ```
   After the context, the two facts carry the premise
   `hopcroft_karp_axiom_rbt G vertex_list`. They state the two conclusions
   of today's `hopcroft_karp_correct` (§0.1).
   - Check with `thm` that the folded form prints with `hopcroft_karp_impl`
     and `hopcroft_karp_initial_state`, or with `hopcroft_karp_run_impl` if
     that is folded too.
   - If no fold order prints the intended statement, ask the orchestrator;
     do not add a proof.
4. *Demonstration.* The `demo_*` data and `value` commands are kept.
   - `demo_input` proves `hopcroft_karp_axiom_rbt demo_G demo_vs`, giving
     the witnesses `{0,1,2}` and `{3,4,5}` (RD4). `demo_bip` becomes ≤ 4
     lines.
   - `demo_max` is `hopcroft_karp_correct_1[OF demo_input]`.
   - `export_code hopcroft_karp_run_impl in SML module_name Hopcroft_Karp`.

**Gate R5 checks.** These are the checks of §3, plus:
- the re-exported statements match §0.1;
- `export_code` succeeds;
- the demonstration values are as in R4;
- `locale_struct.py` shows the example theory's interpretations as BFS_Example's
  plus rule 7.

---

## R6. Close-out

1. Run `style_stats.py` and `locale_struct.py` on the five restyled theories.
   Put the table of §0 with the measured column into this plan and into
   `progress.md`. Any target that is missed is listed with the reason.
2. Update `Hopcroft_Karp_Plan.md` (status, theory renames) and the memory
   file `hopcroft-karp-project-copy.md`.
3. Coordination:
   - The read-only split was integrated at R0-0 (RD12 (a)). Confirm that the
     interim theory and the `RO.c = G.c` bridges are gone.
   - Record for integration that `layered_dgraph` and `layered_graph_input`
     (D2) belong in the graph library.
4. Remove the editor backup files `Hopcroft_Karp/*.thy~`.
5. If the user chose P1 under RD3, P1 becomes a follow-up phase R7:
   - an abstract `Hopcroft_Karp_Phase.thy`;
   - the builder in `Hopcroft_Karp_Subprocedures.thy`;
   - the composition moves to the example theory.

---

## A. Rename table

**Theories.**

| Now | New |
|---|---|
| `HK_Top_Loop` | `Hopcroft_Karp_Top_Loop` |
| `HK_Search` | removed (loop → `Disjoint_Paths_Search`; step contract → `Hopcroft_Karp_Subprocedures`) |
| `Hopcroft_Karp` | `Alt_BFS_Bipartite` |
| `HK_Phase` | `Hopcroft_Karp_Subprocedures` |
| `HK_Example` | `Hopcroft_Karp_Example` |

**Locales, records, interpretations.**

| Now | New |
|---|---|
| — | `Hopcroft_Karp_Input` (input, `ugraph_abs`, `Hopcroft_Karp_axiom`) |
| `hk_loop_defs` / `hk_loop_spec` | `Hopcroft_Karp_Loop` / `Hopcroft_Karp_Loop_thms` |
| — (bare matching) | `record Hopcroft_Karp_Loop_state` (`current_matching`, `phases`) |
| `disjoint_search_gen` (6-argument `fun`) | `Disjoint_Paths_Search` / `Disjoint_Paths_Search_thms`, `record Disjoint_Paths_Search_state` |
| `hkbfs` | `phase_bfs` |
| `W` | `idfs_witness` (local, D1) |
| — | `phase_search` (global), `phase_search_proofs` (local, D1), `hopcroft_karp_input_rbt` |
| `hk_exec` / `hk` | `hopcroft_karp` / `hopcroft_karp_proofs` |
| context `fixes UG M X Y assumes UG_inv M_sub Mabs Uabs srcs_free bip` | context `assumes "bipartite_matching_input UG M X Y"` |

**Constants.**

| Now | New |
|---|---|
| `hk_loop`, `hk_loop_impl` | `Hopcroft_Karp_Loop`, `Hopcroft_Karp_Loop_impl`; plus `Hopcroft_Karp_Loop_run`, `_run_impl` |
| `augment_list`, `augment_all` | removed (`foldl augment` in the loop body) |
| `matching_abs` | `matching_abstract` (+ `empty_matching`) |
| `hk_input` | `Hopcroft_Karp_axiom` (locale), `hopcroft_karp_axiom_rbt` (instance), with `\<exists>X Y` |
| `UG_of` | `ugraph_abs` (locale), `ugraph_abs_rbt` (instance) |
| `search_pre` | `invar_1`, `invar_within_graph` (+ the premises of the `search_step` contract) |
| `hk_edges` | `adjacency_edges` |
| `match_list`, `unmatch_list` | `matched_edges`, `unmatched_edges` |
| `free_list` | `free_vertices` |
| `hk_srcs` | `free_vertex_set` |
| `copies_list` | `copies_edges` |
| `hk_level` | `copy_level` |
| `hk_roots` | `phase_roots` |
| `hk_blk` | `blocked_copies` |
| `hk_stack0`, `hk_idfs` | `IDFS_stack0_rbt`, `IDFS_impl_rbt` |
| `hk_phase` | `hopcroft_karp_phase` |
| `hk_loop_exec`, `hk_augment_list`, `hopcroft_karp` | `hopcroft_karp_impl`, removed, `hopcroft_karp_run_impl` |
| `es Mt Ut S st T cl CG lv` | `edge_list matching_graph non_matching_graph bfs_sources bfs_state bfs_dag copies_edge_list copies_graph level` (context-local) |

**Lemmas.**

| Now | New |
|---|---|
| `edge_of_disjoint_path`, `aug_path_disjoint_preserved` | `edges_of_path_disjoint`, `augmenting_path_disjoint_preserved` |
| `augment_list_correct`, `augment_all_correct` | `foldl_augment_invar`, `foldl_augment_card` |
| `finite_abs`, `card_abs_le` | `graph_matching_finite`; the bound is inside `call_1_terminates` |
| `hk_loop_dom_aux`, `hk_loop_dom` | `call_1_terminates`, `in_Hopcroft_Karp_Loop_term_rel'`, `Hopcroft_Karp_Loop_terminates` |
| `hk_loop_invar` | `invar_matching_holds` |
| `hk_loop_final` | `ret1_holds` + `Hopcroft_Karp_Loop_correct_ret_1` |
| `hk_loop_impl_same` | `Hopcroft_Karp_Loop_impl_same`, `Hopcroft_Karp_Loop_impl_to_Hopcroft_Karp_Loop` |
| `hk_loop_correct`, `hk_loop_impl_correct` | `Hopcroft_Karp_Loop_correct_1/2` |
| `hopcroft_karp_correct` | `hopcroft_karp_correct_1/2` (`[folded …]` re-export) |
| `root_call` | `search_step` (contract lemma of the implementation) |
| `disjoint_search_correct` | `Disjoint_Paths_Search_correct_1/2_ret_1`, `Disjoint_Paths_Search_correct_1/2` |
| `none_closed_reach`, `disjoint_search_nonempty` | `invar_explored_closed_*`, `Disjoint_Paths_Search_correct_3_ret_1`, `Disjoint_Paths_Search_correct_3` |
| `BFS_axiom_hk` | removed (cartouche) |
| `G_char`, `dVs_G_Vs`, `vwalk_G_path` + `path_vwalk_G`, `alt_path_alt_list` | `G_eq_undirected_edges`, `dVs_G_subset_Vs`, `vwalk_G_iff_path`, `alt_path_imp_alt_list` |
| `aug_path_alt_walk`, `aug_path_copies_start`, `aug_path_iff_free_odd_copy`, `BFS_aug_path_iff` | `augmenting_path_*`, `BFS_augmenting_path_iff` |
| `copies_walk_side` | `copies_walk_label_side` |
| `inp_parts`, `hk_edges_set`, `UG_edge_iff`, `Vs_UG`, `UG_graph_invar` | `hopcroft_karp_axiom_rbtE`, `adjacency_edges_set`, `ugraph_abs_rbt_edge_iff`, `Vs_ugraph_abs_rbt`, `ugraph_abs_graph_invar` |
| `hk_phase_sound/_disjoint/_complete` | `phase` (contract lemma, three clauses) |
| `hk_idfs_eq` | `IDFS_impl_rbt_eq` |
| ζ-5 lemmas | see R4-2 |
