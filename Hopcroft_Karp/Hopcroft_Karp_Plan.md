# Plan: Hopcroft–Karp on the Micali–Vazirani pipeline (phased, with one-shot proofs)

> **STATUS (2026-10-12): RESTYLE R0–R6 COMPLETE** (Hopcroft_Karp_Restyle_Plan.md;
> every gate orchestrator-verified: PIDE 0 errors, batch build
> `isabelle build -d . Hopcroft_Karp` exit 0, no sorry/metis/smt/meson, ASCII).
> The development now follows the DFS/BFS template. Theory renames:
> `HK_Top_Loop` → `Hopcroft_Karp_Top_Loop`; `HK_Search` → `Disjoint_Paths_Search`
> (loop) + `Hopcroft_Karp_Subprocedures` (step contract); `Hopcroft_Karp` →
> `Alt_BFS_Bipartite`; `HK_Phase` → `Hopcroft_Karp_Subprocedures`; `HK_Example` →
> `Hopcroft_Karp_Example`. The final results are `hopcroft_karp_correct_1`
> (maximum cardinality) and `hopcroft_karp_correct_2` (`mate_invar`) of
> `hopcroft_karp_run_impl G vs`, under `hopcroft_karp_axiom_rbt G vs`. The read-only
> split (HK-D9) is integrated (R0; `Pair_Graph_Specs_Read_Only`). The names used
> in the phase sections below are the pre-restyle names (rename table: restyle
> plan, appendix A). D2 removed (2026-10-12, user: "split dfs"): the incremental DFS is
> split from DDFS (`Micali_Vazirani/Layered_Digraph.thy`, `IDFS_Example.thy`); no HK theory
> imports DDFS; MV patch `backups/integration/DFS_DDFS_split.patch`. Not done: HK-M5,
> commit (user decision).

> **STATUS (2026-10-11): ALL SIX GATES GREEN** (each orchestrator-verified:
> PIDE 0 errors, statements identical to this plan or approved amendments
> ζ-A/η-A, no sorry/metis/smt, ASCII, batch build exit 0). HK-M1 … HK-M4 are
> complete: `hopcroft_karp_correct` proves that the executable `hopcroft_karp`
> returns a maximum-cardinality matching for every input satisfying
> `hk_input`; the demo runs and is proved maximal. Not done: HK-M5 (phase
> bound), integration of the read-only split (HK-D9), commit (user decision).
> Lessons from Gates 1–2 for the remaining one-shots: `foo[OF a b c]` where
> two premises are higher-order may fail with "multiple unifiers" — use
> `by (rule foo[OF a]) (fact b, fact c)`; `presburger` fails when its facts
> were simp-normalised into list form — state a local arithmetic helper.
> Builds on `Top_Loop.thy` M1 (`valid_DAG_layered`, 402 lines,
> batch-green; copied uncommitted from the Micali–Vazirani checkout). All
> Hopcroft–Karp work happens in this copy,
> `/media/llms/Isabelle-Graph-Library-Hopcroft-Karp`; the directory
> `/media/llms/Isabelle-Graph-Library-Micali-Vazirani` is reserved for
> Micali–Vazirani.

**Why Hopcroft–Karp first.** The MV top loop (Top_Loop_Plan.md M2/M3) needs
DDFS, blossom/petal bookkeeping and the matching-instantiation layer all at
once. Hopcroft–Karp (HK) is the bipartite special case of exactly the same
pipeline — alt-BFS → layered copies DAG → DFS for disjoint shortest augmenting
paths → augment → repeat — with one simplification: **no blossoms**, so a
plain incremental DFS (`DFS_Avoid`/`IDFS`, already proven and executable)
replaces DDFS, and every walk in the copies DAG projects to a *simple* path.
HK therefore exercises the whole top-loop architecture (matching instance,
path read-off, phases, termination, Berge) on the reusable MV components, and
everything generic it produces (β-lemmas below) is directly reusable by MV.

**Roadmap.**

- **HK-M1 — the oracle (Gates 1–2, `Hopcroft_Karp.thy`).** For a bipartite
  graph `UG`, a set of edges `M ⊆ UG`, and the alt-BFS digraph pair built
  from them (`matching` = both orientations of `M`, `unmatching` = both
  orientations of `UG - M`, `srcs` = free vertices):
  - *soundness* — every walk of the copies DAG from `Vtx Odd t` (`t` free) to
    a level-0 copy reads off (reversed, projected by `vtx`) a
    `graph_augmenting_path UG M`, of length `altd_G Odd t` (shortest);
  - *completeness* — if any augmenting path exists, some free `t` has
    `Vtx Odd t` in the copies DAG (hence, by `copies_reach_zero`, a walk to
    level 0 that any complete DFS will find);
  - capstone `aug_path_iff_free_odd_copy` + corollaries at `BFS initial_state`.
- **HK-M2 — the abstract loop (Gate 3, `HK_Top_Loop.thy`).** Augmenting
  along vertex-disjoint augmenting paths; the loop over phases, specified
  only by the phase contract (sound, pairwise disjoint, non-empty when an
  augmenting path exists); termination and maximum cardinality via Berge.
- **HK-M3 — the search (Gate 4, `HK_Search.thy`).** Repeated incremental
  DFS (`IDFS_impl`) with a growing avoid set and a carried-over visited set,
  on any layered graph: soundness, disjointness, non-emptiness.
- **HK-M4 — the concrete phase and the executable algorithm (Gates 5–6,
  `HK_Phase.thy`, `HK_Example.thy`).** Alt-BFS → copies graph → search →
  read-off on red–black trees; proof of the phase contract; interpretation
  of the abstract loop; `hopcroft_karp_correct`; code export and demo.
- HK-M5 (optional, research, not planned in detail): the `O(√|V|)` phase bound.

**Project copy (user decision, 2026-10-11; set up 2026-10-11).**
- *Location:* `/media/llms/Isabelle-Graph-Library-Hopcroft-Karp`, a worktree of
  the Micali–Vazirani repository on branch `hopcroft-karp`, created from HEAD
  `dacfcfc` (user decision: interim Micali–Vazirani changes are NOT
  committed). Copied over as uncommitted working files, identical to the
  Micali–Vazirani working tree on 2026-10-11:
  - `Micali_Vazirani/Alt_BFS.thy` — ASCII version (HEAD's literal UTF-8 fails
    the batch build);
  - `Set_Graphs/Graph_Algorithms/DFS_Time.thy` — completed version (HEAD's is
    truncated);
  - `Set_Graphs/Graph_Algorithms/DFS_Skeleton.thy`, `DFS_DirCycle.thy`,
    `DFS_DirCycle_Example.thy` — listed in the library's ROOT but never
    committed (`DFS_Avoid` imports `DFS_Skeleton`);
  - `Micali_Vazirani/Top_Loop.thy` (md5 67155b2c…) and `Micali_Vazirani/ROOT`
    (its `Top_Loop` entry). Option 1 was chosen (2026-10-11): Hopcroft–Karp
    keeps the copies DAG of `Top_Loop.thy`, the bridge that turns alt-BFS
    output into the layered graph required by the incremental DFS.
- *New in the copy:* `Hopcroft_Karp/ROOT` (session `Hopcroft_Karp`), the line
  `Hopcroft_Karp` in `ROOTS`, this plan, and `mcp.py` (the I/Q bridge script;
  token from `IQ_AUTH_TOKEN`, default `hk`; port from `IQ_MCP_BRIDGE_PORT`).
  Progress log: `Hopcroft_Karp/progress.md`. Nothing Hopcroft–Karp-related is
  written into the Micali–Vazirani directory.
- *Separate Isabelle home:* every `isabelle build` / `isabelle jedit` for
  Hopcroft–Karp runs with `USER_HOME=/media/llms/isabelle-home-hk`
  (`ISABELLE_HOME_USER=/media/llms/isabelle-home-hk/.isabelle/Isabelle2025-2`).
  It was seeded with copies of the shared home's `etc/` (registered
  components; preferences with `editor_document_session = "Hopcroft_Karp"`),
  `jedit/` (`iq_plugin.jar`), `ROOTS`, `mash_state`, and a one-time COPY of
  `heaps/` (to avoid rebuilding the ancestors; nothing is shared or linked).
  Both directories define the same session names and their sources will
  diverge, so the shared `~/.isabelle` heaps must never be written from here.
- *Disk:* the root file system is 99% full (about 7 GB free on 2026-10-11).
  Check `df -h /media/llms` before large builds.
- *Own jEdit/I/Q instance:* launched from the copy with
  `USER_HOME=/media/llms/isabelle-home-hk IQ_AUTH_TOKEN=hk`; I/Q takes the first
  free port from 8765 upward (record it in `Hopcroft_Karp/progress.md`). The
  instances with tokens gemini-1 (8765), ddfs (8768) and graph-adt belong to
  other campaigns: never touch, never kill.

**File / ROOT.** In the copy, a new session `Hopcroft_Karp` in a new directory
`Hopcroft_Karp/`, so that the Micali–Vazirani session stays unchanged:
`Hopcroft_Karp/ROOT` =
```
session Hopcroft_Karp = Micali_Vazirani +
  options [timeout = 3600]
  sessions
    Basic_Matching
  theories
    Hopcroft_Karp
```
plus a line `Hopcroft_Karp` in the top-level `ROOTS`. The theory is
`Hopcroft_Karp/Hopcroft_Karp.thy` (`theory Hopcroft_Karp`); it imports
`Micali_Vazirani.Top_Loop` and `"Basic_Matching.Berge"`.

**HARD RULE: pure-ASCII sources.** One-shots below use glyphs for
readability; the coder transcribes them with `\<name>` escapes
(`\<Rightarrow> \<Longrightarrow> \<in> \<notin> \<and> \<or> \<longrightarrow>
\<longleftrightarrow> \<forall> \<exists> \<noteq> \<infinity> \<union> \<inter>
\<subseteq> \<lbrakk> \<rbrakk> \<open> \<close> \<comment> \<And>` …).
`grep -P -c '[^\x00-\x7F]' Hopcroft_Karp/Hopcroft_Karp.thy` must be 0.

---

## Design decisions (settled)

- **HK-D1 — reuse the MV pipeline unchanged.** Alt-BFS is run exactly as for
  MV (full BFS, `srcs` = ALL free vertices, both sides); the copies DAG is
  Top_Loop's `copies_dag`/`copies_lev`; the DFS is `DFS_Avoid`/`IDFS` (M2).
  No new BFS variant, no truncation (Alt_BFS has none — verified). For
  shortest paths, M2 roots its DFS calls only at free `t` of *minimal*
  `altd_G Odd t`; exploring deeper levels is harmless.
- **HK-D2 — the matching instance is a nested `context` of locale `BFS`,
  not a new locale.** It fixes `UG M :: 'ver set set` and `X Y :: 'ver set`
  and assumes: `graph_invar UG`, `M ⊆ UG`, `Graph.digraph_abs matching =
  {(u, v). {u, v} ∈ M}`, `Graph.digraph_abs unmatching = {(u, v). {u, v} ∈
  UG - M}`, `t_set srcs = Vs UG - Vs M`, `bipartite UG X Y`. `BFS_axiom`
  stays a separate hypothesis in M1 (M3 discharges it from the instance plus
  ADT facts). `Matching.matching M` is deliberately NOT assumed — M1's
  results hold for any `M ⊆ UG` (M3 adds it).
  *Satisfiability check (lesson from the ∀-form `upd_dists` axiom):* under
  the instance, `BFS_axiom` holds iff, besides ADT well-formedness/finiteness,
  `srcs ≠ {}` — a free vertex `v ∈ Vs UG` has an edge, necessarily unmatched,
  so `srcs ⊆ dVs unmatching`; `M ∩ (UG - M) = {}` gives disjointness. So the
  M1 results are vacuous exactly when every vertex of `UG` is matched — the
  case M3's loop must exit on before running BFS. Consistent.
- **HK-D3 — distinctness from labels, not from shortestness.** A copies walk
  is distinct because `copies_lev` strictly decreases along copies edges
  (`copies_lev_decrease`). In a bipartite graph the label of every copy on a
  walk is determined by the side of its vertex (`copies_walk_side`), so `vtx`
  is injective on the walk and the projected walk is a simple path. No
  closed-walk surgery, no use of clause D for distinctness. (Clause D is still
  used, but only for the "shortest" conclusion that HK-M5 needs.)
- **HK-D4 — read-off direction.** The (I)DFS returns copies walks from
  `Vtx Odd t` DOWN to level 0 (copies edges are reversed BFS edges, TL-D2);
  the augmenting path is `rev (map vtx q)`, from the source `vtx z` to `t`.
- **HK-D5 — name hygiene inside `context BFS`.** `matching` is a BFS locale
  PARAMETER (an adjmap): the Berge constant must be written
  `Matching.matching` (not needed in M1). `G` is BFS's digraph
  `unmatching ∪ matching` (`G_def`); the undirected graph is `UG`. `path`,
  `edges_of_path`, `Vs` are the undirected (`Paths`, `Undirected_Set_Graphs`)
  ones; walks in digraphs are always written `Vwalk.vwalk`/`Vwalk.vwalk_bet`.
- **HK-D6 — re-entering the `BFS_axiom` context.** Every Top_Loop/Alt_BFS
  lemma proved inside a `BFS_axiom` context is exported WITH a `BFS_axiom ⟹`
  premise — including Top_Loop's `BFS_axiom_ctxt`, which is useless here.
  The new theory proves its own `BFS_axiom_hk` and cites every imported
  context lemma as `foo[OF BFS_axiom_hk …]` (Top_Loop's pattern with
  `BFS_axiom_ctxt`). Top_Loop's `copies_dagE` would need that premise too and
  its `consumes`/case names are not guaranteed to survive `[OF …]`, so the
  plan restates it axiom-free as `copies_dag_cases` (same proof) at locale
  level.
- **HK-D7 — generic layer first.** Gate 1 mentions no matching at all; its
  lemmas (copies walk ⟹ alternating walk in `T`, level-0 copies are sources,
  odd-visited ⟹ odd copy present) are equally what MV needs to read off DDFS
  output, and may later migrate into `Top_Loop.thy`.
- **HK-D8 — the search procedure is the incremental DFS, not DDFS.**
  Augmenting paths are found by `IDFS_impl` (IDFS.thy, built on DFS_Avoid),
  the same procedure that DDFS calls twice internally. DDFS itself is not
  used. DDFS searches from the two endpoints of a bridge for two
  vertex-disjoint downward paths, or reports a bottleneck (a blossom).
  Bipartite graphs have no blossoms, so one downward search from each free
  odd copy `Vtx Odd t` to level 0 suffices: by HK-M1 every such walk projects
  to a simple augmenting path (`copies_walk_side`,
  `copies_walk_distinct_vtx`). HK-M1 is independent of the search procedure:
  it only states that every copies-DAG walk from `Vtx Odd t` to level 0
  reads off an augmenting path, and that such a walk exists whenever an
  augmenting path exists. The choice of `IDFS_impl` is made in Gates 4–5.
- **HK-D9 — the input graph is stated through the read-only graph
  specification (user decision, 2026-10-11).** A read-only graph
  specification is being split out of `Pair_Graph_Specs` in a parallel
  session ("Micali_Vazirani - Hopcroft-Karp Graph ADT"). That session first
  delivers an interim theory with the locale `pair_graph_specs_read_only`,
  whose name and parameters are those of the final base locale: lookup, the
  invariant, the vertex-set operations, and the definitions `neighbourhood`,
  `digraph_abs`, `graph_inv`, `finite_graph`, `finite_vsets` with their
  read-only lemmas. Every `Pair_Graph_Specs` instance is automatically an
  instance of it (`sublocale … rewrites …`), with identical constants.
  Consequences for this plan:
  - Gates 1–4 are unaffected (no input-graph interface).
  - From Gate 5 on (the concrete phase), the input graph is stated ONLY in the
    vocabulary of `pair_graph_specs_read_only`. Do not define a separate
    read-only locale, and never refer to the sublocale's qualifier (`ro.` or
    similar): that name disappears after the split.
  - Where the input graph's abstraction must be identified with an alt-BFS
    `Graph.` constant at the same operations, confine the bridging to one or
    two lemmas; after the split both sides are the same constant.
  - Never import the interim theory together with the split library (the
    locale names would clash).
  - The interim theory is delivered into the Hopcroft–Karp project copy.
    The Graph ADT session keeps it in its own copy until the Hopcroft–Karp
    copy exists, then sends its path and contents. The Hopcroft–Karp session
    places it under `Hopcroft_Karp/`; the Graph ADT session never writes into
    the Hopcroft–Karp copy. Its own split copy is planned at
    `/media/llms/Isabelle-Graph-Library-Graph-ADT`, with Isabelle home
    `/media/llms/isabelle-home-graph-adt`, based on the same commit.
  - Integration (in the project copy), AFTER Hopcroft–Karp is verified: delete the interim theory,
    apply the other session's patch (library files plus the repair sites,
    among them DDFS_Example.thy:238–288), and rebuild all sessions.

## Baseline facts (recon 2026-10-10, verify in β-0)

- Top_Loop (`context BFS`; lines 35–398 inside `assumes BFS_axiom`):
  `copies_of` (9), `copies_dag` (21), `copies_lev` (27, locale level),
  `BFS_axiom_ctxt` (35), `altd_set_witness` (40: `alt_distance_set H parity v
  ≠ ∞` obtains `u ∈ srcs`, `alt_walk parity H u p v`), `altd_G_srcs_Even_0`
  (59), `valid_DAG_tight_unmatched/_matched` (70/111), `copies_dagE` (145),
  `copies_lev_decrease` (153), `copies_dag_dVs` (193), `copies_dag_finite`
  (216), `alt_walk_copies_path` (228), `copies_reach_zero` (293),
  `valid_DAG_layered` (348), `BFS_output_layered` (369),
  `copies_lev_by_lookup` (375).
- Alt_BFS: `G_def` (163), `unmatched_edge_def`/`matched_edge_def` (204–205),
  `alt_distance_set_def` (207, argument order `H parity v`), `alt_walk`
  abbreviation (210), `altd_G` (212); context `assumes BFS_axiom` from 258:
  `altd_G_parity` (937), `alt_walk_snocE` (2615),
  `valid_alt_BFS_DAG_props` (3374; (1) `T ⊆ G`, (4)/(5) `altd ≠ ∞`, (6)/(7)
  completeness, (10)/(11) C2, (12) D), `BFS_valid_DAG` (3466).
- Alt_Dist (global): `alt_vwalk_bet_append_2` (319, ends `Even`) / `_3`
  (389, ends `Odd`), `distance_set_0[simp]` (2383), `alt_dist_set_not_inf`
  (2087); in locale `alt_dist` (use `alt_dist.` prefix): `alt_vwalk_bet_def`,
  `alt_vwalk_bet_subset` (61), `alt_dist_set_inf` (1882, β-0 confirms prefix).
  `alt_vwalk_bet parity` checks `of_parity (other_parity parity) (length p)`
  (vertex count): `Odd` walks have an EVEN number of vertices.
- Vwalk: `induct_vwalk_bet` (384; cases `path1 v` / `path2 v v' vs b`,
  `consumes 1`), `Vwalk.vwalk.induct` (cases `vwalk0/1/2`),
  `vwalk_bet_in_dVs` (347: `set p ⊆ dVs E`), `vwalk_bet_in_vertices` (577),
  `hd_of_vwalk_bet'` (`v = hd p`), `hd_of_vwalk_bet''` (`u ∈ set p`),
  `last_of_vwalk_bet` (`v' = last p`), `last_of_vwalk_bet'`
  (`∃p'. p = p' @ [v']`), `Vwalk.vwalk_bet_def`.
- Pair_Graph: `dVs_eq` (47: `dVs E = fst ` E ∪ snd ` E`), `dVsI` (29,
  `[intro]`, two conclusions), `in_dVsE` (157), `dVs_subset` (142).
- Undirected: `Vs_def`, `vs_member` (`v ∈ Vs G ⟷ (∃e∈G. v ∈ e)`),
  `edges_are_Vs` (`{v, v'} ∈ G ⟹ v ∈ Vs G`), `edges_are_Vs_2`
  (`{v', v} ∈ G ⟹ v ∈ Vs G`), `dblton_graph_def`, `graph_invar` (abbrev:
  `dblton_graph G ∧ finite (Vs G)`); Paths: `path` (intro `path0/1/2`, `path1:
  v ∈ Vs X ⟹ path X [v]`, `path2: {v,v'} ∈ X ⟹ path X (v'#vs) ⟹ path X
  (v#v'#vs)`), `mem_path_Vs` (44), `path_edges_subset` (985),
  `edges_of_path` (`fun`, 3 equations).
- Bipartite: `bipartite_def` (`X ∩ Y = {} ∧ (∀e∈G. ∃u v. e = {u,v} ∧ u ∈ X ∧
  v ∈ Y)`), `bipartite_edgeD` (56; (3) `v ∈ X ⟹ u ∈ Y - X`, (4) `v ∈ Y ⟹
  u ∈ X - Y` for `{u,v} ∈ G`), `bipartite_vs_subset` (84),
  `bipartite_commute` (74).
- Matching/Berge: `matching_augmenting_path_def` (`length p ≥ 2 ∧ alt_list
  (λe. e ∉ M) (λe. e ∈ M) (edges_of_path p) ∧ hd p ∉ Vs M ∧ last p ∉ Vs M`),
  `graph_augmenting_path G M p ≡ path G p ∧ distinct p ∧
  matching_augmenting_path M p` (abbrev), `alt_path M p` (abbrev, the
  `alt_list` conjunct), `aug_paths_are_even` (724: `even (length p)`),
  `Berge_2`, `Berge`.
- Alternating_Lists: `alt_list_empty`, `alt_list_step` (`inductive_simps`:
  `alt_list P1 P2 (x#l) = (P1 x ∧ alt_list P2 P1 l)`).
- **Nothing in the library** does: several disjoint augmenting paths at once,
  shortest-augmenting-path growth, or `M ⊕ M*` decomposition into
  `|M*| - |M|` disjoint augmenting paths (the first is proved in Gate 3, δ-2; the others are needed only for HK-M5).

## Coder protocol

As for the Top_Loop campaign (coder.md §1 REPL-gate is in force):
- **Isar skeletons are authoritative; every search closer is a CANDIDATE.**
  Each `auto`/`simp`/`simp_all`/`blast`/`force`/`fastforce` below must pass
  the REPL's per-step cap BEFORE it is written to the buffer. `presburger`,
  `linarith`, `rule`, `fact`, `.` are deterministic. Where this plan names a
  FALLBACK, try it before sledgehammer.
- Work ONLY in the project copy `/media/llms/Isabelle-Graph-Library-Hopcroft-Karp`
  (see "Project copy"); never write into the Micali–Vazirani directory.
- **I/Q channel (set up 2026-10-11):** the Hopcroft–Karp jEdit runs with
  `USER_HOME=/media/llms/isabelle-home-hk`, logic `Micali_Vazirani`, I/Q on
  **port 8767, token `hk`**. Call it ONLY through the copy's bridge script,
  from the copy root:
  `python3 /media/llms/Isabelle-Graph-Library-Hopcroft-Karp/mcp.py <tool> '<json>'`.
  That script pins port 8767 and token `hk` and authenticates on every call;
  do NOT call `authenticate` with `gemini-1`, and do NOT use the
  Micali–Vazirani `mcp.py` (the shell exports `IQ_AUTH_TOKEN=gemini-1`, which
  belongs to another campaign). If jEdit must be restarted, the ONLY command
  is, from the copy root:
  `USER_HOME=/media/llms/isabelle-home-hk IQ_AUTH_TOKEN=hk DISPLAY=:1 nohup isabelle jedit -l Micali_Vazirani -d /media/llms/AutoCorrode/iq/ -d . &`
  then re-check the port with `ss -ltnp | grep 87` (first free from 8765).
  **Other instances belong to other campaigns — never touch, never kill:**
  on 2026-10-11 port 8765 = token graph-adt, 8766 = token ddfs; a gemini-1
  (Micali–Vazirani) instance may bind any free port.
- Pure ASCII; batch re-gate `USER_HOME=/media/llms/isabelle-home-hk isabelle build -d . Hopcroft_Karp` after each
  PIDE-green gate; no smt/metis/sorry; sledgehammer-in-REPL first on a broken
  step; `enat` steps via `(auto simp only: enat_simps …)`; never `dVs_def` in
  a search tactic (use `dVs_eq`); milestone snapshots to
  `/media/llms/Isabelle-Graph-Library-Hopcroft-Karp/Hopcroft_Karp/backups/`;
  progress log `Hopcroft_Karp/progress.md` ("## Hopcroft_Karp Gate N").
- REPL anchoring (lesson): anchor on the last lemma INSIDE the innermost
  context, never on a context's `end`; a `note` after `proof (rule …,
  goal_cases)` is scoped to case 1 only.

---

## Phase β — the generic read-off layer (Gate 1)

### β-0. Skeleton + recon

In the project copy, create `Hopcroft_Karp/Hopcroft_Karp.thy`:

```isabelle
theory Hopcroft_Karp
  imports Micali_Vazirani.Top_Loop "Basic_Matching.Berge"
begin

text ‹Hopcroft-Karp on the Micali-Vazirani pipeline. Milestone 1: in a
bipartite graph, walks of the alt-BFS copies DAG from a free odd copy down to
level 0 are exactly (reversed) augmenting paths.›

section ‹Generic walk lemmas›

― ‹β-1 goes here (and, in Gate 2, the two alt_list transfer lemmas)›

context BFS
begin

― ‹β-2, β-3 (axiom-free) go here›

context
  includes Graph.adjmap.automation and Graph.vset.set.automation
       and set_ops.automation2
  assumes BFS_axiom
begin

lemma BFS_axiom_hk: "BFS_axiom"
  using ‹BFS_axiom› .

― ‹β-4 goes here; Gate 2 adds the matching-instance context at the end›

end ― ‹BFS_axiom context›

end ― ‹locale BFS›

end
```

Create `Hopcroft_Karp/ROOT` (as in "File / ROOT") and add `Hopcroft_Karp` to the top-level `ROOTS`. `Micali_Vazirani/ROOT` stays unchanged.

Recon checks (record in progress.md before β-1):
(a) the import merge loads (`Top_Loop` + `Basic_Matching.Berge`): no
duplicate-name errors; note any "Ambiguous input" warnings on `path`,
`edges_of_path`, `Vs`, `dVs_subset`, `bipartite`.
(b) Inside `context BFS`: `term "matching"` is the adjmap parameter;
`term "Matching.matching"` is the Berge constant; `term "G"` is BFS's digraph.
(c) `thm` each of: `induct_vwalk_bet Vwalk.vwalk.induct path.induct
edges_of_path.induct alt_list_step alt_list_empty alt_vwalk_bet_append_2
alt_vwalk_bet_append_3 alt_dist.alt_vwalk_bet_subset alt_dist.alt_dist_set_inf
distance_set_0 bipartite_edgeD bipartite_vs_subset bipartite_commute
mem_path_Vs vs_member edges_are_Vs edges_are_Vs_2 dVs_eq dVsI in_dVsE
dVs_subset vwalk_bet_in_dVs vwalk_bet_in_vertices hd_of_vwalk_bet'
hd_of_vwalk_bet'' last_of_vwalk_bet aug_paths_are_even
matching_augmenting_path_def distinct_map path_edges_subset`. Record the
exact name of any that needs a qualifier.
(d) Inside the new axiom context: `thm copies_dagE copies_lev_decrease
copies_reach_zero altd_set_witness valid_alt_BFS_DAG_props alt_walk_snocE
altd_G_parity BFS_valid_DAG` — confirm each shows the leading `BFS_axiom ⟹`
premise (so `[OF BFS_axiom_hk …]` is the right citation form).

### β-1. Level-decreasing walks are distinct (global, generic)

In section "Generic walk lemmas":

```isabelle
lemma vwalk_bet_level_distinct:
  assumes "Vwalk.vwalk_bet E w q z"
      and "⋀a b. (a, b) ∈ E ⟹ lv b < (lv a :: nat)"
  shows "distinct q ∧ (∀x ∈ set q. lv x ≤ lv w)"
  using assms(1)
proof (induction rule: induct_vwalk_bet)
  case (path1 v)
  show ?case by simp
next
  case (path2 v v' vs b)
  have lt: "lv v' < lv v" by (rule assms(2)[OF path2(1)])
  have ih: "distinct (v' # vs)" "∀x ∈ set (v' # vs). lv x ≤ lv v'"
    using path2(3) by simp_all
  have nin: "v ∉ set (v' # vs)"
  proof
    assume "v ∈ set (v' # vs)"
    hence "lv v ≤ lv v'" using ih(2) by blast
    thus False using lt by linarith
  qed
  have all: "∀x ∈ set (v # v' # vs). lv x ≤ lv v"
  proof
    fix x assume "x ∈ set (v # v' # vs)"
    then consider "x = v" | "x ∈ set (v' # vs)" by auto
    then show "lv x ≤ lv v"
    proof cases
      case 1
      then show ?thesis by simp
    next
      case 2
      then have "lv x ≤ lv v'" using ih(2) by blast
      then show ?thesis using lt by linarith
    qed
  qed
  show ?case using ih(1) nin all by simp
qed
```

### β-2. Copies edges, axiom-free (locale level, before the axiom context)

```isabelle
lemma copies_dag_cases:
  assumes "(w, w') ∈ copies_dag (Graph.digraph_abs T)"
  obtains u v where "w = Vtx Odd v" "w' = Vtx Even u"
      "(u, v) ∈ Graph.digraph_abs T" "(u, v) ∈ Graph.digraph_abs unmatching"
    | u v where "w = Vtx Even v" "w' = Vtx Odd u"
      "(u, v) ∈ Graph.digraph_abs T" "(u, v) ∈ Graph.digraph_abs matching"
  using assms by (auto simp: copies_dag_def)
  ― ‹verbatim copy of Top_Loop's copies_dagE (which proved this way)›

lemma copies_dag_vtx_dVs:
  assumes "w ∈ dVs (copies_dag (Graph.digraph_abs T))"
  shows "vtx w ∈ dVs (Graph.digraph_abs T)"
proof -
  from assms obtain a b where ab: "(a, b) ∈ copies_dag (Graph.digraph_abs T)" "w = a ∨ w = b"
    by (force simp: dVs_eq)              ― ‹Top_Loop copies_dag_dVs pattern›
  from ab(1) show ?thesis
  proof (cases rule: copies_dag_cases)
    case (1 u v)
    then show ?thesis using ab(2) by (auto intro: dVsI)
  next
    case (2 u v)
    then show ?thesis using ab(2) by (auto intro: dVsI)
  qed
qed
```

### β-3. A copies walk ending at an Even copy is an alternating walk of `T` (axiom-free; the crux)

Reads a copies walk `w … z` backwards: the vertex projections, reversed, form
an alternating walk of `T` from `vtx z` to `vtx w` whose parity is
`label w`. Structural — uses only `copies_dag_cases` and the Alt_Dist append
lemmas, exactly as Top_Loop's `valid_DAG_tight_unmatched/_matched` did.

```isabelle
lemma copies_walk_alt_walk:
  assumes "Vwalk.vwalk_bet (copies_dag (Graph.digraph_abs T)) w q z"
  shows "label z = Even ⟶
           alt_walk (label w) (Graph.digraph_abs T) (vtx z) (rev (map vtx q)) (vtx w)"
  using assms
proof (induction rule: induct_vwalk_bet)
  case (path1 v)
  have vT: "vtx v ∈ dVs (Graph.digraph_abs T)" by (rule copies_dag_vtx_dVs[OF path1])
  show ?case
    using vT by (auto simp: alt_dist.alt_vwalk_bet_def parity_simps alt_list_empty)
    ― ‹Top_Loop singleton pattern (valid_DAG_tight_unmatched, `single`)›
next
  case (path2 v v' vs b)
  show ?case
  proof
    assume ev: "label b = Even"
    have IH: "alt_walk (label v') (Graph.digraph_abs T) (vtx b) (rev (map vtx (v' # vs))) (vtx v')"
      by (rule mp[OF path2(3) ev])
    have pne: "rev (map vtx (v' # vs)) ≠ []" by simp
    from path2(1)
    show "alt_walk (label v) (Graph.digraph_abs T) (vtx b) (rev (map vtx (v # v' # vs))) (vtx v)"
    proof (cases rule: copies_dag_cases)
      case (1 u x)
      ― ‹v = Vtx Odd x, v' = Vtx Even u, (u, x) an unmatched T-edge: append it›
      have w1: "alt_walk Even (Graph.digraph_abs T) (vtx b) (rev (map vtx (v' # vs)))
                  (last (rev (map vtx (v' # vs))))"
        using IH 1(2) by simp
      have step2: "alt_walk Odd (Graph.digraph_abs T) u [u, x] x"
        using 1(3) 1(4)
        by (auto simp: alt_dist.alt_vwalk_bet_def parity_simps unmatched_edge_def
                       alt_list_empty alt_list_step edge_iff_vwalk_bet[symmetric])
        ― ‹verbatim Top_Loop step2 (unmatched)›
      have w2: "next_alt_list_parity Even alt_dist.alt_vwalk_bet unmatched_edge matched_edge
                  (other_parity Even) (Graph.digraph_abs T)
                  (last (rev (map vtx (v' # vs)))) (last (rev (map vtx (v' # vs))) # [x]) x"
        using step2 1(2) by (simp add: parity_simps)
      have res: "alt_walk Odd (Graph.digraph_abs T) (vtx b) (rev (map vtx (v' # vs)) @ [x]) x"
        by (rule alt_vwalk_bet_append_3[where parity = Even, OF w1 w2 pne])
      show ?thesis using res 1(1) by simp
    next
      case (2 u x)
      ― ‹v = Vtx Even x, v' = Vtx Odd u, (u, x) a matched T-edge: append it›
      have w1: "alt_walk Odd (Graph.digraph_abs T) (vtx b) (rev (map vtx (v' # vs)))
                  (last (rev (map vtx (v' # vs))))"
        using IH 2(2) by simp
      have step2: "alt_dist.alt_vwalk_bet matched_edge unmatched_edge Odd
                     (Graph.digraph_abs T) u [u, x] x"
        using 2(3) 2(4)
        by (auto simp: alt_dist.alt_vwalk_bet_def parity_simps matched_edge_def
                       alt_list_empty alt_list_step edge_iff_vwalk_bet[symmetric])
        ― ‹verbatim Top_Loop step2 (matched)›
      have w2: "next_alt_list_parity Odd alt_dist.alt_vwalk_bet unmatched_edge matched_edge
                  Odd (Graph.digraph_abs T)
                  (last (rev (map vtx (v' # vs)))) (last (rev (map vtx (v' # vs))) # [x]) x"
        using step2 2(2) by (simp add: parity_simps)
      have res: "alt_walk Even (Graph.digraph_abs T) (vtx b) (rev (map vtx (v' # vs)) @ [x]) x"
        by (rule alt_vwalk_bet_append_2[where parity = Odd, OF w1 w2 pne])
      show ?thesis using res 2(1) by simp
    qed
  qed
qed
```

Notes for the coder: `w1`/`res`'s `simp` must normalise both sides of
`rev (map vtx (v # v' # vs))` identically (expected:
`rev (map vtx vs) @ [vtx v', x]`); if the final `show` fails, prove
`rev (map vtx (v # v' # vs)) = rev (map vtx (v' # vs)) @ [x]` first
(`using 1(1) by simp`) and rewrite with it (`by (simp only: …)` / `subst`).
If `induct_vwalk_bet` is not found unqualified, use
`Vwalk.induct_vwalk_bet`; case facts are positional (`path2(1)` edge,
`path2(2)` tail walk, `path2(3)` IH).

### β-4. Inside the `BFS_axiom` context: level 0, the odd start, the odd copy

```isabelle
lemma copies_lev_zero:
  assumes V: "valid_alt_BFS_DAG T dists VisE VisO"
      and mem: "z ∈ dVs (copies_dag (Graph.digraph_abs T))"
      and z0: "copies_lev z = 0"
  shows "label z = Even" "vtx z ∈ t_set srcs"
proof -
  note P = valid_alt_BFS_DAG_props[OF BFS_axiom_hk V]
  have zmem: "z ∈ Vtx Even ` t_set VisE ∪ Vtx Odd ` t_set VisO"
    using copies_dag_dVs[OF BFS_axiom_hk V] mem by blast
  then consider (Ev) x where "z = Vtx Even x" "x ∈ t_set VisE"
              | (Od) x where "z = Vtx Odd x" "x ∈ t_set VisO"
    by blast
  then have "label z = Even ∧ vtx z ∈ t_set srcs"
  proof cases
    case (Ev x)
    have fin: "altd_G Even x ≠ ∞" using P(5)[OF Ev(2)] .
    obtain n where n: "altd_G Even x = enat n"
      using fin by (cases "altd_G Even x") auto
    have n0: "n = 0" using z0 n Ev(1) by (simp add: copies_lev_def)
    have xG: "x ∈ dVs G"
    proof (rule ccontr)
      assume "x ∉ dVs G"
      hence "altd_G Even x = ∞"
        by (simp add: alt_distance_set_def alt_dist.alt_dist_set_inf)
      thus False using fin by simp
    qed
    ― ‹FALLBACK for xG if alt_dist_set_inf is unavailable: obtain s p from
       altd_set_witness[OF BFS_axiom_hk fin]; vb: Vwalk.vwalk_bet G s p x
       (simp add: alt_dist.alt_vwalk_bet_def); x ∈ set p from
       last_of_vwalk_bet'[OF vb]; conclude by vwalk_bet_in_vertices[OF vb]›
    have d0: "altd_G Even x = 0" using n n0 by (simp add: zero_enat_def)
    have xs: "x ∈ t_set srcs" using d0 xG by (auto simp: alt_distance_set_def)
      ― ‹converse of Top_Loop altd_G_srcs_Even_0; distance_set_0 is [simp]›
    show ?thesis using Ev(1) xs by simp
  next
    case (Od x)
    have fin: "altd_G Odd x ≠ ∞" using P(4)[OF Od(2)] .
    obtain n where n: "altd_G Odd x = enat n"
      using fin by (cases "altd_G Odd x") auto
    have n0: "n = 0" using z0 n Od(1) by (simp add: copies_lev_def)
    have "of_parity Odd n" by (rule altd_G_parity[OF BFS_axiom_hk n])
    hence False using n0 by (simp add: parity_simps)
    then show ?thesis by simp
  qed
  thus "label z = Even" "vtx z ∈ t_set srcs" by simp_all
qed

lemma copies_walk_from_odd:
  assumes V: "valid_alt_BFS_DAG T dists VisE VisO"
      and q: "Vwalk.vwalk_bet (copies_dag (Graph.digraph_abs T)) (Vtx Odd t) q z"
      and z0: "copies_lev z = 0"
  shows "vtx z ∈ t_set srcs"
        "alt_walk Odd G (vtx z) (rev (map vtx q)) t"
        "enat (length q - 1) = altd_G Odd t"
proof -
  note P = valid_alt_BFS_DAG_props[OF BFS_axiom_hk V]
  have zq: "z ∈ set q" using q by (auto simp: Vwalk.vwalk_bet_def)
  have zmem: "z ∈ dVs (copies_dag (Graph.digraph_abs T))"
    using vwalk_bet_in_dVs[OF q] zq by blast
  note lz = copies_lev_zero[OF V zmem z0]
  have aw: "alt_walk Odd (Graph.digraph_abs T) (vtx z) (rev (map vtx q)) t"
    using mp[OF copies_walk_alt_walk[OF q] lz(1)] by simp
  show "vtx z ∈ t_set srcs" by (rule lz(2))
  show "alt_walk Odd G (vtx z) (rev (map vtx q)) t"
    by (rule alt_dist.alt_vwalk_bet_subset[OF aw P(1)])
  show "enat (length q - 1) = altd_G Odd t"
    using P(12)[OF lz(2) aw] by simp
qed

lemma VisO_copies_dVs:
  assumes V: "valid_alt_BFS_DAG T dists VisE VisO"
      and t: "t ∈ t_set VisO"
  shows "Vtx Odd t ∈ dVs (copies_dag (Graph.digraph_abs T))"
proof -
  note P = valid_alt_BFS_DAG_props[OF BFS_axiom_hk V]
  have ne: "alt_distance_set (Graph.digraph_abs T) Odd t ≠ ∞"
    using P(10)[OF t] P(4)[OF t] by simp
  obtain s p where sp: "s ∈ t_set srcs" "alt_walk Odd (Graph.digraph_abs T) s p t"
    using altd_set_witness[OF BFS_axiom_hk ne] by blast
  have pne: "p ≠ []" using sp(2) by (auto simp: alt_dist.alt_vwalk_bet_def)
  have ev: "even (length p)"
    using sp(2) by (auto simp: alt_dist.alt_vwalk_bet_def parity_simps)
  have l0: "length p ≠ 0" using pne by simp
  have len: "1 < length p" using l0 ev by presburger
  obtain q y where sn: "p = q @ [t]" "q ≠ []" "y = last q"
      "alt_walk (other_parity Odd) (Graph.digraph_abs T) s q y"
      "(y, t) ∈ Graph.digraph_abs T"
      "case Odd of Odd ⇒ unmatched_edge (y, t) | Even ⇒ matched_edge (y, t)"
    by (rule alt_walk_snocE[OF BFS_axiom_hk sp(2) len])
    ― ‹Top_Loop α-5 pattern; the `case` line must be written in this branch
       order (Odd first, as in alt_walk_snocE) so the terms match›
  have ue: "(y, t) ∈ Graph.digraph_abs unmatching"
    using sn(6) by (simp add: unmatched_edge_def)
  have edge: "(Vtx Odd t, Vtx Even y) ∈ copies_dag (Graph.digraph_abs T)"
    using sn(5) ue by (auto simp: copies_dag_def)
  show ?thesis by (rule dVsI(1)[OF edge])
qed
```

**Gate 1 deliverable:** β-0…β-4 PIDE-green, ROOT updated, ASCII = 0, batch
green. STOP and report (PIDE evidence, `thm` output of the four main
lemmas, batch result).

---

## Phase γ — the bipartite matching instance (Gate 2)

### γ-0. Two global `alt_list` transfer lemmas (section "Generic walk lemmas")

Directed walk edges `(u, v)` ↔ undirected path edges `{u, v}`, predicate by
predicate. (The library's `edges_of_path_eq`/`path_edges_set_of_pair_of_vwalk_edges`
give `edges_of_path p = map … (edges_of_vwalk p)`, but sit in other sessions/
locales; a direct induction is cheaper than the plumbing.)

```isabelle
lemma alt_list_edges_of_vwalk_path:
  assumes "alt_list P1 P2 (edges_of_vwalk p)"
      and "⋀u v. P1 (u, v) ⟹ Q1 {u, v}"
      and "⋀u v. P2 (u, v) ⟹ Q2 {u, v}"
  shows "alt_list Q1 Q2 (edges_of_path p)"
  using assms
proof (induction p arbitrary: P1 P2 Q1 Q2 rule: edges_of_path.induct)
  case 1
  show ?case by (simp add: alt_list_empty)
next
  case (2 v)
  show ?case by (simp add: alt_list_empty)
next
  case (3 v v' l)
  have h: "P1 (v, v')" "alt_list P2 P1 (edges_of_vwalk (v' # l))"
    using 3(2) by (simp_all add: alt_list_step)
  have ih: "alt_list Q2 Q1 (edges_of_path (v' # l))"
    by (rule 3(1)[OF h(2) 3(4) 3(3)])
  show ?case using 3(3)[OF h(1)] ih by (simp add: alt_list_step)
qed

lemma alt_list_edges_of_path_vwalk:
  assumes "alt_list Q1 Q2 (edges_of_path p)"
      and "⋀u v. {u, v} ∈ set (edges_of_path p) ⟹ Q1 {u, v} ⟹ P1 (u, v)"
      and "⋀u v. {u, v} ∈ set (edges_of_path p) ⟹ Q2 {u, v} ⟹ P2 (u, v)"
  shows "alt_list P1 P2 (edges_of_vwalk p)"
  using assms
proof (induction p arbitrary: P1 P2 Q1 Q2 rule: edges_of_path.induct)
  case 1
  show ?case by (simp add: alt_list_empty)
next
  case (2 v)
  show ?case by (simp add: alt_list_empty)
next
  case (3 v v' l)
  have h: "Q1 {v, v'}" "alt_list Q2 Q1 (edges_of_path (v' # l))"
    using 3(2) by (simp_all add: alt_list_step)
  have e1: "P1 (v, v')"
    by (rule 3(3)) (simp_all add: h(1))
  have ih: "alt_list P2 P1 (edges_of_vwalk (v' # l))"
  proof (rule 3(1)[OF h(2)])
    fix a b assume ab: "{a, b} ∈ set (edges_of_path (v' # l))" "Q2 {a, b}"
    have "{a, b} ∈ set (edges_of_path (v # v' # l))" using ab(1) by simp
    thus "P2 (a, b)" using ab(2) by (rule 3(4))
  next
    fix a b assume ab: "{a, b} ∈ set (edges_of_path (v' # l))" "Q1 {a, b}"
    have "{a, b} ∈ set (edges_of_path (v # v' # l))" using ab(1) by simp
    thus "P1 (a, b)" using ab(2) by (rule 3(3))
  qed
  show ?case using e1 ih by (simp add: alt_list_step)
qed
```

(If the `fun` induction rule's cases are not named `1/2/3`, use
`goal_cases`/positional names as PIDE shows them. Case facts: `3(1)` IH,
`3(2)` the `alt_list` premise, `3(3)`/`3(4)` the two transfer premises.)

### γ-1. The instance context (at the END of the `BFS_axiom` context)

```isabelle
subsection ‹The bipartite matching instance›

context
  fixes UG M :: "'ver set set" and X Y :: "'ver set"
  assumes UG_inv: "graph_invar UG"
      and M_sub: "M ⊆ UG"
      and Mabs: "Graph.digraph_abs matching = {(u, v). {u, v} ∈ M}"
      and Uabs: "Graph.digraph_abs unmatching = {(u, v). {u, v} ∈ UG - M}"
      and srcs_free: "t_set srcs = Vs UG - Vs M"
      and bip: "bipartite UG X Y"
begin

lemma G_char: "G = {(u, v). {u, v} ∈ UG}"
  using M_sub by (auto simp: G_def Mabs Uabs)

lemma dVs_G_Vs: "dVs G ⊆ Vs UG"
proof
  fix x assume "x ∈ dVs G"
  then obtain a b where ab: "(a, b) ∈ G" "x = a ∨ x = b"
    by (force simp: dVs_eq)
  have e: "{a, b} ∈ UG" using ab(1) by (simp add: G_char)
  show "x ∈ Vs UG" using ab(2) e by (auto intro: edges_are_Vs edges_are_Vs_2)
qed

― ‹γ-2 … γ-6 go here›

end ― ‹matching instance›
```

(Check the vertex type variable of locale `BFS` is `'ver` — it is in
`lookup_neighb :: 'adjmap ⇒ 'ver ⇒ 'vset option`.)

### γ-2. Digraph walks in `G` ↔ undirected paths in `UG`

```isabelle
lemma vwalk_G_path:
  assumes "Vwalk.vwalk G p"
  shows "path UG p"
  using assms
proof (induction rule: Vwalk.vwalk.induct)
  case vwalk0
  show ?case by (rule path0)
next
  case (vwalk1 v)
  have "v ∈ Vs UG" using vwalk1 dVs_G_Vs by blast
  thus ?case by (rule path1)
next
  case (vwalk2 v v' vs)
  have "{v, v'} ∈ UG" using vwalk2(1) by (simp add: G_char)
  thus ?case using vwalk2(3) by (rule path2)
qed

lemma path_vwalk_G:
  assumes "path UG p"
  shows "Vwalk.vwalk G p"
  using assms
proof (induction rule: path.induct)
  case path0
  show ?case by (rule vwalk0)
next
  case (path1 v)
  have "∃e ∈ UG. v ∈ e" using path1 by (simp add: vs_member)
  then obtain e where e: "e ∈ UG" "v ∈ e" by blast
  from UG_inv e(1) obtain a b where ab: "e = {a, b}"
    unfolding dblton_graph_def by blast
  have ab_G: "(a, b) ∈ G" using e(1) ab by (simp add: G_char)
  have "v ∈ dVs G" using e(2) ab ab_G by (auto intro: dVsI)
  thus ?case by (rule vwalk1)
next
  case (path2 v v' vs)
  have "(v, v') ∈ G" using path2(1) by (simp add: G_char)
  thus ?case using path2(3) by (rule vwalk2)
qed
```

(Case facts are positional: `vwalk2(1)` edge, `vwalk2(2)` tail, `vwalk2(3)`
IH; same for `path2`. If `path.induct`/`vwalk0` etc. are ambiguous after the
merge, qualify with the theory names recorded in β-0.)

### γ-3. Alternation transfer

```isabelle
lemma alt_walk_alt_path:
  assumes "alt_walk parity G u p v"
  shows "alt_path M p"
proof -
  have al: "alt_list unmatched_edge matched_edge (edges_of_vwalk p)"
    using assms by (simp add: alt_dist.alt_vwalk_bet_def)
  show ?thesis
    using al
  proof (rule alt_list_edges_of_vwalk_path)
    fix a b assume "unmatched_edge (a, b)"
    thus "{a, b} ∉ M" by (simp add: unmatched_edge_def Uabs)
  next
    fix a b assume "matched_edge (a, b)"
    thus "{a, b} ∈ M" by (simp add: matched_edge_def Mabs)
  qed
qed

lemma alt_path_alt_list:
  assumes pth: "path UG p" and ap: "alt_path M p"
  shows "alt_list unmatched_edge matched_edge (edges_of_vwalk p)"
  using ap
proof (rule alt_list_edges_of_path_vwalk)
  fix a b assume ab: "{a, b} ∈ set (edges_of_path p)" "{a, b} ∉ M"
  have "{a, b} ∈ UG" using path_edges_subset[OF pth] ab(1) by blast
  thus "unmatched_edge (a, b)" using ab(2) by (simp add: unmatched_edge_def Uabs)
next
  fix a b assume ab: "{a, b} ∈ set (edges_of_path p)" "{a, b} ∈ M"
  thus "matched_edge (a, b)" by (simp add: matched_edge_def Mabs)
qed
```

### γ-4. Augmenting paths are odd alternating walks of `G` between sources

```isabelle
lemma aug_path_alt_walk:
  assumes A: "graph_augmenting_path UG M p"
  shows "hd p ∈ t_set srcs" "last p ∈ t_set srcs"
        "alt_walk Odd G (hd p) p (last p)"
proof -
  have pth: "path UG p" using A by simp
  have aug: "matching_augmenting_path M p" using A by simp
  have len: "2 ≤ length p" and ap: "alt_path M p"
    and hM: "hd p ∉ Vs M" and lM: "last p ∉ Vs M"
    using aug by (simp_all add: matching_augmenting_path_def)
  have pne: "p ≠ []" using len by auto
  have hV: "hd p ∈ Vs UG" by (rule mem_path_Vs[OF pth hd_in_set[OF pne]])
  have lV: "last p ∈ Vs UG" by (rule mem_path_Vs[OF pth last_in_set[OF pne]])
  show "hd p ∈ t_set srcs" using hV hM by (simp add: srcs_free)
  show "last p ∈ t_set srcs" using lV lM by (simp add: srcs_free)
  have vw: "Vwalk.vwalk G p" by (rule path_vwalk_G[OF pth])
  have al: "alt_list unmatched_edge matched_edge (edges_of_vwalk p)"
    by (rule alt_path_alt_list[OF pth ap])
  have ev: "even (length p)" by (rule aug_paths_are_even[OF aug])
  show "alt_walk Odd G (hd p) p (last p)"
    unfolding alt_dist.alt_vwalk_bet_def
    using vw pne al ev by (simp add: Vwalk.vwalk_bet_def parity_simps)
qed
```

### γ-5. Bipartite: labels are sides, so projected copies walks are simple

```isabelle
lemma copies_walk_side:
  assumes q: "Vwalk.vwalk_bet (copies_dag (Graph.digraph_abs T)) w q z"
      and TG: "Graph.digraph_abs T ⊆ G"
      and B: "bipartite UG Xs Ys"
  shows "(label w = Odd ⟷ vtx w ∈ Xs) ⟶ (∀w' ∈ set q. label w' = Odd ⟷ vtx w' ∈ Xs)"
  using q
proof (induction rule: induct_vwalk_bet)
  case (path1 v)
  show ?case by simp
next
  case (path2 v v' vs b)
  show ?case
  proof
    assume hv: "label v = Odd ⟷ vtx v ∈ Xs"
    have hv': "label v' = Odd ⟷ vtx v' ∈ Xs"
      using path2(1)
    proof (cases rule: copies_dag_cases)
      case (1 u x)
      ― ‹v = Vtx Odd x (so x ∈ Xs), v' = Vtx Even u: the edge forces u ∉ Xs›
      have uxG: "(u, x) ∈ G" using 1(3) TG by blast
      have e: "{u, x} ∈ UG" using uxG by (simp add: G_char)
      have "x ∈ Xs" using hv 1(1) by simp
      hence "u ∈ Ys - Xs" by (rule bipartite_edgeD(3)[OF e B])
      thus ?thesis using 1(2) by simp
    next
      case (2 u x)
      ― ‹v = Vtx Even x (so x ∉ Xs, hence x ∈ Ys), v' = Vtx Odd u: u ∈ Xs›
      have uxG: "(u, x) ∈ G" using 2(3) TG by blast
      have e: "{u, x} ∈ UG" using uxG by (simp add: G_char)
      have xnX: "x ∉ Xs" using hv 2(1) by simp
      have xV: "x ∈ Vs UG" by (rule edges_are_Vs_2[OF e])
      have "x ∈ Ys" using xnX xV bipartite_vs_subset[OF B] by blast
      hence "u ∈ Xs - Ys" by (rule bipartite_edgeD(4)[OF e B])
      thus ?thesis using 2(2) by simp
    qed
    have rest: "∀w' ∈ set (v' # vs). label w' = Odd ⟷ vtx w' ∈ Xs"
      by (rule mp[OF path2(3) hv'])
    show "∀w' ∈ set (v # v' # vs). label w' = Odd ⟷ vtx w' ∈ Xs"
      using hv rest by simp
  qed
qed

lemma copies_walk_distinct_vtx:
  assumes V: "valid_alt_BFS_DAG T dists VisE VisO"
      and q: "Vwalk.vwalk_bet (copies_dag (Graph.digraph_abs T)) w q z"
  shows "distinct (map vtx q)"
proof -
  note P = valid_alt_BFS_DAG_props[OF BFS_axiom_hk V]
  have dq: "distinct q"
    using conjunct1[OF vwalk_bet_level_distinct[OF q copies_lev_decrease[OF BFS_axiom_hk V]]] .
  have wmem: "w ∈ dVs (copies_dag (Graph.digraph_abs T))"
    using vwalk_bet_in_dVs[OF q] hd_of_vwalk_bet''[OF q] by blast
  have wT: "vtx w ∈ dVs (Graph.digraph_abs T)" by (rule copies_dag_vtx_dVs[OF wmem])
  have wV: "vtx w ∈ Vs UG" using wT dVs_subset[OF P(1)] dVs_G_Vs by blast
  obtain Z Z' where B: "bipartite UG Z Z'" and Zw: "label w = Odd ⟷ vtx w ∈ Z"
  proof (cases "label w = Odd ⟷ vtx w ∈ X")
    case True
    show thesis by (rule that[OF bip True])
  next
    case False
    have disj: "X ∩ Y = {}" using bip by (simp add: bipartite_def)
    have XY: "vtx w ∈ X ∪ Y" using wV bipartite_vs_subset[OF bip] by blast
    have "label w = Odd ⟷ vtx w ∈ Y" using False disj XY by blast
    then show thesis by (rule that[OF bipartite_commute[OF bip]])
  qed
  have side: "∀w' ∈ set q. label w' = Odd ⟷ vtx w' ∈ Z"
    by (rule mp[OF copies_walk_side[OF q P(1) B] Zw])
  have inj: "inj_on vtx (set q)"
  proof (rule inj_onI)
    fix a b assume ab: "a ∈ set q" "b ∈ set q" "vtx a = vtx b"
    have "label a = Odd ⟷ label b = Odd" using side ab by auto
    hence lab: "label a = label b" by (cases "label a"; cases "label b") simp_all
    show "a = b" using lab ab(3) by (cases a; cases b) simp_all
  qed
  show ?thesis using dq inj by (simp add: distinct_map)
qed
```

### γ-6. The oracle theorems

```isabelle
theorem copies_walk_augmenting:
  assumes V: "valid_alt_BFS_DAG T dists VisE VisO"
      and t: "t ∈ t_set srcs"
      and q: "Vwalk.vwalk_bet (copies_dag (Graph.digraph_abs T)) (Vtx Odd t) q z"
      and z0: "copies_lev z = 0"
  shows "graph_augmenting_path UG M (rev (map vtx q))"
        "enat (length q - 1) = altd_G Odd t"
proof -
  note W = copies_walk_from_odd[OF V q z0]
  let ?P = "rev (map vtx q)"
  have vb: "Vwalk.vwalk_bet G (vtx z) ?P t"
    using W(2) by (simp add: alt_dist.alt_vwalk_bet_def)
  have ev: "even (length ?P)"
    using W(2) by (simp add: alt_dist.alt_vwalk_bet_def parity_simps)
  have vw: "Vwalk.vwalk G ?P" using vb by (simp add: Vwalk.vwalk_bet_def)
  have pne: "?P ≠ []" using vb by (simp add: Vwalk.vwalk_bet_def)
  have pth: "path UG ?P" by (rule vwalk_G_path[OF vw])
  have ap: "alt_path M ?P" by (rule alt_walk_alt_path[OF W(2)])
  have dst: "distinct ?P" using copies_walk_distinct_vtx[OF V q] by simp
  have hd: "vtx z = hd ?P" by (rule hd_of_vwalk_bet'[OF vb])
  have lst: "t = last ?P" by (rule last_of_vwalk_bet[OF vb])
  have l0: "length ?P ≠ 0" using pne by simp
  have len2: "2 ≤ length ?P" using l0 ev by presburger
  have hdM: "vtx z ∉ Vs M" using W(1) by (simp add: srcs_free)
  have lM: "t ∉ Vs M" using t by (simp add: srcs_free)
  have aug: "matching_augmenting_path M ?P"
    unfolding matching_augmenting_path_def
  proof (intro conjI)
    show "2 ≤ length ?P" by (rule len2)
    show "alt_list (λe. e ∉ M) (λe. e ∈ M) (edges_of_path ?P)" by (rule ap)
    show "hd ?P ∉ Vs M" using hdM hd by simp
    show "last ?P ∉ Vs M" using lM lst by simp
  qed
  show "graph_augmenting_path UG M ?P" using pth dst aug by blast
  show "enat (length q - 1) = altd_G Odd t" by (rule W(3))
qed

theorem aug_path_copies_start:
  assumes V: "valid_alt_BFS_DAG T dists VisE VisO"
      and A: "graph_augmenting_path UG M p"
  obtains t q z where "t ∈ t_set srcs"
      "Vwalk.vwalk_bet (copies_dag (Graph.digraph_abs T)) (Vtx Odd t) q z"
      "copies_lev z = 0"
proof -
  note P = valid_alt_BFS_DAG_props[OF BFS_axiom_hk V]
  note W = aug_path_alt_walk[OF A]
  have tO: "last p ∈ t_set VisO" using P(6) W(1) W(3) by blast
  have mem: "Vtx Odd (last p) ∈ dVs (copies_dag (Graph.digraph_abs T))"
    by (rule VisO_copies_dVs[OF V tO])
  obtain q z where qz:
      "Vwalk.vwalk_bet (copies_dag (Graph.digraph_abs T)) (Vtx Odd (last p)) q z"
      "copies_lev z = 0"
    by (rule copies_reach_zero[OF BFS_axiom_hk V mem])
  show thesis by (rule that[OF W(2) qz])
qed

theorem aug_path_iff_free_odd_copy:
  assumes V: "valid_alt_BFS_DAG T dists VisE VisO"
  shows "(∃p. graph_augmenting_path UG M p) ⟷
         (∃t ∈ t_set srcs. Vtx Odd t ∈ dVs (copies_dag (Graph.digraph_abs T)))"
proof
  assume "∃p. graph_augmenting_path UG M p"
  then obtain p where p: "graph_augmenting_path UG M p" by blast
  obtain t q z where tqz: "t ∈ t_set srcs"
      "Vwalk.vwalk_bet (copies_dag (Graph.digraph_abs T)) (Vtx Odd t) q z"
      "copies_lev z = 0"
    by (rule aug_path_copies_start[OF V p])
  have "Vtx Odd t ∈ dVs (copies_dag (Graph.digraph_abs T))"
    by (rule vwalk_bet_in_vertices[OF tqz(2) hd_of_vwalk_bet''[OF tqz(2)]])
  thus "∃t ∈ t_set srcs. Vtx Odd t ∈ dVs (copies_dag (Graph.digraph_abs T))"
    using tqz(1) by blast
next
  assume "∃t ∈ t_set srcs. Vtx Odd t ∈ dVs (copies_dag (Graph.digraph_abs T))"
  then obtain t where t: "t ∈ t_set srcs"
      "Vtx Odd t ∈ dVs (copies_dag (Graph.digraph_abs T))" by blast
  obtain q z where qz:
      "Vwalk.vwalk_bet (copies_dag (Graph.digraph_abs T)) (Vtx Odd t) q z"
      "copies_lev z = 0"
    by (rule copies_reach_zero[OF BFS_axiom_hk V t(2)])
  show "∃p. graph_augmenting_path UG M p"
    using copies_walk_augmenting(1)[OF V t(1) qz] by blast
qed

corollary BFS_aug_path_iff:
  "(∃p. graph_augmenting_path UG M p) ⟷
   (∃t ∈ t_set srcs.
      Vtx Odd t ∈ dVs (copies_dag (Graph.digraph_abs (parents (BFS initial_state)))))"
  by (rule aug_path_iff_free_odd_copy[OF BFS_valid_DAG[OF BFS_axiom_hk]])

corollary BFS_copies_walk_augmenting:
  assumes "t ∈ t_set srcs"
      and "Vwalk.vwalk_bet (copies_dag (Graph.digraph_abs (parents (BFS initial_state))))
             (Vtx Odd t) q z"
      and "copies_lev z = 0"
  shows "graph_augmenting_path UG M (rev (map vtx q))"
  by (rule copies_walk_augmenting(1)[OF BFS_valid_DAG[OF BFS_axiom_hk] assms])
```

Notes: in `copies_walk_augmenting`, if `simp` normalises `hd (rev …)` /
`last (rev …)` differently in fact and goal, close those two `show`s with
`by (simp only: hd[symmetric] …)`-style rewrites or `subst`. The `alt_list`
`show` must match the unfolded conjunct literally (it is the expansion of
`alt_path M ?P`); if not, `by (fact ap)` / `using ap by simp`.

**Gate 2 deliverable:** γ-0…γ-6 PIDE-green; ASCII 0; batch green; STOP and
report with `thm copies_walk_augmenting aug_path_iff_free_odd_copy
BFS_aug_path_iff` output (showing the exported premises).

## Gate structure and revert criteria

| Gate | Phases | Theory | Depends on |
|---|---|---|---|
| 1 | β-0 … β-4 (generic read-off) | `Hopcroft_Karp.thy` | Top_Loop |
| 2 | γ-0 … γ-6 (bipartite oracle) | `Hopcroft_Karp.thy` | Gate 1, Berge |
| 3 | δ-0 … δ-6 (disjoint augmentation, abstract loop) | `HK_Top_Loop.thy` | Berge only |
| 4 | ε-0 … ε-5 (disjoint-path search) | `HK_Search.thy` | IDFS only |
| 5 | ζ-0 … ζ-6 (concrete phase on red–black trees) | `HK_Phase.thy` | Gates 2–4, Alt_BFS_Example, DDFS_Example, read-only interim |
| 6 | η-1 … η-3 (verified executable algorithm, demo) | `HK_Example.thy` | Gate 5 |

- The coder STOPS after each gate; the orchestrator verifies (PIDE,
  comment-aware sorry/metis/smt scan, unsorted statement-fidelity diff
  against this plan, ASCII, batch build) before the next gate starts.
- Gates 3 and 4 do not depend on Gates 1–2 and may run in either order.
- If a crux lemma resists after honest REPL/sledgehammer attempts —
  `copies_walk_alt_walk` (β-3), `copies_walk_side` (γ-5),
  `aug_path_disjoint_preserved` (δ-1), `disjoint_search_correct` (ε-4),
  `CG_abs`/`CG_layered` (ζ-5) — stop and report the exact stuck goal.
  Do NOT add axioms, do NOT touch `Alt_BFS.thy`, `Top_Loop.thy`, `IDFS.thy`,
  `DDFS_Example.thy` or the interim read-only theory.
- Statement changes (beyond qualifiers, ASCII, and the recon-dependent
  argument orders flagged in ζ-0 and η-1) need orchestrator approval.
- Gates 5–6 contain more recon-dependent plumbing than Gates 1–4 (constant
  argument orders of interpreted constants, code equations). Their Isar
  skeletons fix the STATEMENTS and the proof route; where a proof is given as
  a `― ‹…›` outline, the coder writes the Isar from the outline and the cited
  facts, REPL-gating every closer.

---

## Phase δ — augmentation along disjoint paths and the abstract top loop (Gate 3)

New theory `Hopcroft_Karp/HK_Top_Loop.thy`. It depends only on
`Basic_Matching.Berge` — not on alt-BFS, `Top_Loop` or Gates 1–2 — so Gate 3
can be done before, after or independently of them. Add it to
`Hopcroft_Karp/ROOT` (`theories HK_Top_Loop Hopcroft_Karp`). Outside the BFS
locale, `matching` is the Berge constant and `G` is free, so no
qualification is needed here.

The loop is stated over an abstract matching REPRESENTATION `'m` (abstraction
`matching_abs`, invariant `matching_invar`, single-path `augment`), exactly
as `hungarian_loop` (Hungarian_Method_Top_Loop.thy:308–337). In Gate 6 the
representation becomes the mate function of
`Matching_Augmentation_Executable` (`augment_impl`, `augmentation_correct`).
The search procedure enters only through the phase contract (HK-D8): this
gate knows nothing about alt-BFS or the incremental DFS.

### δ-0. Skeleton + recon

```isabelle
theory HK_Top_Loop
  imports "Basic_Matching.Berge"
begin

section ‹Augmenting along vertex-disjoint augmenting paths›
― ‹δ-1, δ-2›

section ‹The abstract Hopcroft-Karp loop›
― ‹δ-3 … δ-6›

end
```
Recon (`thm`): `Berge Berge_2' new_matching_plus_one rematch_atl_path_Vs_change
aug_paths_are_even alt_list_cong_1 alt_list_cong_2 in_symmetric_diff_iff
finite_symm_diff edges_of_path_Vs in_edges_of_path_split finite_Vs_then_finite
max_card_matching_def matching_augmenting_path_def`.

### δ-1. One augmentation keeps every disjoint augmenting path augmenting

```isabelle
lemma edge_of_disjoint_path:
  assumes e: "e ∈ set (edges_of_path q)" and disj: "set p ∩ set q = {}"
  shows "e ∉ set (edges_of_path p)"
proof
  assume ep: "e ∈ set (edges_of_path p)"
  obtain a b where ab: "e = {a, b}"
    using in_edges_of_path_split[OF e] by blast
  have aq: "a ∈ set q" using e ab edges_of_path_Vs[of q] by (auto simp: Vs_def)
  have ap: "a ∈ set p" using ep ab edges_of_path_Vs[of p] by (auto simp: Vs_def)
  show False using aq ap disj by blast
qed

lemma aug_path_disjoint_preserved:
  assumes M: "matching M"
      and p: "graph_augmenting_path G M p"
      and q: "graph_augmenting_path G M q"
      and disj: "set p ∩ set q = {}"
  shows "graph_augmenting_path G (M ⊕ set (edges_of_path p)) q"
proof -
  let ?M' = "M ⊕ set (edges_of_path p)"
  have qa: "matching_augmenting_path M q" "path G q" "distinct q" using q by simp_all
  have pa: "matching_augmenting_path M p" "distinct p" using p by simp_all
  have same: "⋀e. e ∈ set (edges_of_path q) ⟹ (e ∈ ?M') = (e ∈ M)"
    using edge_of_disjoint_path[OF _ disj] by (auto simp: in_symmetric_diff_iff)
  have qlen: "2 ≤ length q" and qalt: "alt_path M q"
    and qh: "hd q ∉ Vs M" and ql: "last q ∉ Vs M"
    using qa(1) by (simp_all add: matching_augmenting_path_def)
  have alt1: "alt_list (λe. e ∉ ?M') (λe. e ∈ M) (edges_of_path q)"
    by (rule alt_list_cong_2[OF qalt]) (use same in auto)
  have alt2: "alt_list (λe. e ∉ ?M') (λe. e ∈ ?M') (edges_of_path q)"
    by (rule alt_list_cong_1[OF alt1]) (use same in auto)
  have palt: "alt_path M p" and plen: "2 ≤ length p"
    using pa(1) by (simp_all add: matching_augmenting_path_def)
  have pev: "even (length p)" by (rule aug_paths_are_even[OF pa(1)])
  have VsM': "Vs ?M' = {hd p, last p} ∪ Vs M"
    using rematch_atl_path_Vs_change[OF M palt pa(2) plen] pev by simp
  have pne: "p ≠ []" using plen by auto
  have qne: "q ≠ []" using qlen by auto
  have qh': "hd q ∉ Vs ?M'"
    using VsM' qh disj hd_in_set[OF qne] hd_in_set[OF pne] last_in_set[OF pne] by blast
  have ql': "last q ∉ Vs ?M'"
    using VsM' ql disj last_in_set[OF qne] hd_in_set[OF pne] last_in_set[OF pne] by blast
  have "matching_augmenting_path ?M' q"
    unfolding matching_augmenting_path_def using qlen alt2 qh' ql' by simp
  then show ?thesis using qa(2,3) by simp
qed
```

### δ-2. Augmenting along a list of pairwise vertex-disjoint augmenting paths

```isabelle
definition augment_all :: "'a set set ⇒ 'a list list ⇒ 'a set set" where
  "augment_all M ps = foldl (λN p. N ⊕ set (edges_of_path p)) M ps"

lemma augment_all_simps[simp]:
  "augment_all M [] = M"
  "augment_all M (p # ps) = augment_all (M ⊕ set (edges_of_path p)) ps"
  by (simp_all add: augment_all_def)

lemma augment_all_correct:
  assumes "graph_matching G M" "finite M"
      and "∀p ∈ set ps. graph_augmenting_path G M p"
      and "sorted_wrt (λp q. set p ∩ set q = {}) ps"
  shows "graph_matching G (augment_all M ps) ∧ finite (augment_all M ps) ∧
         card (augment_all M ps) = card M + length ps"
  using assms
proof (induction ps arbitrary: M)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  let ?M' = "M ⊕ set (edges_of_path p)"
  have p: "graph_augmenting_path G M p" using Cons.prems(3) by simp
  have gm': "graph_matching G ?M'"
    by (rule Berge_2'[of M p G]) (use p Cons.prems(1,2) in auto)
  have fin': "finite ?M'" by (rule finite_symm_diff[OF Cons.prems(2) finite_set])
  have card': "card M + 1 = card ?M'"
    by (rule new_matching_plus_one) (use p Cons.prems(2) in auto)
  have rest: "∀q ∈ set ps. graph_augmenting_path G ?M' q"
  proof
    fix q assume qin: "q ∈ set ps"
    have q: "graph_augmenting_path G M q" using Cons.prems(3) qin by simp
    have d: "set p ∩ set q = {}" using Cons.prems(4) qin by simp
    have mM: "matching M" using Cons.prems(1) by simp
    show "graph_augmenting_path G ?M' q"
      by (rule aug_path_disjoint_preserved[OF mM p q d])
  qed
  have sw: "sorted_wrt (λp q. set p ∩ set q = {}) ps" using Cons.prems(4) by simp
  have IH: "graph_matching G (augment_all ?M' ps) ∧ finite (augment_all ?M' ps) ∧
            card (augment_all ?M' ps) = card ?M' + length ps"
    by (rule Cons.IH[OF gm' fin' rest sw])
  show ?case using IH card' by simp
qed
```

### δ-3. The abstract loop: definitions locale + proof locale (Hungarian style)

Two locales, as in Hungarian_Method_Top_Loop.thy (`hungarian_loop_spec` holds
the definitions, `hungarian_loop` the assumptions and proofs). Definitions
live in an assumption-free locale so that their code equations are
unconditional; Gate 6 obtains the executable loop by a
`global_interpretation` of `hk_loop_defs` alone.

```isabelle
locale hk_loop_defs =
  fixes augment :: "'m ⇒ 'a list ⇒ 'm"
    and phase :: "'m ⇒ 'a list list"
begin

definition augment_list :: "'m ⇒ 'a list list ⇒ 'm" where
  "augment_list m ps = foldl augment m ps"

function (domintros) hk_loop :: "'m ⇒ 'm" where
  "hk_loop m = (if phase m = [] then m else hk_loop (augment_list m (phase m)))"
  by pat_completeness auto

partial_function (tailrec) hk_loop_impl :: "'m ⇒ 'm" where
  "hk_loop_impl m = (if phase m = [] then m else hk_loop_impl (augment_list m (phase m)))"

lemmas [code] = hk_loop_impl.simps augment_list_def

end

locale hk_loop_spec = hk_loop_defs augment phase
  for augment :: "'m ⇒ 'a list ⇒ 'm" and phase :: "'m ⇒ 'a list list" +
  fixes G :: "'a set set"
    and matching_invar :: "'m ⇒ bool" and matching_abs :: "'m ⇒ 'a set set"
  assumes G: "graph_invar G"
      and matching_invar_abs: "matching_invar m ⟹ graph_matching G (matching_abs m)"
      and augment_invar:
        "⟦matching_invar m; graph_augmenting_path G (matching_abs m) p⟧
           ⟹ matching_invar (augment m p)"
      and augment_abs:
        "⟦matching_invar m; graph_augmenting_path G (matching_abs m) p⟧
           ⟹ matching_abs (augment m p) = matching_abs m ⊕ set (edges_of_path p)"
      and phase_sound:
        "⟦matching_invar m; p ∈ set (phase m)⟧ ⟹ graph_augmenting_path G (matching_abs m) p"
      and phase_disjoint:
        "matching_invar m ⟹ sorted_wrt (λp q. set p ∩ set q = {}) (phase m)"
      and phase_complete:
        "⟦matching_invar m; ∃p. graph_augmenting_path G (matching_abs m) p⟧ ⟹ phase m ≠ []"
begin

lemma finite_abs: "matching_invar m ⟹ finite (matching_abs m)"
proof -
  assume inv: "matching_invar m"
  have sub: "matching_abs m ⊆ G" using matching_invar_abs[OF inv] by simp
  have finG: "finite G" by (rule finite_Vs_then_finite) (use G in simp)
  show "finite (matching_abs m)" by (rule finite_subset[OF sub finG])
qed

lemma card_abs_le: "matching_invar m ⟹ card (matching_abs m) ≤ card G"
proof -
  assume inv: "matching_invar m"
  have sub: "matching_abs m ⊆ G" using matching_invar_abs[OF inv] by simp
  have finG: "finite G" by (rule finite_Vs_then_finite) (use G in simp)
  show ?thesis by (rule card_mono[OF finG sub])
qed

lemma augment_list_correct:
  assumes "matching_invar m"
      and "∀p ∈ set ps. graph_augmenting_path G (matching_abs m) p"
      and "sorted_wrt (λp q. set p ∩ set q = {}) ps"
  shows "matching_invar (augment_list m ps) ∧
         matching_abs (augment_list m ps) = augment_all (matching_abs m) ps"
  using assms
proof (induction ps arbitrary: m)
  case Nil
  then show ?case by (simp add: augment_list_def)
next
  case (Cons p ps)
  have p: "graph_augmenting_path G (matching_abs m) p" using Cons.prems(2) by simp
  have inv': "matching_invar (augment m p)" by (rule augment_invar[OF Cons.prems(1) p])
  have abs': "matching_abs (augment m p) = matching_abs m ⊕ set (edges_of_path p)"
    by (rule augment_abs[OF Cons.prems(1) p])
  have mm: "matching (matching_abs m)" using matching_invar_abs[OF Cons.prems(1)] by simp
  have rest: "∀q ∈ set ps. graph_augmenting_path G (matching_abs (augment m p)) q"
  proof
    fix q assume qin: "q ∈ set ps"
    have q: "graph_augmenting_path G (matching_abs m) q" using Cons.prems(2) qin by simp
    have d: "set p ∩ set q = {}" using Cons.prems(3) qin by simp
    show "graph_augmenting_path G (matching_abs (augment m p)) q"
      unfolding abs' by (rule aug_path_disjoint_preserved[OF mm p q d])
  qed
  have sw: "sorted_wrt (λp q. set p ∩ set q = {}) ps" using Cons.prems(3) by simp
  have IH: "matching_invar (augment_list (augment m p) ps) ∧
            matching_abs (augment_list (augment m p) ps) = augment_all (matching_abs (augment m p)) ps"
    by (rule Cons.IH[OF inv' rest sw])
  show ?case using IH abs' by (simp add: augment_list_def)
qed
```
(The `hk_loop_spec` context stays open through δ-6.)

### δ-4. Termination

```isabelle
lemma hk_loop_dom_aux:
  assumes "matching_invar m" "n = card G - card (matching_abs m)"
  shows "hk_loop_dom m"
  using assms
proof (induction n arbitrary: m rule: less_induct)
  case (less n)
  show ?case
  proof (rule hk_loop.domintros)
    assume ne: "phase m ≠ []"
    let ?m' = "augment_list m (phase m)"
    have sound: "∀p ∈ set (phase m). graph_augmenting_path G (matching_abs m) p"
      using phase_sound[OF less.prems(1)] by blast
    have disj: "sorted_wrt (λp q. set p ∩ set q = {}) (phase m)"
      by (rule phase_disjoint[OF less.prems(1)])
    have C: "matching_invar ?m' ∧ matching_abs ?m' = augment_all (matching_abs m) (phase m)"
      by (rule augment_list_correct[OF less.prems(1) sound disj])
    have gm: "graph_matching G (matching_abs m)" by (rule matching_invar_abs[OF less.prems(1)])
    have A: "card (augment_all (matching_abs m) (phase m)) = card (matching_abs m) + length (phase m)"
      using augment_all_correct[OF gm finite_abs[OF less.prems(1)] sound disj] by blast
    have eq: "card (matching_abs ?m') = card (matching_abs m) + length (phase m)"
      using C A by simp
    have le: "card (matching_abs ?m') ≤ card G" by (rule card_abs_le[OF conjunct1[OF C]])
    have len: "1 ≤ length (phase m)" using ne by (cases "phase m") auto
    have lt: "card G - card (matching_abs ?m') < n"
      using less.prems(2) eq le len by presburger
    show "hk_loop_dom ?m'" by (rule less.IH[OF lt conjunct1[OF C] refl])
  qed
qed

lemma hk_loop_dom: "matching_invar m ⟹ hk_loop_dom m"
  using hk_loop_dom_aux by blast
```

### δ-5. Invariant, exit condition, implementation equation

```isabelle
lemma hk_loop_invar:
  assumes "hk_loop_dom m" "matching_invar m"
  shows "matching_invar (hk_loop m)"
  using assms
proof (induction rule: hk_loop.pinduct)
  case (1 m)
  show ?case
  proof (cases "phase m = []")
    case True
    then show ?thesis using 1(3) by (simp add: hk_loop.psimps[OF 1(1)])
  next
    case False
    have sound: "∀p ∈ set (phase m). graph_augmenting_path G (matching_abs m) p"
      using phase_sound[OF 1(3)] by blast
    have inv': "matching_invar (augment_list m (phase m))"
      using augment_list_correct[OF 1(3) sound phase_disjoint[OF 1(3)]] by blast
    have "matching_invar (hk_loop (augment_list m (phase m)))" by (rule 1(2)[OF False inv'])
    then show ?thesis using False by (simp add: hk_loop.psimps[OF 1(1)])
  qed
qed

lemma hk_loop_final:
  assumes "hk_loop_dom m"
  shows "phase (hk_loop m) = []"
  using assms
proof (induction rule: hk_loop.pinduct)
  case (1 m)
  show ?case
  proof (cases "phase m = []")
    case True
    then show ?thesis by (simp add: hk_loop.psimps[OF 1(1)])
  next
    case False
    then show ?thesis using 1(2)[OF False] by (simp add: hk_loop.psimps[OF 1(1)])
  qed
qed

lemma hk_loop_impl_same:
  assumes "hk_loop_dom m"
  shows "hk_loop_impl m = hk_loop m"
  using assms
proof (induction rule: hk_loop.pinduct)
  case (1 m)
  have L: "hk_loop m = (if phase m = [] then m else hk_loop (augment_list m (phase m)))"
    by (rule hk_loop.psimps[OF 1(1)])
  have R: "hk_loop_impl m = (if phase m = [] then m else hk_loop_impl (augment_list m (phase m)))"
    by (rule hk_loop_impl.simps)
  show ?case
  proof (cases "phase m = []")
    case True
    then show ?thesis using L R by simp
  next
    case False
    then show ?thesis using L R 1(2)[OF False] by simp
  qed
qed
```
(Never `simp add: hk_loop_impl.simps` — it unfolds the recursive call forever;
the `R` instance above is ground and safe.)

### δ-6. Maximum cardinality

```isabelle
theorem hk_loop_correct:
  assumes "matching_invar m"
  shows "matching_invar (hk_loop m)" "max_card_matching G (matching_abs (hk_loop m))"
proof -
  have dom: "hk_loop_dom m" by (rule hk_loop_dom[OF assms])
  show inv: "matching_invar (hk_loop m)" by (rule hk_loop_invar[OF dom assms])
  have gm: "graph_matching G (matching_abs (hk_loop m))" by (rule matching_invar_abs[OF inv])
  have fin: "finite (matching_abs (hk_loop m))" by (rule finite_abs[OF inv])
  have none: "phase (hk_loop m) = []" by (rule hk_loop_final[OF dom])
  have noaug: "¬ (∃p. graph_augmenting_path G (matching_abs (hk_loop m)) p)"
    using phase_complete[OF inv] none by blast
  show "max_card_matching G (matching_abs (hk_loop m))"
    unfolding max_card_matching_def
  proof (intro conjI allI impI)
    show "matching_abs (hk_loop m) ⊆ G" using gm by simp
    show "matching (matching_abs (hk_loop m))" using gm by simp
  next
    fix M' assume M': "M' ⊆ G ∧ matching M'"
    show "card M' ≤ card (matching_abs (hk_loop m))"
    proof (rule ccontr)
      assume "¬ card M' ≤ card (matching_abs (hk_loop m))"
      hence ex: "∃M' ⊆ G. matching M' ∧ card (matching_abs (hk_loop m)) < card M'"
        using M' by auto
      have mH: "matching (matching_abs (hk_loop m))" using gm by simp
      have sH: "matching_abs (hk_loop m) ⊆ G" using gm by simp
      have dbl: "dblton_graph G" and fV: "finite (Vs G)" using G by simp_all
      have "∃p. matching_augmenting_path (matching_abs (hk_loop m)) p ∧ path G p ∧ distinct p"
        using Berge[OF fin mH sH dbl fV] ex by blast
      then show False using noaug by blast
    qed
  qed
qed

corollary hk_loop_impl_correct:
  assumes "matching_invar m"
  shows "matching_invar (hk_loop_impl m)" "max_card_matching G (matching_abs (hk_loop_impl m))"
  using hk_loop_correct[OF assms] hk_loop_impl_same[OF hk_loop_dom[OF assms]] by simp_all

end ― ‹hk_loop_spec›
```

**Gate 3 deliverable:** `HK_Top_Loop.thy` PIDE-green, in ROOT, ASCII 0,
batch green; report `thm hk_loop_correct hk_loop_impl_correct
augment_all_correct`.

---

## Phase ε — searching for vertex-disjoint paths with the incremental DFS (Gate 4)

New theory `Hopcroft_Karp/HK_Search.thy`, importing only
`Micali_Vazirani.IDFS`. It is generic: any graph satisfying
`layered_graph_input` (the `IDFS_witness` locale), any target predicate `P`,
any list of roots, and a blocking function `blk` (which copies to add to the
avoid set after a path has been found). It knows nothing about matchings;
Gate 5 instantiates it with the copies graph. Add it to `Hopcroft_Karp/ROOT`
(`theories HK_Top_Loop HK_Search Hopcroft_Karp …`).

The search calls `IDFS_impl P avoid [r] vis` for each root `r` in turn. A
found path `p` (stack, top first: `hd p` satisfies `P`, `last p = r`) is
recorded, and `blk p` is added to the avoid set. The visited set is passed
from one call to the next, so no vertex is explored twice. Maximality (needed
only for the √|V| bound) is NOT part of this gate.

### ε-0. Skeleton + recon

```isabelle
theory HK_Search
  imports Micali_Vazirani.IDFS
begin

section ‹Generic walk lemmas›
― ‹ε-1, and the function of ε-3›

context IDFS_witness
begin
― ‹ε-2 … ε-5›
end

end
```
Recon (`thm`, inside `context IDFS_witness`): `IDFS_sound_1 IDFS_sound_2
IDFS_sound_3 IDFS_sound_6 IDFS_sound_7 IDFS_sound_8 IDFS_vis_works_1
IDFS_vis_works_3 IDFS_vis_works_4 IDFS_closed_None IDFS_complete_w
IDFS_dVs_bound set_ops.set_union set_ops.invar_union
Graph.vset.set.set_empty Graph.vset.set.invar_empty`. Confirm that each
`IDFS_*` fact carries the six context premises first, in this order:
`dpath (Graph.digraph_abs G) (rev p)`, `distinct p`, `vset_inv avoid`,
`vset_inv vis`, `t_set avoid ⊆ dVs …`, `t_set vis ⊆ dVs …` (IDFS.thy:68–73).
If the order differs, adapt the `A` bundle in `root_call` only.

### ε-1. Two generic walk lemmas (global)

```isabelle
lemma vwalk_bet_closed:
  assumes "Vwalk.vwalk_bet E u q v" "u ∈ S"
      and closed: "⋀a b. a ∈ S ⟹ (a, b) ∈ E ⟹ b ∈ S"
  shows "v ∈ S"
  using assms(1,2)
proof (induction rule: induct_vwalk_bet)
  case (path1 x)
  then show ?case by simp
next
  case (path2 x x' xs b)
  ― ‹path2(1): edge, path2(2): tail walk, path2(3): IH, path2(4): x ∈ S›
  have "x' ∈ S" by (rule closed[OF path2(4) path2(1)])
  then show ?case by (rule path2(3))
qed

lemma found_vwalk_bet:
  assumes "Vwalk.vwalk E (rev p)" "p ≠ []"
  shows "Vwalk.vwalk_bet E (last p) (rev p) (hd p)"
  using assms by (simp add: Vwalk.vwalk_bet_def hd_rev last_rev)
```

### ε-2. Preconditions and one root call

```isabelle
definition "search_pre avoid vis ⟷
  vset_inv avoid ∧ vset_inv vis ∧
  t_set avoid ⊆ dVs (Graph.digraph_abs G) ∧ t_set vis ⊆ dVs (Graph.digraph_abs G)"

lemma search_pre_empty: "search_pre vset_empty vset_empty"
  by (simp add: search_pre_def Graph.vset.set.invar_empty Graph.vset.set.set_empty)

lemma root_call:
  assumes pre: "search_pre avoid vis"
      and r: "r ∈ dVs (Graph.digraph_abs G)"
      and call: "IDFS_impl P avoid [r] vis = (res, vis')"
  shows "vset_inv vis'"
    and "t_set vis' ⊆ dVs (Graph.digraph_abs G)"
    and "t_set vis ⊆ t_set vis'"
    and "res = None ⟹ r ∉ t_set avoid ⟹ r ∈ t_set vis'"
    and "res = None ⟹ v ∈ t_set vis' - t_set vis ⟹ (v, w) ∈ Graph.digraph_abs G
           ⟹ w ∈ t_set avoid ∪ t_set vis'"
    and "v ∈ t_set vis' - t_set vis ⟹ ¬ P v"
    and "res = Some p' ⟹
           dpath (Graph.digraph_abs G) (rev p') ∧ p' ≠ [] ∧ distinct p' ∧ P (hd p') ∧
           last p' = r ∧ set p' ∩ (t_set avoid ∪ t_set vis') = {}"
proof -
  have r1: "dpath (Graph.digraph_abs G) [r]" by (rule vwalk1[OF r])
  have pp: "dpath (Graph.digraph_abs G) (rev [r])" using r1 by simp
  have pd: "distinct [r]" by simp
  have i1: "vset_inv avoid" "vset_inv vis"
    and d1: "t_set avoid ⊆ dVs (Graph.digraph_abs G)" "t_set vis ⊆ dVs (Graph.digraph_abs G)"
    using pre by (simp_all add: search_pre_def)
  note A = pp pd i1 d1
  show "vset_inv vis'" by (rule IDFS_vis_works_4[OF A call])
  show "t_set vis' ⊆ dVs (Graph.digraph_abs G)" by (rule IDFS_dVs_bound[OF A call])
  show "t_set vis ⊆ t_set vis'" by (rule IDFS_vis_works_3[OF A call])
  show "r ∈ t_set vis'" if "res = None" "r ∉ t_set avoid"
    using IDFS_complete_w[OF A call[unfolded that(1)]] that(2) by simp
  show "w ∈ t_set avoid ∪ t_set vis'"
    if "res = None" "v ∈ t_set vis' - t_set vis" "(v, w) ∈ Graph.digraph_abs G"
    by (rule IDFS_closed_None[OF A call[unfolded that(1)] that(2,3)])
  show "¬ P v" if "v ∈ t_set vis' - t_set vis"
    by (rule IDFS_vis_works_1[OF A call that])
  show "dpath (Graph.digraph_abs G) (rev p') ∧ p' ≠ [] ∧ distinct p' ∧ P (hd p') ∧
        last p' = r ∧ set p' ∩ (t_set avoid ∪ t_set vis') = {}"
    if "res = Some p'"
  proof -
    note c = call[unfolded that]
    have s1: "dpath (Graph.digraph_abs G) (rev p')" by (rule IDFS_sound_1[OF A c])
    have s7: "p' ≠ []" by (rule IDFS_sound_7[OF A c])
    have s2: "distinct p'" by (rule IDFS_sound_2[OF A c])
    have s8: "P (hd p')" by (rule IDFS_sound_8[OF A c])
    have s6: "last [r] = last p'" by (rule IDFS_sound_6[OF A c]) simp
    have s3: "(set p' - set (tl [r])) ∩ (t_set avoid ∪ t_set vis') = {}"
      by (rule IDFS_sound_3[OF A c])
    show ?thesis using s1 s7 s2 s8 s6 s3 by simp
  qed
qed
```
(`vwalk1` is the singleton introduction rule of `Vwalk.vwalk`; qualify as
`Vwalk.vwalk1` if needed. `dpath` is DDFS's abbreviation for `Vwalk.vwalk`.)

### ε-3. The search

The recursion is a plain global function, parameterised by the union
operation, the blocking function and the single-root search `step`. It lives
OUTSIDE every locale, so its equations are unconditional and Gate 6 can
generate code for it. Inside `IDFS_witness` it is used through an
abbreviation with `step = IDFS_impl P`. Put the `fun` in section "Generic walk
lemmas", before `context IDFS_witness`; put the abbreviation inside the
context.

```isabelle
fun disjoint_search_gen ::
  "('s ⇒ 's ⇒ 's) ⇒ ('v list ⇒ 's) ⇒ ('s ⇒ 'v list ⇒ 's ⇒ 'v list option × 's)
     ⇒ 's ⇒ 's ⇒ 'v list ⇒ 'v list list" where
  "disjoint_search_gen un blk step avoid vis [] = []"
| "disjoint_search_gen un blk step avoid vis (r # rs) =
     (case step avoid [r] vis of
        (Some p, vis') ⇒ p # disjoint_search_gen un blk step (un avoid (blk p)) vis' rs
      | (None, vis') ⇒ disjoint_search_gen un blk step avoid vis' rs)"

― ‹inside context IDFS_witness:›
abbreviation "disjoint_search P blk ≡ disjoint_search_gen union blk (IDFS_impl P)"
```

### ε-4. Soundness and disjointness

```isabelle
theorem disjoint_search_correct:
  assumes pre: "search_pre avoid vis"
      and roots: "set rs ⊆ dVs (Graph.digraph_abs G)"
      and blk_inv: "⋀p. vset_inv (blk p)"
      and blk_dVs: "⋀p. t_set (blk p) ⊆ dVs (Graph.digraph_abs G)"
  shows "(∀p ∈ set (disjoint_search P blk avoid vis rs).
            dpath (Graph.digraph_abs G) (rev p) ∧ p ≠ [] ∧ distinct p ∧ P (hd p) ∧
            last p ∈ set rs ∧ set p ∩ t_set avoid = {}) ∧
         sorted_wrt (λp q. set q ∩ t_set (blk p) = {}) (disjoint_search P blk avoid vis rs)"
  using pre roots
proof (induction rs arbitrary: avoid vis)
  case Nil
  then show ?case by simp
next
  case (Cons r rs)
  have r: "r ∈ dVs (Graph.digraph_abs G)" and rs: "set rs ⊆ dVs (Graph.digraph_abs G)"
    using Cons.prems(2) by simp_all
  obtain res vis' where call: "IDFS_impl P avoid [r] vis = (res, vis')"
    by (cases "IDFS_impl P avoid [r] vis") auto
  note RC = root_call[OF Cons.prems(1) r call]
  have av_inv: "vset_inv avoid" and av_dVs: "t_set avoid ⊆ dVs (Graph.digraph_abs G)"
    using Cons.prems(1) by (simp_all add: search_pre_def)
  show ?case
  proof (cases res)
    case None
    have eq: "disjoint_search P blk avoid vis (r # rs) = disjoint_search P blk avoid vis' rs"
      using call None by simp
    have pre_v: "search_pre avoid vis'"
      using av_inv av_dVs RC(1,2) by (simp add: search_pre_def)
    have IH: "(∀p ∈ set (disjoint_search P blk avoid vis' rs).
                 dpath (Graph.digraph_abs G) (rev p) ∧ p ≠ [] ∧ distinct p ∧ P (hd p) ∧
                 last p ∈ set rs ∧ set p ∩ t_set avoid = {}) ∧
              sorted_wrt (λp q. set q ∩ t_set (blk p) = {}) (disjoint_search P blk avoid vis' rs)"
      by (rule Cons.IH[OF pre_v rs])
    show ?thesis using IH eq by auto
  next
    case (Some p)
    let ?avoid' = "union avoid (blk p)"
    have eq: "disjoint_search P blk avoid vis (r # rs) = p # disjoint_search P blk ?avoid' vis' rs"
      using call Some by simp
    have inv': "vset_inv ?avoid'" by (rule set_ops.invar_union[OF av_inv blk_inv])
    have set': "t_set ?avoid' = t_set avoid ∪ t_set (blk p)"
      by (rule set_ops.set_union[OF av_inv blk_inv])
    have pre': "search_pre ?avoid' vis'"
      using inv' set' av_dVs blk_dVs[of p] RC(1,2) by (simp add: search_pre_def)
    have IH: "(∀q ∈ set (disjoint_search P blk ?avoid' vis' rs).
                 dpath (Graph.digraph_abs G) (rev q) ∧ q ≠ [] ∧ distinct q ∧ P (hd q) ∧
                 last q ∈ set rs ∧ set q ∩ t_set ?avoid' = {}) ∧
              sorted_wrt (λp q. set q ∩ t_set (blk p) = {}) (disjoint_search P blk ?avoid' vis' rs)"
      by (rule Cons.IH[OF pre' rs])
    have pS: "dpath (Graph.digraph_abs G) (rev p) ∧ p ≠ [] ∧ distinct p ∧ P (hd p) ∧
              last p = r ∧ set p ∩ (t_set avoid ∪ t_set vis') = {}"
      by (rule RC(7)[OF Some])
    show ?thesis using IH pS set' eq by auto
  qed
qed
```
(`set_ops.invar_union`/`set_ops.set_union` are the `Set2` axioms at the
locale's vertex-set operations; DDFS.thy cites `set_ops.invar_union` 24 times.
The two final `auto` calls are REPL-gate candidates: if they are slow, split
the conjunction with `intro conjI ballI` and close each part separately.)

### ε-5. The first root succeeds whenever it can reach a target

```isabelle
lemma none_closed_reach:
  assumes pre: "search_pre avoid vis"
      and r: "r ∈ dVs (Graph.digraph_abs G)"
      and call: "IDFS_impl P avoid [r] vis = (None, vis')"
      and empt: "t_set avoid = {}" "t_set vis = {}"
      and walk: "Vwalk.vwalk_bet (Graph.digraph_abs G) r q z"
  shows "¬ P z"
proof -
  note RC = root_call[OF pre r call]
  have r_in: "r ∈ t_set vis'" using RC(4)[OF refl] empt by simp
  have closed: "⋀a b. a ∈ t_set vis' ⟹ (a, b) ∈ Graph.digraph_abs G ⟹ b ∈ t_set vis'"
    using RC(5)[OF refl] empt by blast
  have z_in: "z ∈ t_set vis'" by (rule vwalk_bet_closed[OF walk r_in closed])
  show "¬ P z" using RC(6) z_in empt by simp
qed

theorem disjoint_search_nonempty:
  assumes pre: "search_pre avoid vis"
      and empt: "t_set avoid = {}" "t_set vis = {}"
      and r: "r ∈ dVs (Graph.digraph_abs G)"
      and walk: "Vwalk.vwalk_bet (Graph.digraph_abs G) r q z"
      and Pz: "P z"
  shows "disjoint_search P blk avoid vis (r # rs) ≠ []"
proof -
  obtain res vis' where call: "IDFS_impl P avoid [r] vis = (res, vis')"
    by (cases "IDFS_impl P avoid [r] vis") auto
  show ?thesis
  proof (cases res)
    case None
    have "¬ P z" by (rule none_closed_reach[OF pre r call[unfolded None] empt walk])
    then show ?thesis using Pz by simp
  next
    case (Some p)
    then show ?thesis using call by simp
  qed
qed
```

**Gate 4 deliverable:** `HK_Search.thy` PIDE-green, in ROOT, ASCII 0, batch
green; report `thm disjoint_search_correct disjoint_search_nonempty`.

---

## Phase ζ — the concrete Hopcroft–Karp phase on red–black trees (Gate 5)

New theory `Hopcroft_Karp/HK_Phase.thy`. This is where the pieces meet:
alt-BFS (its executable instance `alt_bfs` from Alt_BFS_Example), the copies
graph built as an adjacency map, the disjoint search of Gate 4 with the
incremental DFS `IDFS_impl`, and the read-off of Gates 1–2. The result is a
phase function `hk_phase` and its contract (the three `phase_*` assumptions of
`hk_loop_spec`). Everything is stated for the red–black-tree representation,
so Gate 6 only has to interpret and run it.

Representation choices (all executable):
- *Input graph* (HK-D9): an adjacency map `Gin`, specified ONLY through the
  read-only vocabulary `RO.*` (`pair_graph_specs_read_only` at the red–black
  operations), together with a vertex list `vs`. The edge list
  `hk_edges Gin vs` enumerates `RO.digraph_abs Gin` once; all builders work
  on it. The undirected graph is `UG_of Gin`.
- *Matching*: the mate function, as a red–black map
  (`Matching_Augmentation_Executable`; instance `mate` below, mirroring
  Hungarian_Method_Instantiation.thy:20–25 and 599–606).
- *Alt-BFS digraphs*: `G.from_list` of filtered edge lists (`G` is the
  red–black `Pair_Graph_Specs` instance of Pair_Graph_RBT.thy;
  `G.from_list_correct` gives the abstraction and the invariants).
- *Copies graph*: `idfs.Graph.from_list` of the copies-edge list, at the
  operations of DDFS_Example's executable incremental DFS (`idfs`
  interpretation, DDFS_Example.thy:300–318), so that the search runs on the
  existing executable `avoid_impl_rbt`.
- *Levels*: read from the distance map, `hk_level D w = the_enat (the
  (lookup D w))`; agrees with `copies_lev` on the copies graph
  (`copies_lev_by_lookup`, Top_Loop).

### ζ-0. Skeleton + recon (record everything in progress.md first)

```isabelle
theory HK_Phase
  imports Hopcroft_Karp HK_Top_Loop HK_Search Pair_Graph_Specs_Read_Only
          Micali_Vazirani.Alt_BFS_Example Micali_Vazirani.DDFS_Example
          "Basic_Matching.Matching_Augmentation_Executable"
begin
end
```
Add `HK_Phase` to `Hopcroft_Karp/ROOT` after `Hopcroft_Karp`.
Recon:
(a) the merge loads (Alt_BFS_Example and DDFS_Example both define demo
constants — check for clashes);
(b) `term` of: `alt_bfs_impl`, `alt_bfs_initial_state`, `alt_bfs.BFS_axiom`,
`alt_bfs.valid_alt_BFS_DAG_impl`, `alt_bfs.copies_dag`, `alt_bfs.copies_lev`,
`IDFS_witness.IDFS_impl` (its exact argument order), `idfs.Graph.from_list`,
`idfs.vset_of_list` / `vset_of_list_rbt`;
(c) `thm` of: `alt_bfs.BFS_valid_DAG_impl alt_bfs.BFS_impl_same
alt_bfs.initial_state_props alt_bfs.copies_walk_augmenting
alt_bfs.aug_path_iff_free_odd_copy alt_bfs.copies_reach_zero
alt_bfs.valid_DAG_layered alt_bfs.copies_lev_by_lookup alt_bfs.copies_dag_dVs
alt_bfs.VisO_copies_dVs G.from_list_correct idfs.Graph.from_list_correct
idfs.vset_of_list_aux` — the HK-M1 lemmas appear as `alt_bfs.*` because
locale facts added after an interpretation are inherited by it;
(d) `lemma "alt_bfs.Graph.digraph_abs = G.digraph_abs" by (rule refl)` and
the same for `graph_inv`, `finite_graph`, `finite_vsets`, `neighbourhood`
(expected: syntactically equal, since both instances use the same map and
vertex-set operations apart from `vset_delete`, which these constants do not
use). If not, add one bridging lemma per constant, proved by unfolding.

### ζ-A. Amendment after the ζ-0 recon (2026-10-11, orchestrator-approved)

The recon refuted one assumption of this plan. Facts added to locale `BFS` by
`Top_Loop` and `Hopcroft_Karp` are NOT inherited by the `alt_bfs`
interpretation of Alt_BFS_Example: `alt_bfs.copies_walk_augmenting`,
`alt_bfs.copies_dag` etc. are undefined, while `alt_bfs.BFS_valid_DAG_impl`,
`alt_bfs.BFS_impl_same`, `alt_bfs.initial_state_props`, `alt_bfs.BFS_axiom_def`
and `alt_bfs.BFS_axioms` exist. Decisions:

1. **Re-interpret `BFS` in HK_Phase** at exactly the `alt_bfs` operations, so
   that every BFS fact (Alt_BFS, Top_Loop, Hopcroft_Karp) is available under
   one prefix:
   ```isabelle
   interpretation hkbfs: Alt_BFS.BFS
     where ‹the same where-clauses as alt_bfs in Alt_BFS_Example.thy:336–350›
     for matching unmatching srcs
     by (rule alt_bfs.BFS_axioms)
   ```
   Then `hkbfs.copies_walk_augmenting`, `hkbfs.copies_dag`, … replace the
   plan's `alt_bfs.*` names, and `hkbfs.BFS_impl` is the same term as
   `alt_bfs_impl`. FALLBACK if theory-level `interpretation … for` is
   rejected or the facts still do not appear: cite the global locale theorems
   as `BFS.foo[OF alt_bfs.BFS_axioms …]` and write the constants out in full
   (qualifier-level change only).
2. **Argument orders found by recon:** `alt_bfs.BFS_axiom` takes
   `srcs matching unmatching` (plus a `TYPE` argument) — the plan's
   `Mt Ut S` order is wrong; `valid_alt_BFS_DAG_impl` takes
   `srcs matching unmatching T dists VisE VisO`; `alt_bfs_impl` takes
   `matching unmatching state`; `IDFS_witness.IDFS_impl` takes
   `insert isin sel vset_empty union diff lookup G P avoid p vis` (as planned).
   With the `hkbfs` interpretation, use whatever order `term` prints.
3. **`vset_of_list_rbt`:** `idfs.vset_of_list_aux` does not exist (the lemma
   lives in `DFS_avoid_thms`). Prove a small global lemma instead:
   `vset_inv (vset_of_list_rbt xs) ∧ t_set (vset_of_list_rbt xs) = set xs`,
   by induction on `xs` with `idfs.Graph.vset.set.invar_insert`/`set_insert`
   and the empty-set facts. Do not depend on the demo interpretation
   `ddfs_diamond`.
4. **Two red–black instances of the graph specification:** `G` (alt-BFS
   digraphs; `M.invar`, `Leaf`) and `idfs.Graph` (copies graph; `adj_inv`,
   `vset_empty`) agree on `finite_graph`/`finite_vsets` but not syntactically on
   `digraph_abs`, `graph_inv`, `neighbourhood`. This is fine as long as the
   copies graph is handled only through `idfs.Graph`/`W` and the BFS digraphs
   only through `G`/`hkbfs`; add a bridging lemma only where a statement
   genuinely mixes them (expected: none beyond `CG_abs`, which relates
   `idfs.Graph.digraph_abs CG` to `hkbfs.copies_dag … (G.digraph_abs T)` and
   needs no bridge).
5. **Executability (decided now, for Gate 6):** `IDFS_witness.IDFS_impl_def`
   carries the locale premise, so `hk_phase` must not call
   `IDFS_witness.IDFS_impl` directly. Define instead, globally,
   ```isabelle
   definition "hk_stack0 avoid vis p =
      (if p ≠ [] ∧ (isin avoid (hd p) ∨ isin vis (hd p)) then tl p else p)"
   definition "hk_idfs CG P avoid p vis =
      (let st = avoid_impl_rbt CG (hk_stack0 avoid vis p) vis avoid P
       in (DFS_avoid_state.ret st, DFS_avoid_state.visited st))"
   ```
   (argument order of `avoid_impl_rbt` from `term`), use
   `hk_idfs CG (λw. hk_level D w = 0)` as the `step` of `disjoint_search_gen`
   in `hk_phase`, and prove in the m-context, after `interpretation W`:
   `lemma hk_idfs_eq: "hk_idfs CG = W.IDFS_impl"` by `intro ext` and unfolding
   `hk_idfs_def hk_stack0_def W.IDFS_impl_def W.IDFS_stack0_def
   avoid_impl_rbt_def` (expected: the same `DFS_avoid.avoid_final_state_impl`
   term at the `idfs` operations). `avoid_impl_rbt` already has code
   equations (DDFS_Example.thy:357). This changes the DEFINITION of
   `hk_phase` in ζ-3 only in the `step` argument; the statements of
   `hk_phase_sound/_disjoint/_complete` are unchanged.

### ζ-1. The matching, represented by its mate function

```isabelle
global_interpretation mate: matching_augmentation_spec Leaf update RBT_Map.delete lookup M.invar
  defines mate_augment = mate.augment_impl
    and mate_matching = mate.\<M>
    and mate_invar = mate.invar_matching
  by (auto intro!: matching_augmentation_spec.intro simp add: Map_axioms_as_needed)

interpretation mate_thms: matching_augmentation Leaf update RBT_Map.delete lookup M.invar
  using mate.matching_augmentation_spec_axioms by (auto intro!: matching_augmentation.intro)

lemmas mate_augmentation_correct =
  mate_thms.augmentation_correct[folded mate_invar_def mate_matching_def mate_augment_def]
lemmas mate_empty_props =
  mate_thms.empty_matching_props[folded mate_invar_def mate_matching_def]
lemmas mate_invarD =
  mate.invar_matchingD[folded mate_invar_def mate_matching_def]

lemma mate_matching_iff:
  assumes "mate_invar G m"
  shows "{u, v} ∈ mate_matching m ⟷ lookup m u = Some v"
proof
  have sym: "⋀a b. lookup m a = Some b ⟹ lookup m b = Some a"
    using mate_invarD[OF assms] by (auto dest: mate.symmetric_buddiesD)
  assume "{u, v} ∈ mate_matching m"
  then obtain x y where xy: "{u, v} = {x, y}" "lookup m x = Some y"
    unfolding mate_matching_def mate.\<M>_def' by blast
  show "lookup m u = Some v"
  proof (cases "x = u")
    case True
    hence "y = v" using xy(1) by (auto simp: doubleton_eq_iff)
    then show ?thesis using xy(2) True by simp
  next
    case False
    hence "x = v" "y = u" using xy(1) by (auto simp: doubleton_eq_iff)
    then show ?thesis using sym[OF xy(2)] by simp
  qed
next
  assume "lookup m u = Some v"
  then show "{u, v} ∈ mate_matching m" unfolding mate_matching_def mate.\<M>_def' by blast
qed

lemma mate_Vs_iff:
  assumes "mate_invar G m"
  shows "v ∈ Vs (mate_matching m) ⟷ lookup m v ≠ None"
proof
  assume "v ∈ Vs (mate_matching m)"
  then obtain e where e: "e ∈ mate_matching m" "v ∈ e" by (auto simp: Vs_def)
  then obtain x y where xy: "e = {x, y}" "lookup m x = Some y"
    unfolding mate_matching_def mate.\<M>_def' by blast
  have "lookup m x = Some y" "lookup m y = Some x"
    using xy(2) mate_invarD[OF assms] by (auto dest: mate.symmetric_buddiesD)
  then show "lookup m v ≠ None" using e(2) xy(1) by auto
next
  assume "lookup m v ≠ None"
  then obtain w where "lookup m v = Some w" by blast
  then have "{v, w} ∈ mate_matching m" unfolding mate_matching_def mate.\<M>_def' by blast
  then show "v ∈ Vs (mate_matching m)" by (rule edges_are_Vs)
qed
```
(`mate.symmetric_buddiesD`, `mate.\<M>_def'` and the exact projection of
`mate_invarD` onto symmetry are recon items. Library identifiers are cited as
they are; every new name and all prose use "mate function".)

### ζ-2. The input graph in the read-only vocabulary (HK-D9)

Peer-tested pattern (Graph ADT session): instantiate with named `where`
clauses only; bridge one lemma per constant.

```isabelle
interpretation RO: pair_graph_specs_read_only
  where vset_empty = Leaf and vset_delete = RBT.delete and vset_inv = vset_inv
    and insert = insert_rbt and isin = isin and t_set = Tree2.set_tree and sel = sel
    and lookup = lookup and adjmap_inv = M.invar
  using S_C.Set_Choose_axioms by (simp add: pair_graph_specs_read_only_def)

lemma RO_neighbourhood: "RO.neighbourhood = G.neighbourhood"
  by (intro ext) (simp add: RO.neighbourhood_def G.neighbourhood_def)
lemma RO_digraph_abs: "RO.digraph_abs = G.digraph_abs"
  by (intro ext) (simp add: RO.digraph_abs_def G.digraph_abs_def RO_neighbourhood)
lemma RO_graph_inv: "RO.graph_inv = G.graph_inv"
  by (intro ext) (simp add: RO.graph_inv_def G.graph_inv_def)
lemma RO_finite_graph: "RO.finite_graph = G.finite_graph"
  by (intro ext) (simp add: RO.finite_graph_def G.finite_graph_def)
lemma RO_finite_vsets: "RO.finite_vsets = G.finite_vsets"
  by (intro ext) (simp add: RO.finite_vsets_def G.finite_vsets_def)

definition hk_edges where
  "hk_edges Gin vs = concat (map (λu. map (Pair u) (Tree2.inorder (RO.neighbourhood Gin u))) vs)"

definition "UG_of Gin = {{u, v} | u v. (u, v) ∈ RO.digraph_abs Gin}"

definition "hk_input Gin vs X Y ⟷
   RO.graph_inv Gin ∧ RO.finite_graph Gin ∧ RO.finite_vsets Gin ∧
   (∀u v. (u, v) ∈ RO.digraph_abs Gin ⟶ (v, u) ∈ RO.digraph_abs Gin) ∧
   (∀u. (u, u) ∉ RO.digraph_abs Gin) ∧
   set vs = dVs (RO.digraph_abs Gin) ∧
   bipartite (UG_of Gin) X Y"
```
(Write `RO.neighbourhood Gin u`, never the `𝒩` notation: two graph
instances are in scope — peer caution.)

### ζ-3. Executable builders (global definitions)

```isabelle
definition "match_list es m = filter (λ(u, v). lookup m u = Some v) es"
definition "unmatch_list es m = filter (λ(u, v). lookup m u ≠ Some v) es"
definition "free_list vs m = filter (λv. lookup m v = None) vs"
definition "hk_srcs vs m = foldr insert_rbt (free_list vs m) Leaf"

definition "copies_list es m T =
   concat (map (λ(u, v).
      if isin (G.neighbourhood T u) v
      then (if lookup m u = Some v then [(Vtx Even v, Vtx Odd u)] else [(Vtx Odd v, Vtx Even u)])
      else []) es)"

definition "hk_level D w = the_enat (the (lookup D w))"

definition "hk_roots vs m VO D =
   (let fs = filter (λt. isin VO t) (free_list vs m) in
    if fs = [] then [] else
    let k = fold min (map (λt. hk_level D (Vtx Odd t)) (tl fs)) (hk_level D (Vtx Odd (hd fs)))
    in map (Vtx Odd) (filter (λt. hk_level D (Vtx Odd t) = k) fs))"

definition "hk_blk cvs p =
   vset_of_list_rbt (filter (λw. w ∈ set cvs) (concat (map (λw. [Vtx Even (vtx w), Vtx Odd (vtx w)]) p)))"

definition "hk_phase es vs m =
  (if free_list vs m = [] then [] else
   let Mt = G.from_list (match_list es m); Ut = G.from_list (unmatch_list es m);
       st = alt_bfs_impl Mt Ut (alt_bfs_initial_state (hk_srcs vs m));
       cl = copies_list es m (parents st);
       CG = idfs.Graph.from_list cl;
       D = distances st;
       qs = disjoint_search_gen vset_union (hk_blk (map fst cl @ map snd cl))
              (IDFS_witness.IDFS_impl vset_insert isin sel vset_empty vset_union vset_diff lookup CG
                 (λw. hk_level D w = 0))
              vset_empty vset_empty (hk_roots vs m (visited_odd st) D)
   in map (map vtx) qs)"
```
(Fix the argument order of `IDFS_witness.IDFS_impl` from recon (b). The roots
are the free vertices at the MINIMAL odd level `k` — Hopcroft–Karp proper;
for correctness alone any non-empty choice would do.)

### ζ-4. Input lemmas (context `fixes Gin vs X Y assumes inp: "hk_input Gin vs X Y"`)

```isabelle
context
  fixes Gin vs X Y
  assumes inp: "hk_input Gin vs X Y"
begin

lemma inp_parts:
  "RO.graph_inv Gin" "RO.finite_graph Gin" "RO.finite_vsets Gin"
  "⋀u v. (u, v) ∈ RO.digraph_abs Gin ⟹ (v, u) ∈ RO.digraph_abs Gin"
  "⋀u. (u, u) ∉ RO.digraph_abs Gin"
  "set vs = dVs (RO.digraph_abs Gin)"
  "bipartite (UG_of Gin) X Y"
  using inp by (simp_all add: hk_input_def)

lemma hk_edges_set: "set (hk_edges Gin vs) = RO.digraph_abs Gin"
proof (intro equalityI subsetI)
  fix e assume "e ∈ set (hk_edges Gin vs)"
  then obtain u v where e: "e = (u, v)" "v ∈ Tree2.set_tree (RO.neighbourhood Gin u)"
    by (auto simp: hk_edges_def)
  show "e ∈ RO.digraph_abs Gin" using e RO.are_connected_abs[OF inp_parts(1)] by simp
next
  fix e assume E: "e ∈ RO.digraph_abs Gin"
  obtain u v where e: "e = (u, v)" by (cases e)
  have uV: "u ∈ set vs" using E e inp_parts(6) by (auto intro: dVsI)
  have "v ∈ Tree2.set_tree (RO.neighbourhood Gin u)"
    using E e RO.are_connected_abs[OF inp_parts(1)] by simp
  then show "e ∈ set (hk_edges Gin vs)" using uV e by (force simp: hk_edges_def)
qed

lemma UG_edge_iff: "{u, v} ∈ UG_of Gin ⟷ (u, v) ∈ RO.digraph_abs Gin"
proof
  assume "{u, v} ∈ UG_of Gin"
  then obtain a b where ab: "{u, v} = {a, b}" "(a, b) ∈ RO.digraph_abs Gin"
    by (auto simp: UG_of_def)
  then show "(u, v) ∈ RO.digraph_abs Gin"
    using inp_parts(4) by (auto simp: doubleton_eq_iff)
next
  assume "(u, v) ∈ RO.digraph_abs Gin"
  then show "{u, v} ∈ UG_of Gin" by (auto simp: UG_of_def)
qed

lemma Vs_UG: "Vs (UG_of Gin) = set vs"
  using inp_parts(4,6) by (auto simp: Vs_def UG_of_def dVs_eq)

lemma UG_graph_invar: "graph_invar (UG_of Gin)"
proof
  show "dblton_graph (UG_of Gin)"
    unfolding dblton_graph_def UG_of_def using inp_parts(5) by blast
  have "finite (dVs (RO.digraph_abs Gin))"
    by (rule RO.finite_vertices[OF inp_parts(1,2,3)])
  then show "finite (Vs (UG_of Gin))" using Vs_UG inp_parts(6) by simp
qed
```
(`dblton_graph`: every edge `{u, v}` has `u ≠ v` by loop-freedom; the
`blast` may need `inp_parts(5)` instantiated — REPL-gate.)

### ζ-5. One phase, for a fixed mate function `m`

Inside the input context, a nested context fixes `m` with
`mi: "mate_invar (UG_of Gin) m"` and `fne: "free_list vs m ≠ []"`, and names
the phase's intermediate objects by abbreviations (local to this context):

```isabelle
context
  fixes m
  assumes mi: "mate_invar (UG_of Gin) m" and fne: "free_list vs m ≠ []"
begin

abbreviation "es ≡ hk_edges Gin vs"
abbreviation "Mt ≡ G.from_list (match_list es m)"
abbreviation "Ut ≡ G.from_list (unmatch_list es m)"
abbreviation "S ≡ hk_srcs vs m"
abbreviation "st ≡ alt_bfs_impl Mt Ut (alt_bfs_initial_state S)"
abbreviation "T ≡ parents st"
abbreviation "cl ≡ copies_list es m T"
abbreviation "CG ≡ idfs.Graph.from_list cl"
abbreviation "lv ≡ hk_level (distances st)"
```

Lemmas, in order (each statement is final; proofs are outlined where they are
more than a citation):

```isabelle
lemma M_sub: "mate_matching m ⊆ UG_of Gin"
  using mate_invarD[OF mi] by auto

lemma Mt_abs: "G.digraph_abs Mt = {(u, v). {u, v} ∈ mate_matching m}"
  ― ‹G.from_list_correct: abstraction = set (match_list es m) =
     {(u,v) ∈ set es. lookup m u = Some v}; hk_edges_set; mate_matching_iff[OF mi];
     a matched pair is an edge of UG (M_sub), hence of the digraph (UG_edge_iff)›

lemma Ut_abs: "G.digraph_abs Ut = {(u, v). {u, v} ∈ UG_of Gin - mate_matching m}"
  ― ‹G.from_list_correct; hk_edges_set; UG_edge_iff; mate_matching_iff[OF mi]›

lemma S_props: "vset_inv S" "Tree2.set_tree S = Vs (UG_of Gin) - Vs (mate_matching m)"
  ― ‹induction on the list for foldr insert_rbt (set.invar_insert, set.set_insert,
     set.invar_empty, set.set_empty of Pair_Graph_RBT's `set` interpretation);
     set (free_list vs m) = {v ∈ set vs. lookup m v = None}; Vs_UG; mate_Vs_iff[OF mi]›

lemma bfs_axiom: "alt_bfs.BFS_axiom Mt Ut S"
  ― ‹unfold alt_bfs.BFS_axiom_def; G.from_list_correct (graph_inv, finite_graph,
     finite_vsets of Mt and Ut); srcs ⊆ dVs (abs Ut): a free v ∈ Vs UG has an
     edge (v, w) in the digraph, and lookup m v = None ≠ Some w (Ut_abs);
     finite neighbourhoods: subsets of the finite set (G.from_list_correct);
     S ≠ {} by fne and S_props; vset_inv S; abs Mt ∩ abs Ut = {} (Mt_abs, Ut_abs)›

lemma st_valid:
  "alt_bfs.valid_alt_BFS_DAG_impl Mt Ut S T (distances st) (visited_even st) (visited_odd st)"
  ― ‹alt_bfs_impl = alt_bfs.BFS on the initial state: alt_bfs.BFS_impl_same with
     alt_bfs.initial_state_props(13)[OF bfs_axiom] (BFS_dom); then
     alt_bfs.BFS_valid_DAG_impl[OF bfs_axiom]›

lemma T_sub: "G.digraph_abs T ⊆ RO.digraph_abs Gin"
  ― ‹clause (1) of the predicate: abs T ⊆ alt_bfs.G = abs Ut ∪ abs Mt; Mt_abs, Ut_abs,
     UG_edge_iff›

lemma CG_abs: "idfs.Graph.digraph_abs CG = alt_bfs.copies_dag Mt Ut (G.digraph_abs T)"
  ― ‹idfs.Graph.from_list_correct: abstraction = set cl; unfold copies_list_def and
     alt_bfs.copies_dag_def; membership test: isin (G.neighbourhood T u) v ⟷
     (u, v) ∈ G.digraph_abs T (G.are_connected_abs, graph_inv T from st_valid);
     matched/unmatched test: Mt_abs, Ut_abs, mate_matching_iff; every T-edge is in
     set es (T_sub, hk_edges_set)›

lemma CG_level:
  "w ∈ dVs (idfs.Graph.digraph_abs CG) ⟹ lv w = alt_bfs.copies_lev Mt Ut S w"
  using alt_bfs.copies_lev_by_lookup[OF bfs_axiom … st_valid'] CG_abs
  ― ‹st_valid' = the non-impl projection of st_valid; unfold hk_level_def›

lemma CG_layered: "idfs.Graph.layered_graph_input CG lv"
  ― ‹layered_graph_inputI: graph_inv/finite_graph/finite_vsets from
     idfs.Graph.from_list_correct; layered_dgraph from alt_bfs.valid_DAG_layered[OF
     bfs_axiom st_valid] rewritten by CG_abs, transported from copies_lev to lv by
     CG_level (both endpoints of every edge and every vertex of a walk are in dVs).
     Write the transport as a small global lemma first:
       layered_dgraph_cong: (⋀w. w ∈ dVs dG ⟹ f w = g w) ⟹
                            layered_dgraph dG f ⟹ layered_dgraph dG g
     (unfold layered_dgraph_def; for the walk clause, the end vertex of a walk is in dVs:
      vwalk_bet_in_dVs)›
```

Then interpret the search locale for this copies graph (inside the same
context, as a local interpretation):

```isabelle
interpretation W: IDFS_witness
  where insert = vset_insert and sel = sel and vset_empty = vset_empty
    and diff = vset_diff and lookup = lookup and empty = map_empty
    and delete = RBT_Map.delete and isin = isin and t_set = t_set
    and update = update and adjmap_inv = adj_inv
    and vset_delete = vset_delete and vset_inv = vset_inv
    and union = vset_union and inter = vset_inter
    and G = CG and lev = lv
  ― ‹mirror DDFS_Example's ddfs_diamond / ddfs_chain interpretation proofs:
     G.Pair_Graph_Specs_axioms, RBT.Set2_axioms, and CG_layered for the assumption›
```
(After this, `W.disjoint_search P blk` is literally the `disjoint_search_gen
…` term inside `hk_phase`; if the recon of `IDFS_witness.IDFS_impl` showed a
different argument order, the abbreviation still matches because both come
from the same constant.)

Search facts for this phase:

```isabelle
lemma roots_props:
  "set (hk_roots vs m (visited_odd st) (distances st)) ⊆
     Vtx Odd ` (Tree2.set_tree S ∩ Tree2.set_tree (visited_odd st))"
  ― ‹unfold hk_roots_def; isin ⟷ membership for vset_inv (visited_odd st) (st_valid);
     free_list vs m ⊆ t_set S (S_props)›

lemma roots_dVs: "set (hk_roots vs m (visited_odd st) (distances st)) ⊆ dVs (idfs.Graph.digraph_abs CG)"
  ― ‹roots_props; alt_bfs.VisO_copies_dVs[OF bfs_axiom … st_valid'] and CG_abs›

lemma fold_min_mem: "fold min xs (x::nat) ∈ insert x (set xs)"
  by (induction xs arbitrary: x) (auto simp: min_def)
  ― ‹global lemma, place before the context›

lemma roots_nonempty:
  "filter (λt. isin (visited_odd st) t) (free_list vs m) ≠ [] ⟹
   hk_roots vs m (visited_odd st) (distances st) ≠ []"
  ― ‹unfold hk_roots_def Let_def; k ∈ set of levels by fold_min_mem; the element
     attaining k survives the filter›

lemma blk_props:
  "vset_inv (hk_blk (map fst cl @ map snd cl) p)"
  "t_set (hk_blk (map fst cl @ map snd cl) p) ⊆ dVs (idfs.Graph.digraph_abs CG)"
  "w ∈ dVs (idfs.Graph.digraph_abs CG) ⟹ vtx w ∈ vtx ` set p ⟹
     w ∈ t_set (hk_blk (map fst cl @ map snd cl) p)"
  ― ‹idfs.vset_of_list_aux (invariant and set of vset_of_list_rbt); dVs (set cl) =
     set (map fst cl @ map snd cl) (dVs_eq) and idfs.Graph.from_list_correct;
     third: w = Vtx (label w) (vtx w) is one of the two copies listed for some
     element of p›
```

### ζ-6. The phase contract

Back in the input context (outside the `m` context), for every `m` with
`mi: mate_invar (UG_of Gin) m`:

```isabelle
theorem hk_phase_sound:
  assumes mi: "mate_invar (UG_of Gin) m"
      and P: "P ∈ set (hk_phase (hk_edges Gin vs) vs m)"
  shows "graph_augmenting_path (UG_of Gin) (mate_matching m) P"
  ― ‹If free_list vs m = [] the phase is [] — contradiction. Otherwise unfold
     hk_phase_def Let_def: P = map vtx q for some q found by W.disjoint_search.
     W.disjoint_search_correct (search_pre_empty, roots_dVs, blk_props(1,2)) gives
     dpath (rev q), q ≠ [], lv (hd q) = 0, last q ∈ set roots. found_vwalk_bet:
     vwalk_bet CG (last q) (rev q) (hd q); last q = Vtx Odd t with t ∈ t_set S
     (roots_props). CG_level gives copies_lev (hd q) = 0; CG_abs rewrites the walk
     into the copies DAG of T. Then
       alt_bfs.copies_walk_augmenting(1)[OF bfs_axiom UG_graph_invar M_sub Mt_abs Ut_abs
                                         S_props(2) inp_parts(7) st_valid' t walk z0]
     gives graph_augmenting_path UG M (rev (map vtx (rev q))), and
     rev (map vtx (rev q)) = map vtx q (rev_map, rev_rev_ident).›

theorem hk_phase_disjoint:
  assumes mi: "mate_invar (UG_of Gin) m"
  shows "sorted_wrt (λP Q. set P ∩ set Q = {}) (hk_phase (hk_edges Gin vs) vs m)"
  ― ‹free_list = []: trivial. Otherwise W.disjoint_search_correct gives
     sorted_wrt (λp q. set q ∩ t_set (blk p) = {}) qs. sorted_wrt_map turns the goal
     into a statement about qs; sorted_wrt_mono_rel reduces it to: for found p, q with
     set q ∩ t_set (blk p) = {}, the vertex sets of map vtx p and map vtx q are
     disjoint. If x = vtx w' with w' ∈ set q and x ∈ vtx ` set p: w' ∈ dVs CG
     (q is a walk of CG: vwalk_bet_in_dVs), so w' ∈ t_set (blk p) by blk_props(3)
     — contradiction.›

theorem hk_phase_complete:
  assumes mi: "mate_invar (UG_of Gin) m"
      and ex: "∃P. graph_augmenting_path (UG_of Gin) (mate_matching m) P"
  shows "hk_phase (hk_edges Gin vs) vs m ≠ []"
  ― ‹free_list = []: an augmenting path P has hd P ∈ Vs UG − Vs M (definition +
     mem_path_Vs), i.e. in set vs with lookup m (hd P) = None (Vs_UG, mate_Vs_iff),
     so free_list ≠ [] — contradiction. Otherwise:
     alt_bfs.aug_path_iff_free_odd_copy[OF … st_valid'] gives t ∈ t_set S with
     Vtx Odd t ∈ dVs (copies DAG); alt_bfs.copies_dag_dVs puts t in visited_odd st;
     hence the filtered free list is non-empty and roots_nonempty gives
     roots = r0 # rs0 with r0 = Vtx Odd t0, t0 ∈ visited_odd st (roots_props).
     r0 ∈ dVs CG (roots_dVs); alt_bfs.copies_reach_zero gives a walk to z with
     copies_lev z = 0, so lv z = 0 (CG_level, CG_abs). W.disjoint_search_nonempty
     [OF W.search_pre_empty (set_empty) (set_empty) r0_dVs walk lv_z] shows qs ≠ [],
     hence the phase (map (map vtx) qs) is non-empty.›

end ― ‹input context›
```

**Gate 5 deliverable:** `HK_Phase.thy` PIDE-green, in ROOT, ASCII 0, batch
green; report `thm hk_phase_sound hk_phase_disjoint hk_phase_complete` and the
recon record (ζ-0).

---

## Phase η — the verified, executable Hopcroft–Karp algorithm (Gate 6)

New theory `Hopcroft_Karp/HK_Example.thy`, importing `HK_Phase`; add to
`Hopcroft_Karp/ROOT`.

### η-A. Amendment after Gate 5 (2026-10-11, orchestrator-approved)

Gate 5 is green with the ζ-A design. Notes for Gate 6, which override η-1…η-3
where they differ:

1. **Executable search step.** `hk_phase` calls `hk_idfs` (global definition
   over DDFS_Example's `avoid_impl_rbt` and `hk_stack0`), not
   `IDFS_witness.IDFS_impl`; both `hk_stack0_def` and `hk_idfs_def` are plain
   global definitions, so they are code equations as they stand. Do NOT use
   `hk_idfs_eq` for code generation (it lives inside the ζ-5 context).
2. **Code equations to check first, with `value` on small terms, before
   running the whole algorithm:**
   - `RO.neighbourhood` (used by `hk_edges`): the inherited `[code]`
     equation was reported as "partially applied". Declare the
     interpretation's own instance `RO.neighbourhood_def` (or an equivalent
     equation `RO.neighbourhood G v = (case lookup G v of Some N ⇒ N | None ⇒
     Leaf)`) as `[code]`.
   - `G.from_list`, `G.add_edge`, `G.neighbourhood`, `idfs.Graph.from_list`,
     `idfs.Graph.add_edge`, `idfs.Graph.neighbourhood`: if `value` fails,
     declare the interpretation instances of `from_list_def`, `add_edge_def`,
     `neighbourhood_def` as `[code]` (instances of a theory-level or global
     interpretation carry no locale premise).
   - `alt_bfs_impl`, `alt_bfs_initial_state`, `avoid_impl_rbt`,
     `vset_of_list_rbt`: already executable (Alt_BFS_Example, DDFS_Example).
   - `hk_exec.hk_loop_impl`: from `hk_loop_impl.simps` of the assumption-free
     locale `hk_loop_defs`; fold with the `defines` of η-1 as in
     DDFS_Example.thy:320–359.
3. **η-1 interpretation of `hk_loop_defs`.** The locale has no assumptions,
   so the `global_interpretation … for Gin vs defines …` may need no proof at
   all; drop the `done` if Isabelle reports "No proof state".
4. **η-2.** `hk_phase_sound/_disjoint/_complete` are exported with
   `hk_input Gin vs X Y` as their first premise (verified). Abbreviations of
   the ζ-5 context print as `local.*` outside it — display only.
5. **η-3 demo.** Run `value` on `hk_edges demo_G demo_vs`, then on
   `hk_phase (hk_edges demo_G demo_vs) demo_vs Leaf`, then on
   `Tree2.inorder (hopcroft_karp demo_G demo_vs)`. Simulate the first phase
   by hand (empty matching: every vertex free, every edge an unmatched level-1
   edge; the roots are the odd copies of all six vertices at level 1, searched
   in vertex-list order) and record the expected and the computed outputs in
   progress.md. A maximum matching here has 3 edges, i.e. 6 entries in the
   mate map.

### η-1. The executable loop (definitions locale only — no assumptions)

```isabelle
global_interpretation hk_exec: hk_loop_defs mate_augment "hk_phase (hk_edges Gin vs) vs"
  for Gin vs
  defines hk_loop_exec = hk_exec.hk_loop_impl
    and hk_augment_list = hk_exec.augment_list
  done

definition "hopcroft_karp Gin vs = hk_loop_exec Gin vs Leaf"
```
Code equations: `hk_exec.hk_loop_impl.simps` and `hk_exec.augment_list_def`,
folded with the `defines` (mirror DDFS_Example.thy:320–359); and a code
equation for `IDFS_witness.IDFS_impl` at the `idfs` operations, folded with
`avoid_impl_rbt_def` (mirror `idfs_chain_code`, DDFS_Example.thy:341–345). If
`IDFS_witness.IDFS_impl_def` turns out to carry the locale premise, define
`hk_idfs CG P avoid p vis` with the body of IDFS.thy:51–55 at these operations,
use it in `hk_phase`, and prove `hk_idfs CG = W.IDFS_impl` inside ζ-5 by
unfolding both definitions.

### η-2. Correctness

```isabelle
context
  fixes Gin vs X Y
  assumes inp: "hk_input Gin vs X Y"
begin

interpretation hk: hk_loop_spec mate_augment "hk_phase (hk_edges Gin vs) vs"
  "UG_of Gin" "mate_invar (UG_of Gin)" mate_matching
proof (unfold_locales, goal_cases)
  case 1 show ?case by (rule UG_graph_invar[OF inp])
next
  case (2 m) show ?case using mate_invarD[OF 2] by simp
next
  case (3 m p) show ?case using mate_augmentation_correct(1)[OF 3] .
next
  case (4 m p) show ?case using mate_augmentation_correct(2)[OF 4] .
next
  case (5 m p) show ?case by (rule hk_phase_sound[OF inp 5])
next
  case (6 m) show ?case by (rule hk_phase_disjoint[OF inp 6])
next
  case (7 m) show ?case by (rule hk_phase_complete[OF inp 7])
qed

theorem hopcroft_karp_correct:
  "mate_invar (UG_of Gin) (hopcroft_karp Gin vs)"
  "max_card_matching (UG_of Gin) (mate_matching (hopcroft_karp Gin vs))"
proof -
  have e: "mate_invar (UG_of Gin) Leaf" using mate_empty_props by blast
  have eq: "hopcroft_karp Gin vs = hk.hk_loop_impl Leaf"
    by (simp add: hopcroft_karp_def hk_loop_exec_def)
  show "mate_invar (UG_of Gin) (hopcroft_karp Gin vs)"
    using hk.hk_loop_impl_correct(1)[OF e] eq by simp
  show "max_card_matching (UG_of Gin) (mate_matching (hopcroft_karp Gin vs))"
    using hk.hk_loop_impl_correct(2)[OF e] eq by simp
qed

end
```
(`hk_phase_sound` etc. are exported from the ζ input context with `hk_input
Gin vs X Y` as first premise; the case facts of `unfold_locales` are the
locale assumptions in declaration order — check `goal_cases` numbering in
PIDE. `mate_augmentation_correct` has the premises `mate_invar G m` and
`graph_augmenting_path G (mate_matching m) p`.)

### η-3. Demonstration

A bipartite graph with sides `{0, 1, 2}` and `{3, 4, 5}` and edges 0–3, 0–4,
1–3, 1–5, 2–4 (maximum matching size 3):

```isabelle
definition "demo_edges =
  [(0::nat, 3::nat), (3, 0), (0, 4), (4, 0), (1, 3), (3, 1), (1, 5), (5, 1), (2, 4), (4, 2)]"
definition "demo_G = G.from_list demo_edges"
definition "demo_vs = [0, 1, 2, 3, 4, 5::nat]"

value "Tree2.inorder (hopcroft_karp demo_G demo_vs)"
value "hk_phase (hk_edges demo_G demo_vs) demo_vs Leaf"

lemma demo_input: "hk_input demo_G demo_vs {0, 1, 2} {3, 4, 5}"
  ― ‹RO_digraph_abs, RO_graph_inv, … + G.from_list_correct reduce everything to
     statements about set demo_edges; then `eval`/`simp` (bipartite_def, dVs_eq).›

corollary demo_max: "max_card_matching (UG_of demo_G) (mate_matching (hopcroft_karp demo_G demo_vs))"
  by (rule hopcroft_karp_correct(2)[OF demo_input])
```
Record the two `value` outputs in progress.md and check them by hand: the
first phase (empty matching: all six vertices free, every edge at level 1)
must return three vertex-disjoint paths of length 1 if the search order
allows, otherwise fewer paths and a second phase; the final mate function
must have six entries (three matched pairs, symmetric).

**Gate 6 deliverable:** `HK_Example.thy` PIDE-green, in ROOT, ASCII 0, batch
green, `hopcroft_karp_correct` and `demo_max` proved, `value` outputs recorded.
`export_code hopcroft_karp in SML module_name HK` succeeds.

---

## Alternative not planned: Hopcroft–Karp in Micali–Vazirani's bridge form

**Alternative (not planned): Hopcroft–Karp in Micali–Vazirani's bridge
form.** Run DDFS from both endpoints of each bridge and join the two
returned paths through the bridge. Extra obligations: a characterisation of
bridges in the bipartite case, and a lemma that DDFS never reports a
bottleneck on a bipartite graph. Benefit: it would exercise the DDFS
interface on alt-BFS output before the general Micali–Vazirani top loop.
Recommendation: keep `IDFS_impl` for Hopcroft–Karp (HK-D8) and leave DDFS
to the Micali–Vazirani top loop.

## HK-M5 (optional, not planned in detail) — `O(√|V|)` phases

Needs M2's maximality + the tight-edge clause, and the classical HK lemmas,
none of which exist in the library: (i) `M ⊕ M*` contains `|M*| - |M|`
vertex-disjoint `M`-augmenting paths (Berge.thy's component machinery —
`component_path'`, `matching_augmenting_path_exists_1`, `degree_symm_diff` —
is the starting point); (ii) after augmenting along a maximal set of
vertex-disjoint shortest augmenting paths, the shortest augmenting path is
strictly longer; (iii) the counting argument. Research-grade; separate plan.
