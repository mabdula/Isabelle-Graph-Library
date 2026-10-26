# Plan: restyling the Hopcroft–Karp theories in the library's DFS/BFS style

Drafted 2026-10-11. Status: **DRAFT, awaiting the user's approval of the
decisions in §1.** No theory has been edited and the coder has not been started.

Inputs:
- Style guide `/media/llms/Isabelle-Graph-Library-Style/Library_Style_Guide.md`
  (cited as "guide §n"), measurement script `style_stats.py` and baseline
  `stats.txt` in the same directory.
- The six green Hopcroft–Karp (HK) gates of `Hopcroft_Karp_Plan.md`.
- Templates: `Set_Graphs/Graph_Algorithms/DFS.thy` (loop machinery, invariant
  families) and `Hungarian_Method/Hungarian_Method_Top_Loop.thy` (top loop with
  an abstract matching and a search parameter).
- The guide was revised on 2026-10-11 with §4.1 (termination) and §4.2 (final
  correctness in layers). R1, R2 and R5 follow that revision.

The user's complaint concerned three points: names (e.g. the lower-case
`pair_graph_specs_read_only`); definitions (loops are not always
`function (domintros)`, there is no state record, and invariants are not shown
per branch); and proofs (many low-level, verbose proofs). The user named DFS as
the model. The plan addresses all three, one theory at a time. The session
stays green at every gate.

---

## 0. What must not change, and how success is measured

**Invariant across the whole campaign.**
1. The final theorem keeps its mathematical content. For every input
   adjacency map and vertex list satisfying the input predicate, the result
   satisfies `mate_invar` and is a maximum-cardinality matching of the
   undirected graph of the input. Only names may change (§A). Today this is
   `hopcroft_karp_correct(1,2)`. After R5 it is `hopcroft_karp_final_invar`
   and `hopcroft_karp_correctness`, re-exported from the top-loop locale.
2. The algorithm stays executable. `export_code hopcroft_karp in SML` succeeds,
   and the demonstration's final mate map is still
   `[(0,3),(1,5),(2,4),(3,0),(4,2),(5,1)]`.
3. Project rules (guide §5.6 plus earlier HK gates):
   - no `sorry`, `smt`, `metis` or `meson`;
   - no `{ … }` blocks;
   - no `apply` (HK convention). The library's two-step `apply(rule X) by (auto …)`
     is written as one call: `by (cases state rule: <loop>_cases) (auto …)` in
     the induction lemmas (Hungarian's form), and `by (intro X[where …]) (auto …)`
     in the final-correctness lemmas. The measurement script counts `by (rule`
     inside structured proofs, so `by (rule X) (…)` is kept for the two
     `domintros` steps of the termination proofs only. There, `intro` would
     re-apply the rule without end;
   - ASCII on disk;
   - theory edits only through I/Q.
4. HK-D9 rules for the read-only specification are unchanged. Instantiate it
   with named `where` only, use one bridge lemma per constant, never refer to
   the sublocale qualifier, and never import the interim theory together with
   the split library.
5. The Micali–Vazirani theories in the copy (`Alt_BFS`, `Top_Loop`, `IDFS`,
   `DDFS`, `*_Example`) are not edited.

**Measured acceptance (after R5).** Run, from the copy root:
```
python3 /media/llms/Isabelle-Graph-Library-Style/style_stats.py \
  /home/llm/.claude/jobs/1269a04e/tmp/restyle_stats.json \
  DFS=Set_Graphs/Graph_Algorithms/DFS.thy BFS=Set_Graphs/Graph_Algorithms/BFS_2.thy \
  HK=<the five restyled theories, comma-separated>
```
The HK group must reach the figures below.

| Metric (guide §1) | Now | Target |
|---|---|---|
| Lemmas closed by a single `by` | 38.0% | ≥ 60% |
| Median proof length | 8 | ≤ 2 |
| Labelled `have`/`show`/`obtain` per lemma | 2.29 | ≤ 0.5 |
| `[OF …]` per lemma | 2.10 | ≤ 0.7 |
| Named assumptions per lemma (locale assumption groups excepted) | 0.51 | 0 |
| `elim!:` + `intro!:` per lemma | 0.00 | ≥ 0.5 |
| `by (rule …)` among closing calls of structured proofs | 25.9% | ≤ 5% (the two `domintros` steps) |
| `by` / `using` opening a line | 17% / 35% | ≥ 95% / ≥ 95% |
| `proof -` / `proof (` with a space | 41 / 52 | 0 / 0 |
| Lemmas carrying an attribute | 6.5% | ≥ 50% |
| Loops as `function (domintros)` over one record, with an `_impl` twin | 0 of 2 | 2 of 2 |
| `invar_*` families (`_props`, `_intro`, one per branch, `_holds`) | 0 | 1 (top loop) + 7 (search) |
| `named_theorems` declared and used | 0 | in both loop theories |
| Termination (guide §4.1, §7 item 10) | inline arithmetic, domain premise | `<loop>_terminates`/`_termination` with invariant premises only; domain of the initial state in `initial_state_props` |
| Final correctness (guide §4.2, §7 item 11) | arbitrary state + premise; proved again in the example | three layers per loop, `initial_state_loops_same`, wrapper theorem, `[folded …]` re-export |
| `hk_` prefixes, one- to three-letter global abbreviations | 15 | 0 |

Per-gate figures are recorded but are not gate criteria, except for the loop
items of the gate that introduces the loop.

---

## 1. Decisions

Decisions marked **(confirm)** change the design and need the user's approval.
The others follow directly from the guide.

- **RD1 (confirm). The search for vertex-disjoint paths becomes a generic loop
  whose search step is a parameter.**
  - This is the Hungarian pattern: `hungarian_loop_spec` fixes `path_search`,
    and `hungarian_loop` assumes its contract.
  - The new locale `disjoint_paths_search_spec` fixes the step function, a
    blocking function, the target predicate and the initial roots. The proofs
    locale `disjoint_paths_search` assumes the step's contract; today that
    contract is the conclusion list of `root_call`.
  - The incremental DFS discharges the contract once, as a lemma in
    `IDFS_witness` (R2).
  - *Why.* The definitions locale carries no assumption. Code generation then
    needs no wrapper of the kind that the ζ-A lesson forced (`hk_idfs` around
    `IDFS_impl`).
  - *Alternative.* Define the loop inside `IDFS_witness`. That repeats the
    ζ-A problem for the new loop.
- **RD2. Field name `current_matching`, not `matching`.** `matching` is the
  constant `matching :: 'a set set ⇒ bool` of Basic_Matching. A record field of
  that name would make every later `matching M` ambiguous. The guide's template
  (§6.1) has this clash. A field `phases :: nat` is kept, as the guide proposes.
  The correctness proofs do not use it; it is meant for the later phase bound
  (HK-M5).
- **RD3 (confirm). Paths are accumulated by prepending (`p # paths state`).**
  - Today `disjoint_search_gen` returns the paths in root order. With
    prepending, a phase returns them in reverse order. The demonstration's
    first phase then prints `[[3,1],[4,0]]` instead of `[[4,0],[3,1]]`.
  - The final matching is unchanged, because augmenting along vertex-disjoint
    paths commutes.
  - The alternative is `paths state @ [p]`, which is quadratic in the number of
    paths per phase.
- **RD4 (confirm). `Hopcroft_Karp.thy` becomes `Alt_BFS_Bipartite.thy`.**
  - The theory adds facts to the locale `BFS` of `Alt_BFS`: walks of the copies
    graph and augmenting paths in a bipartite graph. It introduces no locale,
    so the name follows the content (guide §2.1).
  - The six assumptions of its matching-instance context (`UG_inv`, `M_sub`,
    `Mabs`, `Uabs`, `srcs_free`, `bip`) are bundled into one definition,
    `bipartite_matching_input UG M X Y`. This is the pattern of `DFS_axioms`
    (guide §3.4). The definition is unpacked once into `[simp]`/`[intro]`
    facts.
  - The phase then proves the bundle once, and no longer passes seven facts
    positionally, as in
    `copies_walk_augmenting(1)[OF bfs_axiom UG_graph_invar M_sub Mt_abs Ut_abs S_props(2) inp_parts(7) st_valid' …]`.
- **RD5. The phase context becomes the locale `hopcroft_karp_phase`, with
  definitions in place of the nine abbreviations.** Today this is the context
  `fixes m assumes mi fne` with abbreviations `es Mt Ut S st T cl CG lv`.
  - The global executable definitions stay global and are renamed; they are
    the glue, which conforms (guide §6.4).
  - The locale's definitions name the intermediate objects:

    | Locale definition | Replaces |
    |---|---|
    | `edge_list` | `es` |
    | `matching_graph` | `Mt` |
    | `non_matching_graph` | `Ut` |
    | `bfs_sources` | `S` (`sources` is taken by `Pair_Graph`) |
    | `bfs_state` | `st` |
    | `bfs_dag` | `T` |
    | `copies_edge_list` | `cl` |
    | `copies_graph` | `CG` |
    | `level` | `lv` |
    | `copy_roots` | today's root expression |
  - One lemma, `hopcroft_karp_phase_unfold`, connects the global phase to them.
- **RD6. The constants `mate_augment`, `mate_matching` and `mate_invar` keep
  their names in this campaign.** Using the Hungarian instance's
  `matching_augment_impl`, `matching_abstract` and `matching_invar` instead is
  the separate question I asked earlier (item 1 of the interface comparison).
  It can be added to R4 if the user wants it. The locale *parameters* follow
  `hungarian_loop` exactly (guide §2.3): `empty_matching`, `matching_invar`,
  `augment` and `matching_abstract`. That covers item 2 of the comparison.
- **RD7. The read-only locale name is not changed here.** Renaming
  `pair_graph_specs_read_only` to `Pair_Graph_Specs_Read_Only` is a matter for
  the Graph ADT session's split library. The interim copy is deleted at
  integration (HK-D9), and HK then uses whatever name the split library has.
  R6 sends the question to the Graph ADT session.
- **RD8. Generic helper lemmas stay where they are used.** These are
  `vwalk_bet_level_distinct`, the `alt_list` transfer pair, `vwalk_bet_closed`,
  `found_vwalk_bet`, `fold_min_mem`, `layered_dgraph_cong` and
  `vset_of_list_rbt_props`. They are restyled in place and not moved into the
  library; moving them is a separate integration step.
- **RD9. Nothing is committed.** The user decides on commits (as before).
  Snapshots go to `Hopcroft_Karp/backups/restyle-R<n>/` at every gate
  (milestone-backup rule).

---

## 2. Phases

| Phase | Theory (new name ← old) | Depends on | Kind of change | Size now → expected |
|---|---|---|---|---|
| R0 | — | — | recon, baseline, backups | — |
| R1 | `Hopcroft_Karp_Top_Loop` ← `HK_Top_Loop` | — | record, loop machinery, invariant family, proofs | 321 → ~260 |
| R2 | `Disjoint_Paths_Search` (new; replaces the loop of `HK_Search`) | — | record, loop machinery, 7 invariant families, IDFS contract | 196 → ~480 |
| R3 | `Alt_BFS_Bipartite` ← `Hopcroft_Karp` | — | names, assumption bundle, proofs | 587 → ~420 |
| R4 | `Hopcroft_Karp_Phase` ← `HK_Phase` (+ removal of `HK_Search`) | R2, R3 | names, phase locale, search instance, proofs | 814 → ~560 |
| R5 | `Hopcroft_Karp_Example` ← `HK_Example` | R1, R4 | executable instance, final theorem, demonstration | 163 → ~140 |
| R6 | — | all | measurement, close-out, coordination | — |

R1, R2 and R3 are independent and could run in any order. The proposed order
puts the small, pattern-setting top loop first, so that the coder learns the
loop machinery on 260 lines before the search loop. R4 is the largest gate.

**Keeping the session green.**
- R1 patches the consumer `HK_Example` (its two interpretations and
  `hopcroft_karp_def`) in the same gate. `HK_Phase` uses no top-loop name; only
  its import line changes.
- R2 adds the new theory without removing anything.
  - `HK_Search` keeps working until R4. Its two generic walk lemmas move to
    `Disjoint_Paths_Search`, and `HK_Search` imports that theory, so no fact
    name is declared twice.
  - The new IDFS contract lemma is named `IDFS_impl_search_step`, so it does
    not clash with `root_call`.
- R3 renames lemmas that `HK_Phase` cites. `HK_Phase` gets a pure name
  substitution in the same gate, with no proof changes.
- R4 switches the phase to the new loop and deletes `HK_Search` from `ROOT`.
  The file stays in `backups/`.

**Session `ROOT` order after R5:**
`Pair_Graph_Specs_Read_Only Hopcroft_Karp_Top_Loop Disjoint_Paths_Search
Alt_BFS_Bipartite Hopcroft_Karp_Phase Hopcroft_Karp_Example`.

---

## 3. Gate protocol (all phases)

As in `Hopcroft_Karp_Plan.md` § Coder protocol, which remains in force: I/Q on
port 8767 with token `hk` through the copy's `mcp.py`; `USER_HOME=/media/llms/isabelle-home-hk`;
other instances are never touched; REPL gate for search closers;
sledgehammer in the REPL on a broken step. The coder runs Sonnet at high effort.

Additional rules for the restyle:
1. **Statements first.** The orchestrator writes the statements and the
   candidate proof text into this plan before the gate (one-shot). The coder
   pastes them, then repairs only the steps that fail.
   - A statement may change only if this plan's text says so, or with the
     orchestrator's approval (the gate's amendment section).
2. **Repair order for a failing step.** Each fallback is tried only after the
   one before it fails.
   - First, the same single call with more of the bundles (`elim!:
     call_cond_elims invar_props_elims`, `intro!: invar_props_intros`,
     `simp: <branch>_def Let_def`).
   - Then `force`/`fastforce`/`blast` with the same modifiers.
   - Then sledgehammer. A `metis` or `smt` answer is translated into `auto`,
     `force` or `blast` with the facts it names.
   - Last, a short structured proof of the form in guide §5.2: one `have` per
     mathematical step, chained with `hence`/`moreover`/`ultimately`, with
     earlier facts cited as cartouches.

   The coder never adds a labelled `have` for book-keeping (non-emptiness,
   membership in `set`, a subset that follows from an invariant).
3. **Layout** (guide §5.5).
   - `using` and `by` start their own line, indented two spaces.
   - Write `proof-` and `proof(…)`, with no space.
   - Long method calls are split by modifier, with the modifiers aligned.
4. **Gate checks** (orchestrator):
   - PIDE reports 0 errors on every session theory;
   - the batch build exits with 0;
   - the scan of `tmp/verify_thy.py` finds no `sorry`, `metis`, `smt`, `meson`
     or `apply` (comment-aware) and no `{`-blocks, and the files are pure ASCII;
   - the statements match the plan;
   - `style_stats.py` is run on the gate's theories and the figures are
     recorded in `progress.md` under "## Restyle Gate R<n>";
   - the theories are snapshotted to `backups/restyle-R<n>/`.
   - From R1 on, `value "Tree2.inorder (hopcroft_karp demo_G demo_vs)"` returns
     the mate map of §0.

---

## R0. Recon, baseline, backups (orchestrator, before any edit)

1. Snapshot all six HK theories and `ROOT` to `backups/restyle-R0/`.
2. Check that the session is green: batch build, and `value` of the demo.
3. Run `style_stats.py` on the five HK theories. The output must reproduce the
   HK column of `stats.txt`, which checks the script's path handling.
4. Check in the REPL (`term`, `find_consts`) that these names are free at their
   points of use:
   - the record fields `current_matching`, `phases`, `roots`, `avoided`,
     `explored`, `paths`;
   - the definitions `initial_state` and `call_measure` inside the new locales;
   - `bipartite_matching_input` and `level`;
   - the global names of §A.

   `sources` is known to be taken (`Pair_Graph.sources`). If another name is
   taken, the orchestrator picks a replacement before the gate; the coder never
   picks one.
5. Record the exact parameter order and names of `Set2` as `IDFS_witness`
   instantiates it (`set_ops: Set2 vset_empty vset_delete _ t_set vset_inv insert`,
   with `union` as the union parameter). R2 copies that form.

---

## R1. `Hopcroft_Karp_Top_Loop.thy` (from `HK_Top_Loop.thy`)

Model: `Hungarian_Method_Top_Loop.thy` (state record, definitions locale with
the loop, branch decomposition, proofs locale with assumption groups,
`less_induct` termination). The invariant family has the DFS layout.

### R1-1. Skeleton (candidate text)

```
theory Hopcroft_Karp_Top_Loop
  imports "Basic_Matching.Berge"
begin

section \<open>Top Loop of the Hopcroft-Karp Algorithm\<close>

subsection \<open>Augmenting along vertex-disjoint augmenting paths\<close>

lemma edges_of_path_disjoint:
  "\<lbrakk>e \<in> set (edges_of_path q); set p \<inter> set q = {}\<rbrakk> \<Longrightarrow> e \<notin> set (edges_of_path p)"
  using edges_of_path_Vs[of p] edges_of_path_Vs[of q]
  by (fastforce simp: Vs_def dest!: in_edges_of_path_split)

lemma augmenting_path_disjoint_preserved:
  assumes "matching M" "graph_augmenting_path G M p" "graph_augmenting_path G M q"
          "set p \<inter> set q = {}"
  shows "graph_augmenting_path G (M \<oplus> set (edges_of_path p)) q"
proof-
  have "e \<in> M \<oplus> set (edges_of_path p) \<longleftrightarrow> e \<in> M" if "e \<in> set (edges_of_path q)" for e
    using that assms(4)
    by (auto simp: in_symmetric_diff_iff dest: edges_of_path_disjoint)
  hence "alt_path (M \<oplus> set (edges_of_path p)) q"
    using assms(3)
    by (auto simp: matching_augmenting_path_def
            intro: alt_list_cong_1[OF alt_list_cong_2])
  moreover have "Vs (M \<oplus> set (edges_of_path p)) = {hd p, last p} \<union> Vs M"
    using assms(1,2) rematch_atl_path_Vs_change aug_paths_are_even
    by (auto simp: matching_augmenting_path_def)
  ultimately show ?thesis
    using assms(3,4)
    by (auto simp: matching_augmenting_path_def dest: hd_in_set last_in_set)
qed
```
*Outline, if the closing calls fail:*
1. Edges of `q` have the same membership in `M` and in `M'`, because they are
   edges of a path disjoint from `p`.
2. Hence `q` alternates with respect to `M'` (by `alt_list_cong_1` and
   `alt_list_cong_2`).
3. `Vs M' = {hd p, last p} ∪ Vs M`.
4. The ends of `q` lie in `set q`, which is disjoint from `set p`, so they are
   free in `M'`.

The old `aug_path_disjoint_preserved` (25 labelled steps) is the source for
step 4.

`augment_all`, `augment_all_simps` and `augment_all_correct` are **deleted**:
the card argument moves to `foldl_augment_card` (R1-4).

### R1-2. Program state, automation, definitions locale

```
subsection \<open>The program state\<close>

record 'matching hopcroft_karp_state =
  current_matching :: 'matching
  phases :: nat

subsection \<open>Setup for automation\<close>

named_theorems call_cond_elims
named_theorems call_cond_intros
named_theorems ret_holds_intros
named_theorems invar_props_intros
named_theorems invar_props_elims
named_theorems invar_holds_intros
named_theorems termination_intros

subsection \<open>Locale for the implementation\<close>

locale hopcroft_karp_loop_spec =
  fixes empty_matching :: 'matching
    and matching_invar :: "'matching \<Rightarrow> bool"
    and augment :: "'matching \<Rightarrow> 'v list \<Rightarrow> 'matching"
    and matching_abstract :: "'matching \<Rightarrow> 'v set set"
    and phase :: "'matching \<Rightarrow> 'v list list"
    and G :: "'v set set"
begin

function (domintros) hopcroft_karp_loop ::
  "'matching hopcroft_karp_state \<Rightarrow> 'matching hopcroft_karp_state" where
  "hopcroft_karp_loop state =
     (let paths = phase (current_matching state) in
      if paths \<noteq> [] then
        hopcroft_karp_loop
          (state \<lparr>current_matching := foldl augment (current_matching state) paths,
                  phases := Suc (phases state)\<rparr>)
      else state)"
  by pat_completeness auto

partial_function (tailrec) hopcroft_karp_loop_impl ::
  "'matching hopcroft_karp_state \<Rightarrow> 'matching hopcroft_karp_state" where
  "hopcroft_karp_loop_impl state =
     (let paths = phase (current_matching state) in
      if paths \<noteq> [] then
        hopcroft_karp_loop_impl
          (state \<lparr>current_matching := foldl augment (current_matching state) paths,
                  phases := Suc (phases state)\<rparr>)
      else state)"

definition "initial_state = \<lparr>current_matching = empty_matching, phases = 0\<rparr>"

definition "hopcroft_karp = current_matching (hopcroft_karp_loop_impl initial_state)"

lemmas [code] = hopcroft_karp_loop_impl.simps initial_state_def hopcroft_karp_def

definition "hopcroft_karp_loop_call_1_conds state = (phase (current_matching state) \<noteq> [])"

definition "hopcroft_karp_loop_upd1 state =
  (let paths = phase (current_matching state) in
   state \<lparr>current_matching := foldl augment (current_matching state) paths,
          phases := Suc (phases state)\<rparr>)"

definition "hopcroft_karp_loop_ret_1_conds state = (phase (current_matching state) = [])"

abbreviation "hopcroft_karp_loop_ret1 state \<equiv> state"
```

### R1-3. The branch lemmas and the four standard lemmas (candidate text)

```
lemma hopcroft_karp_loop_call_1_conds[call_cond_elims]:
  "hopcroft_karp_loop_call_1_conds state \<Longrightarrow> (phase (current_matching state) \<noteq> [] \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: hopcroft_karp_loop_call_1_conds_def)

lemma hopcroft_karp_loop_call_1_condsI[call_cond_intros]:
  "phase (current_matching state) \<noteq> [] \<Longrightarrow> hopcroft_karp_loop_call_1_conds state"
  by (auto simp: hopcroft_karp_loop_call_1_conds_def)

lemma hopcroft_karp_loop_ret_1_conds[call_cond_elims]:
  "hopcroft_karp_loop_ret_1_conds state \<Longrightarrow> (phase (current_matching state) = [] \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: hopcroft_karp_loop_ret_1_conds_def)

lemma hopcroft_karp_loop_ret_1_condsI[call_cond_intros]:
  "phase (current_matching state) = [] \<Longrightarrow> hopcroft_karp_loop_ret_1_conds state"
  by (auto simp: hopcroft_karp_loop_ret_1_conds_def)

lemma hopcroft_karp_loop_cases:
  assumes "hopcroft_karp_loop_call_1_conds state \<Longrightarrow> P"
          "hopcroft_karp_loop_ret_1_conds state \<Longrightarrow> P"
  shows "P"
  using assms
  by (auto simp: hopcroft_karp_loop_call_1_conds_def hopcroft_karp_loop_ret_1_conds_def)

lemma hopcroft_karp_loop_simps:
  assumes "hopcroft_karp_loop_dom state"
  shows "hopcroft_karp_loop_call_1_conds state \<Longrightarrow>
           hopcroft_karp_loop state = hopcroft_karp_loop (hopcroft_karp_loop_upd1 state)"
        "hopcroft_karp_loop_ret_1_conds state \<Longrightarrow> hopcroft_karp_loop state = state"
  by (auto simp: hopcroft_karp_loop.psimps[OF assms] Let_def hopcroft_karp_loop_upd1_def
                 hopcroft_karp_loop_call_1_conds_def hopcroft_karp_loop_ret_1_conds_def)

lemma hopcroft_karp_loop_induct:
  assumes "hopcroft_karp_loop_dom state"
          "\<And>state. \<lbrakk>hopcroft_karp_loop_dom state;
                     hopcroft_karp_loop_call_1_conds state \<Longrightarrow> P (hopcroft_karp_loop_upd1 state)\<rbrakk>
                    \<Longrightarrow> P state"
  shows "P state"
  by (rule hopcroft_karp_loop.pinduct[OF assms(1)])
     (auto intro!: assms(2) simp: hopcroft_karp_loop_call_1_conds_def
                                  hopcroft_karp_loop_upd1_def Let_def)

lemma hopcroft_karp_loop_domintros:
  assumes "hopcroft_karp_loop_call_1_conds state \<Longrightarrow>
             hopcroft_karp_loop_dom (hopcroft_karp_loop_upd1 state)"
  shows "hopcroft_karp_loop_dom state"
  using assms
  by (auto intro: hopcroft_karp_loop.domintros
           simp: hopcroft_karp_loop_call_1_conds_def hopcroft_karp_loop_upd1_def Let_def)

lemma hopcroft_karp_loop_impl_same:
  assumes "hopcroft_karp_loop_dom state"
  shows "hopcroft_karp_loop_impl state = hopcroft_karp_loop state"
  by (induction rule: hopcroft_karp_loop.pinduct[OF assms])
     (subst hopcroft_karp_loop_impl.simps, auto simp: hopcroft_karp_loop.psimps Let_def)

end
```

### R1-4. Proofs locale, invariant, termination, correctness (candidate text)

```
subsection \<open>Locale for the proofs\<close>

locale hopcroft_karp_loop = hopcroft_karp_loop_spec +
  assumes G: "graph_invar G"
  and matching:
    "\<And>M. matching_invar M \<Longrightarrow> graph_matching G (matching_abstract M)"
    "matching_invar empty_matching"
    "matching_abstract empty_matching = {}"
  and augment:
    "\<And>M p. \<lbrakk>matching_invar M; graph_augmenting_path G (matching_abstract M) p\<rbrakk>
       \<Longrightarrow> matching_invar (augment M p)"
    "\<And>M p. \<lbrakk>matching_invar M; graph_augmenting_path G (matching_abstract M) p\<rbrakk>
       \<Longrightarrow> matching_abstract (augment M p) = matching_abstract M \<oplus> set (edges_of_path p)"
  and phase:
    "\<And>M p. \<lbrakk>matching_invar M; p \<in> set (phase M)\<rbrakk>
       \<Longrightarrow> graph_augmenting_path G (matching_abstract M) p"
    "\<And>M. matching_invar M \<Longrightarrow> sorted_wrt (\<lambda>p q. set p \<inter> set q = {}) (phase M)"
    "\<And>M. \<lbrakk>matching_invar M; \<exists>p. graph_augmenting_path G (matching_abstract M) p\<rbrakk>
       \<Longrightarrow> phase M \<noteq> []"
begin

lemma graph_matching_finite: "graph_matching G M \<Longrightarrow> finite M"
  using G finite_Vs_then_finite
  by (auto intro: finite_subset)

lemma foldl_augment_invar:
  "\<lbrakk>matching_invar M; \<forall>p \<in> set ps. graph_augmenting_path G (matching_abstract M) p;
    sorted_wrt (\<lambda>p q. set p \<inter> set q = {}) ps\<rbrakk>
   \<Longrightarrow> matching_invar (foldl augment M ps)"
  and foldl_augment_card:
  "\<lbrakk>matching_invar M; \<forall>p \<in> set ps. graph_augmenting_path G (matching_abstract M) p;
    sorted_wrt (\<lambda>p q. set p \<inter> set q = {}) ps\<rbrakk>
   \<Longrightarrow> card (matching_abstract (foldl augment M ps)) = card (matching_abstract M) + length ps"
```
*Proof (one induction for both, `induction ps arbitrary: M`).*
- `Nil` is `simp`.
- `Cons p ps`:
  - `augment(1)` gives the invariant for `augment M p`.
  - `augment(2)` together with `augmenting_path_disjoint_preserved` gives the
    premise for the rest of the list.
  - `new_matching_plus_one` together with `graph_matching_finite` gives the card
    step.
  - Close with `auto` on these facts.

If one induction for the two conclusions is awkward, state them as one lemma
with `\<and>` and derive the two names by `lemmas … = …[THEN conjunct1/2]`.

```
subsection \<open>Invariant\<close>

definition "invar_matching state = matching_invar (current_matching state)"

lemma invar_matching_props[invar_props_elims]:
  "invar_matching state \<Longrightarrow> (matching_invar (current_matching state) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_matching_def)

lemma invar_matching_intro[invar_props_intros]:
  "matching_invar (current_matching state) \<Longrightarrow> invar_matching state"
  by (auto simp: invar_matching_def)

lemma
  assumes "hopcroft_karp_loop_call_1_conds state" "invar_matching state"
  shows invar_matching_holds_upd1[invar_holds_intros]:
          "invar_matching (hopcroft_karp_loop_upd1 state)"
    and card_increase_upd1:
          "card (matching_abstract (current_matching state)) <
           card (matching_abstract (current_matching (hopcroft_karp_loop_upd1 state)))"
  using assms
  by (auto elim!: call_cond_elims invar_props_elims
          intro!: invar_props_intros foldl_augment_invar phase
            simp: hopcroft_karp_loop_upd1_def Let_def foldl_augment_card)

lemma card_matching_bounded:
  "invar_matching state \<Longrightarrow> card (matching_abstract (current_matching state)) \<le> card G"
  using G finite_Vs_then_finite
  by (auto elim!: invar_props_elims dest!: matching(1) intro!: card_mono)
```
The one-step lemma has two named conclusions, as Hungarian's
`state_invar_pres_one_step`/`card_increase` (guide §4.1, variant). The card
arithmetic lives here and in `card_matching_bounded`. The termination proof
below only combines the facts. If the single `by` fails for the card
conclusion, prove it separately: `foldl_augment_card`, plus
`length (phase …) \<noteq> 0` from the branch condition.

```
lemma invar_matching_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>hopcroft_karp_loop_ret_1_conds state; invar_matching state\<rbrakk>
   \<Longrightarrow> invar_matching (hopcroft_karp_loop_ret1 state)"
  by auto

lemma invar_matching_holds[invar_holds_intros]:
  assumes "hopcroft_karp_loop_dom state" "invar_matching state"
  shows "invar_matching (hopcroft_karp_loop state)"
  using assms(2)
proof(induction rule: hopcroft_karp_loop_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    by (cases state rule: hopcroft_karp_loop_cases)
       (auto intro!: IH(2-) invar_holds_intros simp: hopcroft_karp_loop_simps[OF IH(1)])
qed

subsection \<open>Termination\<close>

lemma hopcroft_karp_loop_termination_induction:
  assumes "invar_matching state" "n = card G - card (matching_abstract (current_matching state))"
  shows "hopcroft_karp_loop_dom state"
  using assms
proof(induction n arbitrary: state rule: less_induct)
  case (less n)
  show ?case
    by (rule hopcroft_karp_loop_domintros)
       (auto intro!: less(1) invar_holds_intros
              dest!: card_increase_upd1 card_matching_bounded[OF invar_matching_holds_upd1]
               simp: less(3))
qed

lemmas hopcroft_karp_loop_termination[termination_intros] =
  hopcroft_karp_loop_termination_induction[OF _ refl]
```
This is the Hungarian variant of guide §4.1: one recursive branch, a
natural-number measure, `less_induct`, export with `[OF _ refl]`. The DFS
form (`call_1_measure`, `hopcroft_karp_loop_term_rel'`,
`call_1_terminates`, `wf_induct_rule`) is acceptable as well; use it if the
`less_induct` proof does not close in one call. The premise of
`hopcroft_karp_loop_termination` is the invariant only (guide §7, item 10).

```
subsection \<open>Correctness\<close>

lemma hopcroft_karp_loop_correct_ret_1:
  "\<lbrakk>invar_matching state; hopcroft_karp_loop_ret_1_conds state\<rbrakk>
   \<Longrightarrow> max_card_matching G (matching_abstract (current_matching state))"
```
*Proof.* This is layer 1 of guide §4.2, and the Berge argument goes here.
- `phase(3)` and the branch condition: the matching has no augmenting path.
- Berge's theorem: if there were a matching of larger cardinality inside `G`,
  there would be an augmenting path.
- The source is the `ccontr` block of the old `hk_loop_correct`. Target: a
  structured proof of at most 6 lines in the form of guide §5.2:
  `hence "\<nexists>p. …"`, then `Berge[…]` and `max_card_matching_def`, with facts
  cited as cartouches.

```
lemma hopcroft_karp_loop_ret_1_holds[ret_holds_intros]:
  assumes "hopcroft_karp_loop_dom state"
  shows "hopcroft_karp_loop_ret_1_conds (hopcroft_karp_loop state)"
proof(induction rule: hopcroft_karp_loop_induct[OF assms])
  case IH: (1 state)
  show ?case
    by (cases state rule: hopcroft_karp_loop_cases)
       (auto intro!: IH(2-) simp: hopcroft_karp_loop_simps[OF IH(1)])
qed
```
This is layer 2: one returning branch, so there is no result flag. The return
update is the identity, so DFS's companion lemma `DFS_ret_<i>` ("returning
preserves the condition") would be `P \<Longrightarrow> P` and is omitted.

```
subsection \<open>The initial state\<close>

lemma initial_state_props[invar_holds_intros, termination_intros]:
  "invar_matching initial_state" "hopcroft_karp_loop_dom initial_state"
  by (auto intro!: invar_props_intros hopcroft_karp_loop_termination matching(2)
            simp: initial_state_def)

lemma initial_state_loops_same:
  "hopcroft_karp_loop_impl initial_state = hopcroft_karp_loop initial_state"
  by (auto intro!: hopcroft_karp_loop_impl_same initial_state_props)

subsection \<open>Final correctness\<close>

lemma hopcroft_karp_loop_correct:
  "max_card_matching G (matching_abstract (current_matching (hopcroft_karp_loop initial_state)))"
  by (intro hopcroft_karp_loop_correct_ret_1[where state = "hopcroft_karp_loop initial_state"])
     (auto intro: invar_holds_intros ret_holds_intros)

lemma hopcroft_karp_loop_final_invar:
  "matching_invar (current_matching (hopcroft_karp_loop initial_state))"
  by (auto intro: invar_holds_intros elim!: invar_props_elims)

theorem hopcroft_karp_correctness:
  "max_card_matching G (matching_abstract hopcroft_karp)"
  by (auto simp: hopcroft_karp_def initial_state_loops_same intro: hopcroft_karp_loop_correct)

lemma hopcroft_karp_final_invar:
  "matching_invar hopcroft_karp"
  by (auto simp: hopcroft_karp_def initial_state_loops_same intro: hopcroft_karp_loop_final_invar)

end
end
```
Guide §4.2, layers 3–5:
- The two lemmas about `hopcroft_karp_loop initial_state` have no premise and
  are proved in two lines (layer 3).
- `initial_state_loops_same` carries them over to the executable loop
  (layer 4).
- The wrapper `hopcroft_karp` (defined in R1-2) has one theorem for its single
  outcome, plus the invariant of its result, as `hungarian_correctness` and
  `hungarian_final_invar` do (layer 5).
- Layer 6, the re-export at the concrete instance, is R5.
- The later phase bound (HK-M5) will be a further final lemma about
  `phases (hopcroft_karp_loop initial_state)`, with its own invariant family.

### R1-5. Consumer patch in `HK_Example.thy` (same gate)

This is a minimum patch; R5 restyles the rest.
1. Replace `global_interpretation hk_exec: hk_loop_defs …` and the definition
   of `hopcroft_karp` with:
   ```
   global_interpretation hk_exec: hopcroft_karp_loop_spec
     where empty_matching = Leaf and matching_invar = "mate_invar (UG_of Gin)"
       and augment = mate_augment and matching_abstract = mate_matching
       and phase = "hk_phase (hk_edges Gin vs) vs" and G = "UG_of Gin"
     for Gin vs
     defines hk_loop_exec = hk_exec.hopcroft_karp_loop_impl
       and hk_initial_state = hk_exec.initial_state
       and hopcroft_karp = hk_exec.hopcroft_karp
   ```
   The `hk_` names survive only until R5. R0 checks how many arguments each
   `defines` constant takes. It may be both `Gin vs`, or only the variables
   that occur, as for `hk_initial_state`.
2. The correctness context interprets `hopcroft_karp_loop` with the same
   `where` list.
   - The three `phase` clauses come from `hk_phase_sound`, `_disjoint` and
     `_complete`, as now.
   - The `matching` clauses come from `mate_invarD` and `mate_empty_props`.
3. `hopcroft_karp_correct` keeps its name and statement until R5. Its proof
   becomes the folded `hopcroft_karp_correctness` and `hopcroft_karp_final_invar`
   of the interpretation: `hk.hopcroft_karp_correctness[folded hopcroft_karp_def]`
   and the same for the invariant.
4. `HK_Phase.thy` changes its import `HK_Top_Loop` to `Hopcroft_Karp_Top_Loop`.
   `ROOT` is updated.

**Gate R1 checks.** These are the checks of §3, plus:
- `Hopcroft_Karp_Top_Loop` has a record, the loop with its `_impl` twin and
  `_impl_same`, both branches with their `_conds` lemmas, the four standard
  lemmas, and the complete `invar_matching` family;
- termination has the invariant as its only premise, and the domain of the
  initial state is in `initial_state_props` (guide §7, item 10);
- final correctness has the three layers and the two carry-overs of guide
  §4.2 (§7, item 11);
- no `.psimps` or `.pinduct` appears outside `_simps`, `_induct`,
  `_domintros` and `_impl_same`.

---

## R2. `Disjoint_Paths_Search.thy` (new; generic loop plus the IDFS contract)

Templates: DFS.thy for the machinery, and Hungarian for a search step that is a
parameter with an assumed contract (RD1).

### R2-1. State, locale, loop (candidate text)

```
theory Disjoint_Paths_Search
  imports Micali_Vazirani.IDFS
begin

section \<open>Searching for Vertex-Disjoint Paths\<close>

text \<open>From each root in turn, a search step looks for a path to a target vertex that avoids
  the vertices blocked by the paths found so far. The step is a parameter. Its contract is
  an assumption of the locale for the proofs, and Section~\ref{sec:idfs} discharges it for
  the incremental depth-first search.\<close>

subsection \<open>The program state\<close>

record ('v, 'vset) disjoint_paths_search_state =
  roots :: "'v list"
  avoided :: 'vset
  explored :: 'vset
  paths :: "'v list list"

subsection \<open>Setup for automation\<close>

named_theorems call_cond_elims
named_theorems call_cond_intros
named_theorems ret_holds_intros
named_theorems invar_props_intros
named_theorems invar_props_elims
named_theorems invar_holds_intros
named_theorems termination_intros

subsection \<open>Locale for the implementation\<close>

locale disjoint_paths_search_spec =
  set_ops: Set2 vset_empty vset_delete isin t_set vset_inv insert
  for vset_empty :: 'vset and vset_delete isin t_set vset_inv insert +
  fixes G :: "('v \<times> 'v) set"
    and target :: "'v \<Rightarrow> bool"
    and blocked :: "'v list \<Rightarrow> 'vset"
    and search_step :: "'vset \<Rightarrow> 'v \<Rightarrow> 'vset \<Rightarrow> 'v list option \<times> 'vset"
    and initial_roots :: "'v list"
begin

function (domintros) disjoint_paths_search ::
  "('v, 'vset) disjoint_paths_search_state \<Rightarrow> ('v, 'vset) disjoint_paths_search_state" where
  "disjoint_paths_search state =
     (case roots state of
        [] \<Rightarrow> state
      | r # rs \<Rightarrow>
          (case search_step (avoided state) r (explored state) of
             (Some p, explored') \<Rightarrow>
               disjoint_paths_search
                 (state \<lparr>roots := rs, avoided := union (avoided state) (blocked p),
                         explored := explored', paths := p # paths state\<rparr>)
           | (None, explored') \<Rightarrow>
               disjoint_paths_search (state \<lparr>roots := rs, explored := explored'\<rparr>)))"
  by pat_completeness auto

partial_function (tailrec) disjoint_paths_search_impl :: (same type, same body)

definition "initial_state =
  \<lparr>roots = initial_roots, avoided = vset_empty, explored = vset_empty, paths = []\<rparr>"

lemmas [code] = disjoint_paths_search_impl.simps initial_state_def
```
The Set2 parameter list must be copied from `IDFS_witness` as recorded in
R0-5. If `isin` has to stay anonymous (`_`) there, it does here too.

### R2-2. Branches

| Branch | Condition | Update or result |
|---|---|---|
| `call_1` (a path is found) | `roots state = r # rs` and `search_step (avoided state) r (explored state) = (Some p, explored')` | `upd1`: drop the root, add `blocked p` to `avoided`, set `explored := explored'`, prepend `p` |
| `call_2` (no path) | `roots state = r # rs` and the step returns `(None, explored')` | `upd2`: drop the root, set `explored := explored'` |
| `ret_1` (no root left) | `roots state = []` | `ret1 = state` (abbreviation) |

The `_conds` definitions are copies of the body with `True`/`False` at the
leaves, as in DFS.

```
definition "disjoint_paths_search_upd1 state =
  (let (path, explored') = search_step (avoided state) (hd (roots state)) (explored state);
       p = the path
   in state \<lparr>roots := tl (roots state), avoided := union (avoided state) (blocked p),
             explored := explored', paths := p # paths state\<rparr>)"

definition "disjoint_paths_search_upd2 state =
  state \<lparr>roots := tl (roots state),
         explored := snd (search_step (avoided state) (hd (roots state)) (explored state))\<rparr>"

lemma disjoint_paths_search_call_1_conds[call_cond_elims]:
  "disjoint_paths_search_call_1_conds state \<Longrightarrow>
   (\<And>r rs p explored'. \<lbrakk>roots state = r # rs;
       search_step (avoided state) r (explored state) = (Some p, explored')\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: disjoint_paths_search_call_1_conds_def split: list.splits option.splits prod.splits)
```
Write `call_2` and `ret_1` the same way, each with an `…I[call_cond_intros]`
form. Then come `disjoint_paths_search_cases`, `_simps`, `_induct`,
`_domintros` and `_impl_same`, written exactly as in R1-3 with three branches
(DFS's four-branch versions are the template). The proofs use
`split: list.splits option.splits prod.splits`.

**Termination** follows the DFS form of guide §4.1. There are two recursive
branches. Both drop the head of `roots`, so they decrease the *same* measure,
and no "unchanged" lemma (DFS's `call_2_measure_1`) is needed.
- The measure is defined in the spec locale.
- The lemmas belong to the subsection *Termination* of the proofs locale,
  after the invariants, as in DFS. None of them needs an invariant, so
  `disjoint_paths_search_terminates` has no premise at all.
```
definition "call_measure state = length (roots state)"
definition "disjoint_paths_search_term_rel' = call_measure <*mlex*> {}"

(in the proofs locale, subsection Termination)
lemma call_1_terminates[termination_intros]:
  "disjoint_paths_search_call_1_conds state \<Longrightarrow>
     (disjoint_paths_search_upd1 state, state) \<in> call_measure <*mlex*> r"
  by (auto elim!: call_cond_elims intro!: mlex_less
            simp: call_measure_def disjoint_paths_search_upd1_def)

lemma call_2_terminates[termination_intros]:
  "disjoint_paths_search_call_2_conds state \<Longrightarrow>
     (disjoint_paths_search_upd2 state, state) \<in> call_measure <*mlex*> r"
  by (auto elim!: call_cond_elims intro!: mlex_less
            simp: call_measure_def disjoint_paths_search_upd2_def)

lemma wf_term_rel: "wf disjoint_paths_search_term_rel'"
  by (auto simp: wf_mlex disjoint_paths_search_term_rel'_def)

lemma in_disjoint_paths_search_term_rel'[termination_intros]:
  "disjoint_paths_search_call_1_conds state \<Longrightarrow>
     (disjoint_paths_search_upd1 state, state) \<in> disjoint_paths_search_term_rel'"
  "disjoint_paths_search_call_2_conds state \<Longrightarrow>
     (disjoint_paths_search_upd2 state, state) \<in> disjoint_paths_search_term_rel'"
  by (simp add: disjoint_paths_search_term_rel'_def termination_intros)+

lemma disjoint_paths_search_terminates[termination_intros]:
  "disjoint_paths_search_dom state"
  using wf_term_rel
proof(induction rule: wf_induct_rule)
  case (less state)
  show ?case
    by (rule disjoint_paths_search_domintros) (auto intro!: less in_disjoint_paths_search_term_rel')
qed
```
DFS's shared helpers (`in_prod_relI`, `less_rel`, `wf_less_rel`) are copied
only if one of these proofs needs them.

### R2-3. Invariants (definitions in the spec locale)

```
definition "search_step_precond avoid r vis =
  (vset_inv avoid \<and> vset_inv vis \<and> t_set avoid \<subseteq> dVs G \<and> t_set vis \<subseteq> dVs G \<and> r \<in> dVs G)"

definition "invar_1 state = (vset_inv (avoided state) \<and> vset_inv (explored state))"

definition "invar_within_graph state =
  (t_set (avoided state) \<subseteq> dVs G \<and> t_set (explored state) \<subseteq> dVs G \<and> set (roots state) \<subseteq> dVs G)"

definition "invar_roots state = (set (roots state) \<subseteq> set initial_roots)"

definition "invar_paths_sound state =
  (\<forall>p \<in> set (paths state).
     dpath G (rev p) \<and> p \<noteq> [] \<and> distinct p \<and> target (hd p) \<and> last p \<in> set initial_roots)"

definition "invar_blocked_avoided state =
  (\<forall>p \<in> set (paths state). t_set (blocked p) \<subseteq> t_set (avoided state))"

definition "invar_paths_disjoint state =
  sorted_wrt (\<lambda>q p. set q \<inter> t_set (blocked p) = {}) (paths state)"

definition "invar_explored_closed state =
  (paths state = [] \<longrightarrow>
     t_set (avoided state) = {} \<and>
     set initial_roots \<subseteq> set (roots state) \<union> t_set (explored state) \<and>
     (\<forall>v \<in> t_set (explored state). \<not> target v) \<and>
     (\<forall>v w. v \<in> t_set (explored state) \<longrightarrow> (v, w) \<in> G \<longrightarrow> w \<in> t_set (explored state)))"
```
How the invariants map to the current development:
- `invar_1` and `invar_within_graph` are today's `search_pre`, extended by
  the roots.
- `invar_paths_sound` and `invar_paths_disjoint` are the two conjuncts of
  `disjoint_search_correct`.
- `invar_explored_closed` replaces `none_closed_reach` and
  `disjoint_search_nonempty`. It is stronger: completeness now holds for
  *every* root, not only the first.

The `_props` form of `invar_explored_closed` takes `paths state = []` as a
second premise and has flat conclusions:
```
lemma invar_explored_closed_props[invar_props_elims]:
  "\<lbrakk>invar_explored_closed state; paths state = []\<rbrakk> \<Longrightarrow>
   (\<lbrakk>t_set (avoided state) = {}; set initial_roots \<subseteq> set (roots state) \<union> t_set (explored state);
     \<forall>v \<in> t_set (explored state). \<not> target v;
     \<forall>v w. v \<in> t_set (explored state) \<longrightarrow> (v, w) \<in> G \<longrightarrow> w \<in> t_set (explored state)\<rbrakk> \<Longrightarrow> P)
   \<Longrightarrow> P"
```
If `elim!` handles the second premise badly, declare this one as plain `elim`
(DFS does the same for `invar_visited_through_seen_props`, which is `[elim!]`
without the bundle).

### R2-4. Proofs locale: the contract of the search step

```
locale disjoint_paths_search = disjoint_paths_search_spec +
  assumes search_step:
    "\<And>avoid r vis res vis'. \<lbrakk>search_step_precond avoid r vis; search_step avoid r vis = (res, vis')\<rbrakk>
       \<Longrightarrow> vset_inv vis' \<and> t_set vis' \<subseteq> dVs G \<and> t_set vis \<subseteq> t_set vis'"
    "\<And>avoid r vis res vis' v. \<lbrakk>search_step_precond avoid r vis; search_step avoid r vis = (res, vis');
       v \<in> t_set vis' - t_set vis\<rbrakk> \<Longrightarrow> \<not> target v"
    "\<And>avoid r vis vis'. \<lbrakk>search_step_precond avoid r vis; search_step avoid r vis = (None, vis');
       r \<notin> t_set avoid\<rbrakk> \<Longrightarrow> r \<in> t_set vis'"
    "\<And>avoid r vis vis' v w. \<lbrakk>search_step_precond avoid r vis; search_step avoid r vis = (None, vis');
       v \<in> t_set vis' - t_set vis; (v, w) \<in> G\<rbrakk> \<Longrightarrow> w \<in> t_set avoid \<union> t_set vis'"
    "\<And>avoid r vis p vis'. \<lbrakk>search_step_precond avoid r vis; search_step avoid r vis = (Some p, vis')\<rbrakk>
       \<Longrightarrow> dpath G (rev p) \<and> p \<noteq> [] \<and> distinct p \<and> target (hd p) \<and> last p = r \<and>
           set p \<inter> (t_set avoid \<union> t_set vis') = {}"
  and blocked:
    "\<And>p. vset_inv (blocked p)"
    "\<And>p. t_set (blocked p) \<subseteq> dVs G"
  and roots:
    "set initial_roots \<subseteq> dVs G"
begin
context
  includes set_ops.automation2
begin
```
(Use `set_ops.automation2` only if `Set2` provides it at this instance, as in
DFS; otherwise use `set_ops.invar_union`/`set_ops.set_union` as `[simp]`.)

**Family lemmas.** There are 7 invariants. Each gets `_props`, `_intro`,
`_holds_upd1`, `_holds_upd2`, `_holds_ret_1` and `_holds`, 42 lemmas in all.
The branch lemmas are stated as in guide §4:
`⟦<branch>_conds state; <invariants it needs> state; invar_x state⟧ ⟹ invar_x (<update> state)`.

| Invariant | Needs (for `upd1` and `upd2`) | Facts used |
|---|---|---|
| `invar_1` | `invar_within_graph` | `search_step(1)`, `blocked(1)`, `set_ops.invar_union` |
| `invar_within_graph` | `invar_1` | `search_step(1)`, `blocked(2)`, `set_ops.set_union` |
| `invar_roots` | — | `set (tl xs) ⊆ set xs` |
| `invar_paths_sound` | `invar_1`, `invar_within_graph`, `invar_roots` | `search_step(5)` |
| `invar_blocked_avoided` | `invar_1` | `set_ops.set_union` |
| `invar_paths_disjoint` | `invar_1`, `invar_within_graph`, `invar_blocked_avoided` | `search_step(5)` (the new path misses `avoided`, which contains every earlier `blocked q`), `sorted_wrt.simps(2)` |
| `invar_explored_closed` | `invar_1`, `invar_within_graph` | `upd1`: vacuous (`paths ≠ []`); `upd2`: `search_step(1–4)` with `avoided = {}` |

The candidate for each branch lemma is the single call
```
  by (auto elim!: call_cond_elims invar_props_elims intro!: invar_props_intros
            dest!: search_step[OF search_step_precondI]
            simp: disjoint_paths_search_upd1_def Let_def)
```
It needs `search_step_precondI[intro]`, a one-line introduction rule for the
precondition.
- **Exception: `invar_explored_closed_holds_upd2`.** This is the one
  mathematical case. Write a structured proof of at most 12 lines, with one
  `have` each for the root, the closure of the old explored set, the closure of
  the newly explored vertices, and "no target".
- Every `_holds` lemma is the three-line induction of R1-4.

### R2-5. Correctness (guide §4.2)

Layer 1 (returning branch): one lemma per property *k*, in the BFS naming
`<loop>_correct_<k>_ret_1`. The mathematics of completeness is in
`_correct_3_ret_1`.
```
lemma disjoint_paths_search_correct_1_ret_1:
  "\<lbrakk>invar_paths_sound state; disjoint_paths_search_ret_1_conds state; p \<in> set (paths state)\<rbrakk>
   \<Longrightarrow> dpath G (rev p) \<and> p \<noteq> [] \<and> distinct p \<and> target (hd p) \<and> last p \<in> set initial_roots"
  by (auto elim!: invar_props_elims)

lemma disjoint_paths_search_correct_2_ret_1:
  "\<lbrakk>invar_paths_disjoint state; disjoint_paths_search_ret_1_conds state\<rbrakk>
   \<Longrightarrow> sorted_wrt (\<lambda>q p. set q \<inter> t_set (blocked p) = {}) (paths state)"
  by (auto elim!: invar_props_elims)

lemma disjoint_paths_search_correct_3_ret_1:
  "\<lbrakk>invar_explored_closed state; disjoint_paths_search_ret_1_conds state;
    r \<in> set initial_roots; Vwalk.vwalk_bet G r q z; target z\<rbrakk>
   \<Longrightarrow> paths state \<noteq> []"
  by (auto elim!: call_cond_elims invar_props_elims dest: vwalk_bet_closed)
```
Layer 2 (the final state returns; one returning branch, no flag). As in R1,
the return update is the identity, so there is no `disjoint_paths_search_ret_1`
companion lemma.
```
lemma disjoint_paths_search_ret_1_holds[ret_holds_intros]:
  assumes "disjoint_paths_search_dom state"
  shows "disjoint_paths_search_ret_1_conds (disjoint_paths_search state)"
  (proof: the three-line induction with disjoint_paths_search_cases, as in R1)
```
The initial state:
```
lemma initial_state_props[invar_holds_intros, termination_intros]:
  "invar_1 initial_state" "invar_within_graph initial_state" "invar_roots initial_state"
  "invar_paths_sound initial_state" "invar_blocked_avoided initial_state"
  "invar_paths_disjoint initial_state" "invar_explored_closed initial_state"
  "disjoint_paths_search_dom initial_state"
  by (auto intro!: invar_props_intros disjoint_paths_search_terminates
            simp: initial_state_def roots)

lemma initial_state_loops_same:
  "disjoint_paths_search_impl initial_state = disjoint_paths_search initial_state"
  by (auto intro!: disjoint_paths_search_impl_same initial_state_props)
```
Layer 3 (about the initial state, with no domain or invariant premise; two
lines each, in the form of R1's `hopcroft_karp_loop_correct`):
```
lemma disjoint_paths_search_correct_1:
  "p \<in> set (paths (disjoint_paths_search initial_state)) \<Longrightarrow>
   dpath G (rev p) \<and> p \<noteq> [] \<and> distinct p \<and> target (hd p) \<and> last p \<in> set initial_roots"
  by (intro disjoint_paths_search_correct_1_ret_1[where state = "disjoint_paths_search initial_state"])
     (auto intro: invar_holds_intros ret_holds_intros)

lemma disjoint_paths_search_correct_2:
  "sorted_wrt (\<lambda>q p. set q \<inter> t_set (blocked p) = {}) (paths (disjoint_paths_search initial_state))"
  (same two lines with _correct_2_ret_1)

lemma disjoint_paths_search_correct_3:
  "\<lbrakk>r \<in> set initial_roots; Vwalk.vwalk_bet G r q z; target z\<rbrakk>
   \<Longrightarrow> paths (disjoint_paths_search initial_state) \<noteq> []"
  (same two lines with _correct_3_ret_1)
```
Layer 4 (executable loop) is `initial_state_loops_same`. There is no wrapper
at this level. The carry-over to the phase is the interpretation in R4, which
re-uses these lemmas and does not prove them again.

`vwalk_bet_closed` and `found_vwalk_bet` move here from `HK_Search`, global,
before the record. `vwalk_bet_closed` gets a single-call proof:
`by (induction rule: induct_vwalk_bet) auto`.

### R2-6. The incremental DFS fulfils the contract (section `\label{sec:idfs}`)

```
context IDFS_witness
begin

lemma IDFS_impl_search_step:
  assumes "vset_inv avoid" "vset_inv vis" "t_set avoid \<subseteq> dVs (Graph.digraph_abs G)"
          "t_set vis \<subseteq> dVs (Graph.digraph_abs G)" "r \<in> dVs (Graph.digraph_abs G)"
          "IDFS_impl P avoid [r] vis = (res, vis')"
  shows (the seven conclusions of today's root_call, in the order of R2-4)
```
*Proof.* The source is today's `root_call`, which has 30 lines and 14 labels.
Target: an opening `note`, then one `by` per conclusion. The opening is
`note A = vwalk1[OF assms(5), THEN …] assms(1-4)`; it is the only `[OF]`
chain. Each conclusion is closed with the matching `IDFS_*` theorem, for
example `using IDFS_vis_works_4[OF A assms(6)] by simp`.

`HK_Search` imports `Disjoint_Paths_Search` from this gate on and loses its
copies of `vwalk_bet_closed` and `found_vwalk_bet`.

**Gate R2 checks.** These are the checks of §3, plus:
- the loop items of §0 for this theory;
- the 7 complete invariant families;
- termination in the DFS form of guide §4.1, without a premise;
- the domain of the initial state in `initial_state_props`;
- correctness in layers 1–4 of guide §4.2: three `_correct_<k>_ret_1`
  lemmas, `disjoint_paths_search_ret_1_holds`, three premise-free
  `_correct_<k>` lemmas, and `initial_state_loops_same`.

---

## R3. `Alt_BFS_Bipartite.thy` (from `Hopcroft_Karp.thy`)

No loop; this gate changes names and proofs only (RD4).

### R3-1. Changes
1. **Theory name and header.** Rename the theory and update `ROOT` and the
   import of `HK_Phase`. Use `subsection`s:
   - *Walk lemmas*;
   - *Edges of the copies graph*;
   - *Walks of the copies graph under the BFS axiom*;
   - *The bipartite matching instance*;
   - *Augmenting paths and walks of the copies graph*.
2. **`BFS_axiom_hk` is deleted.** Its uses become the cartouche
   `\<open>BFS_axiom\<close>`, which is in scope in the `assumes BFS_axiom` context.
3. **Assumption bundle (in locale `BFS`, before the axiom context):**
   ```
   definition "bipartite_matching_input UG M X Y =
     (graph_invar UG \<and> M \<subseteq> UG \<and>
      Graph.digraph_abs matching = {(u, v). {u, v} \<in> M} \<and>
      Graph.digraph_abs unmatching = {(u, v). {u, v} \<in> UG - M} \<and>
      t_set srcs = Vs UG - Vs M \<and> bipartite UG X Y)"
   ```
   The instance context becomes
   `context fixes UG M X Y assumes bipartite_matching_input: "bipartite_matching_input UG M X Y"`.
   It unpacks the bundle once:
   `lemma bipartite_matching_input_facts[simp]: "graph_invar UG" "M ⊆ UG" "Graph.digraph_abs matching = …" … "bipartite UG X Y"`,
   proved `by (auto simp: …_def)`. Every proof then drops the six names.
4. **Renames.** The full list is in §A. The main ones:
   - `G_char` → `G_eq_undirected_edges`;
   - `vwalk_G_path` and `path_vwalk_G` → one lemma, `vwalk_G_iff_path`;
   - `aug_path_*` → `augmenting_path_*`.

### R3-2. Proof targets (lemma by lemma)

| Lemma | Now (lines / labels) | Target |
|---|---|---|
| `vwalk_bet_level_distinct` | 35 / 6 | ≤ 8 lines: `induction rule: induct_vwalk_bet`, `auto` with `less_le_trans`/`le_less_trans`, no `consider` |
| `alt_list_edges_of_vwalk_path` / `_path_vwalk` | 20 / 3, 30 / 6 | one `by (induction p arbitrary: … rule: edges_of_path.induct) (auto simp: alt_list_step alt_list_empty)` each; structured cases only if needed |
| `copies_dag_vtx_dVs` | 14 / 1 | `by (force simp: dVs_eq copies_dag_def)` |
| `copies_walk_alt_walk` | 55 / 10 | keep the induction; one case per edge kind, each ≤ 6 lines (no `w1`/`w2`/`step2` labels; chain with `hence`) |
| `copies_lev_zero` | 40 / 9 | ≤ 12 lines; the case `Odd` closes with `altd_G_parity` in one call |
| `copies_walk_from_odd`, `VisO_copies_dVs` | 20 / 5, 25 / 8 | ≤ 8 lines each |
| `G_eq_undirected_edges`, `dVs_G_subset_Vs`, `vwalk_G_iff_path`, `alt_walk_alt_path`, `alt_path_imp_alt_list` | 4–25 each | single `by`, or `induction` + `auto` |
| `augmenting_path_alt_walk` | 23 / 11 | ≤ 6 lines |
| `copies_walk_label_side` | 35 / 8 | keep the induction; the two edge kinds by `bipartite_edgeD` in one call each |
| `copies_walk_distinct_vtx` | 33 / 10 | ≤ 12 lines; the choice of the side (`obtain Z Z'`) stays, as one mathematical step |
| `copies_walk_augmenting` | 36 / 16 | ≤ 10 lines: from `copies_walk_from_odd`, `vwalk_G_iff_path`, `alt_walk_alt_path`, `copies_walk_distinct_vtx`, then `auto simp: matching_augmenting_path_def` |
| `augmenting_path_copies_start`, `augmenting_path_iff_free_odd_copy` | 18 / 5, 26 / 6 | ≤ 6 lines each |

**Consumer patch.** `HK_Phase` changes its import to `Alt_BFS_Bipartite`.
Lemma names change by substitution. Cited positional fact lists such as
`[OF bfs_axiom UG_graph_invar M_sub Mt_abs Ut_abs S_props(2) inp_parts(7) st_valid' …]`
are replaced by `[OF bfs_axiom <bundle fact> st_valid' …]` with a one-line
`have` of the bundle. This is the only proof change in `HK_Phase` at R3.

---

## R4. `Hopcroft_Karp_Phase.thy` (from `HK_Phase.thy`; `HK_Search` removed)

### R4-1. Layout

1. *The matching, represented by its mate function.*
   - The `mate` interpretation and its `lemmas` are unchanged (RD6).
   - `mate_matching_iff` and `mate_Vs_iff` become `by (auto …)` proofs.
     They use the library's symmetry lemma for the mate function, as the
     current proofs do. It keeps its library name.
   - Both become conditional `[simp]` rules under `mate_invar G m`.
2. *The input graph in the read-only vocabulary.* The `RO` interpretation and
   the five bridges are unchanged (HK-D9, RD7).
3. *The re-interpretation of the alternating BFS.*
   - `hkbfs` → `phase_bfs`; the text block stays.
4. *The search at the operations of the incremental DFS (executable).*
   ```
   definition "IDFS_stack0_rbt avoid vis p = …"        (was hk_stack0)
   definition "IDFS_impl_rbt CG P avoid p vis = …"     (was hk_idfs)
   global_interpretation phase_search: disjoint_paths_search_spec
     where vset_empty = vset_empty and … (Set2 operations as in the current W interpretation)
       and G = "idfs.Graph.digraph_abs CG" and target = P and blocked = blk
       and search_step = "\<lambda>avoid r vis. IDFS_impl_rbt CG P avoid [r] vis"
       and initial_roots = rs
     for CG P blk rs
     defines disjoint_paths_search_rbt = phase_search.disjoint_paths_search_impl
       and disjoint_paths_search_initial_rbt = phase_search.initial_state
   ```
   The `G` parameter is only used by the invariants, not by the loop. If the
   `for` list then makes a constant depend on `CG` only through `G`, keep it as
   it is: the code equations do not mention `G`.
5. *Executable builders (global, renamed, §A)* and the phase:
   ```
   definition "hopcroft_karp_phase edges vs m =
     (if free_vertices vs m = [] then [] else
      let matching_graph = G.from_list (matched_edges edges m);
          non_matching_graph = G.from_list (unmatched_edges edges m);
          bfs_state = alt_bfs_impl matching_graph non_matching_graph
                        (alt_bfs_initial_state (free_vertex_set vs m));
          copies_edge_list = copies_edges edges m (Alt_BFS.BFS_state.parents bfs_state);
          copies_graph = idfs.Graph.from_list copies_edge_list;
          level = copy_level (distances bfs_state);
          blk = blocked_copies (map fst copies_edge_list @ map snd copies_edge_list);
          rs = phase_roots vs m (visited_odd bfs_state) (distances bfs_state);
          target = (\<lambda>w. level w = 0)
      in map (map vtx)
           (paths (disjoint_paths_search_rbt copies_graph target blk rs
                     (disjoint_paths_search_initial_rbt rs))))"
   ```
   The argument order of the `defines` constants follows the `for` list. R0
   checks it.
6. *Input lemmas* are global, as plain `⟦hopcroft_karp_input Gin vs X Y⟧ ⟹ …`
   statements:
   - `adjacency_edges_set`
   - `undirected_graph_edge_iff`
   - `Vs_undirected_graph`
   - `undirected_graph_invar`

   Plus `hopcroft_karp_inputE[elim]`, which unpacks the bundle with flat
   premises. Each proof is ≤ 4 lines.
7. *The locale `hopcroft_karp_phase`* (RD5):
   ```
   locale hopcroft_karp_phase =
     fixes input_graph vertex_list X Y mate
     assumes input: "hopcroft_karp_input input_graph vertex_list X Y"
         and matching: "mate_invar (undirected_graph input_graph) mate"
         and free: "free_vertices vertex_list mate \<noteq> []"
   begin
   definition "edge_list = adjacency_edges input_graph vertex_list"
   definition "matching_graph = G.from_list (matched_edges edge_list mate)"
   definition "non_matching_graph = G.from_list (unmatched_edges edge_list mate)"
   definition "bfs_sources = free_vertex_set vertex_list mate"
   definition "bfs_state = alt_bfs_impl matching_graph non_matching_graph (alt_bfs_initial_state bfs_sources)"
   definition "bfs_dag = Alt_BFS.BFS_state.parents bfs_state"
   definition "copies_edge_list = copies_edges edge_list mate bfs_dag"
   definition "copies_graph = idfs.Graph.from_list copies_edge_list"
   definition "level = copy_level (distances bfs_state)"
   definition "copy_roots = phase_roots vertex_list mate (visited_odd bfs_state) (distances bfs_state)"
   ```
   The types of `input_graph` and `mate` are those of `Gin` and `m` today.
   R0 records them from the current context.

   Inside the locale come the interpretations `idfs_witness: IDFS_witness`
   (today's `W`) and `search: disjoint_paths_search`. The step contract of the
   latter is proved from `idfs_witness.IDFS_impl_search_step` and
   `IDFS_impl_rbt_eq` (today's `hk_idfs_eq`). Then the lemmas of R4-2.
8. *The phase contract (global).* Three theorems with plain statements:
   - `hopcroft_karp_phase_sound`
   - `hopcroft_karp_phase_disjoint`
   - `hopcroft_karp_phase_complete`

   Each has the premises `⟦hopcroft_karp_input Gin vs X Y; mate_invar (undirected_graph Gin) m⟧`.
   The case `free_vertices vs m = []` is closed by `simp`. Otherwise the proof
   is the locale theorem.

### R4-2. Locale lemmas: renames and proof targets

| Now | New | Target |
|---|---|---|
| `M_sub` | `mate_matching_subset` | single `by` |
| `Mt_abs`, `Ut_abs` (25 lines each) | `matching_graph_abs`, `non_matching_graph_abs` | single `by (auto simp: matching_graph_def matched_edges_def G.from_list_correct adjacency_edges_set undirected_graph_edge_iff …)` |
| `S_props`, `S_free` | `bfs_sources_props` (`[simp]`) | ≤ 3 lines; the `foldr insert_rbt` fact becomes a global one-line lemma `set_tree_foldr_insert_rbt` |
| `bfs_axiom` (55 lines) | `phase_bfs_axiom` | split into `[simp]` facts (finite neighbourhoods of `from_list` graphs; sources inside the non-matching graph; sources not empty; the two graphs disjoint), then `by (auto simp: phase_bfs.BFS_axiom_def)` |
| `st_eq`, `st_valid`, `st_valid'` | `bfs_state_eq`, `bfs_state_valid_impl`, `bfs_state_valid` | single `by` each |
| `T_sub`, `T_graph_inv`, `isin_T` | `bfs_dag_subset`, `bfs_dag_graph_inv`, `isin_bfs_dag` | ≤ 4 lines each |
| `cl_mem`, `CG_abs` (65 lines) | `copies_edge_list_mem`, `copies_graph_abs` | ≤ 10 lines: `auto simp: copies_edges_def phase_bfs.copies_dag_def … split: if_splits` with `bfs_dag_subset` |
| `CG_level`, `CG_layered` | `copies_graph_level`, `copies_graph_layered` | ≤ 4 lines each |
| `roots_props`, `roots_dVs`, `roots_nonempty` | `copy_roots_free_odd`, `copy_roots_in_graph`, `copy_roots_nonempty` | ≤ 6 lines each |
| `dVs_CG`, `blk_props` | `dVs_copies_graph`, `blocked_copies_props` | ≤ 6 lines |
| `phase_unfold`, `DS_facts` | `hopcroft_karp_phase_unfold`; `DS_facts` deleted (replaced by `search.disjoint_paths_search_correct_1/2/3`) | single `by` |
| `phase_sound_aux`, `phase_disjoint_aux`, `phase_complete_aux` (28, 32, 42 lines) | `phase_paths_augmenting`, `phase_paths_disjoint`, `phase_paths_nonempty` | ≤ 10 lines each, with the bundle fact of R3 |
| `vset_of_list_rbt_props`, `fold_min_mem`, `layered_dgraph_cong` | unchanged names | `vset_of_list_rbt_props`: single `by (induction …) auto`; `layered_dgraph_cong`: ≤ 8 lines |

`HK_Search.thy` is removed from `ROOT` (snapshot in `backups/restyle-R4/`).
`HK_Example` gets the name substitutions of §A that concern the phase.

**Gate R4 checks.** These are the checks of §3, plus:
- the demonstration's first phase is `[[3,1],[4,0]]` (RD3);
- the final mate map is unchanged.

---

## R5. `Hopcroft_Karp_Example.thy` (from `HK_Example.thy`)

1. *Code equations.* The bridges are kept (`nb_rbt`, `add_edge_rbt`,
   `from_list_rbt`, `add_edge_idfs`, `from_list_idfs`, `[code_unfold]`). Their
   proofs become single `by` (e.g. `G_from_list_code_unfold`:
   `by (auto simp: G.from_list_def from_list_rbt_def G_add_edge_code_unfold RBT_Set.empty_def)`).
2. *The executable loop:*
   ```
   global_interpretation hopcroft_karp_exec: hopcroft_karp_loop_spec
     where empty_matching = Leaf and matching_invar = "mate_invar (undirected_graph Gin)"
       and augment = mate_augment and matching_abstract = mate_matching
       and phase = "hopcroft_karp_phase (adjacency_edges Gin vs) vs" and G = "undirected_graph Gin"
     for Gin vs
     defines hopcroft_karp_loop_exec = hopcroft_karp_exec.hopcroft_karp_loop_impl
       and hopcroft_karp_initial_state = hopcroft_karp_exec.initial_state
       and hopcroft_karp = hopcroft_karp_exec.hopcroft_karp
   ```
   The executable algorithm is the wrapper `hopcroft_karp` of R1-2 (guide
   §4.2, layer 5), so there is no separate `definition "hopcroft_karp …"`.
3. *Correctness* is a re-export (guide §4.2, layer 6), with no new proof of
   the final statement:
   ```
   context
     fixes Gin vs X Y
     assumes "hopcroft_karp_input Gin vs X Y"
   begin

   interpretation hopcroft_karp_top_loop: hopcroft_karp_loop
     where empty_matching = Leaf and matching_invar = "mate_invar (undirected_graph Gin)"
       and augment = mate_augment and matching_abstract = mate_matching
       and phase = "hopcroft_karp_phase (adjacency_edges Gin vs) vs" and G = "undirected_graph Gin"
     (proof: unfold_locales, then one auto per assumption group, citing
      undirected_graph_invar, mate_invarD, mate_empty_props, mate_augmentation_correct
      and hopcroft_karp_phase_sound/_disjoint/_complete)

   lemmas hopcroft_karp_correctness =
       hopcroft_karp_top_loop.hopcroft_karp_correctness[folded hopcroft_karp_def]
     and hopcroft_karp_final_invar =
       hopcroft_karp_top_loop.hopcroft_karp_final_invar[folded hopcroft_karp_def]

   end
   ```
   - After the context ends, the two facts carry the premise
     `hopcroft_karp_input Gin vs X Y`. They state:
     - `hopcroft_karp_input Gin vs X Y \<Longrightarrow> max_card_matching (undirected_graph Gin) (mate_matching (hopcroft_karp Gin vs))`;
     - `hopcroft_karp_input Gin vs X Y \<Longrightarrow> mate_invar (undirected_graph Gin) (hopcroft_karp Gin vs)`.

     These are the two conclusions of today's `hopcroft_karp_correct` (§0.1).
   - Check with `thm` that the `[folded …]` form prints exactly this. The
     argument pattern of the global `hopcroft_karp` (R0 check) decides whether
     `folded hopcroft_karp_def` or `folded hopcroft_karp_def[symmetric]` is
     needed. If neither prints the statement, ask the orchestrator; do not
     add a proof.
4. *Demonstration.* `demo_*` names and `value` commands are kept.
   - `demo_bip` becomes ≤ 4 lines (`auto simp: bipartite_def UG… demo_edges_def`,
     with the witness swap as one `insert_commute` step).
   - `demo_input` and `demo_max` are kept. The demonstration theorem is
     `hopcroft_karp_correctness[OF demo_input]`.
   - `export_code hopcroft_karp in SML module_name Hopcroft_Karp`.

**Gate R5 checks.** These are the checks of §3, plus:
- `hopcroft_karp_correct` matches §0.1;
- `export_code` succeeds;
- the demonstration values are as in R4.

---

## R6. Close-out

1. Run `style_stats.py` on the five restyled theories. Put the table of §0
   with the measured column into this plan and into `progress.md`. Any target
   that is missed is listed with the reason.
2. Update the status block of `Hopcroft_Karp_Plan.md`, which gets a pointer to
   this plan and the theory renames. Update the memory file
   `hopcroft-karp-project-copy.md` (theory names, the new locales).
3. **Coordination.**
   - Ask the Graph ADT session whether its split library will name the
     read-only locale `Pair_Graph_Specs_Read_Only` (RD7), and record the
     answer for the integration step of HK-D9.
   - Ask the user about RD6: should the Hungarian method's matching constants
     be used?
4. Remove the editor backup files `Hopcroft_Karp/*.thy~` from the copy. They
   are untracked by-products of jEdit.

---

## A. Rename table

**Theories.**

| Now | New |
|---|---|
| `HK_Top_Loop` | `Hopcroft_Karp_Top_Loop` |
| `HK_Search` | removed (loop → `Disjoint_Paths_Search`) |
| `Hopcroft_Karp` | `Alt_BFS_Bipartite` |
| `HK_Phase` | `Hopcroft_Karp_Phase` |
| `HK_Example` | `Hopcroft_Karp_Example` |

**Locales, records, interpretations.**

| Now | New |
|---|---|
| `hk_loop_defs` / `hk_loop_spec` | `hopcroft_karp_loop_spec` / `hopcroft_karp_loop` |
| — (bare matching) | `record hopcroft_karp_state` (`current_matching`, `phases`) |
| `disjoint_search_gen` (6-argument `fun`) | `disjoint_paths_search_spec` / `disjoint_paths_search`, `record disjoint_paths_search_state` |
| `hkbfs` | `phase_bfs` |
| `W` | `idfs_witness` |
| `hk_exec` / `hk` | `hopcroft_karp_exec` / (unnamed `interpretation hopcroft_karp_loop`) |
| context `fixes m assumes mi fne` | locale `hopcroft_karp_phase` |
| context `fixes UG M X Y assumes UG_inv M_sub Mabs Uabs srcs_free bip` | context `assumes bipartite_matching_input` |

**Constants.**

| Now | New |
|---|---|
| `hk_loop`, `hk_loop_impl` | `hopcroft_karp_loop`, `hopcroft_karp_loop_impl` |
| `augment_list`, `augment_all` | removed (`foldl augment` in the loop body) |
| `matching_abs` | `matching_abstract` (+ `empty_matching`) |
| `search_pre` | `search_step_precond` (+ `invar_1`, `invar_within_graph`) |
| `hk_edges` | `adjacency_edges` |
| `UG_of` | `undirected_graph` |
| `hk_input` | `hopcroft_karp_input` |
| `match_list`, `unmatch_list` | `matched_edges`, `unmatched_edges` |
| `free_list` | `free_vertices` |
| `hk_srcs` | `free_vertex_set` |
| `copies_list` | `copies_edges` |
| `hk_level` | `copy_level` |
| `hk_roots` | `phase_roots` |
| `hk_blk` | `blocked_copies` |
| `hk_stack0`, `hk_idfs` | `IDFS_stack0_rbt`, `IDFS_impl_rbt` (as `avoid_impl_rbt` in DDFS_Example) |
| `hk_phase` | `hopcroft_karp_phase` |
| `hk_loop_exec`, `hk_augment_list` | `hopcroft_karp_loop_exec`, removed |
| `es Mt Ut S st T cl CG lv` (abbreviations) | `edge_list matching_graph non_matching_graph bfs_sources bfs_state bfs_dag copies_edge_list copies_graph level` (locale definitions) |

**Lemmas (main ones; the rest follow guide §2.4).**

| Now | New |
|---|---|
| `edge_of_disjoint_path` | `edges_of_path_disjoint` |
| `aug_path_disjoint_preserved` | `augmenting_path_disjoint_preserved` |
| `augment_list_correct`, `augment_all_correct` | `foldl_augment_invar`, `foldl_augment_card` |
| `hk_loop_dom_aux`, `hk_loop_dom` | `hopcroft_karp_loop_termination_induction`, `hopcroft_karp_loop_termination` (Hungarian form, guide §4.1) |
| — (inline arithmetic) | `card_increase_upd1` (second conclusion of the one-step lemma), `card_matching_bounded` |
| `hk_loop_invar` | `invar_matching_holds` |
| `hk_loop_final` | `hopcroft_karp_loop_ret_1_holds` + `hopcroft_karp_loop_correct_ret_1` |
| `hk_loop_impl_same` | `hopcroft_karp_loop_impl_same` |
| `hk_loop_correct` (arbitrary `m`), `hk_loop_impl_correct` | `hopcroft_karp_loop_correct_ret_1` (layer 1), `hopcroft_karp_loop_correct` + `hopcroft_karp_loop_final_invar` about `initial_state` (layer 3), `initial_state_loops_same` (layer 4), `hopcroft_karp_correctness` + `hopcroft_karp_final_invar` for the wrapper `hopcroft_karp` (layer 5) |
| `hopcroft_karp_correct` (`HK_Example`, proved again) | `hopcroft_karp_correctness`, `hopcroft_karp_final_invar`, re-exported with `[folded hopcroft_karp_def]` (layer 6) |
| `root_call` | `IDFS_impl_search_step` |
| `disjoint_search_correct` | `disjoint_paths_search_correct_1/2_ret_1` (layer 1), `disjoint_paths_search_correct_1/2` (layer 3) |
| `none_closed_reach`, `disjoint_search_nonempty` | `invar_explored_closed_*`, `disjoint_paths_search_correct_3_ret_1`, `disjoint_paths_search_correct_3` |
| `BFS_axiom_hk` | removed (cartouche `\<open>BFS_axiom\<close>`) |
| `G_char`, `dVs_G_Vs` | `G_eq_undirected_edges`, `dVs_G_subset_Vs` |
| `vwalk_G_path`, `path_vwalk_G` | `vwalk_G_iff_path` |
| `alt_path_alt_list` | `alt_path_imp_alt_list` |
| `aug_path_alt_walk`, `aug_path_copies_start`, `aug_path_iff_free_odd_copy`, `BFS_aug_path_iff` | `augmenting_path_alt_walk`, `augmenting_path_copies_start`, `augmenting_path_iff_free_odd_copy`, `BFS_augmenting_path_iff` |
| `copies_walk_side` | `copies_walk_label_side` |
| `inp_parts` | `hopcroft_karp_inputE` |
| `hk_edges_set`, `UG_edge_iff`, `Vs_UG`, `UG_graph_invar` | `adjacency_edges_set`, `undirected_graph_edge_iff`, `Vs_undirected_graph`, `undirected_graph_invar` |
| ζ-5 lemmas | see R4-2 |
| `hk_phase_sound/_disjoint/_complete` | `hopcroft_karp_phase_sound/_disjoint/_complete` |
| `hk_idfs_eq` | `IDFS_impl_rbt_eq` |
